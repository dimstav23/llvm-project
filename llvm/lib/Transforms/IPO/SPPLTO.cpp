///////////////////////////////////////////
///                                     ///
///           /IPO/SPPLTO.cpp           ///
///           (clangllvm.12.0)          ///
///                                     ///
///////////////////////////////////////////


#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Transforms/IPO/SPPLTO.h"
#include "llvm/Transforms/IPO.h"

#include "llvm/Analysis/ValueTracking.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../lib/IR/ConstantsContext.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include <utility>
#include <queue>
#include <unordered_set>
#include <cxxabi.h>

#include <climits>
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ValueTracking.h"
#include <algorithm>
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../lib/IR/ConstantsContext.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include <utility>
#include <queue>
#include <unordered_set>
#include <cxxabi.h>
#include "llvm/Transforms/SPP/SPPUtils.h"

// #define DEBUG_TYPE "spplto"

//#define SPPDEBUG // Uncomment for debugging
#ifdef SPPDEBUG
#  define dbg(x) x
#else
#  define dbg(x)
#endif

using namespace llvm;
using namespace std; // Jin: this is NOT recommended..

namespace {

struct SPPLTO : public ModulePass {
  static char ID;

  SPPLTO() : ModulePass(ID) 
  {
    initializeSPPLTOPass(*PassRegistry::getPassRegistry());
  }
  
  virtual bool redundantCB(Function *F);
  virtual bool trackPtrs (Function * F);
  virtual bool runOnFunction (Function * F, Module &M);
  virtual bool runOnModule(Module &M) override;
  bool doCallBase (CallBase * ins);

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    //AU.addRequired<DominatorTreeWrapperPass>();
    //AU.addRequired<AAResultsWrapperPass>();
    //AU.addRequired<CallGraphWrapperPass>();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
  }

  TargetLibraryInfoWrapperPass* TLIWP = nullptr;
  void setTLIWP(TargetLibraryInfoWrapperPass *TLIWP) 
  {
    this->TLIWP = TLIWP;
  }

  TargetLibraryInfo *getTLI(const Function & F)
  {
    return &this->TLIWP->getTLI(F);
  }

  protected:

};

} // end anonymous namespace

static std::unordered_set <Value*> globalPtrs;
static std::unordered_set <Value*> volPtrs;
static std::unordered_set <Value*> pmemPtrs;
static std::unordered_set <Value*> extPtrs;
static std::unordered_set <Value*> vtPtrs;

static std::vector<Instruction*> redundantChecks;

char SPPLTO::ID = 0;

INITIALIZE_PASS(SPPLTO, "spplto", "SPPLTO", false, false)

ModulePass *llvm::createSPPLTOPass() 
{
  return new SPPLTO;
}

PreservedAnalyses
SPPLTOPass::run(Module &M, ModuleAnalysisManager &MAM) 
{
  return PreservedAnalyses::all();
}

static string 
demangleName(StringRef str)
{
    string result = "";
    int unmangledStatus;
    
    char *unmangledName = abi::__cxa_demangle(
        str.data(), nullptr, nullptr, &unmangledStatus);
    if (unmangledStatus == 0) 
    {
        string unmangledNameStr(unmangledName);
        result = unmangledNameStr;
    }
    return result;    
}

static bool hasZeroRedundantChecks()
{
    return redundantChecks.empty();
}

static void eraseRedundantChecks() 
{ 
    dbg(errs()<<">>ERASE_size: "<<redundantChecks.size()<<"\n";)
    for (unsigned i=0; i < redundantChecks.size(); i++) {
        Instruction * eraseI = redundantChecks.at(i);
        dbg(errs()<<i<<">>ERASE: "<< *eraseI <<"\n";)
        eraseI->eraseFromParent(); 
    }
    dbg(errs()<<">>ERASE_done\n";)
}
        
static void memCleanUp()
{
    redundantChecks.clear();
    volPtrs.clear();
    globalPtrs.clear();
    pmemPtrs.clear();
    // for (auto extPtr : extPtrs) {
    //     errs()<< "ext Ptr:" << *extPtr << "\n"; 
    // }
    extPtrs.clear();
    vtPtrs.clear();
}

static bool
doCallFunc_LLVMDbg(CallBase *CB)
{
    dbg(errs() << ">>llvm.dbg.CB" << *CB << "\n";)

    MetadataAsValue* Arg= dyn_cast<MetadataAsValue>(CB->getOperand(0));
    assert(Arg);
    
    ValueAsMetadata* ArgMD= dyn_cast<ValueAsMetadata>(Arg->getMetadata());   
    assert(ArgMD);
    
    Value* ArgVal= ArgMD->getValue();   
    assert(ArgVal);
        
    if (!ArgVal->getType()->isPointerTy() || isa<Constant>(ArgVal)) {
        dbg(errs()<<">>llvm.dbg.CB: skipping.. Not PointerTy\n";)
        return false;
    }

    IRBuilder<> B(CB);
    vector <Value*> arglist;
    
    Module *mod = CB->getModule();
    Type *vpty = Type::getInt8PtrTy(mod->getContext());
    FunctionType *fty = FunctionType::get(vpty, vpty, false);
    FunctionCallee hook = 
        mod->getOrInsertFunction("__spp_cleantag_external", fty); 

    Value *TmpPtr = B.CreateBitCast(ArgVal, 
                hook.getFunctionType()->getParamType(0));
    arglist.push_back(TmpPtr);
    CallInst *Masked = B.CreateCall(hook, arglist);
    Value *Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 
    MetadataAsValue *MDAsVal= 
            MetadataAsValue::get(CB->getModule()->getContext(), 
                                 ValueAsMetadata::get(Unmasked));
    
    CB->setArgOperand(0, MDAsVal);
    dbg(errs() << ">>new_CB after masking: " << *CB << "\n";)
    
    return true;
}

static bool
doCallExternal(CallBase *CB)
{
    bool changed = false;

    // Skip tag cleaning for certain transaction functions
    if (CB->getCalledFunction() != NULL && 
        CB->getCalledFunction()->getName().contains("pmemobj_tx_add_range_direct")) 
    {
        return changed;
    }

    if (CB->getCalledFunction() != NULL &&
        !CB->getCalledFunction()->getName().contains("pmemobj_direct"))
    {
        Value *CBval = dyn_cast<Value>(CB);
        if (CBval)
        {
            extPtrs.insert(CBval);
            std::vector<User*> Users(CBval->user_begin(), CBval->user_end());
            dbg(errs() << ">>external callback : " << *CBval << " Uses: " \
                                            << CBval->getNumUses() << "\n";)
            for (auto User : Users) 
            {
                Instruction *iUser= dyn_cast<Instruction>(User);
                dbg(errs() << ">>External ptr use: " << *iUser << "\n";)
                // mark directly derived values as volatile:
                switch (iUser->getOpcode()) 
                {
                    case Instruction::BitCast:
                    case Instruction::PtrToInt:
                    case Instruction::IntToPtr:
                    case Instruction::GetElementPtr:
                        extPtrs.insert(iUser);
                    default:
                        break;
                }                      
            }
        }
    }
    
    Module *mod = CB->getModule();
    Type *vpty = Type::getInt8PtrTy(mod->getContext());
    FunctionType *fty = FunctionType::get(vpty, vpty, false);
    
    FunctionCallee hook = 
        mod->getOrInsertFunction("__spp_cleantag_external", fty); 

    for (auto Arg = CB->arg_begin(); Arg != CB->arg_end(); ++Arg) 
    {   
        Value *ArgVal = dyn_cast<Value>(Arg);
        if (!ArgVal) 
        {
            dbg(errs() << ">>Argument skipping.. Not a value\n";)
            continue;
        }
        
        // Now we got a Value arg. 
        if (!ArgVal->getType()->isPointerTy()) 
        {
            dbg(errs()<<">>Argument skipping.. Not pointerType\n";)
            continue;
        }

        if (isa<Constant>(ArgVal)) 
        {
            dbg(errs()<<">>Argument skipping.. Constant\n";)
            continue; 
        } 

        if ( volPtrs.find(ArgVal->stripPointerCasts()) != volPtrs.end() ||
             vtPtrs.find(ArgVal->stripPointerCasts()) != vtPtrs.end() ||
             globalPtrs.find(ArgVal->stripPointerCasts()) != globalPtrs.end() ||
             extPtrs.find(ArgVal->stripPointerCasts()) != extPtrs.end() )
        {
            dbg(errs() << ">>global, volatile or external ptr skipped cleaning: " << *CB << "\n";)
            continue;
        }
        
        // TODO: move to opt pass later.
        //if (isSafePtr(From->stripPointerCasts())) {
        //    continue; 
        //}

        IRBuilder<> B(CB);
        vector <Value*> arglist;

        Value *TmpPtr = B.CreateBitCast(ArgVal, 
                        hook.getFunctionType()->getParamType(0));
        arglist.push_back(TmpPtr);
        CallInst *Masked = B.CreateCall(hook, arglist);
        Value *Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 

        CB->setArgOperand(Arg - CB->arg_begin(), Unmasked);

        dbg(errs() << ">>new_CB after masking: " << *CB << "\n";)

        changed = true;
    }
    
    return changed;
}

static bool
doCallNonFunc(CallBase *cb)
{
    return doCallExternal(cb);
}

static bool
doCallFunction(CallBase *cb, Function *cfn)
{
    assert(cfn);
   
    // just checking..
    // FIXME: use subclasses of CallInst here
    if (cfn->getName().startswith("llvm.eh.") ||
        cfn->getName().startswith("llvm.dbg.") ||
        cfn->getName().startswith("llvm.lifetime."))
    {
        return false;
    }
    
    // Ignore exception handling calls
    if (cfn->getName().startswith("__cxa_"))
    {
        return false;
    }

    if (cfn->isDeclaration() ||
        StringRef(demangleName(cfn->getName())).equals("pmemobj_direct_inline") ||
        cfn->getName().contains("pmemobj_direct_inline") ||
        cfn->getName().contains("ZL21pmemobj_direct_inline7pmemoid"))
    {         
        dbg(errs() << ">>" << cfn->getName() << " external function call...\n";)
        return doCallExternal(cb);
    }
    
    //simple verification to avoid mistakes
    assert(!cfn->getName().contains("pmemobj_direct_"));    

    dbg(errs() << ">>" << cfn->getName() << " internal function call: skipping..\n";)
    return false; 
}


bool
SPPLTO::doCallBase(CallBase *cb)
{
    bool changed= false;
    dbg(errs() << ">>CallBase: "<<*cb<<"\n";)

    Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());

    if (cfn) 
    {
        StringRef fname = cfn->getName();
        dbg(errs() << ">>CalledFn: " << fname << " / " << demangleName(fname) << "\n";)

        // if it's SPP hook, do not do anything
        if (isSPPFuncName(fname)) 
        {
            dbg(errs() << ">>SPP hook fn call: skipping..\n";)
            return changed; 
        }        
        // if it's memory or string function, do not do anything
        if (isMemFuncName(fname) || isStringFuncName(fname)) 
        {
            dbg(errs() << ">>memory or string fn call: skipping..\n";)
            return changed;
        }
        // if it's memory intrinsic function, do not do anything
        if (dyn_cast<MemIntrinsic>(cb))
        {
            dbg(errs() << ">>LLVM memory intrinsic fn call: skipping..\n";)
            return changed;
        }

        changed = doCallFunction(cb, cfn);
    }
    else 
    {
        changed = doCallNonFunc(cb);
    }
    
    return changed;
}

bool 
SPPLTO::trackPtrs(Function* F) 
{

    dbg(errs() << "Function: " << F->getName() << "\n";)
    for (auto Arg = F->arg_begin(); Arg != F->arg_end(); ++Arg) 
    {
        if (Arg->getType()->isPointerTy() && 
            (Arg->hasAttribute(Attribute::ByVal) ||
             Arg->hasAttribute(Attribute::StructRet)))
        {
            dbg(errs()<<">> Already Cleaned Argument ByVal " << *Arg <<  "\n";)
            volPtrs.insert(Arg);  
            
            std::vector<User*> Users(Arg->user_begin(), Arg->user_end());
            for (auto User : Users) 
            {
                Instruction *iUser= dyn_cast<Instruction>(User);

                // mark directly derived values as volatile:
                switch (iUser->getOpcode()) 
                {
                    case Instruction::BitCast:
                    case Instruction::PtrToInt:
                    case Instruction::IntToPtr:
                    case Instruction::GetElementPtr:
                        volPtrs.insert(Arg);
                        dbg(errs() << ">>ByVal Arg ptr use: " << *iUser << "\n";)
                    default:
                        break;
                }                      
            }
        }
    }

    for (auto BI= F->begin(); BI!= F->end(); ++BI) 
    {
        BasicBlock *BB = &*BI; 

        for (auto II = BB->begin(); II != BB->end(); ++II) 
        {    
            Instruction* Ins= &*II;

            if (isa<AllocaInst>(Ins)) 
            {
                volPtrs.insert(Ins);  
                dbg(errs()<<"Local: "<< *Ins <<"\n";)
                std::vector<User*> Users(Ins->user_begin(), Ins->user_end());
                for (auto User : Users) 
                {
                    Instruction *iUser= dyn_cast<Instruction>(User);
                    dbg(errs() << ">>Local ptr use: " << *iUser << "\n";)

                    // mark directly derived values as volatile:
                    switch (iUser->getOpcode()) 
                    {
                        case Instruction::BitCast:
                        case Instruction::PtrToInt:
                        case Instruction::IntToPtr:
                        case Instruction::GetElementPtr:
                            volPtrs.insert(iUser);
                            dbg(errs() << ">>Local ptr use: " << *iUser << "\n";)
                        default:
                            break;
                    }                      
                }
            }
            else if (auto *CI = dyn_cast<CallInst>(Ins)) 
            { 
                Function* CalleeF = CI->getCalledFunction();
                if (!CalleeF) continue;

                //- Volatile Ptr -// 
                if (isAllocLikeFn(CI, getTLI(*CalleeF)) ||
                    isReallocLikeFn(CI, getTLI(*CalleeF)) ||
                    CalleeF->getName().contains("__errno_location") ||
                    CalleeF->getName().startswith("__cxa_")) 
                {
                    volPtrs.insert(Ins);
                    dbg(errs()<<"malloc/calloc/realloc/exception ptr: " << *Ins << "\n";)

                    std::vector<User*> Users(Ins->user_begin(), Ins->user_end());
                    for (auto User : Users) 
                    {
                        Instruction *iUser= dyn_cast<Instruction>(User);
                        dbg(errs() << ">>vol ptr use: " << *iUser << "\n";)

                        // mark directly derived values as volatile:
                        switch (iUser->getOpcode()) 
                        {
                            case Instruction::BitCast:
                            case Instruction::PtrToInt:
                            case Instruction::IntToPtr:
                            case Instruction::GetElementPtr:
                                volPtrs.insert(iUser);
                            default:
                                break;
                        }  
                    }
                }
                //- already cleaned ptr -//
                if (CalleeF->getName().contains("__spp_cleantag") ||
                    CalleeF->getName().contains("__spp_memintr_check_and_clean") ||
                    CalleeF->getName().contains("__spp_checkbound")) 
                {
                    volPtrs.insert(Ins);
                    dbg(errs()<<"malloc/calloc/realloc/exception ptr: " << *Ins << "\n";)

                    std::vector<User*> Users(Ins->user_begin(), Ins->user_end());
                    for (auto User : Users) 
                    {
                        Instruction *iUser= dyn_cast<Instruction>(User);
                        dbg(errs() << ">>vol ptr use: " << *iUser << "\n";)

                        // mark directly derived values as volatile:
                        switch (iUser->getOpcode()) 
                        {
                            case Instruction::BitCast:
                            case Instruction::PtrToInt:
                            case Instruction::IntToPtr:
                            case Instruction::GetElementPtr:
                                volPtrs.insert(iUser);
                            default:
                                break;
                        }  
                    }
                }                
                //- PM ptr -//
                else if (CalleeF->getName().contains("pmemobj_direct")) {
                    pmemPtrs.insert(Ins);
                    dbg(errs()<<"PM ptr: "<<*Ins<<"\n";)
                    std::vector<User*> Users(Ins->user_begin(), Ins->user_end());
                    for (auto User : Users) 
                    {
                        Instruction *iUser= dyn_cast<Instruction>(User);
                        dbg(errs() << ">>pm ptr use: " << *iUser << "\n";)

                        // mark directly derived values as volatile:
                        switch (iUser->getOpcode()) 
                        {
                            case Instruction::BitCast:
                            case Instruction::GetElementPtr:
                                pmemPtrs.insert(iUser);
                            default:
                                break;
                        }  
                    }
                }
            }
            /* vtable,vbase and vfn variables */
            else if (Ins->getName().startswith("vbase.offset") ||
                    Ins->getName().startswith("vfn") ||
                    Ins->getName().startswith("vtable"))
            {
                vtPtrs.insert(Ins);
                dbg(errs()<<"Vtable ptr: "<<*Ins<<"\n";)
                std::vector<User*> Users(Ins->user_begin(), Ins->user_end());
                for (auto User : Users) 
                {
                    Instruction *iUser= dyn_cast<Instruction>(User);
                    dbg(errs() << ">>Virtual ptr use: " << *iUser << "\n";)
                    // mark directly derived values as volatile:
                    switch (iUser->getOpcode()) 
                    {
                        case Instruction::BitCast:
                        case Instruction::PtrToInt:
                        case Instruction::IntToPtr:
                        case Instruction::GetElementPtr:
                        case Instruction::ExtractValue:
                        case Instruction::InsertValue:
                            vtPtrs.insert(iUser);
                        default:
                            break;
                    }  
                }
            }
            else if (auto *EV = dyn_cast<ExtractValueInst>(Ins)) 
            {
                assert(!EV->getOperand(0)->getType()->isPointerTy() && 
                        "Extract value with ptr operand currently not supported");
            }
            else if (auto *IV = dyn_cast<InsertValueInst>(Ins)) 
            {
                assert(!IV->getOperand(0)->getType()->isPointerTy() && 
                        "Insert value with ptr operand currently not supported");
            }
        }
    } //endof forloop

    return false;
}

bool
SPPLTO::redundantCB(Function *FN)
{
    bool changed = false;

    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        { 
            if (auto cb = dyn_cast<CallInst>(ins)) 
            {
                Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
                if (cfn)
                {
                    if (cfn->getName().contains("__spp_checkbound") ||
                        cfn->getName().contains("__spp_updatetag") || 
                        cfn->getName().contains("__spp_cleantag"))
                    {
                        dbg(errs() << ">>CallBase: "<<*cb<<"\n";)
                        for (auto Arg = cb->arg_begin(); Arg != cb->arg_end(); ++Arg) 
                        {   
                            Value *ArgVal = dyn_cast<Value>(Arg);
                            if (!ArgVal) 
                            {
                                dbg(errs() << ">>Argument skipping.. Not a value\n";)
                                continue;
                            }
                            
                            // Now we got a Value arg. 
                            if (!ArgVal->getType()->isPointerTy()) 
                            {
                                dbg(errs()<<">>Argument skipping.. Not pointerType\n";)
                                continue;
                            }

                            // stripPointerCasts() is needed to identify untracked bitcasts
                            if ( extPtrs.find(ArgVal->stripPointerCasts()) != extPtrs.end() ||
                                 globalPtrs.find(ArgVal->stripPointerCasts()) != globalPtrs.end() ||
                                 volPtrs.find(ArgVal->stripPointerCasts()) != volPtrs.end() ||
                                 vtPtrs.find(ArgVal->stripPointerCasts()) != vtPtrs.end() )
                            {   
                                //replace uses of the returned value with ArgVal
                                //and remove the function call
                                dbg(errs() << ">>ext or vol ptr -- should skip : " << *cb << " Uses: " \
                                            << cb->getNumUses() << " argval: " << *ArgVal << "\n";)
                                cb->replaceAllUsesWith(ArgVal);

                                std::vector<User*> Users(ArgVal->user_begin(), ArgVal->user_end());
                                for (auto User : Users) 
                                {
                                    Instruction *iUser= dyn_cast<Instruction>(User);
                                    dbg(errs() << ">>New external ptr use: " << *iUser << "\n";)

                                    // mark new directly derived values as external:
                                    switch (iUser->getOpcode()) 
                                    {
                                        case Instruction::BitCast:
                                        case Instruction::PtrToInt:
                                        case Instruction::IntToPtr:
                                        case Instruction::GetElementPtr:
                                            extPtrs.insert(iUser);
                                        default:
                                            break;
                                    }                      
                                }

                                redundantChecks.push_back(cb);
                                break;
                            }
                            else 
                            {
                                dbg(errs() << ">>remaining CallBase: "<<*cb<<"\n";)
                            }
                        }
                    }
                }
            }
        }
    }
    return changed;
}

bool
SPPLTO::runOnFunction(Function *FN, Module &M)
{
    bool changed = false;

    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        {
            if (auto cb = dyn_cast<CallBase>(ins)) 
            {
                changed= doCallBase(&*cb); 
            }
        }
    }
    return changed;
}

bool
SPPLTO::runOnModule(Module &M)
{    
    errs() << ">>Starting SPPLTO pass\n";
    errs() << ">>" << __func__ << " : " << M.getModuleIdentifier() << "\n";
    
    /*
    * DO NOT DELETE the following lines,
    *   -- returning if 'main' doesnt exist)!!!
    * Deleting it causes unit test failures, and
    * LLVM errors - Immutable passes not initialised, since
    * it just exits without returning to LLVM pass manager.
    * LLVM just loses track of it, and emits errors.
    */

    if (!M.getFunction("main")) 
    {
        errs() << "!>ALERT: No main found in module\n";
        // for (auto curFref = M.getFunctionList().begin(), 
        //     endFref = M.getFunctionList().end(); 
        //     curFref != endFref; ++curFref) {
        //     errs() << ">>Found function: " << curFref->getName() << "\n";
        // }
        // return false; /// DON'T DELETE ME!!
    }
    
    setTLIWP(&getAnalysis<TargetLibraryInfoWrapperPass>());

    //Track global ptrs
    for (auto GV = M.global_begin(); GV!=M.global_end(); GV++) 
    {
        dbg(errs() << "Global found : " << *GV << "\n";)
        globalPtrs.insert(&*GV);
        std::vector<User*> Users(GV->user_begin(), GV->user_end());
        for (auto User : Users) 
        {
            Instruction *iUser= dyn_cast<Instruction>(User);
            if (iUser && iUser->getType()->isPointerTy())
            {
                dbg(errs() << ">>Global use: " << *iUser << "\n";)
                // mark directly derived values as volatile:
                switch (iUser->getOpcode()) 
                {
                    case Instruction::BitCast:
                    case Instruction::PtrToInt:
                    case Instruction::IntToPtr:
                    case Instruction::GetElementPtr:
                        globalPtrs.insert(iUser);
                        dbg(errs() << ">>Global ptr use: " << *iUser << "\n";)
                    default:
                        break;
                }
            }                     
        }

    }

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    {
        trackPtrs(&*Fn);
    }

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    {
        dbg(errs() << ">>FName: " << Fn->getName() << "\n";)
        // errs() << *Fn << "\n";
        if (Fn->isDeclaration()) 
        {
            dbg(errs() << ">>declaration: skipping..\n";)
            continue;
        } 
        if (isSPPFuncName(Fn->getName())) // hook func names are not mangled.
        { 
            dbg(errs() << ">>SPP hooks: skipping..\n";)
            continue;
        }
        if (isMemFuncName(Fn->getName())) 
        {
            dbg(errs() << ">>Memory func: skipping..\n";)
            continue;
        } 

        runOnFunction(&*Fn, M);
    }

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    { 
        redundantCB(&*Fn);
    }

    if (!hasZeroRedundantChecks()) {
        eraseRedundantChecks(); 
    }
 
    // for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    // {
    //     for (auto BB = Fn->begin(); BB != Fn->end(); ++BB) 
    //     {
    //         BasicBlock *BaB = &*BB; 
    //         if (BaB == &BaB->getParent()->getEntryBlock())
    //             errs() << *Fn <<"\n";
    //         errs() << *BB << "\n";
    //     }
    // }

    // errs() << M << "\n";
    
    memCleanUp();

    errs() << ">>Leaving SPPLTO\n";

    return true;
}

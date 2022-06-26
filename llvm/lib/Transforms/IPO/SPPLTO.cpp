///////////////////////////////////////////
///                                     ///
///           /IPO/SPPLTO.cpp           ///
///           (clangllvm.12.0)          ///
///                                     ///
///////////////////////////////////////////


#include "llvm/Analysis/PostDominators.h"
#include <llvm/IR/Dominators.h>
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
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
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

  enum operandType {
        VOL,
        PM,
        CONST,
        UKNOWN,
        MAX_TYPE
  };

  SPPLTO() : ModulePass(ID) 
  {
    initializeSPPLTOPass(*PassRegistry::getPassRegistry());
  }
  
  virtual bool redundantCB(Function *F);
  virtual bool redundantTagUpdates(Function *F);
  virtual bool duplicateCleanTags(Function *F);
  virtual bool duplicateUpdateTags(Function *FN);
  virtual bool duplicateCheckBounds(Function *F);
  virtual bool mergeTagUpdates(Function *F);  

  virtual bool trackPtrs (Function * F);
  virtual void trackFnArgs(Function* F);
  virtual void propagateFnArgsTypes(Function* F);
  virtual void assessPtrArgs(Module* M);

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
static std::unordered_set <Value*> untaggedPtrs;
static std::unordered_set <Value*> pmemPtrs;
static std::unordered_set <Value*> vtPtrs;

static std::vector<Instruction*> redundantChecks;
DenseMap<Value*, SPPLTO::operandType> FnArgType;
DenseMap<Value*, Function*> FnArgFun;

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

static void setSPPprefix(Value *V) {
    // Void values can not have a name
    if (V->getType()->isVoidTy())
        return;
            
    // Don't corrupt externally visable symbols
    GlobalValue *GV = dyn_cast<GlobalValue>(V);
    if (GV && GV->isDeclarationForLinker())
        return;

    // Don't name values that are not globals or instructions
    if (!GV && !isa<Instruction>(V))
        return;

    // Add name to anonymous instructions
    if (!V->hasName()) {
        V->setName("spp.pm.anon");
        return;
    }

    // Don't corrupt llvm.* names
    if (V->getName().startswith("llvm."))
        return;

    // Don't rename twice
    if (V->getName().startswith("spp."))
        return;

    // Default: prefix name with "safe."
    V->setName(Twine("spp.pm.") + V->getName());
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
    redundantChecks.clear();
}
        
static void memCleanUp()
{
    redundantChecks.clear();
    untaggedPtrs.clear();
    globalPtrs.clear();
    pmemPtrs.clear();
    vtPtrs.clear();
    FnArgType.clear();
    FnArgFun.clear();
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
    Masked->setDoesNotThrow(); 
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
        !CB->getCalledFunction()->getName().contains("pmemobj_direct") &&
        !(StringRef(CB->getCalledFunction()->getName()).startswith("pmem::obj::persistent_ptr") && 
          StringRef(CB->getCalledFunction()->getName()).contains("spp_get()")) &&
        !CB->getCalledFunction()->getName().equals("__spp_updatetag_direct"))
    {
        Value *CBval = dyn_cast<Value>(CB);
        if (CBval)
        {
            untaggedPtrs.insert(CBval);
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
                        untaggedPtrs.insert(iUser);
                    default:
                        break;
                }                      
            }
        }
    }
    
    Module *mod = CB->getModule();
    Type *vpty = Type::getInt8PtrTy(mod->getContext());
    FunctionType *fty = FunctionType::get(vpty, vpty, false);
    
    FunctionCallee hook_generic = 
        mod->getOrInsertFunction("__spp_cleantag_external", fty); 
    FunctionCallee hook_direct = 
        mod->getOrInsertFunction("__spp_cleantag_external_direct", fty); 

    for (auto Arg = CB->arg_begin(); Arg != CB->arg_end(); ++Arg) 
    {   
        Value *ArgVal = dyn_cast<Value>(Arg);
        FunctionCallee hook;

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

        if ( untaggedPtrs.find(ArgVal->stripPointerCasts()) != untaggedPtrs.end() ||
             vtPtrs.find(ArgVal->stripPointerCasts()) != vtPtrs.end() ||
             globalPtrs.find(ArgVal->stripPointerCasts()) != globalPtrs.end() )
        {
            dbg(errs() << ">>global or volatile ptr skipped cleaning: " << *CB << "\n";)
            continue;
        }
        else if (pmemPtrs.find(ArgVal->stripPointerCasts()) != pmemPtrs.end() ||
                (CB->getCalledFunction() != NULL && CB->getCalledFunction()->getName().equals("pmemobj_pool_by_ptr")))
        {
            dbg(errs() << ">>direct cleantag external inserted for: " << *CB << "\n";)
            hook = hook_direct;
        }
        else
        {
            hook = hook_generic;
        }

        IRBuilder<> B(CB);
        vector <Value*> arglist;

        Value *TmpPtr = B.CreateBitCast(ArgVal, 
                        hook.getFunctionType()->getParamType(0));
        arglist.push_back(TmpPtr);
        CallInst *Masked = B.CreateCall(hook, arglist);
        Masked->setDoesNotThrow(); 
        Value *Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 

        CB->setArgOperand(Arg - CB->arg_begin(), Unmasked);
        untaggedPtrs.insert(Unmasked);

        dbg(errs() << ">>new_CB after masking: " << *CB << "\n";)
        dbg(errs() << "inserted : " << *Masked << " in " << CB->getFunction()->getName() << "\n";)

        changed = true;
    }
    
    return changed;
}

static bool
doCallNonFunc(CallBase *cb)
{
    return doCallExternal(cb);
}

static bool doCallFunction(CallBase *cb, Function *cfn)
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
    
    // Ignore exception handling calls and free calls
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

void 
SPPLTO::assessPtrArgs(Module* M)
{
    // initially add the args to their respective categories
    for (auto it : FnArgType)
    {
        Value* ArgVal= it.first;
        operandType Type = it.second;
        if (ArgVal && Type == PM)
        {
            dbg(errs() << FnArgFun[ArgVal]->getName() << " PM argument found " << *ArgVal << "\n";)
            pmemPtrs.insert(ArgVal);
            setSPPprefix(ArgVal);

        }
        else if (ArgVal && Type == VOL)
        {
            dbg(errs() << FnArgFun[ArgVal]->getName() << " VOL argument found " << *ArgVal << "\n";)
            untaggedPtrs.insert(ArgVal);
            std::vector<User*> Users(ArgVal->user_begin(), ArgVal->user_end());
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
                        dbg(errs() << ">>VOL argument ptr use: " << *iUser << "\n";)
                        untaggedPtrs.insert(iUser);
                    default:
                        break;
                }                      
            }
        }
        else if (ArgVal && Type == MAX_TYPE)
        {
            dbg(errs() << ">>" << FnArgFun[ArgVal]->getName() << " : Didn't find a call with " << *ArgVal << "\n";)
        }
    }

    //go through the code again to completely propagate through subsequent bitcasts and GEPs
    for (auto F = M->begin(), Fend = M->end(); F != Fend; ++F) 
    {
        for (auto BB= F->begin(); BB!= F->end(); ++BB)
        {
            for (auto II = BB->begin(); II != BB->end(); ++II) 
            {
                Instruction* Ins= &*II;
                if (auto *Gep = dyn_cast<GetElementPtrInst>(Ins)) 
                {
                    Value *Operand = Gep->getPointerOperand()->stripPointerCasts();
                    if (pmemPtrs.find(Operand) != pmemPtrs.end())
                    {
                        dbg(errs() << "new pm ptr\n";)
                        pmemPtrs.insert(Gep);
                        setSPPprefix(Gep);
                    }
                    else if (untaggedPtrs.find(Operand) != untaggedPtrs.end() ||
                            globalPtrs.find(Operand) != globalPtrs.end() ||
                            vtPtrs.find(Operand) != vtPtrs.end())
                    {
                        dbg(errs() << "new vol ptr\n";)
                        untaggedPtrs.insert(Gep);
                    }
                }
                else if (auto *Bitcast = dyn_cast<BitCastInst>(Ins)) 
                {
                    Value *Operand = Bitcast->getOperand(0)->stripPointerCasts();
                    if (pmemPtrs.find(Operand) != pmemPtrs.end())
                    {
                        dbg(errs() << "new pm ptr\n";)
                        pmemPtrs.insert(Bitcast);
                        setSPPprefix(Bitcast);
                    }
                    else if (untaggedPtrs.find(Operand) != untaggedPtrs.end() ||
                            globalPtrs.find(Operand) != globalPtrs.end() ||
                            vtPtrs.find(Operand) != vtPtrs.end())
                    {
                        dbg(errs() << "new vol ptr " << *Bitcast << "\n";)
                        untaggedPtrs.insert(Bitcast);
                    }
                }
            }
        }
    }
}

void 
SPPLTO::propagateFnArgsTypes(Function* F) 
{
    for (auto BI= F->begin(); BI!= F->end(); ++BI) 
    {
        BasicBlock *BB = &*BI; 

        for (auto II = BB->begin(); II != BB->end(); ++II) 
        {
            Instruction* Ins= &*II;
            // CallBase to include CallInst and InvokeInst
            if (auto *CI = dyn_cast<CallBase>(Ins))
            {   
                dbg(errs() << "call :" << *CI << "\n";)
                for (auto Arg = CI->arg_begin(); Arg != CI->arg_end(); ++Arg) 
                {
                    Value *ArgVal = dyn_cast<Value>(Arg);
                    if (ArgVal->getType()->isPointerTy())
                    {
                        unsigned argIdx = CI->getArgOperandNo(Arg);
                        dbg(errs() << "PtrArg: " << *ArgVal->stripPointerCasts() << " in position " << argIdx <<"\n";)
                        Function* CalleeF = CI->getCalledFunction();

                        if (!CalleeF) 
                        {
                            continue;
                        }   
                        if (CalleeF->isDeclaration())
                        {
                            dbg(errs() << "skipped decl " << CalleeF->getName() << " from " << *CI << "\n";)
                            continue; // external funcs, cleaned anyway
                        }
                        if (CalleeF->arg_size() <= argIdx) 
                        {
                            dbg(errs() << "skipped arg " << CalleeF->getName() << " from " << *CI << "\n";)
                            continue; // functions with arbitrary args cannot be tracked
                        }

                        if (pmemPtrs.find(ArgVal->stripPointerCasts()) != pmemPtrs.end())
                        {
                            Value* FnArg = CalleeF->getArg(argIdx);
                            if (FnArgType[FnArg] == MAX_TYPE)
                                FnArgType[FnArg] = PM;
                            else if (FnArgType[FnArg] != PM)
                                FnArgType[FnArg] = UKNOWN;
                        }
                        else if (untaggedPtrs.find(ArgVal->stripPointerCasts()) != untaggedPtrs.end() ||
                                    globalPtrs.find(ArgVal->stripPointerCasts()) != globalPtrs.end() ||
                                    vtPtrs.find(ArgVal->stripPointerCasts()) != vtPtrs.end())
                        {
                            Value* FnArg = CalleeF->getArg(argIdx);
                            if (FnArgType[FnArg] == MAX_TYPE)
                                FnArgType[FnArg] = VOL;
                            else if (FnArgType[FnArg] != VOL)
                                FnArgType[FnArg] = UKNOWN;
                        }
                        else 
                        {
                            Value* FnArg = CalleeF->getArg(argIdx);
                            FnArgType[FnArg] = UKNOWN;
                        }
                        
                        dbg(Value* FnArg = CalleeF->getArg(argIdx);)
                        dbg(errs() << "FnArg: " << *FnArg << " type : " << FnArgType[FnArg] << "\n";)
                        dbg(errs() << "Function :" << CalleeF->getName() << "\n";)
                        dbg(errs() << "respective arg: " << *CalleeF->getArg(argIdx) << "\n";)
                    }
                }
            }
        }
    }
    return;
}

void 
SPPLTO::trackFnArgs(Function* F) 
{
    dbg(errs() << "Function: " << demangleName(F->getName()) << " with " << F->arg_size() << " argument(s): \n";)
    dbg(errs() << "real fname: " << F->getName() << "\n";)
    for (auto Arg = F->arg_begin(); Arg != F->arg_end(); ++Arg) 
    {
        Value *ArgVal = dyn_cast<Value>(Arg);
        if (ArgVal->getType()->isPointerTy())
        {
            dbg(errs() << "PtrArg: "<< *ArgVal << "\n";)
            FnArgType[ArgVal] = MAX_TYPE;
            FnArgFun[ArgVal] = F;
        }

    }
    return;
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
            dbg(errs()<<">> Already Cleaned Argument ByVal/SRET " << *Arg <<  "\n";)
            untaggedPtrs.insert(Arg);  
            
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
                        untaggedPtrs.insert(Arg);
                        dbg(errs() << ">> ByVal/SRET Arg ptr use: " << *iUser << "\n";)
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
                untaggedPtrs.insert(Ins);  
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
                            untaggedPtrs.insert(iUser);
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

                std::string CalleeFName = demangleName(CalleeF->getName());

                //- Volatile Ptr -// 
                if (isAllocLikeFn(CI, getTLI(*CalleeF)) ||
                    isReallocLikeFn(CI, getTLI(*CalleeF)) ||
                    CalleeF->getName().contains("__errno_location") ||
                    CalleeF->getName().equals("_Znwm") || //new cpp
                    CalleeF->getName().equals("_Znam") || //new cpp
                    CalleeF->getName().startswith("__cxa_")) 
                {
                    untaggedPtrs.insert(Ins);
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
                                untaggedPtrs.insert(iUser);
                            default:
                                break;
                        }  
                    }
                }
                // Arguments of a free call are volatile ptrs
                else if (isFreeCall(CI, getTLI(*CalleeF)) ||
                         CalleeF->getName().equals("_ZdlPv") || //free cpp
                         CalleeF->getName().equals("_ZdaPv")) //free cpp
                {
                    Value *Operand = Ins->getOperand(0)->stripPointerCasts();
                    dbg(errs()<<"call to free ptr: " << *Ins << " Op : " << *Operand << "\n";)
                    
                    // This check exists for the case of a mid-pipeline optimization pass
                    // where free func can get null argument before being eliminated
                    if (!isa<ConstantPointerNull>(Operand))
                    {
                        untaggedPtrs.insert(Operand);

                        std::vector<User*> Users(Operand->user_begin(), Operand->user_end());
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
                                    untaggedPtrs.insert(iUser);
                                default:
                                    break;
                            }  
                        }
                    }
                } 
                //- already cleaned ptr -//
                else if (CalleeF->getName().contains("__spp_cleantag") ||
                    CalleeF->getName().contains("__spp_memintr_check_and_clean") ||
                    CalleeF->getName().contains("__spp_checkbound")) 
                {
                    untaggedPtrs.insert(Ins);
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
                                untaggedPtrs.insert(iUser);
                            default:
                                break;
                        }  
                    }
                }                
                //- PM ptr -//
                else if ( CalleeF->getName().contains("pmemobj_direct") ||
                        (StringRef(CalleeFName).startswith("pmem::obj::persistent_ptr") && 
                         StringRef(CalleeFName).contains("spp_get()")) ||
                         CalleeF->getName().equals("__spp_updatetag_direct"))
                        //  CalleeF->getName().contains("pmemobj_oid")) 
                {
                    pmemPtrs.insert(Ins);
                    setSPPprefix(Ins);
                    dbg(errs()<<"LTO PM ptr: "<<*Ins<<"\n";)
                    std::vector<User*> Users(Ins->user_begin(), Ins->user_end());
                    for (auto User : Users) 
                    {
                        Instruction *iUser= dyn_cast<Instruction>(User);
                        dbg(errs() << ">>pm ptr use: " << *iUser << "\n";)

                        // mark directly derived values as persistent:
                        switch (iUser->getOpcode()) 
                        {
                            case Instruction::BitCast:
                            case Instruction::GetElementPtr:
                                pmemPtrs.insert(iUser);
                                setSPPprefix(iUser);
                            default:
                                break;
                        }  
                    }
                }
                // pmemobj_pool_by_ptr, pmemobj_tx_xadd_range_direct and pmemobj_tx_add_range_direct
                // only take PM ptrs as arguments
                else if ( CalleeF->getName().equals("pmemobj_pool_by_ptr") ||
                        CalleeF->getName().equals("pmemobj_tx_xadd_range_direct") ||
                        CalleeF->getName().equals("pmemobj_tx_add_range_direct"))
                {
                    Value* PMptr = Ins->getOperand(0);
                    dbg(errs() << ">> LTO pass PM ptr from PMDK funcs: " << *PMptr << " from " << *Ins << "\n";)
                    std::vector <Value*> trackOrigins;
                    trackOrigins.push_back(PMptr);
                    pmemPtrs.insert(PMptr);
                    setSPPprefix(PMptr);

                    while (!trackOrigins.empty())
                    {                                
                        Value* curr = trackOrigins.front();
                        if (Instruction *iUser = dyn_cast<Instruction>(curr))
                        {
                            switch (iUser->getOpcode()) 
                            {
                                case Instruction::BitCast:
                                case Instruction::GetElementPtr:
                                    dbg(errs() << ">> LTO pass PM ptr from PMDK funcs: " << *iUser->getOperand(0) << " from " << *Ins << "\n";)
                                    pmemPtrs.insert(iUser->getOperand(0));
                                    setSPPprefix(iUser->getOperand(0));
                                    trackOrigins.push_back(iUser->getOperand(0));
                                default:
                                    break;
                            }
                        }
                        trackOrigins.erase(trackOrigins.begin());
                    }
                }
                //- PM ptr progataion for update tag -//
                else if (CalleeF->getName().contains("__spp_updatetag")) {                    
                    dbg(errs() << "update tag prop candidate : " << *Ins <<" Arg: " << *CI->getArgOperand(0)->stripPointerCasts() << "\n";)
                    // get the update tag argument
                    Value *ArgVal = dyn_cast<Value>(CI->getArgOperand(0));
                    
                    if (ArgVal && ArgVal->getType()->isPointerTy())
                    {
                        if (pmemPtrs.find(ArgVal->stripPointerCasts()) != pmemPtrs.end())
                        {
                            pmemPtrs.insert(Ins);
                            setSPPprefix(Ins);
                            dbg(errs() << "update tag prop: "  <<*Ins <<" Arg: " << *CI->getArgOperand(0) << "\n";)
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
                                        setSPPprefix(iUser);
                                    default:
                                        break;
                                }  
                            }
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
            else if (auto *Gep = dyn_cast<GetElementPtrInst>(Ins)) 
            {
                Value *Operand = Gep->getPointerOperand()->stripPointerCasts();
                if (pmemPtrs.find(Operand) != pmemPtrs.end())
                {
                    pmemPtrs.insert(Gep);
                    setSPPprefix(Gep);
                }
                else if (untaggedPtrs.find(Operand) != untaggedPtrs.end() ||
                         globalPtrs.find(Operand) != globalPtrs.end() ||
                         vtPtrs.find(Operand) != vtPtrs.end())
                {
                    dbg(errs() << "GEP propagation " << *Bitcast << "\n";)
                    untaggedPtrs.insert(Gep);
                }
            }
            else if (auto *Bitcast = dyn_cast<BitCastInst>(Ins)) 
            {
                Value *Operand = Bitcast->getOperand(0)->stripPointerCasts();
                if (pmemPtrs.find(Operand) != pmemPtrs.end())
                {
                    pmemPtrs.insert(Bitcast);
                    setSPPprefix(Bitcast);
                }
                else if (untaggedPtrs.find(Operand) != untaggedPtrs.end() ||
                         globalPtrs.find(Operand) != globalPtrs.end() ||
                         vtPtrs.find(Operand) != vtPtrs.end())
                {
                    dbg(errs() << "Bitcast propagation " << *Bitcast << "\n";)
                    untaggedPtrs.insert(Bitcast);
                }
            }
            else if (auto *PHI = dyn_cast<PHINode>(Ins)) 
            {
                if (PHI->getType()->isPointerTy())
                {
                    dbg(errs() << ">>>" << *PHI <<"\n";)

                    operandType phiType = PM;
                    std::vector<Value*> Ops(PHI->op_begin(), PHI->op_end());
                    for (auto Op : Ops)
                    {
                        Value *StrippedOp = Op->stripPointerCasts();
                        dbg(errs() << *StrippedOp << " type : " << *StrippedOp->getType() << "\n";)
                        if (isa<Constant>(StrippedOp) ||
                            pmemPtrs.find(StrippedOp) != pmemPtrs.end())
                        {
                            dbg(errs() << *StrippedOp << " pm type : " << *StrippedOp->getType() << "\n";)
                            continue;
                        }
                        else
                        {
                            dbg(errs() << *StrippedOp << " ignored type : " << *StrippedOp->getType() << "\n";)
                            phiType = UKNOWN;
                            break;
                        }
                    }
                    if (phiType == PM)
                    {
                        dbg(errs() << "persistent phi: " << *PHI << "\n";)
                        pmemPtrs.insert(PHI);
                        setSPPprefix(PHI);
                        std::vector<User*> Users(PHI->user_begin(), PHI->user_end());
                        for (auto User : Users) 
                        {
                            Instruction *iUser= dyn_cast<Instruction>(User);
                            dbg(errs() << ">>PM ptr from PHI use: " << *iUser << "\n";)
                            // mark directly derived values as volatile:
                            switch (iUser->getOpcode()) 
                            {
                                case Instruction::BitCast:
                                case Instruction::GetElementPtr:
                                    pmemPtrs.insert(iUser);
                                    setSPPprefix(iUser);
                                default:
                                break;
                            }  
                        }
                        continue;
                    }
                    phiType = VOL;
                    for (auto Op : Ops)
                    {
                        Value *StrippedOp = Op->stripPointerCasts();
                        dbg(errs() << *StrippedOp << " type : " << *StrippedOp->getType() << "\n";)
                        if (isa<Constant>(StrippedOp) ||
                            untaggedPtrs.find(StrippedOp) != untaggedPtrs.end() ||
                            globalPtrs.find(StrippedOp) != globalPtrs.end() ||
                            vtPtrs.find(StrippedOp) != vtPtrs.end())
                        {
                            dbg(errs() << *StrippedOp << " vol type : " << *StrippedOp->getType() << "\n";)
                            continue;
                        }
                        else
                        {
                            dbg(errs() << *StrippedOp << " ignored type : " << *StrippedOp->getType() << "\n";)
                            phiType = UKNOWN;
                            break;
                        }
                    }
                    if (phiType == VOL)
                    {
                        dbg(errs() << "volatile phi: " << *PHI << "\n";)
                        untaggedPtrs.insert(PHI);
                        std::vector<User*> Users(PHI->user_begin(), PHI->user_end());
                        for (auto User : Users) 
                        {
                            Instruction *iUser= dyn_cast<Instruction>(User);
                            dbg(errs() << ">>vol ptr from PHI use: " << *iUser << "\n";)
                            // mark directly derived values as volatile:
                            switch (iUser->getOpcode()) 
                            {
                                case Instruction::BitCast:
                                case Instruction::PtrToInt:
                                case Instruction::IntToPtr:
                                case Instruction::GetElementPtr:
                                    untaggedPtrs.insert(iUser);
                                default:
                                break;
                            }  
                        }
                        continue;
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
SPPLTO::duplicateCleanTags(Function *FN)
{
    bool changed = false;
    
    DenseMap<Value*, Value*> cleanedVals;
    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        { 
            if (auto cb = dyn_cast<CallInst>(ins)) 
            {
                Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
                if (cfn)
                {
                    // Check for redundant updatetag calls that are directly cleaned
                    if (cfn->getName().contains("__spp_cleantag"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        if (cleanedVals.find(ArgVal) == cleanedVals.end()) 
                        {
                            cleanedVals[ArgVal] = cb;
                            dbg(errs() << *cb << " op : " << *ArgVal << "\n";)  
                        }
                        else 
                        {
                            DominatorTree DT = DominatorTree(*FN);
                            if (!DT.dominates(cleanedVals[ArgVal], cb))
                            {
                                dbg(errs() << "Non-dominated cleantag usage" << *cb << "\n";)
                            }
                            else
                            {
                                dbg(errs() << *cb << " duplicate cleantag : " << *ArgVal << "\n";)
                                dbg(errs() << "should be replaced with: " << *cleanedVals[ArgVal] << "\n";)
                                cb->replaceAllUsesWith(cleanedVals[ArgVal]);
                                redundantChecks.push_back(cb);
                            }
                        }
                    }
                }
            }
        }
    }
    cleanedVals.clear();
    return changed;
}

bool
SPPLTO::duplicateUpdateTags(Function *FN)
{
    bool changed = false;

    DenseMap<Value*, DenseMap<Value*, Value*>> updatedVals;
    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        // DenseMap<Value*, Value*> updatedVals;
        // DenseMap<Value*, Value*> offsetVals;
        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        { 
            if (auto cb = dyn_cast<CallInst>(ins)) 
            {
                Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
                if (cfn)
                {
                    // Check for redundant updatetag calls that have been performed already
                    if (cfn->getName().contains("__spp_updatetag"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        Value* Off = cb->getOperand(1)->stripPointerCasts();
                        
                        if (updatedVals.find(ArgVal) == updatedVals.end()) 
                        {
                            updatedVals[ArgVal][Off] = cb;
                            // offsetVals[ArgVal].push_back(Off);
                        }
                        else 
                        {
                            if (updatedVals[ArgVal].find(Off) != updatedVals[ArgVal].end())
                            {
                                DominatorTree DT = DominatorTree(*FN);
                                if (!DT.dominates(updatedVals[ArgVal][Off], cb))
                                {
                                    dbg(errs() << "Non-dominated updatetag usage" << *cb << "\n";)
                                }
                                else
                                {
                                    dbg(errs() << FN->getName() << " :there is a duplicate updatetag " << \
                                                *updatedVals[ArgVal][Off] << "\n";)
                                    cb->replaceAllUsesWith(updatedVals[ArgVal][Off]);
                                    redundantChecks.push_back(cb);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    updatedVals.clear();
    return changed;
}

bool
SPPLTO::duplicateCheckBounds(Function *FN)
{
    bool changed = false;
    DenseMap<Value*, Value*> checkedVals;
    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        { 
            if (auto cb = dyn_cast<CallInst>(ins)) 
            {
                Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
                if (cfn)
                {
                    // Check for redundant updatetag calls that are directly cleaned
                    if (cfn->getName().contains("__spp_checkbound"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        if (checkedVals.find(ArgVal) == checkedVals.end()) 
                        {
                            checkedVals[ArgVal] = cb;
                            dbg(errs() << *cb << " op : " << *ArgVal << "\n";)  
                        }
                        else 
                        {
                            DominatorTree DT = DominatorTree(*FN);
                            if (!DT.dominates(checkedVals[ArgVal], cb))
                            {
                                dbg(errs() << "Non-dominated checkbound usage" << *cb << "\n";)
                            }
                            else
                            {
                                dbg(errs() << *cb << " duplicate checkbound : " << *ArgVal << "\n";)
                                dbg(errs() << "should be replaced with: " << *checkedVals[ArgVal] << "\n";)
                                cb->replaceAllUsesWith(checkedVals[ArgVal]);
                                redundantChecks.push_back(cb);
                            }
                        }
                    }
                }
            }
        }
    }
    checkedVals.clear();
    return changed;
}

bool
SPPLTO::mergeTagUpdates(Function *FN)
{
    bool changed = false;

    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        Module* M = BB->getModule();

        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        { 
            if (auto cb = dyn_cast<CallInst>(ins)) 
            {
                Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
                if (cfn)
                {
                    // Check for updatetag calls that can be merged
                    if (cfn->getName().contains("__spp_updatetag"))
                    {
                        Value* ArgVal = cb->getOperand(0); // get the current ptr -- not the stripped
                        Value* Off = cb->getOperand(1)->stripPointerCasts(); // strip the casts to check for constant;
                        
                        if (ArgVal && isa<Constant>(Off))
                        {
                            bool canBeMerged = false;
                            // if the returned value has one use and this is in a GEP
                            // this updatetag can be merged with the one following the GEP
                            if (cb->hasOneUser())
                            {
                                User *U = cb->user_back();
                                if (auto *gep = dyn_cast<GetElementPtrInst>(U))
                                {
                                    dbg(errs() << *cb << " potential merge\n";)
                                    // loop over the uses of the gep to find the updatetag 
                                    // and merge with the initial one
                                    std::vector<User*> Users(gep->user_begin(), gep->user_end());
                                    for (auto User : Users) 
                                    {
                                        if (auto *updateCI= dyn_cast<CallInst>(User))
                                        {
                                            if (auto *fnCall = dyn_cast<Function>(updateCI->getCalledOperand()->stripPointerCasts()))
                                            {
                                                if (fnCall->getName().contains("__spp_updatetag")) {
                                                    Value* updOff = updateCI->getOperand(1)->stripPointerCasts();
                                                    if (isa<Constant>(updOff))
                                                    {
                                                        dbg(errs() << "merge via gep " << *cb << " with " << *updateCI << "\n";)
                                                        int64_t firstOff = (cast<ConstantInt>(Off))->getSExtValue();
                                                        int64_t secondOff = (cast<ConstantInt>(updOff))->getSExtValue();
                                                        int64_t totalOff = firstOff + secondOff;
                                                        Value *newOff = ConstantInt::get(Type::getInt64Ty(M->getContext()), totalOff);
                                                        // change the GEP operand to the argument of the initial updatetag call
                                                        gep->setOperand(0, ArgVal);
                                                        // update the offset of the next updatetag with the offset of the first one
                                                        updateCI->setOperand(1, newOff);
                                                        // remove the initial updatetag call
                                                        redundantChecks.push_back(cb);
                                                        errs() << "results CI: " << *updateCI << " changed gep: " << *gep <<"\n";
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                else if (auto *updateCI = dyn_cast<CallInst>(U))
                                {
                                    if (auto *fnCall = dyn_cast<Function>(updateCI->getCalledOperand()->stripPointerCasts()))
                                    {
                                        if (fnCall->getName().contains("__spp_updatetag")) {
                                            Value* updOff = updateCI->getOperand(1)->stripPointerCasts();
                                            if (isa<Constant>(updOff))
                                            {
                                                dbg(errs() << "direct merge " << *cb << " with " << *updateCI << "\n";)
                                                int64_t firstOff = (cast<ConstantInt>(Off))->getSExtValue();
                                                int64_t secondOff = (cast<ConstantInt>(updOff))->getSExtValue();
                                                int64_t totalOff = firstOff + secondOff;
                                                Value *newOff = ConstantInt::get(Type::getInt64Ty(M->getContext()), totalOff);
                                                // update the ptr of the next updatetag with the ptr of the first one
                                                updateCI->setOperand(0, ArgVal);
                                                // update the offset of the next updatetag with the offset of the first one
                                                updateCI->setOperand(1, newOff);
                                                // remove the initial updatetag call
                                                redundantChecks.push_back(cb);
                                            }
                                        }
                                    }
                                }
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
SPPLTO::redundantTagUpdates(Function *FN)
{
    bool changed = false;
    
    DenseMap<Value*, DenseMap<Value*, Value*>> updatedVals;
    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        { 
            if (auto cb = dyn_cast<CallInst>(ins)) 
            {
                Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
                if (cfn)
                {
                    // Check for redundant updatetag calls that have been performed already
                    if (cfn->getName().contains("__spp_updatetag"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        Value* Off = cb->getOperand(1)->stripPointerCasts();
                        
                        if (updatedVals.find(ArgVal) == updatedVals.end()) 
                        {
                            updatedVals[ArgVal][Off] = cb;
                            // offsetVals[ArgVal].push_back(Off);
                        }
                        else 
                        {
                            if (updatedVals[ArgVal].find(Off) != updatedVals[ArgVal].end())
                            {
                                DominatorTree DT = DominatorTree(*FN);
                                if (!DT.dominates(updatedVals[ArgVal][Off], cb))
                                {
                                    dbg(errs() << "Non-dominated updatetag usage" << *cb << "\n";)
                                }
                                else
                                {
                                    dbg(errs() << FN->getName() << " :there is a duplicate updatetag " << \
                                                *updatedVals[ArgVal][Off] << "\n";)
                                    cb->replaceAllUsesWith(updatedVals[ArgVal][Off]);
                                    redundantChecks.push_back(cb);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    updatedVals.clear();
    return changed;
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
                        cfn->getName().contains("__spp_cleantag") ||
                        cfn->getName().contains("__spp_memintr_check_and_clean"))
                    {
                        dbg(errs() << ">>CallBase: "<<*cb<<"\n";)
    
                        if (cb->getNumUses() == 0){
                            dbg(errs() << "no use :" << *cb << "\n";)
                            dbg(errs() << "added " << *cb << " from " << FN->getName() << "\n";)
                            redundantChecks.push_back(cb);
                            continue;
                        }

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
                            if ( globalPtrs.find(ArgVal->stripPointerCasts()) != globalPtrs.end() ||
                                 untaggedPtrs.find(ArgVal->stripPointerCasts()) != untaggedPtrs.end() ||
                                 vtPtrs.find(ArgVal->stripPointerCasts()) != vtPtrs.end() ||
                                 isa<Constant>(ArgVal) )
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
                                    if (iUser)
                                    {
                                        dbg(errs() << ">>New external ptr use: " << *iUser << "\n";)

                                        // mark new directly derived values as external:
                                        switch (iUser->getOpcode()) 
                                        {
                                            case Instruction::BitCast:
                                            case Instruction::PtrToInt:
                                            case Instruction::IntToPtr:
                                            case Instruction::GetElementPtr:
                                                untaggedPtrs.insert(iUser);
                                            default:
                                                break;
                                        }
                                    }
                                    else
                                    {
                                        dbg(errs() << "not an ins ptr use:" << *User << "\n";)
                                    }                
                                }
                                dbg(errs() << "added " << *cb << " from " << FN->getName() << "\n";)
                                redundantChecks.push_back(cb);
                                break;
                            }
                            else if (pmemPtrs.find(ArgVal->stripPointerCasts()) != pmemPtrs.end())
                            {
                                dbg(errs() << *cb << " could have been direct\n";)
                                if (!cfn->getName().endswith("_direct")) 
                                {
                                    IRBuilder<> B(cb);
                                    Module *mod = cb->getModule();
                                    StringRef FnName;
                                    if (cfn->getName().equals("__spp_checkbound"))
                                        FnName = "__spp_checkbound_direct";
                                    else if (cfn->getName().equals("__spp_updatetag"))
                                        FnName = "__spp_updatetag_direct";
                                    else if (cfn->getName().equals("__spp_cleantag"))
                                        FnName = "__spp_cleantag_direct";
                                    else if (cfn->getName().equals("__spp_cleantag_external"))
                                        FnName = "__spp_cleantag_external_direct";
                                    else if (cfn->getName().equals("__spp_memintr_check_and_clean"))
                                        FnName = "__spp_memintr_check_and_clean_direct";
                                    
                                    FunctionType *fty = cfn->getFunctionType();
                                    FunctionCallee hook = mod->getOrInsertFunction(FnName, fty); 
                                    vector <Value*> arglist(cb->arg_begin(), cb->arg_end());
                                    CallInst *NewCI = B.CreateCall(hook, arglist);                         
                                    NewCI->setDoesNotThrow();

                                    if (!cb->use_empty())
                                        cb->replaceAllUsesWith(NewCI);
                                    // ReplaceInstWithInst(cb, NewCI);
                                    dbg(errs() << "added " << *NewCI << " from " << FN->getName() << "\n";)
                                    redundantChecks.push_back(cb);
                                    pmemPtrs.insert(NewCI);
                                }
                            }
                            else 
                            {
                                dbg(errs() << ">>Remaining callbase : " << *cb << " Uses: " \
                                            << cb->getNumUses() << " argval: " << *ArgVal << "\n";)
                            }
                        }
                    }
                }
            }
            else if (auto cb = dyn_cast<InvokeInst>(ins))
            {
                Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
                if (cfn)
                {
                    if (cfn->getName().contains("__spp_checkbound") ||
                        cfn->getName().contains("__spp_updatetag") || 
                        cfn->getName().contains("__spp_cleantag"))
                    {
                        // errs() << ">>InvokeInst: "<<*cb<<"\n";
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
                            if ( globalPtrs.find(ArgVal->stripPointerCasts()) != globalPtrs.end() ||
                                 untaggedPtrs.find(ArgVal->stripPointerCasts()) != untaggedPtrs.end() ||
                                 vtPtrs.find(ArgVal->stripPointerCasts()) != vtPtrs.end() )
                            {   
                                //replace uses of the returned value with ArgVal
                                //and remove the function call
                                dbg(errs() << ">>InvokeInst ext or vol ptr -- should skip : " << *cb << " Uses: " \
                                            << cb->getNumUses() << " argval: " << *ArgVal << "\n";)
                                // cb->replaceAllUsesWith(ArgVal);

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
                                            untaggedPtrs.insert(iUser);
                                        default:
                                            break;
                                    }                      
                                }

                                // redundantChecks.push_back(cb);
                                break;
                            }
                            else 
                            {
                                dbg(errs() << ">>Remaining InvokeInst : " << *cb << " Uses: " \
                                            << cb->getNumUses() << " argval: " << *ArgVal << "\n";)
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
    dbg(errs() << ">>" << __func__ << " : " << M.getModuleIdentifier() << "\n";)
    
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
        dbg(errs() << "!>ALERT: No main found in module\n";)
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

    //initial ptr tracking based on PTR derivation functions
    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    {
        trackFnArgs(&*Fn);
        trackPtrs(&*Fn);
    }

    //function arguments PTR type tracking
    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    {
        if (Fn->isDeclaration()) 
        {
            dbg(errs() << ">>declaration: skipping..\n";)
            continue;
        }
        propagateFnArgsTypes(&*Fn);
    }
    assessPtrArgs(&M);

    dbg(errs() << M << "\n";)

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    {
        dbg(errs() << ">>FName: " << Fn->getName() << "\n";)

        std::string FName = demangleName(Fn->getName());
        dbg(errs() << ">>Func : " << Fn->getName() << "\n";)
        dbg(errs() << ">>Func Name demangled : " << FName << "\n";)
        if (StringRef(FName).startswith("pmem::obj::persistent_ptr") &&
            StringRef(FName).contains("spp_get()"))
        {
            dbg(errs() << ">>Func Name demangled : " << FName << "\n";)
        }

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

    // errs() << M << "\n";

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    { 
        redundantCB(&*Fn);
    }

    if (!hasZeroRedundantChecks()) {
        eraseRedundantChecks();
    }
    
    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    { 
        redundantTagUpdates(&*Fn);
    }

    if (!hasZeroRedundantChecks()){
        eraseRedundantChecks();
    }

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    { 
        duplicateCleanTags(&*Fn);
    }

    if (!hasZeroRedundantChecks()){
        eraseRedundantChecks();
    }

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    { 
        duplicateUpdateTags(&*Fn);
    }

    if (!hasZeroRedundantChecks()){
        eraseRedundantChecks();
    }

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    { 
        mergeTagUpdates(&*Fn);
    }

    if (!hasZeroRedundantChecks()){
        eraseRedundantChecks();
    }

    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    { 
        duplicateCheckBounds(&*Fn);
    }

    if (!hasZeroRedundantChecks()){
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

    dbg(errs() << M << "\n";)
    
    memCleanUp();

    errs() << ">>Leaving SPPLTO\n";

    return true;
}

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
  virtual bool duplicateTagUpdates(Function *F);
  virtual bool duplicateCleanTags(Function *F);
  virtual bool duplicateUpdateTags(Function *F);
  virtual bool duplicateCheckBounds(Function *F);
  virtual bool mergeTagUpdates(Function *F);
  virtual bool mergeTagUpdatesCheckbounds(Function *F);
  virtual bool mergeTagUpdatesMemChecks(Function *F);
  virtual bool redundantTagUpdates(Function *F);  

  virtual bool trackPtrs (Function * F);
  virtual void trackFnArgs(Function* F);
  virtual void propagateFnArgsTypes(Function* F);
  virtual void assessPtrArgs(Module* M);

  virtual bool runOnFunction (Function * F, Module &M);
  virtual bool runOnModule(Module &M) override;

  virtual bool doCallBase (CallBase * ins);

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    //AU.addRequired<DominatorTreeWrapperPass>();
    //AU.addRequired<AAResultsWrapperPass>();
    //AU.addRequired<CallGraphWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
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

  ScalarEvolution* SE = nullptr;
  void setScalarEvolution(ScalarEvolution *SE) 
  {
    this->SE = SE;
  }
  
  const DataLayout *DL = nullptr;
  void setDL(const DataLayout *DL) 
  {
    this->DL = DL;
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

int isFirstLTO = 1;

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

    // Skip tag cleaning for certain snapshotting functions, thread functions and pmemobj_oid function
    if (CB->getCalledFunction() != NULL &&
        (CB->getCalledFunction()->getName().contains("pmemobj_tx_add_range_direct") || 
         CB->getCalledFunction()->getName().contains("pmemobj_tx_xadd_range_direct") || 
         CB->getCalledFunction()->getName().contains("pmemobj_oid") ||
         CB->getCalledFunction()->getName().equals("pthread_create") ||
         CB->getCalledFunction()->getName().equals("pthread_cond_signal")))
    {
        return changed;
    }

    // if it's not a call to any of the below functions
    // the ptr is untagged
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
        if (isMemFuncName(fname) || isPMemFuncName(fname) ||
            isStringFuncName(fname)) 
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
            std::vector<User*> Users(ArgVal->user_begin(), ArgVal->user_end());
            for (auto User : Users) 
            {
                Instruction *iUser= dyn_cast<Instruction>(User);
                // mark directly derived values as PM ptrs:
                switch (iUser->getOpcode()) 
                {
                    case Instruction::BitCast:
                    case Instruction::GetElementPtr:
                        dbg(errs() << ">>PM argument ptr use: " << *iUser << "\n";)
                        pmemPtrs.insert(iUser);
                    default:
                        break;
                }                      
            }
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
    
    // Arguments of main are volatile ptrs 
    // all the byval or sret arguments are untagged
    for (auto Arg = F->arg_begin(); Arg != F->arg_end(); ++Arg) 
    {
        if (Arg->getType()->isPointerTy() && 
            (F->getName().equals("main") ||
            (Arg->hasAttribute(Attribute::ByVal) || Arg->hasAttribute(Attribute::StructRet))))
        {
            dbg(errs()<<">> Already Cleaned Argument ByVal/SRET/main " << *Arg <<  "\n";)
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
                        dbg(errs() << ">> ByVal/SRET/main Arg ptr use: " << *iUser << "\n";)
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
                // Arguments of pthread calls are volatile ptrs 
                else if (CalleeF->getName().equals("pthread_create") || //pthread_create variables
                         CalleeF->getName().equals("pthread_cond_signal")) //pthread_cond variables
                {
                    for (auto Op = Ins->op_begin(); Op != Ins->op_end(); ++Op) 
                    {
                        Value *ArgVal = dyn_cast<Value>(Op);
                        if (!ArgVal->getType()->isPointerTy())
                            continue;
                        
                        Value *Operand = ArgVal->stripPointerCasts();

                        dbg(errs()<<"call to pthread function with ptr: " << *Ins << " Op : " << *Operand << "\n";)
                        
                        // This check exists for the case of a mid-pipeline optimization pass
                        // where free func can get null argument before being eliminated
                        if (!isa<ConstantPointerNull>(Operand))
                        {
                            untaggedPtrs.insert(Operand);

                            std::vector<User*> Users(Operand->user_begin(), Operand->user_end());
                            for (auto User : Users) 
                            {
                                Instruction *iUser= dyn_cast<Instruction>(User);
                                dbg(errs() << ">>pthread fn arg ptr use: " << *iUser << "\n";)

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
                }
                //- already cleaned ptr -//
                else if (CalleeF->getName().contains("__spp_cleantag") ||
                    CalleeF->getName().contains("__spp_memintr_check_and_clean") ||
                    CalleeF->getName().contains("__spp_checkbound") || 
                    CalleeF->getName().contains("__spp_update_check_clean")) 
                {
                    untaggedPtrs.insert(Ins);

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
                // pmemobj_oid, pmemobj_pool_by_ptr, pmemobj_tx_xadd_range_direct, pmemobj_tx_add_range_direct
                // and __spp_update_check_clean_direct
                // only take PM ptrs as arguments
                else if ( CalleeF->getName().equals("pmemobj_pool_by_ptr") ||
                        CalleeF->getName().equals("pmemobj_oid") ||
                        CalleeF->getName().equals("pmemobj_tx_xadd_range_direct") ||
                        CalleeF->getName().equals("pmemobj_tx_add_range_direct") ||
                        CalleeF->getName().contains("__spp_update_check_clean_direct"))
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
                // libpmem pm management functions have their dest argument as a PM ptr
                else if (CalleeF->getName().equals("pmem_memmove_persist") ||
                        CalleeF->getName().equals("pmem_memcpy_persist") ||
                        CalleeF->getName().equals("pmem_memmove_nodrain") ||
                        CalleeF->getName().equals("pmem_memmove") ||
                        CalleeF->getName().equals("pmem_memcpy") ||
                        CalleeF->getName().equals("pmem_memset_nodrain") ||
                        CalleeF->getName().equals("pmem_memset") ||
                        CalleeF->getName().equals("pmem_memset_persist"))
                {
                    Value* PMptr = Ins->getOperand(0);
                    dbg(errs() << ">> SPP pass PM ptr from PMDK funcs: " << *PMptr << " from " << *Ins << "\n";)
                    std::vector <Value*> trackOrigins;
                    trackOrigins.push_back(PMptr);

                    while (!trackOrigins.empty())
                    {                                
                        Value* curr = trackOrigins.front();
                        if (Instruction *iUser = dyn_cast<Instruction>(curr))
                        {
                            switch (iUser->getOpcode()) 
                            {
                                case Instruction::BitCast:
                                case Instruction::GetElementPtr:
                                    dbg(errs() << ">> SPP pass PM ptr from PMDK funcs:" << *iUser->getOperand(0) << "\n";)
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
                // libpmemobj pm management functions have their dest argument as a PM ptr
                else if (CalleeF->getName().equals("pmemobj_memcpy") ||
                        CalleeF->getName().equals("pmemobj_memcpy_persist") ||
                        CalleeF->getName().equals("pmemobj_memmove") ||
                        CalleeF->getName().equals("pmemobj_memset") ||
                        CalleeF->getName().equals("pmemobj_memset_persist"))
                {
                    Value* PMptr = Ins->getOperand(1);
                    dbg(errs() << ">> SPP pass PM ptr from PMDK funcs: " << *PMptr << " from " << *Ins << "\n";)
                    std::vector <Value*> trackOrigins;
                    trackOrigins.push_back(PMptr);

                    while (!trackOrigins.empty())
                    {                                
                        Value* curr = trackOrigins.front();
                        if (Instruction *iUser = dyn_cast<Instruction>(curr))
                        {
                            switch (iUser->getOpcode()) 
                            {
                                case Instruction::BitCast:
                                case Instruction::GetElementPtr:
                                    dbg(errs() << ">> SPP pass PM ptr from PMDK funcs:" << *iUser->getOperand(0) << "\n";)
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

/*
 * Remove duplicate checkbound calls
 */
bool
SPPLTO::duplicateCheckBounds(Function *FN)
{
    bool changed = false;
    DenseMap<Value*, DenseMap<Value*, Value*>> checkedVals;
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
                        Value* DerefOff = cb->getOperand(1)->stripPointerCasts();

                        if (checkedVals.find(ArgVal) == checkedVals.end()) 
                        {
                            checkedVals[ArgVal][DerefOff] = cb;
                            dbg(errs() << *cb << " op : " << *ArgVal << " deref : " << DerefOff << "\n";)  
                        }
                        else 
                        {
                            if (checkedVals[ArgVal].find(DerefOff) != checkedVals[ArgVal].end())
                            {
                                DominatorTree DT = DominatorTree(*FN);
                                if (!DT.dominates(checkedVals[ArgVal][DerefOff], cb))
                                {
                                    dbg(errs() << "Non-dominated checkbound usage" << *cb << "\n";)
                                }
                                else
                                {
                                    dbg(errs() << *cb << " duplicate checkbound : " << *ArgVal << "\n";)
                                    dbg(errs() << "should be replaced with: " << *checkedVals[ArgVal][DerefOff] << "\n";)
                                    cb->replaceAllUsesWith(checkedVals[ArgVal][DerefOff]);
                                    redundantChecks.push_back(cb);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

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
                    // Check for redundant updatetag calls that are directly cleaned
                    if (cfn->getName().contains("__spp_update_check_clean"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        Value* Off = cb->getOperand(1)->stripPointerCasts();
                        
                        if (updatedVals.find(ArgVal) == updatedVals.end()) 
                        {
                            updatedVals[ArgVal][Off] = cb;
                        }
                        else 
                        {
                            if (updatedVals[ArgVal].find(Off) != updatedVals[ArgVal].end())
                            {
                                DominatorTree DT = DominatorTree(*FN);
                                if (!DT.dominates(updatedVals[ArgVal][Off], cb))
                                {
                                    dbg(errs() << "Non-dominated __spp_update_check_clean usage" << *cb << "\n";)
                                }
                                else
                                {
                                    dbg(errs() << FN->getName() << " :there is a duplicate __spp_update_check_clean " << \
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
    checkedVals.clear();
    return changed;
}

/*
 * Merge consecutive tag updates into a single one
 */
bool
SPPLTO::mergeTagUpdates(Function *FN)
{
    bool changed = false;
    dbg(errs() << FN->getName() << "\n";)
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
                                                        dbg(errs() << "results CI: " << *updateCI << " changed gep: " << *gep <<"\n";)
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
                                                dbg(errs() << "results CI: " << *updateCI << "\n";)
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        else if (ArgVal)
                        {
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
                                                    dbg(errs() << "merge via createAdd " << *cb << " with " << *updateCI << " using " << *gep << "\n";)
                                                    //set the insert point before the updated instruction
                                                    IRBuilder<> B(BB->getContext());
                                                    B.SetInsertPoint(updateCI);
                                                    
                                                    //get the offset values and create their addition
                                                    Value* firstOff = cb->getOperand(1);
                                                    Value* secondOff = updateCI->getOperand(1);
                                                    Value* newOff = B.CreateAdd(firstOff, secondOff);
                                                    // change the GEP operand to the argument of the initial updatetag call
                                                    gep->setOperand(0, ArgVal);
                                                    // update the offset of the next updatetag with the offset of the first one
                                                    updateCI->setOperand(1, newOff);
                                                    // remove the initial updatetag call
                                                    redundantChecks.push_back(cb);
                                                    dbg(errs() << "results CI: " << *updateCI << " changed gep: " << *gep << " added: " << *newOff <<"\n";)
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
                                            dbg(errs() << "direct merge via createAdd " << *cb << " with " << *updateCI << "\n";)
                                            //set the insert point before the updated instruction
                                            IRBuilder<> B(BB->getContext());
                                            B.SetInsertPoint(updateCI);

                                            //get the offset values and create their addition
                                            Value* firstOff = cb->getOperand(1);
                                            Value* secondOff = updateCI->getOperand(1);
                                            Value* newOff = B.CreateAdd(firstOff, secondOff);
                                            // update the ptr of the next updatetag with the ptr of the first one
                                            updateCI->setOperand(0, ArgVal);
                                            // update the offset of the next updatetag with the offset of the first one
                                            updateCI->setOperand(1, newOff);
                                            // remove the initial updatetag call
                                            redundantChecks.push_back(cb);
                                            dbg(errs() << "results CI: " << *updateCI << " added: " << *newOff <<"\n";)
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

/*
 * Remove duplicate tag updates
 */
bool
SPPLTO::duplicateTagUpdates(Function *FN)
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
                        
                        // duplicate tag updates
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

/*
 * Remove redundant tag updates, e.g., when directly cleaned
 */
bool
SPPLTO::redundantTagUpdates(Function *FN)
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
                    // Check for redundant updatetag calls that have been performed already
                    if (cfn->getName().contains("__spp_cleantag"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        if (auto ArgInst = dyn_cast<CallInst>(ArgVal))
                        {
                            if (auto ArgFnCall = dyn_cast<Function>(ArgInst->getCalledOperand()->stripPointerCasts()))
                            {
                                if (ArgFnCall->getName().contains("__spp_updatetag"))
                                {
                                    if (ArgVal->hasOneUser())
                                    {
                                        dbg(errs() << "redundant updatetag :" << *ArgVal << "\n";)
                                        dbg(errs() << "cleantag callback :" << *cb << "\n";)
                                        dbg(errs() << "replace operand with " << *ArgInst->getOperand(0) << "\n";)
                                        cb->setOperand(0, ArgInst->getOperand(0));
                                        dbg(errs() << "updated cleantag callback :" << *cb << "\n";)
                                        ArgInst->replaceAllUsesWith(ArgInst->getOperand(0));
                                        redundantChecks.push_back(ArgInst);
                                        changed = true;
                                    }
                                    else 
                                    {
                                        dbg(errs() << "\nCheck" << *ArgVal << "\n";)
                                        dbg(errs() << *BB;)
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

/*
 * Merge some occasions of tag update and immediate checkbound
 */
bool
SPPLTO::mergeTagUpdatesCheckbounds(Function *FN)
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
                    if (cfn->getName().contains("__spp_checkbound"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        Value* DerefOff = cb->getOperand(1)->stripPointerCasts();
                        
                        if (auto ArgInst = dyn_cast<CallInst>(ArgVal))
                        {
                            if (auto ArgFnCall = dyn_cast<Function>(ArgInst->getCalledOperand()->stripPointerCasts()))
                            {
                                if (ArgFnCall->getName().contains("__spp_updatetag"))
                                {
                                    if (ArgVal->hasOneUser())
                                    {
                                        // Merge updatetag + checkbound in a function call
                                        dbg(errs() << "to be merged updatetag :" << *ArgVal << "\n";)

                                        IRBuilder<> B(cb);
                                        Module *mod = cb->getModule();
                                        StringRef FnName = "__spp_update_check_clean";
                                        if (ArgFnCall->getName().endswith("_direct"))
                                            FnName = "__spp_update_check_clean_direct";
                                        
                                        // create a call with the same type of update tag
                                        FunctionType *fty = ArgFnCall->getFunctionType();
                                        FunctionCallee hook = mod->getOrInsertFunction(FnName, fty); 

                                        // get the ptr operand of update tag call
                                        Value* Ptr = ArgInst->getArgOperand(0); 
                                        Value *TotalOff;
                                        // get the offset of update tag call
                                        if (auto *CI = dyn_cast<ConstantInt>(ArgInst->getArgOperand(1)->stripPointerCasts()))
                                        {
                                            // if update has a constant offset simply add the integers
                                            int64_t UpdOff = CI->getSExtValue(); 
                                            // get the dereference size
                                            int64_t CheckOff = (cast<ConstantInt>(DerefOff))->getSExtValue(); 
                                            // accummulate the offset and the dereferenced type size
                                            int64_t NewOff = UpdOff + CheckOff; 

                                            TotalOff = ConstantInt::get(Type::getInt64Ty(mod->getContext()), NewOff);
                                            dbg(errs()<<"updated off " << NewOff << " " << UpdOff << "+" << CheckOff <<"\n";)
                                        }
                                        else
                                        {
                                            // if update tag has a variable offset create an ADD
                                            Value* UpdOff = ArgInst->getArgOperand(1)->stripPointerCasts();
                                            // get the dereference size
                                            Value* CheckOff = DerefOff;
                                            // accummulate the offset and the dereferenced type size
                                            Value* NewOff = B.CreateAdd(UpdOff, CheckOff);
                                            
                                            TotalOff = NewOff;

                                            dbg(errs()<<"updated off " << *NewOff << " " << *UpdOff << "+" << *CheckOff <<"\n";)
                                        }
                                        
                                        vector <Value*> arglist;
                                        arglist.push_back(Ptr);
                                        arglist.push_back(TotalOff);

                                        CallInst *NewCI = B.CreateCall(hook, arglist, "spp_upd_cb.");                         
                                        NewCI->setDoesNotThrow();

                                        // replace the use of the updated tag with the initial ptr
                                        ArgInst->replaceAllUsesWith(ArgInst->getArgOperand(0));
                                        // replace the uses of the checked and cleaned value
                                        if (!cb->use_empty())
                                            cb->replaceAllUsesWith(NewCI);
                                        
                                        // remove both the update tag and the checkbound call
                                        redundantChecks.push_back(ArgInst);
                                        redundantChecks.push_back(cb);
                                        untaggedPtrs.insert(NewCI);
                                        changed = true;
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
SPPLTO::mergeTagUpdatesMemChecks(Function *FN)
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
                    // Check for redundant updatetag calls that have been performed already
                    if (cfn->getName().contains("__spp_memintr_check_and_clean"))
                    {
                        Value* ArgVal = cb->getOperand(0)->stripPointerCasts();
                        Value* MemIntrOff = cb->getOperand(1)->stripPointerCasts();

                        if (auto ArgInst = dyn_cast<CallInst>(ArgVal))
                        {
                            if (auto ArgFnCall = dyn_cast<Function>(ArgInst->getCalledOperand()->stripPointerCasts()))
                            {
                                if (ArgFnCall->getName().contains("__spp_updatetag"))
                                {
                                    if (ArgVal->hasOneUser())
                                    {
                                        // Merge updatetag + checkbound in a function call
                                        IRBuilder<> B(cb);
                                        Module *mod = cb->getModule();
                                        StringRef FnName = "__spp_update_check_clean";
                                        if (ArgFnCall->getName().endswith("_direct"))
                                            FnName = "__spp_update_check_clean_direct";
                                        
                                        Value* UpdateTagOff = ArgInst->getOperand(1)->stripPointerCasts();
                                        // for correct calculation:
                                        // we have to pass updatetag_off + (memintr_off - 1)
                                        Value *TotalOff = nullptr;
                                        if ( isa<Constant>(MemIntrOff) && 
                                             isa<Constant>(UpdateTagOff) )
                                        {
                                            dbg(errs() << "In Function: " << FN->getName() << "\n";)
                                            dbg(errs() << "to be merged updatetag with const offs:" << *ArgVal << "\n";)
                                            int64_t FirstOff = (cast<ConstantInt>(MemIntrOff))->getSExtValue();
                                            int64_t SecondOff = (cast<ConstantInt>(UpdateTagOff))->getSExtValue();
                                            int64_t NewOff = FirstOff + SecondOff - 1;
                                            TotalOff = ConstantInt::get(Type::getInt64Ty(mod->getContext()), NewOff);
                                        }
                                        else
                                        {
                                            dbg(errs() << "In Function: " << FN->getName() << "\n";)
                                            dbg(errs() << "to be merged updatetag with created Add:" << *ArgVal << "\n";)
                                            Value *NewOff = B.CreateAdd(MemIntrOff, UpdateTagOff);
                                            Value *One = ConstantInt::get(Type::getInt64Ty(mod->getContext()), 1);
                                            TotalOff = B.CreateSub(NewOff, One);
                                        }
                                        
                                        // create a call with the same type of update tag
                                        FunctionType *fty = ArgFnCall->getFunctionType();
                                        FunctionCallee hook = mod->getOrInsertFunction(FnName, fty); 
                                        vector <Value*> arglist;
                                        arglist.push_back(ArgInst->getOperand(0));
                                        arglist.push_back(TotalOff);
                                        CallInst *NewCI = B.CreateCall(hook, arglist, "spp_upd_memintr.");                         
                                        NewCI->setDoesNotThrow();

                                        // replace the use of the updated tag
                                        ArgInst->replaceAllUsesWith(ArgInst->getOperand(0));
                                        // replace the uses of the checked and cleaned value
                                        if (!cb->use_empty())
                                            cb->replaceAllUsesWith(NewCI);
                                        
                                        // remove both the update tag and the checkbound call
                                        redundantChecks.push_back(ArgInst);
                                        redundantChecks.push_back(cb);
                                        untaggedPtrs.insert(NewCI);
                                        changed = true;
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
                        cfn->getName().contains("__spp_memintr_check_and_clean") ||
                        cfn->getName().contains("__spp_update_check_clean"))
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
                                    else if (cfn->getName().equals("__spp_update_check_clean"))
                                        FnName = "__spp_update_check_clean_direct";
                                    
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
                                    
                                    if (FnName.equals("__spp_updatetag_direct"))
                                        pmemPtrs.insert(NewCI);
                                    else
                                        untaggedPtrs.insert(NewCI);
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

static void insertPrint(BasicBlock *BB, Instruction *I, StringRef S) {
  Module *M = BB->getModule();
  LLVMContext &Ctx = M->getContext();
  auto *CharPointerTy = PointerType::get(IntegerType::getInt8Ty(Ctx), 0);
  auto *PrintfTy =
      FunctionType::get(IntegerType::getVoidTy(Ctx), {CharPointerTy}, true);
  auto Printf = M->getOrInsertFunction("__spp_update_checkcnt", PrintfTy);
  auto Arr = ConstantDataArray::getString(Ctx, S);
  GlobalVariable *GV = new GlobalVariable(
      *M, Arr->getType(), true, GlobalValue::PrivateLinkage, Arr, ".str");
  GV->setAlignment(MaybeAlign(1));
  CallInst::Create(Printf, {ConstantExpr::getBitCast(GV, CharPointerTy)}, "",
                   I);
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
    
    setDL(&M.getDataLayout()); //init the data layout
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
        if (isPMemFuncName(Fn->getName())) 
        {
            dbg(errs() << ">>Persistent Memory func: skipping..\n";)
            continue;
        }

        runOnFunction(&*Fn, M);
    }

    // errs() << M << "\n";
    
    int postProcessedInst;
    do {
        postProcessedInst = 0;
        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            redundantCB(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();
        
        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            duplicateTagUpdates(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();


        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            duplicateCleanTags(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();
        

        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            duplicateUpdateTags(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();
        

        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            mergeTagUpdates(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();
        
        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            redundantTagUpdates(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();

        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            duplicateCheckBounds(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();

        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            mergeTagUpdatesCheckbounds(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();

        for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
        { 
            mergeTagUpdatesMemChecks(&*Fn);
        }
        postProcessedInst += redundantChecks.size();
        eraseRedundantChecks();

        dbg(errs() << "post processed inst: " << postProcessedInst << "\n";)
    } while(postProcessedInst!=0);

    // if (!isFirstLTO)
    // {
    //     for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    //     { 
    //         int cnt = 0;
    //         for (auto BB = Fn->begin(); BB != Fn->end(); ++BB) 
    //         {
    //             for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
    //             {
    //                 if (auto cb = dyn_cast<CallBase>(ins)) 
    //                 {
    //                     Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());
    //                     if (cfn) 
    //                     {
    //                         StringRef fname = cfn->getName();
    //                         if (fname.contains("__spp_checkbound") ||
    //                             fname.contains("__spp_update_check"))
    //                             cnt++;
    //                     }
    //                 }
    //             }
    //         }
    //         errs() << Fn->getName() << " checkbounds : " << cnt << "\n";
    //     }
    // }

    // if (!isFirstLTO)
    // {
    //     int check_idx=1;
    //     for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    //     { 
    //         for (auto BB = Fn->begin(); BB != Fn->end(); ++BB) 
    //         {
    //             BasicBlock *BaB = &*BB;
    //             for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
    //             {
    //                 if (auto cb = dyn_cast<CallBase>(ins)) 
    //                 {
    //                     Function* CalleeF = cb->getCalledFunction();
    //                     if (CalleeF) 
    //                     {
    //                         StringRef fname = CalleeF->getName();
    //                         if (fname.contains("__spp_checkbound"))
    //                         {
    //                             // StringRef S = StringRef((Fn->getName()+"_"+Twine(check_idx)).str());
    //                             StringRef S = StringRef(std::to_string(check_idx));
    //                             insertPrint(BaB, cb, S);
    //                             check_idx++;
    //                         }
    //                         else if (fname.contains("__spp_update_check_clean"))
    //                         {
    //                             // StringRef S = StringRef((Fn->getName()+"_"+Twine(check_idx)).str());
    //                             StringRef S = StringRef(std::to_string(check_idx));
    //                             insertPrint(BaB, cb, S);
    //                             check_idx++;
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }
    
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

    // if (!isFirstLTO)
    //     errs() << M << "\n";

    memCleanUp();

    errs() << ">>Leaving SPPLTO\n";
    isFirstLTO=0;
    return true;
}

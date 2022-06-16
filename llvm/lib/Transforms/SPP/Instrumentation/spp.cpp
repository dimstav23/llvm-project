//===----- spp.cpp - Bounds Checker in SPP transformation pass -----===//
// #define DEBUG_TYPE "spp"

#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Casting.h>
#include <llvm/IR/Dominators.h>
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/SmallSet.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Metadata.h>
#include <llvm/Analysis/MemoryBuiltins.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/LoopAccessAnalysis.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/LoopIterator.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Transforms/Utils/Local.h>
#include "llvm/Transforms/SPP/SPPUtils.h"

#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <tr1/memory>
#include <tr1/tuple>
#include <assert.h>

//#define SPP_PRINT_DEBUG // Uncomment for debugging
#ifdef SPP_PRINT_DEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

using namespace llvm;
// using namespace std; // Jin: this is NOT recommended..

namespace {
    
    static int getOpIdx(Instruction* I, Value* Ptr) 
    {
        for (auto Op = I->op_begin(), OpEnd = I->op_end(); Op != OpEnd; ++Op)
        {
            if (Op->get() == Ptr)
                return Op->getOperandNo();
        }
        return -1;
    }

    class SPPPass {

        Module* M = nullptr;
        TargetLibraryInfoWrapperPass* TLIWP = nullptr;
        ScalarEvolution* SE = nullptr;

        const DataLayout *DL;

        SmallSet<Function*, 32> varargFuncs;
        DenseMap<Constant*, Constant*> globalUses;
        DenseMap<Instruction*, Instruction*> optimizedMemInsts;
        //TODO: Debuglist.

        enum operandType {
            VOL,
            PM,
            CONST,
            UKNOWN
        };

    public:
        std::unordered_set <Value*> globalPtrs;
        std::unordered_set <Value*> untaggedPtrs;
        std::unordered_set <Value*> pmemPtrs;
        std::unordered_set <Value*> extPtrs;

        std::unordered_set <Value*> vtPtrs;
        std::unordered_set <Value*> cxaPtrs;
        std::unordered_set <Value*> checkedPtrs;

        std::vector<Instruction*> GEP_hooked_CBs;
        std::vector<Instruction*> GEP_skipped_CBs;
    
        SPPPass(Module* M) 
        {
            this->M = M;
        }

        void setScalarEvolution(ScalarEvolution *SE) 
        {
            this->SE = SE;
        }

        void setDL(const DataLayout *DL) 
        {
            this->DL = DL;
        }

        void setTLIWP(TargetLibraryInfoWrapperPass *TLIWP) 
        {
            this->TLIWP = TLIWP;
        }

        TargetLibraryInfo *getTLI(const Function & F)
        {
            return &this->TLIWP->getTLI(F);
        }
        
        void memCleanUp()
        {
            this->globalPtrs.clear();
            this->untaggedPtrs.clear();
            this->pmemPtrs.clear();
            this->extPtrs.clear();
            this->vtPtrs.clear();
            this->cxaPtrs.clear();
            this->checkedPtrs.clear();
        }
        
        void setSPPprefix(Value *V) {
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

        void visitGlobals() 
        {
            SmallVector<GlobalVariable*, 16> globals;
            for (auto G = M->global_begin(), Gend = M->global_end(); G != Gend; ++G) 
            {
                globals.push_back(&*G);
            }
        }

        bool isVtableGep(GetElementPtrInst *Gep) {

            Value *SrcPtr = Gep->getPointerOperand();

            if (SrcPtr->hasName() && SrcPtr->getName().startswith("vtable")) 
            {
                dbg(errs() << ">>Ignoring GV vtable GEP: " << *Gep << "\n";)
                return true;
            }

            if (Gep->getNumIndices() == 1) {
                Value *FirstOp = Gep->getOperand(1);
                if (FirstOp->hasName() &&
                    FirstOp->getName().startswith("vbase.offset")) 
                {
                    dbg(errs() << ">>Ignoring vbase GEP: " << *Gep << "\n";)
                    return true;
                }
            }

            if (GlobalVariable *GV = dyn_cast<GlobalVariable>(SrcPtr))
            {
                if (GV->getName().startswith("_ZTV")) 
                {
                    dbg(errs() << ">>Ignoring GV vtable GEP: " << *Gep << "\n";)
                    return true;
                }
            }
            return false;
        }

        bool isVolatileGep(GetElementPtrInst *Gep)
        {
            if ( untaggedPtrs.find(Gep) != untaggedPtrs.end() ||
                globalPtrs.find(Gep) != globalPtrs.end() ||
                vtPtrs.find(Gep) != vtPtrs.end() )
            {
                dbg(errs() << ">>" << __func__ << " global or volatile GEP skipped: " << *Gep << "\n";)
                return true;
            }
            return false;
        }

        bool isTagUpdated(GetElementPtrInst *Gep)
        {
            for (auto user = Gep->user_begin(); user != Gep->user_end(); ++user) 
            {
                CallBase *GepCBUser = dyn_cast<CallBase>(user->stripPointerCasts());
                if (!GepCBUser) 
                { 
                    continue; 
                }

                Function *FN = GepCBUser->getCalledFunction();
                if (!FN) 
                {  
                    continue;
                }

                if (FN->getName().startswith("__spp_update")) 
                {
                    return true;
                }
                
                dbg(errs() << "!>ALERT: missed function callBase!\n";)
            }
            
            return false;
        }

        bool isDefinedLater(Instruction *Op, Instruction *userI)
        {
            Function *F = userI->getFunction();
            bool found = false;

            for (auto & Iter : instructions(F)) 
            {                
                if (&Iter == userI) 
                {
                    //has to be found first
                    found= true;
                }
                else if (&Iter == Op) 
                {
                    //has to be found afterwards
                    dbg(errs() << "Function : " << *F << " op : " << *Op << " userI : " << *userI << "\n";)
                    assert(found);
                    return true;
                }
            }
            assert(found);
            return found;
        }
        
        bool isMissedGep(GetElementPtrInst *gep, Instruction *userI)
        {
            if (isVtableGep(gep))
            {
                return false;
            }

            if (isVolatileGep(gep))
            {
                return false;
            }

            if (isTagUpdated(gep)) 
            {
                return false;
            }
            
            if (gep->hasAllZeroIndices()) 
            {
               return false;
            }
           
            if (isDefinedLater(gep, userI)) 
            {
                return false;
            }

            return true;
        }

        bool instrGepOperand(Instruction *userI, GetElementPtrInst *gep) 
        {            
            IRBuilder<> B(gep);
            
            SmallVector <Type*, 2> tlist;
            
            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            Type *Arg2Ty = Type::getInt64Ty(M->getContext());
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
            
            FunctionType *hookfty = FunctionType::get(RetArgTy, tlist, false);
            FunctionCallee hook = M->getOrInsertFunction("__spp_update_pointer", hookfty);
            
            SmallVector <Value*, 2> arglist;
            Value *TmpPtr = B.CreateBitCast(gep, hook.getFunctionType()->getParamType(0));
            Value *GepOff = EmitGEPOffset(&B, *DL, gep);
            arglist.push_back(TmpPtr);
            arglist.push_back(GepOff);
            CallInst *Masked = B.CreateCall(hook, arglist);
            Masked->setDoesNotThrow();
            Value *NewPtr = B.CreatePointerCast(Masked, gep->getType());

            int OpIdx = getOpIdx(userI, gep);
            userI->setOperand(OpIdx, NewPtr);            
            return true;
        }
        
        bool replaceFoldedGepOp(Instruction *Ins)
        {
            bool changed= false;
            for (auto Op = Ins->op_begin(); Op != Ins->op_end(); ++Op) 
            {
                Instruction *MyOp= dyn_cast<Instruction>(Op);
                if (!MyOp) 
                {
                    dbg(errs() << ">>" << __func__ << "op: not inst\n";) 
                    continue;
                }
                dbg(errs() << ">>" << __func__ << " folded op: " << **Op << "\n";) 
                
                // only one-depth for now.. 
                if (!isa<GetElementPtrInst>(MyOp->stripPointerCasts())) 
                {
                    continue;
                }
                
                GetElementPtrInst *GepOp= cast<GetElementPtrInst>(MyOp->stripPointerCasts()); 

                if (isMissedGep(GepOp, Ins)) 
                {
                    dbg(errs() << "!>ALERT: missed GepOp: " << *GepOp << " in " << *Ins \
                                << " of " << Ins->getFunction()->getName() << "\n";)

                    if (GepOp == MyOp) 
                    {
                        changed = instrGepOperand(MyOp, GepOp);
                    }
                    else 
                    {
                        changed = instrGepOperand(Ins, GepOp);
                    }
                }
            }
            return changed;
        }
        
        
        /*
        * Get the insert point after the specified instruction. For non-terminators
        * this is the next instruction. For `invoke` intructions, create a new
        * fallthrough block that jumps to the default return target, and return the
        * jump instruction.
        */
        Instruction* getInsertPointAfter(Instruction *I) 
        {
            if (InvokeInst *Invoke = dyn_cast<InvokeInst>(I)) 
            {
                BasicBlock *Dst = Invoke->getNormalDest();
                BasicBlock *NewBlock = BasicBlock::Create(I->getContext(),
                        "invoke_insert_point", Dst->getParent(), Dst);
                BranchInst *Br = BranchInst::Create(Dst, NewBlock);
                Invoke->setNormalDest(NewBlock);

                /* Patch references in PN nodes in original successor */
                BasicBlock::iterator It(Dst->begin());
                while (PHINode *PN = dyn_cast<PHINode>(It)) 
                {
                    int i;
                    while ((i = PN->getBasicBlockIndex(Invoke->getParent())) >= 0)
                    {
                        PN->setIncomingBlock(i, NewBlock);
                    }
                    It++;
                }
                return Br;
            }
            if (isa<PHINode>(I))
            {
                return &*I->getParent()->getFirstInsertionPt();
            }
           
            assert(!Instruction::isTerminator(I->getOpcode()));
            return &*std::next(BasicBlock::iterator(I));
        }

        bool instrPtrToInt(Instruction *I)
        {
            IRBuilder<> B(I);

            Value* Ptr = cast<PtrToIntInst>(I)->getPointerOperand();
            assert(Ptr->getType()->isPointerTy()); 

            if ( untaggedPtrs.find(Ptr->stripPointerCasts()) != untaggedPtrs.end() ||
                 globalPtrs.find(Ptr->stripPointerCasts()) != globalPtrs.end() ||
                 vtPtrs.find(Ptr->stripPointerCasts()) != vtPtrs.end() )
            {
                dbg(errs() << ">>global or volatile ptr skipped cleantag: " << *I << "\n";)
                return false;
            }

            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            SmallVector <Type*, 1> tlist;
            tlist.push_back(RetArgTy);
            FunctionType *hookfty = FunctionType::get(RetArgTy, RetArgTy, false);
            FunctionCallee hook;
            if (pmemPtrs.find(Ptr->stripPointerCasts()) != pmemPtrs.end())
            {
                dbg(errs() << "__spp_cleantag_direct\n";)
                hook = M->getOrInsertFunction("__spp_cleantag_direct", hookfty);
            }
            else 
            {
                hook = M->getOrInsertFunction("__spp_cleantag", hookfty);
            }

            Value *TmpPtr = B.CreateBitCast(Ptr, hook.getFunctionType()->getParamType(0));
            CallInst *Masked = B.CreateCall(hook, TmpPtr);
            Masked->setDoesNotThrow();
            Value *NewPtr = B.CreatePointerCast(Masked, Ptr->getType());

            int OpIdx = getOpIdx(I, Ptr);
            I->setOperand(OpIdx, NewPtr);
            dbg(errs() << ">> updated PtrToInt: " << *Masked << " " << *I << "\n";)

            untaggedPtrs.insert(I);
            return true;
        }

        bool instrCallBase(CallBase *CB)
        {
            /*
             *  Check for byval arguments and clean their tag 
             */
            bool changed = false;
            dbg(errs() << ">>CallBase: "<< *CB << "\n";)
            
            if (CB->getCalledFunction() == NULL) 
            {
                return changed;
            }

            Module *mod = CB->getModule();
            Type *vpty = Type::getInt8PtrTy(mod->getContext());
            FunctionType *fty = FunctionType::get(vpty, vpty, false);
            FunctionCallee hook_generic = 
                mod->getOrInsertFunction("__spp_cleantag", fty);
            FunctionCallee hook_direct = 
                mod->getOrInsertFunction("__spp_cleantag_direct", fty);

            for (auto Arg = CB->arg_begin(); Arg != CB->arg_end(); ++Arg) 
            {   
                Value *ArgVal = dyn_cast<Value>(Arg);
                if (!ArgVal) 
                {
                    dbg(errs() << ">>Argument skipping.. Not a value\n";)
                    continue;
                }
                
                // Now we got a Value arg. 
                if (ArgVal->getType()->isPointerTy())
                {
                    if ( untaggedPtrs.find(ArgVal->stripPointerCasts()) != untaggedPtrs.end() ||
                        globalPtrs.find(ArgVal->stripPointerCasts()) != globalPtrs.end() ||
                        vtPtrs.find(ArgVal->stripPointerCasts()) != vtPtrs.end() )
                    {
                        dbg(errs() << ">>global, volatile or vtable ptr skipped cleaning: " << *CB << "\n";)
                        continue;
                    }
                }

                if (ArgVal->getType()->isPointerTy() && 
                    ( CB->paramHasAttr(Arg - CB->arg_begin(), Attribute::ByVal) ||
                      CB->paramHasAttr(Arg - CB->arg_begin(), Attribute::StructRet) ))
                {
                    dbg(errs()<<">>Argument ByVal or StructRet.. cleaning\n";)
                    IRBuilder<> B(CB);
                    std::vector <Value*> arglist;

                    FunctionCallee hook;
                    if ( pmemPtrs.find(ArgVal->stripPointerCasts()) != pmemPtrs.end() )
                    {
                        dbg(errs() << "__spp_cleantag_direct\n";)
                        hook = hook_direct;
                    }
                    else
                    {
                        dbg(errs() << "__spp_cleantag for " << *ArgVal << "\n";)
                        hook = hook_generic;
                    }                    
                    Value *TmpPtr = B.CreateBitCast(ArgVal, 
                                    hook.getFunctionType()->getParamType(0));
                    arglist.push_back(TmpPtr);
                    CallInst *Masked = B.CreateCall(hook, arglist);
                    Masked->setDoesNotThrow();                  
                    Value *Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 

                    CB->setArgOperand(Arg - CB->arg_begin(), Unmasked);

                    dbg(errs() << ">>new_CB after masking: " << *CB << "\n";)

                    changed = true;
                }                
            }

            return changed;
        }
        
        bool instrMemIntr(MemIntrinsic *mi)
        {
            bool changed = false;
            
            // create hook prototype
            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            Type *Arg2Ty = Type::getInt64Ty(M->getContext());
            SmallVector <Type*, 2> tlist;
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
             
            FunctionType *hookfty = FunctionType::get(RetArgTy, tlist, false);
            FunctionCallee hook_generic = M->getOrInsertFunction("__spp_memintr_check_and_clean", hookfty);
            FunctionCallee hook_direct = M->getOrInsertFunction("__spp_memintr_check_and_clean_direct", hookfty);

            if (MemCpyInst *MCI = dyn_cast<MemCpyInst>(mi))
            {
                Value *Dest = MCI->getRawDest();
                Value *Src = MCI->getRawSource();
                Value *Length = MCI->getLength();
                
                dbg(errs() << ">>MCI " << *Dest << " | " << *Src << " | " << *Length   << "\n";)

                IRBuilder<> B(MCI);
                std::vector <Value*> arglist;

                if ( untaggedPtrs.find(Dest->stripPointerCasts()) != untaggedPtrs.end() ||
                    globalPtrs.find(Dest->stripPointerCasts()) != globalPtrs.end() ||
                    vtPtrs.find(Dest->stripPointerCasts()) != vtPtrs.end() )
                {
                    dbg(errs() << ">>" << __func__ << " global or volatile ptr Dest skipped: " << *MCI << "\n";)
                }
                else
                {
                    FunctionCallee hook;
                    if ( pmemPtrs.find(Dest->stripPointerCasts()) != pmemPtrs.end() )
                    {
                        dbg(errs() << "__spp_memintr_check_and_clean_direct\n";)
                        hook = hook_direct;
                    }
                    else
                    {
                        hook = hook_generic;
                    }     
                    Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                    Value *DestPtr = B.CreateBitCast(Dest, hook.getFunctionType()->getParamType(0));
                    std::vector<Value*> dest_args;
                    dest_args.push_back(DestPtr);
                    dest_args.push_back(IntOff);
                    CallInst *DestChecked = B.CreateCall(hook, dest_args);
                    DestChecked->setDoesNotThrow(); 
                    Value *DestCleaned = B.CreatePointerCast(DestChecked, Dest->getType());
                    MCI->setDest(DestCleaned);

                    untaggedPtrs.insert(DestCleaned);
                    untaggedPtrs.insert(MCI);
                    changed = true;
                }

                if ( untaggedPtrs.find(Src->stripPointerCasts()) != untaggedPtrs.end() ||
                    globalPtrs.find(Src->stripPointerCasts()) != globalPtrs.end() ||
                    vtPtrs.find(Src->stripPointerCasts()) != vtPtrs.end() )
                {
                    dbg(errs() << ">>" << __func__ << " global or volatile ptr Src skipped: " << *MCI << "\n";)
                }
                else
                {
                    FunctionCallee hook;
                    if ( pmemPtrs.find(Src->stripPointerCasts()) != pmemPtrs.end() )
                    {
                        dbg(errs() << "__spp_memintr_check_and_clean_direct\n";)
                        hook = hook_direct;
                    }
                    else
                    {
                        hook = hook_generic;
                    }    
                    Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                    Value *SrcPtr = B.CreateBitCast(Src, hook.getFunctionType()->getParamType(0));
                    std::vector<Value*> src_args;
                    src_args.push_back(SrcPtr);
                    src_args.push_back(IntOff);
                    CallInst *SrcChecked = B.CreateCall(hook, src_args);   
                    SrcChecked->setDoesNotThrow();        
                    Value *SrcCleaned = B.CreatePointerCast(SrcChecked, Src->getType());
                    MCI->setSource(SrcCleaned);

                    untaggedPtrs.insert(SrcCleaned);
                    untaggedPtrs.insert(MCI);
                    changed = true;
                }
            }
            else if (MemMoveInst *MMI = dyn_cast<MemMoveInst>(mi))
            {
                Value *Dest = MMI->getRawDest();
                Value *Src = MMI->getRawSource();
                Value *Length = MMI->getLength();
                dbg(errs() << ">>MMI " << *Dest << " | " << *Src << " | " << *Length   << "\n";)

                IRBuilder<> B(MMI);
                std::vector <Value*> arglist;

                if ( untaggedPtrs.find(Dest->stripPointerCasts()) != untaggedPtrs.end() ||
                    globalPtrs.find(Dest->stripPointerCasts()) != globalPtrs.end() ||
                    vtPtrs.find(Dest->stripPointerCasts()) != vtPtrs.end() )
                {
                    dbg(errs() << ">>" << __func__ << " global or volatile ptr Dest skipped: " << *MMI << "\n";)
                }
                else
                {
                    FunctionCallee hook;
                    if ( pmemPtrs.find(Dest->stripPointerCasts()) != pmemPtrs.end() )
                    {
                        dbg(errs() << "__spp_memintr_check_and_clean_direct\n";)
                        hook = hook_direct;
                    }
                    else
                    {
                        hook = hook_generic;
                    }
                    Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                    Value *DestPtr = B.CreateBitCast(Dest, hook.getFunctionType()->getParamType(0));
                    std::vector<Value*> dest_args;
                    dest_args.push_back(DestPtr);
                    dest_args.push_back(IntOff);
                    CallInst *DestChecked = B.CreateCall(hook, dest_args); 
                    DestChecked->setDoesNotThrow(); 
                    Value *DestCleaned = B.CreatePointerCast(DestChecked, Dest->getType());
                    MMI->setDest(DestCleaned);

                    untaggedPtrs.insert(DestCleaned);
                    untaggedPtrs.insert(MMI);
                    changed = true;
                }

                if ( untaggedPtrs.find(Src->stripPointerCasts()) != untaggedPtrs.end() ||
                    globalPtrs.find(Src->stripPointerCasts()) != globalPtrs.end() ||
                    vtPtrs.find(Src->stripPointerCasts()) != vtPtrs.end() )
                {
                    dbg(errs() << ">>" << __func__ << " global or volatile ptr Src skipped: " << *MMI << "\n";)
                }
                else
                {
                    FunctionCallee hook;
                    if ( pmemPtrs.find(Src->stripPointerCasts()) != pmemPtrs.end() )
                    {
                        dbg(errs() << "__spp_memintr_check_and_clean_direct\n";)
                        hook = hook_direct;
                    }
                    else
                    {
                        hook = hook_generic;
                    }
                    Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                    Value *SrcPtr = B.CreateBitCast(Src, hook.getFunctionType()->getParamType(0));
                    std::vector<Value*> src_args;
                    src_args.push_back(SrcPtr);
                    src_args.push_back(IntOff);
                    CallInst *SrcChecked = B.CreateCall(hook, src_args);      
                    SrcChecked->setDoesNotThrow();    
                    Value *SrcCleaned = B.CreatePointerCast(SrcChecked, Src->getType());
                    MMI->setSource(SrcCleaned);

                    untaggedPtrs.insert(SrcCleaned);
                    untaggedPtrs.insert(MMI);
                    changed = true;
                }
            }
            else if (MemSetInst *MSI = dyn_cast<MemSetInst>(mi))
            {
                Value *Dest = MSI->getRawDest();
                Value *Length = MSI->getLength();
                dbg(errs() << ">>MSI " << *Dest << " | " << *Src << " | " << *Length   << "\n";)

                IRBuilder<> B(MSI);
                std::vector <Value*> arglist;

                if ( untaggedPtrs.find(Dest->stripPointerCasts()) != untaggedPtrs.end() ||
                    globalPtrs.find(Dest->stripPointerCasts()) != globalPtrs.end() ||
                    vtPtrs.find(Dest->stripPointerCasts()) != vtPtrs.end() )
                {
                    dbg(errs() << ">>" << __func__ << " global or volatile ptr Dest skipped: " << *MSI << "\n";)
                }
                else
                {
                    FunctionCallee hook;
                    if ( pmemPtrs.find(Dest->stripPointerCasts()) != pmemPtrs.end() )
                    {
                        dbg(errs() << "__spp_memintr_check_and_clean_direct\n";)
                        hook = hook_direct;
                    }
                    else
                    {
                        hook = hook_generic;
                    }
                    Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                    Value *DestPtr = B.CreateBitCast(Dest, hook.getFunctionType()->getParamType(0));
                    std::vector<Value*> dest_args;
                    dest_args.push_back(DestPtr);
                    dest_args.push_back(IntOff);
                    CallInst *DestChecked = B.CreateCall(hook, dest_args);
                    DestChecked->setDoesNotThrow();          
                    Value *DestCleaned = B.CreatePointerCast(DestChecked, Dest->getType());
                    MSI->setDest(DestCleaned);

                    untaggedPtrs.insert(DestCleaned); 
                    untaggedPtrs.insert(MSI);
                    changed = true;
                }
            }
            return changed;
        }

        bool instrGep(GetElementPtrInst *Gep) 
        {
            IRBuilder<> B(getInsertPointAfter(Gep));
            std::vector<User*> Users(Gep->user_begin(), Gep->user_end());
                        
            /* No effect on ptr means no effect on size. */
            if (Gep->hasAllZeroIndices()) 
            {
                dbg(errs() << ">>GEP: Zero Indices.. skipping...\n";)
                return false;
            }
                    
            /* We want to skip GEPs on vtable stuff, as they shouldn't be able to
            * overflow, and because they don't have metadata normally negative
            * GEPs fail on these. */
            if (isVtableGep(Gep))
            {
                return false;
            }

            /* TODO: we cannot support GEPs operating on vectors. */
            if (Gep->getType()->isVectorTy()) 
            {
                dbg(errs() << ">>GEP:Warning: ignoring GEP on vector: " << *Gep << "\n";)
                return false;
            }

            if (globalPtrs.find(Gep->getPointerOperand()->stripPointerCasts()) != globalPtrs.end())
            {
                dbg(errs() << ">>global ptr skipped tag update: " << *Gep << "\n";)
                globalPtrs.insert(Gep);
                return false;
            }            

            if (untaggedPtrs.find(Gep->getPointerOperand()->stripPointerCasts()) != untaggedPtrs.end())
            {
                dbg(errs() << ">>volatile ptr skipped tag update: " << *Gep << "\n";)
                untaggedPtrs.insert(Gep);
                return false;
            }   

            if (vtPtrs.find(Gep->getPointerOperand()->stripPointerCasts()) != vtPtrs.end())
            {
                dbg(errs() << ">>vtable ptr skipped tag update: " << *Gep << "\n";)
                untaggedPtrs.insert(Gep);
                return false;
            }   

            //get the GEP offset
            Value *GepOff = EmitGEPOffset(&B, *DL, Gep);
           
            // create hook prototype
            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            Type *Arg2Ty = Type::getInt64Ty(M->getContext());
            SmallVector <Type*, 2> tlist;
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
             
            FunctionType *hookfty = FunctionType::get(RetArgTy, tlist, false);
            FunctionCallee hook;           
            if (pmemPtrs.find(Gep->getPointerOperand()->stripPointerCasts()) != pmemPtrs.end())
            {
                dbg(errs() << "__spp_updatetag_direct\n";)
                hook = M->getOrInsertFunction("__spp_updatetag_direct", hookfty);
            }
            else 
            {
                hook = M->getOrInsertFunction("__spp_updatetag", hookfty);
            }

            Value *TmpPtr = B.CreateBitCast(Gep, hook.getFunctionType()->getParamType(0));
            Value *IntOff = B.CreateSExt(GepOff, hook.getFunctionType()->getParamType(1));
            
            std::vector<Value*> args;
            args.push_back(TmpPtr);
            args.push_back(IntOff);

            CallInst *Masked = B.CreateCall(hook, args);
            Masked->setDoesNotThrow(); //to avoid it getting converted to invoke     
            Value *UpdatedPtr = B.CreatePointerCast(Masked, Gep->getType());

            if (pmemPtrs.find(Gep->getPointerOperand()->stripPointerCasts()) != pmemPtrs.end())
            {
                dbg(errs() << "added: " << *UpdatedPtr << " ||| " << *Masked << "\n";)
                pmemPtrs.insert(Masked);
                setSPPprefix(Masked);
                pmemPtrs.insert(UpdatedPtr);
                setSPPprefix(UpdatedPtr);
            }

            for (auto User : Users) 
            {
                Instruction *iUser= dyn_cast<Instruction>(User);
                assert(iUser);
                User->setOperand(getOpIdx(iUser, Gep), UpdatedPtr);
                dbg(errs() << ">>GEP updated instruction: " << *iUser << " with " \
                            << *UpdatedPtr->stripPointerCasts() << "\n";)
                
                // mark directly derived values as persistent:
                // no need to check for volatile pointers as they will never reach here!
                if (pmemPtrs.find(UpdatedPtr) != pmemPtrs.end())
                {
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
            
            return true;

        }
        
        bool instrumentLoadOrStore(Instruction *I) 
        {            
            IRBuilder<> B(I);
            bool isStore = isa<StoreInst>(*I);
            Value* Ptr = isStore
                ? cast<StoreInst>(I)->getPointerOperand()
                : cast<LoadInst>(I)->getPointerOperand();
            
            assert(Ptr->getType()->isPointerTy()); 
            
            dbg(errs() << ">>" << __func__ << "Ptr: " << *Ptr << " stripped: " \
                        << *Ptr->stripPointerCasts() << " type : " << *Ptr->stripPointerCasts()->getType() << "\n";)
            
            if (isa<GetElementPtrInst>(Ptr->stripPointerCasts())) 
            {
                assert(!isMissedGep(cast<GetElementPtrInst>(Ptr->stripPointerCasts()), I));
            }
 
            if (isa<Constant>(Ptr->stripPointerCasts())) 
            {
                dbg(errs() << ">>" << __func__ << " constant skipping boundscheck: " \
                        << *Ptr->stripPointerCasts() << "\n";)
                return false;
            }

            if (Ptr->getName().startswith("vtable") ||
                Ptr->getName().startswith("vbase.offset") ||
                Ptr->getName().startswith("vfn")) 
            {
                dbg(errs() << ">>Ignoring vbase/vtable/vfn ld/st boundcheck: " << *I << "\n";)
                return false;
            }

            if (I->getName().startswith("vtable") ||
                I->getName().startswith("vbase.offset") ||
                I->getName().startswith("vfn")) 
            {
                dbg(errs() << ">>Ignoring vbase/vtable/vfn variables assignment boundcheck: " << *I << "\n";)
                return false;
            }

            //check for tag-free globals/volatile ptrs
            if ( untaggedPtrs.find(Ptr->stripPointerCasts()) != untaggedPtrs.end() ||
                 globalPtrs.find(Ptr->stripPointerCasts()) != globalPtrs.end() ||
                 vtPtrs.find(Ptr->stripPointerCasts()) != vtPtrs.end() )
            {
                dbg(errs() << ">>" << __func__ << " global or volatile ptr skipped checkbound: " << *I << "\n";)
                return false;
            }

            //check for already checked ptrs
            if ( checkedPtrs.find(Ptr) != checkedPtrs.end() )
            {
                dbg(errs() << ">>" << __func__ << " checked ptr skipped checkbound: " << *I << "\n";)
                return false;
            }

            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            SmallVector <Type*, 1> tlist;
            tlist.push_back(RetArgTy);
            FunctionType *hookfty = FunctionType::get(RetArgTy, RetArgTy, false);
            FunctionCallee hook;

            if (pmemPtrs.find(Ptr->stripPointerCasts()) != pmemPtrs.end())
            {
                dbg(errs() << ">> Inserted __spp_checkbound_direct\n";)
                hook = M->getOrInsertFunction("__spp_checkbound_direct", hookfty);
            }
            else 
            {
                hook = M->getOrInsertFunction("__spp_checkbound", hookfty);
            }

            Value *TmpPtr = B.CreateBitCast(Ptr, hook.getFunctionType()->getParamType(0));
            CallInst *Masked = B.CreateCall(hook, TmpPtr);
            Masked->setDoesNotThrow();
            Value *NewPtr = B.CreatePointerCast(Masked, Ptr->getType());

            dbg(errs() << ">> old ld/st: " << *I << " ptr: " << *Ptr << " stripped: " << *Ptr->stripPointerCasts() << "\n";)
            int OpIdx = getOpIdx(I, Ptr);
            I->setOperand(OpIdx, NewPtr);
            dbg(errs() << ">> updated ld/st: " << *I << " ptr: " << *NewPtr << " stripped: " << *NewPtr->stripPointerCasts() << "\n";)
            
            //replace subsequent uses of the same ptr in ld/st/atomic instructions
            checkedPtrs.insert(NewPtr);
            // checkedPtrs.insert(Ptr);
            
            dbg(errs() << "old ptr: " << *Ptr << " stripped: " << *Ptr->stripPointerCasts() << "\n";)
            dbg(errs() << "new ptr: " << *NewPtr << " stripped: " << *NewPtr->stripPointerCasts() << "\n";)
            /* replace these */
            DenseMap<Instruction*, int> replaceChecked;
            for(auto U : Ptr->users()){  // U is of type User*
                if (auto userI = dyn_cast<Instruction>(U)){

                    if (userI->getParent() == I->getParent() &&
                        userI->comesBefore(I))
                    {
                        dbg(errs() << "Earlier use of old ptr: " << *userI << "\n";)
                        continue;
                    }
                    // an instruction uses V
                    dbg(errs() << "Use of old ptr: " << *userI << "\n";)
                    if (isa<LoadInst>(userI) || isa<StoreInst>(userI) ||
                        isa<AtomicRMWInst>(userI) || isa<BitCastInst>(userI) ||
                        isa<CallInst>(userI) || isa<InvokeInst>(userI))
                    {
                        int OpIdx = getOpIdx(userI, Ptr);
                        if (OpIdx >= 0)
                        {
                            replaceChecked[userI] = OpIdx;
                        }
                    }
                }
            }

            DominatorTree DT = DominatorTree(*I->getFunction());
            for (auto it : replaceChecked)
            {
                Instruction* I = it.first;
                int OpIdx = it.second;
                dbg(errs() << "Instr without replacement: " << *I << "\n";)
                I->setOperand(OpIdx, NewPtr);
                dbg(errs() << "Instr with replacement: " << *I << " idx : " << OpIdx<<"\n";)
                
                if (!DT.dominates(NewPtr, I))
                {
                    I->setOperand(OpIdx, Ptr);
                    dbg(errs() << "Non-dominated -- revert back to: " << *I << "\n";)
                }
            }
            replaceChecked.clear();

            return true;
        }

        bool instrumentAtomicOps(Instruction *I) 
        {         
            //checkbound and then cleantag for atomic ops   
            IRBuilder<> B(I);
            Value* Ptr = cast<AtomicRMWInst>(I)->getPointerOperand();
            
            assert(Ptr->getType()->isPointerTy()); 
            
            dbg(errs() << ">>"__func__ << "Ptr: " << *Ptr << " stripped: " \
                        << *Ptr->stripPointerCasts() << "\n";)
            
            if (isa<GetElementPtrInst>(Ptr->stripPointerCasts())) 
            {
                assert(!isMissedGep(cast<GetElementPtrInst>(Ptr->stripPointerCasts()), I));
            }

            if (isa<Constant>(Ptr->stripPointerCasts())) 
            {
                dbg(errs() << ">>" << __func__ << " constant skipping boundscheck: " \
                        << *Ptr->stripPointerCasts() << "\n";)
                return false;
            }

            if (Ptr->getName().startswith("vtable") ||
                Ptr->getName().startswith("vbase.offset") ||
                Ptr->getName().startswith("vfn")) 
            {
                dbg(errs() << ">>Ignoring vbase/vtable/vfn atomic op boundcheck: " << *I << "\n";)
                return false;
            }

            if (I->getName().startswith("vtable") ||
                I->getName().startswith("vbase.offset") ||
                I->getName().startswith("vfn")) 
            {
                dbg(errs() << ">>Ignoring vbase/vtable/vfn variables assignment boundcheck: " << *I << "\n";)
                return false;
            }
            
            //check for tag-free globals/volatile ptrs
            if ( untaggedPtrs.find(Ptr->stripPointerCasts()) != untaggedPtrs.end() ||
                 globalPtrs.find(Ptr->stripPointerCasts()) != globalPtrs.end() ||
                 vtPtrs.find(Ptr->stripPointerCasts()) != vtPtrs.end() )
            {
                dbg(errs() << ">>" << __func__ << " global or volatile ptr skipped checkbound: " << *I << "\n";)
                return false;
            }

            //check for already checked ptrs
            if ( checkedPtrs.find(Ptr) != checkedPtrs.end() )
            {
                dbg(errs() << ">>" << __func__ << " checked ptr skipped checkbound: " << *I << "\n";)
                return false;
            }

            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            SmallVector <Type*, 1> tlist;
            tlist.push_back(RetArgTy);
            FunctionType *hookfty = FunctionType::get(RetArgTy, RetArgTy, false);
            FunctionCallee hook;
            if (pmemPtrs.find(Ptr->stripPointerCasts()) != pmemPtrs.end())
            {
                errs() << "__spp_checkbound_direct\n";
                hook = M->getOrInsertFunction("__spp_checkbound_direct", hookfty);
            }
            else 
            {
                hook = M->getOrInsertFunction("__spp_checkbound", hookfty);
            }

            Value *TmpPtr = B.CreateBitCast(Ptr, hook.getFunctionType()->getParamType(0));
            CallInst *Masked = B.CreateCall(hook, TmpPtr);
            Masked->setDoesNotThrow();
            Value *NewPtr = B.CreatePointerCast(Masked, Ptr->getType());
            
            int OpIdx = getOpIdx(I, Ptr);
            I->setOperand(OpIdx, NewPtr);
            dbg(errs() << ">> updated atomic op: " << *I << "\n";)

            //replace subsequent uses of the same ptr in ld/st/atomic instructions
            checkedPtrs.insert(NewPtr);
            checkedPtrs.insert(Ptr);
            
            dbg(errs() << "old ptr: " << *Ptr << " stripped: " << *Ptr->stripPointerCasts() << "\n";)
            dbg(errs() << "new ptr: " << *NewPtr << " stripped: " << *NewPtr->stripPointerCasts() << "\n";)

            /* replace these */
            DenseMap<Instruction*, int> replaceChecked;
            for(auto U : Ptr->users()){  // U is of type User*
                if (auto userI = dyn_cast<Instruction>(U)){

                    if (userI->getParent() == I->getParent() &&
                        userI->comesBefore(I))
                    {
                        dbg(errs() << "Earlier use of old ptr: " << *userI << "\n";)
                        continue;
                    }
                    // an instruction uses V
                    dbg(errs() << "Use of old ptr: " << *userI << "\n";)
                    if (isa<LoadInst>(userI) || isa<StoreInst>(userI) ||
                        isa<AtomicRMWInst>(userI) || isa<BitCastInst>(userI) ||
                        isa<CallInst>(userI) || isa<InvokeInst>(userI))
                    {
                        int OpIdx = getOpIdx(userI, Ptr);
                        if (OpIdx >= 0)
                        {
                            replaceChecked[userI] = OpIdx;
                        }
                    }
                }
            }
            
            DominatorTree DT = DominatorTree(*I->getFunction());
            for (auto it : replaceChecked)
            {
                Instruction* I = it.first;
                int OpIdx = it.second;
                dbg(errs() << "Instr without replacement: " << *I << "\n";)
                I->setOperand(OpIdx, NewPtr);
                dbg(errs() << "Instr with replacement: " << *I << " idx : " << OpIdx<<"\n";)
                
                if (!DT.dominates(NewPtr, I))
                {
                    I->setOperand(OpIdx, Ptr);
                    dbg(errs() << "Non-dominated -- revert back to: " << *I << "\n";)
                }
            }
            replaceChecked.clear();

            return true;
        }
        
        bool visitFunc(Function* F) 
        {
            bool changed = false;

            for (auto BI = F->begin(); BI != F->end(); ++BI) 
            {
                BasicBlock *BB = &*BI; 
                Instruction *sucInst = &*(BB->begin());

                for (auto II = BB->begin(); II != BB->end(); ++II) 
                {    
                    Instruction *Ins= &*II;

                    if (Ins != sucInst) 
                    {
                        dbg(errs() << "<<added_by_instrumentation: " << *Ins << " skipping\n";)
                        continue;
                    }

                    sucInst = getNextInst(Ins);
                     
                    changed = replaceFoldedGepOp(Ins);
                    
                    if (isa<LoadInst>(Ins) || isa<StoreInst>(Ins)) 
                    {
                        changed = instrumentLoadOrStore(Ins);
                    }
                    if (isa<AtomicRMWInst>(Ins))
                    {
                        changed = instrumentAtomicOps(Ins);
                    }
                    else if (auto *Gep = dyn_cast<GetElementPtrInst>(Ins)) 
                    {
                        /* GEPs handling --- Apply the arithmetic to the top tag part*/
                        changed = instrGep(Gep);
                    }
                    else if (auto *memIntr = dyn_cast<MemIntrinsic>(Ins))
                    {
                        /* LLVM memory intrinsics handling */
                        /* these are not wrapped and should be checked before cleaned */
                        dbg(errs() << ">>LLVM memory intrinsic fn call:" << memIntr->getName() << " checking..\n";)
                        changed = instrMemIntr(memIntr);
                    }
                    else if (isa<PtrToIntInst>(Ins))
                    {
                        /* Clean the tag for now */
                        /* remove them from checking possibly? */
                        dbg(errs() << ">>LLVM PtrToInt call: " << *Ins << " cleaning..\n";)
                        changed = instrPtrToInt(Ins);
                    }
                    else if (auto *callBase = dyn_cast<CallBase>(Ins))
                    {
                        /* Clean the tag for now */
                        dbg(errs() << ">>LLVM CallBase : " << *Ins << " to check for byval args\n";)
                        changed = instrCallBase(&*callBase);
                    }
                }
            } //endof forloop

            return changed;
        }

        bool trackPtrs(Function* F) 
        {

            // first check the byval arguments as they will be cleaned
            dbg(errs() << F->getName() << "\n";)
            for (auto Arg = F->arg_begin(); Arg != F->arg_end(); ++Arg) 
            {
                if (Arg->getType()->isPointerTy() && 
                    (Arg->hasAttribute(Attribute::ByVal) ||
                    Arg->hasAttribute(Attribute::StructRet)))
                {
                    dbg(errs()<<">> Already Cleaned Argument ByVal " << *Arg <<  "\n";)
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
                    /* Stack variables*/
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
                                default:
                                    break;
                            }                      
                        }
                    }
                    // CallBase to include CallInst and InvokeInst
                    else if (auto *CI = dyn_cast<CallBase>(Ins)) 
                    { 
                        Function* CalleeF = CI->getCalledFunction();
                        if (!CalleeF) continue;

                        /* Volatile Ptrs */
                        if (isAllocLikeFn(CI, getTLI(*CalleeF)) ||
                            isReallocLikeFn(CI, getTLI(*CalleeF)) ||
                            CalleeF->getName().contains("__errno_location") ||
                            CalleeF->getName().contains("__cxa")) 
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
                        /* PM Ptrs */
                        else if (CalleeF->getName().contains("pmemobj_direct"))
                                //  CalleeF->getName().contains("pmemobj_oid")) 
                        {
                            pmemPtrs.insert(Ins);
                            setSPPprefix(Ins);
                            dbg(errs()<<"PM ptr: "<<*Ins<< " Type : " << *Ins->getType() <<"\n";)

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
            }
            return false;
        }
        
    };
    
    class SPPModule : public ModulePass {
    public:
        static char ID;

        SPPModule() : ModulePass(ID) { }

        void getAnalysisUsage(AnalysisUsage &AU) const override{

            // AU.addRequired<DominatorTreeWrapperPass>();
            // AU.addRequired<AAResultsWrapperPass>(); 
            // AU.addRequired<CallGraphWrapperPass>(); 
            AU.addRequired<TargetLibraryInfoWrapperPass>();
        }

        virtual bool runOnModule(Module& M) override
        {
            errs() << ">>Running_SPP_Module_Pass start...\n";
            dbg(errs() << ">>" << __func__ << " : " << M.getModuleIdentifier() << "\n";)
            
            SPPPass Spp(&M);
            Spp.setDL(&M.getDataLayout()); //init the data layout
            Spp.setTLIWP(&getAnalysis<TargetLibraryInfoWrapperPass>());

            bool changed = false;
           
            // for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
            // {
            //     for (auto BB = Fn->begin(); BB != Fn->end(); ++BB) 
            //     {
            //         BasicBlock *BaB = &*BB; 
            //         if (BaB == &BaB->getParent()->getEntryBlock())
            //             errs() << *Fn <<"\n";
            //         errs() << *BB << "\n";
            //         // for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
            //         // {
            //         //     errs() << *ins << "\n";
            //         // }
            //     }
            // }

            //Track global ptrs
            for (auto GV = M.global_begin(); GV!=M.global_end(); GV++) 
            {
                dbg(errs() << "Global found : " << *GV << "\n";)
                Spp.globalPtrs.insert(&*GV);
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
                                Spp.globalPtrs.insert(iUser);
                                dbg(errs() << ">>Global ptr use: " << *iUser << "\n";)
                            default:
                                break;
                        }
                    }                     
                }
            }
            
            //Visit the functions to identify volatile ptrs, pm and vtable ptrs
            for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) 
            {                
                if (F->isDeclaration()) 
                {
                    dbg(errs() << "External.. skipping\n";)
                    continue; 
                }
                if (isSPPFuncName(F->getName()))
                {
                    dbg(errs() << "SPP hook func.. skipping\n";)
                    continue; 
                }

                dbg(errs() << "Internal.. processing\n";)
                changed = Spp.trackPtrs(&*F);
            }
            //Visit the functions to clear the appropriate ptr before external calls
            for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) 
            {
                dbg(errs() << ">>Func : " << F->getName() << "\t";)
                
                if (F->isDeclaration()) 
                {
                    dbg(errs() << "External.. skipping\n";)
                    continue; 
                }
                if (isSPPFuncName(F->getName()))
                {
                    dbg(errs() << "SPP hook func.. skipping\n";)
                    continue; 
                }

                if (F->getName().contains("pmemobj_direct"))
                    // F->getName().contains("pmemobj_oid"))
                {
                    dbg(errs() << "pmempobj direct func.. skipping\n";)
                    continue; 
                }

                dbg(errs() << "Internal.. processing\n";)
                changed = Spp.visitFunc(&*F);
            
            }
            
            errs() << ">>Running_SPP_Module_Pass exiting...\n";

            // for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
            // {
            //     for (auto BB = Fn->begin(); BB != Fn->end(); ++BB) 
            //     {
            //         BasicBlock *BaB = &*BB; 
            //         if (BaB == &BaB->getParent()->getEntryBlock())
            //             errs() << *Fn <<"\n";
            //         errs() << *BB << "\n";
            //         // for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
            //         // {
            //         //     errs() << *ins << "\n";
            //         // }
            //     }
            // }
            Spp.memCleanUp();
            return changed;
        }
        
    };

    char SPPModule::ID = 0;
    static RegisterPass<SPPModule> X("spp", "Safe Persistent Pointers Pass", false, false);

    static void registerPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) 
    {
        PM.add(new SPPModule());
        // PM.add(new VerifierPass());
    }
    //apply the module pass at this phase because EarlyAsPossible can cause UB
    static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
                   registerPass);

    //to keep the pass available even in -O0
    static RegisterStandardPasses
    RegisterMyPass_non_opt(PassManagerBuilder::EP_EnabledOnOptLevel0,
                   registerPass);

} // endof namespace


/////////////////////////////////////////////////////
///                                               ///
///                   SPPUtils.h                  ///
///                                               ///
/////////////////////////////////////////////////////

#ifndef LLVM_TRANSFORMS_SPP_UTILS_H
#define LLVM_TRANSFORMS_SPP_UTILS_H

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

using namespace llvm;

bool
isStringFuncName (StringRef fname)
{
    if (fname.startswith("strcmp") || 
        fname.startswith("strncmp") || 
        fname.startswith("strncpy") || 
        fname.startswith("memcmp") || 
        fname.startswith("memchr") || 
        fname.startswith("strchr") || 
        fname.startswith("strncat") ||
        fname.startswith("strcat") || 
        fname.startswith("strtol") || 
        fname.startswith("strcpy") || 
        fname.startswith("snprintf") ||
        fname.startswith("strlen")) 
    {   
        return true;
    }

    return false;
}

bool
isMemFuncName(StringRef fname)
{
    if (fname.equals("memset") || 
        fname.equals("memcpy") ||
        fname.equals("memmove") ||
        fname.equals("free")) 
    {  
        return true;
    }

    return false;
}

bool
isPMemFuncName(StringRef fname)
{
    if (fname.contains("pmem_memmove_persist") || 
        fname.contains("pmem_memcpy_persist") ||
        fname.contains("pmem_memmove_nodrain") ||
        fname.contains("pmem_memcpy_nodrain") ||
        fname.contains("pmem_memmove") ||
        fname.contains("pmem_memcpy") ||
        fname.contains("pmem_memset_nodrain") ||
        fname.contains("pmem_memset") ||
        fname.contains("pmem_memset_persist") ||
        fname.contains("pmemobj_memcpy") ||
        fname.contains("pmemobj_memcpy_persist") ||
        fname.contains("pmemobj_memmove") || 
        fname.contains("pmemobj_memset") ||
        fname.contains("pmemobj_memset_persist") )
    {  
        return true;
    }

    return false;
}

bool
isSPPFuncName(StringRef fname)
{
    if (fname.startswith("__spp")) 
    {    
        return true;
    }

    return false;
}

Instruction*
getNextInst(Instruction *Inst)
{
    BasicBlock::iterator I (Inst);
    I++;
    if (I == Inst->getParent()->end()) 
    {
        return nullptr;
    }
    return &*I;
}

#endif //LLVM_TRANSFORMS_SPP_UTILS_H

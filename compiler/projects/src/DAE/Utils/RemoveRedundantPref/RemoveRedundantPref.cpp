//===- RemoveRedundantPref.cpp - Pass to remove redundant
//prefetches--------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file RemoveRedundantPref.cpp
///
/// \brief Pass to remove redundant prefetches
///
/// \copyright Eta Scale AB. Licensed under the Eta Scale Open Source License. See
/// the LICENSE file for details.
//===----------------------------------------------------------------------===//
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include <fstream>
#include <iostream>
#include <set>

using namespace llvm;
using namespace std;

/* Intrinsics.gen*/
#define PREFETCH_ID 3856

namespace {
struct RemoveRedundantPref : public FunctionPass {

  static char ID;
  RemoveRedundantPref() : FunctionPass(ID) {}

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {}

  virtual bool runOnFunction(Function &F) {

    std::set<Value *> prefTargets;
    for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
	if (LoadInst *LI = dyn_cast<LoadInst>(&(*I)))
	{
		Value * target = LI->getPointerOperand();
                prefTargets.insert(target);
		//outs() << "target: " << *target << "\n";
		if (!isa<Instruction>(target))
		{
			target = target->stripPointerCasts();
                	prefTargets.insert(target);
		}
	}
    }
    std::vector<Instruction *> toBeRemoved;
    for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
      // prefetch instructions
      if (isa<CallInst>(&(*I))) {
        CallInst *ci = dyn_cast<CallInst>(&(*I));
        if (isa<IntrinsicInst>(ci)) {
          IntrinsicInst *intr = dyn_cast<IntrinsicInst>(ci);
	  //outs() << "IntrInstruction: " << *intr << " with ID: " << intr->getIntrinsicID()<< "\n";
		
          if (intr->getIntrinsicID() == PREFETCH_ID) {
	  //outs() << "PrefInstruction: " << *intr << "\n";
            Value *bitcast = ci->getArgOperand(0);
	    Value *target = (cast<Instruction>(bitcast))->getOperand(0);
	    //outs() << "target: " << *target << "\n";
            if (prefTargets.find(target) != prefTargets.end()) {
              // already prefetched or loaded
              //outs() << "Remove: " << *target << "\n";
              toBeRemoved.push_back(ci);
            } else {
              // first time prefetched
              //outs() << "Stay: " << *target << "\n";
              prefTargets.insert(target);
            }
          }
        }
      }
    }

    bool change = !toBeRemoved.empty();

    std::vector<Instruction *>::iterator it = toBeRemoved.begin(),
                                         et = toBeRemoved.end();
    while (it != et) {
      (*it)->eraseFromParent();
      it++;
    }

    return change;
  }
};
}

char RemoveRedundantPref::ID = 1;
static RegisterPass<RemoveRedundantPref>
    X("rrp", "Remove Redundant Prefetch instructions Pass", true, true);

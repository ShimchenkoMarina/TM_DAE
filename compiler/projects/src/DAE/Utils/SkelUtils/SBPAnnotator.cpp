//===--------------- SBPAnnotator.cpp - Annotator for branch merging ------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file SBPAnnotator.cpp
///
/// \brief
///
/// \copyright Eta Scale AB. Licensed under the Eta Scale Open Source License. See
/// the LICENSE file for details.
//
// Annotates branches with their static probability to be taken.
//
//===----------------------------------------------------------------------===//
#include <map>
#include <vector>
#include <string>
#include <iostream>
#include <type_traits>
#include <fstream>
#include <sstream>

#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"


#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "Util/Annotation/MetadataInfo.h"


using namespace llvm;
using namespace util;

std::string floatToString(float val) {
        std::ostringstream strs;
        strs << val;
        std::string s = strs.str();
        if (s.length() == 0) {
                return "0";
        }
	return s;
}

void saveToFile(std::string filename, TerminatorInst *TInst, std::string data) {
        std::ofstream file;
        file.open(filename, std::ios::app);
	Instruction * inst = dyn_cast<Instruction>(&*TInst);
        file << dyn_cast<Instruction>(&*TInst)->getParent()->getParent()->getName().str() << " : "<< data << "\n";
        file.close();
}

void getBranchProbabilities(Function &F, BranchProbabilityInfo *BPI) {
        /* This function is used to gather the probabilities for each branch.
        * If the terminator instruction has a conditional jump (two successors),
        * it will save the probability of the most likely taken branch to a file called "branchProbabilities.txt"
        * in the current folder
        */
	//Currently it has been changed to save probabilities for both branches
	//In complementary function, which is getBranchProb, both branches are evaluated
	//and this function return the number of branch that is more likely will be taken. 
        for (Function::iterator block = F.begin(), blockEnd = F.end(); block != blockEnd; ++block) {
                llvm::TerminatorInst *TInst = block->getTerminator();
                int numSuccessors = TInst->getNumSuccessors();
                if (numSuccessors == 2) {
                    BasicBlock *dst = TInst->getSuccessor(0);
                    BranchProbability result = BPI->getEdgeProbability(&*block, dst);
                    BranchProbability comp = result.getCompl();
                    float r = result.getNumerator() / ((float)result.getDenominator());
                    float r2 = result.getCompl().getNumerator() / ((float)result.getCompl().getDenominator());
                    //if (r >= r2) {
                        saveToFile("branchProbabilities.txt", TInst, floatToString(r));//0 successor
                    //} else {
                        saveToFile("branchProbabilities.txt", TInst, floatToString(r2));//1 successor
                    //}
                }
        }
}

void annotateBranches(Function &F, BranchProbabilityInfo *BPI) {
        /* This function annotates each branch with two meta data fields:
        * BranchProb0: the probability that the first branch is taken from the branch instruction
        * BranchProb1: the probability that the second branch is taken from the branch instruction
        * If there's one successor, BranchProb0 will be 1, and BranchProb1 will be 0.
        * If there's no successor, BranchProb0 will be 0, and BranchProb0 will be 0.
        */
        float r;
        for (Function::iterator block = F.begin(), blockEnd = F.end(); block != blockEnd; ++block) {
                TerminatorInst *TInst = block->getTerminator();
                if (BranchInst *BI = dyn_cast<BranchInst>(TInst)) {
                    if (BI->isConditional()) {
                        if (Value *vbi = dyn_cast<Value>(BI->getCondition())) {
			    if (vbi->getName().str().find("stdin") != std::string::npos) {
                                return;
                            }
                        }
                    }
           }
           int numSuccessors = TInst->getNumSuccessors();
           AttachMetadata(TInst, "BranchProb0", "0");
           AttachMetadata(TInst, "BranchProb1", "0");
           if (numSuccessors >= 1) {
                    BasicBlock *dst = TInst->getSuccessor(0);
                    BranchProbability result = BPI->getEdgeProbability(&*block, dst);
                    r = result.getNumerator() / ((float)result.getDenominator());
                    AttachMetadata(TInst, "BranchProb0", floatToString(r));
            } 
            if (numSuccessors == 2) {
                    BasicBlock *dst = TInst->getSuccessor(1);
                    BranchProbability result = BPI->getEdgeProbability(&*block, dst);
                    r = result.getNumerator() / ((float)result.getDenominator());
                    AttachMetadata(TInst, "BranchProb1", floatToString(r));
            }
        }
} 

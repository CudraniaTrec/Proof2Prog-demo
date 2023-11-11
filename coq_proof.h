//
// Created by Windows on 2023/11/9.
//

#ifndef PROOF2PROG_COQ_PROOF_H
#define PROOF2PROG_COQ_PROOF_H

#include<vector>
using namespace std;

#define SeqProofType 0
#define BranchProofType 1
#define SingleProofType 2

class CoqProof {
public:
    int type;
};

/*  proof1. proof2. */
class SeqProof : public CoqProof {
public:
    CoqProof *proof1;
    CoqProof *proof2;

    SeqProof(CoqProof *proof1, CoqProof *proof2) : proof1(proof1), proof2(proof2) {
        type = 0;
    }
};

/* - proofs[0].
 * - proofs[1].
 * ...
 * - proofs[len-1]. */
class BranchProof : public CoqProof {
public:
    vector<CoqProof *> proofs;
    int len;

    BranchProof(int len) :len(len) {
        type = 1;
        proofs = vector<CoqProof *>(len);
    }
};

class SingleProof : public CoqProof {
    
};

#endif //PROOF2PROG_COQ_PROOF_H

//
// Created by Windows on 2023/11/9.
//

#ifndef PROOF2PROG_COQ_PROOF_H
#define PROOF2PROG_COQ_PROOF_H

#include <utility>
#include<vector>
#include<string>

using namespace std;

#define SeqProofType 0
#define BranchProofType 1
#define SingleProofType 2

string delimiter(int level) {
    switch (level) {
        case 0:
            return "";
        case 1:
            return "- ";
        case 2:
            return "+ ";
        case 3:
            return "-- ";
        case 4:
            return "++ ";
        case 5:
            return "--- ";
        case 6:
            return "+++ ";
        default: {
            string res = "";
            for (int i = 0; i < level - 6; i++) {
                res += "*";
            }
            res += " ";
            return res;
        }
    }
}

string indent(int level) {
    string res = "";
    for (int i = 1; i <= level; i++) {
        for(int j = 0; j< delimiter(i).size(); j++)
            res += " ";
    }
    return res;
}

class CoqProof {
public:
    int type;

    virtual string out(int level, bool first_line_indent) {
        return "UndefinedProof";
    }

    string out() {
        return "Proof.\neexists.\n"+out(0, true);
    }
};

/* proof1.
 * proof2. */
class SeqProof : public CoqProof {
public:
    CoqProof *proof1;
    CoqProof *proof2;

    SeqProof(CoqProof *proof1, CoqProof *proof2) : proof1(proof1), proof2(proof2) {
        type = SeqProofType;
    }

    string out(int level, bool first_line_indent) override {
        string res = "";
        res += proof1->out(level, first_line_indent);
        res += proof2->out(level, true);
        return res;
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

    BranchProof(int len) : len(len) {
        type = BranchProofType;
        proofs = vector<CoqProof *>(len);
    }

    BranchProof(vector<CoqProof *> p) : len(p.size()) {
        type = BranchProofType;
        proofs = p;
    }

    string out(int level, bool first_line_indent) override {
        string res = "";
        if (first_line_indent)
            res += indent(level);
        res += delimiter(level+1);
        res += proofs[0]->out(level + 1, false);
        for (int i = 1; i < len; i++) {
            res += indent(level) + delimiter(level+1);
            res += proofs[i]->out(level+1, false);
        }
        return res;
    }
};

class SingleProof : public CoqProof {
public:
    string proof;

    SingleProof(string proof) : proof(proof) {
        type = SingleProofType;
    }

    string out(int level, bool first_line_indent) override {
        string res = "";
        if (first_line_indent)
            res += indent(level);
        res += proof + "\n";
        return res;
    }
};

#endif //PROOF2PROG_COQ_PROOF_H

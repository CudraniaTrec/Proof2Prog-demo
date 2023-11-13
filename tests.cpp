//
// Created by Windows on 2023/11/11.
//

#include "algorithm.h"
#include <fstream>
#include <ctime>
#include <cstdio>

using namespace std;

//\x:Nat. x
//able to find this?
void test1() {
    Tm *naive_tm1 = new LambdaTerm("x", new NatType(), new VarTerm("x"));

    beam_search_wrap(naive_tm1, true);
    beam_search_wrap(naive_tm1, false);
}

//\x:Nat. x+x
//able to find this?
void test2() {
    Tm *naive_tm2 = new LambdaTerm("x", new NatType(), new PlusTerm(new VarTerm("x"), new VarTerm("x")));

    beam_search_wrap(naive_tm2, true);
    beam_search_wrap(naive_tm2, false);
}

//\x:Nat. if 1<x then 1 else 0
//able to find this?
void test3() {
    Tm *naive_tm3 = new LambdaTerm("x", new NatType(),
                                   new IfTerm(new LessTerm(new NatTerm(1), new VarTerm("x")), new NatTerm(1),
                                              new NatTerm(0)));

    beam_search_wrap(naive_tm3, true);
    beam_search_wrap(naive_tm3, false);
}

//\x:Nat. \y:Nat. if x<y then y else x
//able to find this?
void test4() {
    Tm *max_tm = new LambdaTerm("x", new NatType(), new LambdaTerm("y", new NatType(), new IfTerm(
            new LessTerm(new VarTerm("x"), new VarTerm("y")), new VarTerm("y"), new VarTerm("x"))));

    beam_search_wrap(max_tm, true);
    beam_search_wrap(max_tm, false);
}

//test type check correctness
void test_type() {
    Tm *tm = new LambdaTerm("x", new NatType(), new EqualTerm(new NatTerm(1), new NotTerm(new VarTerm("x"))));
    cout << tm->out() << endl;
    cout << tm->type(Context())->out() << endl;
}

//change the unit node of a partial term
void test_unitNode_change() {
    Tm *t1 = new LambdaTerm("x", new NatType(), new PlusTerm(new VarTerm("x"), new UnitTerm()));
    Tm *t2 = new NatTerm(1);
    Tm *t3 = deepcopy(t1);
    cout << (*t1).out() << " " << (*t2).out() << " " << (*t3).out() << endl;
    t3->changeUnitNode(t3->findUnitNode()->tm, t2);
    cout << (*t1).out() << " " << (*t2).out() << " " << (*t3).out() << endl;
}

/* assumption.
 * split.
 * - simpl.
 *   reflexivity.
 * - + assumption.
 *   + split.
 *     -- assumption.
 *     -- simpl.
 *        reflexivity.
 *   + reflexivity.
 * Qed.
 * */
void test_coq_proof() {
    SingleProof *simpl = new SingleProof("simpl.");
    SingleProof *reflexivity = new SingleProof("reflexivity.");
    SingleProof *assumption = new SingleProof("assumption.");
    SingleProof *split = new SingleProof("split.");
    SingleProof *qed = new SingleProof("Qed.");

    SeqProof *simpl_ref = new SeqProof(simpl, reflexivity);
    BranchProof *branch1 = new BranchProof(vector<CoqProof *>{assumption, simpl_ref});
    SeqProof *seq1 = new SeqProof(split, branch1);
    BranchProof *branch2 = new BranchProof(vector<CoqProof *>{assumption, seq1, reflexivity});
    BranchProof *branch3 = new BranchProof(vector<CoqProof *>{simpl_ref, branch2});

    SeqProof *seq2 = new SeqProof(branch3, qed);
    SeqProof *seq3 = new SeqProof(split, seq2);
    SeqProof *seq4 = new SeqProof(assumption, seq3);

    cout << seq4->CoqProof::out() << endl;
}

//generate the proof for a partial term
void test_generate_coq_proof() {
    Tm *tm = new LambdaTerm("x", new NatType(), new LambdaTerm("y", new NatType(), new IfTerm(
            new LessTerm(new VarTerm("x"), new VarTerm("y")), new UnitTerm(), new UnitTerm())));
    cout << tm->coq_out();
}

//generate the proof for a random term
void test_generate_coq_proof_random() {
    int ranSize = 7;
    Tm *tm = nullptr;
    Context con = Context();
    int fails = 0;
    do {
        fails++;
        if (tm != nullptr)
            delete (tm);
        if (fails % 20 == 0) {
            ranSize--;
        }
        tm = generateRandomProg(ranSize, Context());
    } while (tm->type(con)->equals(new ErrorType()));
    cout << tm->coq_out();
}

string exec_get_result(string cmd) {
    char buffer[128];
    string result = "";
    cmd = fmt::format("{} 2>&1", cmd);
    FILE *pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        cout << "popen failed!" << endl;
        return "";
    }
    while (!feof(pipe)) {
        if (fgets(buffer, 128, pipe) != NULL) {
            result += buffer;
        }
    }
    pclose(pipe);
    return result;
}

//test whether coq accept the proof
bool test_coq_accept_proof(string proof, bool verbose = false) {
    string coq_work_folder = "/home/cudrania/coq/coq_client/coq-lsp-pyclient/coq_proj/";
    string coq_work_file = "/home/cudrania/coq/coq_client/coq-lsp-pyclient/coq_proj/search.v";
    string coq_work_file2 = "output/coq_code.txt";
    
    //write coq_code to coq_work_file
    ofstream fout(coq_work_file.c_str());
    if (!fout.is_open()) {  //print error message and exit
        cerr << "Can't open output file" << endl;
        return false;
    }

    string coq_code = "From PLF Require Import demo.\nImport demo.Demo2.\n";
    coq_code += proof;
    fout << coq_code << endl;
    fout.close();

    string cmd = fmt::format("cd {} && /home/cudrania/.opam/default/bin/coqc -Q . PLF search.v", coq_work_folder);
    string res = exec_get_result(cmd);
    if (res == "") {
        return true;
    } else {
        if (verbose) {
            cout << res << endl;
        }
        return false;
    }
}

//test the ability between coq and type check
void test_coq_VS_typecheck(int size = 10) {
    int coq_accept_time = 0, typeCheck_accept_time = 0;
    for (int i = 0; i < size; i++) {
        Tm *tm = generateRandomProg(5, Context(), true);
        string proof = tm->coq_out();
        if (test_coq_accept_proof(proof)) {
            coq_accept_time++;
            if (tm->type(Context())->equals(new ErrorType())) {
                cout << "coq accept but type check reject! : " << endl;
                cout << tm->out() << endl << endl;
            } else {
                typeCheck_accept_time++;
            }
        }
    }
    cout << "coq accept time: " << coq_accept_time << endl;
    cout << "type check accept time: " << typeCheck_accept_time << endl;
    cout << "coq accept rate: " << (double) typeCheck_accept_time / coq_accept_time << endl;
}

int main() {
    srand(time(0));
    test_coq_VS_typecheck(100);
//    cout << exec_get_result("\"/home/cudrania/.opam/default/bin/coqc --version\"");
}

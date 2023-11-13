//
// Created by Windows on 2023.
//

#ifndef PROOF2PROG_TERMS_H
#define PROOF2PROG_TERMS_H

#include <utility>
#include "param.h"
#include "Types.h"
#include "coq_proof.h"
#include "fmt/core.h"

typedef map<string, Ty *> Context;

/*
 tm =
0   tm tm
1   | lambda x. tm
2   | x
3   | if tm then tm else tm
4   | nat
5   | tm + tm
6   | tm - tm
7   | true
8   | false
9   | tm && tm
10  | tm || tm
11  | ~ tm
12  | tm < tm
13  | tm = tm
14  | unit
15  | error */

#define AppTm 0
#define LambdaTm 1
#define VarTm 2
#define IfTm 3
#define NatTm 4
#define PlusTm 5
#define MinusTm 6
#define TrueTm 7
#define FalseTm 8
#define AndTm 9
#define OrTm 10
#define NotTm 11
#define LessTm 12
#define EqualTm 13
#define UnitTm 14
#define ErrorTm 15


class Tm {
public:
    int tm_num;

    explicit Tm(int tm_num)
            : tm_num(tm_num) {}

    virtual string out() {
        return "UndefinedTerm";
    }

    string coq_out() {
        string term_code = out();
        string coq_proof = generateProof()->out();
        string res = "Example test: well_typed (<{";
        res += term_code + "}>).\n" + coq_proof + "Qed.\n";
        return res;
    }

    virtual Ty *type(Context con) {
        return new ErrorType();
    }

    virtual Tm *substitute(string x, Tm *t) {
        return nullptr;
    }

    virtual bool equals(Tm &tm) {
        return false;
    }

    virtual int size() {
        return 1;
    }

    class UnitNode {
    public:
        Tm *tm;
        int depth;
        Context *con;

        UnitNode(Tm *tm, int depth, Context *con)
                : tm(tm), depth(depth), con(con) {}
    };

    virtual UnitNode *findUnitNode() {
        return nullptr;
    }

    virtual void changeUnitNode(Tm *unit, Tm *tm) {}

    virtual CoqProof *generateProof() {
        return new SingleProof("UndefinedProof");
    }
};

class VarTerm : public Tm {
public:
    string x;

    explicit VarTerm(string x)
            : Tm(VarTm), x(x) {}

    string out() override {
        return x;
    }

    Ty *type(Context con) override {
        auto it = con.find(x);
        if (it == con.end()) return new ErrorType();
        return it->second;
    }

    Tm *substitute(string x, Tm *t) override {
        if (this->x == x) return t;
        return new VarTerm(this->x);
    }

    bool equals(Tm &tm) override {
        VarTerm *vt = dynamic_cast<VarTerm *>(&tm);
        if (vt == nullptr) return false;
        return x == vt->x;
    }

    int size() override {
        return 1;
    }

    UnitNode *findUnitNode() override {
        return nullptr;
    }

    CoqProof *generateProof() override {
        return new SingleProof("apply T_Var. simpl_map. reflexivity. ");
    }
};

class AppTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;

    AppTerm(Tm *t1, Tm *t2)
            : Tm(AppTm), t1(t1), t2(t2) {}

    string out() override {
        return "( " + t1->out() + " " + t2->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);
        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy) return new ErrorType();
        if (t1_type->ty_num == UnitTy) return new UnitType();
        if (t1_type->ty_num != ArrowTy) return new ErrorType();

        ArrowType *at = dynamic_cast<ArrowType *>( t1_type );
        if (at == nullptr) return new ErrorType();
        if (t2_type->contains(at->domain)) return at->range;
        return new ErrorType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new AppTerm(t1->substitute(x, t), t2->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        AppTerm *at = dynamic_cast<AppTerm *>(&tm);
        if (at == nullptr) return false;
        return t1->equals(*at->t1) && t2->equals(*at->t2);
    }

    int size() override {
        return 1 + t1->size() + t2->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;

        if (t1_node == nullptr) return t2_node;
        if (t2_node == nullptr) return t1_node;

        if (t1_node->depth <= t2_node->depth) return t1_node;
        else return t2_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2});
        return new SeqProof(new SingleProof("eapply T_App. "), branch);
    }

};

class LambdaTerm : public Tm {
public:
    string x;
    Ty *ty;
    Tm *t;

    LambdaTerm(string x, Ty *ty, Tm *t)
            : Tm(LambdaTm), x(std::move(x)), t(t), ty(ty) {}

    string out() override {
        return "(\\" + x + ":" + ty->out() + ", " + t->out() + ")";// \x:nat, x
    }

    Ty *type(Context con) override {
        Context new_con = con;
        new_con.insert_or_assign(x, ty);
        Ty *t_type = t->type(new_con);
        if (t_type->ty_num == ErrorTy) return new ErrorType();
        return new ArrowType(ty, t_type);
    }

    Tm *substitute(string x, Tm *t) override {
        if (this->x == x) return substitute("error", t);
        return new LambdaTerm(this->x, ty, this->t->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        LambdaTerm *lt = dynamic_cast<LambdaTerm *>(&tm);
        if (lt == nullptr) return false;
        if (!ty->equals(lt->ty)) return false;
        if (x == lt->x) return t->equals(*lt->t);
        return t->substitute(x, new VarTerm(lt->x))->equals(*lt->t);
    }

    int size() override {
        return 1 + t->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t_node = t->findUnitNode();
        if (t_node == nullptr) return nullptr;

        t_node->depth++;
        t_node->con->insert_or_assign(x, ty);
        return t_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t == unit) {
            t = tm;
            return;
        }
        t->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof = t->generateProof();
        return new SeqProof(new SingleProof("eapply T_Abs. "), proof);
    }
};

class IfTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;
    Tm *t3;

    IfTerm(Tm *t1, Tm *t2, Tm *t3)
            : Tm(IfTm), t1(t1), t2(t2), t3(t3) {}

    string out() override {
        return "( if " + t1->out() + " then " + t2->out() + " else " + t3->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);
        Ty *t3_type = t3->type(con);
        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy || t3_type->ty_num == ErrorTy)
            return new ErrorType();

        if (t1_type->ty_num != BoolTy && t1_type->ty_num != UnitTy) return new ErrorType();
        if (t2_type->ty_num == UnitTy) return t3_type;
        if (t3_type->ty_num == UnitTy) return t2_type;
        if (!t2_type->equals(t3_type)) return new ErrorType();
        return t2_type;
    }

    Tm *substitute(string x, Tm *t) override {
        return new IfTerm(t1->substitute(x, t), t2->substitute(x, t), t3->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        IfTerm *it = dynamic_cast<IfTerm *>(&tm);
        if (it == nullptr) return false;
        return t1->equals(*it->t1) && t2->equals(*it->t2) && t3->equals(*it->t3);
    }

    int size() override {
        return 1 + t1->size() + t2->size() + t3->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        UnitNode *t3_node = t3->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;
        if (t3_node != nullptr)t3_node->depth++;

        if (t1_node == nullptr && t2_node == nullptr) return t3_node;
        if (t1_node == nullptr && t3_node == nullptr) return t2_node;
        if (t2_node == nullptr && t3_node == nullptr) return t1_node;
        if (t1_node == nullptr) return t2_node->depth <= t3_node->depth ? t2_node : t3_node;
        if (t2_node == nullptr) return t1_node->depth <= t3_node->depth ? t1_node : t3_node;
        if (t3_node == nullptr) return t1_node->depth <= t2_node->depth ? t1_node : t2_node;

        if (t1_node->depth <= t2_node->depth && t1_node->depth <= t3_node->depth) return t1_node;
        if (t2_node->depth <= t1_node->depth && t2_node->depth <= t3_node->depth) return t2_node;
        return t3_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        if (t3 == unit) {
            t3 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
        t3->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();
        CoqProof *proof3 = t3->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2, proof3});
        return new SeqProof(new SingleProof("eapply T_If. "), branch);
    }
};

class NatTerm : public Tm {
public:
    int n;

    explicit NatTerm(int n)
            : Tm(NatTm), n(n) {}

    string out() override {
        return to_string(n);
    }

    Ty *type(Context con) override {
        return new NatType();
    }

    bool equals(Tm &tm) override {
        NatTerm *nt = dynamic_cast<NatTerm *>(&tm);
        if (nt == nullptr) return false;
        return n == nt->n;
    }

    Tm *substitute(string x, Tm *t) override {
        return new NatTerm(n);
    }

    int size() override {
        return 1;
    }

    UnitNode *findUnitNode() override {
        return nullptr;
    }

    CoqProof *generateProof() override {
        return new SingleProof("apply T_Nat. ");
    }
};

class PlusTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;

    PlusTerm(Tm *t1, Tm *t2)
            : Tm(PlusTm), t1(t1), t2(t2) {}

    string out() override {
        return "( " + t1->out() + " + " + t2->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);

        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy) return new ErrorType();
        if (t1_type->ty_num != NatTy && t1_type->ty_num != UnitTy) return new ErrorType();
        if (t2_type->ty_num != NatTy && t2_type->ty_num != UnitTy) return new ErrorType();
        return new NatType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new PlusTerm(t1->substitute(x, t), t2->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        PlusTerm *pt = dynamic_cast<PlusTerm *>(&tm);
        if (pt == nullptr) return false;
        return t1->equals(*pt->t1) && t2->equals(*pt->t2);
    }

    int size() override {
        return 1 + t1->size() + t2->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;

        if (t1_node == nullptr) return t2_node;
        if (t2_node == nullptr) return t1_node;

        if (t1_node->depth <= t2_node->depth) return t1_node;
        else return t2_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2});
        return new SeqProof(new SingleProof("apply T_Add. "), branch);
    }
};

class MinusTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;

    MinusTerm(Tm *t1, Tm *t2)
            : Tm(MinusTm), t1(t1), t2(t2) {}

    string out() override {
        return "( " + t1->out() + " - " + t2->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);

        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy) return new ErrorType();
        if (t1_type->ty_num != NatTy && t1_type->ty_num != UnitTy) return new ErrorType();
        if (t2_type->ty_num != NatTy && t2_type->ty_num != UnitTy) return new ErrorType();
        return new NatType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new MinusTerm(t1->substitute(x, t), t2->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        MinusTerm *mt = dynamic_cast<MinusTerm *>(&tm);
        if (mt == nullptr) return false;
        return t1->equals(*mt->t1) && t2->equals(*mt->t2);
    }

    int size() override {
        return 1 + t1->size() + t2->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;

        if (t1_node == nullptr) return t2_node;
        if (t2_node == nullptr) return t1_node;

        if (t1_node->depth <= t2_node->depth) return t1_node;
        else return t2_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2});
        return new SeqProof(new SingleProof("apply T_Sub. "), branch);
    }
};

class TrueTerm : public Tm {
public:
    TrueTerm()
            : Tm(TrueTm) {}

    string out() override {
        return "true";
    }

    Ty *type(Context con) override {
        return new BoolType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new TrueTerm();
    }

    bool equals(Tm &tm) override {
        TrueTerm *tt = dynamic_cast<TrueTerm *>(&tm);
        if (tt == nullptr) return false;
        return true;
    }

    int size() override {
        return 1;
    }

    UnitNode *findUnitNode() override {
        return nullptr;
    }

    CoqProof *generateProof() override {
        return new SingleProof("apply T_True. ");
    }
};

class FalseTerm : public Tm {
public:
    FalseTerm()
            : Tm(FalseTm) {}

    string out() override {
        return "false";
    }

    Ty *type(Context con) override {
        return new BoolType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new FalseTerm();
    }

    bool equals(Tm &tm) override {
        FalseTerm *ft = dynamic_cast<FalseTerm *>(&tm);
        if (ft == nullptr) return false;
        return true;
    }

    int size() override {
        return 1;
    }

    CoqProof *generateProof() override {
        return new SingleProof("apply T_False. ");
    }
};

class AndTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;

    AndTerm(Tm *t1, Tm *t2)
            : Tm(AndTm), t1(t1), t2(t2) {}

    string out() override {
        return "( " + t1->out() + " && " + t2->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);

        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy) return new ErrorType();
        if (t1_type->ty_num != BoolTy && t1_type->ty_num != UnitTy) return new ErrorType();
        if (t2_type->ty_num != BoolTy && t2_type->ty_num != UnitTy) return new ErrorType();
        return new BoolType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new AndTerm(t1->substitute(x, t), t2->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        AndTerm *at = dynamic_cast<AndTerm *>(&tm);
        if (at == nullptr) return false;
        return t1->equals(*at->t1) && t2->equals(*at->t2);
    }

    int size() override {
        return 1 + t1->size() + t2->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;

        if (t1_node == nullptr) return t2_node;
        if (t2_node == nullptr) return t1_node;

        if (t1_node->depth <= t2_node->depth) return t1_node;
        else return t2_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2});
        return new SeqProof(new SingleProof("apply T_And. "), branch);
    }
};

class OrTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;

    OrTerm(Tm *t1, Tm *t2)
            : Tm(OrTm), t1(t1), t2(t2) {}

    string out() override {
        return "( " + t1->out() + " || " + t2->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);

        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy) return new ErrorType();
        if (t1_type->ty_num != BoolTy && t1_type->ty_num != UnitTy) return new ErrorType();
        if (t2_type->ty_num != BoolTy && t2_type->ty_num != UnitTy) return new ErrorType();
        return new BoolType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new OrTerm(t1->substitute(x, t), t2->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        OrTerm *ot = dynamic_cast<OrTerm *>(&tm);
        if (ot == nullptr) return false;
        return t1->equals(*ot->t1) && t2->equals(*ot->t2);
    }

    int size() override {
        return 1 + t1->size() + t2->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;

        if (t1_node == nullptr) return t2_node;
        if (t2_node == nullptr) return t1_node;

        if (t1_node->depth <= t2_node->depth) return t1_node;
        else return t2_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2});
        return new SeqProof(new SingleProof("apply T_Or. "), branch);
    }
};

class NotTerm : public Tm {
public:
    Tm *t;

    explicit NotTerm(Tm *t)
            : Tm(NotTm), t(t) {}

    string out() override {
        return "( ~" + t->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t_type = t->type(con);
        if (t_type->ty_num == ErrorTy) return new ErrorType();
        if (t_type->ty_num != BoolTy && t_type->ty_num != UnitTy) return new ErrorType();
        return new BoolType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new NotTerm(this->t->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        NotTerm *nt = dynamic_cast<NotTerm *>(&tm);
        if (nt == nullptr) return false;
        return this->t->equals(*nt->t);
    }

    int size() override {
        return 1 + t->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t_node = t->findUnitNode();
        if (t_node != nullptr)t_node->depth++;
        return t_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t == unit) {
            t = tm;
            return;
        }
        t->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof = t->generateProof();
        return new SeqProof(new SingleProof("apply T_Not. "), proof);
    }
};

class LessTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;

    LessTerm(Tm *t1, Tm *t2)
            : Tm(LessTm), t1(t1), t2(t2) {}

    string out() override {
        return "( " + t1->out() + " < " + t2->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);
        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy) return new ErrorType();
        if (t1_type->ty_num != NatTy && t1_type->ty_num != UnitTy) return new ErrorType();
        if (t2_type->ty_num != NatTy && t2_type->ty_num != UnitTy) return new ErrorType();
        return new BoolType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new LessTerm(t1->substitute(x, t), t2->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        LessTerm *lt = dynamic_cast<LessTerm *>(&tm);
        if (lt == nullptr) return false;
        return t1->equals(*lt->t1) && t2->equals(*lt->t2);
    }

    int size() override {
        return 1 + t1->size() + t2->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;

        if (t1_node == nullptr) return t2_node;
        if (t2_node == nullptr) return t1_node;

        if (t1_node->depth <= t2_node->depth) return t1_node;
        else return t2_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2});
        return new SeqProof(new SingleProof("apply T_Lt. "), branch);
    }
};

class EqualTerm : public Tm {
public:
    Tm *t1;
    Tm *t2;

    EqualTerm(Tm *t1, Tm *t2)
            : Tm(EqualTm), t1(t1), t2(t2) {}

    string out() override {
        return "( " + t1->out() + " == " + t2->out() + " )";
    }

    Ty *type(Context con) override {
        Ty *t1_type = t1->type(con);
        Ty *t2_type = t2->type(con);
        if (t1_type->ty_num == ErrorTy || t2_type->ty_num == ErrorTy) return new ErrorType();
        if (t1_type->ty_num != NatTy && t1_type->ty_num != UnitTy) return new ErrorType();
        if (t2_type->ty_num != NatTy && t2_type->ty_num != UnitTy) return new ErrorType();
        return new BoolType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new EqualTerm(t1->substitute(x, t), t2->substitute(x, t));
    }

    bool equals(Tm &tm) override {
        EqualTerm *et = dynamic_cast<EqualTerm *>(&tm);
        if (et == nullptr) return false;
        return t1->equals(*et->t1) && t2->equals(*et->t2);
    }

    int size() override {
        return 1 + t1->size() + t2->size();
    }

    UnitNode *findUnitNode() override {
        UnitNode *t1_node = t1->findUnitNode();
        UnitNode *t2_node = t2->findUnitNode();
        if (t1_node != nullptr)t1_node->depth++;
        if (t2_node != nullptr)t2_node->depth++;

        if (t1_node == nullptr) return t2_node;
        if (t2_node == nullptr) return t1_node;

        if (t1_node->depth <= t2_node->depth) return t1_node;
        else return t2_node;
    }

    void changeUnitNode(Tm *unit, Tm *tm) override {
        if (t1 == unit) {
            t1 = tm;
            return;
        }
        if (t2 == unit) {
            t2 = tm;
            return;
        }
        t1->changeUnitNode(unit, tm);
        t2->changeUnitNode(unit, tm);
    }

    CoqProof *generateProof() override {
        CoqProof *proof1 = t1->generateProof();
        CoqProof *proof2 = t2->generateProof();

        BranchProof *branch = new BranchProof(vector<CoqProof *>{proof1, proof2});
        return new SeqProof(new SingleProof("apply T_Eq. "), branch);
    }
};

class UnitTerm : public Tm {
public:
    UnitTerm()
            : Tm(UnitTm) {}

    string out() override {
        return "unit";
    }

    Ty *type(Context con) override {
        return new UnitType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new UnitTerm();
    }

    bool equals(Tm &tm) override {
        UnitTerm *ut = dynamic_cast<UnitTerm *>(&tm);
        if (ut == nullptr) return false;
        return true;
    }

    int size() override {
        return 1;
    }

    UnitNode *findUnitNode() override {
        return new UnitNode(this, 0, new Context());
    }

    CoqProof *generateProof() override {
        return new SingleProof("admit. ");
    }
};

class ErrorTerm : public Tm {
public:
    ErrorTerm()
            : Tm(ErrorTm) {}

    string out() override {
        return "error";
    }

    Ty *type(Context con) override {
        return new ErrorType();
    }

    Tm *substitute(string x, Tm *t) override {
        return new ErrorTerm();
    }

    bool equals(Tm &tm) override {
        ErrorTerm *et = dynamic_cast<ErrorTerm *>(&tm);
        if (et == nullptr) return false;
        return true;
    }

    int size() override {
        return 1;
    }

    UnitNode *findUnitNode() override {
        return nullptr;
    }

    CoqProof *generateProof() override {
        return new SingleProof("Admitted. ");
    }
};


Tm *deepcopy(Tm *tm) {
    return tm->substitute("error", new ErrorTerm());
}

#endif //PROOF2PROG_TERMS_H

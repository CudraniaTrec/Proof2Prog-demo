//
// Created by Windows on 2023.
//

#ifndef PROOF2PROG_TYPES_H
#define PROOF2PROG_TYPES_H

#include <iostream>
#include <string>
#include <map>
using namespace std;

/* ty =
0    nat
1    | bool
2    | ty -> ty
3    | unit
4    | error*/

#define NatTy 0
#define BoolTy 1
#define ArrowTy 2
#define UnitTy 3
#define ErrorTy 4

class Ty {
public:
    int ty_num;

    explicit Ty( int ty_num )
            : ty_num( ty_num ) {}

    virtual string out(){
        return "UndefinedType";
    }

    virtual bool equals(Ty* t ) { return ty_num == t->ty_num; }

    virtual bool contains(Ty* t ) { return equals(t); }
};

class NatType : public Ty {
public:
    NatType()
            : Ty( NatTy ) {}

    string out() override { return "Nat"; }
};

class BoolType : public Ty {
public:
    BoolType()
            : Ty( BoolTy ) {}

    string out() override { return "Bool"; }
};

class ArrowType : public Ty {
public:
    Ty *domain;
    Ty *range;

    ArrowType( Ty *t1, Ty *t2 )
            : Ty( ArrowTy )
            , domain( t1 )
            , range( t2 ) {}

    string out() override {
        return "( "+domain->out()+" -> " + range->out() + " )"; // ( nat -> bool )
    }

    bool equals(Ty* t ) override {
        if ( ty_num != t->ty_num ) return false;
        ArrowType *at = dynamic_cast<ArrowType *>( t );
        if ( at == nullptr ) return false;

        return domain->equals( at->domain ) && range->equals( at->range );
    }

    bool contains(Ty* t ) override {
        if ( ty_num != t->ty_num ) return false;
        ArrowType *at = dynamic_cast<ArrowType *>( t );
        if ( at == nullptr ) return false;

        return domain->contains(at->domain) && range->contains(at->range);
    }
};

class UnitType : public Ty {
public:
    UnitType()
            : Ty( UnitTy ) {}

    string out() override { return "Unit"; }

    bool contains(Ty* t ) override { return true; }
};

class ErrorType : public Ty {
public:
    ErrorType()
            : Ty( ErrorTy ) {}

    string out() override { return "ErrorType"; }
};


#endif //PROOF2PROG_TYPES_H

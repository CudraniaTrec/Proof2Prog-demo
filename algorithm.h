//
// Created by Windows on 2023.
//

#ifndef PROOF2PROG_ALGORITHM_H
#define PROOF2PROG_ALGORITHM_H

#include"Terms.h"
#include<queue>
#include<vector>
#include<list>
#include<map>
#include<cmath>

struct BeamItem {
    Tm *tm;
    double prob;

    BeamItem(Tm *tm, double prob) : tm(tm), prob(prob) {}
};

struct Beam {
    list<BeamItem *> beamList;
    int beamSize;

    Beam(int beamSize) : beamSize(beamSize) {
        beamList = list<BeamItem *>();
    }

    int size() {
        return beamList.size();
    }

    void add(BeamItem *item) {
        int flag = 0;
        for (auto it = beamList.begin(); it != beamList.end(); it++) {
            if ((*it)->prob > item->prob) {
                beamList.insert(it, item);
                flag = 1;
                break;
            }
        }
        if (flag == 0) {
            beamList.push_back(item);
        }
    }

    int push(BeamItem *item) {
        if (size() < beamSize) {
            add(item);
            return 1;
        }

        if (item->prob <= beamList.front()->prob) {
            return 0;
        }
        BeamItem* del = beamList.front();
        beamList.pop_front();
        delete del;
        add(item);
        return 1;
    }

    BeamItem *getRandom() {
        int index = rand() % beamList.size();
        for (auto it = beamList.begin(); it != beamList.end(); it++) {
            if (index == 0) {
                BeamItem *ret = *it;
                beamList.erase(it);
                return ret;
            }
            index--;
        }
    }

    BeamItem *getBest() {
        BeamItem *ret = beamList.back();
        beamList.pop_back();
        return ret;
    }

    vector<BeamItem *> getNeeded(int n) {
        vector<BeamItem *> ret = vector<BeamItem *>();
        for (int i = 0; i < n; i++) {
            if (size() == 0)
                break;
            else
                ret.push_back(getBest());
        }
        if (size() > 0)
            ret.push_back(getRandom());
        return ret;
    }
};

string generateNewVar(Context *con) {
    for (auto &it: alphabet) {
        if (con->find(it) == con->end()) {
            return it;
        }
    }
    return "err";
}

vector<BeamItem *> generateRandomNode(Context *con) {
    vector<BeamItem *> ret = vector<BeamItem *>();
    double prob = prob_all();
    ret.push_back(new BeamItem(new AppTerm(new UnitTerm(), new UnitTerm()), app_prob / prob));

    string var = generateNewVar(con);
    ret.push_back(new BeamItem(new LambdaTerm(var, new NatType(), new UnitTerm()), 0.5 * lambda_prob / prob));
    ret.push_back(new BeamItem(new LambdaTerm(var, new BoolType(), new UnitTerm()), 0.2 * lambda_prob / prob));
    ret.push_back(new BeamItem(new LambdaTerm(var, new ArrowType(new NatType(), new NatType()), new UnitTerm()),
                               0.1 * lambda_prob / prob));
    ret.push_back(new BeamItem(new LambdaTerm(var, new ArrowType(new BoolType(), new BoolType()), new UnitTerm()),
                               0.1 * lambda_prob / prob));
    ret.push_back(new BeamItem(new LambdaTerm(var, new ArrowType(new NatType(), new BoolType()), new UnitTerm()),
                               0.1 * lambda_prob / prob));

    for (auto v: *con)
        ret.push_back(new BeamItem(new VarTerm(v.first), (var_prob / con->size()) / prob));

    ret.push_back(new BeamItem(new IfTerm(new UnitTerm(), new UnitTerm(), new UnitTerm()), if_prob / prob));

    ret.push_back(new BeamItem(new NatTerm(0), 0.4 * nat_prob / prob));
    ret.push_back(new BeamItem(new NatTerm(1), 0.5 * nat_prob / prob));
    ret.push_back(new BeamItem(new NatTerm(2), 0.1 * nat_prob / prob));

    ret.push_back(new BeamItem(new PlusTerm(new UnitTerm(), new UnitTerm()), plus_prob / prob));
    ret.push_back(new BeamItem(new MinusTerm(new UnitTerm(), new UnitTerm()), minus_prob / prob));
    ret.push_back(new BeamItem(new TrueTerm(), true_prob / prob));
    ret.push_back(new BeamItem(new FalseTerm(), false_prob / prob));
    ret.push_back(new BeamItem(new AndTerm(new UnitTerm(), new UnitTerm()), and_prob / prob));
    ret.push_back(new BeamItem(new OrTerm(new UnitTerm(), new UnitTerm()), or_prob / prob));
    ret.push_back(new BeamItem(new NotTerm(new UnitTerm()), not_prob / prob));
    ret.push_back(new BeamItem(new LessTerm(new UnitTerm(), new UnitTerm()), less_prob / prob));
    ret.push_back(new BeamItem(new EqualTerm(new UnitTerm(), new UnitTerm()), equal_prob / prob));

    return ret;
}

int failTime = 0;

Tm *beamSearchOne(BeamItem *item, Beam *b, Tm *target, int size, bool type_check) {
    Tm *tm = item->tm;

//    cout << "Get Term: " << tm->out() << ", prob: " << item->prob << endl;

    Tm::UnitNode *unit_node = tm->findUnitNode();
    if (unit_node == nullptr) {
        if (tm->equals(*target)) {
            return tm;
        }
        failTime++;
    } else {
        for (auto t: generateRandomNode(unit_node->con)) {
            Tm *new_tm = deepcopy(tm);

            if (new_tm->tm_num == UnitTm) {
                new_tm = t->tm;
            } else {
                new_tm->changeUnitNode(new_tm->findUnitNode()->tm, t->tm);
            }

//        if(size<=5)
//        cout<<"Try Push Term: "<<new_tm->out()<<endl;

            Context c = Context();
            if (type_check && !(new_tm->type(c)->contains(target->type(c)) || new_tm->type(c)->ty_num == UnitTy)) {
                continue;
            }
            if (new_tm->size() > size) {
                continue;
            }

//        cout<<"Push Term: "<<new_tm->out()<<", Prob: "<<exp(item->prob + log(t->prob))<<endl;

            b->push(new BeamItem(new_tm, item->prob + log(t->prob)));
        }
    }

    return nullptr;
}

Tm *beamSearch(Beam *b, Tm *target, int size, bool type_check) {
    if (b->size() == 0) {
        return nullptr;
    }

    for (auto item: b->getNeeded(2)) {
        Tm *ret = beamSearchOne(item, b, target, size, type_check);
        if (ret != nullptr) {
            return ret;
        }
    }

    return beamSearch(b, target, size, type_check);
}

Tm *beam_search_wrap(Tm *target, bool type_check) {
    failTime = 0;
    cout << "\nStart Beam Search " << (type_check ? "with types" : "without types") << endl;
    cout << "Target: " << target->out() << ", Size: " << target->size() << endl;
    for (int s = 5; s <= 10; s++) {
//        cout << "Size Limit: " << s << endl;
        Beam *b = new Beam(100);
        b->push(new BeamItem(new UnitTerm(), 0));
        Tm *ret = beamSearch(b, target, s, type_check);
        if (ret != nullptr) {
            cout << "Found: " << ret->out() << endl;
            return ret;
        }
    }
    cout << "Fail to find a solution in range" << endl;
    return nullptr;
}

#endif //PROOF2PROG_ALGORITHM_H

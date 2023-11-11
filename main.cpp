#include "algorithm.h"
#include<ctime>
#include<fstream>
#include<iomanip>

using namespace std;

//\x:Nat. x
void test1() {
    Tm *naive_tm1 = new LambdaTerm("x", new NatType(), new VarTerm("x"));

    beam_search_wrap(naive_tm1, true);
    beam_search_wrap(naive_tm1, false);
}

//\x:Nat. x+x
void test2() {
    Tm *naive_tm2 = new LambdaTerm("x", new NatType(), new PlusTerm(new VarTerm("x"), new VarTerm("x")));

    beam_search_wrap(naive_tm2, true);
    beam_search_wrap(naive_tm2, false);
}

//\x:Nat. if 1<x then 1 else 0
void test3() {
    Tm *naive_tm3 = new LambdaTerm("x", new NatType(),
                                   new IfTerm(new LessTerm(new NatTerm(1), new VarTerm("x")), new NatTerm(1),
                                              new NatTerm(0)));

    beam_search_wrap(naive_tm3, true);
    beam_search_wrap(naive_tm3, false);
}

//\x:Nat. \y:Nat. if x<y then y else x
void test4() {
    Tm *max_tm = new LambdaTerm("x", new NatType(), new LambdaTerm("y", new NatType(), new IfTerm(
            new LessTerm(new VarTerm("x"), new VarTerm("y")), new VarTerm("y"), new VarTerm("x"))));

    beam_search_wrap(max_tm, true);
    beam_search_wrap(max_tm, false);
}

double genRan() {
    return (rand() % 1000009) / (double) 1000009;
}

string generateRandomVar(Context *con) {
    int index = rand() % con->size();
    for (auto &it: *con) {
        if (index == 0) {
            return it.first;
        }
        index--;
    }
    return "err";
}

Tm *generateRandomProg(int size, Context con) {
    vector<Tm *> possibleRets = vector<Tm *>();
    vector<double> possibility = vector<double>();
    if (size <= 0) {
        return new ErrorTerm();
    }
    if (size == 1) {
        double prob = prob_size_1();
        double ran = genRan();
        if (ran < var_prob / prob && !con.empty()) {
            return new VarTerm(generateRandomVar(&con));
        } else if (ran < (var_prob + nat_prob) / prob) {
            return new NatTerm(rand() % 2);
        } else if (ran < (var_prob + nat_prob + true_prob) / prob) {
            return new TrueTerm();
        } else {
            return new FalseTerm();
        }
    }

    if (size >= 2) {
        string var = generateNewVar(&con);

        Context con1 = con;
        con1.insert_or_assign(var, new NatType());
        possibleRets.push_back(new LambdaTerm(var, new NatType(), generateRandomProg(size - 1, con1)));
        possibility.push_back(0.5 * lambda_prob);

        Context con2 = con;
        con2.insert_or_assign(var, new BoolType());
        possibleRets.push_back(new LambdaTerm(var, new BoolType(), generateRandomProg(size - 1, con2)));
        possibility.push_back(0.2 * lambda_prob);

        Context con3 = con;
        con3.insert_or_assign(var, new ArrowType(new NatType(), new NatType()));
        possibleRets.push_back(new LambdaTerm(var, new ArrowType(new NatType(), new NatType()),
                                              generateRandomProg(size - 1, con3)));
        possibility.push_back(0.1 * lambda_prob);

        Context con4 = con;
        con4.insert_or_assign(var, new ArrowType(new BoolType(), new BoolType()));
        possibleRets.push_back(new LambdaTerm(var, new ArrowType(new BoolType(), new BoolType()),
                                              generateRandomProg(size - 1, con4)));
        possibility.push_back(0.1 * lambda_prob);

        Context con5 = con;
        con5.insert_or_assign(var, new ArrowType(new NatType(), new BoolType()));
        possibleRets.push_back(new LambdaTerm(var, new ArrowType(new NatType(), new BoolType()),
                                              generateRandomProg(size - 1, con5)));
        possibility.push_back(0.1 * lambda_prob);

        possibleRets.push_back(new NotTerm(generateRandomProg(size - 1, con)));
        possibility.push_back(not_prob);
    }

    if (size >= 3) {
        for (int i = 1; i <= size - 2; i++) {
            possibleRets.push_back(new AppTerm(generateRandomProg(i, con), generateRandomProg(size - i - 1, con)));
            possibility.push_back(app_prob / (size - 2));

            possibleRets.push_back(new PlusTerm(generateRandomProg(i, con), generateRandomProg(size - i - 1, con)));
            possibility.push_back(plus_prob / (size - 2));

            possibleRets.push_back(new MinusTerm(generateRandomProg(i, con), generateRandomProg(size - i - 1, con)));
            possibility.push_back(minus_prob / (size - 2));

            possibleRets.push_back(new AndTerm(generateRandomProg(i, con), generateRandomProg(size - i - 1, con)));
            possibility.push_back(and_prob / (size - 2));

            possibleRets.push_back(new OrTerm(generateRandomProg(i, con), generateRandomProg(size - i - 1, con)));
            possibility.push_back(or_prob / (size - 2));

            possibleRets.push_back(new LessTerm(generateRandomProg(i, con), generateRandomProg(size - i - 1, con)));
            possibility.push_back(less_prob / (size - 2));

            possibleRets.push_back(new EqualTerm(generateRandomProg(i, con), generateRandomProg(size - i - 1, con)));
            possibility.push_back(equal_prob / (size - 2));
        }
    }

    if (size >= 4) {
        double if_prob3 = 0.2 * (if_prob / (size - 3));
        for (int i = 1; i <= size - 3; i++) {
            possibleRets.push_back(new IfTerm(generateRandomProg(1, con), generateRandomProg(i, con),
                                              generateRandomProg(size - i - 2, con)));
            possibility.push_back(if_prob3);
        }
    }

    if (size >= 5) {
        double if_prob3 = 0.2 * (if_prob / (size - 4));
        for (int i = 1; i <= size - 4; i++) {
            possibleRets.push_back(new IfTerm(generateRandomProg(2, con), generateRandomProg(i, con),
                                              generateRandomProg(size - i - 3, con)));
            possibility.push_back(if_prob3);
        }
    }

    if (size >= 6) {
        double if_prob3 = 0.6 * (if_prob / (size - 5));
        for (int i = 1; i <= size - 5; i++) {
            possibleRets.push_back(new IfTerm(generateRandomProg(3, con), generateRandomProg(i, con),
                                              generateRandomProg(size - i - 4, con)));
            possibility.push_back(if_prob3);
        }
    }

    double sum_prob = 0;
    for (auto &it: possibility) {
        sum_prob += it;
    }

    double ran = genRan();
    int ret = 0;
    for (int i = 0; i < possibility.size(); i++) {
        if (ran < possibility[i] / sum_prob) {
            ret = i;
            break;
        }
        ran -= possibility[i] / sum_prob;
    }
    //free
    for (auto &it: possibleRets) {
        if (it != possibleRets[ret])
            delete (it);
    }
    return possibleRets[ret];
}

void testAll(int size) {
    int successWithType = 0;
    int successWithoutType = 0;
    int failWithType = 0;
    int failWithoutType = 0;
    vector<double> timeWithType = vector<double>();
    vector<double> timeWithoutType = vector<double>();
    for (int i = 0; i < size; i++) {
        cout << "\nTest number: " << i << endl;
        int ranSize = 7;

        Tm *tm = nullptr;
        Context con = Context();
        int fails = 0;
        do {
            fails++;
            if (tm != nullptr)
                delete (tm);
            if (fails % 10 == 0) {
                cout << "fail times: " << fails << endl;
                ranSize--;
            }
            tm = generateRandomProg(ranSize, Context());
        } while (tm->type(con)->equals(new ErrorType()));

        long startTime = clock();
        Tm *res = beam_search_wrap(tm, true);
        long midTime = clock();
        int succ1 = res == nullptr ? 0 : 1;
        successWithType += succ1;
        failWithType += failTime;


        res = beam_search_wrap(tm, false);
        long endTime = clock();
        int succ2 = res == nullptr ? 0 : 1;
        successWithoutType += succ2;
        failWithoutType += failTime;

        if (succ1 == 1 || succ2 == 1) {
            timeWithType.push_back((double) (midTime - startTime) / 1000);
            timeWithoutType.push_back((double) (endTime - midTime) / 1000);
        }
    }

    ofstream fout("output/log.txt");
    fout << successWithType << " " << failWithType << " " << endl <<
         successWithoutType << " " << failWithoutType << endl;
    fout << setiosflags(ios::fixed) << setprecision(2);
    for (auto &it: timeWithType) {
        fout << it << " ";
    }
    fout << endl;
    for (auto &it: timeWithoutType) {
        fout << it << " ";
    }
    fout << endl;
    fout.close();
}

void test_type() {
    Tm *tm = new LambdaTerm("x", new NatType(), new EqualTerm(new NatTerm(1), new NotTerm(new VarTerm("x"))));
    cout << tm->out() << endl;
    cout << tm->type(Context())->out() << endl;
}

void test_unitNode_change() {
    Tm *t1 = new LambdaTerm("x", new NatType(), new PlusTerm(new VarTerm("x"), new UnitTerm()));
    Tm *t2 = new NatTerm(1);
    Tm *t3 = deepcopy(t1);
    cout << (*t1).out() << " " << (*t2).out() << " " << (*t3).out() << endl;
    t3->changeUnitNode(t3->findUnitNode()->tm, t2);
    cout << (*t1).out() << " " << (*t2).out() << " " << (*t3).out() << endl;
}

void test_generate_target() {
    for (int i = 0; i < 20; i++) {
        Tm *tm = generateRandomProg(5, Context());
        cout << tm->out() << tm->type(Context())->out() << tm->type(Context())->equals(new ErrorType()) << endl;
    }
}

int main() {
    srand(time(0));
//    test1();
//    test2();
//    test3();
//    test4();
//    test_unitNode_change();
//    test_type();
    testAll(50);
    return 0;
}
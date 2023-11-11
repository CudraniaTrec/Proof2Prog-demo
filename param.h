//
// Created by Windows on 2023.
//

#ifndef PROOF2PROG_PARAM_H
#define PROOF2PROG_PARAM_H

#include<vector>
#include <string>

using namespace std;

vector<string> alphabet = {"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n",
                           "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"};

double app_prob = 0.5;
double lambda_prob = 3;
double var_prob = 10;
double if_prob = 1;
double nat_prob = 10;
double plus_prob = 0.5;
double minus_prob = 0.5;
double true_prob = 0.5;
double false_prob = 0.5;
double and_prob = 0.5;
double or_prob = 0.5;
double not_prob = 0.5;
double less_prob = 3;
double equal_prob = 3;

double prob_all() {
    return app_prob + lambda_prob + var_prob + if_prob + nat_prob + plus_prob +
           minus_prob + true_prob + false_prob + and_prob + or_prob + not_prob + less_prob + equal_prob;
}

double prob_size_1() {
    return var_prob + nat_prob + true_prob + false_prob;
}

double prob_size_2() {
    return lambda_prob + not_prob;
}

double prob_size_3() {
    return app_prob + plus_prob + minus_prob + and_prob + or_prob + less_prob + equal_prob;
}

double prob_size_4() {
    return if_prob;
}

#endif //PROOF2PROG_PARAM_H

#include "algorithm.h"
#include<fstream>
#include<iomanip>
#include<ctime>

using namespace std;

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

int main() {
    srand(time(0));
    testAll(1);
    return 0;
}
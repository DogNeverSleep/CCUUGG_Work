#include <stdio.h>
#include <algorithm>
#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#define MAXSIZE 100

using namespace std;

int numU = 0;     // 属性个数
char U[MAXSIZE];  // 属性集合
int numF = 0;     // 函数依赖个数
string F[MAXSIZE][2];  // 函数依赖 F[a][b]表示第a个函数依赖的b（0为左 1为右）部

// 计算某一集合的所有子集
vector<string> find_subset(string X) {
    vector<string> subset;
    string s = "";
    s += X[0];
    subset.push_back(s);
    for (int i = 1; i < X.size(); i++) {
        int num = subset.size();
        for (int j = 0; j < num; j++) {
            string s = subset[j];
            s += X[i];
            subset.push_back(s);
        }
        string s = "";
        s += X[i];
        subset.push_back(s);
    }
    sort(subset.begin(), subset.end());
    return subset;
}

// 计算闭包
string find_closure(string X) {
    string Xi = X;  // Xi
    sort(Xi.begin(), Xi.end());
    string Xi_ = "";  // Xi+1
    int k = 0;
    while (Xi_ != Xi && Xi.length() != numU) {
        if (k == 0) {
            Xi_ = X;
        } else {
            // 更新Xi
            Xi = Xi_;
        }
        vector<string> subset_Xi;
        subset_Xi = find_subset(Xi);
        vector<string> B;
        for (int i = 0; i < numF; i++) {
            string V = F[i][0];
            string W = F[i][1];
            // 将函数依赖的左部与Xi的子集逐一匹配
            for (int j = 0; j < subset_Xi.size(); j++) {
                // 如果左部与Xi的子集相同
                if (V == subset_Xi[j]) {
                    B.push_back(W);
                }
            }
        }
        sort(B.begin(), B.end());
        for (int i = 0; i < B.size(); i++) {
            Xi_ += B[i];
        }
        // 去掉重复元素
        sort(Xi_.begin(), Xi_.end());
        auto ite = unique(Xi_.begin(), Xi_.end());
        Xi_.erase(ite, Xi_.end());
        k++;
    }
    return Xi;
}

// 一种更普适性的闭包计算函数 这里设计是为了服务于计算最小依赖集
string get_closure(string X, vector<vector<string>> tmp, int num0) {
    string Xi = X;  // Xi
    sort(Xi.begin(), Xi.end());
    string Xi_ = "";  // Xi+1
    int k = 0;
    while (Xi_ != Xi && Xi.length() != numU) {
        if (k == 0) {
            Xi_ = X;
        } else {
            // 更新Xi
            Xi = Xi_;
        }
        vector<string> subset_Xi;
        subset_Xi = find_subset(Xi);
        vector<string> B;
        for (int i = 0; i < num0; i++) {
            string V = tmp[i][0];
            string W = tmp[i][1];
            // 将函数依赖的左部与Xi的子集逐一匹配
            for (int j = 0; j < subset_Xi.size(); j++) {
                // 如果左部与Xi的子集相同
                if (V == subset_Xi[j]) {
                    B.push_back(W);
                }
            }
        }
        sort(B.begin(), B.end());
        for (int i = 0; i < B.size(); i++) {
            Xi_ += B[i];
        }
        // 去掉重复元素
        sort(Xi_.begin(), Xi_.end());
        auto ite = unique(Xi_.begin(), Xi_.end());
        Xi_.erase(ite, Xi_.end());
        k++;
    }
    return Xi;
}

// 计算最小依赖集
void minimal_set_of_dependencies() {
    int numF_0 = 0;  // 右部化为单一属性后的函数依赖个数
    string F_0[MAXSIZE][2];  // 求最小依赖集时 右部化为单一属性后的函数依赖
    // 将函数依赖右部化为单一属性
    for (int i = 0; i < numF; i++) {
        for (int j = 0; j < F[i][1].length(); j++) {
            bool skip=false;
            for (int k=0;k<numF_0;k++){
                string c_0="";
                c_0+=F[i][1][j];
                if (F_0[k][0]==F[i][0]&&F_0[k][1]==c_0){
                    skip=true;
                }
            }
            if (skip==true){
                continue;
            }
            F_0[numF_0][0] = F[i][0];
            F_0[numF_0][1] = F[i][1][j];
            numF_0++;
        }
    }
    int use[numF_0];  // 标记第i个函数依赖是否必要
    for (int i = 0; i < numF_0; i++) {
        vector<vector<string>> temp(MAXSIZE, vector<string>(2));
        int q = 0;
        for (int j = 0; j < numF_0; j++) {
            if (i != j&&use[j]!=-9) {
                temp[q][0] = F_0[j][0];
                temp[q][1] = F_0[j][1];
                q++;
            }
        }
        string c = "";
        c += F_0[i][0];
        // X->A X关于F_0的闭包
        string res = get_closure(c, temp, numF_0-1);
        vector<string> subset_0 = find_subset(res);
        bool flag = false;
        for (int p = 0; p < subset_0.size(); p++) {
            if (F_0[i][1] == subset_0[p]) {
                flag = true;
                break;
            }
        }
        // 去掉此函数依赖
        if (flag == true) {
            use[i] = -9;
            // 保留此函数依赖
        } else {
            use[i] = 99;
        }
    }
    vector<vector<string>> F_1(MAXSIZE, vector<string>(2));  // 去掉不必要的函数依赖后的依赖集
    int numF_1 = 0;
    for (int i = 0; i < numF_0; i++) {
        if (use[i] == 99) {
            F_1[numF_1][0] = F_0[i][0];
            F_1[numF_1][1] = F_0[i][1];
            numF_1++;
        }
    }
    for (int i = 0; i < numF_1; i++) {
        if (F_1[i][0].length() > 1) {
            for (int j = 0; j < F_1[i][0].length(); j++) {
                string X_B = "";  // X-Bi
                for (int k = 0; k < F_1[i][0].length(); k++) {
                    if (k != j) {
                        X_B += F_1[i][0][k];
                    }
                }
                string clo = get_closure(X_B, F_1, numF_1);
                vector<string> subset_1 = find_subset(clo);
                bool flag_0 = false;
                for (int w = 0; w < subset_1.size(); w++) {
                    if (F_1[i][1] == subset_1[w]) {
                        flag_0 = true;
                        break;
                    }
                }
                // 用X-Bi来取代X
                if (flag_0 == true) {
                    F_1[i][0] = X_B;
                    j=-1;
                }
            }
        }
    }
    int baoliu[numF_1];
    for (int i = 0; i < numF_1; i++) {
        for (int j = i + 1; j < numF_1; j++) {
            if (F_1[i][0] == F_1[j][0] && F_1[i][1] == F_1[j][1]) {
                baoliu[j] = 99;
            }
        }
    }
    for (int i = 0; i < numF_1; i++) {
        if (baoliu[i] != 99) {
            cout << F_1[i][0] << "->" << F_1[i][1] << endl;
        }
    }
}

int main() {
    cout << "----------闭包与最小依赖集的计算----------" << endl;
    cout << "请输入属性个数：";
    cin >> numU;
    for (int i = 0; i < numU; i++) {
        cout << "请输入第" << i + 1 << "个属性：";
        cin >> U[i];
    }
    cout << "--------------------------------" << endl;
    cout << "请输入函数依赖的个数：";
    cin >> numF;
    for (int i = 0; i < numF; i++) {
        cout << "请输入第" << i + 1 << "个函数依赖的左部：";
        string s1;
        cin >> s1;
        sort(s1.begin(), s1.end());
        F[i][0] = s1;
        cout << "请输入第" << i + 1 << "个函数依赖的右部：";
        string s2;
        cin >> s2;
        sort(s2.begin(), s2.end());
        F[i][1] = s2;
    }
    cout << "--------------------------------" << endl;
    while (true) {
        cout << "1：计算闭包  2：计算最小依赖集   0：退出" << endl
             << "请输入要使用的功能：";
        int choice;
        cin >> choice;
        cout << "--------------------------------" << endl;
        if (choice == 1) {
            cout << "请输入所要计算闭包的属性集：";
            string X;
            cin >> X;
            string res;
            res = find_closure(X);
            cout << "属性集" << X << "的闭包为：" << res << endl;
            cout << "--------------------------------" << endl;
        } else if (choice == 2) {
            cout << "最小依赖集为：" << endl;
            minimal_set_of_dependencies();
            cout << "--------------------------------" << endl;
        } else {
            break;
        }
    }
    system("pause");
    return 0;
}
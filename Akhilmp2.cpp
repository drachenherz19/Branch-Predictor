#include <iomanip>
#include <string>
#include <cmath>
#include <vector>
#include <algorithm>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <chrono>
#include <armadillo>

using namespace std;
string::size_type sz;

//List of variables that are used in this program:
int counter = 0;
char line[128];
char branch[128];
char taken[1];
int total_bits = 0;
int total_count = 0;
int n_bit;
int bit_map = 0;
int loop_counter = 0;
int pred = 0;
int dock;
int catch1;
int m1;
int m2;
int k;
int n;
int mispred = 0;
int table_bounds;

string g_add;

vector<string> taken_history;
vector<string> branch_history;

vector<int> g_table;
vector<int> b_table;
vector<int> h_table;
vector<int> global_history;
vector<int> b_history;

typedef struct {
    char *branch;
    char *taken;
}line_feed;

void smith_pred() {
    // Here I initialize the inputs before running
    double n_bit_size = pow(2, static_cast<double>(n_bit));
    int pred_flag = 0; // Branch bit_map
    bit_map = static_cast<int>(pow(2, n_bit - 1));

    // Here we run and decipher based on the read-in
    for (unsigned long i = 0; i < taken_history.size(); i++) {
        // Extract "taken" status from history
        char taken = taken_history[i][0];

        // Updating the prediction flag based on bit_map
        pred_flag = (bit_map >= (n_bit_size / 2)) ? 1 : 0;

        
        if (taken == 't') {
            if (pred_flag == 1) {
                pred++;
                bit_map = std::min(bit_map + 1, static_cast<int>(n_bit_size - 1));
            } else {
                mispred++;
                bit_map = std::min(bit_map + 1, static_cast<int>(n_bit_size - 1));
            }
        } else if (taken == 'n') {
            if (pred_flag == 0) {
                pred++;
                bit_map = std::max(bit_map - 1, 0);
            } else {
                mispred++;
                bit_map = std::max(bit_map - 1, 0);
            }
        }
    }
}
void g_share() {
    
    int table_size = pow(2, m1);
    for (int i = 0; i < table_size; i++) {
        g_table.push_back(4);
    }

    
    string temp;
    for (int i = 0; i < n; i++) {
        temp.push_back('0');
        global_history.push_back(0);
    }

    for (unsigned long i = 0; i < taken_history.size(); i++) {
        
        long address = stol(branch_history[i], &sz, 16) / 4;
        long n_bits_end = address % static_cast<long>(pow(2, n));
        long n_bits_begin = address / static_cast<long>(pow(2, n));
        long n_dec = stol(temp, nullptr, 2);
        long xor_bit = n_bits_end ^ n_dec;
        long address_conv = n_bits_begin * static_cast<long>(pow(2, n)) + xor_bit;
        long index = address_conv % static_cast<long>(pow(2, m1));

        
        char taken = taken_history[i][0];

        
        int pred_flag = (g_table[index] >= 4) ? 1 : 0;

        
        if (g_table[index] >= 4) {
            pred_flag = 1;
        } else {
            pred_flag = 0;
        }

        
        if (taken == 't') {
            if (pred_flag == 1) {
                pred++;
                g_table[index] = std::min(g_table[index] + 1, 7);
            } else {
                mispred++;
                g_table[index] = std::min(g_table[index] + 1, 7);
            }
            global_history.insert(global_history.begin(), 1);
        } else if (taken == 'n') {
            if (pred_flag == 0) {
                pred++;
                g_table[index] = std::max(g_table[index] - 1, 0);
            } else {
                mispred++;
                g_table[index] = std::max(g_table[index] - 1, 0);
            }
            global_history.insert(global_history.begin(), 0);
        }

        
        global_history.pop_back();

        
        temp.clear();
        for (int i = 0; i < global_history.size(); i++) {
            temp.push_back((global_history[i] == 0) ? '0' : '1');
        }
    }
}


void bimodal() {
    // Here we initialize the Bimodal Table:
    int table_size = pow(2, m2);
    for (int i = 0; i < table_size; i++) {
        g_table.push_back(4);
    }

    for (unsigned long i = 0; i < taken_history.size(); i++) {
        
        char taken = taken_history[i][0];

        
        long address = stol(branch_history[i], &sz, 16) / 4;
        long index = address % static_cast<long>(pow(2, m2));

        // The taken/not taken history is determined by this prediction flag:
        int pred_flag = (g_table[index] >= 4) ? 1 : 0;

        
        if (g_table[index] >= 4) {
            pred_flag = 1;
        } else {
            pred_flag = 0;
        }

        // We update the G-Table here:
        if (taken == 't') {
            if (pred_flag == 1) {
                pred++;
                g_table[index] = std::min(g_table[index] + 1, 7);
            } else {
                mispred++;
                g_table[index] = std::min(g_table[index] + 1, 7);
            }
        } else if (taken == 'n') {
            if (pred_flag == 0) {
                pred++;
                g_table[index] = std::max(g_table[index] - 1, 0);
            } else {
                mispred++;
                g_table[index] = std::max(g_table[index] - 1, 0);
            }
        }
    }
}


void h_initialize(){
    //Here we initialize Bimodal and Gshare for Hybrid
    int table_size_g = pow(2,m1);
    for(int i = 0; i < table_size_g; i++){
        g_table.push_back(4);
    }

    for(int i =0; i < n; i++){
        g_add.push_back('0');
        global_history.push_back(0);
    }

    
    int table_size_b = pow(2,m2);
    for(int i = 0; i < table_size_b; i++){
        b_table.push_back(4);
    }
}

long g_address(int i) {
    // Extraction of the G-Share address components:
    long address = stol(branch_history[i], &sz, 16) / 4;
    long n_bits_end = address % static_cast<long>(pow(2, n));
    long n_bits_begin = address / static_cast<long>(pow(2, n));
    long n_dec = stol(g_add, nullptr, 2);
    long xor_bit = n_bits_end ^ n_dec;

    
    long address_conv = n_bits_begin * static_cast<long>(pow(2, n)) + xor_bit;

    
    long index = address_conv % static_cast<long>(pow(2, m1));

    return index;
}


long b_address(int i) {
    
    char taken = taken_history[i][0];

    // Here the calculation of the bimodal address is done:
    long address = stol(branch_history[i], &sz, 16) / 4;
    long index = address % static_cast<long>(pow(2, m2));

    return index;
}


bool g_eval(int i, long index) {
    // Extraction of the "taken" status is done here:
    char taken = taken_history[i][0];

    
    int g_pred_strong = (g_table[index] >= 4) ? 1 : 0;

    
    bool guess;

    
    if (taken == 't') {
        if (g_pred_strong) {
            guess = true;
            g_table[index] = std::min(g_table[index] + 1, 7);
        } else {
            guess = false;
            g_table[index] = std::min(g_table[index] + 1, 7);
        }
        global_history.insert(global_history.begin(), 1);
    } else if (taken == 'n') {
        if (!g_pred_strong) {
            guess = true;
            g_table[index] = std::max(g_table[index] - 1, 0);
        } else {
            guess = false;
            g_table[index] = std::max(g_table[index] - 1, 0);
        }
        global_history.insert(global_history.begin(), 0);
    }

    
    global_history.pop_back();

    
    g_add.clear();
    for (int i = 0; i < global_history.size(); i++) {
        g_add.push_back((global_history[i] == 0) ? '0' : '1');
    }

    return guess;
}


bool b_eval(int i, long index) {
    
    int b_pred_strong = (b_table[index] >= 4) ? 1 : 0;

    
    char taken = taken_history[i][0];

    
    bool guess;
    if (taken == 't') {
        guess = (b_pred_strong) ? true : false;
    } else if (taken == 'n') {
        guess = (!b_pred_strong) ? true : false;
    }

    return guess;
}


void g_update_table(int i, long index) {
    
    int g_pred_strong = (g_table[index] >= 4) ? 1 : 0;

    
    char taken = taken_history[i][0];

    
    if (taken == 't') {
        if (g_pred_strong) {
            pred++;
            g_table[index] = std::min(g_table[index] + 1, 7);
        } else {
            g_table[index] = std::min(g_table[index] + 1, 7);
        }
    } else if (taken == 'n') {
        if (!g_pred_strong) {
            pred++;
            g_table[index] = std::max(g_table[index] - 1, 0);
        } else {
            g_table[index] = std::max(g_table[index] - 1, 0);
        }
    }
    
}


void b_update_table(int i, long index) {
    
    int g_pred_strong = (g_table[index] >= 4) ? 1 : 0;

    
    char taken = taken_history[i][0];

    // B-Table updation depending on the "taken" status and G-Table:
    if (taken == 't') {
        if (g_pred_strong) {
            b_table[index] = std::min(b_table[index] + 1, 7);
            pred++;
        } else {
            b_table[index] = std::min(b_table[index] + 1, 7);
        }
    } else if (taken == 'n') {
        if (!g_pred_strong) {
            pred++;
            b_table[index] = std::max(b_table[index] - 1, 0);
        } else {
            b_table[index] = std::max(b_table[index] - 1, 0);
        }
    }
    
}


void hybrid() {
    h_initialize();
    bool g_pred, b_pred;

    // Initialization of the H-Table is done here:
    int h_table_size = pow(2, k);
    for (int i = 0; i < h_table_size; i++) {
        h_table.push_back(1);
    }

    for (unsigned long i = 0; i < taken_history.size(); i++) {
        
        long g_index = g_address(i);
        long b_index = b_address(i);
        long h_index = stol(branch_history[i], &sz, 16) / 4 % long(pow(2, k));

        
        g_pred = g_eval(i, g_index);
        b_pred = b_eval(i, b_index);

        
        if (h_table[h_index] >= 2) {
            g_update_table(i, g_index);
            if (!g_pred) {
                mispred++;
            }
        }

        
        if (h_table[h_index] < 2) {
            b_update_table(i, b_index);
            if (!b_pred) {
                mispred++;
            }
        }

        
        if (g_pred && !b_pred) {
            h_table[h_index] = std::min(h_table[h_index] + 1, 3);
        }
        if (b_pred && !g_pred) {
            h_table[h_index] = std::max(h_table[h_index] - 1, 0);
        }
    }
}


void read_file(const char *file_in) {
    FILE *ifp;
    ifp = fopen(file_in, "r");
    line_feed *lineFeed;

    
    while (fgets(line, sizeof(line), ifp) != NULL) {
        int num_matches = sscanf(line, "%s %s", branch, taken);
        counter++;

        
        if (num_matches != 2) {

        } else {
            
            taken_history.push_back(taken);
            branch_history.push_back(branch);
        }
    }

    
    for (int i = 0; i < branch_history.size(); i++) {
        
    }

    
}



int main(int argc, char* argv[]) {

    string operation = argv[1];

    if(operation == "smith"){
        string b_in  = argv[2];
        const char *file_in = argv[3];
        n_bit = stoi(b_in, &sz);
        read_file(file_in);
        smith_pred();

        cout<<"COMMAND"<<endl;
        cout<<"./sim smith "<<b_in <<" "<< argv[3]<<endl;
        cout<<"OUTPUT"<<endl;
        cout<<"This is the number of predictions:\t" <<counter <<endl;
        cout<<"This is the number of mispredictions:\t"<< mispred<<endl;
        float miss_rate = float(mispred)/float(counter) * 10000;
        cout<<"The misprediction rate is:\t"<< fixed<<setprecision(2)<< round(miss_rate)/100<< "%"<<endl;
        cout<<"Final counter content is as follows:\t"<< bit_map<<endl;
    }

    if(operation == "gshare") {
        string table_bounds_in = argv[2];
        m1 = stoi(table_bounds_in, &sz);
        string b_in  = argv[3];
        n = stoi(b_in, &sz);
        const char *file_in = argv[4];
        read_file(file_in);
        g_share();

        cout<<"COMMAND"<<endl;
        cout<<"./sim gshare "<<m1 <<" " << n << " "<< argv[4]<<endl;
        cout<<"OUTPUT"<<endl;
        cout<<"This is the number of predictions:\t" <<counter <<endl;
        cout<<"This is the number of mispredictions:\t"<< mispred<<endl;
        float miss_rate = float(mispred)/float(counter) * 10000;
        cout<<"The misprediction rate is:\t"<< fixed<<setprecision(2)<< round(miss_rate)/100<< "%"<<endl;
        cout<<"The final gshare contents are as follows:"<<endl;
        for(int i = 0; i <g_table.size(); i++){
            cout<<i<<'\t'<<g_table[i]<<endl;
        }
    }

    if(operation == "bimodal") {
        string table_bounds_in = argv[2];
        m2 = stoi(table_bounds_in, &sz);
        const char *file_in = argv[3];
        read_file(file_in);
        bimodal();

        cout<<"COMMAND"<<endl;
        cout<<"./sim bimodal "<<m2 <<" "<< argv[3]<<endl;
        cout<<"OUTPUT"<<endl;
        cout<<"This is the number of predictions:\t" <<counter <<endl;
        cout<<"This is the number of mispredictions:\t"<< mispred<<endl;
        float miss_rate = float(mispred)/float(counter) * 10000;
        cout<<"The misprediction rate is:\t"<< fixed<<setprecision(2)<< round(miss_rate)/100<< "%"<<endl;
        cout<<"The final bimodal contents are as follows:"<<endl;
        for(int i = 0; i <g_table.size(); i++){
            cout<<i<<'\t'<<g_table[i]<<endl;
        }
    }

    if(operation == "hybrid") {
        string k_in = argv[2];
        k = stoi(k_in, &sz);
        string table_bounds_in = argv[3];
        m1 = stoi(table_bounds_in, &sz);
        string b_in  = argv[4];
        n = stoi(b_in, &sz);
        string m2_in = argv[5];
        m2 = stoi(m2_in, &sz);
        const char *file_in = argv[6];
        read_file(file_in);
        hybrid();

        cout<<"COMMAND"<<endl;
        cout<<"./sim hybrid "<<k<<" "<<m1 << " "<< n<< " "<<m2 << " "<< argv[6]<<endl;
        cout<<"OUTPUT"<<endl;
        cout<<"This is the number of predictions:\t" <<counter <<endl;
        cout<<"This is the number of mispredictions:\t"<< mispred<<endl;
        float miss_rate = float(mispred)/float(counter) * 10000;
        cout<<"The misprediction rate is:\t"<< round(miss_rate)/100<< "%"<<endl;

        cout<<"The final chooser contents are:"<<endl;
        for(int i = 0; i <h_table.size(); i++){
            cout<<i<<'\t'<<h_table[i]<<endl;
        }
        cout<<"The final gshare contents are:"<<endl;
        for(int i = 0; i <g_table.size(); i++){
            cout<<i<<'\t'<<g_table[i]<<endl;
         }
        cout<<"The final bimodal contents are:"<<endl;
        for(int i = 0; i <b_table.size(); i++){
            cout<<i<<'\t'<<b_table[i]<<endl;
        }
    }

    return 0;
}

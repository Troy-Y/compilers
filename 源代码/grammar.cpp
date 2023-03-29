#include <iostream>
#include <fstream>
#include <cstring>
#include <stack>
using namespace std;

bool isV[200];
int sizeItem[200];
bool first[200][200];
char grammar[200][200];
int lenGrammar[200];
char Vt[200];
int lenVt = 0;
char Vn[200];
int lenVn = 0;
stack<int> state;
stack<char> sign;

ifstream grammarFile;
ifstream inputFile;
ofstream itemsFile;
ofstream firstsetFile;
ofstream actionFile;
ofstream procedureFile;

struct Item{
    int num;
    int now;
    char search;
};

struct Trans{ //转换表  项目集转换
	int begin;
	int next;
	char ch;
};

struct Action{
	char ch;
	int nextState;
};

Item item[200][200];
Trans trans[200];
Action actionTable[200][200];
int lenTrans = 0;
int lenItem[200];
int count = 0;
int size = 0;
char buffer[200];
int lenActTable[200];

void getGrammar(){	// 读取二型文法
    grammarFile.open("data/GrammarFormula.txt");
    string line;
    int lineNo = 1;
    grammar[0][0] = 'S';
    lenGrammar[0] = 2;
    while (getline(grammarFile,line)){	// 按行输入
        // cout << line<<endl;
        int j = 0;
        for (int i = 0; line[i];i++){
            if(line[i]=='-'&&line[i+1]=='>'){
                i++;
                continue;
            }
            else if(line[i]){
                grammar[lineNo][j++] = line[i];
                isV[line[i]] = true;
            }
        }
        lenGrammar[lineNo++] = j;
        // cout << grammar[lineNo-1] <<' '<<lenGrammar[lineNo]<< endl;
    }
    grammar[0][1]=grammar[1][0];	// S->P
    // 大写字母为Vn 其他为Vt
    for (int i = 0; i < 64;i++)
        if(isV[i])
            Vt[lenVt++] = i;
    for (int i = 65; i < 91;i++)
        if(isV[i])
            Vn[lenVn++] = i;
    for (int i = 91;i<128; i++)
        if(isV[i])
            Vt[lenVt++] = i;
}

void showGrammar(){	// 输出二型文法
    for (int i = 0; grammar[i][0];i++)
        cout << grammar[i] <<' '<<lenGrammar[i]<< endl;
}

bool isInVn(char a){	// 是否是非终结符
    for (int i = 0; i < lenVn; ++i)
		if (Vn[i] == a)
			return true;
	return false;
}

void ouputFirst(){	// 输出FIRST集
    for (int i = 0; i < 26; i++){
		char ch = char(i + 'A');
		bool flag = true;
        if (isInVn(ch)){
			firstsetFile << "FIRST(" << ch << ")={";
			for (int j = 0; j < 128; j++){
				if (first[i][j] == true&&flag){
					firstsetFile << char(j);
					flag = !flag;
				}
				else if(first[i][j] == true&&!flag){
					firstsetFile << ',' << char(j);
				}
			}
			firstsetFile << "}" << endl;
		}
	}
}

void getFirst(){	// 计算FIRST集
    bool finish = true;
    int t, k;
	bool isEmpty;
    while (finish){
		finish = false;
        for (int i = 1; i<=31; i++){
			t = 1;
			isEmpty = true;
			while (isEmpty && t < lenGrammar[i]){
				isEmpty = false;
				if (grammar[i][t] >= 'A' && grammar[i][t] <= 'Z'){
					for (k = 0; k <= 63; ++k)
						if (first[grammar[i][t] - 'A'][k] == true && !first[grammar[i][0] - 'A'][k]){
							first[grammar[i][0] - 'A'][k] = true;
							finish = true;
						}
					if (first[grammar[i][t] - 'A'][64] == true){ //用@表示 空
						isEmpty = true;
						++t;
					}
					for (k = 91; k < 128; ++k)
						if (first[grammar[i][t] - 'A'][k] == true && first[grammar[i][0] - 'A'][k] == false){
							finish = true;
							first[grammar[i][0] - 'A'][k] = true;
						}
				}
				else if (first[grammar[i][0] - 'A'][grammar[i][t]] == false){
					finish = true;
					first[grammar[i][0] - 'A'][grammar[i][t]] = true;
				}
			}
			if (lenGrammar[i] == t)
				first[grammar[i][0] - 'A'][26] = true;
		}
	}
    ouputFirst();
}

void getSearch(Item temp){	// 计算向前搜索符
    size = 0;
	bool flag = true;
	int nownow = temp.now;
	int i;
	while (flag == true){
		flag = false;
		if (nownow + 1 >= lenGrammar[temp.num]){
			buffer[size++] = temp.search;
			return;
		}
		else if (grammar[temp.num][nownow + 1] < 'A' || grammar[temp.num][nownow + 1] > 'Z'){
			buffer[size++] = grammar[temp.num][nownow + 1];
			return;
		}
		else if (grammar[temp.num][nownow + 1] >= 'A' && grammar[temp.num][nownow + 1] <= 'Z'){
			for (i = 0; i < 64; i++){
				if (first[grammar[temp.num][nownow + 1] - 'A'][i] == true)
					buffer[size++] = i;
			}
			for (i = 91; i < 128; i++){
				if (first[grammar[temp.num][nownow + 1] - 'A'][i] == true){
					buffer[size++] = i;
				}
			}
			if (first[grammar[temp.num][nownow + 1] - 'A'][64] == true){
				nownow++;
				flag = true;
			}
		}
	}
	// cout << buffer<<endl;
}

bool isIn(Item temp,int t){	// 是否在已有项目集中
    int i;
	for (i = 0; i < lenItem[t]; i++)
		if (item[t][i].num == temp.num && item[t][i].now == temp.now && item[t][i].search == temp.search)
			return true;
	return false;
}

void getClosure(int t){ // 求闭包
    Item temp;
	int i, j, k;
	for (i = 0; i < lenItem[t]; i++){
		if (grammar[item[t][i].num][item[t][i].now] >= 'A' && grammar[item[t][i].num][item[t][i].now] <= 'Z'){
			for (j = 0; j < 300; j++){
				size = 0;
				if (grammar[j][0] == grammar[item[t][i].num][item[t][i].now]){
					getSearch(item[t][i]);
					for (k = 0; k < size; k++){
						temp.num = j;
						temp.now = 1;
						temp.search = buffer[k];
						if (isIn(temp, t) == false){
							item[t][lenItem[t]++] = temp;
						}
					}
				}
			}
		}
	}
}

int isInItem(){	// 查看项目集是否重复
    int i;
	int sum = 0;
	int j;
	int k;
	for (i = 0; i < count; i++){
		sum = 0; //记录有多少是匹配的
		if (lenItem[count] == lenItem[i])
			for (j = 0; j < lenItem[count]; j++)
				for (k = 0; k < lenItem[i]; k++)
					if (item[i][k].num == item[count][j].num && item[i][k].now == item[count][j].now && item[i][k].search == item[count][j].search){
						++sum;
						break;
					}
		if (sum == lenItem[count])
			return i;
	}
    return 0;
}

void getItemSet(){	// 输出项目集
    item[0][0].num = 0;
	item[0][0].now = 1;
	item[0][0].search = '#';
	lenItem[0] = 1;
	getClosure(0);
	Item buf[50];
	int bufSize = 0;
	Item tp;
	int i, j, k;
	int nextState;
	itemsFile << "I0:" << endl;
	for (i = 0; i < lenItem[0]; i++)
		itemsFile << grammar[item[0][i].num][0] << "->" << grammar[item[0][i].num] + 1 << " , " << item[0][i].now << " , " << item[0][i].search << endl;
	itemsFile << "--------------------------------------------------" << endl;
	int index;
	int p;
	int t;
	for (index = 0; index < count + 1; index++){
		for (j = 0; j < lenVt; j++){
			bufSize = 0;
			for (p = 0; p < lenItem[index]; p++){
				if (item[index][p].now < lenGrammar[item[index][p].num] && grammar[item[index][p].num][item[index][p].now] == Vt[j]){
					tp.num = item[index][p].num;
					tp.search = item[index][p].search;
					tp.now = item[index][p].now + 1;
					buf[bufSize++] = tp;
				}
			}
			if (bufSize != 0){
				count++;
				for (t = 0; t < bufSize; t++)
					item[count][lenItem[count]++] = buf[t];
				getClosure(count);
				nextState = isInItem();
				if (nextState != 0){		 
					lenItem[count--] = 0;
					trans[lenTrans].begin = index;
					trans[lenTrans].next = nextState;
					trans[lenTrans++].ch = Vt[j];
				}
				else{
					itemsFile << "I" << count << ":" << endl;
					for (i = 0; i < lenItem[count]; i++)
						itemsFile << grammar[item[count][i].num][0] << "->" << grammar[item[count][i].num] + 1 << " , " << item[count][i].now << " , " << item[count][i].search << endl;
					itemsFile << "--------------------------------------------------" << endl;
					trans[lenTrans].begin = index;
					trans[lenTrans].next = count;
					trans[lenTrans++].ch = Vt[j];
				}
			}
		}
		for (j = 0; j < lenVn; j++){
			bufSize = 0;
			for (p = 0; p < lenItem[index]; p++){
				if (item[index][p].now < lenGrammar[item[index][p].num] && grammar[item[index][p].num][item[index][p].now] == Vn[j]){
					tp.num = item[index][p].num;
					tp.search = item[index][p].search;
					tp.now = item[index][p].now + 1;
					buf[bufSize++] = tp;
				}
			}
			if (bufSize != 0){
				count++;
				for (t = 0; t < bufSize; t++)
					item[count][lenItem[count]++] = buf[t];
				getClosure(count);
				nextState = isInItem();
				if (nextState != 0){
					lenItem[count--] = 0;
					trans[lenTrans].begin = index;
					trans[lenTrans].next = nextState;
					trans[lenTrans++].ch = Vn[j];
				}
				else{
					itemsFile << "I" << count << ":" << endl;
					for (i = 0; i < lenItem[count]; i++)
						itemsFile << grammar[item[count][i].num][0] << "->" << grammar[item[count][i].num] + 1 << " , " << item[count][i].now << " , " << item[count][i].search << endl;
					itemsFile << "--------------------------------------------------" << endl;
					trans[lenTrans].begin = index;
					trans[lenTrans].next = count;
					trans[lenTrans++].ch = Vn[j];
				}
			}
		}
	}
}

void getAction(){	// 获取ACTION表
    int i, j;
	int t1, t2, t;
	char tp;
	for (i = 0; i < 300; i++)
		lenActTable[i] = 0;
	for (i = 0; i <= count; i++)
		for (j = 0; j < lenItem[i]; j++)
			if (item[i][j].now == lenGrammar[item[i][j].num] || (item[i][j].now == 1 && lenGrammar[item[i][j].num] == 2 && grammar[item[i][j].num][1] == '@')){
				actionTable[i][lenActTable[i]].ch = item[i][j].search;
				actionTable[i][lenActTable[i]++].nextState = item[i][j].num * (-1);
			}
	for (i = 0; i < lenTrans; i++){
		t1 = trans[i].begin;
		t2 = trans[i].next;
		tp = trans[i].ch;
		actionTable[t1][lenActTable[t1]].ch = tp;
		actionTable[t1][lenActTable[t1]++].nextState = t2;
	}
	for (i = 0; i <= count; i++){
		for (j = 0; j < lenActTable[i] ; j++){
			tp = actionTable[i][j].ch;
			t = actionTable[i][j].nextState;
			actionFile << "[" << i << "," << tp << "," << t << "]" << endl;
		}
	}
}

void writeStack(int x){	// 使用栈处理
    stack<int> a;
	stack<char> c;
	if (x == 1){ // 状态	
		while (state.empty() == false){
			a.push(state.top());
			state.pop();
		}
		while (a.empty() == false){
			procedureFile << a.top() << ',';
			state.push(a.top());
			a.pop();
		}
	}
	if (x == 2){ // 符号
		while (sign.empty() == false){
			c.push(sign.top());
			sign.pop();
		}
		while (c.empty() == false){
			procedureFile << c.top() << ',';
			sign.push(c.top());
			c.pop();
		}
	}
}

void getResult(){	// 计算结果和分析过程
    size = 0;
	string s;
	getline(inputFile, s);
	for (int i = 0; s[i];i++)
		buffer[i] = s[i];
	int workState = 0;
	int indexBuffer = 0;
	bool err = false;
	bool done = false;
	char nowIn;
	nowIn = buffer[0];
	state.push(0);
	sign.push('#');
	procedureFile << "状态栈                 符号栈                  输入串               ACTION                  GOTO" << endl;
	int i, j, k, m;
	int tp, len;
	int aa;
	while (done == false && err == false){
		workState = state.top();
		writeStack(1);
		procedureFile << "               ";
		writeStack(2);
		procedureFile << "               ";
		for (i = indexBuffer; i < size; i++)
			procedureFile << buffer[i];
		procedureFile << "              ";
		err = true;
		for (i = 0; i < lenActTable[workState]; i++)
			if (actionTable[workState][i].ch == nowIn){
				err = false;
				if (actionTable[workState][i].nextState == 0){
					procedureFile << "ACC" << endl;
					cout << "YES" << endl;
					done = true;
					break;
				}
				else if (actionTable[workState][i].nextState > 0){ // 移进
					procedureFile << 'S' << actionTable[workState][i].nextState << endl;

					state.push(actionTable[workState][i].nextState);
					sign.push(actionTable[workState][i].ch);
					++indexBuffer;
					nowIn = buffer[indexBuffer];
					break;
				}
				else if (actionTable[workState][i].nextState < 0){
					tp = actionTable[workState][i].nextState * (-1);
					procedureFile << 'r' << tp << "              ";
					len = lenGrammar[tp] - 1;
					if (grammar[tp][1] == '@')
						--len;
					for (k = 0; k < len; k++){
						state.pop();
						sign.pop();
					}
					sign.push(grammar[tp][0]);
					aa = state.top();
					for (m = 0; m < lenActTable[aa]; m++)
						if (actionTable[aa][m].ch == grammar[tp][0]){
							state.push(actionTable[aa][m].nextState);
							procedureFile << actionTable[aa][m].nextState << endl;
						}
					break;
				}
			}
	}
	if (!done){
		cout << "NO" << endl;
		cout << "出错原因可能是未找到：";
		for (i = 0; i < lenActTable[workState]; i++)
			cout << actionTable[workState][i].ch << " ";
		cout << endl;
	}
}

int main(){
    // system("cls");

	// 初始化集合
    for (int i = 0; i < 300;i++)
        isV[i] = false;
    for (int i = 0; i < 300;i++)
        sizeItem[i] = 0;
    for (int i = 0; i < 300;i++)
        for (int j = 0; j < 300;j++)
            first[i][j] = false;

    inputFile.open("data/LexicalOutput.txt");
    itemsFile.open("data/ItemSet.txt");
    firstsetFile.open("data/FirstSet.txt");
	actionFile.open("data/ActionTable.txt");
	procedureFile.open("data/AnalyzeProcess.txt");

    getGrammar();
    // showGrammar();
    getFirst();
    getItemSet();
    getAction();
    getResult();

	return 0;
}
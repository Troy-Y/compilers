#include <iostream>
#include <fstream>
#include <stack>
#include <cstring>
using namespace std;

FILE *file;
ofstream output;

struct formula{
    char l;
    char r1;
    char r2;
}fml[100];
int fmlNo = 0;

struct NFA{
	char set[100];
	int len=0;
};
NFA Move[100][100];
NFA newSet[100];

int lenState = 0;
int lenFinal = 0;
int lenAlpha = 0;
int numNewSet = 0;
int dfa[200][200];
bool isFinalState[200];

char start;
char state[50];
char alpha[50];
char final[50];

const char keyword[20][10]={"char","double","else","float","for","if","int",
"include","main","return","while","iostream"};
const char delimiter[20]={',','(',')','{','}',';','<','>','#'}; //界符
const char moOperator[10]={'+','-','*','/','^','='};   
const char biOperator[10][3]={"++","--","&&","||","<=","!=","==",">="}; 


char func(char str[]){        //映射到一个字符来表示
	if(strcmp(str,keyword[0])==0)   // char
		return 'c';
	if(strcmp(str,keyword[1])==0)	// double
		return 'd';
	if(strcmp(str,keyword[2])==0)	// else
		return 'e';
	if(strcmp(str,keyword[3])==0)	// float
		return 'l';
	if(strcmp(str,keyword[4])==0)	// for
		return 'f';
	if(strcmp(str,keyword[5])==0)	// if
		return 'i';
	if(strcmp(str,keyword[6])==0)  // int
		return 'n';
	if(strcmp(str,keyword[7])==0)	// include
		return 'z';
	if(strcmp(str,keyword[8])==0)	// main
		return 'm';
	if(strcmp(str,keyword[9])==0)	// return
		return 'r';
	if(strcmp(str,keyword[10])==0)	// while
		return 'w';
	if(strcmp(str,keyword[11])==0)	// iostream
		return 'k';
	return ' ';
}

bool isState(char a){
    for (int i = 0; i < lenState;i++)
        if(a==state[i])
            return true;
    return false;
}

bool isAlpha(char a){
    for (int i = 0; i < lenAlpha;i++)
        if(a==alpha[i])
            return true;
    return false;
}

bool isFinal(char a){
    for (int i = 0; i < lenFinal;i++)
        if(a==final[i])
            return true;
    return false;
}

void createNFA(){
    string line;
    ifstream in;
    in.open("data/LexicalFormula.txt");
    int lineNo = 1;
    bool isStart = true;
    while(getline(in,line)){	// 按行提取
        if(isStart){
            isStart = !isStart;
            start = line[0];
        }
        bool isLeft = true;		// 判断文法等式左边或右边
        for (int i = 0; line[i];i++){
            if(line[i]=='-'&&line[i+1]=='>'){	// 遇到"->"跳过
                i++;
                continue;
            }
            if(line[i]&&isLeft){
                fml[fmlNo].l = line[i];
                isLeft = !isLeft;
                if(!isState(line[i])){	// 如果是新状态，加到状态集
                    state[lenState++] = line[i];
                }
            }
            if(line[i]&&!isLeft){
                if(line[i]>='A'&&line[i]<='Z')
                    fml[fmlNo].r2 = line[i];
                else{
                    fml[fmlNo].r1 = line[i];
                    fml[fmlNo].r2 = ' ';
                    if(!isAlpha(line[i]))	// 如果是新的字母，加到字母表
                        alpha[lenAlpha++] = line[i];
                }
            }
            
        }
        if(fml[fmlNo].r2==' ')	// 如果只能退出终结符，加入到终态集
            if(!isFinal(fml[fmlNo].l))	// 如果是新的终态，加到终态集
                final[lenFinal++] = fml[fmlNo].l;
        fmlNo++;
    }
}

void showNFA(){
	cout << "状态集数量：" << lenState << endl;
	cout << "字母表数量：" << lenAlpha << endl;
	cout << "终态集数量：" << lenFinal << endl;
	cout << "状态集：" << state << endl;
    cout << "字母表：" << alpha << endl;
    cout << "转换函数：" << endl;
    for (int i = 0; fml[i].l;i++)
        cout << fml[i].l << "->" << fml[i].r1 << fml[i].r2 << endl;
    cout << "初态：" << start << endl;
    cout << "终态集：" << final << endl;
}

void createMove(){
    for (int j = 0; j < fmlNo;j++){
        if(fml[j].r1&&fml[j].r2!=' ')
            Move[fml[j].l][fml[j].r1].set[Move[fml[j].l][fml[j].r1].len++]=fml[j].r2;
        else
            Move[fml[j].l][fml[j].r1].set[Move[fml[j].l][fml[j].r1].len++] = 'Y';	// 'Y'表示终态
		// showMove();
	}
}

void showMove(){
	for (int i = 0; i < fmlNo;i++){
		cout << i+1 << '.' << Move[fml[i].l][fml[i].r1].set<<endl;
	}
}

bool stateInSet(char a,NFA temp){	// 查询是否在状态集中
    for (int i = 0; i < temp.len;i++)
        if(a==temp.set[i])
            return true;
    return false;
}

void getClosure(NFA &temp){		// 求ε-closure(move(Ti,alpha))边
    for (int i = 0; i < temp.len;i++){
        for (int j = 0; j < Move[temp.set[i]]['@'].len;j++){
            if(!stateInSet(Move[temp.set[i]]['@'].set[j],temp))
                temp.set[temp.len++]=Move[temp.set[i]]['@'].set[j];
        }
    }
}

bool containY(NFA temp){	// 是否是终态
    for (int i = 0; i < temp.len;i++)
        if(temp.set[i]=='Y')
            return true;
    return false;
}

int isIn(NFA temp){   // 在已有的状态集中查找有没有重复的，有就返回重复的编号，否则返回-1
	bool flag[100];
	bool flag1;
	for(int i=0;i<temp.len;i++){
		flag[i]=false;
	}
	for(int i=0;i<numNewSet;i++){
		for(int k=0;k<temp.len;k++){
			for(int j=0;j<newSet[i].len;j++){
				if(temp.set[k]==newSet[i].set[j]){
					flag[k]=true;
				}
			}
		}
		flag1=true;
		for(int m=0;m<temp.len;m++){	// 有一个元素不一样即不是同一个状态
			if(flag[m]==false){
				flag1=false;
				break;
			}
		}
		if(flag1==true)
			return i;
		for(int m=0;m<temp.len;m++){	// 初始化准备检查下一个状态
			flag[m]=false;
		}
	}
	return -1;
}

void NFAtoDFA(){	// 将NFA转换为DFA
    NFA set0;
    NFA set1;
    set0.set[set0.len++] = start;
    stack<NFA> s;	// 保存DFA的所有状态，便于使用
    getClosure(set0);
    s.push(set0);
    newSet[numNewSet++] = set0;	// 保存DFA的所有状态，便于查找
    for (int i = 0; i < 150;i++)	// 初始化dfa
        for (int j = 0; j < 150;j++)
            dfa[i][j] = -1;
    for (int i = 0; i < 150;i++)	
        isFinalState[i] = false;	// 判断是否是终态
    if(containY(set0))
        isFinalState[numNewSet - 1] = true;
    while(!s.empty()){
        set0 = s.top();
        s.pop();
        for (int i = 0; i < lenAlpha;i++){ 		// 创建新Ti
            for (int j = 0; j < set0.len;j++){
                for (int k = 0; k < Move[set0.set[j]][alpha[i]].len;k++){
                    if(Move[set0.set[j]][alpha[i]].set[k]!='#' && Move[set0.set[j]][alpha[i]].set[k]!='Y' && !stateInSet(Move[set0.set[j]][alpha[i]].set[k],set1)){
						set1.set[set1.len++]=Move[set0.set[j]][alpha[i]].set[k];
					}
					if(Move[set0.set[j]][alpha[i]].set[k]=='Y' && !stateInSet(Move[set0.set[j]][alpha[i]].set[k],set1)){
						set1.set[set1.len++]='Y';    //用Y表示终态
					}
                }
            }
            getClosure(set1);	// 新Ti状态的ε-closure(move(Ti,alpha))
            if(set1.len>0&&isIn(set1)==-1){		// 不重复的话创建新Ti
                dfa[numNewSet - 1][alpha[i]] = numNewSet;	// 建立DFA矩阵
                s.push(set1);
                newSet[numNewSet++] = set1;
                if(containY(set1)){
                    isFinalState[numNewSet - 1] = true;
                }
            }
            if(set1.len>0&&isIn(set1)>-1&&alpha[i]!='@'){	// 重复的话覆盖
                dfa[isIn(set0)][alpha[i]] = isIn(set1);
            }
            set1.len = 0;
        }
    }
}

bool isPassedDFA(char str[]){	// 判断是否符合DFA
    char nowState=0;
	for(int i=0;i<strlen(str);++i ){
		nowState=dfa[nowState][str[i]];
		if(nowState==-1)
			return false;
	}
	if(isFinalState[nowState]==true)	// 遍历字符串后为DFA终态可认为词法分析通过
		return true;
	return false;
}

bool isKeyword(char str[]){	// 是否为关键字
	for(int j=0;j<12;++j)
		if(strcmp(keyword[j],str)==0)
			return true;
	return false;
}

bool isDelimiter(char a){	// 是否为界符
    for(int i=0;i<9;++i)
		if(delimiter[i]==a)
			return true;
	return false;
}

bool isMO(char a){	// 是否为单目运算符
    for(int i=0;i<6;++i){
		if(moOperator[i]==a)
			return true;
	}
	return false;
}

bool isBO(char str[]){	// 是否为双目运算符
    for(int i=0;i<8;++i)
		if(strcmp(biOperator[i],str)==0)
			return true;
	return false;
}

void getResult(){	
    char str[100];
	char ch;
	int i,j;
	int numLine = 1;
	int pointer;	// 指向每个有效字符、数字的指针
	int flag;	/* 判断字符类型
				   -1为出错
				   1为数字
				   2为字母	
				*/
    ch = fgetc(file);
	bool finish = false;
    while(!finish){
	 	flag=-1;
		pointer=0;
		if(isdigit(ch)){
			flag=1;
			str[pointer++]=ch;
			ch=fgetc(file);
			while(isalpha(ch) || isdigit(ch) || ch=='.' || ch=='+' || ch=='-'){
				flag=1;
				str[pointer++]=ch;
				ch=fgetc(file);
			}
			str[pointer]='\0';
		}
		if(flag==1){
			if(isPassedDFA(str)){	
				cout << "<" << numLine << ",常量,'" << str << "'" << '>' << endl;
				output<<1;
			}
			else
				cout<<str<<" "<<"出错，不是常量"<<endl;
			pointer=0;
			flag=-1;
		}
		if(isalpha(ch)){
			flag=2;
			str[pointer++]=ch;
			ch=fgetc(file);
			while(isalpha(ch) || isdigit(ch)){
				flag=2;
				str[pointer++]=ch;
				ch=fgetc(file);
			}
			str[pointer]='\0';
		}
		if(flag==2){
			if(isKeyword(str)){
				cout<< "<" << numLine << ",关键字,'"<<str<<"'>"<<endl;
				output<<func(str);
			}
			else{
				if(isPassedDFA(str)){	
					cout<< "<" << numLine << ",标识符,'"<<str<<"'>"<<endl;
					output<<0;
				}
				else
					cout<<str<<" "<<"出错，不是标识符"<<endl;
			}
			pointer=0;
			flag=-1;
		}
		if(isDelimiter(ch)){
			cout<< "<" << numLine <<",界符,'"<<ch<<"'>"<<endl;
			if(ch=='#')
				output<<'*';
			else
				output<<ch;
			if((ch=fgetc(file))==EOF){
				finish=true;
				break;
			}
		}
		if(isMO(ch)){
			str[pointer++]=ch;
			if((ch=fgetc(file))==EOF){
				finish=true;
			}
			str[pointer++]=ch;
			str[pointer]='\0';
			if(finish==false && isBO(str)){
				cout<< "<" << numLine <<",双目运算符,'"<<str<<"'>"<<endl;
				output<<2;
				ch=fgetc(file);
			}
			else{
				cout<< "<" << numLine << ",单目运算符,'"<<str[0]<<"'>"<<endl;
				output<<str[0];
			}
			pointer=0;
		}
		if(ch=='\n')
			numLine++;
		if(ch==' ' || ch=='\n' || ch=='\t'){
			if((ch=fgetc(file))==EOF){
				finish=true;
				break;
			}
			continue;
		}
	}
	output<<'#';
}

int main(){    
	system("cls");
	// 使MOVE表全部为空（'#'表示空）
    for(int i=0;i<100;++i)
		for(int j=0;j<100;++j)
			for(int k=0;k<100;++k)
				Move[i][j].set[k]='#';
	
    createNFA();
    // showNFA();
    createMove();
    NFAtoDFA();

    file = fopen("data/LexicalAnalysis.txt", "r+");
	output.open("data/LexicalOutput.txt");

	getResult();
	fclose(file);
	output.close();
	
	return 0;
}
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
const char delimiter[20]={',','(',')','{','}',';','<','>','#'}; //���
const char moOperator[10]={'+','-','*','/','^','='};   
const char biOperator[10][3]={"++","--","&&","||","<=","!=","==",">="}; 


char func(char str[]){        //ӳ�䵽һ���ַ�����ʾ
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
    while(getline(in,line)){	// ������ȡ
        if(isStart){
            isStart = !isStart;
            start = line[0];
        }
        bool isLeft = true;		// �ж��ķ���ʽ��߻��ұ�
        for (int i = 0; line[i];i++){
            if(line[i]=='-'&&line[i+1]=='>'){	// ����"->"����
                i++;
                continue;
            }
            if(line[i]&&isLeft){
                fml[fmlNo].l = line[i];
                isLeft = !isLeft;
                if(!isState(line[i])){	// �������״̬���ӵ�״̬��
                    state[lenState++] = line[i];
                }
            }
            if(line[i]&&!isLeft){
                if(line[i]>='A'&&line[i]<='Z')
                    fml[fmlNo].r2 = line[i];
                else{
                    fml[fmlNo].r1 = line[i];
                    fml[fmlNo].r2 = ' ';
                    if(!isAlpha(line[i]))	// ������µ���ĸ���ӵ���ĸ��
                        alpha[lenAlpha++] = line[i];
                }
            }
            
        }
        if(fml[fmlNo].r2==' ')	// ���ֻ���˳��ս�������뵽��̬��
            if(!isFinal(fml[fmlNo].l))	// ������µ���̬���ӵ���̬��
                final[lenFinal++] = fml[fmlNo].l;
        fmlNo++;
    }
}

void showNFA(){
	cout << "״̬��������" << lenState << endl;
	cout << "��ĸ��������" << lenAlpha << endl;
	cout << "��̬��������" << lenFinal << endl;
	cout << "״̬����" << state << endl;
    cout << "��ĸ��" << alpha << endl;
    cout << "ת��������" << endl;
    for (int i = 0; fml[i].l;i++)
        cout << fml[i].l << "->" << fml[i].r1 << fml[i].r2 << endl;
    cout << "��̬��" << start << endl;
    cout << "��̬����" << final << endl;
}

void createMove(){
    for (int j = 0; j < fmlNo;j++){
        if(fml[j].r1&&fml[j].r2!=' ')
            Move[fml[j].l][fml[j].r1].set[Move[fml[j].l][fml[j].r1].len++]=fml[j].r2;
        else
            Move[fml[j].l][fml[j].r1].set[Move[fml[j].l][fml[j].r1].len++] = 'Y';	// 'Y'��ʾ��̬
		// showMove();
	}
}

void showMove(){
	for (int i = 0; i < fmlNo;i++){
		cout << i+1 << '.' << Move[fml[i].l][fml[i].r1].set<<endl;
	}
}

bool stateInSet(char a,NFA temp){	// ��ѯ�Ƿ���״̬����
    for (int i = 0; i < temp.len;i++)
        if(a==temp.set[i])
            return true;
    return false;
}

void getClosure(NFA &temp){		// ���-closure(move(Ti,alpha))��
    for (int i = 0; i < temp.len;i++){
        for (int j = 0; j < Move[temp.set[i]]['@'].len;j++){
            if(!stateInSet(Move[temp.set[i]]['@'].set[j],temp))
                temp.set[temp.len++]=Move[temp.set[i]]['@'].set[j];
        }
    }
}

bool containY(NFA temp){	// �Ƿ�����̬
    for (int i = 0; i < temp.len;i++)
        if(temp.set[i]=='Y')
            return true;
    return false;
}

int isIn(NFA temp){   // �����е�״̬���в�����û���ظ��ģ��оͷ����ظ��ı�ţ����򷵻�-1
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
		for(int m=0;m<temp.len;m++){	// ��һ��Ԫ�ز�һ��������ͬһ��״̬
			if(flag[m]==false){
				flag1=false;
				break;
			}
		}
		if(flag1==true)
			return i;
		for(int m=0;m<temp.len;m++){	// ��ʼ��׼�������һ��״̬
			flag[m]=false;
		}
	}
	return -1;
}

void NFAtoDFA(){	// ��NFAת��ΪDFA
    NFA set0;
    NFA set1;
    set0.set[set0.len++] = start;
    stack<NFA> s;	// ����DFA������״̬������ʹ��
    getClosure(set0);
    s.push(set0);
    newSet[numNewSet++] = set0;	// ����DFA������״̬�����ڲ���
    for (int i = 0; i < 150;i++)	// ��ʼ��dfa
        for (int j = 0; j < 150;j++)
            dfa[i][j] = -1;
    for (int i = 0; i < 150;i++)	
        isFinalState[i] = false;	// �ж��Ƿ�����̬
    if(containY(set0))
        isFinalState[numNewSet - 1] = true;
    while(!s.empty()){
        set0 = s.top();
        s.pop();
        for (int i = 0; i < lenAlpha;i++){ 		// ������Ti
            for (int j = 0; j < set0.len;j++){
                for (int k = 0; k < Move[set0.set[j]][alpha[i]].len;k++){
                    if(Move[set0.set[j]][alpha[i]].set[k]!='#' && Move[set0.set[j]][alpha[i]].set[k]!='Y' && !stateInSet(Move[set0.set[j]][alpha[i]].set[k],set1)){
						set1.set[set1.len++]=Move[set0.set[j]][alpha[i]].set[k];
					}
					if(Move[set0.set[j]][alpha[i]].set[k]=='Y' && !stateInSet(Move[set0.set[j]][alpha[i]].set[k],set1)){
						set1.set[set1.len++]='Y';    //��Y��ʾ��̬
					}
                }
            }
            getClosure(set1);	// ��Ti״̬�Ħ�-closure(move(Ti,alpha))
            if(set1.len>0&&isIn(set1)==-1){		// ���ظ��Ļ�������Ti
                dfa[numNewSet - 1][alpha[i]] = numNewSet;	// ����DFA����
                s.push(set1);
                newSet[numNewSet++] = set1;
                if(containY(set1)){
                    isFinalState[numNewSet - 1] = true;
                }
            }
            if(set1.len>0&&isIn(set1)>-1&&alpha[i]!='@'){	// �ظ��Ļ�����
                dfa[isIn(set0)][alpha[i]] = isIn(set1);
            }
            set1.len = 0;
        }
    }
}

bool isPassedDFA(char str[]){	// �ж��Ƿ����DFA
    char nowState=0;
	for(int i=0;i<strlen(str);++i ){
		nowState=dfa[nowState][str[i]];
		if(nowState==-1)
			return false;
	}
	if(isFinalState[nowState]==true)	// �����ַ�����ΪDFA��̬����Ϊ�ʷ�����ͨ��
		return true;
	return false;
}

bool isKeyword(char str[]){	// �Ƿ�Ϊ�ؼ���
	for(int j=0;j<12;++j)
		if(strcmp(keyword[j],str)==0)
			return true;
	return false;
}

bool isDelimiter(char a){	// �Ƿ�Ϊ���
    for(int i=0;i<9;++i)
		if(delimiter[i]==a)
			return true;
	return false;
}

bool isMO(char a){	// �Ƿ�Ϊ��Ŀ�����
    for(int i=0;i<6;++i){
		if(moOperator[i]==a)
			return true;
	}
	return false;
}

bool isBO(char str[]){	// �Ƿ�Ϊ˫Ŀ�����
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
	int pointer;	// ָ��ÿ����Ч�ַ������ֵ�ָ��
	int flag;	/* �ж��ַ�����
				   -1Ϊ����
				   1Ϊ����
				   2Ϊ��ĸ	
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
				cout << "<" << numLine << ",����,'" << str << "'" << '>' << endl;
				output<<1;
			}
			else
				cout<<str<<" "<<"�������ǳ���"<<endl;
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
				cout<< "<" << numLine << ",�ؼ���,'"<<str<<"'>"<<endl;
				output<<func(str);
			}
			else{
				if(isPassedDFA(str)){	
					cout<< "<" << numLine << ",��ʶ��,'"<<str<<"'>"<<endl;
					output<<0;
				}
				else
					cout<<str<<" "<<"�������Ǳ�ʶ��"<<endl;
			}
			pointer=0;
			flag=-1;
		}
		if(isDelimiter(ch)){
			cout<< "<" << numLine <<",���,'"<<ch<<"'>"<<endl;
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
				cout<< "<" << numLine <<",˫Ŀ�����,'"<<str<<"'>"<<endl;
				output<<2;
				ch=fgetc(file);
			}
			else{
				cout<< "<" << numLine << ",��Ŀ�����,'"<<str[0]<<"'>"<<endl;
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
	// ʹMOVE��ȫ��Ϊ�գ�'#'��ʾ�գ�
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
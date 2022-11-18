// heuristicas_bpc.cpp : Defines the entry point for the console application.

#include <ctime>
#include <stdio.h>
#include <string.h>
#include <fstream>
#include <iostream>
#include <string>
#include <sstream>
#include <iomanip>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <math.h>
#include <time.h>

using namespace std;

// Variaveis Globais

time_t now0 = time(0);

struct  BIN{                                 // Estrutura de Cada BIN     
	int cap_bin,w_bin,rcap,n_itens,ncats;
	vector <int> cats;
    vector < int > elems;
};
int nlc;                                     // Numero de Pares de Categorias Conflitantes
vector < BIN > kbin,kbin_l,kbin_l2;                  // Vetor de BINs
vector < vector <int> > confs;               // Vetor de pares de Categorias Conflitantes
vector < vector <int> > cat_vet;                        // Vetor com todas as categorias 
vector < vector <int> > itens,itens_l,itens_l2;       // Vetor com os Itens a serem alocados nos BINs [ ID, LOJA, PESO, CATEGORIA ]
vector <int>  aloc,aloc_l,aloc_l2;                   // Vetor de Alocacao [0-N itens]  0: item nao alocado  1: item alocado 
string nome_inst;                            // Nome da Instancia
int cap_bin,n_itens;                         // Capacidade do BIN, Numero de Itens 
int n_cats;                                  // Numero de Categorias        
int  minimo = 9999999, maximo = 0, soma = 0;

// funcao auxiliar do comando Sort que permite comparar o segundo elemento de um vector
bool comp_elem2(const vector<int>& a, const vector<int>& b) { return a[1] < b[1]; }
bool comp_elem3(const vector<int>& a, const vector<int>& b) { return a[2] < b[2]; }
bool comp_elem2_inv(const vector<int>& a, const vector<int>& b) { return a[1] > b[1]; }
bool comp_elem3_inv(const vector<int>& a, const vector<int>& b) { return a[2] > b[2]; }

int n_itens_aloc() {
    int cont = 0;
    for (int j=0;j<kbin_l.size();j++) 
        cont += kbin_l[j].elems.size();
    return cont; 
}

void esvazia_BIN_cat(int chosen_bin,int catE ) {
    int e1,wbin_temp=0;
    vector < int > elems_temp;
    int b1 = chosen_bin;
    if (find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),catE)!=kbin_l[b1].cats.end()) {
        for (int j=0;j<kbin_l[chosen_bin].elems.size();j++) {
                e1 = kbin_l[chosen_bin].elems[j];
                if (itens_l[e1][3]==catE) {
                    aloc_l[e1]=0;
                    wbin_temp += itens_l[e1][2]; }
                else
                    elems_temp.push_back(e1);
        }
        kbin_l[b1].elems=elems_temp;
        kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),catE));
        kbin_l[b1].w_bin-=wbin_temp;
        kbin_l[b1].rcap=cap_bin-kbin_l[b1].w_bin;
        kbin_l[b1].n_itens=kbin_l[b1].elems.size();
        kbin_l[b1].ncats=kbin_l[b1].cats.size();
    }
}

void le_instancia(char* input, char* input2 )
{	
	
    int n1,n2,n3,n4;    
    //le pesos
    ifstream arq(input,ios::in);
	if (!arq)
	{
		cerr << "problema com o arquivo";
		exit(1);
	}

    arq >> nome_inst;
	arq >> cap_bin;
    arq >> n_itens;
	for (int j = 0; j < n_itens; j++)
	{	
        arq >> n1 >> n2 >> n3 >> n4;
        vector <int> nt;
        nt.push_back(n1); //id
        nt.push_back(n2); //loja
        nt.push_back(n3); //peso
        nt.push_back(n4); // categoria
        aloc.push_back(0);
        itens.push_back(nt);
        
        if (n3>maximo)
            maximo = n3;
        if (n3<minimo)
            minimo = n3;        
    }
    arq.close();
   
    // le conflitos
    string num;
    int n,n_cats;
    ifstream arq2(input2,ios::in);
	if (!arq)
	{
		cerr << "problema com o arquivo";
		exit(1);
	}
	arq2 >> nlc >> n_cats;
    vector <int> temp_nums;
    for (int j = 0; j < nlc; j++)
    {    
        arq2 >> n1 >> n2;
        vector <int> nt;
        nt.push_back(n1);
        nt.push_back(n2);
        confs.push_back(nt);
    }    
    arq2.close();
    
    for (int j=1;j<=n_cats;j++) { 
        vector <int> temp;
        temp.push_back(j); 
        temp.push_back(0);
        cat_vet.push_back(temp);
    }
    // conta  qtde de categoria e conflitos cada uma tem    
    int cont;
    for (int j=0;j<cat_vet.size();j++) {
       cont = 0;
       for (int i=0;i < nlc; i++) {
            if ((confs[i][0]==cat_vet[j][0])||(confs[i][1]==cat_vet[j][0]))
                cont += 1;
       }
       cat_vet[j][1] = cont;    
    }   
    sort(cat_vet.begin(), cat_vet.end(),comp_elem2);       
}

void ordena_itens() {
    itens_l.clear();
    aloc_l.clear();
    sort(itens.begin(), itens.end(),comp_elem3_inv);       
    for (int j = cat_vet.size();j>=1;j--) 
         for (int i=0;i<itens.size();i++)
             if (itens[i][3]==cat_vet[j-1][0]) {
                 itens_l.push_back(itens[i]);
                 aloc_l.push_back(0);
             }
     itens=itens_l;
     aloc=aloc_l;
}

bool tem_conflito(int a,int b)
{
   // verifica qual o menor elemento
   int menor,maior; 
   if (a<b)
   {  menor=a; maior=b;}
   else
    { menor=b; maior=a;}
   
   bool achou=false;
     
   achou = false;
   for (int j=0;j<nlc;j++)
        if ((confs[j][0]==menor)&&(confs[j][1]==maior)) { achou=true; break; }

    return achou;
}

bool nao_conflito(int a, int bin)  // verifica se a Categoria tem conflito com bin
{
    bool achou=true;
    for (int j=0;j<kbin_l[bin].cats.size();j++)
    {
        if (tem_conflito(a,kbin_l[bin].cats[j]))
        {
            achou=false;
            break;
        }
    }
    return achou;
}

bool nao_conflito_cpBIN(int a, BIN bincp)  // verifica se a Categoria tem conflito com bin
{
    bool achou=true;
    for (int j=0;j<bincp.cats.size();j++)
    {
        if (tem_conflito(a,bincp.cats[j]))
        {
            achou=false;
            break;
        }
    }
    return achou;
}

int atualiza_bin(int p, int bin_ut) {
    kbin_l[bin_ut].w_bin += itens_l[p][2];
    kbin_l[bin_ut].cap_bin = cap_bin;
    kbin_l[bin_ut].rcap = cap_bin - itens_l[p][2];
    kbin_l[bin_ut].n_itens += 1;
    if (find(kbin_l[bin_ut].cats.begin(), kbin_l[bin_ut].cats.end(), itens_l[p][3]) == kbin_l[bin_ut].cats.end()) {
        kbin_l[bin_ut].cats.push_back(itens_l[p][3]);
        kbin_l[bin_ut].ncats += 1;
    }
    kbin_l[bin_ut].elems.push_back(p);
    return 0;
}

int adiciona_bin(int p) {
    BIN temp_bin;
    temp_bin.w_bin = itens_l[p][2];
    temp_bin.cap_bin = cap_bin;
    temp_bin.rcap = cap_bin - itens_l[p][2];
    temp_bin.n_itens = 1;
    temp_bin.ncats = 1;
    temp_bin.cats.push_back(itens_l[p][3]);
    temp_bin.elems.push_back(p);
    kbin_l.push_back(temp_bin);
    return 0;
}

void mostra_resultado(string titulo,bool detalhe, int inicial){
    int soma, cat1,e1,soma1,cont1;
    time_t now1 = time(0);
    cout << "\n" << titulo << "  " << "Nome_Instancia " << nome_inst << "  Cap. " << cap_bin << "  N_Itens " << itens_l.size() << "  N_Bins_Inic " << inicial << " N_Bins_VNS " << kbin_l.size() << " Itens Alocados: " << n_itens_aloc() << " Tempo " << now1-now0;  
}

// Heuristica Contrutiva
int best_fit_conflito(char* input) {
	int n_util,j_menor,cap_rest_menor,cap_rest,bin_ut;
    n_util=kbin_l.size();
    for (int p=0;p<itens_l.size();p++) { // armazena item a item
        if (aloc_l[p]==0) {
            j_menor=-1;
            cap_rest_menor=99999;
            for (int j=0;j<kbin_l.size();j++) { // verifica qual o bin utilidado cuja capacidade reidual é a menor
                cap_rest=cap_bin-kbin_l[j].w_bin;
                // verifica os Bins cuja Capacidade residual comporta o peso do item e busca a menor capacidade residual
                if (strcmp(input,"0")==0) { 
                    if ((cap_rest>=itens_l[p][2])&&(cap_rest<cap_rest_menor)) {
                        cap_rest_menor = cap_rest;
                        j_menor=j;
                    }
                }
                else { 
                    if ((cap_rest>=itens_l[p][2])&&(cap_rest<cap_rest_menor)&& nao_conflito(itens_l[p][3],j)) {
                        cap_rest_menor = cap_rest;
                        j_menor=j;
                    }
                }   
            }
           
            if ( j_menor > -1 )  
                int a = atualiza_bin(p,j_menor);
            else {
                n_util++;
                int b = adiciona_bin(p);        
            }
            aloc_l[p]=1; // ativa flag de alocacao
        }
    }
    return kbin_l.size();
} 

// Retirar de 30% dos BINs os elementos de uma categoria Randomica
void shaking_N1(float porc) {
    int e1,b1,n_cats_e;
    n_cats = cat_vet.size();
    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin-kbin_l[i].w_bin); 
        bins_ordenados.push_back(temp);
    }   
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    srand(std::time(0));
    int chosen_cat;
    int nreleased = floor(porc*bins_ordenados.size()); 
    
    n_cats_e = floor(n_cats/2);   
    chosen_cat = rand()%n_cats_e;   
    chosen_cat = cat_vet[n_cats-chosen_cat-1][0];
    
    for (int i=0;i<nreleased;i++){
        b1=bins_ordenados[i][0];
        vector <int> temp;
        bool achou =false;	
        int ccat = 0;
        for (int j=0;j<kbin_l[b1].elems.size();j++){
            e1 = kbin_l[b1].elems[j];
            if (itens_l[e1][3]==chosen_cat) {
                aloc_l[e1]=0;
                achou =true;
            }
            else {
                temp.push_back(e1);
                ccat += 1;
            }
        }
                
        if (ccat > 0)
            kbin_l[b1].elems = temp;
        else 
            kbin_l[b1].elems.clear();
           
        if ((achou)&&(ccat > 0))
            if (find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat)!=kbin_l[b1].cats.end())    
                kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat));
        
    }
    
    // elimina Bins vazios
        bool achou = false;
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()==0) { achou = true; break;}
        vector < BIN > kbin_temp;
        if (achou){
            for (int i=0; i<kbin_l.size();i++)
                if (kbin_l[i].elems.size()>0)
                    kbin_temp.push_back(kbin_l[i]);
            kbin_l = kbin_temp;
        }
    
     //Realoca os Itens
     char st[] = "1";
     int a=best_fit_conflito(st);
}

// Esvaziar 15% dos BINs escolhidos ao acaso
void shaking_N2(float porc) {
    int e1;
    srand(std::time(0));
    int chosen_bin;
    int nreleased = floor(porc*kbin_l.size()); 
    vector <int> solta;
    for (int cont=0;cont<nreleased;cont++){
        chosen_bin = rand()%kbin_l.size();
        for (int j=0;j<kbin_l[chosen_bin].elems.size();j++) {
            e1 = kbin_l[chosen_bin].elems[j];
            aloc_l[e1]=0;
        }
        kbin_l.erase(kbin_l.begin()+chosen_bin); // elimina o BIN
    }
     //Realoca os Itens
     char st[] = "1";
     int a=best_fit_conflito(st);
}


// Retirar de %porc BINs todos os obejtos da categoria menos restritiva
void shaking_N3(float porc) {
    int e1,b1,n_cats_e;
    n_cats = cat_vet.size();
    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin-kbin_l[i].w_bin); 
        bins_ordenados.push_back(temp);
    }   
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    srand(std::time(0));
    
    int chosen_cat;
    int nreleased = floor(porc*bins_ordenados.size()); 
    
    //cout << "e1\n";
    
    //n_cats_e = floor(n_cats/2);   
    chosen_cat = cat_vet[0][0];
    
    for (int i=0;i<nreleased;i++){
        b1=bins_ordenados[i][0];
        vector <int> temp;
        bool achou =false;	
        int ccat = 0;

        if (kbin_l[b1].cats.size() > 2) {
            for (int j=0;j<kbin_l[b1].elems.size();j++){
                e1 = kbin_l[b1].elems[j];
                if (itens_l[e1][3]==chosen_cat){
                    aloc_l[e1]=0;
                    achou =true;
                }
                else {
                    temp.push_back(e1);
                    ccat += 1;
                }
            }
                
            //cout << "e3\n";
            
            if (ccat > 0)
                kbin_l[b1].elems = temp;
            else 
                kbin_l[b1].elems.clear();
               
            //cout << "e4\n";
            if ((achou)&&(ccat > 0))
                if (find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat)!=kbin_l[b1].cats.end())    
                    kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat));
        }    
    }
    
    // elimina Bins vazios
        bool achou = false;
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()==0) { achou = true; break;}
        vector < BIN > kbin_temp;
        if (achou){
            for (int i=0; i<kbin_l.size();i++)
                if (kbin_l[i].elems.size()>0)
                    kbin_temp.push_back(kbin_l[i]);
            kbin_l = kbin_temp;
        }
    
     //Realoca os Itens
     char st[] = "1";
     int a=best_fit_conflito(st);
}


// Retirar de %porc BINs todos os obejtos da DUAS categoria mais restritiva
void shaking_N20(float porc) {
    int e1,b1,n_cats_e;
    n_cats = cat_vet.size();
    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin-kbin_l[i].w_bin); 
        bins_ordenados.push_back(temp);
    }   
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    srand(std::time(0));
    
    int chosen_cat,chosen_cat2;
    int nreleased = floor(porc*bins_ordenados.size()); 
    
    chosen_cat = cat_vet[cat_vet.size()-1][0];
    if (cat_vet.size() > 1)
        chosen_cat2 = cat_vet[cat_vet.size()-2][0];
    else
        chosen_cat2 = chosen_cat;
    
    for (int i=0;i<nreleased;i++){
        b1=bins_ordenados[i][0];
        vector <int> temp;
        bool achou =false;	
        int ccat = 0;

        for (int j=0;j<kbin_l[b1].elems.size();j++){
            e1 = kbin_l[b1].elems[j];
            if ((itens_l[e1][3]==chosen_cat)||(itens_l[e1][3]==chosen_cat2)) {
                aloc_l[e1]=0;
                achou =true;
            }
            else {
                temp.push_back(e1);
                ccat += 1;
            }
        }
        
        if (ccat > 0)
            kbin_l[b1].elems = temp;
        else 
            kbin_l[b1].elems.clear();
           
        if ((achou)&&(ccat > 0))
            if (find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat)!=kbin_l[b1].cats.end())    
                kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat));
            if (find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat2)!=kbin_l[b1].cats.end())    
                kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(),kbin_l[b1].cats.end(),chosen_cat2));
       
    }
    
    // elimina Bins vazios
        bool achou = false;
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()==0) { achou = true; break;}
        vector < BIN > kbin_temp;
        if (achou){
            for (int i=0; i<kbin_l.size();i++)
                if (kbin_l[i].elems.size()>0)
                    kbin_temp.push_back(kbin_l[i]);
            kbin_l = kbin_temp;
        }
    
     //Realoca os Itens
     char st[] = "1";
     int a=best_fit_conflito(st);
}

// Retirar de %porc BINs todos os obejtos exceto os da categoria mais restritiva
void shaking_N4(float porc) {
    int e1,b1,n_cats_e;
    n_cats = cat_vet.size();
    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin-kbin_l[i].w_bin); 
        bins_ordenados.push_back(temp);
    }   
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    srand(std::time(0));
    
    int chosen_cat;
    int nreleased = floor(porc*bins_ordenados.size()); 
    
    //cout << "e1\n";
    
    //n_cats_e = floor(n_cats/2);   
    chosen_cat = cat_vet[cat_vet.size()-1][0];
    
    for (int i=0;i<nreleased;i++){
        b1=bins_ordenados[i][0];
        vector <int> temp;
        bool achou =false;	
        int ccat = 0;    
        if (kbin_l[b1].cats.size()>2) {
        
                for (int j=0;j<kbin_l[b1].elems.size();j++){
                    e1 = kbin_l[b1].elems[j];
                    if (itens_l[e1][3]!=chosen_cat){
                        aloc_l[e1]=0;
                        achou =true;
                    }
                    else {
                        temp.push_back(e1);
                        ccat += 1;
                    }
                }
                
                if (ccat > 0)
                    kbin_l[b1].elems = temp;
                else 
                    kbin_l[b1].elems.clear();
                
                kbin_l[b1].cats.clear();
                kbin_l[b1].cats.push_back(chosen_cat);
        }
  
    }
    
    // elimina Bins vazios
        bool achou = false;
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()==0) { achou = true; break;}
        vector < BIN > kbin_temp;
        if (achou){
            for (int i=0; i<kbin_l.size();i++)
                if (kbin_l[i].elems.size()>0)
                    kbin_temp.push_back(kbin_l[i]);
            kbin_l = kbin_temp;
        }
    
     //Realoca os Itens
     char st[] = "1";
     int a=best_fit_conflito(st);
}

// Esvazia %porc BINs com as menores capacidades restantes
void shaking_N5(float porc) {
    int e1,f1;
    
    int chosen_bin;
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin-kbin_l[i].w_bin); 
        bins_ordenados.push_back(temp);
    }   
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    int nreleased = floor(porc*kbin_l.size()); 
    vector <int> solta;
    for (int cont=0;cont<nreleased;cont++){
        chosen_bin = bins_ordenados[cont][0];
        for (int j=0;j<kbin_l[chosen_bin].elems.size();j++) {
            e1 = kbin_l[chosen_bin].elems[j];
            aloc_l[e1]=0;
        }
        kbin_l[chosen_bin].elems.clear();
    }
    
    // elimina Bins vazios
    bool achou = false;
    for (int i=0; i<kbin_l.size();i++)
        if (kbin_l[i].elems.size()==0) { achou = true; break;}
    vector < BIN > kbin_temp;
    if (achou){
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()>0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
    
     //Realoca os Itens
     char st[] = "1";
     int a=best_fit_conflito(st);
}

// Esvazia os BINs com um unica categoria e coloca os itens em outras, depois que forem retirados outros itens para abrir espaço
void shaking_N6()
{
    int e1,e2,binx,cat_e,ordem_bin_e,ordem_bin_e1,e11,e3;
    bool trocou = false;
    bool det =true;
    
    itens_l2.clear();
    aloc_l2.clear();

    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);

    //esvazia o bin com 1 categoria
    bool achou=false;
    for (int i=0;i<bins_ordenados.size();i++){
    	ordem_bin_e = i;
        e1=bins_ordenados[i][0];           
		if (kbin_l[e1].cats.size()==1) {
			cat_e = kbin_l[e1].cats[0];
            achou =true;
			break;
		}
	}
    
    esvazia_BIN_cat(e1,cat_e);
    
    
    //busca outro bin que contenha aquela categoria, para cada um das outras categoria do bin, leva os elementos para outros bins
		for (int k=ordem_bin_e+1;k<bins_ordenados.size();k++) {
			ordem_bin_e1=k;
			e2=bins_ordenados[k][0];            
            vector <int> temp_cats;
			if ((kbin_l[e2].cats.size()>1)&&(find(kbin_l[e2].cats.begin(),kbin_l[e2].cats.end(),cat_e) != kbin_l[e2].cats.end()))
                for (int j=0;j<kbin_l[e2].cats.size();j++)
                    if (kbin_l[e2].cats[j]!=cat_e)
                        temp_cats.push_back(kbin_l[e2].cats[j]);            
                if (temp_cats.size()>0)
                    for (int j=0;j<temp_cats.size();j++)
                        esvazia_BIN_cat(e2,temp_cats[j]);                
       }
       
    
   
    // elimina Bins vazios  
    vector < BIN > kbin_temp;
    for (int t=0; t<kbin_l.size();t++)
        if (kbin_l[t].elems.size()>0)
            kbin_temp.push_back(kbin_l[t]);
    kbin_l = kbin_temp;        
    
    
	//Realoca os Itens
	char st[] = "1";
	int a=best_fit_conflito(st);
}

// bins ordenados por peso crescente 
void BuscaLocalN1()
{
    int e1,e2;
    bool trocou = false;
    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        if (kbin_l[i].w_bin<cap_bin)
            bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    
    if (bins_ordenados.size()<2) return;
    
    // cria a lista de pares de BINs que irao sofrer possiveis trocas
    vector < vector <int> > pares;
    for (int i=0;i<bins_ordenados.size()-1;i++){
        e1=bins_ordenados[i][0];
        for (int j=bins_ordenados.size()-1;j>i;j--){
            e2=bins_ordenados[j][0];
            vector <int> temp;
            temp.push_back(e1);
            temp.push_back(e2);
            pares.push_back(temp);
        }
    }
    for (int i=0;i<pares.size();i++) {         
        e1 = pares[i][0]; e2 = pares[i][1]; 
        //define vetores temporarios
        BIN bin1 = kbin_l[e1];
        BIN bin2 = kbin_l[e2];    
        
        // executa a tentativa de melhoria se houver elementos no BIN 1
        if (bin1.elems.size()>0) {
        
            for (int j=0;j<kbin_l[e1].elems.size();j++){
                int elemA = kbin_l[e1].elems[j];
                int catA = itens_l[elemA][3];
                int w_A = itens_l[elemA][2];
                //verifica se estoura a capcidade do BIN B e se conflita
                if ((nao_conflito_cpBIN(catA,bin2))&&((bin2.w_bin+w_A)<=cap_bin)){ 
                        bin2.w_bin += w_A;
                        bin1.w_bin -= w_A;
                       
                        //elem_levados.push_back(elemA);
                        bin1.elems.erase(find(bin1.elems.begin(),bin1.elems.end(),elemA));
                        bin2.elems.push_back(elemA);
                        
                        // acrescenta catA no vetor de categorias de bin 2
                        bool achou=false;
                        for (int k=0;k<bin2.cats.size();k++)
                            if (catA==bin2.cats[k]) { achou=true; break; }
                        if (!achou) bin2.cats.push_back(catA);
                        // retira catA no vetor de categorias de bin 1 se o elemA for o unico
                        int ccatA = 0;
                        for (int k=0;k<bin1.elems.size();k++)
                            if (itens_l[bin1.elems[k]][3]==catA) ccatA += 1;
                        if (ccatA==1)
                            bin1.cats.erase(find(bin1.cats.begin(),bin1.cats.end(),catA));
                        
                        bin1.rcap = cap_bin - bin1.w_bin;
                        bin1.n_itens = bin1.elems.size();
                        bin1.ncats = bin1.cats.size();
                        bin2.rcap = cap_bin - bin2.w_bin;
                        bin2.n_itens = bin2.elems.size();
                        bin2.ncats = bin2.cats.size();
                }    
            }        
            //if ( bin2.rcap < kbin_l[e1].rcap ) {   
            if ( bin2.w_bin > kbin_l[e2].w_bin ) {   
                kbin_l[e1] = bin1;
                kbin_l[e2] = bin2;
                break;
            }
        }    
    }
    // elimina Bins vazios
    bool achou = false;
    for (int i=0; i<kbin_l.size();i++)
        if (kbin_l[i].elems.size()==0) { achou = true; break;}
    vector < BIN > kbin_temp;
    if (achou){
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()>0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
}

// bins ordenados por numero de categorias crescente 
void BuscaLocalN2()
{
    int e1,e2;
    bool trocou = false;
    // cria uma vector dos id dos BINs ordenados por numero de categorias
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].cats.size());
        if (kbin_l[i].w_bin<cap_bin)
            bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    if (bins_ordenados.size()<2) return;
    // cria a lista de pares de BINs que irao sofrer possiveis trocas
    vector < vector <int> > pares;
    
    for (int i=0;i<bins_ordenados.size()-1;i++){
        e1=bins_ordenados[i][0];
        for (int j=bins_ordenados.size()-1;j>i;j--){
            e2=bins_ordenados[j][0];
            vector <int> temp;
            temp.push_back(e1);
            temp.push_back(e2);
            pares.push_back(temp);
        }
    }
    
    for (int i=0;i<pares.size();i++) {
        
        e1 = pares[i][0]; e2 = pares[i][1]; 
        
        //define vetores temporarios
        BIN bin1 = kbin_l[e1]; 
        BIN bin2 = kbin_l[e2];    
        
        // executa a tentativa de melhoria se houver elementos no BIN 1
        
        if (bin1.elems.size()>0) {
            
            for (int j=0;j<kbin_l[e1].elems.size();j++){
                int elemA = kbin_l[e1].elems[j];
                int catA = itens_l[elemA][3];
                int w_A = itens_l[elemA][2];
                //verifica se estoura a capcidade do BIN B e se conflita
                
                if ((nao_conflito_cpBIN(catA,bin2))&&((bin2.w_bin+w_A)<=cap_bin)){ 
                        
                        bin2.w_bin += w_A;
                        bin1.w_bin -= w_A;
    
                        //elem_levados.push_back(elemA);
                        bin1.elems.erase(find(bin1.elems.begin(),bin1.elems.end(),elemA));
                        bin2.elems.push_back(elemA);
    
                        
                        // acrescenta catA no vetor de categorias de bin 2
                        bool achou=false;
                        for (int k=0;k<bin2.cats.size();k++)
                            if (catA==bin2.cats[k]) { achou=true; break; }
                        if (!achou) bin2.cats.push_back(catA);
                        // retira catA no vetor de categorias de bin 1 se o elemA for o unico
    
                        int ccatA = 0;
                        for (int k=0;k<bin1.elems.size();k++)
                            if (itens_l[bin1.elems[k]][3]==catA) ccatA += 1;
                        
                        if (ccatA==1)
                            bin1.cats.erase(find(bin1.cats.begin(),bin1.cats.end(),catA));
                        
                        bin1.rcap = cap_bin - bin1.w_bin;
                        bin1.n_itens = bin1.elems.size();
                        bin1.ncats = bin1.cats.size();
                        bin2.rcap = cap_bin - bin2.w_bin;
                        bin2.n_itens = bin2.elems.size();
                        bin2.ncats = bin2.cats.size();
                        
                }    
            }
            
            if ( bin2.rcap < kbin_l[e1].rcap ) {   
                
                kbin_l[e1] = bin1;
                kbin_l[e2] = bin2;
                break;
            }
            
        }    
    }
    
    // elimina Bins vazios
    bool achou = false;
    for (int i=0; i<kbin_l.size();i++)
        if (kbin_l[i].elems.size()==0) { achou = true; break;}
    vector < BIN > kbin_temp;
    if (achou){
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()>0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
}

// bins ordenados por peso crescente 
void BuscaLocalN3()
{
    int e1,e2,maior_obj,obj_temp,e2_e1;
    bool trocou = false;
    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        if (kbin_l[i].w_bin<cap_bin)
            bins_ordenados.push_back(temp);
    }

    if (bins_ordenados.size()<2) return;

    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    
    //cout << "test 1";
    
    // cria a lista de pares de BINs que irao sofrer possiveis trocas
    for (int i=0;i<bins_ordenados.size()-1;i++){
        e1=bins_ordenados[i][0];
        BIN bin1,bin11 = kbin_l[e1];
        //cout << "test 4";
        for (int j=0;j<kbin_l[e1].elems.size();j++){
            int elemA = kbin_l[e1].elems[j];
            int catA = itens_l[elemA][3];
            int w_A = itens_l[elemA][2];
            //cout << "test 5";
            maior_obj = 0;
            for (int k=i+1;k<bins_ordenados.size();k++){
                e2=bins_ordenados[k][0];
                BIN bin2 = kbin_l[e2];
                //cout << "test 6";
                if ((nao_conflito_cpBIN(catA,bin2))&&((bin2.w_bin+w_A)<=cap_bin)){ 
                    obj_temp = pow(bin11.w_bin-w_A,2)+pow(bin2.w_bin+w_A,2)-pow(bin11.w_bin,2)-pow(bin2.w_bin,2);
                    //cout << "test 7";
                    if (obj_temp > maior_obj) {
                        maior_obj = obj_temp;
                        e2_e1 = e2;
                    }
                }
            }
            if ( maior_obj > 0) {
                bin11.elems.erase(find(bin11.elems.begin(),bin11.elems.end(),elemA));
                BIN bin2 = kbin_l[e2_e1];
                bin2.elems.push_back(elemA);
                
                if (find(bin2.cats.begin(),bin2.cats.end(),catA)==bin2.cats.end())
                    bin2.cats.push_back(catA);
                
                // retira catA no vetor de categorias de bin 1 se o elemA for o unico
                int ccatA = 0;
                for (int k=0;k<bin11.elems.size();k++)
                    if (itens_l[bin11.elems[k]][3]==catA) ccatA += 1;
                if (ccatA==1)
                    bin11.cats.erase(find(bin11.cats.begin(),bin11.cats.end(),catA));
                //cout << "test 9";
                bin2.w_bin += w_A;
                bin11.w_bin -= w_A;
                bin11.rcap = cap_bin - bin11.w_bin;
                bin11.n_itens = bin11.elems.size();
                bin11.ncats = bin11.cats.size();
                bin2.rcap = cap_bin - bin2.w_bin;
                bin2.n_itens = bin2.elems.size();
                bin2.ncats = bin2.cats.size();
                
                kbin_l[e2] = bin2;
            }
        }        
       
        kbin_l[e1] = bin11;
    }    

    
    //elimina Bins vazios
    bool achou = false;
    for (int i=0; i<kbin_l.size();i++)
        if (kbin_l[i].elems.size()==0) { achou = true; break;}
    vector < BIN > kbin_temp;
    if (achou){
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()>0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
}

// bins ordenados por peso crescente 
void BuscaLocalN4()
{
    int e1,e2,maior_obj,obj_temp,e2_e1,elemB_e,catB_e,w_B_e,posB_e;
    bool trocou = false;
    
    
    BIN bin2;
    // cria uma vector dos id dos BINs ordenados por peso
    vector < vector <int> > bins_ordenados;
    for (int i=0;i<kbin_l.size();i++){
        vector <int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        if (kbin_l[i].w_bin<cap_bin)
            bins_ordenados.push_back(temp);
    }

    if (bins_ordenados.size()<2) return;

    sort(bins_ordenados.begin(), bins_ordenados.end(),comp_elem2);
    
    // cria a lista de pares de BINs que irao sofrer possiveis trocas
    
    vector < vector <int> > pares;
    
    for (int i=0;i<bins_ordenados.size()-1;i++){
        e1=bins_ordenados[i][0];
        BIN bin1 = kbin_l[e1];
        
        for (int j=0;j<kbin_l[e1].elems.size();j++){
            int elemA = kbin_l[e1].elems[j];
            int posA = j;
            int catA = itens_l[elemA][3];
            int w_A = itens_l[elemA][2];
        
            maior_obj = 0;
            for (int k=i+1;k<bins_ordenados.size();k++){
                e2=bins_ordenados[k][0];
                bin2 = kbin_l[e2];
                
                for (int p=0;p<kbin_l[e2].elems.size();p++) {
                    
                    int elemB = kbin_l[e2].elems[p];
                   
                    int posB = p;
                   
                    int catB = itens_l[elemB][3];
                   
                    int w_B = itens_l[elemB][2];
                   
                    if (((nao_conflito_cpBIN(catA,bin2))&&((bin2.w_bin+w_A)<=cap_bin))&&((nao_conflito_cpBIN(catB,bin1))&&((bin1.w_bin+w_B)<=cap_bin))){ 
                        
                        obj_temp = pow(bin1.w_bin-w_A+w_B,2)+pow(bin2.w_bin+w_A-w_B,2)-pow(bin1.w_bin,2)-pow(bin2.w_bin,2);
                        
                   
                        if (obj_temp > maior_obj) {
                            maior_obj = obj_temp;
                            e2_e1 = e2;
                            elemB_e = elemB;
                            catB_e = catB;
                            w_B_e = w_B;
                            posB_e = posB;
                        }
                    }
                }
            }
            
            if (maior_obj > 0) {
                bin2 = kbin_l[e2_e1];
                // retira catA no vetor de categorias de bin 1 se o elemA for o unico
                int ccatA = 0;
                for (int k=0;k<bin1.elems.size();k++)
                    if (itens_l[bin1.elems[k]][3]==catA) ccatA += 1;
                if (ccatA==1)
                    bin1.cats.erase(find(bin1.cats.begin(),bin1.cats.end(),catA));
                
                // retira catB no vetor de categorias de bin 2 se o elemB for o unico
                ccatA = 0;
                for (int k=0;k<bin2.elems.size();k++)
                    if (itens_l[bin2.elems[k]][3]==catB_e) ccatA += 1;
                if (ccatA==1)
                    bin2.cats.erase(find(bin2.cats.begin(),bin2.cats.end(),catB_e));
                
                if (find(bin2.cats.begin(),bin2.cats.end(),catA)==bin2.cats.end())
                    bin2.cats.push_back(catA);
                if (find(bin1.cats.begin(),bin1.cats.end(),catB_e)==bin1.cats.end())
                    bin1.cats.push_back(catB_e);
                
                bin1.elems[posA] = elemB_e;
                bin2.elems[posB_e] = elemA;
                
    
                
                bin1.w_bin += w_B_e - w_A;
                bin2.w_bin += w_A - w_B_e;
                
                bin1.rcap = cap_bin - bin1.w_bin;
                bin1.n_itens = bin1.elems.size();
                bin1.ncats = bin1.cats.size();

                bin2.rcap = cap_bin - bin2.w_bin;
                bin2.n_itens = bin2.elems.size();
                bin2.ncats = bin2.cats.size();
   
                kbin_l[e2_e1] = bin2;
            }
        }        
        kbin_l[e1] = bin1;
    }    

    
    
    // elimina Bins vazios
    bool achou = false;
    for (int i=0; i<kbin_l.size();i++)
        if (kbin_l[i].elems.size()==0) { achou = true; break;}
    vector < BIN > kbin_temp;
    if (achou){
        for (int i=0; i<kbin_l.size();i++)
            if (kbin_l[i].elems.size()>0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
    
}

void VNS(int niter){
   
    int conts[2] = {0};
    vector < vector <int> > results;
    float porc; 
    int Ks,Ls,contu,contu_max = floor(niter/2);
    bool det = true;
    int cont_ks[6][2],cont_ls[5][2];
    int cont_ks2[6];
    int ultima_melhoria=niter;
    
    
    string tit;
    kbin_l=kbin;
    aloc_l=aloc;
    itens_l=itens;
    // Heuristica Inicial BEST FIT com Conflito
    char st[] = "1";
    int a = best_fit_conflito(st);
    int result_heur_inic = kbin_l.size();
    
    // Guarda a solucao Inicial
    kbin=kbin_l; aloc=aloc_l;
    
    int cont = niter;
    contu = 0; int n_dep = 0; int n_ant = 0;
    
    for (int i=0;i<6;i++)  {
        cont_ks[i][0]=0; cont_ks[i][1]=0;
    }
    for (int i=0;i<6;i++)  
        cont_ks2[i]=0;
    
    for (int i=0;i<4;i++)  {
        cont_ls[i][0]=0; cont_ls[i][1]=0;
    }
        
    
    while (cont > 0) {
        Ks = 1;
        while ((Ks<7)&&(cont > 0)) {
            //cout << "Antes Itens " << n_itens_aloc();
            n_ant = kbin_l.size();
            switch (Ks){
                case 1:
                    porc = 0.30; /*cout << "\n shaking_N1 " << Ks << "  " ;*/ shaking_N1(porc);/* cout << "Itens " << n_itens_aloc();*/   break;
                case 2:
                    porc = 0.15;/* cout << "\n shaking_N2 " << Ks << "  " ;*/ shaking_N2(porc);/*  cout << "Itens " << n_itens_aloc();*/  break;
                case 3:
                    porc = 1.00;/* cout << "\n shaking_N5  " << Ks << "  ";*/ shaking_N3(porc);/* cout << "Itens " << n_itens_aloc();*/  break;
                case 4:
                    porc = 1.00;/* cout << "\n shaking_N7  " << Ks << "  ";*/ shaking_N4(porc);/* cout << "Itens " << n_itens_aloc();*/  break;
                case 5:
                    porc = 0.15;/* cout << "\n shaking_N8  " << Ks << "  ";*/ shaking_N5(porc);/* cout << "Itens " << n_itens_aloc();*/   break;    
                case 6:
                    /*cout << "\n shaking_N9 " << Ks << "  " ;*/ shaking_N6(); /* cout << "Itens " << n_itens_aloc();*/  break;
            }   
            n_dep = kbin_l.size(); 
            cont_ks[Ks-1][0]+=1;
            if (n_dep<n_ant) cont_ks[Ks-1][1]+=1;
            
            if ( kbin_l.size() <= kbin.size() )    
               { kbin_l2=kbin_l; aloc_l2=aloc_l; } // X'
            else
               { kbin_l2=kbin; aloc_l2=aloc; }// X'
           
            
            //cout << "   nbins " << kbin_l.size() << "\n\n\n";
            // Local Search by VND
            Ls = 1;
            while ((Ls<3)&&(cont > 0)) {
                n_ant = kbin_l.size();
                switch (Ls){ // FIND X'' OF X'
                    case 1:
                        /*cout << "\n BuscaLocalN3() \n ";*/ BuscaLocalN1();  break;
                    case 2:
                        /*cout << "\n BuscaLocalN4() \n ";*/ BuscaLocalN2(); break;
                    case 3:
                        /*cout << "\n BuscaLocalN9() \n ";*/BuscaLocalN3(); break;
                    case 4:
                        /*cout << "\n BuscaLocalN10() \n ";*/BuscaLocalN4(); break;             
                }
                n_dep = kbin_l.size(); 
                cont_ls[Ls-1][0]+=1;
                if (n_dep<n_ant) { cont_ls[Ls-1][1]+=1; cont_ks2[Ks-1]+=1; }
                // Move or Not
                vector <int> temp;
                temp.push_back(cont);
                temp.push_back(Ks);
                temp.push_back(Ls);
                temp.push_back(kbin.size());
                temp.push_back(kbin_l2.size());
                temp.push_back(kbin_l.size());
                results.push_back(temp);
                if ( kbin_l.size() < kbin_l2.size() ) {
                    kbin_l2=kbin_l; aloc_l2=aloc_l;
                    Ls = 1;
                    ultima_melhoria = niter - cont;
                }
                else {
                    kbin_l=kbin_l2; aloc_l=aloc_l2;
                    Ls += 1;
                }             
                cont -= 1;    
            }
            // Move or Not
            if (kbin_l2.size()<kbin.size()) {
                kbin=kbin_l2; aloc=aloc_l2; 
                Ks = 1; 
                conts[0]+=1;
                contu = 0;
                ultima_melhoria = niter - cont;
            }
            else {
                kbin_l=kbin;  aloc_l=aloc;
                Ks += 1; 
                contu += 1;
            }   
        }
    }
    kbin_l=kbin; itens_l=itens;
    tit="VNS";   
    mostra_resultado(tit,det,result_heur_inic);
    for (int i=0;i<6;i++)  
        cout << "  Ks: " << i+1 << " " << cont_ks[i][0] << " " << cont_ks[i][1] << " " << cont_ks2[i];
    
    for (int i=0;i<4;i++)  
        cout << "  Ls: " << i+1 << " " << cont_ls[i][0] << " " << cont_ls[i][1];
    
    cout << " ultima_it_melhoria: " << ultima_melhoria; 
     
}

// Uso da ferramente:
// c:\> vns.exe instancia.txt mapa_conflitos.txt 500 
//              (instancia)    (conflitos)      (numero de iteracoes)

int main(int argc, char* argv[])
{
    string s;
    int n_it;
    s = argv[3];
    stringstream convert(s);
    convert >> n_it;
    int max_iter = 50;
    max_iter = n_it;
	le_instancia(argv[1],argv[2]);	
	ordena_itens();
    VNS(max_iter); 
    return 0;
}

// =============================================================================
// heuristicas_bpc4_comentado.cpp
//
// Resolucao do Bin Packing com Conflitos de Categorias (BPC) via VNS + VND
//
// Problema: alocar N itens em bins de capacidade C, minimizando o numero de
// bins utilizados, respeitando que certas categorias de itens NAO podem
// coexistir no mesmo bin.
//
// Abordagem:
//   1. Heuristica construtiva: Best Fit com verificacao de conflitos
//   2. Metaheuristica: Variable Neighborhood Search (VNS)
//      - 6 estruturas de vizinhanca para o Shaking (perturbacao)
//      - 4 estruturas de vizinhanca para a Busca Local (VND)
//
// Uso: ./bpc <instancia.txt> <conflitos.txt> <num_iteracoes>
//
// Formato da instancia:
//   linha 1: nome
//   linha 2: capacidade do bin
//   linha 3: numero de itens
//   linhas seguintes: id  loja  peso  categoria  (um item por linha)
//
// Formato do arquivo de conflitos:
//   linha 1: num_pares  num_categorias
//   linhas seguintes: cat_a  cat_b  (par de categorias que NAO conflitam)
// =============================================================================

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

// =============================================================================
// VARIAVEIS GLOBAIS
// =============================================================================

time_t now0 = time(0); // tempo de inicio da execucao (para medir tempo total)

// Estrutura que representa um bin (compartimento de armazenamento)
struct BIN {
    int cap_bin;        // capacidade total do bin
    int w_bin;          // peso total atualmente alocado no bin
    int rcap;           // capacidade residual (cap_bin - w_bin)
    int n_itens;        // numero de itens alocados no bin
    int ncats;          // numero de categorias distintas no bin
    vector<int> cats;   // lista das categorias presentes no bin
    vector<int> elems;  // lista dos indices dos itens alocados no bin
};

int nlc;                                      // numero de pares de categorias NAO conflitantes
vector<BIN> kbin, kbin_l, kbin_l2;           // tres copias da solucao:
                                              //   kbin   = melhor solucao global encontrada
                                              //   kbin_l = solucao corrente (sendo manipulada)
                                              //   kbin_l2= solucao intermediaria X' (apos shaking)

vector<vector<int>> confs;                    // lista de pares de categorias que NAO conflitam
vector<vector<int>> cat_vet;                  // lista de categorias com seu grau de conflito
                                              //   cat_vet[i] = [id_categoria, num_conflitos]
                                              //   ordenada por num_conflitos crescente

vector<vector<int>> itens, itens_l, itens_l2; // tres copias da lista de itens
                                              //   cada item: [id, loja, peso, categoria]
                                              //   (loja nao e utilizada na logica do algoritmo)

vector<int> aloc, aloc_l, aloc_l2;           // vetores de alocacao paralelos aos itens
                                              //   0 = item ainda nao alocado em nenhum bin
                                              //   1 = item ja alocado

string nome_inst;                             // nome da instancia lida do arquivo
int cap_bin, n_itens;                         // capacidade do bin e total de itens
int n_cats;                                   // numero de categorias distintas
int minimo = 9999999, maximo = 0, soma = 0;   // estatisticas dos pesos (min, max, soma)


// =============================================================================
// FUNCOES AUXILIARES DE COMPARACAO (usadas no sort)
// =============================================================================

// Compara pelo segundo elemento em ordem crescente
bool comp_elem2(const vector<int>& a, const vector<int>& b) { return a[1] < b[1]; }
// Compara pelo terceiro elemento em ordem crescente
bool comp_elem3(const vector<int>& a, const vector<int>& b) { return a[2] < b[2]; }
// Compara pelo segundo elemento em ordem decrescente
bool comp_elem2_inv(const vector<int>& a, const vector<int>& b) { return a[1] > b[1]; }
// Compara pelo terceiro elemento em ordem decrescente
bool comp_elem3_inv(const vector<int>& a, const vector<int>& b) { return a[2] > b[2]; }


// =============================================================================
// Conta o total de itens alocados em kbin_l (solucao corrente)
// =============================================================================
int n_itens_aloc() {
    int cont = 0;
    for (int j = 0; j < kbin_l.size(); j++)
        cont += kbin_l[j].elems.size();
    return cont;
}


// =============================================================================
// Remove todos os itens de uma categoria especifica de um bin especifico.
// Atualiza o peso, capacidade residual, lista de elementos e lista de categorias
// do bin. Os itens removidos sao marcados como nao alocados (aloc_l = 0).
//
// Parametros:
//   chosen_bin - indice do bin em kbin_l
//   catE       - categoria a ser removida do bin
// =============================================================================
void esvazia_BIN_cat(int chosen_bin, int catE) {
    int e1, wbin_temp = 0;
    vector<int> elems_temp;
    int b1 = chosen_bin;

    // Verifica se a categoria realmente existe no bin antes de agir
    if (find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), catE) != kbin_l[b1].cats.end()) {

        // Percorre os itens do bin: separa os que pertencem a catE dos que nao pertencem
        for (int j = 0; j < kbin_l[chosen_bin].elems.size(); j++) {
            e1 = kbin_l[chosen_bin].elems[j];
            if (itens_l[e1][3] == catE) {
                aloc_l[e1] = 0;              // devolve o item ao pool de nao alocados
                wbin_temp += itens_l[e1][2]; // acumula o peso que sera removido
            } else {
                elems_temp.push_back(e1);    // mantem os itens de outras categorias
            }
        }

        // Atualiza o bin com os itens restantes
        kbin_l[b1].elems = elems_temp;
        kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), catE));
        kbin_l[b1].w_bin -= wbin_temp;
        kbin_l[b1].rcap = cap_bin - kbin_l[b1].w_bin;
        kbin_l[b1].n_itens = kbin_l[b1].elems.size();
        kbin_l[b1].ncats = kbin_l[b1].cats.size();
    }
}


// =============================================================================
// Le os arquivos de entrada: instancia de itens e tabela de conflitos.
// Tambem inicializa cat_vet com a contagem de conflitos por categoria,
// ordenada do menos restritivo ao mais restritivo.
//
// Parametros:
//   input  - caminho do arquivo da instancia (itens)
//   input2 - caminho do arquivo de conflitos entre categorias
// =============================================================================
void le_instancia(char* input, char* input2) {
    int n1, n2, n3, n4;

    // --- Leitura da instancia de itens ---
    ifstream arq(input, ios::in);
    if (!arq) {
        cerr << "problema com o arquivo";
        exit(1);
    }

    arq >> nome_inst;  // nome da instancia
    arq >> cap_bin;    // capacidade de cada bin
    arq >> n_itens;    // numero total de itens

    for (int j = 0; j < n_itens; j++) {
        arq >> n1 >> n2 >> n3 >> n4;
        vector<int> nt;
        nt.push_back(n1); // [0] id do item
        nt.push_back(n2); // [1] loja (nao utilizada na logica)
        nt.push_back(n3); // [2] peso do item
        nt.push_back(n4); // [3] categoria do item
        aloc.push_back(0);
        itens.push_back(nt);

        // Rastreia peso minimo e maximo
        if (n3 > maximo) maximo = n3;
        if (n3 < minimo) minimo = n3;
    }
    arq.close();

    // --- Leitura do arquivo de conflitos ---
    // Formato: primeira linha = nlc (num pares) e n_cats (num categorias)
    // Linhas seguintes: pares de categorias que NAO conflitam entre si
    int n, n_cats;
    ifstream arq2(input2, ios::in);
    if (!arq2) {
        cerr << "problema com o arquivo de conflitos";
        exit(1);
    }
    arq2 >> nlc >> n_cats; // le cabecalho

    for (int j = 0; j < nlc; j++) {
        arq2 >> n1 >> n2;
        vector<int> nt;
        nt.push_back(n1);
        nt.push_back(n2);
        confs.push_back(nt); // armazena o par compativel
    }
    arq2.close();

    // --- Inicializa cat_vet: [id_categoria, num_conflitos] ---
    for (int j = 1; j <= n_cats; j++) {
        vector<int> temp;
        temp.push_back(j); // id da categoria
        temp.push_back(0); // contador de conflitos (sera preenchido abaixo)
        cat_vet.push_back(temp);
    }

    // Conta quantos pares de conflito cada categoria participa
    int cont;
    for (int j = 0; j < cat_vet.size(); j++) {
        cont = 0;
        for (int i = 0; i < nlc; i++) {
            if ((confs[i][0] == cat_vet[j][0]) || (confs[i][1] == cat_vet[j][0]))
                cont += 1;
        }
        cat_vet[j][1] = cont;
    }

    // Ordena categorias do menos restritivo (menos conflitos) para o mais restritivo
    sort(cat_vet.begin(), cat_vet.end(), comp_elem2);
}


// =============================================================================
// Reordena os itens priorizando as categorias mais restritivas e, dentro de
// cada categoria, os itens mais pesados primeiro.
// Isso melhora a qualidade da heuristica construtiva (Best Fit).
// =============================================================================
void ordena_itens() {
    itens_l.clear();
    aloc_l.clear();

    // Ordena todos os itens por peso decrescente
    sort(itens.begin(), itens.end(), comp_elem3_inv);

    // Reinsere os itens: primeiro as categorias mais restritivas (fim de cat_vet)
    for (int j = cat_vet.size(); j >= 1; j--)
        for (int i = 0; i < itens.size(); i++)
            if (itens[i][3] == cat_vet[j - 1][0]) {
                itens_l.push_back(itens[i]);
                aloc_l.push_back(0);
            }

    itens = itens_l;
    aloc = aloc_l;
}


// =============================================================================
// Verifica se duas categorias sao CONFLITANTES entre si.
// Retorna true se houver conflito (par NAO esta na lista de compativeis).
//
// Parametros:
//   a, b - ids das duas categorias a verificar
// =============================================================================
bool tem_conflito(int a, int b) {
    int menor, maior;
    if (a < b) { menor = a; maior = b; }
    else        { menor = b; maior = a; }

    // Busca o par na lista de pares compativeis
    for (int j = 0; j < nlc; j++)
        if ((confs[j][0] == menor) && (confs[j][1] == maior))
            return false; // encontrou: sao compativeis (sem conflito)

    return true; // nao encontrou: ha conflito
}


// =============================================================================
// Verifica se uma categoria pode ser inserida em um bin da solucao corrente
// sem gerar conflito com nenhuma das categorias ja presentes no bin.
//
// Parametros:
//   a   - categoria do item a ser inserido
//   bin - indice do bin em kbin_l
// Retorna true se NAO houver conflito (insercao e valida)
// =============================================================================
bool nao_conflito(int a, int bin) {
    for (int j = 0; j < kbin_l[bin].cats.size(); j++)
        if (tem_conflito(a, kbin_l[bin].cats[j]))
            return false; // conflito encontrado
    return true;
}


// =============================================================================
// Versao de nao_conflito que opera sobre uma copia local de BIN (nao sobre
// kbin_l). Usada nas buscas locais onde bins temporarios sao manipulados.
//
// Parametros:
//   a     - categoria do item a ser inserido
//   bincp - copia local do bin
// Retorna true se NAO houver conflito
// =============================================================================
bool nao_conflito_cpBIN(int a, BIN bincp) {
    for (int j = 0; j < bincp.cats.size(); j++)
        if (tem_conflito(a, bincp.cats[j]))
            return false;
    return true;
}


// =============================================================================
// Insere o item p em um bin ja existente (bin_ut) na solucao corrente.
// Atualiza peso, capacidade residual, lista de categorias e lista de itens.
//
// Parametros:
//   p      - indice do item em itens_l
//   bin_ut - indice do bin em kbin_l
// =============================================================================
int atualiza_bin(int p, int bin_ut) {
    kbin_l[bin_ut].w_bin += itens_l[p][2];
    kbin_l[bin_ut].cap_bin = cap_bin;
    kbin_l[bin_ut].rcap = cap_bin - itens_l[p][2];
    kbin_l[bin_ut].n_itens += 1;

    // Adiciona a categoria do item ao bin se ainda nao estiver presente
    if (find(kbin_l[bin_ut].cats.begin(), kbin_l[bin_ut].cats.end(), itens_l[p][3]) == kbin_l[bin_ut].cats.end()) {
        kbin_l[bin_ut].cats.push_back(itens_l[p][3]);
        kbin_l[bin_ut].ncats += 1;
    }
    kbin_l[bin_ut].elems.push_back(p);
    return 0;
}


// =============================================================================
// Cria um novo bin na solucao corrente ja com o item p alocado.
//
// Parametros:
//   p - indice do item em itens_l
// =============================================================================
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


// =============================================================================
// Exibe o resultado na saida padrao.
// Mostra: nome da instancia, capacidade, numero de bins inicial e final,
// itens alocados e tempo de execucao.
//
// Parametros:
//   titulo  - rotulo da heuristica (ex: "VNS")
//   detalhe - flag para exibicao detalhada (atualmente comentada)
//   inicial - numero de bins da heuristica construtiva (antes do VNS)
// =============================================================================
void mostra_resultado(string titulo, bool detalhe, int inicial) {
    int soma, cat1, e1, soma1, cont1;
    time_t now1 = time(0);
    cout << "\n" << titulo
         << "  Nome_Instancia " << nome_inst
         << "  Cap. " << cap_bin
         << "  N_Itens " << itens_l.size()
         << "  N_Bins_Inic " << inicial
         << " N_Bins_VNS " << kbin_l.size()
         << " Itens Alocados: " << n_itens_aloc()
         << " Tempo " << now1 - now0;
    // Detalhamento por bin (comentado para nao poluir saida)
    /*
    if (detalhe) { ... }
    */
}


// =============================================================================
// HEURISTICA CONSTRUTIVA: Best Fit com Conflito
//
// Para cada item ainda nao alocado, busca o bin com menor capacidade residual
// que comporte o item e nao gere conflito de categoria.
// Se nenhum bin existente for viavel, abre um novo bin.
//
// Parametro:
//   input - "1" para usar verificacao de conflito, "0" para ignorar conflitos
// Retorna o numero total de bins utilizados.
// =============================================================================
int best_fit_conflito(char* input) {
    int n_util, j_menor, cap_rest_menor, cap_rest, bin_ut;
    n_util = kbin_l.size();

    for (int p = 0; p < itens_l.size(); p++) { // percorre todos os itens
        if (aloc_l[p] == 0) {                  // processa apenas itens nao alocados
            j_menor = -1;
            cap_rest_menor = 99999;

            for (int j = 0; j < kbin_l.size(); j++) { // avalia cada bin existente
                cap_rest = cap_bin - kbin_l[j].w_bin;

                if (strcmp(input, "0") == 0) {
                    // Sem verificacao de conflito: apenas verifica capacidade
                    if ((cap_rest >= itens_l[p][2]) && (cap_rest < cap_rest_menor)) {
                        cap_rest_menor = cap_rest;
                        j_menor = j;
                    }
                } else {
                    // Com verificacao de conflito: bin deve ter espaco E ser compativel
                    if ((cap_rest >= itens_l[p][2]) && (cap_rest < cap_rest_menor) &&
                        nao_conflito(itens_l[p][3], j)) {
                        cap_rest_menor = cap_rest;
                        j_menor = j;
                    }
                }
            }

            if (j_menor > -1)
                atualiza_bin(p, j_menor); // aloca no melhor bin encontrado
            else {
                n_util++;
                adiciona_bin(p); // nenhum bin viavel: abre um novo
            }
            aloc_l[p] = 1; // marca item como alocado
        }
    }
    return kbin_l.size();
}


// =============================================================================
// SHAKING N1 - Perturbacao por categoria aleatoria nos bins mais cheios
//
// Escolhe aleatoriamente uma categoria dentre as mais restritivas (metade
// superior de cat_vet). Remove todos os itens dessa categoria nos 30% de bins
// com menor capacidade residual (mais cheios). Realoca os itens liberados.
//
// Objetivo: diversificar a solucao forcando a redistribuicao de uma categoria
// problemtica entre bins com pouco espaco livre.
// =============================================================================
void shaking_N1(float porc) {
    int e1, b1, n_cats_e;
    n_cats = cat_vet.size();

    // Ordena bins por capacidade residual crescente (mais cheios primeiro)
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin - kbin_l[i].w_bin);
        bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    srand(std::time(0));
    int nreleased = floor(porc * bins_ordenados.size()); // numero de bins a perturbar

    // Escolhe categoria aleatoria dentre as mais restritivas (metade superior)
    n_cats_e = floor(n_cats / 2);
    int chosen_cat = rand() % n_cats_e;
    chosen_cat = cat_vet[n_cats - chosen_cat - 1][0]; // indice real da categoria

    // Remove itens da categoria escolhida dos bins selecionados
    for (int i = 0; i < nreleased; i++) {
        b1 = bins_ordenados[i][0];
        vector<int> temp;
        bool achou = false;
        int ccat = 0;

        for (int j = 0; j < kbin_l[b1].elems.size(); j++) {
            e1 = kbin_l[b1].elems[j];
            if (itens_l[e1][3] == chosen_cat) {
                aloc_l[e1] = 0; // libera o item
                achou = true;
            } else {
                temp.push_back(e1);
                ccat++;
            }
        }

        if (ccat > 0)
            kbin_l[b1].elems = temp;
        else
            kbin_l[b1].elems.clear();

        // Remove a categoria do bin se ela nao tiver mais itens
        if ((achou) && (ccat > 0))
            if (find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat) != kbin_l[b1].cats.end())
                kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat));
    }

    // Remove bins que ficaram vazios apos a perturbacao
    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }

    // Realoca todos os itens liberados usando Best Fit com conflito
    char st[] = "1";
    best_fit_conflito(st);
}


// =============================================================================
// SHAKING N2 - Esvazia bins aleatorios
//
// Escolhe aleatoriamente 15% dos bins e os esvazia completamente.
// Realoca os itens liberados.
//
// Objetivo: diversificacao forte, forcando remontagem de parte da solucao.
// =============================================================================
void shaking_N2(float porc) {
    int e1;
    srand(std::time(0));
    int nreleased = floor(porc * kbin_l.size()); // numero de bins a esvaziar

    for (int cont = 0; cont < nreleased; cont++) {
        int chosen_bin = rand() % kbin_l.size();
        // Libera todos os itens do bin escolhido
        for (int j = 0; j < kbin_l[chosen_bin].elems.size(); j++) {
            e1 = kbin_l[chosen_bin].elems[j];
            aloc_l[e1] = 0;
        }
        kbin_l.erase(kbin_l.begin() + chosen_bin); // remove o bin da solucao
    }

    // Realoca todos os itens liberados
    char st[] = "1";
    best_fit_conflito(st);
}


// =============================================================================
// SHAKING N3 - Remove a categoria menos restritiva de todos os bins com mais
// de 2 categorias
//
// Percorre todos os bins e remove os itens da categoria com menos conflitos
// (cat_vet[0]) dos bins que contenham mais de 2 categorias distintas.
//
// Objetivo: reduzir a diversidade de categorias por bin, potencialmente
// liberando espaco para consolidacao.
// =============================================================================
void shaking_N3(float porc) {
    int e1, b1, n_cats_e;
    n_cats = cat_vet.size();

    // Ordena bins por capacidade residual crescente
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin - kbin_l[i].w_bin);
        bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    int nreleased = floor(porc * bins_ordenados.size());
    int chosen_cat = cat_vet[0][0]; // categoria menos restritiva

    for (int i = 0; i < nreleased; i++) {
        b1 = bins_ordenados[i][0];
        vector<int> temp;
        bool achou = false;
        int ccat = 0;

        // Aplica apenas em bins com mais de 2 categorias
        if (kbin_l[b1].cats.size() > 2) {
            for (int j = 0; j < kbin_l[b1].elems.size(); j++) {
                e1 = kbin_l[b1].elems[j];
                if (itens_l[e1][3] == chosen_cat) {
                    aloc_l[e1] = 0;
                    achou = true;
                } else {
                    temp.push_back(e1);
                    ccat++;
                }
            }

            if (ccat > 0)
                kbin_l[b1].elems = temp;
            else
                kbin_l[b1].elems.clear();

            if ((achou) && (ccat > 0))
                if (find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat) != kbin_l[b1].cats.end())
                    kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat));
        }
    }

    // Remove bins vazios
    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }

    char st[] = "1";
    best_fit_conflito(st);
}


// =============================================================================
// SHAKING N20 - Remove as DUAS categorias mais restritivas de todos os bins
// (funcao auxiliar, nao usada no VNS principal)
//
// Similar ao N3, mas remove as duas categorias com mais conflitos.
// =============================================================================
void shaking_N20(float porc) {
    int e1, b1, n_cats_e;
    n_cats = cat_vet.size();

    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin - kbin_l[i].w_bin);
        bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    int nreleased = floor(porc * bins_ordenados.size());

    // As duas categorias mais restritivas (final de cat_vet)
    int chosen_cat = cat_vet[cat_vet.size() - 1][0];
    int chosen_cat2 = (cat_vet.size() > 1) ? cat_vet[cat_vet.size() - 2][0] : chosen_cat;

    for (int i = 0; i < nreleased; i++) {
        b1 = bins_ordenados[i][0];
        vector<int> temp;
        bool achou = false;
        int ccat = 0;

        for (int j = 0; j < kbin_l[b1].elems.size(); j++) {
            e1 = kbin_l[b1].elems[j];
            if ((itens_l[e1][3] == chosen_cat) || (itens_l[e1][3] == chosen_cat2)) {
                aloc_l[e1] = 0;
                achou = true;
            } else {
                temp.push_back(e1);
                ccat++;
            }
        }

        if (ccat > 0)
            kbin_l[b1].elems = temp;
        else
            kbin_l[b1].elems.clear();

        if ((achou) && (ccat > 0)) {
            if (find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat) != kbin_l[b1].cats.end())
                kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat));
            if (find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat2) != kbin_l[b1].cats.end())
                kbin_l[b1].cats.erase(find(kbin_l[b1].cats.begin(), kbin_l[b1].cats.end(), chosen_cat2));
        }
    }

    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }

    char st[] = "1";
    best_fit_conflito(st);
}


// =============================================================================
// SHAKING N4 - Mantém apenas a categoria mais restritiva em cada bin com
// mais de 2 categorias, liberando todos os outros itens
//
// Para bins com mais de 2 categorias: remove todos os itens que NAO pertencem
// a categoria mais restritiva (cat_vet.back()), deixando o bin apenas com
// itens dessa categoria. Realoca os itens liberados.
//
// Objetivo: forcar bins "puros" para a categoria mais dificil de alocar,
// permitindo que os demais itens encontrem novos arranjos.
// =============================================================================
void shaking_N4(float porc) {
    int e1, b1, n_cats_e;
    n_cats = cat_vet.size();

    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin - kbin_l[i].w_bin);
        bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    int nreleased = floor(porc * bins_ordenados.size());
    int chosen_cat = cat_vet[cat_vet.size() - 1][0]; // categoria mais restritiva

    for (int i = 0; i < nreleased; i++) {
        b1 = bins_ordenados[i][0];
        vector<int> temp;
        bool achou = false;
        int ccat = 0;

        // Aplica apenas em bins com mais de 2 categorias
        if (kbin_l[b1].cats.size() > 2) {
            for (int j = 0; j < kbin_l[b1].elems.size(); j++) {
                e1 = kbin_l[b1].elems[j];
                if (itens_l[e1][3] != chosen_cat) {
                    aloc_l[e1] = 0; // libera tudo que NAO e a categoria mais restritiva
                    achou = true;
                } else {
                    temp.push_back(e1);
                    ccat++;
                }
            }

            if (ccat > 0)
                kbin_l[b1].elems = temp;
            else
                kbin_l[b1].elems.clear();

            // Atualiza a lista de categorias do bin para conter apenas a mais restritiva
            kbin_l[b1].cats.clear();
            kbin_l[b1].cats.push_back(chosen_cat);
        }
    }

    // Remove bins vazios
    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }

    char st[] = "1";
    best_fit_conflito(st);
}


// =============================================================================
// SHAKING N5 - Esvazia os bins mais cheios
//
// Ordena os bins por capacidade residual crescente (mais cheios primeiro) e
// esvazia os primeiros 15%. Realoca os itens liberados.
//
// Objetivo: forcar redistribuicao dos bins mais saturados, que sao os que
// mais limitam a consolidacao da solucao.
// =============================================================================
void shaking_N5(float porc) {
    int e1;

    // Ordena bins por capacidade residual crescente (mais cheios primeiro)
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(cap_bin - kbin_l[i].w_bin);
        bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    int nreleased = floor(porc * kbin_l.size());

    for (int cont = 0; cont < nreleased; cont++) {
        int chosen_bin = bins_ordenados[cont][0];
        // Libera todos os itens do bin
        for (int j = 0; j < kbin_l[chosen_bin].elems.size(); j++) {
            e1 = kbin_l[chosen_bin].elems[j];
            aloc_l[e1] = 0;
        }
        kbin_l[chosen_bin].elems.clear();
    }

    // Remove bins vazios
    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }

    char st[] = "1";
    best_fit_conflito(st);
}


// =============================================================================
// SHAKING N6 - Consolidacao forcada de bins com uma unica categoria
//
// Encontra o bin mais leve que possua apenas uma categoria. Esvazia esse bin
// e tenta consolidar: para cada outro bin que tambem contenha aquela categoria
// (e tenha mais de uma categoria), remove as outras categorias desse bin para
// abrir espaco. Realoca tudo com Best Fit.
//
// Objetivo: eliminar bins "sobrando" que so tem uma categoria, promovendo
// fusoes entre bins compativeis.
// =============================================================================
void shaking_N6() {
    int e1, e2, binx, cat_e, ordem_bin_e, ordem_bin_e1, e11, e3;

    // Ordena bins por peso crescente (mais leves primeiro)
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    // Encontra o primeiro bin (mais leve) que possui apenas 1 categoria
    bool achou = false;
    for (int i = 0; i < bins_ordenados.size(); i++) {
        ordem_bin_e = i;
        e1 = bins_ordenados[i][0];
        if (kbin_l[e1].cats.size() == 1) {
            cat_e = kbin_l[e1].cats[0];
            achou = true;
            break;
        }
    }

    // Esvazia esse bin (libera todos os seus itens)
    esvazia_BIN_cat(e1, cat_e);

    // Para cada bin mais pesado que tambem contenha cat_e e tenha mais de 1 categoria:
    // remove as outras categorias desse bin para tentar abrir espaco para consolidacao
    for (int k = ordem_bin_e + 1; k < bins_ordenados.size(); k++) {
        e2 = bins_ordenados[k][0];
        vector<int> temp_cats;
        if ((kbin_l[e2].cats.size() > 1) &&
            (find(kbin_l[e2].cats.begin(), kbin_l[e2].cats.end(), cat_e) != kbin_l[e2].cats.end())) {
            // Coleta as outras categorias (nao cat_e)
            for (int j = 0; j < kbin_l[e2].cats.size(); j++)
                if (kbin_l[e2].cats[j] != cat_e)
                    temp_cats.push_back(kbin_l[e2].cats[j]);
            // Remove essas categorias do bin
            if (temp_cats.size() > 0)
                for (int j = 0; j < temp_cats.size(); j++)
                    esvazia_BIN_cat(e2, temp_cats[j]);
        }
    }

    // Remove bins que ficaram vazios
    vector<BIN> kbin_temp;
    for (int t = 0; t < kbin_l.size(); t++)
        if (kbin_l[t].elems.size() > 0)
            kbin_temp.push_back(kbin_l[t]);
    kbin_l = kbin_temp;

    // Realoca todos os itens liberados
    char st[] = "1";
    best_fit_conflito(st);
}


// =============================================================================
// BUSCA LOCAL N1 - Relocacao por peso (mover itens do bin mais leve para o
// mais pesado)
//
// Ordena os bins por peso crescente. Para cada par (bin leve, bin pesado),
// tenta mover itens do bin leve para o bin pesado, respeitando capacidade e
// conflitos. Aceita o movimento se o bin de destino ganhou peso (ficou mais
// cheio), favorecendo a consolidacao. Para na primeira melhora encontrada.
//
// Objetivo: esvaziar bins leves para reduzir o total de bins utilizados.
// =============================================================================
void BuscaLocalN1() {
    int e1, e2;

    // Monta lista de bins nao cheios, ordenados por peso crescente
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        if (kbin_l[i].w_bin < cap_bin)
            bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    if (bins_ordenados.size() < 2) return;

    // Gera todos os pares (bin_leve, bin_pesado)
    vector<vector<int>> pares;
    for (int i = 0; i < bins_ordenados.size() - 1; i++) {
        e1 = bins_ordenados[i][0];
        for (int j = bins_ordenados.size() - 1; j > i; j--) {
            e2 = bins_ordenados[j][0];
            vector<int> temp;
            temp.push_back(e1); // bin leve (candidato a esvaziar)
            temp.push_back(e2); // bin pesado (candidato a receber itens)
            pares.push_back(temp);
        }
    }

    for (int i = 0; i < pares.size(); i++) {
        e1 = pares[i][0]; // bin leve
        e2 = pares[i][1]; // bin pesado
        BIN bin1 = kbin_l[e1];
        BIN bin2 = kbin_l[e2];

        if (bin1.elems.size() > 0) {
            // Tenta mover cada item do bin leve para o bin pesado
            for (int j = 0; j < kbin_l[e1].elems.size(); j++) {
                int elemA = kbin_l[e1].elems[j];
                int catA = itens_l[elemA][3];
                int w_A = itens_l[elemA][2];

                // Verifica se o item cabe e e compativel com o bin destino
                if ((nao_conflito_cpBIN(catA, bin2)) && ((bin2.w_bin + w_A) <= cap_bin)) {
                    // Move o item: retira do bin1 e coloca no bin2
                    bin2.w_bin += w_A;
                    bin1.w_bin -= w_A;
                    bin1.elems.erase(find(bin1.elems.begin(), bin1.elems.end(), elemA));
                    bin2.elems.push_back(elemA);

                    // Atualiza lista de categorias do bin destino
                    bool achou = false;
                    for (int k = 0; k < bin2.cats.size(); k++)
                        if (catA == bin2.cats[k]) { achou = true; break; }
                    if (!achou) bin2.cats.push_back(catA);

                    // Remove a categoria do bin origem se era o unico item dela
                    int ccatA = 0;
                    for (int k = 0; k < bin1.elems.size(); k++)
                        if (itens_l[bin1.elems[k]][3] == catA) ccatA++;
                    if (ccatA == 1)
                        bin1.cats.erase(find(bin1.cats.begin(), bin1.cats.end(), catA));

                    // Atualiza metadados dos bins
                    bin1.rcap = cap_bin - bin1.w_bin;
                    bin1.n_itens = bin1.elems.size();
                    bin1.ncats = bin1.cats.size();
                    bin2.rcap = cap_bin - bin2.w_bin;
                    bin2.n_itens = bin2.elems.size();
                    bin2.ncats = bin2.cats.size();
                }
            }

            // Aceita o movimento se o bin de destino ficou mais pesado (houve transferencia)
            if (bin2.w_bin > kbin_l[e2].w_bin) {
                kbin_l[e1] = bin1;
                kbin_l[e2] = bin2;
                break; // para na primeira melhora
            }
        }
    }

    // Remove bins que ficaram vazios apos a relocacao
    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
}


// =============================================================================
// BUSCA LOCAL N2 - Relocacao por numero de categorias
//
// Identica a BuscaLocalN1 na logica de movimentacao de itens, mas ordena os
// bins pelo numero de categorias (crescente) em vez de pelo peso.
// Aceita o movimento se a capacidade residual do bin destino diminuiu.
//
// Objetivo: esvaziar bins com poucas categorias (menos diversidade de itens),
// que sao candidatos mais faceis de serem eliminados.
// =============================================================================
void BuscaLocalN2() {
    int e1, e2;

    // Monta lista de bins nao cheios, ordenados por numero de categorias crescente
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].cats.size()); // ordena por num categorias
        if (kbin_l[i].w_bin < cap_bin)
            bins_ordenados.push_back(temp);
    }
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);
    if (bins_ordenados.size() < 2) return;

    // Gera todos os pares (bin com poucas cats, bin com muitas cats)
    vector<vector<int>> pares;
    for (int i = 0; i < bins_ordenados.size() - 1; i++) {
        e1 = bins_ordenados[i][0];
        for (int j = bins_ordenados.size() - 1; j > i; j--) {
            e2 = bins_ordenados[j][0];
            vector<int> temp;
            temp.push_back(e1);
            temp.push_back(e2);
            pares.push_back(temp);
        }
    }

    for (int i = 0; i < pares.size(); i++) {
        e1 = pares[i][0];
        e2 = pares[i][1];
        BIN bin1 = kbin_l[e1];
        BIN bin2 = kbin_l[e2];

        if (bin1.elems.size() > 0) {
            for (int j = 0; j < kbin_l[e1].elems.size(); j++) {
                int elemA = kbin_l[e1].elems[j];
                int catA = itens_l[elemA][3];
                int w_A = itens_l[elemA][2];

                if ((nao_conflito_cpBIN(catA, bin2)) && ((bin2.w_bin + w_A) <= cap_bin)) {
                    bin2.w_bin += w_A;
                    bin1.w_bin -= w_A;
                    bin1.elems.erase(find(bin1.elems.begin(), bin1.elems.end(), elemA));
                    bin2.elems.push_back(elemA);

                    bool achou = false;
                    for (int k = 0; k < bin2.cats.size(); k++)
                        if (catA == bin2.cats[k]) { achou = true; break; }
                    if (!achou) bin2.cats.push_back(catA);

                    int ccatA = 0;
                    for (int k = 0; k < bin1.elems.size(); k++)
                        if (itens_l[bin1.elems[k]][3] == catA) ccatA++;
                    if (ccatA == 1)
                        bin1.cats.erase(find(bin1.cats.begin(), bin1.cats.end(), catA));

                    bin1.rcap = cap_bin - bin1.w_bin;
                    bin1.n_itens = bin1.elems.size();
                    bin1.ncats = bin1.cats.size();
                    bin2.rcap = cap_bin - bin2.w_bin;
                    bin2.n_itens = bin2.elems.size();
                    bin2.ncats = bin2.cats.size();
                }
            }

            // Aceita se a capacidade residual do destino diminuiu (ficou mais cheio)
            if (bin2.rcap < kbin_l[e1].rcap) {
                kbin_l[e1] = bin1;
                kbin_l[e2] = bin2;
                break;
            }
        }
    }

    // Remove bins vazios
    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
}


// =============================================================================
// BUSCA LOCAL N3 - Relocacao com funcao objetivo quadratica
//
// Para cada bin (do mais leve ao mais pesado) e para cada item nele contido,
// busca o bin destino que maximize o ganho na funcao:
//
//   Delta = (w1 - wA)^2 + (w2 + wA)^2 - w1^2 - w2^2
//
// onde w1 = peso do bin origem, w2 = peso do bin destino, wA = peso do item.
// Maximizar essa expressao equivale a maximizar a soma dos quadrados dos pesos,
// o que favorece bins mais cheios (concentracao de carga = menos bins).
//
// Move o item para o melhor destino encontrado e continua (nao para na 1a melhora).
// =============================================================================
void BuscaLocalN3() {
    int e1, e2, maior_obj, obj_temp, e2_e1;

    // Monta lista de bins nao cheios, ordenados por peso crescente
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        if (kbin_l[i].w_bin < cap_bin)
            bins_ordenados.push_back(temp);
    }
    if (bins_ordenados.size() < 2) return;
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    for (int i = 0; i < bins_ordenados.size() - 1; i++) {
        e1 = bins_ordenados[i][0];
        BIN bin1, bin11 = kbin_l[e1];

        for (int j = 0; j < kbin_l[e1].elems.size(); j++) {
            int elemA = kbin_l[e1].elems[j];
            int catA = itens_l[elemA][3];
            int w_A = itens_l[elemA][2];

            maior_obj = 0;

            // Para cada bin destino possivel, calcula o delta da funcao quadratica
            for (int k = i + 1; k < bins_ordenados.size(); k++) {
                e2 = bins_ordenados[k][0];
                BIN bin2 = kbin_l[e2];

                if ((nao_conflito_cpBIN(catA, bin2)) && ((bin2.w_bin + w_A) <= cap_bin)) {
                    // Delta = ganho na soma dos quadrados ao mover elemA de bin11 para bin2
                    obj_temp = pow(bin11.w_bin - w_A, 2) + pow(bin2.w_bin + w_A, 2)
                             - pow(bin11.w_bin, 2) - pow(bin2.w_bin, 2);
                    if (obj_temp > maior_obj) {
                        maior_obj = obj_temp;
                        e2_e1 = e2; // melhor bin destino encontrado ate agora
                    }
                }
            }

            // Se encontrou um destino melhor, executa o movimento
            if (maior_obj > 0) {
                bin11.elems.erase(find(bin11.elems.begin(), bin11.elems.end(), elemA));
                BIN bin2 = kbin_l[e2_e1];
                bin2.elems.push_back(elemA);

                // Atualiza categorias do bin destino
                if (find(bin2.cats.begin(), bin2.cats.end(), catA) == bin2.cats.end())
                    bin2.cats.push_back(catA);

                // Remove categoria do bin origem se era o ultimo item dela
                int ccatA = 0;
                for (int k = 0; k < bin11.elems.size(); k++)
                    if (itens_l[bin11.elems[k]][3] == catA) ccatA++;
                if (ccatA == 1)
                    bin11.cats.erase(find(bin11.cats.begin(), bin11.cats.end(), catA));

                // Atualiza pesos e metadados
                bin2.w_bin += w_A;
                bin11.w_bin -= w_A;
                bin11.rcap = cap_bin - bin11.w_bin;
                bin11.n_itens = bin11.elems.size();
                bin11.ncats = bin11.cats.size();
                bin2.rcap = cap_bin - bin2.w_bin;
                bin2.n_itens = bin2.elems.size();
                bin2.ncats = bin2.cats.size();

                kbin_l[e2_e1] = bin2; // aplica mudanca no bin destino imediatamente
            }
        }
        kbin_l[e1] = bin11; // aplica mudancas no bin origem
    }
    // Nota: bins vazios nao sao removidos aqui (tratado em outras etapas)
}


// =============================================================================
// BUSCA LOCAL N4 - Troca de itens entre bins (swap) com funcao quadratica
//
// Para cada par de bins (bin1, bin2) e para cada par de itens (elemA em bin1,
// elemB em bin2), avalia a troca dos dois itens usando a funcao:
//
//   Delta = (w1 - wA + wB)^2 + (w2 + wA - wB)^2 - w1^2 - w2^2
//
// Executa a troca que maximiza esse delta, se for positivo.
// Diferente das buscas de relocacao, aqui dois itens sao trocados de lugar
// simultaneamente, respeitando capacidade e conflitos em ambos os bins.
// =============================================================================
void BuscaLocalN4() {
    int e1, e2, maior_obj, obj_temp, e2_e1, elemB_e, catB_e, w_B_e, posB_e;
    BIN bin2;

    // Monta lista de bins nao cheios, ordenados por peso crescente
    vector<vector<int>> bins_ordenados;
    for (int i = 0; i < kbin_l.size(); i++) {
        vector<int> temp;
        temp.push_back(i);
        temp.push_back(kbin_l[i].w_bin);
        if (kbin_l[i].w_bin < cap_bin)
            bins_ordenados.push_back(temp);
    }
    if (bins_ordenados.size() < 2) return;
    sort(bins_ordenados.begin(), bins_ordenados.end(), comp_elem2);

    for (int i = 0; i < bins_ordenados.size() - 1; i++) {
        e1 = bins_ordenados[i][0];
        BIN bin1 = kbin_l[e1];

        for (int j = 0; j < kbin_l[e1].elems.size(); j++) {
            int elemA = kbin_l[e1].elems[j];
            int posA = j;
            int catA = itens_l[elemA][3];
            int w_A = itens_l[elemA][2];

            maior_obj = 0;

            // Avalia todos os possiveis parceiros de troca em bins mais pesados
            for (int k = i + 1; k < bins_ordenados.size(); k++) {
                e2 = bins_ordenados[k][0];
                bin2 = kbin_l[e2];

                for (int p = 0; p < kbin_l[e2].elems.size(); p++) {
                    int elemB = kbin_l[e2].elems[p];
                    int posB = p;
                    int catB = itens_l[elemB][3];
                    int w_B = itens_l[elemB][2];

                    // Verifica viabilidade da troca nos dois sentidos
                    if (((nao_conflito_cpBIN(catA, bin2)) && ((bin2.w_bin + w_A) <= cap_bin)) &&
                        ((nao_conflito_cpBIN(catB, bin1)) && ((bin1.w_bin + w_B) <= cap_bin))) {

                        // Delta da funcao quadratica para a troca
                        obj_temp = pow(bin1.w_bin - w_A + w_B, 2) + pow(bin2.w_bin + w_A - w_B, 2)
                                 - pow(bin1.w_bin, 2) - pow(bin2.w_bin, 2);

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

            // Executa a melhor troca encontrada para este elemA
            if (maior_obj > 0) {
                bin2 = kbin_l[e2_e1];

                // Atualiza lista de categorias do bin1: remove catA se era unico, adiciona catB
                int ccatA = 0;
                for (int k = 0; k < bin1.elems.size(); k++)
                    if (itens_l[bin1.elems[k]][3] == catA) ccatA++;
                if (ccatA == 1)
                    bin1.cats.erase(find(bin1.cats.begin(), bin1.cats.end(), catA));

                // Atualiza lista de categorias do bin2: remove catB se era unico, adiciona catA
                ccatA = 0;
                for (int k = 0; k < bin2.elems.size(); k++)
                    if (itens_l[bin2.elems[k]][3] == catB_e) ccatA++;
                if (ccatA == 1)
                    bin2.cats.erase(find(bin2.cats.begin(), bin2.cats.end(), catB_e));

                if (find(bin2.cats.begin(), bin2.cats.end(), catA) == bin2.cats.end())
                    bin2.cats.push_back(catA);
                if (find(bin1.cats.begin(), bin1.cats.end(), catB_e) == bin1.cats.end())
                    bin1.cats.push_back(catB_e);

                // Troca os itens nas listas de elementos
                bin1.elems[posA] = elemB_e;
                bin2.elems[posB_e] = elemA;

                // Atualiza pesos e metadados
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

    // Remove bins que ficaram vazios
    bool achou = false;
    for (int i = 0; i < kbin_l.size(); i++)
        if (kbin_l[i].elems.size() == 0) { achou = true; break; }
    vector<BIN> kbin_temp;
    if (achou) {
        for (int i = 0; i < kbin_l.size(); i++)
            if (kbin_l[i].elems.size() > 0)
                kbin_temp.push_back(kbin_l[i]);
        kbin_l = kbin_temp;
    }
}


// =============================================================================
// VNS - Variable Neighborhood Search
//
// Metaheuristica principal. Combina perturbacao (shaking) com busca local
// (VND - Variable Neighborhood Descent).
//
// Estrutura geral:
//
//   solucao_inicial <- best_fit_conflito()
//
//   enquanto iteracoes > 0:
//       para Ks = 1..6  (vizinhancas de shaking):
//           aplica shaking_Ks(solucao_atual) -> X'
//
//           para Ls = 1..4  (vizinhancas de busca local - VND):
//               aplica BuscaLocalLs(X') -> X''
//               se X'' melhor que X':
//                   X' <- X''
//                   Ls = 1       (reinicia VND na melhor vizinhanca)
//               senao:
//                   Ls += 1      (tenta proxima vizinhanca)
//
//           se X' melhor que solucao_atual:
//               solucao_atual <- X'
//               Ks = 1           (reinicia shaking)
//           senao:
//               Ks += 1          (tenta proxima perturbacao)
//
// Ao final, exibe estatisticas de uso de cada Ks e Ls e a iteracao da
// ultima melhoria.
//
// Parametro:
//   niter - numero total de iteracoes (decrementado a cada avaliacao de busca local)
// =============================================================================
void VNS(int niter) {
    int conts[2] = {0};
    vector<vector<int>> results;
    float porc;
    int Ks, Ls, contu, contu_max = floor(niter / 2);
    bool det = true;

    // Contadores de chamadas e sucessos para cada vizinhanca
    int cont_ks[6][2], cont_ls[5][2]; // [vizinhanca][0=total chamadas, 1=melhorias]
    int cont_ks2[6];                   // melhorias de busca local atribuidas a cada Ks
    int ultima_melhoria = niter;       // iteracao em que ocorreu a ultima melhoria

    string tit;

    // Inicializa a solucao corrente com copias da base
    kbin_l = kbin;
    aloc_l = aloc;
    itens_l = itens;

    // --- Heuristica Construtiva Inicial: Best Fit com Conflito ---
    char st[] = "1";
    int a = best_fit_conflito(st);
    int result_heur_inic = kbin_l.size();

    // Salva a solucao inicial como melhor conhecida
    kbin = kbin_l;
    aloc = aloc_l;

    int cont = niter;
    contu = 0;
    int n_dep = 0, n_ant = 0;

    // Inicializa contadores de estatisticas
    for (int i = 0; i < 6; i++) { cont_ks[i][0] = 0; cont_ks[i][1] = 0; }
    for (int i = 0; i < 6; i++)    cont_ks2[i] = 0;
    for (int i = 0; i < 4; i++) { cont_ls[i][0] = 0; cont_ls[i][1] = 0; }

    // === LOOP PRINCIPAL DO VNS ===
    while (cont > 0) {
        Ks = 1;
        while ((Ks < 7) && (cont > 0)) {

            n_ant = kbin_l.size();

            // --- SHAKING: perturba a solucao atual com a vizinhanca Ks ---
            switch (Ks) {
                case 1: porc = 0.30; shaking_N1(porc); break; // perturba bins mais cheios (cat. aleatoria)
                case 2: porc = 0.15; shaking_N2(porc); break; // esvazia bins aleatorios
                case 3: porc = 1.00; shaking_N3(porc); break; // remove cat. menos restritiva
                case 4: porc = 1.00; shaking_N4(porc); break; // mantem apenas cat. mais restritiva
                case 5: porc = 0.15; shaking_N5(porc); break; // esvazia bins mais cheios
                case 6:              shaking_N6();      break; // consolida bins de uma categoria
            }

            n_dep = kbin_l.size();
            cont_ks[Ks - 1][0] += 1;
            if (n_dep < n_ant) cont_ks[Ks - 1][1] += 1;

            // X' = melhor entre solucao apos shaking e melhor global atual
            if (kbin_l.size() <= kbin.size())
                { kbin_l2 = kbin_l; aloc_l2 = aloc_l; } // shaking melhorou: usa X' novo
            else
                { kbin_l2 = kbin;   aloc_l2 = aloc;   } // shaking piorou: volta para melhor global

            // --- BUSCA LOCAL (VND): refina X' com ate 4 vizinhancas ---
            Ls = 1;
            while ((Ls < 5) && (cont > 0)) {
                n_ant = kbin_l.size();

                switch (Ls) {
                    case 1: BuscaLocalN1(); break; // relocacao por peso
                    case 2: BuscaLocalN2(); break; // relocacao por num. categorias
                    case 3: BuscaLocalN3(); break; // relocacao com funcao quadratica
                    case 4: BuscaLocalN4(); break; // swap com funcao quadratica
                }

                n_dep = kbin_l.size();
                cont_ls[Ls - 1][0] += 1;
                if (n_dep < n_ant) { cont_ls[Ls - 1][1] += 1; cont_ks2[Ks - 1] += 1; }

                // Registra historico para analise
                vector<int> temp;
                temp.push_back(cont);
                temp.push_back(Ks);
                temp.push_back(Ls);
                temp.push_back(kbin.size());    // melhor global antes
                temp.push_back(kbin_l2.size()); // X' apos shaking
                temp.push_back(kbin_l.size());  // X'' apos busca local
                results.push_back(temp);

                // Aceita X'' se melhorou X'; reinicia VND. Senao, tenta proxima vizinhanca.
                if (kbin_l.size() < kbin_l2.size()) {
                    kbin_l2 = kbin_l; aloc_l2 = aloc_l;
                    Ls = 1; // reinicia VND
                    ultima_melhoria = niter - cont;
                } else {
                    kbin_l = kbin_l2; aloc_l = aloc_l2;
                    Ls += 1; // tenta proxima vizinhanca
                }

                cont -= 1; // consome uma iteracao
            }

            // Apos VND: aceita X' se melhorou a melhor solucao global
            if (kbin_l2.size() < kbin.size()) {
                kbin = kbin_l2; aloc = aloc_l2;
                Ks = 1;   // reinicia shaking
                conts[0] += 1;
                contu = 0;
                ultima_melhoria = niter - cont;
            } else {
                kbin_l = kbin; aloc_l = aloc;
                Ks += 1;  // tenta proxima perturbacao
                contu += 1;
            }
        }
    }

    // Restaura a melhor solucao encontrada para exibicao
    kbin_l = kbin;
    itens_l = itens;

    // --- Exibe resultado e estatisticas ---
    tit = "VNS";
    mostra_resultado(tit, det, result_heur_inic);

    // Estatisticas por vizinhanca de shaking: total de chamadas, melhorias diretas, melhorias via BL
    for (int i = 0; i < 6; i++)
        cout << "  Ks: " << i + 1 << " " << cont_ks[i][0] << " " << cont_ks[i][1] << " " << cont_ks2[i];

    // Estatisticas por vizinhanca de busca local: total de chamadas, melhorias
    for (int i = 0; i < 4; i++)
        cout << "  Ls: " << i + 1 << " " << cont_ls[i][0] << " " << cont_ls[i][1];

    cout << " ultima_it_melhoria" << ultima_melhoria;
}


// =============================================================================
// MAIN
//
// Uso: ./bpc <instancia.txt> <conflitos.txt> <num_iteracoes>
//
// argv[1] - arquivo da instancia (itens: id, loja, peso, categoria)
// argv[2] - arquivo de conflitos (pares de categorias nao conflitantes)
// argv[3] - numero de iteracoes do VNS
// =============================================================================
int main(int argc, char* argv[]) {
    string s;
    int n_it;
    s = argv[3];
    stringstream convert(s);
    convert >> n_it;

    int max_iter = n_it;

    le_instancia(argv[1], argv[2]);

    VNS(max_iter);

    return 0;
}

# VNS for the Bin Packing Problem with Compatible Categories (BPCC)

A C++ implementation of a **Variable Neighborhood Search (VNS)** metaheuristic to solve the **Bin Packing Problem with Compatible Categories (BPCC)** — a variant of the classic Bin Packing Problem where items are classified into categories and certain categories cannot coexist in the same bin.

---

## 📄 Reference Article

This implementation is based on the following peer-reviewed paper, of which I am a co-author:

> Santos, L.F.O.M., Iwayama, R.S., Cavalcanti, L.B., Turi, L.M., Morais, F.E.S., Mormilho, G., & Cunha, C.B. (2019).
> **A variable neighborhood search algorithm for the bin packing problem with compatible categories.**
> *Expert Systems With Applications*, 124, 209–225.
> https://doi.org/10.1016/j.eswa.2019.01.052

The article PDF is included in this repository for reference.

> ⚠️ **Note:** Although I am one of the authors of the article, the implementation available in this repository **differs in some aspects** from the algorithm described in the paper. Specifically, the shaking and local search neighborhood structures, as well as the VNS control logic, were adapted and extended beyond what is formally described in the publication.

---


## 🧩 Problem Description

The **BPCC** arises in the context of last-mile distribution to small retail stores (*nanostores*). Items from different product categories (e.g., food, cleaning products, tobacco) must be loaded into vehicles (bins) of limited capacity. Certain category pairs are **incompatible** and cannot share the same vehicle, due to risks such as cross-contamination or damage.

The goal is to **minimize the number of bins (vehicles)** used to pack all items, while respecting:
- Bin capacity constraints
- Category compatibility constraints

---

## ⚙️ Algorithm Overview

### Constructive Heuristic
A **Best Fit with Conflict Check (BFCD)**: items are inserted into the bin with the smallest residual capacity that still fits the item and has no category conflict. Items are pre-sorted by category restrictiveness (most constrained first) and by weight (heaviest first within each category).

### VNS + VND Structure

```
Initial solution ← BFCD()

while iterations > 0:
    for Ks = 1..6  (shaking neighborhoods):
        apply Shaking_Ks(current_solution) → X'
        
        for Ls = 1..4  (local search - VND):
            apply LocalSearch_Ls(X') → X''
            if X'' improves X':
                X' ← X''
                restart VND (Ls = 1)
            else:
                Ls += 1
        
        if X' improves best solution:
            best ← X'
            restart shaking (Ks = 1)
        else:
            Ks += 1
```

### Shaking Neighborhoods (Perturbation)
| # | Description |
|---|-------------|
| N1 | Remove items of a random restrictive category from the 30% most loaded bins |
| N2 | Randomly empty 15% of bins |
| N3 | Remove the least restrictive category from all bins with more than 2 categories |
| N4 | Keep only the most restrictive category in each bin with more than 2 categories |
| N5 | Empty the 15% most loaded bins |
| N6 | Force consolidation of bins that contain only one category |

### Local Search Neighborhoods (VND)
| # | Description |
|---|-------------|
| L1 | Relocation sorted by bin weight — move items from lighter to heavier bins |
| L2 | Relocation sorted by number of categories |
| L3 | Relocation using a quadratic objective function (maximizes Σw²) |
| L4 | Item swap between bins using the same quadratic objective |

---

## 🗃️ Input File Formats

### Instance file (`*.txt`)
```
<instance_name>
<bin_capacity>
<number_of_items>
<id> <store> <weight> <category>
...
```

Example:
```
P-n23-k8
40
113
1 2 2 1
2 2 2 2
...
```

> The `store` field is present in the file format (inherited from VRP benchmark instances) but is **not used** by the algorithm.

### Compatibility file (`nao_confl.txt`)
```
<num_pairs> <num_categories>
<cat_a> <cat_b>
...
```

Each pair `(cat_a, cat_b)` represents two categories that are **compatible** (i.e., can share the same bin). Category pairs **not listed** are considered conflicting.

Example:
```
20 6
1 1
1 3
2 2
...
```

---

## 🚀 How to Compile and Run

### Requirements
- Linux/macOS (or WSL on Windows)
- `g++` compiler

### Install compiler (Ubuntu/Debian)
```bash
sudo apt update
sudo apt install g++
```

### Compile
```bash
g++ -O2 heuristicas_bpc4_comentado.cpp -o bpc -lm
```

### Run
```bash
./bpc <instance_file> <compatibility_file> <num_iterations>
```

Example:
```bash
./bpc P-n23-k8.txt nao_confl.txt 100
```

### Save output to file
```bash
./bpc P-n23-k8.txt nao_confl.txt 100 > result.txt
```

---

## 📦 Benchmark Instances

A ZIP archive (`BPCC_Instances.zip`) containing dozens of benchmark instances is included in this repository. These instances were derived from the augmented Non-IRUP (ANI) and augmented IRUP (AI) BPP benchmark sets proposed by Delorme et al. (2016), adapted for the BPCC with 6 and 8 product categories and varying bin capacity factors (100%, 120%, 150%, 200%).

Instance naming follows the convention `P-nXX-kY`, where `XX` is the number of nodes (stores) and `Y` is a reference vehicle count from the original VRP dataset.

---

## 📊 Sample Output

```
VNS  Nome_Instancia P-n23-k8  Cap. 40  N_Itens 113  N_Bins_Inic 22 N_Bins_VNS 19  Itens Alocados: 113  Tempo 2
  Ks: 1 45 12 8  Ks: 2 30 7 5  ...
  Ls: 1 120 34  Ls: 2 98 21  ...
  ultima_it_melhoria 67
```

Fields:
- `N_Bins_Inic` — number of bins from the constructive heuristic
- `N_Bins_VNS` — number of bins after VNS optimization
- `Itens Alocados` — total items successfully packed
- `Ks`/`Ls` statistics — calls and improvements per neighborhood
- `ultima_it_melhoria` — iteration at which the last improvement occurred

---

## 📜 License

This code is made available for academic and research purposes. If you use it in your work, please cite the reference article above.

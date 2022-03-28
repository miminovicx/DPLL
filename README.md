# DPLL
Implementation d'un solveur DPLL récursif en
OCaml.
---
# Instructions d'execution
Sur une machine disposant d'OCaml et de ocaml-findlib, se placer à la racine du projet et executer dans un premier temps ```make``` afin de générer l'executable puis lancer ```./dpll path/namefile.cnf``` tel que path/namefile.cnf représente le fichier DIMACS sur lequel on veut lancer. Des fichiers de tests sont disponibles dans le dossier tests/.
Exemple : ```./dpll tests/sudoku-4x4.cnf```

(* Trabalho de Semântica Formal 

Objetivo: implementar em OCaml um interpretador para a linguagem L2 da especificação.
Bônus: com variações definidas que serão deixadas propositalmente subespecificadas.

*)

(* ========= Sintaxe Abstrata ========= *)

(* Expressões binárias *)
(* bop ∈ {+, -, *, /, ==, <>, <, >, &&, ||}*)
type bop = Sum | Sub | Mul | Div   (* operações aritméticas *)
         | Eq  | Neq | Lt | Gt   (* operações relacionais  *)
         | And | Or   (* operações lógicas *)

(* Identificadores *)
type ident = string 

(* Localização de uma variável no ambiente de execução *)
type loc = string

(* Expressões *)
type expr = 
  | Num of int (* números inteiros *)                               (* int ∈ Z *)
  | Bool of bool (* valores booleanos *)                            (* bool ∈ {true, false} *)
  | If of expr * expr * expr (* operação if else *)                 (* if e_1 then e_2 else e_3 *)
  | Binop of bop * expr * expr (* operações binárias *)             (* e_1 op e_2*)
  | X of ident (* variável identificada por um nome *)              (* x *)
  | Let of string * expr * expr (* declaração local *)              (* let x:T = e_1 in e_2*)
  | Atr of expr * expr (* atribuição de valor a local dememória *)  (* e_1 := e_2*)
  | Derref of expr (* Acessa o valor em uma posição de memória *)   (* !e *)
  | New of expr (* aloca valor em uma nova posição de memória *)    (* new e *)
  | Unit of unit (* valor unitário, indica ausência de valor *)     (* () *)
  | While of expr * expr (* laço de repetição *)                    (* while e_1 do e_2 *)
  | Seq of expr * expr (* sequência de expressões *)                (* e_1; e_2 *)
  | Memloc of loc (* referência a uma posição de memória *)         (* l *)

  
(* Tipos *)
type tipo =
  | TyBool (* bool *)
  | TyInt  (* int*)
  | TyRef  (* ref T *)
  | TyUnit (* unit *)

(* Valores *)
let isvalue (e:expr) : bool = 
  match e with  (* Se avaliarem para true, as expressões são valores*)
    Num _   -> true
  | Bool _  -> true
  | Unit _  -> true
  | Memloc _ -> true
  | _ -> false
    
(* Declara exceção para erros de tipo inferido *)
exception BugTypeInfer 

(* Função para computar o resultado de uma operação binária *)
let compute (op: bop) (v1:expr) (v2:expr) : expr = 
  match (op,v1,v2) with
    (* operações aritméticas *)
    (Sum,Num n1, Num n2) -> Num (n1 + n2) (* soma *)
  | (Sub,Num n1, Num n2) -> Num (n1 - n2) (* subtração *)
  | (Mul,Num n1, Num n2) -> Num (n1 * n2) (* multiplicação *)                     
  | (Div,Num n1, Num n2) -> Num (n1 / n2) (* divisão *)
    
    (* operações relacionais *)
  | (Eq,Num n1, Num n2)  -> Bool (n1 = n2) (* igualdade *)
  | (Neq,Num n1, Num n2) -> Bool (n1 != n2) (* diferença *)
  | (Lt,Num n1, Num n2)  -> Bool (n1 < n2) (* menor que *)       
  | (Gt,Num n1, Num n2)  -> Bool (n1 > n2) (* maior que *)
    
    (* operações lógicas *)
  | (And, Bool b1, Bool b2) -> Bool (b1 && b2) (* conjunção (AND) *)
  | (Or,  Bool b1, Bool b2) -> Bool (b1 || b2) (* disjunção (OR) *)
    
  (* caso não seja uma operação válida *)
  |  _ -> raise BugTypeInfer 
                             
exception NoRuleApplies

(* Função para aplicar uma avaliação small-step na expressão *)
let rec step (e:expr) : expr = 
  match e with 
  | Num _   -> raise NoRuleApplies 
  | Bool _  -> raise NoRuleApplies
                 
  | If(Bool true,e2,e3)  -> e2 
  | If(Bool false,e2,e3) -> e3 
  | If(e1,e2,e3)         -> 
      let e1'= step e1 in If(e1',e2,e3)
  
  | Binop (op,v1,v2) when isvalue v1 && isvalue v2 -> compute op v1 v2 
  | Binop (op,v1,e2) when isvalue v1 ->  
      let e2'= step e2 in Binop (op,v1,e2')
  | Binop (op,e1,e2) ->  
      let e1'= step e1 in Binop (op,e1',e2) 
    
exception TypeError of string 
    
(* Função para inferir o tipo de uma expressão *)
let rec typeinfer (e:expr) : tipo =
  match e with 
  | Num _ -> TyInt
  | Bool _  -> TyBool 
    
  | If(e1,e2,e3)         -> 
      if (typeinfer e1) = TyBool then
        let t2 = typeinfer e2 in
        let t3 = typeinfer e3 in 
        if t2 = t3 then t2 
        else raise (TypeError "then e else devem ser do mesmo tipo")
      else raise (TypeError "condição do if deve ser booleana ") 
        
  | Binop (op,e1,e2)  ->
      let t1 = typeinfer e1 in 
      let t2 = typeinfer e2 in 
      (match op with
       | Sum | Sub | Mul | Div -> 
           if t1 = TyInt && t2 = TyInt 
           then TyInt
           else raise (TypeError "operandos de ops aritméticas devem ser inteiros")
               
       | Eq | Neq | Lt | Gt -> 
           if t1 = TyInt && t2 = TyInt 
           then TyBool
           else raise (TypeError "operandos de ops relacionais devem ser inteiros")
               
       | And | Or  -> 
           if t1 = TyBool && t2 = TyBool 
           then TyBool
           else raise (TypeError "operandos de ops lógicos devem ser booleanos"))
               
(* Função principal de avaliação *)
let rec eval (e: expr) : expr  =
  try 
    let e' = step e
    in eval e'
  with NoRuleApplies -> e

(* Função para converter uma operação binária em string *)
let rec string_of_op (op: bop)  : string = 
  match op with 
    Sum -> " + " 
  | Sub -> " - "
  | Mul -> " * "
  | Div -> " / "  
  | Eq  -> " = "
  | Neq -> " != "
  | Lt -> " < "
  | Gt -> " > "  
  | And -> " and "
  | Or -> " or "
  
(* Função para converter um tipo em string *)
let rec string_of_tipo (t: tipo)  : string = 
  match t with 
    TyInt  -> " int " 
  | TyBool -> " bool " 
    
(* Função para converter uma expressão em string *)
let rec string_of_expr (e : expr) : string = 
  match e with
  | Num  n  -> string_of_int n
  | Bool b  -> string_of_bool b 
  | If(e1,e2,e3) -> " if "    ^ (string_of_expr e1) ^ 
                    " then "  ^ (string_of_expr e2) ^ 
                    " else "  ^ (string_of_expr e3) 
  | Binop (op,e1,e2)  ->  (string_of_expr e1)  ^ (string_of_op op) ^ (string_of_expr e2)

(* Função para interpretar uma expressão e imprimir o resultado *)
let interp (e:expr) : unit =
  try
    let t = typeinfer e in
    let v = eval e
    in  ( print_string ("Resultado:\n")  ;
          print_string ((string_of_expr v) ^ " : " ^ (string_of_tipo t) ))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg) 
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"


(* ========= ASTs para TESTES ========= *)
let teste1 =  Binop(Sum, Num 10, Binop(Mul, Num 30, Num 2))  (*   10 + 30 * 2  *)
let teste2 =  Binop(Mul, Binop(Sum, Num 10, Num 30), Num 2)  (*   (10 + 30) * 2  *)
let teste3 =  If(Binop(Eq, Num 5, Num 5), Binop(Mul, Num 10, Num 2), Binop(Sum, Num 10, Num 2))
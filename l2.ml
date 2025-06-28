(* Trabalho de Semântica Formal 

Objetivo: implementar em OCaml um interpretador para a linguagem L2 da especificação.
Bônus: com variações definidas que serão deixadas propositalmente subespecificadas.

*)

(* filepath: l2.ml *)
module L2 = struct

(* Exceções *)
exception BugTypeInfer  (* Declara exceção para erros de tipo inferido *)
exception NoRuleApplies (* Declara exceção para quando não há regra aplicável *)
exception TypeError of string (* Declara exceção para erros de tipo *)

(* ========= Sintaxe Abstrata ========= *)

(* Expressões binárias *)
(* bop ∈ {+, -, *, /, ==, <>, <, >, &&, ||}*)
type bop = Sum | Sub | Mul | Div   (* operações aritméticas *)
         | Eq  | Neq | Lt | Geq   (* operações relacionais  *)
         | And | Or   (* operações lógicas *)

(* Identificadores *)
type ident = string 

(* Localização de uma variável no ambiente de execução *)
type loc = int

(* Expressões *)
type expr = 
  | Num of int (* números inteiros *)                               (* n ∈ Z *)
  | Bool of bool (* valores booleanos *)                            (* b ∈ {true, false} *)
  | If of expr * expr * expr (* operação if else *)                 (* if e_1 then e_2 else e_3 *)
  | Binop of bop * expr * expr (* operações binárias *)             (* e_1 op e_2*)
  | Id of ident (* variável identificada por um nome *)             (* x *)
  | Let of ident * expr * expr (* declaração local *)               (* let x:T = e_1 in e_2*)
  | Atr of expr * expr (* atribuição de valor a local dememória *)  (* e_1 := e_2*)
  | Derref of expr (* Acessa o valor em uma posição de memória *)   (* !e *)
  | New of expr (* aloca valor em uma nova posição de memória *)    (* new e *)
  | Unit (* valor unitário, indica ausência de valor *)             (* () *)
  | While of expr * expr (* laço de repetição *)                    (* while e_1 do e_2 *)
  | Seq of expr * expr (* sequência de expressões *)                (* e_1; e_2 *)
  | Memloc of loc (* referência a uma posição de memória *)         (* l *)
  | Read (* lê uma entrada*)                                        (* read() *)
  | Print of expr (* imprime uma expressão *)                       (* print e *)

(* Valores *)

(* isvalue: e → bool
   Verifica se uma expressão é um valor, ou seja, se não pode ser avaliada mais. *) 
let isvalue (e:expr) : bool = 
  match e with  (* Se avaliarem para true, as expressões são valores*)
    Num _   -> true   (* n *)
  | Bool _  -> true   (* b *)
  | Unit  -> true     (* () *)
  | Memloc _ -> true  (* l *)
  | _ -> false
  
(* Tipos *)
type tipo =
  | TyBool (* bool *)
  | TyInt  (* int *)
  | TyRef  (* ref T *)
  | TyUnit (* unit *)

(* in *)
type inlist =
  | Empty                   (* [] *)
  | Cons of int * inlist    (* n::in *)

(* out *)
type outlist =
  | Empty                   (* [] *)
  | Cons of int * outlist   (* n::out *)

(* ========= Semântica Operacional small-step ========= *)

(* Memória *)
(* Representação da memória como uma lista de pares (local, valor) *)
type tymem = (loc * expr) list 
let empty_mem : tymem = []

(* Expressão memória da semântica small-step *)
type expr_mem = expr * tymem

(* Funções auxiliares *)

(* update_memory: σ[l → v]
  Atualiza a memória g com um valor v na localização l *)
let update_memory (g: tymem) (l: loc) (v: expr) : tymem =
  let rec aux mem = 
    match mem with
      [] -> [(l, v)]  (* Se a memória estiver vazia, adiciona o novo par *)
    | (loc, _) :: tail when loc = l -> (l, v) :: tail  (* Se a localização já existir, atualiza o valor *)
    | head :: tail -> head :: aux tail  (* Caso contrário, mantém o par e continua procurando *)
  in aux g

(* lookup_memory: !l
Recupera o valor em uma localização l, caso esteja na memória g*)
let lookup_memory (g: tymem) (l: loc) : expr option =
  let rec aux mem = 
    match mem with
      [] -> None  (* Se a memória estiver vazia, retorna None *)
    | (loc, v) :: tail when loc = l -> Some v  (* Se encontrar a localização, retorna o valor *)
    | _ :: tail -> aux tail  (* Caso contrário, continua procurando *)
  in aux g

(* compute_bop: [[n_1]] bop [[n_2]]
  Função para computar o resultado de uma operação binária *)
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
  | (Geq,Num n1, Num n2)  -> Bool (n1 >= n2) (* maior ou igual que *)
    
    (* operações lógicas *)
  | (And, Bool b1, Bool b2) -> Bool (b1 && b2) (* conjunção (AND) *)
  | (Or,  Bool b1, Bool b2) -> Bool (b1 || b2) (* disjunção (OR) *)
    
  (* caso não seja uma operação válida *)
  |  _ -> raise BugTypeInfer 

(* subs: {v/x}
  Função para substituir uma variável x por um valor v em uma expressão e.
  Se a variável for a mesma, substitui pelo valor, caso contrário, mantém a expressão.
  Se a variável for uma localização de memória, substitui o valor na memória. *)
let rec subs (v: expr) (x: string) (e: expr) : expr =
  match e with
  | Num _ -> e
  | Bool _ -> e
  | Id y -> if y = x then v else e
  | Binop (op, e1, e2) -> Binop (op, subs v x e1, subs v x e2)
  | If (e1, e2, e3) -> If (subs v x e1, subs v x e2, subs v x e3)
  | Let (y, e1, e2) ->
      if y = x then Let (y, subs v x e1, e2)
      else Let (y, subs v x e1, subs v x e2)
  | Atr (e1, e2) -> Atr (subs v x e1, subs v x e2)
  | Derref e1 -> Derref (subs v x e1)
  | New e1 -> New (subs v x e1)
  | Seq (e1, e2) -> Seq (subs v x e1, subs v x e2)
  | While (e1, e2) -> While (subs v x e1, subs v x e2)
  | Print e1 -> Print (subs v x e1)
  | Unit -> Unit
  | Memloc _ -> e
  | Read -> Read
  | _ -> raise (TypeError "expressão não suportada para substituição")

  
(* step: -> 
  Função para aplicar uma avaliação small-step na expressão *)
let rec step (e:expr_mem) : expr_mem = 
  match e with 
  | (Num _, mem)   -> raise NoRuleApplies   (* Valor *)
  | (Bool _, mem)  -> raise NoRuleApplies   (* Valor *)

  (* == OP N ==================================================================== *)
  | (Binop (Sum, Num n1, Num n2), mem) ->                           (* OP+ *)
      (Num (n1 + n2), mem)
  | (Binop (Lt, Num n1, Num n2), mem) when n1 < n2 ->               (* OP<TRUE *)
      (Bool true, mem)
  | (Binop (Lt, Num n1, Num n2), mem) when n1 >= n2 ->              (* OP<FALSE *)
      (Bool false, mem)  
     
  (* == IF ====================================================================== *)
  | (If(Bool true,e2,e3), mem)  -> (e2, mem)                        (* IF-1 *)
  | (If(Bool false,e2,e3), mem) -> (e3, mem)                        (* IF-2 *)
  | (If(e1,e2,e3), mem) -> 
      let (e1', mem') = step (e1, mem) in (If(e1', e2, e3), mem')   (* IF-3 *)

  (* == OP ====================================================================== *)
  | (Binop (op,v1,v2), mem) when isvalue v1 && isvalue v2 -> (compute op v1 v2, mem) 
  | (Binop (op,v1,e2), mem) when isvalue v1 ->  
      let (e2', mem') = step (e2, mem) in (Binop (op,v1,e2'), mem') (* OP-2 *)
  | (Binop (op,e1,e2), mem) ->  
      let (e1', mem') = step (e1, mem) in (Binop (op,e1',e2), mem') (* OP-1 *) 
  
  (* == E-LET =================================================================== *)
  | (Let (x, v1, e2), mem) when isvalue v1 ->                       (* E-LET2 *)
      (subs v1 x e2, mem)  (*  {v1/x} e2 *)  
  | (Let (x, e1, e2), mem) ->
      let (e1', mem') = step (e1, mem) in (Let (x, e1', e2), mem')  (* E-LET1 *)
  
  (* == ATR ===================================================================== *)
  | (Atr (l, v1), mem) when isvalue l && isvalue v1 ->              (* ATR1 *)
      (Unit, update_memory mem (match l with 
                                  Memloc loc -> loc 
                                  | _ -> raise NoRuleApplies) 
                            v1)                                     
  | (Atr (l, e1), mem) when isvalue l ->
      let (e1', mem') = step (e1, mem) in (Atr (l, e1'), mem')      (* ATR2 *)
  | (Atr (e1, e2), mem) ->
      let (e1', mem') = step (e1, mem) in (Atr (e1', e2), mem')     (* ATR *)

  (* == DERREF ================================================================== *)
  | (Derref (l), mem) when isvalue l ->                             (* DERREF1 *)
      (match lookup_memory mem (match l with 
                                Memloc loc -> loc 
                                | _ -> raise NoRuleApplies) with
       (* Se a localização existir, retorna o valor *)
       | Some v -> (v, mem)  
       (* Se não existir, lança exceção *) 
       | None -> raise NoRuleApplies)  
  | (Derref (e), mem) ->
      let (e', mem') = step (e, mem) in (Derref (e'), mem')         (* DERREF *)
  
  (* == NEW ====================================================================== *)
  | (New (v), mem) when isvalue v ->                                (* NEW1 *)
      (* Nova localização baseada no tamanho atual da memória *)                           
      let loc = List.length mem in  
      (Memloc loc, update_memory mem loc v) 
  | (New (e), mem) -> 
      let (e', mem') = step (e, mem) in (New (e'), mem')            (* NEW *)

  (* == SEQ ====================================================================== *)
  | (Seq (Unit, e2), mem) -> (e2, mem)                              (* SEQ1 *)
  | (Seq (e1,e2), mem) ->                                           (* SEQ2 *)
      let (e1', mem') = step (e1, mem) in 
      (Seq (e1', e2), mem')                                         

  (* == WHILE ==================================================================== *)
  | (While (e1, e2), mem) ->                                        (* E-WHILE *)
      if e1 = Bool true then
        (Seq (e2, While (e1, e2)), mem)
      else
        (Unit, mem)

  (* == PRINT ==================================================================== *)
  | (Print (n), mem) when isvalue n ->                              (* PRINT-N *)
      (Unit, mem)  (* Imprime o valor e retorna Unit *)

  | (Print (e), mem) -> 
      let (e', mem') = step (e, mem) in (Print (e'), mem')          (* PRINT *)

  (* == READ ===================================================================== *)
  (* | (Read, mem) ->  VEM AÍ COM n.in*) (* @TODO *)
  | _ -> raise NoRuleApplies  (* TODO: TEMPORÁRIO *)
    
(* ========= Sistema de Tipos ========= *)

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
               
       | Eq | Neq | Lt | Geq -> 
           if t1 = TyInt && t2 = TyInt 
           then TyBool
           else raise (TypeError "operandos de ops relacionais devem ser inteiros")
               
       | And | Or  -> 
           if t1 = TyBool && t2 = TyBool 
           then TyBool
           else raise (TypeError "operandos de ops lógicos devem ser booleanos"))
    | _ -> 
        raise (TypeError "expressão não suportada para inferência de tipo") (* TODO: adicionar mais expressões *)


(* ========= Interpretador ========= *)

(* Função principal de avaliação *)
let rec eval (e: expr_mem) : expr_mem  =
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
  | Geq -> " >= "  
  | And -> " and "
  | Or -> " or "
  
(* Função para converter um tipo em string *)
let rec string_of_tipo (t: tipo)  : string = 
  match t with 
    TyInt  -> " int " 
  | TyBool -> " bool " 
  | TyRef -> " ref "
  | TyUnit -> " unit "
  | _ -> 
      raise (TypeError "tipo não suportado para conversão em string") (* TODO: adicionar mais tipos *)
    
(* Função para converter uma expressão em string *)
let rec string_of_expr (e : expr) : string = 
  match e with
  | Num  n  -> string_of_int n
  | Bool b  -> string_of_bool b 
  | If(e1,e2,e3) -> " if "    ^ (string_of_expr e1) ^ 
                    " then "  ^ (string_of_expr e2) ^ 
                    " else "  ^ (string_of_expr e3) 
  | Binop (op,e1,e2)  ->  (string_of_expr e1)  ^ (string_of_op op) ^ (string_of_expr e2)
  | _ -> 
      raise (TypeError "expressão não suportada para conversão em string")

(* Função para interpretar uma expressão e imprimir o resultado *)
let interp (e:expr_mem) : unit =
  try
    let t = typeinfer (fst e) in
    let v = eval e
    in  ( print_string ("Resultado:\n")  ;
          print_string ((string_of_expr (fst v)) ^ " : " ^ (string_of_tipo t) ))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg) 
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"


(* ========= ASTs para TESTES ========= *)
let teste1 =  Binop(Sum, Num 10, Binop(Mul, Num 30, Num 2))  (*   10 + 30 * 2  *)
let teste2 =  Binop(Mul, Binop(Sum, Num 10, Num 30), Num 2)  (*   (10 + 30) * 2  *)
let teste3 =  If(Binop(Eq, Num 5, Num 5), Binop(Mul, Num 10, Num 2), Binop(Sum, Num 10, Num 2))

(* ========== Testes de Avaliação ========= *)
let () =

  (* Testes de Avaliação *)
  print_string "Testes de Avaliação:\n";
  let e1 = (teste1, empty_mem) in
  let e2 = (teste2, empty_mem) in
  let e3 = (teste3, empty_mem) in     
  print_string "Teste 1:\n";
  interp e1;
  print_newline ();
  print_string "Teste 2:\n";
  interp e2;
  print_newline ();
  print_string "Teste 3:\n";
  interp e3;
  print_newline ();

  (* Teste de IF *)
  print_string "Teste de If:\n";
  interp (If(Bool true, Num 42, Num 0), empty_mem);
  print_newline ();

  (* Teste de Atribuição *)
  print_string "Teste de Atribuição:\n";
  interp (Let("x", Num 10, Binop(Sum, Id "x", Num 5)), empty_mem);
  print_newline ();

  (* Teste de Atribuição com Memória *)
  print_string "Teste de Atribuição com Memória:\n";
  let mem_test = update_memory empty_mem 0 (Num 100) in
  interp (Atr(Memloc 0, Num 200), mem_test);
  print_newline ();

  (* Teste de Derreferência *)
  print_string "Teste de Derreferência:\n";
  interp (Derref(Memloc 0), mem_test);
  print_newline ();

  (* Teste de Nova Alocação *)
  print_string "Teste de Nova Alocação:\n";
  interp (New (Num 42), empty_mem);
  print_newline ();

  (* Teste de Sequência *)
  print_string "Teste de Sequência:\n";
  interp (Seq(Num 1, Num 2), empty_mem);
  print_newline ();

  (* Teste de While *)
  print_string "Teste de While:\n";
  interp (While(Bool true, Num 42), empty_mem);
  print_newline ();

  (* Teste de Print *)
  print_string "Teste de Print:\n";
  interp (Print (Num 42), empty_mem);
  print_newline ();

  (* Teste de Read *)
  print_string "Teste de Read:\n";
  interp (Read, empty_mem); (* Este teste não funcionará corretamente sem implementação de leitura *)
  print_newline ();

  (* Teste de Memloc *)
  print_string "Teste de Memloc:\n";
  interp (Memloc 0, empty_mem);
  print_newline ();

  (* Teste de Unit *)
  print_string "Teste de Unit:\n";
  interp (Unit, empty_mem);
  print_newline ();

  (* Teste de Identificador *)
  print_string "Teste de Identificador:\n";
  interp (Id "x", empty_mem); (* Este teste não funcionará corretamente sem implementação de variáveis *)
  print_newline ();

  (* Teste de Atribuição com Identificador *)
  print_string "Teste de Atribuição com Identificador:\n";
  interp (Let("x", Num 10, Atr(Id "x", Num 20)), empty_mem);
  print_newline ();

  (* Teste de Atribuição com Identificador e Memória *)
  print_string "Teste de Atribuição com Identificador e Memória:\n";
  let mem_test2 = update_memory empty_mem 1 (Num 100) in
  interp (Let("y", Memloc 1, Atr(Id "y", Num 200)), mem_test2);
  print_newline ();

  
end
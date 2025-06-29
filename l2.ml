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
  | TyBool        (* bool *)
  | TyInt         (* int *)
  | TyRef of tipo (* ref T *)
  | TyUnit        (* unit *)

(* in *)
type inlist =
  | EmptyIn                   (* [] *)
  | ConsIn of int * inlist    (* n::in *)

(* out *)
type outlist =
  | EmptyOut                   (* [] *)
  | ConsOut of int * outlist   (* n::out *)

(* ========= Semântica Operacional small-step ========= *)

(* Memória *)
(* Representação da memória como uma lista de pares (local, valor) *)
type tymem = (loc * expr) list 
let empty_mem : tymem = []

(* Expressão memória da semântica small-step *)
type expr_mem = expr * tymem * inlist * outlist

(* ========= Funções auxiliares ========= *)

(* read: read ()
Função para ler uma string da entrada padrão *)
let read (unit) : int =
  try
    print_endline "Digite um inteiro:";
    (* Lê uma linha da entrada padrão e retorna como string *)
    let input = read_int () in
    input;
  with _ -> raise (TypeError "entrada inválida para read_string()")

let print (e: expr_mem): unit =
  match e with
  | (Num n, _, _, _) -> print_endline (string_of_int n)  (* Imprime número *)
  | _ -> raise (TypeError "expressão não suportada para impressão")  (* Exceção para expressões não suportadas *)

(* isvalue: e → bool
   Verifica se uma expressão é um valor, ou seja, se não pode ser avaliada mais. *)

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
let rec step (e, mem, in_, out_): expr_mem = 
  match (e, mem, in_, out_) with 
  (* == VALORES ================================================================== *)
  | (Num _, mem, _, _)   -> raise NoRuleApplies  
  | (Bool _, mem, _, _)  -> raise NoRuleApplies  
  | (Unit, mem, _, _) -> raise NoRuleApplies
  | (Memloc _, mem, _, _) -> raise NoRuleApplies

  (* == OP N ==================================================================== *)
  | (Binop (Sum, Num n1, Num n2), mem, in_, out_) ->                (* OP+ *)
      (Num (n1 + n2), mem, in_, out_)
  | (Binop (Lt, Num n1, Num n2), mem, in_, out_) when n1 < n2 ->    (* OP<TRUE *)
      (Bool true, mem, in_, out_)
  | (Binop (Lt, Num n1, Num n2), mem, in_, out_) when n1 >= n2 ->   (* OP<FALSE *)
      (Bool false, mem, in_, out_)  
     
  (* == OP ====================================================================== *)
  | (Binop (op,e1,e2), mem, in_, out_) ->                           (* OP-1 *) 
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
      (Binop (op,e1',e2), mem', in_', out_') 
  | (Binop (op,v1,e2), mem, in_, out_) when isvalue v1 ->           (* OP-2 *)
      let (e2', mem', in_', out_') = step (e2, mem, in_, out_) in 
      (Binop (op,v1,e2'), mem', in_', out_') 

  (* == IF ====================================================================== *)
  | (If(Bool true,e2,e3), mem, in_, out_)  -> (e2, mem, in_, out_)  (* IF-1 *)
  | (If(Bool false,e2,e3), mem, in_, out_) -> (e3, mem, in_, out_)  (* IF-2 *)
  | (If(e1,e2,e3), mem, in_, out_) -> 
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
        (If(e1', e2, e3), mem', in_', out_')                        (* IF-3 *)

  (* == E-LET =================================================================== *)
  | (Let (x, e1, e2), mem, in_, out_) ->                            (* E-LET1 *)
    let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
      (Let (x, e1', e2), mem', in_', out_')  
  | (Let (x, v1, e2), mem, in_, out_) when isvalue v1 ->            (* E-LET2 *)
      (subs v1 x e2, mem, in_, out_)  (*  {v1/x} e2 *)  
  
  (* == ATR ===================================================================== *)
  | (Atr (l, v1), mem, in_, out_) when isvalue l && isvalue v1 ->   (* ATR1 *)
      (Unit, update_memory mem (match l with 
                                  Memloc loc -> loc 
                                  | _ -> raise NoRuleApplies) v1, in_, out_)   

  | (Atr (l, e1), mem, in_, out_) when isvalue l ->                 (* ATR2 *)
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
        (Atr (l, e1'), mem', in_', out_')      
  | (Atr (e1, e2), mem, in_, out_) ->                               (* ATR *)
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
        (Atr (e1', e2), mem', in_', out_')     

  (* == DERREF ================================================================== *)
  | (Derref (l), mem, in_, out_) when isvalue l ->                  (* DERREF1 *)
      (match lookup_memory mem (match l with 
                                Memloc loc -> loc 
                                | _ -> raise NoRuleApplies) with
       (* Se a localização existir, retorna o valor *)
       | Some v -> (v, mem, in_, out_)  
       (* Se não existir, lança exceção *) 
       | None -> raise NoRuleApplies)  
  | (Derref (e), mem, in_, out_) ->                                 (* DERREF *)
      let (e', mem', in_', out_') = step (e, mem, in_, out_) in 
        (Derref (e'), mem', in_', out_')         
  
  (* == NEW ====================================================================== *)
  | (New (v), mem, in_, out_) when isvalue v ->                     (* NEW1 *)
      (* Nova localização baseada no tamanho atual da memória *)                           
      let loc = List.length mem in  
      (Memloc loc, update_memory mem loc v, in_, out_)  
  | (New (e), mem, in_, out_) ->                                    (* NEW *)
      let (e', mem', in_', out_') = step (e, mem, in_, out_) in 
        (New (e'), mem', in_', out_')            

  (* == SEQ ====================================================================== *)
  | (Seq (Unit, e2), mem, in_, out_) -> (e2, mem, in_, out_)        (* SEQ1 *)
  | (Seq (e1,e2), mem, in_, out_) ->                                (* SEQ2 *)
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
      (Seq (e1', e2), mem', in_', out_')                                         

  (* == WHILE ==================================================================== *)
  | (While (e1, e2), mem, in_, out_) ->                             (* E-WHILE *)
      if e1 = Bool true then
        (Seq (e2, While (e1, e2)), mem, in_, out_)
      else
        (Unit, mem, in_, out_)

  (* == PRINT ==================================================================== *)
  | (Print n, mem, in_, out_) when isvalue n ->                     (* PRINT-N *)
      (match n with
       | Num v -> (Unit, mem, in_, ConsOut (v, out_))
       | _ -> raise (TypeError "Print só suporta números"))

  | (Print e, mem, in_, out_) -> 
      let (e', mem', in_', out_') = step (e, mem, in_, out_) in     (* PRINT *)
        (Print (e'), mem', in_', out_')     

  (* == READ ===================================================================== *)
  | (Read, mem, in_, out_) -> 
      (* Se a expressão for Read, lê um valor da entrada *)         (* READ *)
      (match in_ with
      | EmptyIn -> raise (TypeError "entrada vazia")
      | ConsIn (n, rest) -> 
          (Num n, mem, rest, out_))
    
  (* == NONE ===================================================================== *) 
  | _ -> raise NoRuleApplies
    
(* ========= Sistema de Tipos ========= *)
type tyenv = (string * tipo) list (* Γ Ambiente de tipos *)
let empty_env : tyenv = []

(* Função para inferir o tipo de uma expressão *)
let rec typeinfer (env: tyenv) (e:expr) : tipo =
  match e with 
  | Num _ -> TyInt                                (* T-INT *)
  | Bool _  -> TyBool                             (* T-BOOL *)                 
    
  | Binop (Sum,e1,e2) ->                          (* T-OP+ *)   
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 == TyInt then 
        if t2 == t1 then TyInt
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | Binop (Lt,e1,e2) ->                          (* T-OP+ *)   
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 == TyInt then 
        if t2 == t1 then TyBool
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | If (e1,e2,e3)         ->                     (* T-IF *)
      if (typeinfer env e1) = TyBool then
        let t2 = typeinfer env e2 in
        let t3 = typeinfer env e3 in 
        if t2 = t3 then t2 
        else raise (TypeError "then e else devem ser do mesmo tipo")
      else raise (TypeError "condição do if deve ser booleana ") 

  | Id x ->                                     (* T-ATR *)
      (try List.assoc x env
        with Not_found -> raise (TypeError ("variável livre: " ^ x)))

  | Let (x, e1, e2) ->                          (* T-LET *)
      let t1 = typeinfer env e1 in
        let n_env = ((x, t1) :: env) in   (* x |→ T *)
          let t2 = typeinfer n_env e2 in
          if t1 != t2 then t2
          else raise (TypeError ("e1 deve ter tipo diferente de e2"))
      
  | Atr (e1, e2) ->                             (* T-ATR *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 == TyRef t2 then TyUnit
      else raise (TypeError ("o tipo ref T de e1 precisa ter o ser do mesmo tipo T de e2"))

  | Derref e1 ->                                (* T-DERREF *)
      let t1 = typeinfer env e1 in
      (match t1 with
        TyRef t -> t  (* Se for um tipo de referência, retorna o tipo referenciado *)
      | _ -> raise (TypeError "e1 deve ser do tipo ref T"))

  | New e1 ->                                   (* T-NEW *)
      let t1 = typeinfer env e1 in TyRef t1
  
  | Unit -> TyUnit                              (* T-UNIT *)

  | While (e1, e2) ->                           (* T-WHILE *)
      if (typeinfer env e1) = TyBool then
        let t2 = typeinfer env e2 in
        if t2 = TyUnit then TyUnit
        else raise (TypeError "corpo do while deve ser do tipo unit")
      else raise (TypeError "condição do while deve ser booleana")

  | Seq (e1, e2) ->                             (* T-SEQ *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyUnit then t2
      else raise (TypeError "e1 deve ser do tipo unit")

  | Read -> TyInt                               (* T-READ *)

  | Print e1 ->                                 (* T-PRINT *)
      let t1 = typeinfer env e1 in
      if t1 = TyInt then TyUnit
      else raise (TypeError "print só suporta números inteiros")

  | _ -> 
        raise (TypeError "expressão não suportada para inferência de tipo") (* TODO: adicionar mais expressões *)


(* ========= Interpretador ========= *)
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
  | TyRef t_ -> " ref "
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

(* Função principal de avaliação *)
let rec eval (e: expr_mem) : expr_mem  =
  try 
    let e' = step e
    in eval e'
  with NoRuleApplies -> e

(* Função para interpretar uma expressão e imprimir o resultado *)
let interp (e:expr_mem) : unit = 
  try
    let (e1, _, _, _) = e in
    let t = typeinfer empty_env e1 in
    let v = eval e in
    let (v1, _, _, _) = v in
    ( print_string ("Resultado:\n")  ;
      print_string ((string_of_expr v1) ^ " : " ^ (string_of_tipo t)) )
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg) 
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"

(* ========= ASTs para TESTES ========= *)
let teste1 =  Binop(Sum, Num 10, Binop(Mul, Num 30, Num 2))  (*   10 + 30 * 2  *)
let teste2 =  Binop(Mul, Binop(Sum, Num 10, Num 30), Num 2)  (*   (10 + 30) * 2  *)
let teste3 =  If(Binop(Eq, Num 5, Num 5), Binop(Mul, Num 10, Num 2), Binop(Sum, Num 10, Num 2))


        
end

(* ========== Testes de Avaliação ========= *)
let teste = L2.read ();
L2.interp(L2.Read, L2.empty_mem, L2.ConsIn (1, L2.ConsIn (2, L2.EmptyIn)), L2.EmptyOut); (* Teste de leitura e impressão *)



(* Testes de Tipos *)

(* Testes de Avaliação
print_string "Testes de Avaliação:\n";
let e1 = (L2.teste1, L2.empty_mem) in
let e2 = (L2.teste2, L2.empty_mem) in
let e3 = (L2.teste3, L2.empty_mem) in     
print_string "Teste 1:\n";
L2.interp e1;
print_newline ();
print_string "Teste 2:\n";
L2.interp e2;
print_newline ();
print_string "Teste 3:\n";
L2.interp e3;
print_newline ();

(* Teste de IF *)
print_string "Teste de If:\n";
L2.interp (L2.If(L2.Bool true, L2.Num 42, L2.Num 0), L2.empty_mem);
print_newline ();

(* Teste de Atribuição *)
print_string "Teste de Atribuição:\n";
L2.interp (L2.Let("x", L2.Num 10, L2.Binop(L2.Sum, L2.Id "x", L2.Num 5)), L2.empty_mem);
print_newline ();

(* Teste de Atribuição com Memória *)
print_string "Teste de Atribuição com Memória:\n";
let mem_test = L2.update_memory L2.empty_mem 0 (L2.Num 100) in
L2.interp (L2.Atr(L2.Memloc 0, L2.Num 200), mem_test);
print_newline ();

(* Teste de Derreferência *)
print_string "Teste de Derreferência:\n";
L2.interp (L2.Derref(L2.Memloc 0), mem_test);
print_newline ();

(* Teste de Nova Alocação *)
print_string "Teste de Nova Alocação:\n";
L2.interp (L2.New (L2.Num 42), L2.empty_mem);
print_newline ();

(* Teste de Sequência *)
print_string "Teste de Sequência:\n";
L2.interp (L2.Seq(L2.Num 1, L2.Num 2), L2.empty_mem);
print_newline ();

(* Teste de While *)
print_string "Teste de While:\n";
L2.interp (L2.While(L2.Bool true, L2.Num 42), L2.empty_mem);
print_newline ();

(* Teste de Print *)
print_string "Teste de Print:\n";
L2.interp (L2.Print (L2.Num 42), L2.empty_mem);
print_newline ();

(* Teste de Read *)
print_string "Teste de Read:\n";
L2.interp (L2.Read, L2.empty_mem); (* Este teste não funcionará corretamente sem implementação de leitura *)
print_newline ();

(* Teste de Memloc *)
print_string "Teste de Memloc:\n";
L2.interp (L2.Memloc 0, L2.empty_mem);
print_newline ();

(* Teste de Unit *)
print_string "Teste de Unit:\n";
L2.interp (L2.Unit, L2.empty_mem);
print_newline ();

(* Teste de Identificador *)
print_string "Teste de Identificador:\n";
L2.interp (L2.Id "x", L2.empty_mem); (* Este teste não funcionará corretamente sem implementação de variáveis *)
print_newline ();

(* Teste de Atribuição com Identificador *)
print_string "Teste de Atribuição com Identificador:\n";
L2.interp (L2.Let("x", L2.Num 10, L2.Atr(L2.Id "x", L2.Num 20)), L2.empty_mem);
print_newline ();

(* Teste de Atribuição com Identificador e Memória *)
print_string "Teste de Atribuição com Identificador e Memória:\n";
let mem_test2 = L2.update_memory L2.empty_mem 1 (L2.Num 100) in
L2.interp (L2.Let("y", L2.Memloc 1, L2.Atr(L2.Id "y", L2.Num 200)), mem_test2);
print_newline (); *)
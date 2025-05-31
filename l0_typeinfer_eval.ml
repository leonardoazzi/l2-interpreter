type bop = Sum | Sub | Mul | Div   (* operações aritméticas *)
         | Eq  | Neq | Lt | Gt   (* operações relacionais  *)
         | And | Or   (* operações lógicas *)

type expr = 
  | Num of int
  | Bool of bool 
  | If of expr * expr * expr 
  | Binop of bop * expr * expr
             
type tipo =
  | TyBool
  | TyInt

           
let isvalue (e:expr) : bool = 
  match e with
    Num _   -> true
  | Bool _  -> true
  | If _    -> false
  | Binop _ -> false 
    


exception BugTypeInfer
  
let compute (op: bop) (v1:expr) (v2:expr) : expr = 
  match (op,v1,v2) with
    (Sum,Num n1, Num n2) -> Num (n1 + n2)
  | (Sub,Num n1, Num n2) -> Num (n1 - n2)
  | (Mul,Num n1, Num n2) -> Num (n1 * n2)                      
  | (Div,Num n1, Num n2) -> Num (n1 / n2)
                              
  | (Eq,Num n1, Num n2)  -> Bool (n1 = n2)
  | (Neq,Num n1, Num n2) -> Bool (n1 != n2)
  | (Lt,Num n1, Num n2)  -> Bool (n1 < n2)                      
  | (Gt,Num n1, Num n2)  -> Bool (n1 > n2)
             
  | (And, Bool b1, Bool b2) -> Bool (b1 && b2)
  | (Or,  Bool b1, Bool b2) -> Bool (b1 || b2) 
                                 
  |  _ -> raise BugTypeInfer 
                             
exception NoRuleApplies
  
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
               
    
let rec eval (e: expr) : expr  =
  try 
    let e' = step e
    in eval e'
  with NoRuleApplies -> e
    
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
  
let rec string_of_tipo (t: tipo)  : string = 
  match t with 
    TyInt  -> " int " 
  | TyBool -> " bool " 
    
let rec string_of_expr (e : expr) : string = 
  match e with
  | Num  n  -> string_of_int n
  | Bool b  -> string_of_bool b 
  | If(e1,e2,e3) -> " if "    ^ (string_of_expr e1) ^ 
                    " then "  ^ (string_of_expr e2) ^ 
                    " else "  ^ (string_of_expr e3) 
  | Binop (op,e1,e2)  ->  (string_of_expr e1)  ^ (string_of_op op) ^ (string_of_expr e2)
  
    
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

                                           
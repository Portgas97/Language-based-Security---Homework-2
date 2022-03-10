(* An environment is a map from identifier to a value (what the identifier is bound to).
  For simplicity we represent the environment as an association list, i.e., a list of pair (identifier, data).
*)
type 'v env = (string * 'v) list;;

(**
  Given an environment {env} and an identifier {x} it returns the data {x} is bound to.
  If there is no binding, it raises an exception.
*)
let rec lookup env x =
  match env with
  | []        -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x;;

(* Homework 1 *)
(* types of possible permissions, placeholder *)
type permission =
  | P_Read
  | P_Send
  | P_Write
  | P_Open
  | P_Close;;
 
(* permission set of a single function *)
(* ASSUMPTION: The programmer-supplied list of permissions has no duplicates *)
type permissionList = (permission) list;;

(* Stack of PermissionList to be passed around during function instancing *)
type permissionStack = (permissionList) list;;

(* /Homework 1 *)

(* Homework 2 *)
type state = int;;
type symbol = char;;
type transition = state * symbol * state;;
type dfa =    {
  states : state list;
  sigma : symbol list;
  start : state;
  transitions : transition list;
  accepting : state list; 
};; 

(* /Homework 2 *)

type expr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Let of string * expr * expr
  | LetRec of string * string * expr * expr * permissionList
  | Prim of string * expr * expr
  | If of expr * expr * expr
  | Fun of string * expr * permissionList	  					(* Homework 1 *)
  | FunRec of string * string * expr * permissionList 			(* Homework 2 *)
  | Call of expr * expr
  | Phi of dfa * expr 											(* Homework 2 *)
  | Read of string
  | Write of string
  | Send of expr * string;;


(** 
Intermediate representation:
	expressions extended with Abort routine and global state manipulation
*)

type iexpr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Let of string * iexpr * iexpr
  | LetRec of string * string * iexpr * iexpr * permissionList	(* Homework 2 *)
  | Prim of string * iexpr * iexpr
  | If of iexpr * iexpr * iexpr
  | Fun of string * iexpr * permissionList						(* Homework 1 *)
  | FunRec of string * string * iexpr * permissionList 			(* Homework 2 *)
  | Call of iexpr * iexpr
  | Phi of dfa * iexpr											(* Homework 2 *)
  | Read of string
  | Write of string
  | Send of iexpr * string
  | Abort of string
  | GLet of iexpr * iexpr
  | GVar;;
 
type ivalue =
  | Int of int
  | Closure of string * iexpr * permissionList * ivalue env				 	(* Homework 1 *)
  | RecClosure of string * string * iexpr * permissionList * ivalue env;;	(* Homework 2 *)
 
type gstate = GState of int;;

(* Homework 2 *)

let explode s = let rec expl i l = 
                  if i < 0 then l else expl (i - 1) (s.[i] :: l) in  
    (* s.[i] returns the ith element of s as a char *) 
  expl (String.length s - 1) [];; 
	(* String.length s returns the length of s      *) 

let rec contains e l = match l with   
  | [] -> false   
  | hd::tl -> if hd = e then true else contains e tl;;

let checkAccepts str dfa =
  let symbols = explode str in  
  let transition state symbol =    
    let rec find_state l =        
      match l with       
      | (s1,sym,s2)::tl ->         
          if (s1 = state && symbol = sym) then          
            s2 else find_state tl      
      | _ -> failwith "no next state"   
    in find_state dfa.transitions 
  in let final_state =      
       let rec h symbol_list =        
         match symbol_list with       
         | [hd] -> (transition dfa.start hd)       
         | hd::tl -> (transition (h tl) hd)       
         | _ -> failwith "empty list of symbols" 
       in     
       h (List.rev symbols) 
  in 
		if (contains final_state dfa.accepting) then true else false;;

let rec checkSecurityHistoryHelper dfa_list history : bool=
  match dfa_list with
  | [] -> true
  | hd::tl -> if checkAccepts history hd then checkSecurityHistoryHelper tl history else false

(* Class for managing DFAs *)
class dfa_container = 
  object (self)
    val mutable dfa_list = ([]: dfa list)
	(* Global variable holding the value of the execution history *)
    val mutable securityHistory = ("": string)
    method push dfa =
      dfa_list <- dfa :: dfa_list
    method pop =                         (* pop method *)
      let result = List.hd dfa_list in
      dfa_list<- List.tl dfa_list;
	(* static method that will add char c to string securityHistory *)
    method extendHistory c = 
      securityHistory <- securityHistory^c; 
    method viewHistory = 
      securityHistory
    method checkSecurityHistory =
      checkSecurityHistoryHelper dfa_list securityHistory
    method clearHistory =
      securityHistory <- ""
  end;;
  
(* instantiate an object of dfa_container to handle the state of the interpreter *)
let dfa_overlord = new dfa_container;;

(* Homework 1 *)

(* this method checks if a given function has the neededPermission in its permission list
   do not be confused, this checks only for a single function, and does not stackwalk
*) 
let rec checkPermission permissionList neededPermission = 
  match permissionList with
  | [] -> false
  | y::r -> if y = neededPermission then true else checkPermission r neededPermission;;
 
(* Stackwalking method to check permissions on all functions in call stack
*)
let rec stackWalking permissionStack neededPermission =
  match permissionStack with
  | [] -> true
  | y::r -> if checkPermission y neededPermission then stackWalking r neededPermission else false;;
 
(* Base code *) 
let rec ieval (e : iexpr) (env : ivalue env) (g : gstate) (pStack: permissionStack) : ivalue * gstate  =
  match e with
  | CstI i -> (Int i, g)
  | CstB b -> (Int (if b then 1 else 0), g)
  | Var x  -> (lookup env x, g)
  | Prim(ope, e1, e2) ->
      let (v1, g') = ieval e1 env g pStack in
      let (v2, g'') = ieval e2 env g' pStack in
      begin
        match (ope, v1, v2) with
        | ("*", Int i1, Int i2) -> (Int (i1 * i2), g'')
        | ("+", Int i1, Int i2) -> (Int (i1 + i2), g'')
        | ("-", Int i1, Int i2) -> (Int (i1 - i2), g'')
        | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0), g'')
        | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0), g'')
        |  _ -> failwith "unknown primitive or wrong type"
      end
  | Let(x, eRhs, letBody) ->
      let (xVal, g') = ieval eRhs env g pStack in
      let letEnv = (x, xVal) :: env in
      ieval letBody letEnv g' pStack 
  | LetRec(f, i, fBody, letBody, permList) -> 
      let (rval, g') = ieval (FunRec(f,i,fBody, permList)) env g pStack in
      let benv = (f,rval)::env
      in ieval letBody benv g' pStack
  | If(e1, e2, e3) ->
      begin
        match ieval e1 env g pStack with
        | (Int 0, g') -> ieval e3 env g' pStack
        | (Int _, g') -> ieval e2 env g' pStack
        | _     -> failwith "eval If"
      end
  | Fun(x,fBody, permList) -> (Closure(x, fBody, permList, env), g)
  | FunRec(f, x, fBody, permList) -> (RecClosure (f, x, fBody, permList, env), g);
  | Call(eFun, eArg) ->
      let (fClosure, _) = ieval eFun env g pStack in
      begin
        match fClosure with
        | Closure (x, fBody, fDeclPermList, fDeclEnv) ->
            let (xVal, g') = ieval eArg env g pStack in
            let fBodyEnv = (x, xVal) :: fDeclEnv in
            let fDeclPermStack = fDeclPermList::pStack
            in ieval fBody fBodyEnv g' fDeclPermStack
        | RecClosure (fName, x, fBody, fDeclPermList, fDeclEnv) ->
            let (xVal, g') = ieval eArg env g pStack in
            let rEnv = (fName, fClosure) :: fDeclEnv in
            let fBodyEnv = (x, xVal) :: rEnv in
            let fDeclPermStack = fDeclPermList::pStack
            in ieval fBody fBodyEnv g' fDeclPermStack
        | _ -> failwith "eval Call: not a function"
      end
  (* currently identical dfas are allowed *)
  | Phi(dfa, e) -> 
      dfa_overlord#push dfa; 
      let interval = ieval e env g pStack in
      dfa_overlord#pop;
      interval
  | Read(_) -> 	
      dfa_overlord#extendHistory "r"; 
      if dfa_overlord#checkSecurityHistory then
        if stackWalking pStack P_Read then (Int 0, g) else failwith("No Read permission on stack")
      else failwith("Illegal History.")
  | Write(_) -> 
      dfa_overlord#extendHistory "w"; 	
      if dfa_overlord#checkSecurityHistory then
        if stackWalking pStack P_Write then (Int 0, g) else failwith("No Read permission on stack")
      else failwith("Illegal History.")
  | Send(x, _) -> 
      dfa_overlord#extendHistory "s";
      if dfa_overlord#checkSecurityHistory then				
        if stackWalking pStack P_Send then let (_, g') = ieval x env g pStack in (Int 1, g') else failwith("No Send permission on stack")
      else failwith("Illegal History.")
  | Abort msg -> failwith msg
  | GLet(letVal, letBody) -> let (xVal, _) = ieval letVal env g pStack
      in begin match xVal with 
        | Int(i) -> ieval letBody env (GState i) pStack
        | _ -> failwith "eval Call: not an integer"
      end
  | GVar -> begin match g with
      | GState(i) -> (Int(i), g)
    end;;
   
   
type stateNFA = int;;
type symbolNFA = iexpr;;
(* (s0, s1, delta, msg) *)
type nfa = stateNFA * stateNFA * (stateNFA * symbolNFA -> stateNFA option) * string;;

(* type 'a option = None | Some of 'a;; *)

let inlineNfa (s0, s1, delta, msg) e = 
  If(Prim("=", GVar, CstI s0), 
     begin match (delta(s0,e)) with 
       | Some s -> GLet(CstI s, e)
       | None -> Abort(msg)
     end, 
     begin match (delta(s1,e)) with 
       | Some s -> GLet(CstI s, e)
       | None -> Abort(msg)
     end)

let rec comp (sa : nfa) (p : expr) : iexpr = match p with
  | CstI i -> CstI i
  | CstB b -> CstB b
  | Var x -> inlineNfa sa (Var x)
  | Prim(ope, e1, e2) -> inlineNfa sa (Prim(ope, (comp sa e1), (comp sa e2)))
  | Let(x, e1, e2) -> Let(x, (comp sa e1), (comp sa e2))
  | LetRec(f, x, e1, e2, pl) -> LetRec(f, x, (comp sa e1), (comp sa e2), pl)
  | If(e1, e2, e3) -> inlineNfa sa (If((comp sa e1), (comp sa e2), (comp sa e3)))
  | Fun(x, e, pStack) -> Fun(x, (comp sa e), pStack)
  | FunRec(f, x, e, pStack) -> FunRec(f, x, (comp sa e), pStack)
  | Call(f, a) -> inlineNfa sa (Call((comp sa f), (comp sa a)))
  | Phi(dfa, e) -> Phi(dfa, (comp sa e)) 
  | Read s -> inlineNfa sa (Read s)
  | Write s -> inlineNfa sa (Write s)
  | Send(e, s) -> inlineNfa sa (Send((comp sa e), s));;

let eval (e : expr) (env : ivalue env) (sa : nfa) (pStack: permissionStack) : ivalue = match sa with 
  | (initialState, _, _, _) -> let (result, _) = ieval (comp sa e) env (GState initialState) pStack in result;;

(* We won't be implementing the EM again. This is simply here to show the whole mechanism is still around *)

let myDelta (s, e) = match (s, e) with
  | (0, Read _) -> Some 1
  | (0, _) -> Some 0
  | (1, Send(_, _)) -> None 
  | (1, _) -> Some 1
  | _ -> None;;

let mySa = (0, 1, myDelta, "send after read detected");;

let noWaR:dfa =
  { states = [0;1;2];
    sigma = ['r';'w'];
    start = 0;
    transitions = [
      (0,'w',0);
      (0,'r',1);
      (1,'r',1);
      (1,'w',2);
      (2,'w',2);
      (2,'r',2)
    ];
    accepting = [0;1]
  };;
  
(* our test cases *) 
(* recursion test taken straight off the course material *)  
let myRP : expr =
  LetRec("fact", "n",
         If(Prim("=",Var "n",CstI(0)),
            CstI(1),
            Prim("*",Var"n",
                 Call(Var"fact",
                      Prim("-",Var"n",CstI(1))))),
         Call(Var"fact",CstI(9)), []);;

eval myRP [] mySa [];;

dfa_overlord#clearHistory;;

(* accepted execution test *)
let goodTest : expr = 
	Phi(noWaR, 
		Let("f", 
			Fun("x", 
				Let("g", 
					Fun("y",Read("test"),[P_Write;P_Read]), 
					Call(Var "g", Write("test"))), 
			[P_Write;P_Read]), 
		Call(Var "f", CstI(0)))
	);;

(* always returns 0 *)
eval goodTest [] mySa [];;

dfa_overlord#clearHistory;;

(* failed execution test *)
let badTest : expr = Phi(noWaR, Let("f", Fun("x", Let("g", Fun("y",Write("test"),[P_Write;P_Read]), Call(Var "g", Read("test"))), [P_Write;P_Read]), Call(Var "f", CstI(0))));;

(* always fails *)
eval badTest [] mySa [];;



(* Utility function for creating strings for collecting semantics *)
open Core_kernel
open Scilla_base
open Identifier
open ParserUtil
open Syntax
open EvalUtil
open MonadUtil
open PatternMatching
open Stdint
open ContractUtil
open EvalTypeUtilities
open EvalIdentifier
open EvalType
open EvalLiteral
open EvalSyntax
open SemanticsUtil
open TypeChecker
module CU = ScillaContractUtil (ParserRep) (ParserRep)

let init_log = ([],[])

(* Finding all variables that have flown into variable x - as a String *)
let rec trace_flow (prev_f: ((String.t * SType.t option) * (String.t * SType.t option)) list) (v: String.t) acc =
    match List.find prev_f ~f:(fun x -> String.equal (fst @@ fst x) v) with
    | None -> List.rev acc
    | Some (v1, v2) -> trace_flow prev_f (fst v2) (v2 :: acc)

(*Update: handles type *)
(* let trace_flow (prev_f: ((String.t * SType.t option) * String.t) list) (v: String.t) =
    let ty_dict = ref [] in
    let rec step_flow (prev_f: ((String.t * SType.t option) * String.t) list) (v: String.t) acc =
        match List.find prev_f ~f:(fun x -> String.equal (fst @@ fst x) v) with
        | None -> List.rev acc
        | Some (v1, v2) -> trace_flow prev_f v2 (v2 :: acc) *)
    
(*Product flows to string *)
let flow_to_string (f_l: ((String.t * SType.t option) * (String.t * SType.t option)) list) =
    let s_l = List.map ~f:(fun ((x, ty), _) ->
        let trace = trace_flow f_l x [] in
        (*TODO: FIX THIS TO INCLUDE PRINTING OUT TYPES *)
        let s = String.concat ~sep:" <- " (List.map trace ~f:(fun (x,y) -> x)) in
        let tys = if Option.is_empty ty then "__" else SType.pp_typ @@ Option.value_exn ty in
        sprintf "%s: %s -> (%s)" x tys s
    ) f_l in 
    String.concat ~sep:"\n" s_l


(* Used in eval_runner to print output *)
let output_seman log_l =
    (* let filtered_log = List.filteri (snd log_l) ~f:(fun i _ -> i > 209) in *)
    let filered_flow = List.filteri (fst log_l) ~f:(fun i _ -> i > 103) in
    let filtered_log = List.filter (snd log_l) ~f:(fun s -> not (String.equal s "")) in 
    let edit_flow = flow_to_string filered_flow in
    "\nLogging sequence: \n" ^
    (String.concat ~sep:"\n" filtered_log) ^ 
    (* "\n" ^ flow ^  *)
    "\n\nFlows: \n" ^ edit_flow ^ "\n"

let to_string = SIdentifier.as_string

(* open TypeChecker
open TypeUtil *)

(* Makes all Literals into strings other than GasExpr *)
let rec no_gas_to_string l =
    (* let tenv = TEnv.mk () in
    let typed_expr = TypeChecker.type_expr l tenv TypeChecker.init_gas_kont (Uint64.of_int 0) in *)
    match l with 
        | Literal l -> "Lit " ^ (Env.pp_value l)
        | Var i -> "Variable " ^ SIdentifier.as_string i
        | Let (i1, _, i2, _)  -> "Let " ^ to_string i1 ^ " = " ^ (no_gas_to_string @@ fst i2) (*Because we get Gas next*)
        | Message _ -> "Message"
        | Fun (i, ty, body) -> sprintf "Fun (Var %s: %s): Body: %s " (to_string i) (SType.pp_typ ty) (no_gas_to_string (fst body))
        | App (i, i_l) -> "App " ^ to_string i ^ " --to--> (" ^ (String.concat ~sep:", " (List.map ~f:(fun x -> to_string x) i_l)) ^ " )"   
        | Constr (i, _, _) -> "Constr " ^ to_string i
        | MatchExpr (i, _) -> "MatchExpr " ^ to_string i
        | Builtin _ -> "Builtin"
        | TFun (i, _) -> "TFun " ^ to_string i
        | TApp (i, _) -> "TApp" ^ to_string i
        | Fixpoint _ -> "Fixpoint"
        | GasExpr (_, e) -> no_gas_to_string (fst e)


(* **********************************************

Printing semantics

************************************************ *)
(*Printing a Let expr*)
let let_semantics i lhs lval =
    sprintf "Let: %s <- (%s) = (%s)" (to_string i) (no_gas_to_string @@ fst lhs) (Env.pp_value lval)

(* Printing Variable expr*)
let var_semantics i v = 
    sprintf "Variable: %s -> (%s)" (to_string i)(Env.pp_value v)

(* Printing Application expr *)
let app_semantics i i_l = 
    sprintf "App: %s ---to---> (%s)" (to_string i) (String.concat ~sep:", " (List.map ~f:(fun x -> to_string x) i_l))

(* Printing Fun expr *)
let fun_semantics i ty body =
    sprintf "Fun: Var %s: %s : (%s)" (to_string i) (SType.pp_typ ty) (no_gas_to_string body)

(* Printing Message *) 
let mes_semantics bs = 
    sprintf "Message: [%s]" @@
        String.concat ~sep: ", " (List.map bs (fun (x1, x2) -> x1))

let constr_semantics constr =
    sprintf "Const: %s" (no_gas_to_string constr)

let match_semantics x =
    sprintf "MatchExpr: %s" (to_string x)

let tfun_semantics tv body =
    sprintf "TFun: Var %s: (%s)" (to_string tv) (no_gas_to_string body)

let tapp_semantics tf arg_types =
    sprintf "TApp: %s --to--> (%s)" (to_string tf) (String.concat ~sep:", " (List.map ~f:(fun x -> SType.pp_typ x) arg_types))

module TC = TypeChecker.ScillaTypechecker (ParserRep) (ParserRep)
open TC.TypeEnv.TEnv

(* Adding v2 flowed into v1. If v2 is a Literal expr, then record its type too*)
let new_flow v1 v2 (ty: SType.t option): ((String.t * LType.t option) * (String.t * LType.t option)) List.t =
    let v1' = (no_gas_to_string v1, ty) in
    match v2 with
    | Literal l -> 
        begin
        match literal_type l with
        | Ok ty' -> [(v1', (no_gas_to_string v2, Some ty'))]
        | Error _ -> failwith ""
        end
    | _ -> [(v1', (no_gas_to_string v2, None))]


(* File: mp3.ml *)

open Mp3common

(* Problem 1 *)
let rec import_list lst = match lst with
						[a] -> BinOpAppExp (ConsOp,
											(BinOpAppExp 
												(CommaOp,
												(ConstExp (IntConst (fst a) ) ), 
												(ConstExp (IntConst (snd a) ) ) ) ),
											(ConstExp NilConst) ) |
						h :: t -> BinOpAppExp (ConsOp,
											(BinOpAppExp 
												(CommaOp,
												(ConstExp (IntConst (fst h) ) ),
												(ConstExp (IntConst (snd h) ) ) ) ),
											(import_list t) )

		 

(* Problem 2 *)
let pair_sums = 
			LetRecInExp
				("pair_sums",
				"lst",
				(IfExp ( 
					(BinOpAppExp
						(EqOp,
						(VarExp "lst"),
						(ConstExp NilConst) )
					), 
					(ConstExp NilConst),
					(LetInExp 
						("x",
						(MonOpAppExp (
							HdOp, 
							(VarExp "lst") 
							)
						),
						(BinOpAppExp 
							(
							ConsOp,
							(BinOpAppExp
								(
								IntPlusOp,
								MonOpAppExp
									(FstOp,
									(VarExp "x") )
								,
								MonOpAppExp
									(SndOp,
									(VarExp "x") )
								)
							)
							,
							(AppExp
								(
								(VarExp "pair_sums"),
								(MonOpAppExp
									(
									TlOp,
									(VarExp "lst") )
								) ) 
							) )	
						) )
					)
				)

				), 

				(
				AppExp
					(
					(VarExp "pair_sums"),

					(import_list [(7,1); (4,2); (6,3)])
					)
				)
			)

(* Problem 3 *)
let rec count_const_in_exp exp =  match exp with
								VarExp s -> 0 |
								ConstExp a -> 1 |
								MonOpAppExp (op, e) -> count_const_in_exp e |
								BinOpAppExp (op, e1, e2) -> count_const_in_exp e1 +
														count_const_in_exp e2 |
								IfExp (e1, e2, e3) -> count_const_in_exp e1 +
													count_const_in_exp e2 +
													count_const_in_exp e3 |
								AppExp (e1, e2) -> count_const_in_exp e1 +
												count_const_in_exp e2 |
								FunExp (f,e) -> count_const_in_exp e |
								LetInExp (var, e1, e2) ->  count_const_in_exp e1 +
														count_const_in_exp e2 |
								LetRecInExp (f, x, e1, e2) -> count_const_in_exp e1 +
														count_const_in_exp e2
(* Set subtraction, evaluates to eorg - erem *)
let sub eorg erem = (List.filter (fun x -> not (List.mem x erem) ) eorg)

(* Set union, evaluates to l1 U l2 *)
let union l1 l2 = List.filter (fun x -> (List.mem x l1)) l2

(* Set intersection *)
let inter l1 l2 = sub (l1 @ l2) (union l1 l2)

(* Problem 4 *)
let rec freeVarsInExp exp = match exp with 
								VarExp s -> [s] |
								ConstExp v -> [] |
								IfExp (e1, e2, e3) -> 
										let fv1 = freeVarsInExp e1 in
										let fv2 = freeVarsInExp e2 in
										let fv3 = freeVarsInExp e3 in
										inter (inter fv1 fv2) fv3 |
								FunExp (s, e) -> sub 
												(freeVarsInExp e) [s] |
								LetInExp (var, e1, e2) ->
										inter (freeVarsInExp e1)
												(sub (freeVarsInExp e2) [var]) |
								LetRecInExp (f, x, e1, e2) ->
										let fv1 = freeVarsInExp e1 in
										let fv2 = freeVarsInExp e2 in
										inter (sub fv1 [f; x]) (sub fv2 [f]) |
								FunExp (f, e) -> freeVarsInExp e |
								AppExp (e1, e2) ->
										let fv1 = freeVarsInExp e1 in
										let fv2 = freeVarsInExp e2 in
										inter fv1 fv2 |
								MonOpAppExp (op, e) -> freeVarsInExp e |
								BinOpAppExp (op, e1, e2) ->
										let fv1 = freeVarsInExp e1 in
										let fv2 = freeVarsInExp e2 in
										inter fv1 fv2 |
								_ -> []

(* Problem 5 *)
let rec cps_exp e k =  match e with 
						VarExp s -> VarCPS (k, s) |
						ConstExp c -> ConstCPS (k, c) |
						IfExp (e1, e2, e3) ->
							cps_exp e1 
								(
									let a = freshFor (freeVarsInExp e1 @ freeVarsInExp e2 @ freeVarsInExp e3) in
									FnContCPS (a, ( IfCPS (a, (cps_exp e2 k), (cps_exp e3 k) ) ) )
								) |
						AppExp (f, x) -> 
							cps_exp x
							(
							let v2 = freshFor (freeVarsInExp f @ freeVarsInContCPS k) in
								let v1 = freshFor (v2 :: freeVarsInContCPS k) in
										(
											FnContCPS (v2, (
												cps_exp f 
													(
														FnContCPS (v1,
															AppCPS (k, v1, v2)
														)
													) 
												)
											)
										)
							)
							|

						BinOpAppExp (op, e1, e2) ->
							cps_exp e2
							(
							let v2 = freshFor (freeVarsInExp e1 @ freeVarsInContCPS k) in
								let v1 = freshFor (v2 :: freeVarsInContCPS k) in
									(
										FnContCPS(v2, (

											cps_exp e1
												(
													FnContCPS(v1,
														BinOpAppCPS (k, op, v1, v2)
													)

												)
											)
										)

									)
							) |

						MonOpAppExp (op, e1) ->

							cps_exp e1
							(
							let v = freshFor (freeVarsInExp e1 @ freeVarsInContCPS k) in
								(
									FnContCPS(v,
										MonOpAppCPS (k, op, v)
									)
								)
							) |

						FunExp (parameter, e1) ->
								FunCPS (
									k,
									parameter,
									Kvar,
									cps_exp e1 (ContVarCPS Kvar)
								)
						|
						LetInExp (x, e1, e2) ->
							cps_exp e1
							(
								FnContCPS
								(
									x,
									cps_exp e2 k
								)
							)


							



%% -*- mode: prolog; coding: utf-8 -*-

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :- predicate_property(new_atom(_,_), built_in) ->
                     new_atom(X, A);
                 gensym(X, A).
				 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Jad Yammine 1067212				Annie-Pier Coulombe 1067670 %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Description de la syntaxe des termes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% wf(+E)
%% Vérifie que E est une expression syntaxiquement correcte.
%% Cette règle est inutile en soit, elle ne set qu'à documenter la forme des
%% termes du langage μPTS.

%% D'abord les termes du langage interne.
wf(X) :- identifier(X); integer(X); float(X).       %Une variable ou un nombre.
wf(fun(X, T, E)) :- identifier(X), wf(T), wf(E).    %Une fonction.
wf(app(E1, E2)) :- wf(E1), wf(E2).                  %Un appel de fonction.
wf(pi(X, T1, T2)) :- identifier(X), wf(T1), wf(T2). %Le type d'une fonction.
wf(forall(X, T, B)) :- identifier(X), wf(T), wf(B). 
												%Le type d'une fonction implicite.
wf(let(X, T, E1, E2)) :- identifier(X), wf(T), wf(E1), wf(E2). %Definition locale.

%% Puis les éléments additionnels acceptés dans le langage source.
wf(fun(X, B)) :- identifier(X), wf(B).
wf(let(X, E1, E2)) :- identifier(X), wf(E1), wf(E2).
wf(let(Decls, E)) :- wf_decls(Decls), wf(E).
wf((T1 -> T2)) :- wf(T1), wf(T2).
wf(forall(X, B)) :- (identifier(X); wf_ids(X)), wf(B).
wf((E : T)) :- wf(E), wf(T).
wf(E) :- E =.. [Head|Tail], identifier(Head), wf_exps(Tail).
wf(X) :- var(X).       %Une métavariable, utilisée pour l'inférence de type.

%% identifier(+X)
%% Vérifie que X est un identificateur valide.
identifier(X) :- atom(X),
                 \+ member(X, [fun, app, pi, forall, (->), (:), let, [], (.)]).

wf_exps([]).
wf_exps([E|Es]) :- wf(E), wf_exps(Es).
wf_ids([]).
wf_ids([X|Xs]) :- identifier(X), wf_ids(Xs).
wf_decls([]).
wf_decls([X = E|Decls]) :-
    wf_decls(Decls), wf(E),
    (X = (X1 : T) -> wf(T), X1 =.. Ids, wf_ids(Ids);
     X =.. [F|Args], identifier(F), wf_args(Args)).
wf_args([]).
wf_args([X:T|Args]) :- wf_args(Args), identifier(X), wf(T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Manipulation du langage interne %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Occasionnellement pendant l'inférence de types, il se peut qu'une
%% métavariable apparaisse dans un terme du langage interne.  Donc les
%% prédicats ci-dessous font souvent attention à tester le cas `var(MV)`
%% (accompagné d'un `cut`) pour veiller à ne pas instancier cette
%% métavariable par inadvertance, parce que cela mène sinon très vite à des
%% boucles sans fin difficiles à déboguer.

%% subst(+Env, +X, +V, +Ei, -Eo)
%% Remplace X par V dans Ei.  V et Ei sont des expressions du langage interne.
%% Les variables qui peuvent apparaître libres dans V (et peuvent aussi apparaître
%% dans Ei) doivent toutes être incluses dans l'environnement Env.
%% Cette fonction évite la capture de nom, e.g.
%%
%%     subst(Env, x, y, fun(y,int,x+y), R)
%%
%% ne doit pas renvoyer `R = fun(y,int,y+y)` mais `R = fun(y1,int,y+y1)`.
subst(_, _, _, MV, Eo) :-
    %% Si MV est un terme non-instancié (i.e. une métavariable), la substitution
    %% ne peut pas encore se faire.  Dans certains cas, on pourrait renvoyer
    %% app(fun(X,Y),V), mais en général c'est problématique.
    %% Donc on impose ici la contrainte que les metavars ne peuvent pas
    %% faire référence à X.
    %% Le faire vraiment correctement est plus difficile.
    var(MV), !, Eo = MV.
subst(_, X, V, X, V).
subst(_, _, _, E, E) :- identifier(E); integer(E).
subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)) :-
    subst(Env, X, V, Ti, To),
    (X = Y ->
         %% If X is equal to Y, X is shadowed, so no subst can take place.
         Y1 = Y, Bo = Bi;
     (member((Y : _), Env) ->
          %% If Y appears in Env, it can appear in V, so we need to
          %% rename it to avoid name capture.
          genatom(Y, Y1),
          subst([], Y, Y1, Bi, Bi1);
      Y1 = Y, Bi1 = Bi),
     %% Perform substitution on the body.
     subst(Env, X, V, Bi1, Bo)).
subst(Env, X, V, pi(Y, Ti, Bi), pi(Y1, To, Bo)) :-
    subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)).
subst(Env, X, V, forall(Y, Ti, Bi), forall(Y1, To, Bo)) :-
    subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)).
subst(Env, X, V, app(E1i, E2i), app(E1o, E2o)) :-
    subst(Env, X, V, E1i, E1o), subst(Env, X, V, E2i, E2o).


%% apply(+Env, +F, +Arg, -E)
%% Les règles d'évaluations primitives.  Env donne le types des variables
%% libres qui peuvent apparaître.
apply(Env, fun(X, _, B), Arg, E) :- \+ var(B), subst(Env, X, Arg, B, E).
apply(_,   app(+, N1), N2, N) :- integer(N1), integer(N2), N is N1 + N2.
apply(_,   app(-, N1), N2, N) :- integer(N1), integer(N2), N is N1 - N2.


%% normalize(+Env, +Ei, -Eo)
%% Applique toutes les réductions possibles sur Ei et tous ses sous-termes.
%% Utilisé pour tester si deux types sont équivalents.
normalize(_, MV, Eo) :- var(MV), !, Eo = MV.
normalize(_, V, V) :- (integer(V); float(V); identifier(V)).
normalize(Env, fun(X, T, B), fun(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn), normalize([X:T|Env], B, Bn).
normalize(Env, pi(X, T, B), pi(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn), normalize([X:T|Env], B, Bn).
normalize(Env, forall(X, T, B), forall(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn), normalize([X:T|Env], B, Bn).
normalize(Env, app(E1, E2), En) :-
    normalize(Env, E1, E1n),
    normalize(Env, E2, E2n),
    (apply(Env, E1n, E2n, E) ->
         normalize(Env, E, En);
     En = app(E1n, E2n)).

%% equal(+Env, +T1, +T2)
%% Vérifie que deux expressions sont égales.
%% Utilisé pour vérifier l'égalité des types au niveau du langage interne, où
%% `forall` and `pi` sont équivalents.
equal(_, E, E).
equal(Env, forall(X1, T1, E1), E2) :- equal(Env, pi(X1, T1, E1), E2).
equal(Env, E2, forall(X1, T1, E1)) :- equal(Env, E2, pi(X1, T1, E1)).
equal(Env, fun(X1, T1, E1), fun(X2, T2, E2)) :-
    equal(Env, T1, T2),
    Env1 = [X1:T1|Env],
    (X1 = X2 ->
         E3 = E2;
     %% Si X1 et X2 sont différents, renomme X2 dans E2!
     subst(Env1, X2, X1, E2, E3)),
    equal(Env1, E1, E3).
equal(Env, pi(X1, T1, E1), pi(X2, T2, E2)) :-
    equal(Env, fun(X1, T1, E1), fun(X2, T2, E2)).
equal(Env, E1, E2) :-
    normalize(Env, E1, E1n),
    normalize(Env, E2, E2n),
    ((E1 = E1n, E2 = E2n) ->
         %% There was nothing to normalize :-(
         fail;
     equal(Env, E1n, E2n) -> true).
        

%% verify(+Env, +E, +T)
%% Vérifie que E a type T dans le contexte Env.
%% E est une expression du langage interne (i.e. déjà élaborée).
%% Elle ne devrait pas contenir de métavariables.
verify(Env, E, T) :-
    verify1(Env, E, T1) ->
        (equal(Env, T, T1) -> true;
         write(user_error, not_equal(T, T1)), nl(user_error), fail);
    write(user_error, verify_failure(E)), nl(user_error), fail.

%% verify1(+Env, +E, -T)
%% Calcule le type de E dans Env.
verify1(_, MV, _) :- var(MV), !, fail.
verify1(_, N, int) :- integer(N).
verify1(_, N, float) :- float(N).
verify1(Env, X, T) :-
    %% `member(X:T, Env)` risquerait de trouver dans Env un autre X que le
    %% plus proche, au cas où il y a plusieurs X dans l'environnement.
    atom(X), (member(X:T1, Env) -> T = T1; fail).
verify1(Env, fun(X, T1, E), forall(X, T1, T2)) :-
    verify(Env, T1, type),
    verify1([X:T1|Env], E, T2).
verify1(Env, app(F, A), T2) :-
    verify(Env, F, pi(X, T1, T3)),
    verify(Env, A, T1),
    subst(Env, X, A, T3, T2).
verify1(Env, pi(X, T1, T2), type) :-
    verify(Env, T1, type), verify([X:T1|Env], T2, type).
verify1(Env, forall(X, T1, T2), T) :- verify1(Env, pi(X, T1, T2), T).
verify1(Env, let(X, T, E1, E2), Tret) :-
    verify(Env, T, type),
    Env1 = [X:T|Env],
    verify(Env1, E1, T),
    verify1(Env1, E2, Tret).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Élaboration du langage source vers le langage interne %%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


get_tail([_|Tail],  Tail).
get_head([Head|_], Head).

l_empty([], true).
l_empty([_|_], false).

%% appeler a travers expand pour transformer x(t,z,g) -> app(app(app(x,t),z),g)
exp_fct(R1 , [Head|Tail], R):- l_empty(Tail, X),
	(X = false ->
		exp_fct((app(R1,Head)), Tail, R); 
	X = true ->
		R = app(R1,Head)).


build_f_call(MV, _) :- var(MV), !, fail.
build_f_call((X+Y), app(app(+,X),Y)).
build_f_call((X-Y), app(app(-,X),Y)).
build_f_call((X*Y), app(app(*,X),Y)).
build_f_call((X/Y), app(app(/,X),Y)).
build_f_call(E, R):- E=..[Head|Tail],exp_fct(Head , Tail, R).

	
%%exp_fct(h0,(E),r,newtail):- E =.. [Head|Tail],r=expfct(h0,get_tail(Tail),r
%%	x1 = app(h0,Head), get__tail(Tail, newtail),y1 = 

	
%%exp_fct(MV,[],Mv,[]):- identifier(MV).
%%exp_fct(h0, tail0,app(h1,t1)):-
%%				 tail0 =.. [Head|Tail],r=expfct(h0,get_tail(Tail),r
%%	x1 = app(h0,Head), get__tail(Tail, newtail),y1 = 
	
%%exp_fun(R1 , [Head|Tail], R):- l_empty(Tail, X),
%%	(X = false ->
%%		exp_fun((R1,Head), Tail, R); 
%%	X = true ->
%%		R = (R1,Head)).	

exp_fun([Head|Tail],X,fun(X, Head,R)):- 
	get_head(Tail,H), write(H), build_fun(H,R).

build_fun(MV, _) :- var(MV), !, fail.
build_fun((X+Y), app(app(+,X),Y)).
build_fun((X-Y), app(app(-,X),Y)).
build_fun((X*Y), app(app(*,X),Y)).
build_fun((X/Y), fun(X,float,fun(Y,float, float))).
build_fun(E, R):- E=..[Head|Tail], Head = fun,
				get_head(Tail,H1),
				exp_fun(Tail, H1, R).
%%=============================================================================	
%%=============================================================================	
%%%%%%%%%%%%%%%%%%%% 			expand		:%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%=============================================================================	

	
%% expand(+Ei, -Eo)
%% Remplace un élement de sucre syntaxique dans Ei, donnant Eo.
%% Ne renvoie jamais un Eo égal à Ei.
expand(MV, _) :- var(MV), !, fail.
expand((T1 -> T2), pi(X, T1, T2)) :- genatom('dummy_', X).
%% !!!À COMPLÉTER!!!


expand((X+Y), app(app(+,X),Y)).
expand((X-Y), app(app(-,X),Y)).
%%expand((X*Y), app(app(*,X),Y)).
%%expand((X/Y), app(app(/,X),Y)).


expand((X/Y), fun(X,float,fun(Y,float, float))).




%%expand(E, R):- E=..[Head|Tail],	
%%			(Head = fun ->
%%				build_fun(E,R);
%%			build_f_call(E, R)).
			
			
%%write(yolo),
%%get_head(Tail,H1),get_tail(Tail,Ta1), exp_fun(Ta1, H1, R);
%%expand([Head|Tail], R):-exp_fct(Head , Tail, R).
%%expand(X(Y), app(X,Y)).
%% subst(+Env, +X, +V, +Ei, -Eo)
%% check(+Env, Ei, +T, -Eo)
%% infer(+Env, +Ei, -Eo, -T)
%%check(Env, E1, E3, Eo1):- normalize(Env, E2, E3),infer(Env,E1,Eo1,E2).
	
%%check(Env, E1, T, R):- normalize(Env, E2, E3),infer(Env,E1,Eo1,E2).

		%%R = [Head|Tail];write(Head),write(Tail),
		%%get_head(Tail,H1),get_tail(Tail,Ta1), exp_fun(Ta1, H1, R);
	
	
%%expand(E, R):- write(Head), E=.. [Head|Tail],write(Head),
%%	(Head = fun -> 
%%		get_tail(Tail,R1), exp_fun(Tail , R1, R));
%%	exp_fct(Head , Tail, R)).



%%expand((int -> int), pi(X, T1, T2)).
%%expand(fun(X,)
%%expand(x([e1:e2]), expand(e2(app(x,e1)), r)).
%%expand([E1:E2:E], expand(E(app(E1,E2)), r)).
%%expand(X:Y, f).



%%expand(fun(E),fun(E));
%%expand(X(Y), app(X,Y)).
%%expand(E, R):-

%%app(app(app(X,E1),E2),E3)

%%X(E1,E2,E3)
	
%%get_head([_|_], Tail):- E=.. [Head|Tail].
	



%%=============================================================================	
%%=============================================================================	
%%%%%%%%%%%%%%%%%%%% 			coerce		:%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%=============================================================================	





%% coerce(+Env, +E1, +T1, +T2, -E2)
%% Transforme l'expression E1 (qui a type T1) en une expression E2 de type T2.
coerce(Env, E, T1, T2, E) :-
    T1 = T2;
    normalize(Env, T1, T1n),
    normalize(Env, T2, T2n),
    T1n = T2n.        %T1 = T2: rien à faire!
%% !!!À COMPLÉTER!!!
coerce(Env, E1,T1, T2,Eo1):- write(yolo),subst(Env,X,E3,E2, T1), coerce(Env, E1,
					forall(X,E2,E3),T2, Eo1).
					
coerce(Env, E1, bool, T, Eo1):- coerce(Env,E1, int, T, Eo1).
coerce(Env, E1, float, T, Eo1):- coerce(Env,E1, int, T, Eo1).

						%% coerce(Env,E1,forall(X,E2,E3), 
%%infer(_, app(x,y),_,_):-write(app(x,y)).

%% subst(+Env, +X, +V, +Ei, -Eo)
%% check(+Env, Ei, +T, -Eo)
%%
%%infer(Env,nil, app(nil,int),forall(T,type,list(T,0))).
%%infer(Env,nil, app(nil,int),list(int,0).
%%=============================================================================	
%%=============================================================================	
%%%%%%%%%%%%%%%%%%%% 			infer		:%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%=============================================================================	



%% infer(+Env, +Ei, -Eo, -T)
%% Élabore Ei (dans un contexte Env) en Eo et infère son type T.
infer(_, MV, MV, _) :- var(MV), !.            %Une expression encore inconnue.
infer(Env, Ei, Eo, T) :- expand(Ei, Ei1), infer(Env, Ei1, Eo, T).
infer(_, X, X, int) :- integer(X).
infer(_, X, X, float) :- float(X).
infer(Env, (Ei : T), Eo, T1) :- check(Env, T, type, T1), 
	check(Env, Ei, T1, Eo).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% Elaborate environnement:%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

infer(_,type,type,type).
infer(_,int, int, type).
infer(_,(int -> float), pi(x,int,float),type).
infer(_,(int -> bool), pi(x,int,bool),type).
infer(_, (float -> int),pi(x,float,int),type).
infer(_, (float -> float -> int), pi(x,float,pi(x,float,int)),type).
infer(_, (int -> int -> int), pi(t, int, pi(n, int, int)), type).
infer(_, (float -> float -> float), pi(t,float,pi(n,float,float)),type).
infer(_, (type -> int -> type), pi(t,type,pi(n,int,type)),type).
infer(_, forall(t, list(t, 0)), pi(t,type,pi(t, type,pi(0,int,type))),type).
infer(_,forall([t,n],t -> list(t, n) -> list(t, n + 1)),
			pi(t, type, pi(n, int, pi(n, pi(t, type, pi(n, int, type)), 
            pi(t, type, pi(n+1, int, type))))),type).
infer(_, forall(t, (bool -> t -> t -> t)), 
                                        pi(t, type, pi(x, bool, pi(x, type, 
                                            pi(x, type, type)))),
                                               type).
	

infer(Env,X, X, E ):- member(X:E,Env).

infer(Env, pi(X,E1,E2), pi(X,Eo1,Eo2), type):- 
		check([X:E1|Env], E2, type, Eo2),
		check(Env, E1, type, Eo1).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% Building process of fun %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

	
infer(Env, fun(X,E2), fun(X,int, Eo2),pi(X,int,int)):-
				check([X:int|Env],E2,int,Eo2).
infer(Env, fun(X,E2), fun(X,int, Eo2),pi(X,int,bool)):- 
				check([X:int|Env],E2,bool,Eo2).
infer(Env, fun(X,E2), fun(X,int, Eo2),pi(X,int,float)):-
				check([X:int|Env],E2,float,Eo2).
infer(Env, fun(X,E2), fun(X,float, Eo2),pi(X,float,int)):-
				check([X:float|Env],E2,int,Eo2).
infer(Env, fun(X,E2), fun(X,int, Eo2),pi(X,int,type)):-
				check([X:int|Env],E2,type,Eo2).
infer(Env, fun(X,E2), fun(X,type, Eo2),pi(X,type,int)):-
				check([X:type|Env],E2,int,Eo2).


infer(Env, fun(X,T1,E2), fun(X,T1, Eo2),pi(X,T1,T2)):- 
	infer([X:T1|Env], E2,Eo2,T2), check(Env, T1, type, _).
	
%% subst(+Env, +X, +V, +Ei, -Eo)
%% check(+Env, Ei, +T, -Eo)
%% infer(+Env, +Ei, -Eo, -T)
%% Élabore Ei (dans un contexte Env) en Eo et infère son type T.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% Building block infer cons:  %%%%%%%%%%%%%%%%%%%%%%55%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%sample(cons(13,nil)).
%%sample(cons(1.0, cons(2.0, nil))).
infer(Env,cons(E1, E2), cons(Eo1,Eo2), 
		TT):- write(yolo),
		(E2 = nil-> 
			infer(Env, E2,Eo2,pi(t,type,pi(t, type,pi(0,int,type))));
			TT = pi(T,type,pi(E1,T,pi(N,int, pi(Y,list(app(T,1)),
				list(app(T,(N1 is N+1)))))));
		TT = pi(T,type,pi(E1,T,pi(N,int, pi(Y,list(app(T,N)),list(app(T,(N1 is N+1)))))))
		
		
		).
	%%	check(Env, E1, T, Eo1), 
	%%		infer(Env, E2,Eo2,pi(T,type,pi(E2,T,pi(N,int, pi(Y,list(app(T,N1)),nil))))).
			
%% infer(+Env, +Ei, -Eo, -T)
			
%%infer(Env,nil, app(nil,int),forall(T,type,list(T,0))):-write(yolo).
%%infer(Env,nil, app(nil,int),list(int,0).
%%infer(Env, cons(E1, ):-write(yolo).

%%infer(cons )		
		
		
		
		
		%%pi(T,type,pi(X,T,pi(N,int, pi(Y,list,T))))	
	%%	pi
	%%	(T,type,pi(X, T,pi(0,int,type)))):-
	%%		infer([E1:T1|Env], E2,Eo2,T2), check(Env, E1, T, _).	
			
			
%%infer(_, forall(t, list(t, 0)), pi(t,type,pi(t, type,pi(0,int,type))),type).
%%			
%%infer(_,forall([t,n],t -> list(t, n) -> list(t, n + 1)),
%%			pi(t, type, pi(n, int, pi(n, pi(t, type, pi(n, int, type)), 
 %%           pi(t, type, pi(n+1, int, type))))),type).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%% Division : %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

infer(Env, app(app((/),E1), E2), app(app((/),Eo1), Eo2),
	pi(t,float,pi(n,float,float))):- write(yo),
	%%float):- write(yo),

		check(Env, E1, float, Eo1), check(Env, E2, float, Eo2).
		
%% check(+Env, Ei, +T, -Eo)
%%
%%infer(Env, app(E1,E2), app(Eo1,Eo2), T):- infer(Env,E1, Eo1, pi(X,E4,E5)),
%%	check(Env,E2, E4, Eo2), subst(Env, X, E2, E5, T).

%%infer(Env, app(app((/),E1),E2),app(app((/),Eo1),Eo2),float):-
%%	check(Env, E1,float,Eo1), check(Env, E1,float,Eo1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% app General case: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

infer(Env, app(E1,E2), app(Eo1,Eo2), T):- infer(Env,E1, Eo1, pi(X,E4,E5)),
	check(Env,E2, E4, Eo2), subst(Env, X, E2, E5, T).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% BESOIN REPARATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



infer(Env, forall(X,E1,E2), forall(X,Eo1,Eo2), type):-
						check(Env,E1,type,Eo1),
						check([X:E1|Env],E2,type, Eo2).

infer(Env, let(X,E1,E2,E3), let(X,Eo1,Eo2,Eo3), E4):- check(Env,E1,type,Eo1),
						check([X:E1|Env], E2, E1, Eo2),
						infer([X:E1|Env], E3, Eo3, E4).

infer(Env, let(X,E2,E3), let(X,Eo2,Eo3), E4):-
						infer([X:E1|Env],E2,E1,Eo2),
						infer([X:E1|Env],E3,Eo3,E4).
						
						
infer(Env, E1:E2, Eo1:Eo2, E2):- check(Env,E2,type,Eo2),
						check(Env, E1, E2,Eo1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%=============================================================================	
%%=============================================================================	
%%%%%%%%%%%%%%%%%%%% 			check		:%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%=============================================================================	


%% check(+Env, Ei, +T, -Eo)
%% Élabore Ei (dans un contexte Env) en Eo, en s'assurant que son type soit T.
check(_Env, MV, _, Eo) :-
    %% On ne fait pas l'effort de se souvenir du type des métavariables,
    %% donc on ne peut pas vérifier si elle a effectivement le type attendu.
    %% À la place, on accepte n'importe quel usage de métavariable, en
    %% espérant qu'elles sont utilisées correctement.  C'est généralement le
    %% cas de toute façon, et pour les cas restants on se repose sur le filet
    %% de sécurité qu'est `verify`.
    var(MV), !, Eo = MV.
check(Env, Ei, T, Eo) :- expand(Ei, Ei1), check(Env, Ei1, T, Eo).
%% !!!À COMPLÉTER!!!
check(Env, E1, E3, Eo1):- normalize(Env, E2, E3),infer(Env,E1,Eo1,E2).
check(Env, E1, forall(X,E2,E3), Eo1):- write(yolo),
	check(([X:E2|Env]), E1  , E3, Eo1).


%% Finalement, cas par défaut:
check(Env, Ei, T, Eo):-
    infer(Env, Ei, Eo1, T1),
    (coerce(Env, Eo1, T1, T, Eo) -> true).


%%check(Env, E1, pi(X,T1,T2),fun(X,T1,Eo2)) :- E1 = fun(X,E2), write(yo),
%%			check([X:T1|Env],E2,T2,Eo2).




%%check(Env, E1, forall(X,E2,E3),Eo1):-check([X:E2|Env],E1, E3,Eo1).
%%check(Env, fun(X,E1,E2), pi(X,T1,T2),fun(X,T1,E2) ) :-
%%		 check(Env, E1,T1,e1), check([E1:T1|Env],E2,T2,e2).
%%infer(Env, fun(X,T1,E2), fun(X,T1, Eo2),pi(X,T1,T2)):- 
%%	infer([X:T1|Env], E2,Eo2,T2), check(Env, T1, type, _),write(yolo).


	
	
	
	
	
%%check(Env, E1, pi(X,int,int),fun(X,int,Eo2)) :- 
%%				E1 = fun(X,E2),check([X:int|Env],E2,int,Eo2).
%%check(Env, E1, pi(X,int,bool),fun(X,int,Eo2)) :- 
%%				E1 = fun(X,E2),check([X:int|Env],E2,bool,Eo2).
%%check(Env, E1, pi(X,int,float),fun(X,int,Eo2)) :- 
%%				E1 = fun(X,E2),check([X:int|Env],E2,float,Eo2).
%%check(Env, E1, pi(X,float,int),fun(X,float,Eo2)) :- 
%%				E1 = fun(X,E2),check([X:float|Env],E2,int,Eo2).
%%check(Env, E1, pi(X,int,type),fun(X,int,Eo2)) :-
%%				 E1 = fun(X,E2),check([X:int|Env],E2,type,Eo2).
%%check(Env, E1, pi(X,type,int),fun(X,type,Eo2)) :-
%%				 E1 = fun(X,E2),check([X:type|Env],E2,int,Eo2).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Environnement initial et tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


elaborate_env(Env, [], Env).
elaborate_env(Env, [X:Ti|Envi], Envo) :-
    check(Env, Ti, type, To) ->
        (verify(Env, To, type) ->
             elaborate_env([X:To|Env], Envi, Envo));
    write(user_error, 'FAILED_TO_ELABORATE'(Ti)), nl(user_error), !, fail.

initenv(Env) :-
    elaborate_env(
        [type : type],
        [int :  type,
         float :  type,
         bool :  type,
         int_to_float : (int -> float),
         int_to_bool : (int -> bool),
         list : (type -> int -> type),
         (+) : (int -> int -> int),
         (-) : (int -> int -> int),
         (*) : (int -> int -> int),
         (/) : (float -> float -> float),
         (<) : (float -> float -> int),
         if : forall(t, (bool -> t -> t -> t)),
         nil :  forall(t, list(t, 0)),
         cons : forall([t,n],
                       (t -> list(t, n) ->
                            list(t, n + 1)))],
        Env).

%% Quelques expressions pour nos tests.
sample(1 + 2).
sample(1 / 2).
%%sample(cons(13,nil)).
%%sample(cons(1.0, cons(2.0, nil))).
%%sample(let([fact(n:int) = if(n < 2, 1, n * fact(n - 1))],
%%           fact(44))).
%%sample(let([fact(n) : (int -> int) = if(n < 2, 1, n * fact(n - 1))],
%%           fact(45))).
%%sample(let([list1 : forall(a, (a -> list(a, 1))) = fun(x, cons(x, nil))],
%%           list1(42))).
%%sample(let([list1(x) : forall(a, (a -> list(a, 1))) = cons(x, nil)],
%%           list1(43))).
%%sample(let([pushn(n,l) : pi(n, _, (list(int,n) -> list(int,n+1))) = cons(n,l)],
%%           %% L'argument `n` ne peut être que 0, ici, et on peut l'inférer!
%%           pushn(_,nil))).

%% Roule le test sur une expression.
test_sample(Env, E) :-
    infer(Env, E, Eo, T) ->
        normalize(Env, T, T1),
        write(user_error, inferred(E, T1)), nl(user_error),
        write(user_error, verifying(Eo)), nl(user_error),
        (verify(Env, Eo, T) ->
             write(user_error, 'VERIFIED!!'), nl(user_error);
         write(user_error, 'FAILED_TO_VERIFY'(Eo)), nl(user_error));
    write(user_error, 'FAILED_TO_INFER'(E)), nl(user_error).

%% Roule le test sur chacune des expressions de `sample`.
test_samples :-
    initenv(Env), sample(E), test_sample(Env, E).
	
calls(E) :- initenv(Env), test_sample(Env,E).

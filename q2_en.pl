% Student name: NAME
% Student number: NUMBER
% UTORid: ID

% This code is provided solely for the personal and private use of students
% taking the CSC485H/2501H course at the University of Toronto. Copying for
% purposes other than this use is expressly prohibited. All forms of
% distribution of this code, including but not limited to public repositories on
% GitHub, GitLab, Bitbucket, or any other online platform, whether as given or
% with any changes, are expressly prohibited.

% Authors: Jingcheng Niu and Gerald Penn

% All of the files in this directory and all subdirectories are:
% Copyright c 2022 University of Toronto

:- ensure_loaded(csc485).
:- ale_flag(pscompiling, _, parse_and_gen).
lan(en).
question(q2).

bot sub [cat, sem, list, logic, func, qs, gap_struct].
    cat sub [q, det, gappable, has_sem] intro [logic:logic, qstore:list].
        has_sem sub [n, gappable] intro [sem:sem].
            gappable sub [np, verbal] intro [gap:gap_struct].
                verbal sub [v, vp, s] intro [subcat:list].

    gap_struct sub [none, np].

    sem sub [hacker, language, speak].

    list sub [e_list, ne_list].
        ne_list intro [hd:bot, tl:list].

    logic sub [free, scopal].
        scopal sub [lambda, quant] intro [bind:logic, body:logic].
            quant sub [exists, forall] intro [bind:qvar].
        free sub [op, app, qvar].
            op sub [and, imply] intro [lhs:logic, rhs:logic].
            app intro [f:func, args:list].
    func sub [lambda, sem].

    qs intro [l:logic, x:logic].

% Lexical entries (incomplete)
every ---> (
    logic: @lambda(F, 
                @lambda(P, 
                    @forall(Y, 
                        @apply(F, [Y]),
                        @apply(P, [Y])))),
    qstore:[],
    q).

a ---> (
    logic: @lambda(F, 
                @lambda(P, 
                    @exists(Y, 
                        @apply(F, [Y]),
                        @apply(P, [Y])))),
    qstore:[],
    q).

language ---> (n,
    logic: @lambda(X, @apply(Language, [X])),
    qstore:[],
    sem:(language, Language)).

hacker ---> (n,
    logic: @lambda(X, @apply(Hacker, [X])),
    qstore:[],
    sem:(hacker, Hacker)).

speaks ---> (v,
    logic: @lambda(Q, 
                @lambda(Z, 
                    @apply(Q, [
                        @lambda(X, @apply(Speak, [Z, X]))
                    ]))),
    qstore:[],
    subcat:[(np, sem:language), (np, sem:hacker)], % the subcat list should not be empty
    sem:(speak, Speak)).

% Phrase structure rules (incomplete)
np rule
    (np, sem:N_sem, logic: NP_logic, qstore: NP_qstore, gap:none) ===>
    cat> (q, logic: Q_logic),
    sem_head> (n, sem:N_sem, logic:N_logic, qstore: N_qstore),
    goal> apply_normalize_and_qaction(
        Q_logic, N_logic, N_qstore, NP_logic, NP_qstore
    ).

vp rule
    (vp, sem:V_sem, logic: VP_logic, qstore: NP_qstore, gap:Gap, subcat: VP_subcat) ===>
    sem_head> (v, sem:V_sem, logic:V_logic, subcat: V_subcat),
    cat> (np, logic:NP_logic, qstore: NP_qstore, gap:Gap, sem:NP_obj_sem, NP),
    goal> check_gap_and_normalize(V_logic, V_subcat, NP, VP_logic, VP_subcat).

s rule
    (s, sem:VP_sem, logic: S_logic, qstore: S_qstore, gap:(none, None), subcat:[]) ===>
    cat> (np, logic:NP_logic, qstore: e_list, gap:None, sem:NP_subj_sem),
    sem_head> (vp, sem:VP_sem, logic:VP_logic, qstore: VP_qstore, gap:None, subcat:[(np, sem:NP_subj_sem)]),
    goal> apply_normalize_and_retrieve(
        NP_logic, VP_logic, VP_qstore, S_logic, S_qstore
    ).

s_gap rule
    (s, sem:VP_sem, logic: S_logic, qstore: S_qstore, gap:(none, None), subcat:[]) ===>
    cat> (np, logic:NP_Obj_logic, qstore: NP_Obj_qstore, gap:None, sem:NP_obj_sem, NP_Obj),
    cat> (np, logic:NP_Sub_logic, qstore: e_list, gap:None, sem:NP_subj_sem),
    sem_head> (vp, sem:VP_sem, logic:VP_logic, qstore: VP_qstore, gap:Gap, 
                subcat:[(np, sem:NP_obj_sem), (np, sem:NP_subj_sem)], VP),
    goal> resolve_gap_and_normalize(NP_Sub_logic, VP, NP_Obj, S_logic, S_qstore).

% The empty category:
empty (np, sem:Sem, logic:Logic, qstore:QStore,
    gap:(sem:Sem, logic:Logic, qstore:QStore, gap:none)).


% Macros
lambda(X, Body) macro (lambda, bind:X, body:Body).
forall(X, Restr, Body) macro (forall, bind:X, body:(imply, lhs:Restr, rhs:Body)).
exists(X, Restr, Body) macro (exists, bind:X, body:(and, lhs:Restr, rhs:Body)).
apply(F, Args) macro (app, f:F, args:Args).

% extra helper goals
apply_normalize_and_qaction(LogicFunc, LogicArg, QStore, NewLogic, NewQStore) if
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic),
    qaction(Norm_logic, QStore, NewLogic, NewQStore).

apply_normalize_and_retrieve(LogicFunc, LogicArg, QStore, NewLogic, NewQStore) if
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic),
    retrieve(QStore, Norm_logic, NewQStore, NewLogic).

is_not_gap(none) if true.
is_gap(np) if true.

check_gap_and_normalize(
    V_logic, [(np, sem:NP_obj_sem), NP_subj], (np, logic: NP_logic, gap:Gap, sem:NP_obj_sem), VP_logic, [NP_subj]
    ) if
    is_not_gap(Gap),
    beta_normalize(@apply(V_logic, [NP_logic]), VP_logic).

check_gap_and_normalize(V_logic, V_subcat, (np, logic: NP_logic, gap:Gap), V_logic, V_subcat) if
    is_gap(Gap).

resolve_gap_and_normalize(
        NP_Sub_logic, 
        (vp, logic: VP_logic, gap:Gap), 
        (np, logic:NP_Obj_logic, qstore: NP_Obj_qstore), 
        S_logic, S_qstore
    ) if
    is_gap(Gap),
    beta_normalize(@apply(VP_logic, [NP_Obj_logic]), VP_Obj_logic),
    apply_normalize_and_retrieve(NP_Sub_logic, VP_Obj_logic, NP_Obj_qstore, S_logic, S_qstore).

% Helper goals
append([],Xs,Xs) if true.
append([H|T1],L2,[H|T2]) if append(T1,L2,T2).
is_empty([]) if true.

% Beta normalization goals
beta_normalize((lambda,Lambda),Lambda) if !,true.
beta_normalize((Input,bind:Bind,body:Body),(Output,bind:Bind,body:BetaBody)) if
    bn_quant(Input,Output),
    beta_normalize(Body,BetaBody).
beta_normalize((Input,lhs:LHS,rhs:RHS),(Output,lhs:BetaLHS,rhs:BetaRHS)) if
    bn_op(Input,Output),
    beta_normalize(LHS,BetaLHS),
    beta_normalize(RHS,BetaRHS).
beta_normalize(@apply(@lambda(X,Body),[X]),Beta) if 
    !,beta_normalize(Body,Beta).
beta_normalize((app,Apply),Apply) if true.

bn_quant(exists,exists) if true.
bn_quant(forall,forall) if true.
bn_op(and,and) if true.
bn_op(imply,imply) if true.

% Quantifier actions
store(Logic, QStore, @lambda(F, @apply(F,[X])), 
                     [(l:Logic, x:X)|QStore]) if true.

qaction(Logic, QStore, Logic, QStore) if true.
qaction(Logic, QStore, NewLogic, NewQStore) if
    store(Logic, QStore, NewLogic, NewQStore).

retrieve((Empty, []), Logic, Empty, Logic) if true.
retrieve([(l:QLogic, x:X)|T], Logic, T, NewLogic) if 
    beta_normalize(@apply(QLogic, [@lambda(X, Logic)]), NewLogic).

% Specifying the semantics for generation.
semantics sem1.
sem1(logic:S, S) if true.
sem1(sem:S, S) if true.

% Some examples
% You should write more
prect_test :- prec([a,hacker,speaks,every,language]).
translate_test :- translate([a,hacker,speaks,every,language]).
gen1_test :- gen((s, sem:speak, logic: @forall(X, @apply(language, [X]), @exists(Y, @apply(hacker, [Y]), @apply(speak, [Y|[X]]))))).
gen2_test :- gen((s, sem:speak, logic: @forall(X, @apply(hacker, [X]), @exists(Y, @apply(language, [Y]), @apply(speak, [X|[Y]]))))).

p0 :- (prec([every, hacker, speaks, every, hacker]); write('failed')), (write('\n'),nl). 
p1 :- (prec([every, hacker, every, hacker, speaks]); write('failed')), (write('\n'),nl). 
p2 :- (prec([every, hacker, speaks, every, language]); write('failed')), (write('\n'),nl). 
p3 :- (prec([every, language, every, hacker, speaks]); write('failed')), (write('\n'),nl). 
p4 :- (prec([every, hacker, speaks, a, hacker]); write('failed')), (write('\n'),nl). 
p5 :- (prec([a, hacker, every, hacker, speaks]); write('failed')), (write('\n'),nl). 
p6 :- (prec([every, hacker, speaks, a, language]); write('failed')), (write('\n'),nl). 
p7 :- (prec([a, language, every, hacker, speaks]); write('failed')), (write('\n'),nl). 
p8 :- (prec([every, language, speaks, every, hacker]); write('failed')), (write('\n'),nl). 
p9 :- (prec([every, hacker, every, language, speaks]); write('failed')), (write('\n'),nl). 
p10 :- (prec([every, language, speaks, every, language]); write('failed')), (write('\n'),nl). 
p11 :- (prec([every, language, every, language, speaks]); write('failed')), (write('\n'),nl). 
p12 :- (prec([every, language, speaks, a, hacker]); write('failed')), (write('\n'),nl). 
p13 :- (prec([a, hacker, every, language, speaks]); write('failed')), (write('\n'),nl). 
p14 :- (prec([every, language, speaks, a, language]); write('failed')), (write('\n'),nl). 
p15 :- (prec([a, language, every, language, speaks]); write('failed')), (write('\n'),nl). 
p16 :- (prec([a, hacker, speaks, every, hacker]); write('failed')), (write('\n'),nl). 
p17 :- (prec([every, hacker, a, hacker, speaks]); write('failed')), (write('\n'),nl). 
p18 :- (prec([a, hacker, speaks, every, language]); write('failed')), (write('\n'),nl). 
p19 :- (prec([every, language, a, hacker, speaks]); write('failed')), (write('\n'),nl). 
p20 :- (prec([a, hacker, speaks, a, hacker]); write('failed')), (write('\n'),nl). 
p21 :- (prec([a, hacker, a, hacker, speaks]); write('failed')), (write('\n'),nl). 
p22 :- (prec([a, hacker, speaks, a, language]); write('failed')), (write('\n'),nl). 
p23 :- (prec([a, language, a, hacker, speaks]); write('failed')), (write('\n'),nl). 
p24 :- (prec([a, language, speaks, every, hacker]); write('failed')), (write('\n'),nl). 
p25 :- (prec([every, hacker, a, language, speaks]); write('failed')), (write('\n'),nl). 
p26 :- (prec([a, language, speaks, every, language]); write('failed')), (write('\n'),nl). 
p27 :- (prec([every, language, a, language, speaks]); write('failed')), (write('\n'),nl). 
p28 :- (prec([a, language, speaks, a, hacker]); write('failed')), (write('\n'),nl). 
p29 :- (prec([a, hacker, a, language, speaks]); write('failed')), (write('\n'),nl). 
p30 :- (prec([a, language, speaks, a, language]); write('failed')), (write('\n'),nl). 
p31 :- (prec([a, language, a, language, speaks]); write('failed')), (write('\n'),nl). 

all_test :- tell('my_output_en.txt'),
p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,
told.

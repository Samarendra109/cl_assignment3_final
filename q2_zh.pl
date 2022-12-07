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
lan(zh).
question(q2).

bot sub [cat, sem, list, logic, gap_struct, agr].
    cat sub [gappable, agreeable, dou] intro [logic:logic, qstore:list].
        gappable sub [verbal, n, np, n_np_vp] intro [gap:gap_struct, sem:sem].
            verbal sub [vp, s, v] intro [subcat:list].

        agreeable sub [cl_agreeable, q_agreeable, n_np_vp] intro [agr:agr].
            cl_agreeable sub [cl, n] intro [agr:cl_agr].
            q_agreeable sub [np_vp, q] intro [agr:quant].

        n_np_vp sub [n, np_vp].
            np_vp sub [np, vp].

        n intro [cl:cl].

    agr sub [cl_agr, quant].
        cl_agr sub [ge, zhong].

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
% 每: the universal quantifier
mei ---> (q,
    logic: @lambda(F, 
                @lambda(P, 
                    @forall(Y, 
                        @apply(F, [Y]),
                        @apply(P, [Y])))),
    qstore:[],
    agr:forall).

% 一: the existential quantifier
yi ---> (q,
    logic: @lambda(F, 
                @lambda(P, 
                    @exists(Y, 
                        @apply(F, [Y]),
                        @apply(P, [Y])))),
    qstore:[],
    agr:exists).

% 个: the classifier for hackers
ge ---> (cl, agr:ge).
% 种: the classifier for languages
zhong ---> (cl, agr:zhong).

% 都: the distributive operator
dou ---> dou.

% 语言: language
yuyan ---> (n,
    agr:zhong,
    logic: @lambda(X, @apply(Language, [X])),
    qstore:[],
    sem:(language, Language)).

% 黑客: hacker
heike ---> (n,
    agr:ge,
    logic: @lambda(X, @apply(Hacker, [X])),
    qstore:[],
    sem:(hacker, Hacker)).

% 会说: speak
huishuo ---> (v,
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
    (np, sem:N_sem, logic:NP_logic, qstore:NP_qstore, agr:(quant, Q_agr), gap:none) ===>
    cat> (q, logic:Q_logic, agr:Q_agr),
    cat> (cl, agr:(cl_agr, CL_agr)),
    sem_head> (n, sem:N_sem, logic:N_logic, qstore:N_qstore, agr:CL_agr),
    goal> apply_normalize_and_qaction(
        Q_logic, N_logic, N_qstore, NP_logic, NP_qstore
    ).

vp rule
    (vp, sem:V_sem, logic: VP_logic, qstore: NP_qstore, agr:exists, gap:Gap, subcat: VP_subcat) ===>
    sem_head> (v, sem:V_sem, logic:V_logic, subcat: V_subcat),
    cat> (np, logic:NP_logic, qstore: NP_qstore, gap:Gap, NP),
    goal> check_gap_and_normalize(V_logic, V_subcat, NP, VP_logic, VP_subcat).

dou rule
    (vp, sem:VP_sem, logic: VP_logic, qstore: VP_qstore, agr:forall, subcat: VP_subcat) ===>
    cat> (dou),
    sem_head> (vp, sem:VP_sem, logic: VP_logic, qstore: VP_qstore, agr:exists, subcat: VP_subcat).

s rule
    (s, sem:VP_sem, logic: S_logic, qstore: S_qstore, gap:(none, None), subcat: []) ===>
    cat> (np, logic:NP_logic, qstore: e_list, agr:(quant, NP_agr), gap:None, sem:NP_subj_sem, NP),
    sem_head> (vp, sem:VP_sem, logic:VP_logic, qstore: VP_qstore, agr:NP_agr, gap:None, subcat:[(np, sem:NP_subj_sem)]),
    goal> apply_normalize_and_retrieve(NP, NP_logic, VP_logic, VP_qstore, S_logic, S_qstore).

s_gap rule
    (s, sem:VP_sem, logic: S_logic, qstore: S_qstore, gap:(none, None), subcat:[]) ===>
    cat> (np, logic:NP_Obj_logic, qstore: NP_Obj_qstore, gap:None, sem:NP_obj_sem, NP_Obj),
    cat> (np, logic:NP_Sub_logic, qstore: e_list, agr:(forall, Forall), gap:None, sem:NP_subj_sem, NP),
    sem_head> (vp, sem:VP_sem, logic:VP_logic, qstore: VP_qstore, agr:Forall, gap:Gap, 
                subcat:[(np, sem:NP_obj_sem), (np, sem:NP_subj_sem)], VP),
    goal> resolve_gap_and_normalize(NP, NP_Sub_logic, VP, NP_Obj, S_logic, S_qstore).

% The empty category
empty (np, sem:Sem, logic:Logic, qstore:QStore, agr:Agr,
    gap:(sem:Sem, logic:Logic, qstore:QStore, agr:Agr, gap:none)).

% Macros
lambda(X, Body) macro (lambda, bind:X, body:Body).
forall(X, Restr, Body) macro (forall, bind:X, body:(imply, lhs:Restr, rhs:Body)).
exists(X, Restr, Body) macro (exists, bind:X, body:(and, lhs:Restr, rhs:Body)).
apply(F, Args) macro (app, f:F, args:Args).

% extra helper goals
apply_normalize_and_qaction(LogicFunc, LogicArg, QStore, NewLogic, NewQStore) if
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic),
    qaction(Norm_logic, QStore, NewLogic, NewQStore).

is_ambiguous((np, agr:NP1_agr), [(l:body:NP2_agr)]) if
    bn_quant(NP1_agr, forall),
    bn_quant(NP2_agr, exists).

apply_normalize_and_retrieve(NP1, LogicFunc, LogicArg, QStore, NewLogic, NewQStore) if
    is_not_empty(QStore),
    is_ambiguous(NP1, QStore),
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic),
    retrieve(QStore, Norm_logic, NewQStore, NewLogic).

apply_normalize_and_retrieve(NP1, LogicFunc, LogicArg, QStore, Norm_logic, QStore) if
    is_empty(QStore),
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic).

is_not_gap(none) if true.
is_gap(np) if true.

check_gap_and_normalize(
    V_logic, [(np, sem:NP_obj_sem), NP_subj], (np, logic: NP_logic, gap:Gap, sem:NP_obj_sem), VP_logic, [NP_subj]
    ) if
    is_not_gap(Gap),
    beta_normalize(@apply(V_logic, [NP_logic]), VP_logic).

check_gap_and_normalize(V_logic, V_subcat, (np, logic: NP_logic, gap:Gap), V_logic, V_subcat) if
    is_gap(Gap).

is_not_empty([_|_]) if true.

resolve_gap_and_normalize(
        NP,
        NP_Sub_logic, 
        (vp, logic: VP_logic, gap:Gap), 
        (np, logic:NP_Obj_logic, qstore: NP_Obj_qstore, NP_obj), 
        Norm_logic, NP_Obj_qstore
    ) if
    is_gap(Gap),
    beta_normalize(@apply(VP_logic, [NP_Obj_logic]), VP_Obj_logic),
    beta_normalize(@apply(NP_Sub_logic, [VP_Obj_logic]), Norm_logic),
    is_empty(NP_Obj_qstore).

% The below two can work instead, but for simplicity of testing I am omitting these.
% resolve_gap_and_normalize(
%         NP,
%         NP_Sub_logic, 
%         (vp, logic: VP_logic, gap:Gap), 
%         (np, logic:NP_Obj_logic, qstore: NP_Obj_qstore, NP_obj), 
%         S_logic, S_qstore
%     ) if
%     is_gap(Gap),
%     beta_normalize(@apply(VP_logic, [NP_Obj_logic]), VP_Obj_logic),
%     beta_normalize(@apply(NP_Sub_logic, [VP_Obj_logic]), Norm_logic),
%     is_not_empty(NP_Obj_qstore),
%     retrieve(NP_Obj_qstore, Norm_logic, S_qstore, S_logic).

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
prect_test :- prec([yi,ge,heike,huishuo,mei,zhong,yuyan]).
translate_test :- translate([yi,ge,heike,huishuo,mei,zhong,yuyan]).
gen1_test :- gen((s, sem:speak, logic: @forall(X, @apply(language, [X]), @exists(Y, @apply(hacker, [Y]), @apply(speak, [Y|[X]]))))).
gen2_test :- gen((s, sem:speak, logic: @forall(X, @apply(hacker, [X]), @exists(Y, @apply(language, [Y]), @apply(speak, [X|[Y]]))))).

p0 :- (prec([mei, ge, heike, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p1 :- (prec([mei, ge, heike, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p2 :- (prec([mei, ge, heike, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p3 :- (prec([mei, ge, yuyan, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p4 :- (prec([mei, ge, heike, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p5 :- (prec([mei, zhong, heike, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p6 :- (prec([mei, ge, heike, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p7 :- (prec([mei, zhong, yuyan, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p8 :- (prec([mei, ge, heike, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p9 :- (prec([yi, ge, heike, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p10 :- (prec([mei, ge, heike, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p11 :- (prec([yi, ge, yuyan, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p12 :- (prec([mei, ge, heike, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p13 :- (prec([yi, zhong, heike, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p14 :- (prec([mei, ge, heike, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p15 :- (prec([yi, zhong, yuyan, mei, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p16 :- (prec([mei, ge, heike, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p17 :- (prec([mei, ge, heike, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p18 :- (prec([mei, ge, heike, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p19 :- (prec([mei, ge, yuyan, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p20 :- (prec([mei, ge, heike, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p21 :- (prec([mei, zhong, heike, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p22 :- (prec([mei, ge, heike, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p23 :- (prec([mei, zhong, yuyan, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p24 :- (prec([mei, ge, heike, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p25 :- (prec([yi, ge, heike, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p26 :- (prec([mei, ge, heike, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p27 :- (prec([yi, ge, yuyan, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p28 :- (prec([mei, ge, heike, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p29 :- (prec([yi, zhong, heike, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p30 :- (prec([mei, ge, heike, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p31 :- (prec([yi, zhong, yuyan, mei, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p32 :- (prec([mei, ge, yuyan, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p33 :- (prec([mei, ge, heike, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p34 :- (prec([mei, ge, yuyan, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p35 :- (prec([mei, ge, yuyan, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p36 :- (prec([mei, ge, yuyan, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p37 :- (prec([mei, zhong, heike, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p38 :- (prec([mei, ge, yuyan, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p39 :- (prec([mei, zhong, yuyan, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p40 :- (prec([mei, ge, yuyan, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p41 :- (prec([yi, ge, heike, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p42 :- (prec([mei, ge, yuyan, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p43 :- (prec([yi, ge, yuyan, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p44 :- (prec([mei, ge, yuyan, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p45 :- (prec([yi, zhong, heike, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p46 :- (prec([mei, ge, yuyan, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p47 :- (prec([yi, zhong, yuyan, mei, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p48 :- (prec([mei, ge, yuyan, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p49 :- (prec([mei, ge, heike, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p50 :- (prec([mei, ge, yuyan, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p51 :- (prec([mei, ge, yuyan, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p52 :- (prec([mei, ge, yuyan, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p53 :- (prec([mei, zhong, heike, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p54 :- (prec([mei, ge, yuyan, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p55 :- (prec([mei, zhong, yuyan, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p56 :- (prec([mei, ge, yuyan, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p57 :- (prec([yi, ge, heike, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p58 :- (prec([mei, ge, yuyan, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p59 :- (prec([yi, ge, yuyan, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p60 :- (prec([mei, ge, yuyan, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p61 :- (prec([yi, zhong, heike, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p62 :- (prec([mei, ge, yuyan, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p63 :- (prec([yi, zhong, yuyan, mei, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p64 :- (prec([mei, zhong, heike, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p65 :- (prec([mei, ge, heike, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p66 :- (prec([mei, zhong, heike, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p67 :- (prec([mei, ge, yuyan, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p68 :- (prec([mei, zhong, heike, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p69 :- (prec([mei, zhong, heike, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p70 :- (prec([mei, zhong, heike, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p71 :- (prec([mei, zhong, yuyan, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p72 :- (prec([mei, zhong, heike, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p73 :- (prec([yi, ge, heike, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p74 :- (prec([mei, zhong, heike, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p75 :- (prec([yi, ge, yuyan, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p76 :- (prec([mei, zhong, heike, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p77 :- (prec([yi, zhong, heike, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p78 :- (prec([mei, zhong, heike, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p79 :- (prec([yi, zhong, yuyan, mei, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p80 :- (prec([mei, zhong, heike, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p81 :- (prec([mei, ge, heike, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p82 :- (prec([mei, zhong, heike, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p83 :- (prec([mei, ge, yuyan, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p84 :- (prec([mei, zhong, heike, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p85 :- (prec([mei, zhong, heike, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p86 :- (prec([mei, zhong, heike, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p87 :- (prec([mei, zhong, yuyan, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p88 :- (prec([mei, zhong, heike, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p89 :- (prec([yi, ge, heike, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p90 :- (prec([mei, zhong, heike, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p91 :- (prec([yi, ge, yuyan, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p92 :- (prec([mei, zhong, heike, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p93 :- (prec([yi, zhong, heike, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p94 :- (prec([mei, zhong, heike, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p95 :- (prec([yi, zhong, yuyan, mei, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p96 :- (prec([mei, zhong, yuyan, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p97 :- (prec([mei, ge, heike, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p98 :- (prec([mei, zhong, yuyan, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p99 :- (prec([mei, ge, yuyan, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p100 :- (prec([mei, zhong, yuyan, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p101 :- (prec([mei, zhong, heike, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p102 :- (prec([mei, zhong, yuyan, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p103 :- (prec([mei, zhong, yuyan, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p104 :- (prec([mei, zhong, yuyan, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p105 :- (prec([yi, ge, heike, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p106 :- (prec([mei, zhong, yuyan, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p107 :- (prec([yi, ge, yuyan, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p108 :- (prec([mei, zhong, yuyan, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p109 :- (prec([yi, zhong, heike, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p110 :- (prec([mei, zhong, yuyan, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p111 :- (prec([yi, zhong, yuyan, mei, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p112 :- (prec([mei, zhong, yuyan, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p113 :- (prec([mei, ge, heike, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p114 :- (prec([mei, zhong, yuyan, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p115 :- (prec([mei, ge, yuyan, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p116 :- (prec([mei, zhong, yuyan, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p117 :- (prec([mei, zhong, heike, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p118 :- (prec([mei, zhong, yuyan, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p119 :- (prec([mei, zhong, yuyan, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p120 :- (prec([mei, zhong, yuyan, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p121 :- (prec([yi, ge, heike, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p122 :- (prec([mei, zhong, yuyan, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p123 :- (prec([yi, ge, yuyan, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p124 :- (prec([mei, zhong, yuyan, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p125 :- (prec([yi, zhong, heike, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p126 :- (prec([mei, zhong, yuyan, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p127 :- (prec([yi, zhong, yuyan, mei, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p128 :- (prec([yi, ge, heike, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p129 :- (prec([mei, ge, heike, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p130 :- (prec([yi, ge, heike, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p131 :- (prec([mei, ge, yuyan, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p132 :- (prec([yi, ge, heike, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p133 :- (prec([mei, zhong, heike, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p134 :- (prec([yi, ge, heike, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p135 :- (prec([mei, zhong, yuyan, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p136 :- (prec([yi, ge, heike, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p137 :- (prec([yi, ge, heike, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p138 :- (prec([yi, ge, heike, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p139 :- (prec([yi, ge, yuyan, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p140 :- (prec([yi, ge, heike, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p141 :- (prec([yi, zhong, heike, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p142 :- (prec([yi, ge, heike, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p143 :- (prec([yi, zhong, yuyan, yi, ge, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p144 :- (prec([yi, ge, heike, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p145 :- (prec([mei, ge, heike, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p146 :- (prec([yi, ge, heike, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p147 :- (prec([mei, ge, yuyan, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p148 :- (prec([yi, ge, heike, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p149 :- (prec([mei, zhong, heike, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p150 :- (prec([yi, ge, heike, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p151 :- (prec([mei, zhong, yuyan, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p152 :- (prec([yi, ge, heike, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p153 :- (prec([yi, ge, heike, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p154 :- (prec([yi, ge, heike, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p155 :- (prec([yi, ge, yuyan, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p156 :- (prec([yi, ge, heike, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p157 :- (prec([yi, zhong, heike, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p158 :- (prec([yi, ge, heike, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p159 :- (prec([yi, zhong, yuyan, yi, ge, heike, huishuo]); write('failed')), (write('\n'),nl). 
p160 :- (prec([yi, ge, yuyan, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p161 :- (prec([mei, ge, heike, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p162 :- (prec([yi, ge, yuyan, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p163 :- (prec([mei, ge, yuyan, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p164 :- (prec([yi, ge, yuyan, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p165 :- (prec([mei, zhong, heike, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p166 :- (prec([yi, ge, yuyan, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p167 :- (prec([mei, zhong, yuyan, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p168 :- (prec([yi, ge, yuyan, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p169 :- (prec([yi, ge, heike, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p170 :- (prec([yi, ge, yuyan, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p171 :- (prec([yi, ge, yuyan, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p172 :- (prec([yi, ge, yuyan, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p173 :- (prec([yi, zhong, heike, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p174 :- (prec([yi, ge, yuyan, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p175 :- (prec([yi, zhong, yuyan, yi, ge, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p176 :- (prec([yi, ge, yuyan, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p177 :- (prec([mei, ge, heike, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p178 :- (prec([yi, ge, yuyan, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p179 :- (prec([mei, ge, yuyan, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p180 :- (prec([yi, ge, yuyan, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p181 :- (prec([mei, zhong, heike, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p182 :- (prec([yi, ge, yuyan, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p183 :- (prec([mei, zhong, yuyan, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p184 :- (prec([yi, ge, yuyan, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p185 :- (prec([yi, ge, heike, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p186 :- (prec([yi, ge, yuyan, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p187 :- (prec([yi, ge, yuyan, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p188 :- (prec([yi, ge, yuyan, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p189 :- (prec([yi, zhong, heike, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p190 :- (prec([yi, ge, yuyan, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p191 :- (prec([yi, zhong, yuyan, yi, ge, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p192 :- (prec([yi, zhong, heike, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p193 :- (prec([mei, ge, heike, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p194 :- (prec([yi, zhong, heike, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p195 :- (prec([mei, ge, yuyan, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p196 :- (prec([yi, zhong, heike, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p197 :- (prec([mei, zhong, heike, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p198 :- (prec([yi, zhong, heike, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p199 :- (prec([mei, zhong, yuyan, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p200 :- (prec([yi, zhong, heike, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p201 :- (prec([yi, ge, heike, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p202 :- (prec([yi, zhong, heike, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p203 :- (prec([yi, ge, yuyan, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p204 :- (prec([yi, zhong, heike, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p205 :- (prec([yi, zhong, heike, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p206 :- (prec([yi, zhong, heike, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p207 :- (prec([yi, zhong, yuyan, yi, zhong, heike, dou, huishuo]); write('failed')), (write('\n'),nl). 
p208 :- (prec([yi, zhong, heike, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p209 :- (prec([mei, ge, heike, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p210 :- (prec([yi, zhong, heike, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p211 :- (prec([mei, ge, yuyan, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p212 :- (prec([yi, zhong, heike, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p213 :- (prec([mei, zhong, heike, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p214 :- (prec([yi, zhong, heike, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p215 :- (prec([mei, zhong, yuyan, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p216 :- (prec([yi, zhong, heike, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p217 :- (prec([yi, ge, heike, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p218 :- (prec([yi, zhong, heike, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p219 :- (prec([yi, ge, yuyan, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p220 :- (prec([yi, zhong, heike, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p221 :- (prec([yi, zhong, heike, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p222 :- (prec([yi, zhong, heike, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p223 :- (prec([yi, zhong, yuyan, yi, zhong, heike, huishuo]); write('failed')), (write('\n'),nl). 
p224 :- (prec([yi, zhong, yuyan, dou, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p225 :- (prec([mei, ge, heike, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p226 :- (prec([yi, zhong, yuyan, dou, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p227 :- (prec([mei, ge, yuyan, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p228 :- (prec([yi, zhong, yuyan, dou, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p229 :- (prec([mei, zhong, heike, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p230 :- (prec([yi, zhong, yuyan, dou, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p231 :- (prec([mei, zhong, yuyan, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p232 :- (prec([yi, zhong, yuyan, dou, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p233 :- (prec([yi, ge, heike, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p234 :- (prec([yi, zhong, yuyan, dou, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p235 :- (prec([yi, ge, yuyan, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p236 :- (prec([yi, zhong, yuyan, dou, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p237 :- (prec([yi, zhong, heike, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p238 :- (prec([yi, zhong, yuyan, dou, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p239 :- (prec([yi, zhong, yuyan, yi, zhong, yuyan, dou, huishuo]); write('failed')), (write('\n'),nl). 
p240 :- (prec([yi, zhong, yuyan, huishuo, mei, ge, heike]); write('failed')), (write('\n'),nl). 
p241 :- (prec([mei, ge, heike, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p242 :- (prec([yi, zhong, yuyan, huishuo, mei, ge, yuyan]); write('failed')), (write('\n'),nl). 
p243 :- (prec([mei, ge, yuyan, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p244 :- (prec([yi, zhong, yuyan, huishuo, mei, zhong, heike]); write('failed')), (write('\n'),nl). 
p245 :- (prec([mei, zhong, heike, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p246 :- (prec([yi, zhong, yuyan, huishuo, mei, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p247 :- (prec([mei, zhong, yuyan, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p248 :- (prec([yi, zhong, yuyan, huishuo, yi, ge, heike]); write('failed')), (write('\n'),nl). 
p249 :- (prec([yi, ge, heike, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p250 :- (prec([yi, zhong, yuyan, huishuo, yi, ge, yuyan]); write('failed')), (write('\n'),nl). 
p251 :- (prec([yi, ge, yuyan, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p252 :- (prec([yi, zhong, yuyan, huishuo, yi, zhong, heike]); write('failed')), (write('\n'),nl). 
p253 :- (prec([yi, zhong, heike, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 
p254 :- (prec([yi, zhong, yuyan, huishuo, yi, zhong, yuyan]); write('failed')), (write('\n'),nl). 
p255 :- (prec([yi, zhong, yuyan, yi, zhong, yuyan, huishuo]); write('failed')), (write('\n'),nl). 

all_test :- tell('my_output_zh.txt'),
p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115,p116,p117,p118,p119,p120,p121,p122,p123,p124,p125,p126,p127,p128,p129,p130,p131,p132,p133,p134,p135,p136,p137,p138,p139,p140,p141,p142,p143,p144,p145,p146,p147,p148,p149,p150,p151,p152,p153,p154,p155,p156,p157,p158,p159,p160,p161,p162,p163,p164,p165,p166,p167,p168,p169,p170,p171,p172,p173,p174,p175,p176,p177,p178,p179,p180,p181,p182,p183,p184,p185,p186,p187,p188,p189,p190,p191,p192,p193,p194,p195,p196,p197,p198,p199,p200,p201,p202,p203,p204,p205,p206,p207,p208,p209,p210,p211,p212,p213,p214,p215,p216,p217,p218,p219,p220,p221,p222,p223,p224,p225,p226,p227,p228,p229,p230,p231,p232,p233,p234,p235,p236,p237,p238,p239,p240,p241,p242,p243,p244,p245,p246,p247,p248,p249,p250,p251,p252,p253,p254,p255,
told.

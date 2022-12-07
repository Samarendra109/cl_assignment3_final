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

:- ale_flag(pscompiling, _, parse_and_gen).
:- ensure_loaded(csc485).
lan(en).
question(q1).

bot sub [cat, sem, agr, list].
    sem sub [n_sem, v_sem].
        n_sem sub [mouse, sheep, linguist] intro [count:count].
        v_sem sub [see, chase] intro [subj:sem, obj:sem].

    cat sub [nominal, verbal] intro [agr:agr, sem:sem].
        nominal sub [n, np, det, num] intro [sem:n_sem].
        verbal sub [v, vp, s] intro [sem:v_sem, subcat:list].

    % Define your agreement
    agr intro [person:pers, noun_count:noun_c].

    pers sub [first,second,third].
    noun_c sub [singular,plural].

    count sub [one, two, three].

    list sub [e_list, ne_list].
        ne_list intro [hd:bot, tl:list].

% Specifying the semantics for generation.
semantics sem1.
sem1(sem:S, S) if true.

% Define your Lexical entries
a ---> (det, agr:noun_count:singular, sem:count:one).
one ---> (num, agr:noun_count:singular, sem:count:one).
two ---> (num, agr:noun_count:plural, sem:count:two).
three ---> (num, agr:noun_count:plural, sem:count:three).
mouse ---> (n, agr:(person:third, noun_count:singular), sem:mouse).
mice ---> (n, agr:(person:third, noun_count:plural), sem:mouse).
sheep ---> (n, agr:(person:third, noun_count:singular), sem:sheep).
sheep ---> (n, agr:(person:third, noun_count:plural), sem:sheep).
linguist ---> (n, agr:(person:third, noun_count:singular), sem:linguist).
linguists ---> (n, agr:(person:third, noun_count:plural), sem:linguist).
%see ---> (v, sem:see, agr:person:first).  %Won't need the first person
%see ---> (v, sem:see, agr:person:second). %Won't need the second person
see ---> (v, sem:see, agr:(person:third, noun_count:plural)).
sees ---> (v, sem:see, agr:(person:third, noun_count:singular)).
saw ---> (v, sem:see, agr:(person:third, noun_count:plural)).
saw ---> (v, sem:see, agr:(person:third, noun_count:singular)).
%chase ---> (v, sem:chase, agr:person:first). % Won't need the first person
%chase ---> (v, sem:chase, agr:person:second). % Won't need the second person
chase ---> (v, sem:chase, agr:(person:third, noun_count:plural)).
chases ---> (v, sem:chase, agr:(person:third, noun_count:singular)).
chased ---> (v, sem:chase, agr:(person:third, noun_count:plural)).
chased ---> (v, sem:chase, agr:(person:third, noun_count:singular)).

% Define your Rules
snpvp rule
(s, sem:(V_sem, subj:N_sem, obj:N_sem_o)) 
    ===> cat> (np, sem:N_sem, agr:Agr),
         sem_head> (vp, sem:(V_sem, obj:N_sem_o), agr:Agr).

vpvnp rule
(vp, agr:Agr, sem:(V_sem, obj:N_sem)) 
    ===> sem_head> (v, agr:Agr, sem:V_sem),
         cat> (np, sem:N_sem).

npdetn rule
(np, agr:(person:Person, noun_count:Noun_c), sem:(N_sem, count:Count))
    ===> cat> (det, agr:noun_count:Noun_c, sem:count:Count),
         sem_head> (n, agr:(person:Person, noun_count:Noun_c), sem:N_sem).

npnumn rule
(np, agr:(person:Person, noun_count:Noun_c), sem:(N_sem, count:Count)) 
    ===> cat> (num, agr:noun_count:Noun_c, sem:count:Count),
         sem_head> (n, agr:(person:Person, noun_count:Noun_c), sem:N_sem).
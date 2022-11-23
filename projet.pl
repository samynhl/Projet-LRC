/* on met les cut?*/

genere(Nom) :- compteur(V),nombre(V,L1),
    append([105,110,115,116],L1,L2),
    V1 is V+1,
    dynamic(compteur/1),
    retract(compteur(V)),
    dynamic(compteur/1),
    assert(compteur(V1)),nl,nl,nl,
    name(Nom,L2).
nombre(0,[]).
nombre(X,L1) :-
    R is (X mod 10),
    Q is ((X-R)//10),
    chiffre_car(R,R1),
    char_code(R1,R2),
    nombre(Q,L),
    append(L,[R2],L1).
chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').

compteur(1).

definition(X, X, _) :- 
    cnamea(X).
definition(X, D, [(X, D)|_]).
definition(X, Y, [(C, _)|L]) :-    
    X \= C, 
    definition(X, Y, L).

pas_autoref(_, E, _) :-
    cnamea(E).
pas_autoref(C, E, Tbox) :-
    cnamena(E),
    definition(E, D, Tbox),
    pas_autoref(C, D, Tbox).
pas_autoref(C, not(C1), Tbox) :-
    C \= C1,
    pas_autoref(C, C1, Tbox).
pas_autoref(C, and(C1, C2), Tbox) :-
    C \= C1, 
    C \= C2,
    pas_autoref(C, C1, Tbox),
    pas_autoref(C, C2, Tbox).
pas_autoref(C, or(C1, C2), Tbox) :-
    C \= C1, 
    C \= C2,
    pas_autoref(C, C1, Tbox),
    pas_autoref(C, C2, Tbox).
pas_autoref(C, some(_, C1), Tbox) :-
    C \= C1,
    pas_autoref(C, C1, Tbox).
pas_autoref(C, all(_, C1), Tbox) :-
    C \= C1,
    pas_autoref(C, C1, Tbox).

concept(C) :- cnamea(C).
concept(C) :- cnamena(C).
concept(not(C)) :- concept(C).
concept(and(C1,C2)) :- concept(C1), concept(C2).
concept(or(C1,C2)) :- concept(C1), concept(C2).
concept(some(R,C)) :- rname(R), concept(C).
concept(all(R,C)) :- rname(R), concept(C).

expr_atomique(E, E, _) :-
    cnamea(E).
expr_atomique(E, EA, Tbox) :-
    cnamena(E),
    definition(E, D, Tbox),
    expr_atomique(D, EA, Tbox).
expr_atomique(not(E), not(EA), Tbox) :-
    expr_atomique(E, EA, Tbox).
expr_atomique(and(E1, E2), and(EA1, EA2), Tbox) :-
    expr_atomique(E1, EA1, Tbox),
    expr_atomique(E2, EA2, Tbox).
expr_atomique(or(E1, E2), or(EA1, EA2), Tbox) :-
    expr_atomique(E1, EA1, Tbox),
    expr_atomique(E2, EA2, Tbox).
expr_atomique(some(R, E), some(R, EA), Tbox) :-
    expr_atomique(E, EA, Tbox).
expr_atomique(all(R, E), all(R, EA), Tbox) :-
    expr_atomique(E, EA, Tbox).

nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)):- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),X):-!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

traitement_expr(E, E1, Tbox):-
    expr_atomique(E, EA, Tbox),
    nnf(EA, E1).

traitement_Tbox([], [], _).
traitement_Tbox([(C, E)|L], [(C, E1)|L1], Tbox) :-
    cnamena(C),
    concept(E), 
    pas_autoref(C, E, Tbox),
    traitement_expr(E, E1, Tbox),
    traitement_Tbox(L, L1, Tbox).

traitement_Abi([], [], _).
traitement_Abi([(I, C)|L], [(I, C1)|L1], Tbox) :-
    iname(I),
    concept(C),
    traitement_expr(C, C1, Tbox),
    traitement_Abi(L, L1, Tbox).

traitement_Abr([], [], _).
traitement_Abr([(I1, I2, R)|L], [(I1, I2, R)|L1], Tbox) :-
    iname(I1),
    iname(I2),
    rname(R),
    traitement_Abr(L, L1, Tbox).

traitement_Abox(Abi, Abi1, Abr, Abr1, Tbox) :-
    traitement_Abi(Abi, Abi1, Tbox),
    traitement_Abr(Abr, Abr1, Tbox).

/*pas sure, il devrait pas y avoir plus d arg, on retourne les listes traités nan?*/
/*pk y a un warning*/
premiere_etape(Tbox, Abi, Abr) :- 
    traitement_Tbox(Tbox, Tbox1, Tbox),
    traitement_Abox(Abi, Abi1, Abr, Abr2, Tbox).

/*comment indiquer a l utilisateur que le concept entré est pas correct?*/
/*concat marche pas j ai utiliser append*/
acquisition_prop_type1(Abi, Abi1, Tbox) :- 
    nl, write('Instance I='),
    nl, read(I),
    nl, write('Concept c='),
    nl, read(C),
    concept(C), 
    traitement_expr(not(C), C1, Tbox),
    append(Abi, [(I, C1)], Abi1).

/*comment indiquer a l utilisateur que le concept entré est pas correct?*/
acquisition_prop_type2(Abi, Abi1, Tbox) :-
    nl, write('Premier concept C1='),
    nl, read(C1),
    nl, write('Deuxieme concept C2='),
    nl, read(C2),
    concept(C1), 
    concept(C2), 
    expr_atomique(and(C1,C2), C, Tbox),
    genere(I),
    append(Abi, [(I, C)], Abi1).

suite(1,Abi,Abi1,Tbox) :-
    acquisition_prop_type1(Abi,Abi1,Tbox),!.

suite(2,Abi,Abi1,Tbox) :-
    acquisition_prop_type2(Abi,Abi1,Tbox),!.

suite(_,Abi,Abi1,Tbox) :-
    nl, write('Cette reponse est incorrecte.'),
    nl,
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
    nl, write('Entrez le numero du type de proposition que vous voulez demontrer :'),
    nl, write('1 Une instance donnee appartient a un concept donne.'),
    nl, write('2 Deux concepts n\'ont pas d\'elements en commun (ils ont une intersection vide).'),
    nl, read(R), 
    suite(R, Abi, Abi1, Tbox).

deuxieme_etape(Abi, Abi1, Tbox) :-
    saisie_et_traitement_prop_a_demontrer(Abi, Abi1, Tbox).


evolue((I, some(R,C)), Lie, _, _, _, _, Lie1, _, _, _, _) :-
    append(Lie, [(I, some(R,C))], Lie1).
evolue((I, all(R,C)), _, Lpt, _, _, _, _, Lpt1, _, _, _) :-
    append(Lpt, [(I, all(R,C))], Lpt1).
evolue((I, and(C1,C2)), _, _, Li, _, _, _, _, Li1, _, _) :-
    append(Li, [(I, and(C1,C2))], Li1).
evolue((I, or(C1,C2)), _, _, _, Lu, _, _, _, _, Lu1, _) :-
    append(Lu, [(I, or(C1,C2))], Lu1).
evolue((I, not(C)), _, _, _, _, Ls, _, _, _, _, Ls1) :-
    append(Ls, [(I, not(C))], Ls1).
evolue((I, C), _, _, _, _, Ls, _, _, _, _, Ls1) :-
    append(Ls, [(I, C)], Ls1).

/*A TESTER*/
tri_Abox([], _, _, _, _, _).
tri_Abox([A, L], Lie, Lpt, Li, Lu, Ls) :-
    evolue(A, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    tri_Abox(L, Lie1, Lpt1, Li1, Lu1, Ls1).

/*affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2)*/

/*renvoie 1 si y a un clash et 0 si y en a pas*/
clash([(I, C)|L], 1) :-
    member((I, not(C)), L).
clash([(I, C)|L], 0) :-
    not(member((I, not(C)), L)).

suite_clash(1, _, _, _, _, _, _).
suite_clash(0, Lie, Lpt, Li, Lu, Ls, Abr) :-
    resolution(Lie, Lpt, Li, Lu, Ls, Abr).

test_clash(Lie, Lpt, Li, Lu, Ls, Abr) :-
    clash(Ls, Cl),
    suite_clash(Cl, Lie, Lpt, Li, Lu, Ls, Abr).

complete_some([], Lpt, Li, Lu, Ls, Abr) :-
    transformation_and([], Lpt, Li, Lu, Ls, Abr).
complete_some([(A, some(R, C))|L], Lpt, Li, Lu, Ls, Abr) :-
    genere(B),
    append(Abr, [(A, B, R)], Abr2), 
    append(Ls, [(B, C)], Ls2),
    test_clash(L, Lpt, Li, Lu, Ls2, Abr2).

transformation_and(Lie, Lpt, [], Lu, Ls, Abr) :-
    deduction_all(Lie, Lpt, [], Lu, Ls, Abr).
/*attention si (a,c1) appartient deja a l'arbre (enlever avant)*/
transformation_and(Lie, Lpt, [(A, and(C1, C2))|L], Lu, Ls, Abr) :-
    append(Ls, [(A, C1)], Ls2), 
    append(Ls2, [(A, C2)], Ls3),
    test_clash(Lie, Lpt, L, Lu, Ls3, Abr).

/*L est la liste des instances reliés a I par la relation R*/
instances_relies(_, _, [], []).
instances_relies(A, R, [B|L], Abr) :-
    member((A, B, R), Abr),
    enleve((A,B, R), Abr, Abr1),
    instances_relies(A, R, L, Abr1).

/*ajoute a Ls les couples (B, C) tel que B appartienne a Lb*/
ajout_assertion([], _, _, _).
/*et si (B, C) appartenait deja a Ls?*/
ajout_assertion([B|L], C, Ls, Ls1) :-
    append(Ls, [(B, C)], Ls2), 
    ajout_assertion(L, C, Ls2, Ls1).

deduction_all(Lie, [], Li, Lu, Ls, Abr) :-
    transformation_or(Lie, [], Li, Lu, Ls, Abr).
deduction_all(Lie, [(A, all(R,C))|L], Li, Lu, Ls, Abr) :-
    instances_relies(A, R, Lb, Abr),
    ajout_assertion(Lb, C, Ls, Ls1),
    test_clash(Lie, L, Li, Lu, Ls1, Abr).
/*c est sur on enleve l assertion pour tout ? oui car on fait toutes les deductions d un cout et qu on peut pas rajouter de relation car on a traiter tous les il existe*/

/*comment coder l echec si la liste est vide? le programme va repondre false ds le terminal je pense*/
/*attention si (a,c1) appartient deja a l'arbre (enlever avant)*/
transformation_or(Lie, Lpt, Li, [(A, or(C1,C2))|L], Ls, Abr) :-
    append(Ls, [(A, C1)], Ls2), 
    append(Ls, [(A, C2)], Ls3),
    test_clash(Lie, Lpt, Li, L, Ls2, Abr),
    test_clash(Lie, Lpt, Li, L, Ls3, Abr).

resolution(Lie, Lpt, Li, Lu, Ls, Abr) :-
    complete_some(Lie, Lpt, Li, Lu, Ls, Abr).


/*affichee_evolution_Abox*/


troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').

programme :-
    premiere_etape(Tbox,Abi,Abr),
    deuxieme_etape(Abi,Abi1,Tbox),
    troisieme_etape(Abi1,Abr).
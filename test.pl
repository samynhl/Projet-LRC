%                                                 PROJET
%                                              LRC - M1 DAC
%                                     NEHLIL Samy - BOUTALEB Allaa

% ##########################################################################################

% MAIN

% ##########################################################################################

programme :-
    nl, write('M1 DAC - PROJET LRC - Samy NEHLIL et Allaa BOUTALEB'), nl,

    nl, write('--------------------------------------- Premiere partie ---------------------------------------'), nl,
    premiere_etape(TBox, Abi, Abr),

    nl, write('--------------------------------------- Deuxieme partie ---------------------------------------'), nl,
    deuxieme_etape(Abi, Abi1, Tbox),

    nl, write('--------------------------------------- Troisieme partie ---------------------------------------'), nl,
    troisieme_etape(Abi1, Abr).

% ##########################################################################################

% PARTIE 1

% ##########################################################################################

% Cette methode permet de creer des listes qui vont contenir la TBox, la ABox d instances et la ABox de rôles.
% Ces listes evolueront au fur et à mesure qu on soumettra des propositions à la démonstration.
premiere_etape(Tbox, Abi, Abr) :-
    setof((X, Y), equiv(X, Y), Tbox),
    nl, write('Tbox = '), write(Tbox), nl,

    setof((X, Y), inst(X, Y), Abi),
    nl, write('Abi = '), write(Abi), nl,

    setof((X, Y, Z), instR(X, Y, Z), Abr),
    nl, write('Abr = '), write(Abr), nl.

% ##########################################################################################

% PARTIE 2

% ##########################################################################################

% Méthode de la deuxième étape
deuxieme_etape(Abi,Abi1,Tbox) :-
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

% ------------------------------------------------------------------------------------------

% Mise en place du code donnée dans lénoncé
saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
    nl,write('Entrer le numero du type de proposition que l"on souhaite demontrer :'),
    nl,write('\tType 1 - Une instance donnee appartient a un concept donne.'),
    nl,write('\tType 2 - Deux concepts n-elements en commun dont l"intersection est vide (negation).'),
    nl,read(R),
    suite(R,Abi,Abi1,Tbox), !.

% ------------------------------------------------------------------------------------------

suite(1,Abi,Abi1,Tbox) :-
    acquisition_prop_type1(Abi,Abi1,Tbox), !.

% ------------------------------------------------------------------------------------------

suite(2,Abi,Abi1,Tbox) :-
    acquisition_prop_type2(Abi,Abi1,Tbox), !.

% ------------------------------------------------------------------------------------------

suite(R,Abi,Abi1,Tbox) :-
    nl, write('Cette option n"existe pas.'),
    nl, saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

% ------------------------------------------------------------------------------------------
% On met en place les methodes utilisées plus haut
% ------------------------------------------------------------------------------------------
lect([]).
lect([X|L]):- read(X), X \= fin, !, lect(L).

/*concat/3 : concatene les deux listes L1 et L2 dans L3.*/
concatene([],L1,L1).
concatene([X|Y],L1,[X|L2]) :- concatene(Y,L1,L2).

% Méthode permettant l acquisition de propositions du type 1 (I : C)
acquisition_prop_type1(Abi,Abi1,Tbox) :-
    % On entre le type de l instance
    nl, write('Veuillez entrer l"instance :'),
    nl, read(I),

    % On réalise une vérification sur l instance
    verificationInstance(I),

    % On entre le concept
    nl, write('Veuillez entrer le concept :'),
    nl, read(C),

    % On effectue une vérification sur le concept
    % verificationConcept(C)

    % On effectue les manipulations sur le concept
    % On le remplace (RC) puis on effectue sa négation (NRC)
    traitement_Abox([I,C],Ctraitennf),

    nl, write(Ctraitennf),

    % On ajoute l élément (I, Ctraitennf) à la ABox
    concatene([Ctraitennf], Abi,Abi1).

% ------------------------------------------------------------------------------------------
% Méthode permettant l acquisition de proposition du type 2 :
% ------------------------------------------------------------------------------------------
acquisition_prop_type2(Abi,Abi1,Tbox) :-
    % On entre le concept 1
    nl, write('Veuillez entrer le concept 1 :'),
    nl, read(C1),

    % On entre le concept 2
    nl, write('Veuillez entrer le concept 2 :'),
    nl, read(C2),

    % On effectue une vérification sur les deux concepts
    verification_type2([C1,C2]),

    % On effectue les manipulations sur les concepts
    % On effectue le remplacement (RC) puis on on effectue sa négation (NRC)
    traitement_Tbox([C1,C2], (C1traite_n, C2traite_n)),

    % On génère une instance et on ajoute l élément (I : C1 and C2) à la ABox
    add2((C1traite_n,C2traite_n),Abi,Abi1).

add2((C1traite,C2traite),Abi,Abi1) :- genere(Nom),
                                        concatene([(Nom,and(C1traite,C2traite))],Abi,Abi1).
% ##########################################################################################

% PARTIE I :  PREPARATION

% ##########################################################################################

/* 
  TBox
*/
% Le prédicat ci-dessus signifie qu un sculpteur est équivalent à une personne ayant crée une sculpture
equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).

cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).

cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).

iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).

rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).

% ------------------------------------------------------------------------------------------

/*
  ABox
*/
% ABox dinstances Abi
inst(michelAnge,personne). % Signifie que Michel-Ange est une personne
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).
inst(socrate,personne).

% ABox de relations Abr
instR(michelAnge, david, aCree). % Signifie que Michel-Ange a créé David
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).

% ------------------------------------------------------------------------------------------

% Règles de mises sous forme normale négative (nnf) donnée dans lénoncé
nnf(not(and(C1,C2)),or(NC1,NC2)) :- nnf(not(C1),NC1),
                                    nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)) :- nnf(not(C1),NC1),
                                    nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)) :- nnf(not(C),NC),!.
nnf(not(not(X)),X) :- !.
nnf(not(X),not(X)) :- !.
nnf(and(C1,C2),and(NC1,NC2)) :- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)) :- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)) :- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

% ------------------------------------------------------------------------------------------

% Règles de création de concepts : prédicat concept

% Verification syntaxique et semantique
concept([not(C)|_]) :- concept([C]),!.
concept([and(C1,C2)|_]) :- concept([C1]),concept([C2]),!.
concept([or(C1,C2)|_]) :- concept([C1]),concept([C2]),!.
concept([some(R,C)|_]) :- rname(R),concept([C]),!.
concept([all(R,C)|_]) :- rname(R),concept([C]),!.
concept([C|_]) :- setof(X,cnamea(X),L),member(C,L),!.
concept([C|_]) :- setof(X,cnamena(X),L),member(C,L),!.

% ------------------------------------------------------------------------------------------

% Prédicat prédéfini testant l appartenance d un élément X à une liste L
% member(X, L).

% ------------------------------------------------------------------------------------------

% Règles de remplacement (replace_concept_na)
replace_concept_na([not(C)|_],not(Ctraite)) :- replace_concept_na([C],Ctraite).
replace_concept_na([and(C1,C2)|_],and(C1traite,C2traite)) :- replace_concept_na([C1],C1traite),replace_concept_na([C2],C2traite), !.
replace_concept_na([or(C1,C2)|_],or(C1traite,C2traite)) :- replace_concept_na([C1],C1traite),replace_concept_na([C2],C2traite), !.
replace_concept_na([some(R,C)|_],some(R,Ctraite)) :- replace_concept_na([C],Ctraite), !.
replace_concept_na([all(R,C)|_],all(R,Ctraite)) :- replace_concept_na([C],Ctraite), !.
replace_concept_na([C|_],C) :- cnamea(C), !.
replace_concept_na([C|_],Ctraite) :- cnamena(C),equiv(C,Ctraite), !.

% Traitement sémantique de la Tbox (prédicat traitement_Tbox)
traitement_Tbox([],(_,_)).
traitement_Tbox([C2],(_,C2traite)) :- replace_concept_na([C2],C2traite), !.
traitement_Tbox([C1|C2],(C1traite_n,C2traite_n)) :- replace_concept_na([C1],C1traite),
                                            traitement_Tbox(C2,(C1traite,C2traite)),
                                            nnf(C1traite, C1traite_n),
                                            nnf(C2traite, C2traite_n).


% Traitement sémantique de la Abox (prédicat traitement_Abox)
traitement_Abox([I|C],(I,Ctraitennf)) :- replace_concept_na(C,Ctraite), nnf(not(Ctraite),Ctraitennf).

% ------------------------------------------------------------------------------------------

% Prédicat réalisant la concaténation de deux listes L1 et L2 et renvoie la liste L3
ajout(Ptraitennf,Abi,Abi1) :- concat([Ptraitennf],Abi,Abi1).

% ------------------------------------------------------------------------------------------
% Prédicat réalisant la suppression de X de la liste L1 et renvoie la liste résultante L2
enleve(X,[X|L],L) :- !.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

% ------------------------------------------------------------------------------------------

% Prédicat compteur et prédicat de génération d un nouvel identificateur 
% qui est fourni en sortie dans Nom
compteur(1).

genere(Nom) :- compteur(V),nombre(V,L1),
    concatene([105,110,115,116],L1,L2),
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
        concatene(L,[R2],L1).
chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').

% ------------------------------------------------------------------------------------------
% Vérification des données en entrée
% ------------------------------------------------------------------------------------------
% Vérification entrée type 1
verification_type1([I|C]) :- iname(I),concept(C).

% Vérification entrée type 2
verification_type2([]).
verification_type2([C1|C2]) :- concept([C1]),verification_type2(C2).


% Prédicat de vérification sur les instances
verificationInstance(I) :-
    iname(I), !.
% ------------------------------------------------------------------------------------------

% Prédicat de vérification sur les concepts
% Les concepts peuvent être de différentes formes donc le prédicat a plusieurs formes
verificationConcept(C) :-
    cnamea(C), !.

verificationConcept(C) :- 
    cnamena(C), !.

verificationConcept(not(C)) :- 
    verificationConcept(C), !.

verificationConcept(or(C1, C2)) :- 
    verificationConcept(C1), 
    verificationConcept(C2), !.

verificationConcept(and(C1, C2)) :- 
    verificationConcept(C1), 
    verificationConcept(C2), !.

verificationConcept(some(R, C)) :- 
    rname(R), 
    verificationConcept(C), !.

verificationConcept(all(R, C)) :- 
    rname(R), 
    verificationConcept(C), !.

% ##########################################################################################

%  PARTIE III : DEMONSTRATION DE LA PROPOSITION

% ##########################################################################################

troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            write("Debut de la resolution\n"),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl, write('Demonstration reussite ~~').

tri_Abox([],[],[],[],[],[]). /*cas d arrêt*/
tri_Abox([(I,some(R,C))|T],LieNew,Lpt,Li,Lu,Ls) :- concatene([(I,some(R,C))],Lie,LieNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!. /*some -> Lie*/
tri_Abox([(I,all(R,C))|T],Lie,LptNew,Li,Lu,Ls) :- concatene([(I,all(R,C))],Lpt,LptNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!. /*all -> Lpt*/
tri_Abox([(I,and(C1,C2))|T],Lie,Lpt,LiNew,Lu,Ls) :- concatene([(I,and(C1,C2))],Li,LiNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!. /*and -> Li*/
tri_Abox([(I,or(C1,C2))|T],Lie,Lpt,Li,LuNew,Ls) :- concatene([(I,or(C1,C2))],Lu,LuNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!. /*or -> Lu*/
tri_Abox([(I,not(C))|T],Lie,Lpt,Li,Lu,LsNew) :-concatene([(I,not(C))],Ls,LsNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!. /*not(concept) -> Ls*/
tri_Abox([(I,C)|T],Lie,Lpt,Li,Lu,LsNew) :- concatene([(I,C)],Ls,LsNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!. /*concept -> Ls*/


% affiche/1: predicat qui affiche une liste d assertions
affiche([]).
affiche([A|L]):- affiche(A),affiche(L).
affiche((A,B,R)) :- nl,write("<"),write(A),write(","),write(B),write("> : "),write(R).
affiche((I,or(C1,C2))) :- nl,write(I),write(" : "), affiche(C1),write(" ⊔ "),affiche(C2).
affiche((I,and(C1,C2))) :- nl,write(I),write(" : "), affiche(C1),write(" ⊓ "),affiche(C2).
affiche((I,C)) :- nl,write(I), write(" : "), affiche(C).
affiche(or(C1,C2)) :- write("("),affiche(C1),write(" ⊔ "),affiche(C2),write(")").
affiche(and(C1,C2)) :- write("("),affiche(C1),write(" ⊓ "),affiche(C2),write(")").
affiche(all(R,C)) :- write("∀"),write(R),write("."),affiche(C).
affiche(some(R,C)) :- write("∃"), write(R), write("."), affiche(C).
affiche(not(C)) :- write("¬"),affiche(C).
affiche(C) :- write(C).

% affiche_evolution_Abox/12 : Affiche l évolution de la Abox étendue
affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1) :- write("---État de départ de la Abox---"),
                                                                                      affiche(Ls),
                                                                                      affiche(Lie),
                                                                                      affiche(Lpt),
                                                                                      affiche(Li),
                                                                                      affiche(Lu),
                                                                                      affiche(Abr),
                                                                                      nl,nl,write("---Etat d'arrivée---"),
                                                                                      affiche(Ls1),
                                                                                      affiche(Lie1),
                                                                                      affiche(Lpt1),
                                                                                      affiche(Li1),
                                                                                      affiche(Lu1),
                                                                                      affiche(Abr1),
                                                                                      nl,write("=======FIN========"),nl,!.

/* test_clash/1 : predicat qui vaut vrai s'il n'y a pas de clash,
et faux s'il y en a un dans la liste passée en argument */
test_clash([]).
test_clash([(I,C)|T]) :- nnf(not(C),Cnnf), not(member((I,Cnnf),T)), test_clash(T).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Lie,0)), test_clash(Ls), write("\nAppel de complete_some\n"),  complete_some(Lie,Lpt,Li,Lu,Ls,Abr). /*règle il existe*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Li,0)), test_clash(Ls), write("\nAppel de transformation_and\n"), transformation_and(Lie,Lpt,Li,Lu,Ls,Abr). /*règle et*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Lpt,0)), test_clash(Ls), write("\nAppel de deduction_all\n"), deduction_all(Lie,Lpt,Li,Lu,Ls,Abr). /*règle pour tout*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Lu,0)), test_clash(Ls), write("\nAppel de transformation_or \n"), transformation_or(Lie,Lpt,Li,Lu,Ls,Abr). /*règle ou*/
resolution([],[],[],[],Ls,Abr) :- not(test_clash(Ls)), write("\nBranche fermée !!\n").

/*evolue/11 : màj des listes de Abe*/
evolue((I,some(R,C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt,Li,Lu,Ls) :- concatene([(I,some(R,C))],Lie,Lie1),!.
evolue((I,and(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li1,Lu,Ls) :- concatene([(I,and(C1,C2))],Li,Li1),!.
evolue((I,or(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu1,Ls) :- concatene([(I,or(C1,C2))],Lu,Lu1),!.
evolue((I,all(R,C)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt1,Li,Lu,Ls) :- concatene([(I,all(R,C))],Lpt,Lpt1),!.
evolue((I,not(C)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu,Ls1) :- cnamea(C), concatene([(I,not(C))],Ls,Ls1),!. /*si C est un concept atomique, on ajoute dans Ls*/
evolue((I,not(C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1) :- not(cnamea(C)), nnf(not(C),NotCnnf), evolue((I,NotCnnf),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),!. /*sinon, on prend le nnf pour le mettre dans la bonne liste*/
evolue((I,C),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu,Ls1):- concatene([(I,C)],Ls,Ls1),!.

generer(B):- random(10,100000,B).

complete_some([(I,some(R,C))|Tie],Lpt,Li,Lu,Ls,Abr) :- generer(B), /*on cree un nouvel objet B*/
                                                       concatene([(I,B,R)],Abr,AbrNew), /*on ajoute (I,B,R) dans Abr*/
                                                       evolue((B,C),Tie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /*l ajout de (B,C) depend de la nature de C*/
                                                       affiche_evolution_Abox(Ls,[(I,some(R,C))|Tie], Lpt, Li, Lu ,Abr, Ls1, Lie1, Lpt1, Li1, Lu1, AbrNew),
                                                       resolution(Lie1,Lpt1,Li1,Lu1,Ls1,AbrNew). /*on boucle*/


transformation_and(Lie,Lpt,[(I,and(C1,C2))|Ti],Lu,Ls,Abr) :- evolue((I,C1),Lie,Lpt,Ti,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /*ajout de (I,C1)*/
                                                             evolue((I,C2),Lie1,Lpt1,Li1,Lu1,Ls1,Lie2,Lpt2,Li2,Lu2,Ls2), /*ajout de (I,C2)*/
                                                             affiche_evolution_Abox(Ls,Lie, Lpt, [(I,and(C1,C2))|Ti], Lu ,Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
                                                             resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr).


presence_all((I,B,R),Abr):- member((I,B,R), Abr),!.


deduction_all(Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls,Abr) :- member((I,B,R),Abr), /*on a du I : all(R,C) donc pour utiliser la règle ∀, on cherche une relation <I,B> : R*/
                                                      evolue((B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /* ajout de (B,C)*/
                                                      affiche_evolution_Abox(Ls,Lie, [(I,all(R,C))|Lpt], Li, Lu , Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
                                                      resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).


transformation_or(Lie,Lpt,Li,[(I,or(C1,C2))|Tu],Ls,Abr) :- evolue((I,C1),Lie,Lpt,Li,Tu,Ls,Lie1g,Lpt1g,Li1g,Lu1g,Ls1g), /*ajout fils gauche*/
                                                           affiche_evolution_Abox(Ls,Lie,Lpt, Li, [(I,or(C1,C2))|Tu] , Abr, Ls1g, Lie1g,Lpt1g,Li1g,Lu1g, Abr),
                                                           evolue((I,C2),Lie,Lpt,Li,Tu,Ls,Lie1d,Lpt1d,Li1d,Lu1d,Ls1d), /*ajout fils droit*/
                                                           affiche_evolution_Abox(Ls,Lie,Lpt, Li, [(I,or(C1,C2))|Tu] , Abr, Ls1d, Lie1d,Lpt1d,Li1d,Lu1d, Abr),
                                                           resolution(Lie1g,Lpt1g,Li1g,Lu1g,Ls1g,Abr), /*fils gauche*/
                                                           resolution(Lie1d,Lpt1d,Li1d,Lu1d,Ls1d,Abr). /*fils droit*/
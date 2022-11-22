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
% Méthode permettant l acquisition de proposition du type 2 : (C1 and C2 compris dans 'neg')
acquisition_prop_type2(Abi,Abi1,Tbox) :-
    % On entre le concept 1
    nl, write('Veuillez entrer le concept 1 :'),
    nl, read(C1),

    % On effectue une vérification sur le concept 1
    % verification_type2(C1),

    % On entre le concept 2
    nl, write('Veuillez entrer le concept 2 :'),
    nl, read(C2),
    % On effectue une vérification sur le concept 2
    verification_type2([C1,C2]),
    % On effectue les manipulations sur les concepts
    % On effectue le remplacement (RC) puis on on effectue sa négation (NRC)
    traitement_Tbox([C1,C2], RC),
    nl, write(RC),
    nnf(RC, NRC),
    nl, write(NRC),
    % On génère une instance et on ajoute l élément (I : C1 and C2) à la ABox
    ajout2(NRC,Abi,Abi1).

ajout2((C1traite,C2traite),Abi,Abi1) :- genere(Nom),
                                        concatene([(Nom,and(C1traite,C2traite))],Abi,Abi1).
% ##########################################################################################

%  PARTIE 3

% ##########################################################################################

% Prédicat de la troisième étape
troisieme_etape(Abi,Abr) :- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    affiche_evolution_Abox(Lie,Lpt,Li,Li,Ls,Abr),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,write('Demonstration reussite ~~').

% ##########################################################################################

% PARTIE PREPARATION

% ##########################################################################################

/* 
  TBox
*/
equiv(sculpteur,and(personne,some(aCree,sculpture))). 
% Le prédicat ci-dessus signifie qu un sculpteur est équivalent à une personne ayant crée une sculpture
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

% Règles de mises sous forme normale négative (NNF) donnée dans lénoncé
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
/*
concept(and(C1,C2)) :- concept(C1), concept(C2), !.
concept(or(C1,C2)) :- concept(C1), concept(C2), !.
concept(all(R,C)) :- concept(C) ,concept(R), !.
concept(some(R,C)) :- concept(C),concept(R) ,!.
concept(not(C)) :- concept(C) ,!.
concept(C) :- cnamea(C), !.
concept(C) :- rname(C), !.
concept(C) :- cnamena(C), !.
*/

/* Verification syntaxique et semantique */
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
traitement_Tbox([C1|C2],(C1traite,C2traite)) :- replace_concept_na([C1],C1traite),
                                            traitement_Tbox(C2,(C1traite,C2traite)).


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

genere(Nom) :-  compteur(V), nombre(V,L1),
                concat([105,110,115,116],L1,L2),
                V1 is V+1,
                dynamic(compteur/1),
                retract(compteur(V)),
                dynamic(compteur/1),
                assert(compteur(V1)), nl, nl, nl,
                name(Nom,L2).

nombre(0,[]).
nombre(X,L1) :- R is (X mod 10),
                Q is ((X-R)//10),
                chiffre_car(R,R1),
                char_code(R1,R2),
                nombre(Q,L),
                concat(L,[R2],L1).

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


% ------------------------------------------------------------------------------------------
% Vérification des données en entée
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

% ------------------------------------------------------------------------------------------

% Prédicat de tri des différentes listes lors de la résolution
% Voir lénoncé du projet ou le rapport pour plus de précision par rapport aux listes
tri_Abox([],[],[],[],[],[]).

tri_Abox([(I,some(R,C))|Abi],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls) :- 
  tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

tri_Abox([(I,all(R,C))|Abi],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls) :- 
  tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

tri_Abox([(I,and(C1,C2))|Abi],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls) :- 
  tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

tri_Abox([(I,or(C1,C2))|Abi],Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls) :- 
  tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

tri_Abox([E|Abi],Lie,Lpt,Li,Lu,[E|Ls]) :- 
  tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

% ------------------------------------------------------------------------------------------

% Prédicat réalisant la résolution de propositions
resolution([],[],[],[],Ls,Abr) :- 
    not(verificationClash(Ls)), nl, !.

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- 
    verificationClash(Ls), 
    Lie \== [], 
    complete_some(Lie,Lpt,Li,Lu,Ls,Abr).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-	
    verificationClash(Ls),	
    Li \== [], 
    transformation_and(Lie,Lpt,Li,Lu,Ls,Abr).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-	
    verificationClash(Ls),	
    Lpt \==[], 
    deduction_all(Lie,Lpt,Li,Lu,Ls,Abr).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-	
    verificationClash(Ls),	
    Lu \==[], 
    transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).
 

% ------------------------------------------------------------------------------------------

% Prédicat réalisant la vérification de clashs lors de la résolution de proposition
verificationClash([(I,C)|Ls]) :-
    nnf(not(C),NC),
    member((I,NC),Ls),
    write('\nOn trouve un clash avec : '),
    write(I), nl.

verificationClash([_|Ls]) :- 
    verificationClash(Ls).

% ------------------------------------------------------------------------------------------

% Prédicat d  évolution
% Permet la mise à jour des différentes listes lors de la résolution
evolue((I,and(A,B)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, [(I,and(A,B))|Li], Lu, Ls).
evolue((I,all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, [(I,all(R,C))|Lpt], Li, Lu, Ls).
evolue((I,some(R,C)), Lie, Lpt, Li, Lu, Ls, [(I,some(R,C))|Lie], Lpt, Li, Lu, Ls).
evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, [(I,or(C1,C2))|Lu], Ls).
evolue(Elem, Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(Elem)|Ls]).

% ------------------------------------------------------------------------------------------

% Prédicat de complétion
% Représente la règle : 'il existe'
complete_some([],Lpt,Li,Lu,Ls,Abr) :-
    transformation_and([],Lpt,Li,Lu,Ls,Abr).

complete_some([(I1,some(R,C))|Lie],Lpt,Li,Lu,Ls,Abr) :-
    genere(I2),
    Abr1 = Abr,
    evolue((I2,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
    Abr2 = [(I1,I2,R)|Abr],
    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,[(I1,I2,R)|Abr]).

% ------------------------------------------------------------------------------------------

% Prédicat de déduction
% Représente la règle : 'pour tout'
deduction_all(Lie,[],Li,Lu,Ls,Abr) :-
    transformation_or(Lie,[],Li,Lu,Ls,Abr).

deduction_all(Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls,Abr) :-
    member((I,B,R),Abr),
    evolue((B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

% ------------------------------------------------------------------------------------------

% Prédicat de transformation (formule 'or' et 'and')
% Représente la règle 'ou'
transformation_or(Lie,Lpt,Li,[(I,or(C,D))|Lu],Ls,Abr):- 
    evolue((I,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
    evolue((I,D),Lie,Lpt,Li,Lu,Ls,Lie2,Lpt2,Li2,Lu2,Ls2),
    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr),
    resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr).

% Représente la règle 'et'
transformation_and(Lie,Lpt,[],Lu,Ls,Abr) :-
    deduction_all(Lie,Lpt,[],Lu,Ls,Abr).

transformation_and(Lie,Lpt,[(I,and(A,B))|Li],Lu,Ls,Abr) :-
    evolue((I,A),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
    evolue((I,B),Lie1,Lpt1,Li1,Lu1,Ls1,Lie2,Lpt2,Li2,Lu2,Ls2),
    resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr).

% ------------------------------------------------------------------------------------------

% Prédicat effectuant l affichage de la ABox
affiche_evolution_Abox(Lie,Lpt,Li,Lu,Ls,Abr) :- 
    write('\n###################################################################################'),
    nl, write('\nListe Abi :'),
    affiche(Lie),
    affiche(Lpt),
    affiche(Li),
    affiche(Lu),
    affiche(Ls),
    nl, write('\nListe Abr :'), 
    affiche(Abr), !.

% Prédicat permettant l'affichage d'une liste d'éléments et d'éléments sous une forme précise (and, or)
affiche([]).

affiche([H|T]) :- affiche(H), affiche(T).

affiche((I,some(R,C))) :- 
    nl,write('\t'), affiche(I), write(' : some.'), affiche(R), write('.'),affiche(C), !.

affiche((I,all(R,C))) :-  
    nl,write('\t'), affiche(I), write(' : all.'), affiche(R), write('.'),affiche(C), !.

affiche((I, and(C,D))) :- 
    nl,write('\t'), affiche(I), write(' : '), affiche(C), write(' and '), affiche(D), !.

affiche((I,or(C,D))) :- 
    nl,write('\t'), affiche(I), write(' : ') , affiche(C), write(' or '), affiche(D), !.

affiche((not(C))) :- 
    write('not '), affiche(C).

affiche((I,C,R)) :- 
    nl, write('\t<'), affiche(I), write(', '), affiche(C), write('> : ') , affiche(R), !.

affiche((I,C)) :- 
    nl,write('\t'), affiche(I), write(' : ') , affiche(C), !.

affiche(some(R,C)) :- 
    write(' some.'), affiche(R),write('.'),affiche(C), !.

affiche(all(R,C)) :- 
    write(' all.'), affiche(R),write('.'),affiche(C), !.

affiche(and(C,D)) :- 
    affiche(C), write(' and '), affiche(D), !.

affiche(or(C,D)) :- 
    affiche(C), write(' or '), affiche(D), !.

affiche(C) :- write(C).
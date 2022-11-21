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

% Cette methode permet de creer des listes qui vont contenir la TBox, la ABox d'instances et la ABox de rôles.
% Ces listes evolueront au fur et à mesure qu'on soumettra des propositions à la démonstration.
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
% On met en place les méthodes utilisées plus haut
% ------------------------------------------------------------------------------------------

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
    verificationConcept(C),

    % On effectue les manipulations sur le concept
    % On le remplace (RC) puis on effectue sa négation (NRC)
    replace(C, RC),
    nnf(not(RC),NRC),

    % On ajoute l élément (I, NRC) à la ABox
    concat([((I,NRC))],Abi,Abi1).

% ------------------------------------------------------------------------------------------

% Méthode permettant l acquisition de proposition du type 2 : (C1 and C2 compris dans 'neg')
acquisition_prop_type2(Abi,Abi1,Tbox) :-
    % On entre le concept 1
    nl, write('Veuillez entrer le concept 1 :'),
    nl, read(C1),

    % On effectue une vérification sur le concept 1
    verificationConcept(C1),

    % On entre le concept 2
    nl, write('Veuillez entrer le concept 2 :'),
    nl, read(C2),

    % On effectue une vérification sur le concept 2
    verificationConcept(C2),

    % On effectue les manipulations sur les concepts
    % On effectue le remplacement (RC) puis on on effectue sa négation (NRC)
    replace(and(C1, C2), RC),
    nnf(RC, NRC),

    % On génère une instance et on ajoute l élément (I : C1 and C2) à la ABox
    genere(Inst),
    concat([((Inst,NRC))], Abi, Abi1).

/* ##########################################################################################

  PARTIE 3

 ##########################################################################################*/

% Prédicat de la troisième étape
troisieme_etape(Abi,Abr) :- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    affiche_evolution_Abox(Lie,Lpt,Li,Li,Ls,Abr),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').

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
 
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).

instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).

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
concept(and(C1,C2)) :- concept(C1), concept(C2), !.
concept(or(C1,C2)) :- concept(C1), concept(C2), !.
concept(all(R,C)) :- concept(C) ,concept(R), !.
concept(some(R,C)) :- concept(C),concept(R) ,!.
concept(not(C)) :- concept(C) ,!.
concept(C) :- cnamea(C), !.
concept(C) :- rname(C), !.
concept(C) :- cnamena(C), !.

% ------------------------------------------------------------------------------------------

% Prédicat prédéfini testant l appartenance d un élément X à une liste L
% member(X, L).

% ------------------------------------------------------------------------------------------

% Règles de remplacement (replace)
replace_concept_na(C,C) :- cnamea(C).
replace_concept_na(not(C),not(RC)) :- replace_concept_na(C,RC).
replace_concept_na(and(C1,C2),and(RC1,RC2)) :- replace_concept_na(C1,RC1), replace_concept_na(C2,RC2).
replace_concept_na(or(C1,C2),or(RC1,RC2)) :- replace_concept_na(C1,RC1), replace_concept_na(C2,RC2).
replace_concept_na(all(R,C),all(R,RC)) :- replace_concept_na(C,RC).
replace_concept_na(some(R,C),some(R,RC)) :- replace_concept_na(C,RC).
replace_concept_na(C,RC) :- equiv(C,C2), replace_concept_na(C2,RC).

traitement_Tbox([],(_,_)).
traitement_Tbox([C2],(_,C2traite)) :- replace_concept_na([C2],C2traite), !.
traitement_Tbox([C1|C2],(C1traite,C2traite)) :- replace_concept_na([C1],C1traite),
                                            traitement_Tbox(C2,(C1traite,C2traite)).


traitement_Abox([I|C],(I,Ctraitennf)) :- replace_concept_na(C,Ctraite), nnf(not(Ctraite),Ctraitennf).

ajout(Ptraitennf,Abi,Abi1) :- concat([Ptraitennf],Abi,Abi1).

% ------------------------------------------------------------------------------------------

% Prédicat réalisant la concaténation de deux listes L1 et L2 et renvoie la liste L3
concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

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
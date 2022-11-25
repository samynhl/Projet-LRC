%                                                 PROJET
%                                              LRC - M1 DAC
%                                     NEHLIL Samy - BOUTALEB Allaa

% ____________________________________________________________________________________________________________________

% MAIN

% ____________________________________________________________________________________________________________________

programme :-
    nl, write('M1 DAC - PROJET LRC - Samy NEHLIL et Allaa BOUTALEB'), nl,

    nl, write('_______________________________________ Premiere partie _______________________________________'), nl,
    premiere_etape(TBox, Abi, Abr),

    nl, write('_______________________________________ Deuxieme partie _______________________________________'), nl,
    deuxieme_etape(Abi, Abi1, Tbox),

    nl, write('_______________________________________ Troisieme partie ______________________________________'), nl,
    troisieme_etape(Abi1, Abr).

% ____________________________________________________________________________________________________________________

% PARTIE 1

% ____________________________________________________________________________________________________________________

% Cette methode permet de creer des listes qui vont contenir la TBox, la ABox d instances et la ABox de rôles.
% Ces listes evolueront au fur et à mesure qu on soumettra des propositions à la démonstration.
premiere_etape(Tbox, Abi, Abr) :-
    % Affichage de la Tbox et de la Abox
    setof((X, Y), equiv(X, Y), Tbox),
    nl, write('Tbox = '), write(Tbox), nl,

    setof((X, Y), inst(X, Y), Abi),
    nl, write('Abi = '), write(Abi), nl,

    setof((X, Y, Z), instR(X, Y, Z), Abr),
    nl, write('Abr = '), write(Abr), nl,

    % Réalisation des traitements préliminaires sur la Tbox et la Abox : Partie I
    traitement_Tbox(Tbox, Tbox1, Tbox),
    nl, write("Traitement de la Tbox realise avec succes"),
    nl, traitement_Abox(Abi, Abi1, Abr, Abr2, Tbox),
    nl, write("Traitement de la Abox realise avec succes").

% ____________________________________________________________________________________________________________________

% PARTIE 2

% ____________________________________________________________________________________________________________________

% Méthode de la deuxième étape
deuxieme_etape(Abi,Abi1,Tbox) :-
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

% ____________________________________________________________________________________________________________________

% Mise en place du code donnée dans lénoncé
saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
    nl,write('Entrer le numero du type de proposition que l"on souhaite demontrer :'),
    nl,write('\tType 1 - Une instance donnee appartient a un concept donne.'),
    nl,write('\tType 2 - Deux concepts n-elements en commun dont l"intersection est vide (negation).'),
    nl,read(R),
    suite(R,Abi,Abi1,Tbox), !.

% ____________________________________________________________________________________________________________________

suite(1,Abi,Abi1,Tbox) :-
    acquisition_prop_type1(Abi,Abi1,Tbox), !.

% ____________________________________________________________________________________________________________________

suite(2,Abi,Abi1,Tbox) :-
    acquisition_prop_type2(Abi,Abi1,Tbox), !.

% ____________________________________________________________________________________________________________________

suite(R,Abi,Abi1,Tbox) :-
    nl, write('Cette option n"existe pas.'),
    nl, saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

% ____________________________________________________________________________________________________________________
% On met en place les methodes utilisées plus haut
% ____________________________________________________________________________________________________________________

/*concat/3 : concatene les deux listes L1 et L2 dans L3.*/
concatene([],L1,L1).
concatene([X|Y],L1,[X|L2]) :- concatene(Y,L1,L2).

% Méthode permettant l acquisition de propositions du type 1 (I : C)
acquisition_prop_type1(Abi,Abi1,Tbox) :-
    % On entre le type de l instance
    nl, write('Veuillez entrer l"instance :'),
    nl, read(I),

    % On réalise une vérification sur l instance
    iname(I),

    % On entre le concept
    nl, write('Veuillez entrer le concept :'),
    nl, read(C),

    % On effectue une vérification sur le concept
    % verificationConcept(C)

    % On effectue les manipulations sur le concept
    % On le remplace (RC) puis on effectue sa négation (NRC)
    rev([I,C],Ctraitennf),

    % On ajoute l élément (I, Ctraitennf) à la ABox
    concatene([Ctraitennf], Abi,Abi1).

rev([I|C],(I,Ctraitennf)) :- replace_concept_na(C,Ctraite), nnf(not(Ctraite),Ctraitennf).
% ____________________________________________________________________________________________________________________
% Méthode permettant l acquisition de proposition du type 2 :
% ____________________________________________________________________________________________________________________
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
    genere(Inst),
    concatene([(Inst,and(C1traite,C2traite))],Abi,Abi1).

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
% sculpture ≡ objet ⊓ ∀cree_par.sculpteur : tester le prédicat autoref
% equiv(sculpture,and(objet,all(cree_par,sculpteur))).


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
rname(cree_par).

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

concept(C) :- cnamea(C),!.
concept(C) :- cnamena(C),!.
concept(not(C)) :- concept(C),!.
concept(and(C1,C2)) :- concept(C1), concept(C2),!.
concept(or(C1,C2)) :- concept(C1), concept(C2),!.
concept(some(R,C)) :- rname(R), concept(C),!.
concept(all(R,C)) :- rname(R), concept(C),!.

% ------------------------------------------------------------------------------------------

% Prédicat prédéfini testant l appartenance d un élément X à une liste L
% member(X, L).

% ------------------------------------------------------------------------------------------

% Règles de remplacement des concepts non atomiques par leur définition (replace_concept_na)
replace_concept_na([not(C)|_],not(Ctraite)) :- replace_concept_na([C],Ctraite).
replace_concept_na([and(C1,C2)|_],and(C1traite,C2traite)) :- replace_concept_na([C1],C1traite),replace_concept_na([C2],C2traite), !.
replace_concept_na([or(C1,C2)|_],or(C1traite,C2traite)) :- replace_concept_na([C1],C1traite),replace_concept_na([C2],C2traite), !.
replace_concept_na([some(R,C)|_],some(R,Ctraite)) :- replace_concept_na([C],Ctraite), !.
replace_concept_na([all(R,C)|_],all(R,Ctraite)) :- replace_concept_na([C],Ctraite), !.
replace_concept_na([C|_],C) :- cnamea(C), !.
replace_concept_na([C|_],Ctraite) :- cnamena(C),equiv(C,Ctraite), !.

% ------------------------------------------------------------------------------------------
% remplace les concepts non atomiques par leur définition, met lexpression sous nnf
transform(C, NC):-
    replace_concept_na(C, CA),
    nnf(CA, NC),!.

traitement_Tbox([], [], _).
traitement_Tbox([(C, E)|L], [(C, E1)|L1], Tbox) :-
    cnamena(C),
    concept(E),
    % nl,write(C),write("\t",E), % debug
    %nl,write("pas concept"), % debug
    pas_autoref(C, E, Tbox),
    %nl,write("pas autoref"), % debug
    transform([E], E1),
    traitement_Tbox(L, L1, Tbox),!.

traitement_Abi([], [], _).
traitement_Abi([(I, C)|L], [(I, C1)|L1], Tbox) :-
    concept(C),
    nl,write("concept"),
    transform([C], C1),
    traitement_Abi(L, L1, Tbox),!.

traitement_Abr([], [], _).
traitement_Abr([(I1, I2, R)|L], [(I1, I2, R)|L1], Tbox) :-
    iname(I1),
    iname(I2),
    rname(R),
    traitement_Abr(L, L1, Tbox),!.

traitement_Abox(Abi, Abi1, Abr, Abr1, Tbox) :-
    traitement_Abi(Abi, Abi1, Tbox),
    nl, write("Traitement Abi avec succes"),nl,
    traitement_Abr(Abr, Abr1, Tbox),
    nl, write("Traitement Abr avec succes").
% ________________________________________________________________________________________
% Prédicat qui retourne dans Y le concept non atomique utilisé dans la définition de X
% utile dans pas_autoref
retrieve_na(X, X, _) :- 
    cnamea(X).
retrieve_na(X, D, [(X, D)|_]).
retrieve_na(X, Y, [(C, _)|L]) :-    
    X \= C, 
    retrieve_na(X, Y, L).

pas_autoref(_, E, _) :-
    % Si prédicat utilisé dans la définition est atomique, retourne vrai car cycle impossible
    cnamea(E), !.
pas_autoref(C, E, Tbox) :-
    % Si prédicat E utilisé non atomique, vérifier qu il contient pas C
    cnamena(E),
    retrieve_na(E, D, Tbox),
    pas_autoref(C, D, Tbox).
% Différents cas de concepts
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
chiffre_car(8,'8').
chiffre_car(9,'9').

% ------------------------------------------------------------------------------------------
% Vérification des données en entrée
% ------------------------------------------------------------------------------------------
% ##########################################################################################

%  PARTIE III : DEMONSTRATION DE LA PROPOSITION

% ##########################################################################################

troisieme_etape(Abi,Abr) :- 
                            tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl,write('Youpiiiiii, on a demontre la 
                            proposition initiale !!!').

% Le prédicat tri_Abox, à partir de la liste des assertions de concepts de la Abox étendue 
tri_Abox([],[],[],[],[],[]). /*cas d arrêt*/
% some -> Lie
% Si une expression de type (I,some(R,C)) est rencontre on lajoute à Lie
tri_Abox([(I,some(R,C))|T],LieNew,Lpt,Li,Lu,Ls) :- concatene([(I,some(R,C))],Lie,LieNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!.
% all -> Lpt
% Si une expression de type (I,all(R,C)) est rencontre on lajoute à Lpt
tri_Abox([(I,all(R,C))|T],Lie,LptNew,Li,Lu,Ls) :- concatene([(I,all(R,C))],Lpt,LptNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!.
% and -> Li
% Si une expression de type (I,and(C1,C2)) est rencontre on lajoute à Li
tri_Abox([(I,and(C1,C2))|T],Lie,Lpt,LiNew,Lu,Ls) :- concatene([(I,and(C1,C2))],Li,LiNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!.
% or -> Lu
% Si une expression de type (I,or(C1,C2)) est rencontre on lajoute à Lu
tri_Abox([(I,or(C1,C2))|T],Lie,Lpt,Li,LuNew,Ls) :- concatene([(I,or(C1,C2))],Lu,LuNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!.
% not(concept) -> Ls
% Si une expression de type (I,not(C)) est rencontre on lajoute à Ls
tri_Abox([(I,not(C))|T],Lie,Lpt,Li,Lu,LsNew) :-concatene([(I,not(C))],Ls,LsNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!.
% concept -> Ls
% Si une expression de type (I,C) est rencontre on lajoute à Ls
tri_Abox([(I,C)|T],Lie,Lpt,Li,Lu,LsNew) :- concatene([(I,C)],Ls,LsNew), tri_Abox(T,Lie,Lpt,Li,Lu,Ls),!.


% Predicat qui affiche une liste d assertions
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
% Il sagit dutiliser le prédicat affiche définie ci-dessus afin d afficher l etat de
% la Abox avant et après la résolution en utilisant la methode des tableaux sémantiques
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


%%% test_clash/1 : retourne vrai si pas de clash dans la liste, faux sinon
% Idée : Si un concept C est dans le tableau quon developpe, verifier si nnf(C) y est aussi
% Si oui alors clash, sinon pas de clash
test_clash([]).
test_clash([(I,C)|T]) :- nnf(not(C),Cnnf), not(member((I,Cnnf),T)), test_clash(T).

%%% Prédicat résolution
% Règle IL EXISTE
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Lie,0)), test_clash(Ls), write("\nAppel de complete_some\n"),  complete_some(Lie,Lpt,Li,Lu,Ls,Abr).
% règle ET
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Li,0)), test_clash(Ls), write("\nAppel de transformation_and\n"), transformation_and(Lie,Lpt,Li,Lu,Ls,Abr). 
% règle POUR TOUT
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Lpt,0)), test_clash(Ls), write("\nAppel de deduction_all\n"), deduction_all(Lie,Lpt,Li,Lu,Ls,Abr). 
% règle OU
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- not(length(Lu,0)), test_clash(Ls), write("\nAppel de transformation_or \n"), transformation_or(Lie,Lpt,Li,Lu,Ls,Abr). 

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

/*
Ce prédicat cherche une assertion de concept de la forme (I,some(R,C)) dans la liste Lie. 
S’il  en  trouve  une,  il  cherche  à  appliquer  la  règle  ∃
*/
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
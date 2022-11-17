/* --------------------------------------------------------------------------------------------------------------------------- */

/* PARTIE 1 : PRELIMINAIRES */

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

inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).

instR(michelAnge,david,aCree).
instR(michelAnge,sonnets,aEcrit).
instR(vinci,joconde,aCree).

/*TBox :
[(sculpteur,and(personne,some(aCree,sculpture))), (auteur,and(personne,some(aEcrit,livre))), (editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))), (parent,and(personne,some(aEnfant,anything)))]
*/

/*ABox :
  - assertions de concepts :
[(michelAnge,personne), (david,sculpture), (sonnets,livre), (vinci,personne), (joconde,objet)]
  - assertions de rôles :
  [(michelAnge, david, aCree), (michelAnge, sonnet, aEcrit),(vinci, joconde, aCree)]
*/


compteur(1).

programme :- premiere_etape(Tbox,Abi,Abr),
             deuxieme_etape(Abi,Abi1,Tbox),
             troisieme_etape(Abi1,Abr).

/*Paramètres
- premiere_etape :
  Tbox = liste représentant la TBox
  Abi = liste représentant les assertions de concepts de la ABox
  Abr = liste représentant les assertions de rôles de la ABox

- deuxieme_etape :
  Abi = liste des assertions de concepts initiales
  Abi1 = liste des assertions de concepts complétée après la soumission d'une proposition a demontrer
  Tbox = liste représentant la TBox

- troisieme_etape :
  Abi1 = liste des assertions de concepts complétée
  Abr =  liste des assertions de rôles qui peut également évoluer lors de la démonstration
*/


premiere_etape(
  [(sculpteur,and(personne,some(aCree,sculpture))), (auteur,and(personne,some(aEcrit,livre))), (editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))), (parent,and(personne,some(aEnfant,anything)))],
  [(michelAnge,personne), (david,sculpture), (sonnets,livre), (vinci,personne), (joconde,objet)],
  [(michelAnge, david, aCree), (michelAnge, sonnets, aEcrit),(vinci, joconde, aCree)]
).

/* PARTIE 2 : SAISIE DE LA PROPOSITION A DEMONTRER */

deuxieme_etape(Abi,Abi1,Tbox) :-
  saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
  nl, write('Entrez le numero du type de proposition que vous voulez demontrer :'), nl,
  write('1 = Une instance donnee appartient a un concept donne.'), nl,
  write('2 = Deux concepts n`ont pas d"elements en commun (ils ont une intersection vide).'), nl,
  read(R), suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(_,Abi,Abi1,Tbox) :- nl, write('Cette reponse est incorrecte'),nl,
  saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).


acquisition_prop_type1(Abi,Abi1,Tbox) :-
  nl, write("Entrez la proposition a montrer (d'abord l'instance, puis le concept, puis tapez 'fin.') :"), nl,
  lecture(P), /*P = [I,C] où I est une instance I et C un concept existants*/
  correction(P),  /*verification syntaxique et semantique*/
  traitement(P,Ptraitennf), /*P=[I,C], Ctraitennf = nnf de not(C)*/
  ajout(Ptraitennf,Abi,Abi1). /*ajout dans Abi1*/

/* Ecriture en forme normale negative - Donnée dans l'énoncé du projet*/
nnf(not(and(C1,C2)),or(NC1,NC2)) :- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)) :- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)) :- nnf(not(C),NC),!.
nnf(not(not(X)),X) :- !.
nnf(not(X),not(X)) :- !.
nnf(and(C1,C2),and(NC1,NC2)) :- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)) :- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)) :- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

/* Vérification des expressions entrées par l'utilisateur au clavier*/
% Prédicat de vérification sur les instances
verificationInstance(I) :-
    iname(I), !.
/*Prédicat de vérification sur les concepts
Les concepts peuvent être atomiques ou complexes donc le prédicat a plusieurs formes*/
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

/* ------------------------------------------------------------------------------------------*/
/* Verification syntaxique et semantique  et creation du prédicat concept*/
/* ------------------------------------------------------------------------------------------

% Prédicat prédéfini testant l'appartenance d'un élément X à une liste L
% member(X, L).
 
  ------------------------------------------------------------------------------------------*/
concept([not(C)|_]) :- concept([C]),!.
concept([and(C1,C2)|_]) :- concept([C1]),concept([C2]),!.
concept([or(C1,C2)|_]) :- concept([C1]),concept([C2]),!.
concept([some(R,C)|_]) :- rname(R),concept([C]),!.
concept([all(R,C)|_]) :- rname(R),concept([C]),!.
concept([C|_]) :- setof(X,cnamea(X),L),member(C,L),!.
concept([C|_]) :- setof(X,cnamena(X),L),member(C,L),!.


/* 
   Définition du concept pas_autoref :
   Permet de vérifier que un concept complexe (non atomique) de la Tbox n'est pas circulaire
*/
pas_autoref([C|_],C) :- cnamea(C), !.
pas_autoref([C|_],Ctraite) :- cnamena(C),equiv(C,C1),!.

/* 
Remplacement des concepts complexes par leur definition equivalente en nnf 
Le prédicat remplace_concepts_complexes remplace le concept non atomique c donné en entrée
par sa définition (retrouvée dans equiv dans la Tbox)
*/
remplace_concepts_complexes([not(C)|_],not(Ctraite)) :- remplace_concepts_complexes([C],Ctraite).
remplace_concepts_complexes([and(C1,C2)|_],and(C1traite,C2traite)) :- remplace_concepts_complexes([C1],C1traite),
                                                                  remplace_concepts_complexes([C2],C2traite), !.
remplace_concepts_complexes([or(C1,C2)|_],or(C1traite,C2traite)) :- remplace_concepts_complexes([C1],C1traite),
                                                                remplace_concepts_complexes([C2],C2traite), !.
remplace_concepts_complexes([some(R,C)|_],some(R,Ctraite)) :- remplace_concepts_complexes([C],Ctraite), !.
remplace_concepts_complexes([all(R,C)|_],all(R,Ctraite)) :- remplace_concepts_complexes([C],Ctraite), !.
remplace_concepts_complexes([C|_],C) :- cnamea(C), !.
remplace_concepts_complexes([C|_],Ctraite) :- cnamena(C),equiv(C,Ctraite), !.

/* 
Correction des instances et concepts entrés par l'utilisateur
Il s'agit de vérifier que le nom instance est bien présente dans la 
*/
correction([I|C]) :- iname(I),concept(C).

traitement([I|C],(I,Ctraitennf)) :- remplace_concepts_complexes(C,Ctraite),
                                    nnf(not(Ctraite),Ctraitennf).

ajout(Ptraitennf,Abi,Abi1) :- concat([Ptraitennf],Abi,Abi1).


acquisition_prop_type2(Abi,Abi1,Tbox) :-
  nl, write("Entrez la proposition a montrer (d'abord le premier concept, puis le second, puis tapez 'fin.') :"), nl,
  lecture(P), /*P=[C1,C2] où C1 et C2 sont des concepts. */
  correction2(P),  /*verification syntaxique et semantique*/
  traitement2(P,Ptraite), /*P=[C1,C2], Ptraite = P où on a remplacé les concepts complexes par leur définition*/
  ajout2(Ptraite,Abi,Abi1). /*ajout dans Abi1*/

correction2([]).
correction2([C1|C2]) :- concept([C1]),correction2(C2).

traitement2([],(_,_)).
traitement2([C2],(_,C2traite)) :- remplace_concepts_complexes([C2],C2traite), !.
traitement2([C1|C2],(C1traite,C2traite)) :- remplace_concepts_complexes([C1],C1traite),
                                            traitement2(C2,(C1traite,C2traite)).

ajout2((C1traite,C2traite),Abi,Abi1) :- genere(Nom),
                                        concat([(Nom,and(C1traite,C2traite))],Abi,Abi1).
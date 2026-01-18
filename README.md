## Lexing
Comme indiqué dans le sujet, aucun token WHITE/NEWLINE n'est généré par le lexer, 
à la place deux token différents pour la parenthèse ouvrante pour savoir si elle vient après un espace ou nom.

## Parsing
Pour résoudre les conflit, il a parfois fallu décomposer des règles ou en rassembler, par exemple ublock n'apparait plus car 
j'ai choisi de séparer la règle block en petit et grand block selon par quel symbole il a été introduit ("block:" ou juste ":")
J'ai aussi choisi, à postériori de désucrer directement les boucles for pour simplifier le typage.
Sinon les difficultés du parsing étaient globalement du bricolage pour garder la même grammaire tout en résolvant les conflits.

- Je n'ai pas implémenter la contrainte d'avoir un seul statement par ligne ( je trouvais ça plutôt pratique de pouvoir mettre des statement sur la même ligne quand cela ne créer pas d'ambiguïtés ) 

## Typing
Pour le typeur, il a fallu adapter le TP correspondant. Notamment j'ai rajouter 2 champs au type environnement pour pouvoir
ajouter non seulement des identifiants mais aussi savoir s'ils sont mutable ou s'ils désigne non pas une variable ou fonction mais
un type (notamment introduit par les fonctions entre chevrons).
L'unification de type aussi a été d'une difficulté conséquente : je n'en suis pas encore 100% sûr même si ça passe tous ls tests
Par exemple il fallait faire une fonction is_subtype qui ne tente pas de faire l'unification, afin de ne pas changer les vrariables
si jamais on était sur la mauvaise voie ( pour l'addition surtout, pour savoir si ce sont des nombres ou des string)
L'autre difficulté était la multitude de manière de gérer les types paramétrés pour les fonctions, il m'a notamment fallu réintroduire
après coup un type identifiant général TIdent au lieu de systématiquement les remplacer par des types primitifs ou des variables, 
cependant le type de la fonctions faisaient introduire les variables (Tvar) généralisée que ce soit un l'intérieur du block ( possibilié 
d'un appel récursif qui change le type ) ou après sa définition (ça c'est normal).


## Production de code
Il y a globalement deux fichiers pour la production de code ( en plus de x86_64.ml ) : compile.ml et builtin.ml
builtin.ml traite en quelque sorte ce qui est global les fontcions internes au langage, alors que compile.ml se concentre sur la compilation des expressions génériques.
- strings en octets au lieu de 64bits pour pouvoir l'afficher directement avec printf
- Des précautions ont été prises pour éviter toute collision de label ( entre les fonctions définies par l'utilisateur, les labels internes au compilateur et les fonctions de la bibliothèque C ), le caractère '.' à été choisi comme caractère spécial.
- Un soin particulier à aussi été donné au fait de suivre les conventions callee saved / caller saved afin d'éviter les erreurs, de plus c'est à une échelle plus stricte parce que ce n'est pas seulement les appels de fonctions qui préservent les registres callee saved, mais en fait tout block de code associé à une certaine expression à compiler.
- usage particulier de rbx : il est ici exclusivement utilisé pour pointer vers le début de la fermture/ l'environnement de la fonctions, donc : 
Tout comme rbp+x permet d'accéder aux variables locales et aux arguments, rbx+x permet d'accéder aux variables de la fermeture.
Et, tout comme rbp, une case mémoire sur la pile est réservée à sauvegarder rbx ( donc la première case libre pour une variable locale est décalé de var_size )
- On pourra remarquer l'ajout d'opérateurs (+++) et (++-) permettant de généraliser (++) mais en plus de combiner le code assembleur courant, en parallèle il collecte le code des fonctions qui seront ajoutés à la fin du code : (code_fun1, code_main1) +++ (code_fun2, code_main2) = (code_fun1 ++ code_fun2, code_main1++ code_main2). Cela permet de grandement simplifier/alléger le code. 
- Toutes les fonctions du langages, mise à part fold, sont globale et préalloués au départ ( exactement comme empty et nothing, car les fonctions sont un peu des valeurs comme les autres ). La fonction fold au contraire, n'a pas été codée en assembleur mais ajoutée au moment de la compilation ( dans compile.ml la dans la fonction compile_program ) au début du code à compiler. 
- L'ordre des arguments des fonctions est à l'envers par rapport à celui proposé par le sujet, cela permet notamment d'évaluer les arguments de gauche à droite simplement (donc f(print("a"), print("b")) affiche bien "ab" et non "ba" )

- Pour avoir des fermetures qui fonctionnent par références, il a fallu que je change à postériori l'encodage des variable pour que les blocs d'un certain type fassent toujours la même taille (donc les chaines de caractère et environnements de fonctions doivent être des pointeurs, ce qui n'était pas mon choix initial ) pour pouvoir copier un bloc dans un autre au lieu de faire pointer le pointeur vers le nouveau bloc ( ce qui a pour effet que quand on copie le pointeur, on obtient pas une référence car une modification de la valeur fera changer la case pointée mais donc uniqueent de notre instance de la variable ). 
- Cependant, cela fait apparaitre un autre problème : les arguments de fonctions eux au contraire, il faut les copier, donc il faut créer une nouvelle variable et y copier les arguments qu'on veut placer. 
- Remarque : tout cela créer pas mal de nouvelles allocation de mémoires avec malloc (au moins une pour chaque arguement donné à chaque appel de fontcion ) ce qui n'en fait pas la version la plus efficace. Mais j'en profite pour préciser que l'accent a été plus souvetn mis sur la correction et la simplicité du cide que sur l'efficacité. Par ailleur, il semblerait que le fait que les fermetures accèdent aux variables par références et non par copie n'est pas testé, donc je sais pas si cela était attendu.



## Usage :
Il est possible de faire comme demandé dans le sujet un simple
`make`
pour obtenir un fichier ./pyretc.exe qui peux prendre les options "--parse-only" ou "--type-only" ainsi que le fichier .arr
De plus il est possible d'exécuter les tests de parsing avec :
`make test_parsing`
ceux de typage avec :
`make test_typing`
et ceux d'exécution avec :
`make test_exec`
Enfin il est possible de nettoyer avec
`make clean`
/* -*- Prolog -*- */
/* -*- coding: utf-8 -*- */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% ktp-koligacje-rodzinne.pro (kkr.pro)
% data zapoczątkowania: 2018-05-03
%
% kolejna próba podejścia do 'drzewa genealogicznego'
%
%   m(X) - mężczyzna - to definiujemy
%   k(X) - kobieta   - to definiujemy
%   małżonek (X,Y) - to definiujemy - obojętnie, w którą stronę zapisane
%      czy małżonek('Asia SK', 'Tadeusz K'), czy małżonek('Tadeusz K','Asia SK')
%      za to w pochodnej relacji 'małżeństwo/2'
%      jest już ustalona kolejność: 'małżeństwo(<mąż>,<żona>)'
%
%   rodzic (X,Y) === X jest rodzicem Y - to definiujemy
%      tu oczywiście kolejność JEST istotna: 'rodzic(<rodzic>,<dziecko>)'
%      np: rodzic (X,teo) === kto jest rodzicem teo?
%
%   i.... tyle definicji dotyczących logiki bazy
%   na razie nie ma nic o datach urodzin/zgonów/ślubów/rozwodów itd
%   np kto raz miał ślub, teraz baza zawsze traktuje jak małżonek
%   dlatego wg bazy ktoś  może mieć kilku małżonków
%
%   np te relacje to już wnioskujemy z relacji 'rodzic':
%   dziecko(X,Y) === X jest dzieckiem Y  - pochodne od rodzica
%
%   małżeństwo(X,Y) - a to wnioskujemy z 'małżonek(X,Y);małżonek(Y,X)'
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%   dla przypomnienia podstaw prologu:
%    , spójnik 'and'
%    ; spójnik 'or'
%    . koniec klauzuli
%    =:= porównanie liczb 'czy równe'
%    =\= porównanie liczb 'czy nierówne'
%    <, > porównanie liczb 'mniejsze' 'większe'
%    =<, >= porównanie liczb 'nie większe' 'nie mniejsze'
%    \+ operator 'negacji'
%    ! operator 'odcięcia'
%    a,b,c,... - ogólnie identyfikatory pisane z małej litery
%                to stałe/dane - prolog przyjmuje to jako 'fakty'
%    X,Y,Z,... - ogólnie identyfikatory pisane z Wielkiej litery
%                to zmienne - prolog będzie je obliczać na podstawie
%                znanych faktów i relacji
%
%   tekst:
%      'rodzic/2' oznacza, że relacja/reguła 'rodzic' ma 2 argumenty
%      jest np: 'm/1', 'k/1'
%      niektóre reguły mają kilka wersji o różnej liczbie arg.
%      np: 
%
%
%   listing. === wypisuje wszystkie znane fakty i relacje
%   listing(relacja). === wypisuje definicję tej relacji
%
% UWAGI:
% jak zdefiniowałem kogoś w relacjach ojciec/matka,
% ale zapomniałem w m/k, to przy pytaniach np o dziadków
% (tam, gdzie jest sprawdzenie płci) system NIE widział
% tej osoby....
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% przypomnienie dot.wypisywania komunikatów w kolorze:
%     ansi_format(+Attributes, +Format, +Args) 
%
% zarówno Attributes i Args to listy!
%
% some commonly used attributes are: 
%     fg(Color), bg(Color), hfg(Color), hbg(Color), bold, underline,
%
% Defined color constants are below - default can be used to access
% the default color of the terminal:
%       black, red, green, yellow, blue, magenta, cyan, white
%
% Kolor - np: [bold,fg(cyan)]. The defined names are given below. 
% Note that most terminals only implement this partially:
%   reset   - all attributes off, -Off - Switch (individual) attributes off,
%   blink(slow),blink(rapid), underline(double), intensity(normal),
%   font(primary),  font(N), Alternate font (1..8),
%   fg(Name) -> Color name, bg(Name) -> Color name,
%   hfg(Name)-> Color name, hbg(Name)-> Color name,
%   ideogram(underline), ideogram(underline(double)), 
%   ideogram(overlined), ideogram(stress_marking),
%   true/false: 
%   bold,   faint,  italic, underline,  negative,   conceal,
%   crossed_out,fraktur, framed, encircled, overlined, 
%   right_side_line, right_side_line(double), left_side_line
%



%=======================================================================
%
% C) 'koligacje rodzinne' - flagi, fakty, zmienne, reguły 
%    nie dotyczące bezpośrednio osób ani powiącań między osobami
%
%    tutaj rzeczy dotyczące przeglądania, modyfikacji, wyświetlania 
%    list/reguł/faktów
%


%=======================================================================
%
% C1) wartości początkowe używanych flag/zmiennych
%


%%%%%%%%
%
% flagi systemowe
%

:- style_check(+singleton).
:- style_check(+discontiguous).

:- set_prolog_flag(encoding, utf8).
:- set_prolog_flag(color_term, true).
:- set_prolog_flag(back_quotes,codes).
:- set_prolog_flag(double_quotes,string).
:- set_prolog_flag(verbose_load, silent).
:- set_prolog_flag(print_write_options,
                   [portray(true), quoted(true), numbervars(true)]).
:- set_prolog_stack(global,limit(1*10**8)).


% flaga 'double_quotes' = 'string' / 'atom'
% jest wymagana dla prawidłowego działalnia 
% 'string_concat_many(ListOfStrings,StringResult)'
% wtedy łączone stringi mogą być zarówno w '', jak i ""
% dla wartości 'double_quotes' = 'codes' / 'chars' 
% wszystkie łączone stringi muszą być podane w ''
% dla strinów "" pojawiają się błędy (dużo błędów)


%%%%%%%%
%
% importy systemowe
%

:- use_module(library(check)).
:- use_module(library(apply)).
:- use_module(library(sort)). 
:- use_module(library(yall)).

% z 'yall' biorę sortowanie z 'localsami', uwaga:
% 'locale_sort/2', w przeciwieństwie do 'sort/2' 
% nie usuwa duplikatów z list, zresztą 'locale_sort' 
% działa tylko na 'atomach' lub 'stringach', czyli np 
% NIE radzi sobie z zagnieżdżonymi listami - np par małżonków, 
% rodzic / dziecko itp
% do 'locale-sort' takich rzeczy zrobiłem własne 'localeSortAll'


%%%%%%%%
%
% flagi moje
% flaga 'flgTesty' i powiązany atom 'testy'...


:- set_flag(flgTesty, false ). 
:- set_flag(flgKom, true).

% tutaj ustawiamy tryb 'verbose'(true) lub 'silent' (false)
% można też w konsoli przejść między trybami, wpisując:
%     set_flag(flgKom, true / false).


% bez parametrów - wersje zwracające stan flag
testy   :- get_flag(flgTesty, true). % patrz też ver z param w 'regułach pomocniczych'
piszKom :- get_flag(flgKom, true).

% zmienia stan samej flagi - nie wstawia, ani nie kasuje
% 'danych testowych' - to robią: testy(true) i testy(false)
testFlagOff :- set_flag(flgTesty,false).
testFlagOFF :- testFlagOff.
testFlagOn  :- set_flag(flgTesty,true).
testFlagON  :- testFlagOn.



%%%%%%%%
%
% stałe moje
%

%
% stałe wykorzystywane m.in. do określenia, jak wypisać komunikaty
% 'jestOK' -> znaczy się dobrze -> zielone na niebieski
% 'nieOK'  -> znaczy się coś źle-> czerwone na żółtym
%


jestOK :-true.
nieOK :-false.
maxArność(3). % max liczba argumentów, jaką mają użyteczne reguły

%
% prolog 'sam z siebie' definiuje 'nl', które wstawione w regułę
% wypisuje na <stdout> znak '\n' - brakowało mi 'spc','przec'...
% no i są poniżej:
%

spc   :- put(' ').  % def taka, jak wbudowana 'nl' - ale wypisuje ' '
przec :- put(',').
średn :- put(';').
tab   :- put('\t'). %jak wyżej - są tab/1, tab/2, ale tab/0 chyba wolne.
beep  :- put('\a').


% 'nasz' 'help' - powinien  też pojawić się po załadowaniu pliku

run   :- helpme.
go    :- helpme.
pomoc :- helpme.
pomocy:- helpme.

/*
 clear_screen - patrz pytanie i odpowiedzi:
https://stackoverflow.com/
        /questions/16908764/clearing-screen-in-swipl-prolog-in-windows
*/

clear_screen :- true/*write('\e[H\e[2J\n')*/.

kolorStringNorm(  [      fg(black),  hbg(white) ]).
kolorStringBold1( [bold, fg(magenta),hbg(white) ]).
kolorStringBold2( [bold, fg(blue),   hbg(white) ]).
kolorStringJestOK([bold, fg(blue),   hbg(green) ]).
kolorStringNieOK( [bold,hfg(red),    hbg(yellow)]).


%
% stałe/zmienne  pomocnicze  dla reguły: 'piszListElemWTabeli'
% UWAGA! nie mogę na listach 'justify..' dać wpisów: L,Left,LEFT,R,Right,RIGHT
% bo prolog traktuje je jako zmienne (zaczynają się z wielkiej litery
% i podczas sprawdzania daje to dziwne efekty...
% z kolei, gdy są w '' lub "", to prolog zwraca true np dla testu:
% listElem('f',JustLTVar), lub listElem('g',JustRTVar),
% bo 'f' i 'g' są elementami  ciągów  'Left'/'Right'
% także niech userowi wystarczy jednoliterowe podawanie justyfikacji 
%

justifyLeftTag([ 'l',"l",'L',"L"]).
justifyRightTag(['r',"r",'R',"R"]).
justifyCenterTag(['c',"c",'C',"C"]).

separatorPreferredChars([' ','\t','\n',',',';','|'," ","\t","\n",",",";","|"]).



%
% tutaj coś jakby 'deklaracja' poprzedzająca wywołanie,
% przed którym nie ma jeszcze definicji  (definicje są na końcu pliku)
%

:- discontiguous m/1, k/1, regPom/1, rodzic/2, małżonek/2, daneTestowe/1.

% poniższe fakty mogą ulec zmianie przez dodawanie nowych (assertz)
% lub usuwanie jakichś (retract/retractall)
:- dynamic
       m/1,
       k/1,
       rodzic/2,
       małżonek/2,
       daneTestowe/1.



% chcemy by po załadowaniu pliku, help wyświetlił się automatycznie
% tyle,  że PO nim wyświetla się jeszcze 'help' SWI 
% pewnie można to wyłączyć w jakimś pliku ini/rc itp 

% powitaj się i krótko przedstaw na dzień dobrry
% wywołanie testy(testy) głupio wygląda, ale ma sens...
% 'testy' zwraca początkowy stan flagi flgTest ustawiony
% gdzieś tam wyżej w tym pliku jako właściwy przy  starcie programu
% testy(...) ustawia ją na 'to samo' ALE przy okazji
% modyfikuję bazę faktów/reguł - dodaje/usuwa dane testowe

startuj:-helpme,(testuj(testy);true).
%startuj:-helpme.

:- initialization(startuj).


%
% POWYŻEJ COŚ JAKBY 'PUNKT WEJŚCIA' DO PROGRAMU
% CZYLI REGUŁA STRATUJĄCA AUTOMATYCZNIE
% PO ZAŁADOWANIU TEGO PLIKU
%



%=======================================================================
%
% C2) reguły pomocnicze
%


%
% definiuję swój logiczny exor (exclusive-or, prawnicze: 'albo'
% potrzebuję, a nie widzę na liście predef.
% priorytet i wiązanie takie, jak 'or' (czyli '|' ';')
%

:- op(1100, xfy, [exor,albo]). 
exor(X,Y) :- (((X),(\+(Y)))|((Y),(\+(X)))).
albo(X,Y) :- exor(X,Y).


%
% wersja 'testuj' z parametrami:
% gdy parametr jest 'zmienną niezwiązaną' -> zwróć w nim stan flagi
% gdy parametr ma jakąś wartość logiczną -> ustaw flagę wg tej wartości
%
% tzn miało tak być... ale za mało jeszcze chwytam, jak to działa....
% także do 'czytania' są wersje bez parametrów - czyli: testy, piszKom,...
% a wersje z parametrem mają służyć tylko do ustawiania flag - o!
%

testuj(X) :- ((X) ->  % 'X' można zrozumieć jako 'true' -> ustaw flagę na 'true'
    (forall(daneTestowe(DT),assertz(DT)), %gdy testy ustawiamy na 'true'
                               % wprowadzamy do bazy kilka dodatkowych faktów...
      style_check(+discontiguous),
      style_check(+singleton),
      set_flag(flgTesty,true),!,true
    )  % koniec  'then' od '(X) ->'
   ;
   (forall(daneTestowe(DT),retractall(DT)), % ustawiasz testy na 'false'?
      % to posprzątaj dane testowe... btw... ma być forall _i_ retractall
      % czyli 'dla all danych testowych wyczyść all wpisy każdej z nich'
      % chodzi o to, że jeśli kilka razy wywołano testy(true),
      % to za każdym razem wstawia nowy komplet danych testowych..
      % EDIT: można poprawićc na: forall((daneTestowe(DT),\+DT),assertz(DT))
      % i nie wstawi koljnego kompletu, ale ZOSTAWIAM wielokrotne wstawianie
      % to może być przydatne w testach... 
      % jeśli chce się mieć pewność, że będzie 'jeden' komplet danych testowych,
      % można zrobić: testy(false),testy(true).
      % ustawienie na false usunie _wszystkie_ dane testowe,
      % a pojedyncze ustawienie na true wstawi do bazy _jeden_ ich komplet
      style_check(-discontiguous),
      style_check(-singleton),
      set_flag(flgTesty,false),!,false
   ) % koniec 'else' od '(X) ->'
). % koniec 'testuj(X) ->'

% UWAGA!!! TRICK!!! UWAGA!!! 
% można ustawić 'testy' na false, NIE usuwając z bazy danych testowych..
% trzeba: wstawić dane testowe przez: testy(true). (tyle kompletów ile chcemy)
% potem: set_flag(flgTesty,false) -> ustawimy 'ręcznie' flagę na 'false'
% ale bez wywoływania naszej procedury ustawiania - czyli bez usuwania
% danych testowych...
% podobnie można dać testy na true, nie wstawiając danych:
% trzeba dać: testy(false) i set_flag(flgTesty,true). 


%
%  wersja piszKom(_) z parametrem - do ustawiania flagi 'flgKom'
%

piszKom(X) :- ((X) -> % 'X' można zrozumieć jako 'true' -> 
                      % ustaw flagę na 'true'
      (set_flag(flgKom,true)); 
      (set_flag(flgKom,false),false)
). % koniec głónego pytania i reguły testy(X)




% 'term_string_clever' - przed zamianą termu na string sprawdza,
% czy przypadkiem term już nie jest stringiem...
% jest -> zwraca niezmieniony term
% nie jest -> używa systemowego 'term_string' to zamiany
% chodzi o to, że ten systemowy, jak dostanie  string na wejście,
% to głupieje... i np z S=' ' robi S="' '"
% być może zależy to od flagi 'double_quotes'...
% w każdym razie dzieje się tak, dla wartości 'double_quotes',
% których wymagają inne używane formuły ('string' lub 'atom')
% w każdym razie nie chcę takiego 'dodawania'
% oczywiście przy wywołaniu StrWy 

term_string_clever(We, StrWy) :-
   (string(We)->StrWy=We;swritef(StrWy,'%t',[We])).

%
% komunikat powitalny
%

helpme :- ((\+ piszKom) ->
    % gdy pisanie komunikatów jest wyłączone (piszKom = false),
    % wypisz (bez kolorów) tylko krótkie info jak to włączyć
    % i NIE pisz dalszej części helpa powitalnego
    ( writeln("Chcesz zobaczyć 'helpa'? Ustaw flagę 'flgKom' - np tak:"),
      writeln("\tset_flag(flgKom, true)., lub: piszKom(true)."),
      writeln("i ponownie wpisz: helpme.\n"),
    false); % koniec części 'then' pytania (\+ piszKom)
	 % skoro 'nie piszKom', to zwróć false - ponieważ ta formuła/pytanie
	 % jest w ciągu ,,,, (czyli jest jednym z elementów logicznego AND)
	 % to po zwróceniu teog false następne człony NIE zostaną wykonane
	 % czyli nie wykona się żaden następny writef/ansi_format/...
    (true) % gdy 'piszKom', to zwróć true -> następne człony AND będą wykonane
	   % (do ewentualnego napotkania jakiegoś false oczywiście ;)
    ), % koniec pytania (\+ piszKom)
    ((\+ testy) ->
	 % faza 'normalna' (nie testy) -> możesz wyczyścić ekran
      (clear_screen;true) % koniec części 'then' pytania (\+ testy)
      ;
        % gdy faza testów, NIE czyść ekranu - 'uciekają' errors/warnings
      (true)
    ), % koniec pytania (\+ testy) - w obu przypadkach zwracamy 'true',
       % bo _w_obu_ chcemy, by dalsze człony AND się wykonywały -> wypisały helpme
	
    % ok, tu już wiemy, że helpme ma być wypisany
    % wykorzystajmy podefiniowane zestawy kolorów

    kolorStringNorm(_KolNorm), % '_' żeby wyłączyć warning 'singleton variable'
    kolorStringBold1(KolBold1), kolorStringBold2(KolBold2),

    writef('\t%r\n\n',['-<*>-', 12]),
    tab, tab, tab, tab,
    ansi_format(KolBold1,"W i t a j !\n\n",[]),
    writeln("\tw bazie o koligacjach rodzinnych Sob... i Ku..."),
    write('\tNa razie baza dysponuje danymi o '),
        findall(X1,m(X1),L1),listLen(L1,N1), write(N1),write(' panach i '),
        findall(X2,k(X2),L2),listLen(L2,N2),write(N2), writeln(' paniach,'),
    write('\ta także o '),
        findall([X3,Y3], małżeństwo(X3,Y3),L3),listLen(L3,N3), write(N3), 
    write(' małżeństwach i '),
        findall([X4,Y4],rodzic(X4,Y4),L4),listLen(L4,N4),
        write(N4),writeln(' parach rodzic/dziecko.\n'),
    writeln(
        "\tZnane bazie panie/panów/wszystkich możesz poznać wydając komendy:"),
    tab,tab,
    ansi_format(KolBold2,
        "panie. panowie. osoby.  (kropka na końcu komendy!),\n",[]),
    writeln(
        "\tNatomiast małżeństwa i rodziny - poprzez komendy:"),
    tab,tab,
    ansi_format(KolBold2,
        "małżeństwa.   rodziny.  (tak, kropka na końcu komendy!),\n",[]),

    writeln(
        "\tTę 'ściągę' w każdej chwili możesz wyświetlić wpisując któreś z:"),
    tab,tab,
    ansi_format(KolBold2,
        "go. helpme. pomoc. pomocy. run. (pamiętaj o kropce!),\n",[]),

    writeln(
        "\tA listę dostępnych komend zobaczysz wpisując:"),
    tab,tab,
    ansi_format(KolBold2,
        "piszReguły. lub piszReguły(N). gdzie N = 0..3 (kropka!).\n",[]),!.
    
    
/*
    TO DO:

    wypisać info o możliwych do poznania cechach pojedynczych osób 
         i dwu i 3 elem relacji
    oraz o relacjach, jakie zachodzą między osobami - 
         w tych relacjach zamienić listę na zbiór (bez powtórzeń),
    a z list dostępnych relacji usunąć te 'pomocnicze' - 
    dodać klauzle  regPom()
*/


%
% zwraca 'true', gdy 'Elem' należy do listy, 'false' w przeciwnym wypadku
%

listElem(Elem,[G|_   ]) :- G=Elem,!.
listElem(Elem,[_|Ogon]) :- listElem(Elem,Ogon).


%
% weź element 'X', listę 'L', dodaj jedno do drugiego i zwróć jako 3. param.
%

listDodaj(X,L,[X|L]).


%
% dodaj gdy jescze nie ma - chyba teraz działa
%

listDodajGdyBrak(Elem,LWe,LWy) :-   % LWe ma być listą lub zmienną niezwiązaną
    (((var(LWe),!); is_list(LWe)),   % LWy ma być zmien.niezwiąz.lub []
     ((var(LWy),!);(is_list(LWy), listLen(LWy,0))), 
     
    (((listElem(Elem,LWe), LWy=LWe),!); % Elem jest w LWe -> zwracamy LWe
    LWy=[Elem|LWe])                    % nie było -> dopisujemy, zwracamy całość
). % koniec formuły 'listDodajGdyBrak'


%
% formuła mająca 'podwójne działalnie' - albo 'oblicza' dł listy
% (gdy 'Lenght' jest 'zmienną niezwiązaną'
% albo 'sprawdza', czy podana w 'Length' wartość
% jest zgodna z rzeczywistą długością listy
% dodatkowo przeprowadza testy poprawności typów parametrów
%

listLen(List, Length) :-           %  sprawdz. i oblicz.dł 'Listy' z testami: 
   ((var(Length) ->                % gdy 'Length' jest 'zmienną nieprzypisaną', 
       listLen(List, 0, Length),!) %   wołamy formułę listLen(_._._)
                                   %   (tylko) obliczającej długość 'Listy'
                                   %   (start długości od 0) i zwracamy tę
                                   %   dł w przekazanym  parametrze 'Length'

   ;                            % druga część - gdy 'Length' jest 'związana'
   number(Length),              % sprawdzamy, czy jest liczbą i czy nieujemną
       Length >= 0,             % (nie jest -> zwracamy false) 
   listLen1(List, Length)       % wołamy funkcję 'listLen1' _sprawdzającą_ 
). % koniec formuły 'listLen(_, _)  % czy 'Length' zgadza się z rzeczywistą


%
% a tu już 'po prostu' obliczanie dł.Listy - bez sprawdzeń typów itd
% w środkowym parametrze przekazujemy 'ile ma wynosić 'Length' listy pustej
% (normalnie 0 - coś jakby wart.pocz.), a w ostatnim - otrzymamy długość
% obliczoną (z uwzgl. podanej na środku 'wart.początkowej'
%

listLen([], Length, Length).   % 1. część definicji rekurencyjnej
listLen([_|L], N, Length) :- (
        N1 is N+1,
        listLen(L, N1, Length)
). % koniec formuły 'listLen(_,_,_) tzn 2. części jej definicji rekurencyjnej

%
% a tutaj _sprawdzenie_ czy podana wartość 'Length' zgadza się z rzeczywistą
%

listLen1([], 0) :- !.          % 1. część definicji rekurencyjnej
listLen1([_|L], Length) :- (
        N1 is Length-1,
        listLen1(L, N1)
). % koniec formuły 'listLen1(_,_) tzn 2. części jej definicji rekurencyjnej


%
% listLiczElemN(E,L,N) - zwraca N - ile razy element E występuje na liście L
% na razie to rozwiązanie ściągnięte z:
% https://www.tek-tips.com/viewthread.cfm?qid=1604418
% przerobić je na takie jak listLen wyżej - że po pierwsze sprawdza typy,
% po drugie, gdy 'N' 'nie przypisane' to liczy, a gdy 'N' jest jakąś liczbą,
% to sprawdza,  czy rzeczywiście dany elem tyle razy występuje na liście...
%

listLiczElemN(_,[],0).                      % w pustej liście jest 0 elem :)

listLiczElemN(G, [G | Ogon], N) :-  % gdy badany elem pokrywa się z
  !, listLiczElemN(G, Ogon, N1),        % głową listy, policz ile x występuje
  N is N1 + 1.                              % w ogonie i dodaj 1
                                            % i zwróc to 1 'wyżej'

listLiczElemN(G, [_ | Ogon], N) :- % gdy badany elem NIE pokrywa się z głową,
  listLiczElemN(G, Ogon, N).       % z głową, zbadaj ogon i zwróć 'wyżej'
                                       % bez zmian N - ilość wystąpień w ogonie

listStrElMaxDl([],_,0). % pusta lista nie ma elementu do zwrócenia 
                              % może tylko '0' - żeby chociaż 'coś' - daję '[]'


%
% przegląda listę 'L', zwraca najdłuższy znaleziony element i jego długość
% jeśli kilka elementów ma tę samą 'największą' długość, zwraca pierwszy z nich
% 'długość elementu' oznacza długość tekstu, na jaki możemy zamienić ten elem.
% przy wywołaniu El i StrElLen muszą być 'nieprzypisane'
%

listStrElMaxDl(L,El,StrElLen):- (
   ((\+var(El),\+var(StrElLen)) -> (% chociaż jedna jest przypisana?->uciekamy
      piszTestInfo(false,'liStElMaxD',
         "'El/STrElLen' powinny być nieprzypisane, pa pa...")
      ) % koniec 'then' '(\+var(El),\+var(StrElLen))->'
      ;
      ( % tu wiemy, że El, StrElLen są 'niezwiązane' - można działać
         L=[G|T], listStrElMaxDl(T,El1,StrEl1Len),
         term_string_clever(G,StrG),
         string_length(StrG,StrGLen),
         ((StrGLen > StrEl1Len) -> ( % znaleziono nowy dłuższy element
             % 'wyżej' puszczamy jego dane,  zamiast tych 'z dołu'
             El=G, 
             StrElLen is StrGLen,
             true
            ) % koniec 'then' od  '(StrGLen > StrEl1Len)->'
            ;
            ( % bieżący elem nie jest lepszy od tego 'z dołu'
               % 'w górę' przepuszczamy ten 'z dołu'
               El=El1,
               StrElLen is StrEl1Len,
               true
            ) % koniec 'else' od  '(StrGlen > StrEl1Len)->'
         ) % koniec '(StrGlen > StrEl1Len)->'
      ) % koniec 'else' '(\+var(El),\+var(StrElLen))->'
   ) % koniec '(\+var(El),\+var(StrElLen))->'
). % koniec 'listStrElMaxDl'


%
% listCzyNiePusta (L) - sprawdza, czy przekazany param 'L' jest niepustą listą
% zwraca:
% true - gdy 'L' to lista niepusta,
% false - w pozostałych przypadkach,
%
% wersja listCzyNiePusta (L, Wyn) - jak wersja /1, oprócz zwrcania wyniku testu
% w parametrze 'Wyn' (jak wynik) zwraca:
%  długość listy - dla 'nie pustej',
%  <nul> (zostawia nieprzypisaną) - w pozostałych przypadkach
%

listCzyNiePusta(L, Wyn) :- (
%    piszTestInfo(true,'lCzyNiePus','w środku'),

    (var(L)->(piszTestInfo(false,'lCzyNiePus',
        "'L' to zmienna nieprzypisana, pa pa...")
        )
        ;
        (true)  % 'L' nie jest nieprzypisaną zmienną->sprawdzamy dalej
    ), % powyżej test, czy chcieli nam wcisnąć 'nieprzypisaną' zmienną

    (is_list(L)->(true) % 'L' to lista! ale możliwe, że pusta - idziemy dalej
              ;
              (piszTestInfo(false,'lCzyNiePus',"'L' to nie-lista, pa pa..."))
    ),  % powyżej chcieli nam wcisnąć 'nie listę'

%    piszTestInfo(true,'lCzyNiePus','po nie-liście'),
    listLen(L,NL),
    ((NL=:=0) ->
         (piszTestInfo(false,'lCzyNiePus',"'L' to lista, ale pusta, pa pa..."))
         ;
         (true) % 'L' jest lista i nie pusta, idziemy dalej
    ), 

    % ok, tu już wiemy, że L jest listą i to niepustą...
    Wyn is NL,
    piszTestInfo(true,'lCzyNiePus',"'L' to lista i niepusta - hurra!")
). % koniec 'listCzyNiePusta'


listCzyNiePusta(L) :- listCzyNiePusta(L,_).


/*
   listReorganizuj(L, Kol, LWy) 
   funkcja pomocnicza dla 'piszListWTabeli' i uzupełniająca do 'piszListElWKol'

   'piszListWTabeli' przewiduje wypisywanie list 'w wierszach' i 'w kolumnach'
   zał: L ma elementy e1,e2,e3,e4,e5,e6,e7,e8...........eN
   wypisujemy tę 'L' w układzie tabelarycznym - przeznaczając na każdy element pewną ilość znaków
   przez wypisywanie 'w wierszach' rozumiemy wypisywanie w układzie: (zał: 3 wiersze po 5 kolumn)

                e1,   e2,  e3,  e4,  e5
                e6,   e7,  e8,  e9, e10
                e11, e12, e13, e14, e15

   natomiast przez wypisywanie 'w kolumnach' rozumimy wypisanie  w układzie: (zał jak wyżej)

                e1,   e4,  e7, e10, e13
                e2,   e5,  e8, e11, e14
                e3,   e6,  e9, e12, e15

   funkcja 'piszListElWKol' wywoływana z 'piszListWTabeli' zajmuje się wypisywaniem kolejnych
   elementów otrzymanej listy 'w wierszach' w zadanej ilości kolumn o zadanej szerokości,
   po wypisaniu elementu o Nr =IlKol, następuje wypisanie '\n' i rozpoczęcie ok Kol1 w nast.linii

   czyli, żeby uzyskać tabelę wypisaną 'w kolumnach' trzeba przekazać do 'piszListElWKol'
   elementy pierwotnej listy 'L' uporządkowane w kolejności: 

                e1, e4, e7, e10, e13, e2, e5, e8, e11, e14,... , e9, 12, e15

   czyli wg reguły:     for w in NRW: 
                            for k in NRK: 
                                ELEM = getNthEl( L[ nr = ((k-1)*IW+w) ] ), 
                                pisz(ELEM do LWy) ;; dopisuj na końcu LWy

                                (ewentualnie można dopisywać na początku LWy, a potem 'odwrócić')

   gdzie: NRW=1 .. IlWierszy, NRK=1 .. IlKol, nr=1 .. IlWierszy*IlKol

       przy czym jesteśmy w stanie zapewnić, żeby L (wejściowa) miała IlWierszy * IlKol elementów
       żeby nie było problemów typu 'out of range'
       zresztą z tego wynika, że do tej funkcji wystarczy przekazać ilość kolumn i listę 
       odpowiedniej długości - ilość wierszy będzie oczywista...

   ta funkcja - 'listReorganizuj(L, Kol, LWy)' ma zrobić taką reorganizację

*/ 

%
% pomocnicze dla 'listReorganizuj' - przelicza wsp.[W,K], na index z 'LWe'
%

listReorgIndx(IlW, W, K, Indx) :-  (Indx is ((K-1)*IlW + W)).
listReorgIndx(IlW, [A,B|_], Indx) :- listReorgIndx(IlW,A,B,Indx).

listReorganizuj(LWe,Kol,LWy) :- (
   listLen(LWe,N),
   IlKol is Kol,
   IlWierszy is  (N // IlKol),

   findall([W,K],(between(1,IlWierszy,W),between(1,IlKol,K)),LParIndx),
   % tutaj w 'LParIndx' mamy listę par [w,k] współrzędnych poszczególnych pól 
   % tablicy / tabeli, złożonej z IlWierszy * IlKol pól - z zał.to = Len(Lwe)
   % czyli zrobiłem w prologu tak jakby 2 pętle zagnieżdżone...
   % na razie to wstęp - mam indeksy pól tabeli o zadanej IlWierszy/IlKolumn

   % ok, teraz na podstawie tych par spróbuję wygenerować listę indeksów
   % służących do reorganizacji 'LWe' - patrz opis w komentarzu powyżej)

   maplist(listReorgIndx(IlWierszy),LParIndx,LIndx),
   % teraz w LIndx na kolejnych miejscach są indeksy - numery pól LWe,
   % z których trzeba pobierać wartości, żeby wstawiać je do LWy
   % np dla IlWierszy=3 i IlKol=5, LIndx powinna wyglądać tak:
   %    [1,4,7,10,13,2,5,8,11,14,3,6,9,12,15]

   (testy->writeq(LIndx);true),
   % btw... LIndx powinna mieć taką samą długość, jak LWe...

   % przypominam: N=Len(LWe)

   maplist({LWe}/[IndxWe,ElemWy]>>nth1(IndxWe,LWe,ElemWy), LIndx, LWy)
   % ku pamięci: to ma działać tak, że z listy LIndx pobieramy kolejne elementy,
   % które są indeksami mówiącymi, który element z listy LWe pobrać,
   % żeby wysłać go do LWy - czyli to ma robić tę podmianę o której mowa
   % w komentarzu wstępnym do 'listReorganizuj(L,Kol,LWy)'

). % koniec 'listReorganizuj(L, Kol,LWy)'


%
% listZnajdźDuplikaty(L,D) - szuka duplikatów (powtórzonych elem.) na liście L
% gdy L pusta -> zwraca D pustą i 'false' (nie ma duplikatów)
% gdy L nie ma duplikatów -> zwraca D pustą i 'false' (nie ma duplikatów)
% gdy L zawiera powtarzające się elem, zwraca D - 'listę list' postaci:
% [[e1,n1],[e2,n2],....] - tzn.listę par: [<wielokrotny elem>,<ilość wystąpień>]
%
% EDIT:
% dodano parametry S, A - gdy oba 'false' działa tak, jak dla dwóch, a z nimi:
%
%  A - 'all' - gdy 'true', zwraca 'D' w formacie takim, jak gdy są duplikaty,
%      ale z wszystkimi elementami 'A' - unikalne z <ilością wystąpień> =1.
%
%  S - 'sort' - czy sortować wynikową listę 'D'? (true/false)
%      sortuje z użyciem 'localeSortAll/2'
%
%  S,A NIE wpływają na wartość zwracaną przez f-cję - dalej gdy:
%          'są duplikaty'   -> zwraca 'true'
%          'brak dupikatów' -> zwraca 'false'
%
%  Gdy przy wywołaniu 'D' ma jakieś przypisanie (nie jest zm.wolną wg 'var(X)',
%  to f-cja zwróci odpowiednie false/true, ale nie zwróci 'D'...
%  (w prologu nie ma zmiany wartości parametrów - tylko gdy nieprzypisane)
%
%
% UWAGA!!!: sprawdziłem dla wymyślonej listy:
%    [1,[al,2],2,[be,3],1,[g,h,j],nic,drzewo,zamek,[be,3],1,4]
%  i dało PRAWIDŁOWY wynik: D = [[1, 3], [[be, 3], 2]].
% tzn: elem '1' jest powtórzony 3 razy, elem '[be,3]' jest powt.2 razy 
%


listZnajdźDuplikaty(L,D)   :- listZnajdźDuplikaty(L,D,false,false).
listZnajdźDuplikaty(L,D,A) :- listZnajdźDuplikaty(L,D,A,false).

listZnajdźDuplikaty(L,D, A, S):- (
   listCzyNiePusta(L,NL), % TO DO - SPRAWDZIĆ, z L =[]

   ((NL =:= 0) -> (
         D = [],    % jeśli nonvar(D), to się nie uda, ale to nic - i tak uciekamy
         piszTestInfo(false,'liZnajDupl',
            "'Lwe' jest pusta - zwracam 'false'")
            % 'piszTestInfo' od razu zwraca 'false' => ucieczka z funkcji
      ) % koniec 'then' od '(NL =:= 0) ->'
      ;
      (         % 'LWe' niepusta - potrzebne dalsze badania
         true   % => jedziemy dalej
      ) % koniec 'else' od '(NL =:= 0) ->'
   ), % koniec '(NL =:= 0) ->'

   % ok, tu już wiemy, że L jest listą i to niepustą...
   piszTestInfo(true,'liZnajDupl',"'Lwe' to lista i niepusta"),

   % sprawdzamy, czy 'LWe' zawiera dupliaty

   sort(L,SL),   % listę 'L' sortujemy i usuwamy duplikaty (patrz opis 'sort')
   % UWAGA!!! tutaj MUSI BYĆ 'sort/2' - NIE MOŻE być 'locale_sort/2'
   % tutaj tak naprawdę NIE chodzi o posortowanie, a o to, że 'sort/2'
   % usuwa duplikaty... -  jest też funkcja list_to_set (tylko usuwa duplikaty)
   % ale wg dokumentacji 'sort' jest wydajniejsza/szybsza....

   listLen(SL,NSL), % wyznaczamy długość  'SL' (dł.'L' - 'NL' już mamy

   ((NL =:= NSL) -> ( % obie listy tej samej długości -> nie ma duplikatów
          SąDuplikaty = false,
          % komunikat o stanie duplikatów - wypiszemy później
          StrDuplKom = "'Lwe' nie zawiera duplikatów => zwracam 'false'"
      ) % koniec 'then' od '(NL =:= NSL) -> (nie było duplikatów)
      ;
      (
          SąDuplikaty = true,
          % komunikat o stanie duplikatów - wypiszemy później
          StrDuplKom = "'Lwe' zawiera duplikaty => zwracam 'true'"
%          piszTestInfo(true,'liZnajDupl',"'L' zawiera duplikaty")
      ) % różne dł list 'L' i 'SL' -> są duplikaty
   ), % koniec '(NL =:= NSL) ->'

   % tu już wiemy co f-cja ma zwrócić jako 'kod powrotu' 
   % przechowujemy ten stan w 'SąDuplikaty' i info o tym w 'StrDuplKom'
   % 
   % jescze kwestia określenia, jaką listę 'D' zwrócić i czy jakiś komunikat

   ((nonvar(D)) -> ( %
         D = [],
         piszTestInfo(true,'liZnajDupl',
            "'D' związana (nonvar) - nie mogę jej modyfikować,"),

         ((SąDuplikaty) -> (
               % pisz komunikat i zwróć 'true'
               piszTestInfo(true,'liZnajDupl',StrDuplKom)
            ) % koniec 'then' od '(SąDuplikaty) ->'
            ;
            (
               % pisz komunikat i zwróć 'false'
               piszTestInfo(false,'liZnajDupl',StrDuplKom)
            ) % koniec 'else' od '(SąDuplikaty) ->'
         ) % koniec '(SąDuplikaty) ->'
      ) % koniec 'then' od '(nonvar(D))->'
      ;
      ( % tutaj mamy już obsłużone 'przypadki ogólne/masowe':
        % a)  gdy 'Lwe' puste - zwracaliśmy 'false'+komunikat i 'D=[]'
        % b)  'Lwe' nie puste, ale 'nonvar(D)' - zwracamy stan 'SąDuplikaty'
        %     komunikat 'nonvar(D)' i D=[] (tak naprawdę D bez zmian)

        % czas na prawdziwą zabawę - TU GŁÓWNA CZĘŚĆ 'listZnajdźDuplikaty'

        % przerabiamy listę 'L(we)' na listę par [[<elem L>, <krotność>],....]
        % w zależności od 'A' - tzn czy user chce 'All elem Lwe' z krotnościami
        % czy tylko 'zduplikowane', przerabiamy tak 
        % albo wszystkie E(lementy) - też te unikalne - gdy 'krotność > 0'
        % albo tylko powielone - gdy 'krotność > 1'

         ((A) -> ( % user chce 'All' elem z krotnościami - też unikalne
               findall([E,N],(member(E,L),listLiczElemN(E,L,N),N>0),Lset)
               % tutaj wstawiamy dane od razu to Lset - będzie użyte dalej,
               % chociaż Lset NIE jest zbiorem - patrz uwagi do 'list_to_set' 
               % niżej
            ) % koniec 'then' od '(A)->'
            ;
            ( % user chce tylko zduplikowane (obecne > raz) elem z krotnościami
               findall([E,N],(member(E,L),listLiczElemN(E,L,N),N>1),Lkrotn),
               list_to_set(Lkrotn,Lset)
            ) % koniec 'else' od '(A)->'
         ), % koniec '(A)->'

         % UWAGA!!! 
         % po powyższej operacji Lkrotn zawiera 'wszystkie' elementy
         % spełniające warunek  krotności (N>0 lub N>1),
         % gdy chcemy wszystko (A==true, czyli wyszukiwanie wg N>0):
         % dla L = [1,2,3,4,5], będzie Lkrotn=[[1,1],[2,1],[3,1],[4,1],[5,1]]
         % ALE dla: L=[1,2,1,2,3] => Lkrotn=[[1,2],[2,2],[1,2],[2,2],[3,1]]
         % a gdy chcemy same duplikaty (A != true, czyli wg N>1):
         % dla L = [1,2,3,4,5], będzie Lkrotn=[] 
         % ALE dla: L=[1,2,1,2,3] => Lkrotn=[[1,2],[2,2],[1,2],[2,2]]

         % czyli trzeba usunąć duplikaty z listy duplikatów :D :D :D 
         % dalej operujemy 'Lkrotn' zamiast 'L(we)'

         % teraz musi być 'list_to_set/2' zamiast 'sort/2' (patrz uwagi wyżej)
         % bo teraz interesuje nas usunięcie duplikatów i NIE zmienianie porządku

%         list_to_set(Lkrotn,Lset),
% EDIT: 
% danie 'list_to_set(Lkrotn,Lset)' w tym miejscu, powoduje, 
% że duplikaty były usuwane również wtedy, gdy podano 'A(ll)' = true
% a to raczej NIE jest oczekiwane zachowanie, gdy user chce 'wszystko'
% uznałem, że w tym przypadku lepiej zwrócić listę 'D' odpowiadającą
% ilością i kolejnością elementów liście 'L(we)' tylko z dodaną krotnością...
% także, jeśli 'L(we)' zawiera duplikaty i user podał 'A(ll)' = true,
% do dostanie listę dalej zawierającą powtórzenia - i przy każdym info o krotności
%
% a samo 'list_to_set' przeniosłem do gałęzi 'else' pytania '(A)->'
% tam, gdzie wyznaczamy 'D' zawierające tylko elementy z powtórzeniami,
% z podaną krotnością...

         % teraz operujemy na 'Lset' zamiast 'Lkrotn'

         ((S) -> ( % czy Jaśnie Pan User zamawiał sortowanie?
               localeSortAll(Lset,D)
            ) % koniec 'then' od '(A)->'
            ;
            ( % user chce tylko zduplikowane (obecne > raz) elem z krotnościami
               D = Lset
            ) % koniec 'else' od '(A)->'
         ), % koniec '(S)->' i zwracania odpowiedniej listy 'D'

         %  już zwróciliśmy listę 'D' - jeszcze koment i 'kod powrotu'
         piszTestInfo(true,'liZnajDupl',
            "'D' ma postać [[<elem,<krotność>],...] i zawartość\n\c
            (lub jej brak) zależną od 'A','S' i obecności duplikatów"),
         piszTestInfo(SąDuplikaty,'liZnajDupl',StrDuplKom)
         % komunikat + zwróć 'true/false' wg wartości 'SąDuplikaty'
      )% koniec 'else' od '(nonvar(D))->'
   ) % koniec '(nonvar(D)) ->'
). % koniec 'listZnajdźDuplikaty'



%
% w poniższych formułach szukamy predykatów zdefiniowanych w pliku, w którym
% zdefiniowano term 'antenaci' (dostajemy tutaj pełną ścieżkę (z nazwą) tego
% pliku - nie muszę pytać usera, gdzie go zapisał, jak go nazwał itd.,
% które są regułami (odpowiada za to parametr 'number_of_rules(LN) dla LN>0')
% albo atomami (parametr 'number_of_rules(LN) dla LN=0'),
% i które mają określoną liczbę argumentów (patrz functor(X,Nazwa,Narg)).
%
% reguł szukamy 2-arg. (takich, do których można 'przymierzyć' dwoje ludzi),
% a atomów 1-argumentowych (takie są tylko fakty o nazwiskach ludzi)
% szukamy nazw, które nie zawierają na początku znaków '_'/'$' - te mają w sobie
% niektóre termy predefiniowane prologa - ich nie będziemy 'przymierzać'
% ani takich, które na końcu nazwy mają 'tabled' - te użyto przy 'małżonkach'
% tzn definiowaniu reguły symetrycznej - sprawdzamy tylko 'nasze własne' reguły
%
% nie zdefiniowałem modułu... daltego szukam reguł w określonym (tym) pliku...
%

plikNazwaPełna(Nazwa):-(predicate_property(antenaci(_,_),file(Nazwa)),
                        piszTestInfo(true,'plikNazPeł',Nazwa)).


%
% Typ ='a' - będziemy szukać Narg 'atomów'
% Typ <>'a' (najlepiej 'c') - będziemy szukać klauzul / 'clauses'
% działanie zależy od stanu flagi 'flgTesty' (oddającej jej stan zm. 'testy')
% gdy 'testy' - znajduj/zwracaj all zdefiniowane nazwy,
% gdy 'testy'== false -> nie wyświetlaj  nazw 'z indeksu'
% EDIT: dodaję argument 'All' - żeby można było wybierać treści do wyświetlania
% też przy wywołaniu - teraz daję waunek: 'All OR testy'
%

termNarg(Narg,Nazwa,Typ,All) :-         % szukamy termów o danej Narg, z tego
    plikNazwaPełna(NazwaPełna),!,       % samego pliku co 'antenaci' (czyli tego)  
    predicate_property(X,file(NazwaPełna)),  % 'antenatów' wybrałem, bo jest małe
                                             %  prawdop.że są też gdzieś indziej

    predicate_property(X,number_of_rules(LN)),  % tu miało być rozróżnienie: 
    (Typ='a' -> LN=0;LN>0),              % atomy vs reguły - niedokładnie tak jest, 
    functor(X,Nazwa,Narg),               % ale best przybliżenie...
    \+ sub_atom(Nazwa, 0, _, _, '_'),
    \+ sub_atom(Nazwa, 0, _, _, $),      % w ogóle nie interesują nas 'systemowe',
    \+ sub_atom(Nazwa, _, _, 0, tabled), % z '$' lub '_'  na pocz lub 'tabled' na końcu
    ((testy;All)->true;(\+regPom(Nazwa))).     % do testów pokaż też 'pomocnicze' reguły
                                         % w ver ostatecznej ukryj je przez userem

%
% gdy testy = true, zwracanie 'Nazwa'
% nie zależy, czy 'Nazwa' jest na liście 'pomocniczych', czy nie. gdy test=false
% zwracanie 'Nazwa' ZALEŻY od obecności 'Nazwa' na liście pomocniczych...
% gdy  jest, 'nawias' będzie = false i tej 'Nazwa' NIE zwrócimy,
% gdy nie ma na liście 'zakazanych' -> 'nawias' = true i zwracamy 'Nazwa'
%
% pewnie łatwiej, a przynajmniej 'bardziej elegancko' byłoby to zrobić
% przerabiając ten plik na 'moduł' i badać predykaty zdefiniowane w 'module'
% ale, że o 'modułach' doczytałem już po zrobieniu tego, to 'jest, jak jest'
%
% domyślnie (bez podania All true/false) działaj jak przed zmianą,
% tzn przeszukuj 'widoczne dla usera w danym trybie' - czyli w trybie:
% 'testy'->'wszystkie', 'nie-testy' -> tylko te NIE będące na liście 'regPom(..)'
%

atomNarg(Narg,Nazwa)       :- termNarg(Narg,Nazwa,'a',false).
atomNarg(Narg,Nazwa,All)   :- termNarg(Narg,Nazwa,'a',All).
regułaNarg(Narg,Nazwa)     :- termNarg(Narg,Nazwa,'c',false).
regułaNarg(Narg,Nazwa,All) :- termNarg(Narg,Nazwa,'c',All).
termNarg(Narg,Nazwa)       :- atomNarg(Narg,Nazwa); regułaNarg(Narg,Nazwa).
termNarg(Narg,Nazwa,All)   :- atomNarg(Narg,Nazwa,All); regułaNarg(Narg,Nazwa,All).



%
% odpowiedzi wygenerowane przez reguły:
%    atomNarg(_,_), regułaNarg(_,_), termNarg(_,_)
% przerabiamy teraz na listę LROO - 'listę reguł osób pozostających w relacji'


%
% reguły 'osobyWRel(O,LROO)' i 'osobyWRel(O1,O2,LROO)' 
% zostawiam na wypadek, jeśli będzie potrzebna raczej lista 
% niż wyświetlenie na ekranie
%

osobyWRel(O,LROO) :-
   findall(TE, (termNarg(1,Reg1), (TE=..[Reg1,O]), TE), LROO).

osobyWRel(O1,O2,LROO):-
   findall(TE, (termNarg(2,Reg2), (TE=..[Reg2,O1,O2]), TE),LROO).


%
% 'piszOsobyWRel(O1,O2) :-' - na razie bez obsługi list i bez weryfikacji arg.
%

piszOsobyWRel(O1,O2) :- (
   findall(TE, 
          (termNarg(2,Reg2), (TE=..[Reg2,O1,O2]), TE),
          LROO),
   (var(O1)-> O1a='jakaś osoba'; O1a=O1),
   (var(O2)-> O2a='jakaś osoba'; O2a=O2),
   piszKomunikat(jestOK,
      "\nDostępne reguły dwu-argumentowe, w których\n\c
      biorą udział '~w' i '~w':\n\n",
      [O1a,O2a]),
   piszListWTabeli(LROO),!
). % end of 'piszOsobyWRel(O1,O2)'


piszOsobyWRel(O) :- (is_list(O),O=[G|T],
   (piszOsobyWRel(G),piszOsobyWRel(T)),
   !
).

piszOsobyWRel(O) :- is_list(O),O=[],!.

piszOsobyWRel(O) :- (
   findall(TE,
          (termNarg(1,Reg1),(TE=..[Reg1,O]),TE),
          LROO),
   (var(O)-> O1='jakaś osoba'; O1=O),
   piszKomunikat(jestOK,
      "\nDostępne reguły jedno-argumentowe, w których '~w' bierze udział:\n\n",
      [O1]),
   piszListWTabeli(LROO),!
). % end of 'piszOsobyWRel(O)'

piszOsobyWRel :- piszOsobyWRel(_).


%
% wypisywanie w kolumnach termów 1-argumentowych
%


piszTerm1El(T,Kol,RemDup,Sort,Just,Sep) :- T1=..[T,X], findall(X,T1,LXT1),
    piszListWTabeli(LXT1,Kol,RemDup,Sort,Just,Sep).

piszTerm1El(T,Kol,RemDup,Sort,Jus)  :-piszTerm1El(T,Kol  ,RemDup, Sort,Jus,' ').
piszTerm1El(T,Kol,RemDup,Sort)      :-piszTerm1El(T,Kol  ,RemDup, Sort,'L',' ').
piszTerm1El(T,Kol,RemDup)           :-piszTerm1El(T,Kol  ,RemDup, true,'L',' ').
piszTerm1El(T,Kol)                  :-piszTerm1El(T,Kol  ,  true, true,'L',' ').
piszTerm1El(T)                      :-piszTerm1El(T, true,  true, true,'L',' ').


%
% wypisywanie w kolumnach termów 2-argumentowych
%

piszTerm2El(T,Kol,RemDup,Sort,Just,Sep) :- T2=..[T,X,Y], findall((X,Y),T2,LXT2),
    piszListWTabeli(LXT2,Kol,RemDup,Sort,Just,Sep).
piszTerm2El(T,Kol,RemDup,Sort,Jus)  :-piszTerm2El(T,Kol  ,RemDup, Sort,Jus,' ').
piszTerm2El(T,Kol,RemDup,Sort)      :-piszTerm2El(T,Kol  ,RemDup, Sort,'L',' ').
piszTerm2El(T,Kol,RemDup)           :-piszTerm2El(T,Kol  ,RemDup, true,'L',' ').
piszTerm2El(T,Kol)                  :-piszTerm2El(T,Kol  ,  true, true,'L',' ').
piszTerm2El(T)                      :-piszTerm2El(T, true,  true, true,'L',' ').


%
% 'piszListElWKol'
% wypisuje elementy otrzymanej listy 'tabelarycznie', w kolejności:
%   wiersz1: LEl1<Sep>LEl2<Sep>..LElN<Sep> - N LElem w 1 wierszu, N = ilość 'Kol'
%   wiersz2: LElN+1<Sep>....
% każdy wpis: LElx<Sep> zajmuje 'Szer' znaków (chyba, że przekazano dłuższy LElem
% to niech sobie system radzi...),
% uwaga: na końcu wiersza TEŻ dajemy <Sep> - istotne np gdy piszemy do csv
%
% elementy L w układzie 'Kol' kolumn o szerokości 'Szer' znaków,
% wyjustowanych wg param.'Jus', oddzielonych znakiem  'Sep':
%
%    'Kol' - ilość kol.w wierszu (teraz tej samej szer, może kiedyś lista szer)
%    'Szer'- szerokość jednej kol w znakach - powinna być chociaż o 1 znak
%            większa niż największa występująca szerokość elem.listy L
%            powinna o to zadbać f-cja wywołująca - ta tego nie sprawdza
%         UWAGA! f-cja NIE sprawdza też czy 'Kol'*'Szer'<=szer ekranu/terminala
%            bo nie sprawdza, czy pisze na ekran, czy do pliku -
%            to sprawdzenie to zadanie f-cji wywołującej...
%    'Jus'- wyrównanie: na razie 'l', 'L', "l", "L", 'r', 'R', "r", "R"
%            (może kiedyś będzie 'center')
%    'Sep' - znak (char) separatora - preferowane ' ',',',';','\t',\n',
%            chociaż dopuszczalny dowolny 'pure ascii' (kody 0...127) 
%            ale nie wszystkie mają sens - np '\t' może zachowywać się dziwnie, 
%            skoro szerokość kolumn ustalamy inaczej...
%            ale znowu - ta f-cja tego nie sprawdza
%            tylko, gdy nie rozpozna 'Sep', jako 'znaku ascii',
%            to przyjmie ' ' (spację) jako 'wystarczająco dobrą' na ekranie
%            podanie 'Sep' np ',' lub ';' może się przydać, gdy piszemy do csv
%
% na końcu ostatniego wiersza, nawet, jeśli nie jest cały zapełniony, daje \n
% jeśli parametry przejdą wszystkie testy, po wypisaniu zwraca 'true'
% jeśli któryś test będzie 'oblany' - zwraca 'false'
%


%
% najpierw testujemy kolejne argumenty dla 'piszListElemWTabeli'
%

piszListElWKolTestL(L) :-
(listCzyNiePusta(L, NLElem) ->(
    swritef(StrPom01a,"'L' OK - przekazano listę o długości: %t",[NLElem]),
    piszTestInfo(true,'piszLETTAL',StrPom01a),
    swritef(StrPom01b,"%rL=%t",[' ',14,L]),
    piszTestInfo(true,'piszLETTAL',StrPom01b)
    ) % L 'niepusta' - możemy iść dalej...
    ;                                 
    (piszTestInfo(false,'piszLETTAL',
         "'L' nie przekazano lub l.pustą, pa pa..."))
     % nie ma co wyświetlać-uciekamy i zwracamy 'false'-nie potrzeba osobnego
).

piszListElWKolTestKolSzer(Kol,Szer) :-
(% testuj param 'Kol', 'Szer'
    ((var(Kol);var(Szer))->   % Jus, Sep mają wart.domyślne - tu NIE testujemy
         (piszTestInfo(false,'piszLETTKS',
                       "'Kol/Szer' - któregoś nie przekazano, pa pa...")
         ) % koniec 'then' 'var(Kol);var(Szer)' - ale są wymagane - > uciekamy
         ;
         (true
         ) 
    ), 
    % Kol/Szer jakoś zdefiniowane - sprawdzamy dalej

    StrKol1 ='\tKol=',
    (term_string_clever(Kol,StrKol2)),
    StrSzer1=', Szer=',
    (term_string_clever(Szer,StrSzer2)),
%    string_concat(StrKol1,StrKol2,StrKol),
%    string_concat(StrSzer1,StrSzer2,StrSzer),
%    string_concat(StrKol,StrSzer,StrKolSzer),

    string_concat_many([StrKol1,StrKol2,StrSzer1,StrSzer2],StrKolSzer),
    piszTestInfo(true,'piszLETTKS',"'Kol/Szer' - jakieś przekazano:"),
    piszTestInfo(true,'piszLETTKS',StrKolSzer),

    % tu Kol/Szer oba są 'jakieś' - testuj ich typ i wartości 
    ((integer(Kol),integer(Szer),(Kol>0),(Szer>0))->
        % wiemy, że liczby całkowite dodatnie; sprawdźmy jeszcze czy nie za duże
        (((Kol>128);(Szer>1024))->(piszTestInfo(true,'piszLETTAr',
            "'Kol/Szer' - jesteś pewien, że mają dobre wartości?, może sprawdź..."),
            piszTestInfo(true,'piszLETTKS',StrKolSzer)
            % powyżej tylko warninng - wartości przykładowe - idziemy dalej
            % dlatego 'piszTestInfo...' ma zwracać 'true'
            ) % koniec 'then' ((Kol>128);(Szer>1024))
            ;
            (piszTestInfo(true,'piszLETTKS',"'Kol/Szer' sprawdzone - są OK."),
             piszTestInfo(true,'piszLETTKS',StrKolSzer)
            ) % koniec 'else' ((Kol>128);(Szer>1024))
        ) % koniec 'then' od '(integer(Kol),integer(Szer...'
        ;
        (piszTestInfo(true,'piszLETTKS', 
         "'Kol/Szer muszą być liczbami naturalnymi, a te to co..., pa pa..."),
         piszTestInfo(false,'piszLETTKS',StrKolSzer) % od razu zwracaj false
         % zwracamy 'false', bo dla Kol/Szer nie przewiduję wartości domyślnych
         % także jak są złe, to uciekam...
        ) % koniec 'else' od '(integer(Kol),integer(Szer...'
    ) % koniec '(integer(Kol),integer(Szer...'
). % koniec 'piszListElWKolTestKolSzer'


%
% JusWe - tu wstawiamy testowaną wartość 'Jus'
% JusWy - tu otrzymamy wartość 'Jus' po testach
% jeśli JusWe przeszła je pozytywnie, to zwracamy ją
% jeśli JusWe nie przeszła testów - zwracamy domyślne 'L'(eft)
% UWAGA!!! 
% żeby to działało, zmienna wstawiona w miejsce JusWy
% MUSI BYĆ NIEPRZYPISANA
% jeśli będzie mieć jakąkolwiek wartość prolog NIE zmodyfikuje tej wartości...
% w dalszej części kodu - za wywołaniem tego testu, trzeba się posługiwać 
% już tym, co zwróci 'JusWy', a NIE tym, co daliśmy do sprawdzenia w 'JusWe'
%

piszListElWKolTestJus(JusWe,JusWy) :- (
    justifyLeftTag(JL), justifyRightTag(JR), justifyCenterTag(JC),
    append([JL,JR,JC],JLRC),
    
    % testuj 'JusWe' czy jest i czy ma znaną wartość?
    (var(JusWe)->      % 'Jus' nie zdefiniowano,daję domyślne 'L'
        (JusWe='pustka',  %  nie było określone, więc możemy przypisać...
         piszTestInfo(true,'piszLETTAJ', "'Jus' nie zdefiniowana")
        ) % koniec 'then' od 'var(Jus)'
        ;
        (/*JusWe*/ % na razie NIE zmieniamy JusWe
            true
        ) % 'Jus' 'jakoś' określone - idziemy dalej
    ), % koniec 'var(Jus)->'

    StrJus1a='\tJusWe=',
    (term_string_clever(JusWe,StrJus2)),
    string_concat_many([StrJus1a,StrJus2],StrJus),
    piszTestInfo(true,'piszLETTAJ',"'Jus' na razie (do dalszych testów):"),
    piszTestInfo(true,'piszLETTAJ',StrJus),
    
    % tu 'JusWe' jakoś określona - sprawdzamy, czy ma  znaną  wartość
    (listElem(JusWe,JLRC) -> (
     piszTestInfo(true,'piszLETTAJ',
        "'Jus' jest ze znanego zestawu - hurra!:"),
        piszTestInfo(true,'piszLETTAJ',StrJus),
        JusWy=JusWe
        ) % koniec 'then' od 'listElem(JusWe,JLRC)->'
        ;
        % tu 'JusWe' określona, ale ma nieznaną wartość -> daję 'L'
        (
            JusWy='L',  % przypisujemy wartość domyślną - 'L'
            piszTestInfo(true,
                'piszLETTAJ', "'Jus' było, ale nieznane - daję 'L'(eft)")
        ) % koniec 'else' od 'listElem(JusWe,JLRC)->'
    ), % koniec 'listElem(JusWe,JLRC)->'

    StrJus1b='\tJusWy=',
    (term_string_clever(JusWy,StrJus2b)),
    string_concat_many([StrJus1b,StrJus2b],StrJusWy),
    piszTestInfo(true,'piszLETTAJ',"'Jus' ostatecznie ma wartość:"),
    piszTestInfo(true,'piszLETTAJ',StrJusWy)
). % koniec 'piszListElWKolTestJus'


piszListElWKolTestSep(SepWe,SepWy) :- (
    separatorPreferredChars(SPCh), %[' ','\t','\n',',',';','|', też w ""]

    % ACh   = allowed char (for 'Sep')
    % LACh  = list of allowed chars
    % SLACh = sorted list of allowed chars
    % przyjmuję, że to mogą być znaki ascii 0...127 (\000..\1ff oct)
    % nie wiem dlaczego, ale findall w LACh wpisuje 17 !!! identycznych zestawów
    % znaków ascii - chyba ma to związek z tym, że system unicode ma właśnie
    % 17 jakichś grup znaków - w każdym razie sort m.in.odrzuca duplikaty
    % w ten sposób w SLACH mamy pojedynczy zestaw znaków ascii

    findall(ACh,char_type(ACh,ascii),LACh),sort(LACh,SLACh),
    % tu w sumie mogłoby być 'locale_sort', ale akurat tu nie jest potrzebne


    % testujemy 'Sep', czy jest i czy ma znaną wartość
    % są wartości preferowane-wyróżnione, by szybciej je odnaleźć
    % ale dopuszczam dowolny znak -  przy pisaniu do plików mogą być
    % przydatne/potrzebne różne dziwne separatory...
    % TO DO: być może kiedyś rozróźnić pisanie na ekran i do stringu/pliku
    % z innym zestawem dopuszczalnych separatorów

    (var(SepWe) -> (      % 'Sep' nie zdefiniowano,daję domyślną ' '
            SepWe='pustka', %  nie było określone, więc możemy przypisać...
            piszTestInfo(true,'piszLETTAS', "'Sep' nie zdefiniowana")
        ) % koniec 'then' od 'var(SepWe)'
        ;
        (/*SepWe,*/ % na razie po prostu używamy 'SepWe'
            true
        ) % koniec 'else' od 'var(SepWe)' 'Sep' jest 'jakieś' - idziemy dalej
    ), % koniec 'var(SepWe)->'

    StrSep1a='\tSepWe=',
    (term_string_clever(SepWe,StrSep2a)),
    string_concat_many([StrSep1a,StrSep2a],StrSep),
    piszTestInfo(true,'piszLETTAS',"'Sep' na razie (do dalszych testów):"),
    piszTestInfo(true,'piszLETTAS',StrSep),


    % tu 'Sep' jakoś określona - sprawdzamy, czy ma pref/dopuszcz. wartość
    
    (listElem(SepWe,SPCh) -> (
        piszTestInfo(true,'piszLETTAS',
            "'Sep' jest z preferowanego zestawu - hurra!:"),
        piszTestInfo(true,'piszLETTAS',StrSep),
        SepWy=SepWe
        ) % koniec 'then' od 'listElem(SepWe,SPCh)->'
        ;
        % tu 'Sep' określona, ale ma wartość inną niż preferowana
        % sprawdzam, czy ma chociaż dopuszczalną
        (listElem(SepWe,SLACh) -> (
            piszTestInfo(true,'piszLETTAS',
   "'Sep' - nie preferowany, ale poprawny:"),
            piszTestInfo(true,'piszLETTAS',StrSep),
            SepWy=SepWe
            ) % koniec 'then' od 'listElem(SepWe,SLACh) ->'
            ;
            (piszTestInfo(true,'piszLETTAS',
                "'Sep' ma wartość spoza akceptowalnego zestawu:"),
             (term_string_clever(SepWe,StrSep2b)),
             string_concat_many([StrSep1a,StrSep2b],StrSepPoza),
             piszTestInfo(true,'piszLETTAS',StrSepPoza),
             piszTestInfo(true,'piszLETTAS', "\tDaję domyślną spację:' '"),
             SepWy=' '
            ) % koniec 'else' od 'listElem(SepWy,SLACh)->'
        ) % koniec 'listElem(SepWy,SLACh)->' i  koniec 'else' 'listElem(SepWy,SPCh)'
    ), % koniec 'listElem(SepWy,SPCh)->'

    StrSep1b='\tSepWy=',
    (term_string_clever(SepWy,StrSep2)),
    string_concat_many([StrSep1b,StrSep2],StrSepWy),
    piszTestInfo(true,'piszLETTAS',"'Sep' ostatecznie ma wartość:"),
    piszTestInfo(true,'piszLETTAS',StrSepWy)
). % koniec 'piszListElWKolTestSep'



piszListElWKol(L,Kol,Szer,Jus,Sep) :- (

% UWAGA:
% wartości L, Kol, Szer musza być 'dobrze określone', tzn.:
%    L - niepusta lista,
%    Kol, Szer - liczby naturalne                                                      
% 
% natomiast wartości Jus, Sep na tym etapie są 'sugerowane'
% tzn. po weryfikacji, jeśli nie przejdą testów, NIE zostną użyte,
% tylko zamiast nich jakieś wartości domyślne

    (piszListElWKolTestL(L) ->(true);(false)), 
    % L 'pusta' lub nie-lista - uciekamy (komunikat jest w teście)
    % L 'niepusta' - możemy iść dalej (najpierw pochwalmy się na testach...
    
    (piszListElWKolTestKolSzer(Kol,Szer)->(true);(false)),
    % Kol,Szer nie są liczbami naturalnymi? uciekamy

    % tutaj mamy sprawdzone parametry wymagane: L, Kol, Szer

    % teraz sprawdzamy Jus/Sep - one mogą nie być podane, albo 'dziwne'
    % przewiduję dla nich wartości domyślne, także ich błędy nas nie powstrzymają

    (piszListElWKolTestJus(Jus,JusWyn)->(true);(false)),
    % tu dla pewności sprawdzamy, czy na pweno zwróciło nam dobre 'JusWyn'...
    StrJus1='\tJusWyn=',
    (term_string_clever(JusWyn,StrJus2)),
    string_concat_many([StrJus1,StrJus2],StrJus),
    piszTestInfo(true,'piszLETTAr',"'Jus' po testach ma wartość:"),
    piszTestInfo(true,'piszLETTAr',StrJus),


    (piszListElWKolTestSep(Sep,SepWyn)->(true);(false)),
    % tu dla pewności sprawdzamy, czy na pweno zwróciło nam dobre 'SepWyn'...
    (term_string_clever(SepWyn,StrSepWyn)),
%    StrSepWyn=SepWyn,
    StrSep1='\tSepWyn=',
    string_length(StrSepWyn,StrSepWynLen),
    (term_string_clever(StrSepWynLen,StrStrSepWynLen)),
    string_concat_many([StrSep1,StrSepWyn,' a długość=',StrStrSepWynLen],StrSep),

    piszTestInfo(true,'piszLETTAr',"'Sep' po testach ma wartość:"),
    piszTestInfo(true,'piszLETTAr',StrSep),

    % 'piszListElWKol' - koniec testów parametrów - 
    % dopiero teraz zabieramy się do właściwej pracy

    piszListElWKolPom(L,Kol,0,Szer,JusWyn,SepWyn)   % właściwe pisanie na ekran (lub do pliku...)

).  % koniec 'piszListElWKol(L,Kol,Szer,Jus,Sep).


piszListElWKol(L,Kol,Szer,Jus) :-           % gdy nie podano Jus/Stab
    (piszListElWKol(L,Kol,Szer,Jus,' ')).   % przyjmie wart.domyślne: 'L' i ' ' 

piszListElWKol(L,Kol,Szer) :-
    (piszListElWKol(L,Kol,Szer,'L',' ')).

%
% łączenie wielu stringów w 1 - wzięte z odpowiedzi na pytanie:
% https://stackoverflow.com/questions/33726463/concatenation-of-strings-in-prolog
% (wbudowane string_concat/3 łączy tylko 2 stringi...)
% zalecane, by flagę 'double_quotes' ustawić na 'string' lub 'atom'
% dla wartości 'chars'/'codes' pojawiają się błędy dla stringów
% podanych w "" zamiast ''
%

string_concat_many(StringList, StringResult) :-
    maplist(atom_chars, StringList, Lists),
    append(Lists, List),
    atom_chars(StringResult, List).



% 'piszListElWKolPom' - wół roboczy dla 'piszListElWKol'
% robi właściwe wypisywanie listy w kolejnych wierszach
% w układzie tabelarycznym - ale nie sprawdza dokładnie 
% argumentów (no... trochę tak)
% rozdzieliłem to, ponieważ 'piszListElWKolPom' jest
% wołana rekurencyjnie - żeby sprawdzenie argumentów
% odbyło się raz na początku - w 'piszListElWKol'
% a później już tylko 'jedziemy z koksem'

piszListElWKolPom([],_,_,_,_,_) :-write('\n').


% Kakt - 'kolumna aktualna' - na początku wołamy z '0'/zerem

piszListElWKolPom(L,K,Kakt,Sz,J,Se) :- (
    L =[G| T],

    % nie wiemy co jest na liście 'L'...
    % jeśli aktualnie obrabiany element czyli 'G'
    % to string - zostawiamy, co innego -> przerabiamy na string
    (term_string_clever(G,StrG)),

    % 'Se' (separator) przekazany z wyższego poziomu może być 'x' lub "x"
    % dla jednolitości przerabiamy go na string
%    (term_string_clever(Se,StrSe)),
    StrSe=Se,

    string_length(StrSe, StrSeLen),
    (term_string_clever(StrSeLen,StrStrSeLen)),
    string_concat_many(['Dł Stringu Separatora=',StrStrSeLen],StrPom0),
    piszTestInfo(true,'piszLElWTP',StrPom0),
    % w 'StrGSe' mamy element listy do wypisania, razem z separatorem
    string_concat_many([StrG,StrSe],StrGSe),

    % 'StrGSeLen' - dł z separatorm
    string_length(StrGSe,GSeStrLen),

    justifyLeftTag(JL), justifyRightTag(JR), justifyCenterTag(JC),
    append([JL,JR,JC],JLRC),

    ((GSeStrLen>=Sz) -> ( 
          % szer elementu do wypisania z separatorm jest >= szer kol.
          % czyli nic nie dodaję do tego - w sumie to błąd w wywołaniu...
          % (nie powinno tak być) - ale skoro jest - niech sobie system radzi...
          piszTestInfo(true,'piszLElWTP',"Element do wypisania dłuższy niż szer kol:"),
          string_concat_many(['\t',StrGSe],StrPom1a),
          piszTestInfo(true,'piszLElWTP',StrPom1a),
          (term_string_clever(Sz,StrSz)),
          (term_string_clever(GSeStrLen,StrGSeStrLen)),
          string_concat_many(['\tSzer kol=',StrSz,', dł elem.do wypisania=',StrGSeStrLen],
              StrPom1b),
          piszTestInfo(true,'piszLElWTP',StrPom1b),

          MyOutStr = StrGSe, % trudno, StrGSe, jest za długi, ale go zwracamy...
          true
       ) % koniec 'then' '(StrGSeLen>=Sz) ->'
       ;
       (
          % w gałęzi 'else' szerokość elem do wypisania (z separatorem) < szer Kol
          % czyli trzeba dodać spacje... w zależności od ustawionego justowania
          % 'l'/'L' -> za tekstem, 'r'/'R' -> przed tekstem, 'c'/'C' -> po obu stronach
          NSpc is (Sz - GSeStrLen),  % il.spacji potrzebna do uzupełnienia do Szer Kol
          NSpcBef is (NSpc // 2),    % il.spacji do wstawienia przed tekstem
          NSpcAft is (NSpc - NSpcBef), % '//' to dzielenie z wynikiem całkowitym

          swritef(StrNSpc,'%r',[' ',NSpc]),       % robimy stringi z potrzebnej il.spacji
          swritef(StrNSpcBef,'%r',[' ',NSpcBef]),
          swritef(StrNSpcAft,'%r',[' ',NSpcAft]),

          (listElem(J,JLRC)->( % teoretycznie niepotrzebnie, ale sprawdzamy justowanie...

                % skoro tu jesteśmy, to do którejś z tych list, J musi należeć...
                % zakładam, że te listy są rozłączne!!!
                (listElem(J,JL),string_concat_many([StrGSe,StrNSpc],MyOutStr),!);
                (listElem(J,JR),string_concat_many([StrNSpc,StrGSe],MyOutStr),!);
                (listElem(J,JC),string_concat_many([StrNSpcBef,StrGSe,StrNSpcAft],MyOutStr),!),
                true
             ) % koniec 'then' 'listElem(J,JLRC)'
             ;
             ( % gdy przypadkiem przekazane justowanie nie należy do znanych, robimy jak dla 'L'
                (listElem(J,JL),string_concat_many([StrGSe,StrNSpc],MyOutStr)),
                true
             )
          ) % koniec 'listElem(J,JLRC)->'
       ) % koniec 'else' '(StrGSeLen>=Sz) ->'
    ), % koniec '(StrGSeLen>=Sz) ->'
    string_length(MyOutStr,MyOutStrLen),
    (((MyOutStrLen =< 1),
       piszTestInfo(true,'piszLElWTP',"'MyOutStr' - coś poszło źle"),
       string_concat_many(['\t','Przekazano:',StrG,', a mamy:',MyOutStr],StrPom1c),
       piszTestInfo(false,'piszLElWTP',StrPom1c)
    );true),

    % w końcu coś piszemy... 
    write(MyOutStr),
    ((((Kakt+1) mod K) =:= 0) -> (Kakt1 is 0, nl); (Kakt1 is Kakt+1)),
    piszListElWKolPom(T,K,Kakt1,Sz,J,Se)
). % koniec 'piszListElWKolPom'

piszListElWKolPom(T,K,Kakt,Sz,J) :- piszListElWKolPom(T,K,Kakt,Sz,J,' ').
piszListElWKolPom(T,K,Kakt,Sz)   :- piszListElWKolPom(T,K,Kakt,Sz,'L',' ').


%
% localeSortAll(LWe,LWy)
% funkcja sortująca listy zawierające dane mogący być traktowane jako npisy
% z wykorzystaniem mechnizmu 'locale' - informacji m.in.o znakach narodowych
% był problem: 'zwykłe' locale_sort wymaga listy stringów/atomów... 
% NIE radzi sobie z listami zagnieżdżonymi - np listą małżonków lub rodzic-dziecko
% pomysł - przekształcę elementy LWe na stringi z 'doczepionym z tyłu indexem'
% przepuszczę przez locale_sort, wyodrębnię indeksy i wg nich powybieram elem.
% z listy 'we', do umieszczenia w liście 'wy'
%

localeSortAll(LWe,LWy) :- (
   (nonvar(LWy) -> ( % jeśli nie będzie można zwrócić wyniku, 
                     % nie ma sensu sprawdzać 'LWe' ani robić nic innego
         piszTestInfo(true,'locSortAll',
            "'LWy' związana (nonvar) - nie mogę jej modyfikować,"),
         piszTestInfo(false,'locSortAll',
            "nie mam jak przekazać posortowanej LWe - pa, pa...")
         % zwróć 'false' - uciekaj z funkcji (patrz drugie 'piszTestInfo'
      ) % koniec 'then' od 'nonvar(LWy)->'
      ;
      ( % będzie gdzie zwrócić wynik - mają sens dalsze testy
         piszTestInfo(true,'locSortAll',
            "'LWy' wolna (var) - sprawdzamy dalej,")
         % stąd zwracaj 'true' - znaczy się idziemy dalej z testami
      ) % koniec 'else' od 'nonvar(LWy)->'
   ), % koniec 'nonvar(LWy)->'

   % sprawdzamy czy mamy co sortować i poznajemy dł.

   ((listCzyNiePusta(LWe,LWeLen)) -> ( % pusta - uciekamy, niepusta- idź dalej
         % LWe 'niepusta' => stąd zwracamy 'true' =>  jedziemy dalej...
         piszTestInfo(true,'locSortAll',"'LWe' nie-pusta - sprawdzamy dalej")
         % koniec 'else' od '(LWeLen =:= 0) ->'
      ) % koniec 'then' od '(listCzyNiePusta(LWe,LWeLen)) -> '
      ;
      (  LWy =[],
         % komunikat + zwróć od razu 'false'
         piszTestInfo(false,'locSortAll',"'LWe' pusta - nie mam co sortować")
         % nie ma co sortować => zwracaj 'false' => uciekaj z funkcji
      ) % koniec 'else' od '(listCzyNiePusta(LWe,LWeLen)) -> '
   ), % koniec '(listCzyNiePusta(LWe,LWeLen)) -> '
   
   term_string(LWeLen,LWeIndxStr),         % potrzebuję wiedzieć, jaką max dł
   string_length(LWeIndxStr,LWeIndxStrLen), % może mieć string reprezentujący 
                                            % indeks LWe

   listStrElMaxDl(LWe,_,LWeNajdlElemLen), 
      % zwróć dł najdłuższego Elem LWe po jego przeróbce na string

   swritef(StrPom04a,'%t %t %t %t\n',
      [LWeLen,LWeIndxStr,LWeIndxStrLen,LWeNajdlElemLen]),
   piszTestInfo(true,'locSortAll',StrPom04a),   

   findall(Indx,between(1,LWeLen,Indx),LNr1_LWeLen), % zrób listę liczb 1..LWeLen

   % na takie stringi będę przerabiał elem LWe z indeksami:
   % elem L-justified w szer LWeNajdłElemLen + 2 spacje 
   % + R-justified str indeksu w jego max szer.
   swritef(MyFormat,"%%tl  %%tr",[LWeNajdlElemLen,LWeIndxStrLen]),

   maplist(
      {MyFormat}/[IN,NR,OUT]>>( 
         swritef(StrElem,"%t",[IN]),
         swritef(StrIndx,"%t",[NR]),
         swritef(LWeElemStrZIndx,MyFormat,[StrElem,StrIndx]),
         OUT = LWeElemStrZIndx
      ), % koniec f-cji lambda przerabiającej LWe na 'L stringów z indeksami'
      LWe,
      LNr1_LWeLen,
      LWeStrZIndx
   ), % koniec maplist robiącego z Lwe listę "stringów z indeksami"

   % tutaj w LWeStrZIndx mamy listę stringów odpowiadających elementow Lwe,
   % z doczepionymi stringami reprezentującymi indeks - nr elementu na LWe

   locale_sort(LWeStrZIndx,SrtLWeStrZIndx), % właściwe sortowanie

   % czas na wyodrębnienie z posortowanej listy indeksów i zrobienie z ich listy
   % w stringach powstałych na bazie elementów LWe, 
   % indeksy zajmują 'LWeIndxStrLen' znaków od prawej

   maplist(
      {LWeIndxStrLen}/[IN,OUT]>>( 
         sub_string(IN,_,LWeIndxStrLen,0,SrtIndxStr), % bierzemy też dodane 2 spacje
         term_string(OUT, SrtIndxStr) % działa w <-> strony - tu: string -> liczba
      ), % koniec f-cji lambda robiącej listę indeksów z 'posort.L stringów z indx'
      SrtLWeStrZIndx,
      LIndxSrt
   ), % koniec maplist robiącego z posortowanej listy stringów z indeksami
      % listę indeksów

   % czas na ostatnie działalnie - czytanie po kolei listy indeksów
   % wybieranie wg indeksu N-tego elementu LWe i zapisywanie go do LWy

   maplist(
      {LWe}/[IN,OUT]>>( 
         nth1(IN, LWe,OUT)  % z LWe pobiera elem.z pozycji o numerze (licz.od 1)
                            % będącej wartością indeksu pobranego z LIndx
                            % gdzie LIndx - lista indeksów po sortowaniu
                            % i zapisuje pobrany elem. do LWy
      ), % koniec f-cji lambda robiącej listę indeksów z 'posort.L stringów z indx'
      LIndxSrt,
      LWy
   ),% koniec maplist wybierającego z LWe elementy wg indeksów otrzymanych po
     % przejściu przez locale_sort, tyle, że elem to NIEKONIECZNIE STRINGI,
     % MOGĄ BYĆ NP ZAGNIEŻDŻONE LISTY - czyli możemy np sortować listę par
     % małżonków, albo rodzic-dziecko - samo locale_sort tego nie potrafi :)
     % UWAGA!!!! - to NIE jest rozw.idealne - sortowanie jest _tekstowe_,
     % nawet, jeśli na LWe są liczby - czyli np: 1,10,100,11,12,...
     % a NIE 1,10,11,12,100...

   true % coś tam sortowaliśmy - zwracam 'true'
). % koniec 'localeSortAll(LWe,LWy)'


%
% wypisuje elementy listy 'L' w postaci tabeli wiersze / kolumny
% oczywiście L musi być listą, niepustą
%   Kier: =false -> wypisuje poziomo / wierszami - NOT IMPLEMENTED YET
%         =true  -> wypisuje kolumnami
%   RemDup: =false -> wypisuje 'L' taką, jak przekazano
%         =true  -> usuwa duplikaty
%   Srt:  =false -> wypisuje 'L' taką, jak przekazano
%         =true  -> wypisuje posortowaną 
%   Jus:  sposób justowania: l/L/r/R/c/C, domyślnie L (gdy podano '_' lub nizenany
%   Sep:  separator między wypisanymi elementami 'L' - 1 znak z zestawu ASCII,
%         domyślnie ' '; jeśli wyjście przekierujemy np do csv, warto dać np ',' ';' '\t' itp
% zwraca:
%   true, gdy L była listą, niepustą
%   false, gdy L nie była listą, lub była listą pustą
%

piszListWTabeli(L, Kier, RemDup, Srt, Jus, Sep) :- (
   (listCzyNiePusta(L,LLen) -> ( % w LLen mamy długość listy 'L'
      swritef(StrPom01c,"'L' to lista o długości %t:",[LLen]),
      piszTestInfo(true,'piszLiWTab',StrPom01c),
      swritef(StrPom01d,"\tL=%t",[L]),
      piszTestInfo(true,'piszLiWTab',StrPom01d)
      % w tym przypadku, poza testami nie trzeba komunikatu...
      ) % koniec 'then' 'listCzyNiePusta->'
      ;
      ( % a tu z kolei przyda się komunikat nawet poza testami - dlatego piszę 'ten drugi'
        piszKomunikat(nieOK, "~w\n~w\n",
          ["Tu:'Pisz Listę w formie Tabeli' - przykro mi,",
           "ale nie dostałem listy do wypisania, pa pa..."]),
        false % uciekamy z 'piszListWTabeli' - nie mamy co wypisywać...
      ) % koniec 'else' 'listCzyNiePusta->'
   ), % (listCzyNiePusta)->'

   (((RemDup) -> % gdy uważamy 'RemDup' za 'true'
       list_to_set(L, L0)
       ;
       (L0 = L) % nie usuwamy duplikatów
   );true), % '(RemDup)->', 'true' - żeby nie wyrzuciło nas 'wyżej' jeśli ()->();() zwróci false

   % UWAGA!!! odtąd posługjemy się listą 'L0' !!!


   % UWAGA!!!
   % próbowałem  połączyć etap usuwania duplikatów z sortowaniem (sort/2 robi to _i_ to)
   % ale sort/2 NIE sortuje dobrze polskich liter -> trzeba użyć locale_sort/2
   % za to locale_sort/2 NIE usuwa duplikatów - także rozdzieliłem te etapy
   % najpiew jest usuwanie duplikatów (gdy RemDup = true), a potem, gdy potencjalnie 
   % jest już mniej elem na liście, daję locale_sort/2
   % a... i zamiast 'locale_sort/2' użyłem mojego: 'localeSortAll/2'
   % w przeciwieństwie do 'locale_sort/2' to radzi sobie np z listami zagnieżdż.
   %
   % L0 - we do poniższego ((Srt)->();()) 
   % L1 - wyjście: (Srt) -> (L1 = sorted (L0)) ; (L1 = L0)
   %      do sortowania używa locale_sort(_,_), ale pomimo jego ograniczeń
   %      działa też na zagnieżdżonych listach

   (((Srt) -> ( % gdy uważamy 'Srt' za 'true'
      localeSortAll(L0,L1) % takie locale_sort(), ale też np do 'nested lists'
      ) % koniec 'then' od '(Srt)->'
      ;                    
      (L1 = L0) % ok, bez sortowania
   );true), % '(Srt)->', 'true' - żeby nie wyrzuciło nas 'wyżej' jeśli ()->();() zwróci false

   % UWAGA!!! odtąd posługujemy się listą 'L1' !!!

   % chcemy ustalić, jak zmieścić tę listę na ekranie...
   tty_size(_,TtyKol), % już wiemy ile kolumn znaków zmieści się w oknie

   listLen(L1,L1Len), % L1 może mieć mniej elem od danej 'L' - mogły wypaść duplikaty przy sort.
   listStrElMaxDl(L1,_ /*ElMaxDł*/,ElMaxDlLen), % w ElMaxDł mamy Elem o stringu max dł=ElMaxDłLen

   % mając TtyKol, L1Len i StrElMaxDłLen możemy ustalić, ile elementów zmieści się w 1 wierszu
   % i ile będzie wierszy - to na potrzeby symulacji wyświetlania najpierw w kolumnach...

   % UWAGA!!!    
   % trzeba pamiętać, że do elementów listy dojdzie jeszcze 'Sep'(arator) - z zał.pojedynczy znak
   % oraz niech będzie jakiś 'zapas' między wyświetlanymi elementami 
   % ładniej wyglądają takie kolumny...
   % powiedzmy, że do dł. elementów dodamy 3 znaki (w tym 'Sep'(arator)).
   % dodatkowo szerokość jednej kolumny zaokrąglimy 'w górę' do wielokrotności powiedzmy 5 znaków 
   Zapas is 3, % min zapas/odstęp, jaki chcemy żeby był między wypisanymi elementami
               % musi być >1, bo w nim ma się mieścić też 'Sep'(arator)

   SzerWielokr is 5, % chcemy, żeby szerokość kolumny była wielokrotnością X - tu: 5

   % Krotność = zaokr w górę dzielenia dł.najdłuższego elem.z zapasem, przerz porządaną wielokrotn.
   % '1.0' w obliczeniach, żeby zablokować optymalizacje i  wymusić floaty, 
   Krotność is ceiling(1.0*(ElMaxDlLen + Zapas)/SzerWielokr), % tu ma być '/' a NIE '//'
   SzerKol is SzerWielokr * Krotność,
   ((TtyKol >= (SzerKol)) -> ( % Hurra! ekran szerszy od najszerszego elem.z zapasem i zaokr.szer.
        IlKol is TtyKol // SzerKol, % ile kol.w cał.zmieści się na ekr? (dolne zaokr //)
        true
      ) % koniec 'then' od '(TtyKol >= ElMaxDłLen) ->'
      ;
      ( % ekran jest węższy niż wymagana szerokość kolumny...
        % trudno... przyjmujemy, że ma być conajmniej 1 kolumna - niech system 'sobie radzi'
        IlKol is 1, true
      ) % koniec 'else' od '(TtyKol >= ElMaxDłLen) ->'
   ), % koniec '(TtyKol >= (SzerKol)) -> '
      % tu mamy ustaloną IlKol i SzerKol

   IlWierszy is ceiling(1.0*(L1Len)/IlKol), % tu też  ma być '/', a nie '//' - patrz 'Krotność'

   IlPólTab is (IlWierszy * IlKol),   % oczywiście musi być: IlPólTab >= L1Len

   % w tym miejscu te dane mamy ustalone:
   term_string_clever(L1Len,StrL1Len),              % il.elem listy do wyświetl.
   term_string_clever(ElMaxDlLen,StrElMaxDlLen),    % dł.elem listy o max dł.
   term_string_clever(Zapas,StrZapas),              % zapas szer (w tym separator)
   term_string_clever(SzerWielokr,StrSzerWielokr),  % czego wielokrot.ma być szer kol
   term_string_clever(Krotność,StrKrotność),        % ile x powt.powyższy 'moduł'
   term_string_clever(SzerKol,StrSzerKol),          % całk.szer 1 kolumny
   term_string_clever(IlKol,StrIlKol),              % ilość kol w oknie
   term_string_clever(IlWierszy,StrIlWierszy),      % ile wierszy 


   string_concat_many(['IlElListy=',StrL1Len,', DłMaxEl=',StrElMaxDlLen,', Zapas=',StrZapas,
       ', Szer=N*',StrSzerWielokr,', N=',StrKrotność],StrDaneLiczb1),
   piszTestInfo(true,'piszListWT',StrDaneLiczb1),

   string_concat_many(['SzerKol=',StrSzerKol,', IlośćKol=',StrIlKol,
       ', IlośćWierszy=',StrIlWierszy],StrWymiaryTabeli1),
   piszTestInfo(true,'piszListWT',StrWymiaryTabeli1),

   % gdy 'Kier'unek == true -> piszemy 'kolumnami'
   % gdy 'Kier'unek == false -> piszemy 'wierszami'
   %
   % Uwaga!
   % przy pisaniu 'wierszami' nie ma problemu z 'brakującymi elementami',
   % gdy IlWierszy*IlKolumn > DłListy (ilość elem do wypisania)
   % po prostu ostatni wiersz jest niepełny...
   %
   % przy 'logicznym' pisaniu 'kolumnami' tak naprawdę dalej wypisujemy
   % wiersze - ale może się zdarzyć, że kilka! z nich będzie niepełnych
   % (gdy logicznie to ostatnia kolumna będzie niepełna)
   % dla zachowania spójności działania kolejnych podprogramów
   % zalecane jest, by wypisywane wiersze (oprócz ostatniego), zawierały
   % tyle elementów, ile jest kolumn (dodawanie znaku \n i takie tam)
   % pomysł: 'uzupełnić' wypisywaną listę pozycjami np z jednym znakiem-np ' '
   % tak, by długość listy (ilość elem do wypisania) była = IlKolumn * IlWierszy
   % następnie tworzymy nową listę reorganizując kolejność elementów tak,
   % by 'logicznie' ukazaly się one na ekranie wypisane 'kolumnami'
   %
   
   (Kier -> ( % 'Kier uważamy za  true' -> wyświetlamy 'kolumnami'
       % musimy doprowadzić do zgodności: L1Len == IlKol * IlWierszy
       ((L1Len =< IlPólTab), % ',' - czyli traktujemy to jak 'if'
          IleBrak is IlPólTab - L1Len, % tyle elem trzeba dodać do 'L1' - być może 0
          % tworzymy listę z 'IleBrak' spacji i dołączymy ją do L1
          % btw - gdy bylo ' ', wypisywał ' ' (razem z ''),
          % teraz - jak jest " ", wypisuje zamą <spację> (bez "")
          findall(" ", between(1, IleBrak, _), L2Append2L1),
          append(L1,L2Append2L1, L1uzup), % uzupełniamy L1 do dł IlKol*IlWierszy - być może o []
          % dalej  operujemy na L1uzup
          listLen(L1uzup,L1uzupLen), 
          (testy->(
             swritef(StrPom2a,"Na wyświetlenie 'L1' przewidziano %t \c
                Kol * %t Wierszy =%t pól.\n\t\t'L1' miała dł=%t; \c
                dodano %t ' ' i teraz ma dł=%t i wygląda tak:",
             [IlKol,IlWierszy,IlPólTab,L1Len,IleBrak,L1uzupLen]),
             piszTestInfo(true,'piszLiWTab',StrPom2a),
             write_term(L1uzup,[max_depth(0)])
          );true) % koniec '(testy->('
       ), % koniec '(L1Len < IlPólTab' - sekcji uzupełniania L1 
          % o elem (' ') brakujące do ilości elem = (IlKol * IlWierszy)

       % wypisanie - teraz operujemy na L1uzup, tu ma mieć IlPólTab = IlKol * IlWierszy eleme.
       % żeby pisać ją 'wierszami' a user, żeby miał wrażenie, że było pisane 'kolumnami'
       % (zał: elem L1uzup liczone NREL=1..IlPólTab, NRK=1..IK(IlKol), NRW=1..IW(IlWierszy)
       % w 'normalnym' języku zrobiłbym to tak:
       %       for (NRW): (for (NRK): (ELEM=getNthElL(L1uzup[(k-1)*IW+w], pisz(ELEM)))
       %  wiedząc, że fukcje 'piszące' listy co IlWierszy wypisanych elementów same wstawiają '\n'

       %tutaj tworzę nową listę wstawiając do niej elem z L1uzup wybrane wg powyższego wzoru

       listReorganizuj(L1uzup, IlKol,LWy),
       piszListElWKol(LWy,IlKol,SzerKol,Jus,Sep),
       true
      ) % koniec 'then' do '(Kier ->' (czyli sekcji wyświetlania 'w kolumnach')
     ;
     ( % tu 'Kier uważamy za false' -> wyświetlamy 'wierszami'
       piszListElWKol(L1,IlKol,SzerKol,Jus,Sep),
       true
     ) % koniec 'else' do '(Kier ->' (czyli sekcji wyświetlania 'w wierszach')
   ) % koniec '(Kier ->' (wyboru, jak układać kolejne elem wyświetlanej listy)
). % koniec 'piszListWTabeli(L, Kier, RemDup, Srt, Jus, Sep)'


%
% piszListWTabeli - wreszcie funkcja/reguła wykorzystująca
% wiele powyższych pomocniczych (testy argumentów, przestawianie wierszy na kol)...
% i wypisująca elementy podanej listy wieraszami lub kolumnami
% w kolumanch o szerokości/ilości dostosowanej do okna,
% z uwzględnieniem: usuwania duplikatów/sortowania/justyfikacji/

piszListWTabeli(L, Kier, RemDup, Srt, Jus) :-piszListWTabeli(L, Kier, RemDup,  Srt, Jus,' ').
piszListWTabeli(L, Kier, RemDup, Srt)      :-piszListWTabeli(L, Kier, RemDup,  Srt, 'L',' ').
piszListWTabeli(L, Kier, RemDup)           :-piszListWTabeli(L, Kier, RemDup, true, 'L',' ').
piszListWTabeli(L, Kier)                   :-piszListWTabeli(L, Kier,   true, true, 'L',' ').
piszListWTabeli(L)                         :-piszListWTabeli(L, true,   true, true, 'L',' ').

        
panie   :- 
   piszKomunikat(jestOK, "\nLista Pań znanych bazie:\n\n", []),
   piszTerm1El(k,true,true,true,'c'),!.          % o tym user wie z helpa

panowie :- 
   piszKomunikat(jestOK, "\nLista Panów znanych bazie:\n\n", []),
   piszTerm1El(m,true,true,true,'c'),!.          % o tym user wie z helpa

osoby   :- 
   piszKomunikat(jestOK, "\nLista Osób znanych bazie:\n\n", []),
   piszTerm1El(osoba,true,true,true,'c'),!.      % o tym user wie z helpa

%rodzic-dziecko :- piszTerm1El(rodzic,true,true,true,'c'),!.

małżeństwa :- 
   piszKomunikat(jestOK, "\nLista Małżeństw znanych bazie:\n\n", []),
   piszTerm2El(małżeństwo,true,true,true,'l'),!.

rodziny :- piszKomunikat(nieOK, "\nSorry... not implemented yet :(\n\n", []).

%
% piszReguły(Narg) - wyświetla listę reguł N-argumentowych widocznych dla usera
%

piszReguły(Narg) :- (
   piszKomunikat(jestOK,
      "\nDostępne reguły z 'N' argumentami, gdzie 'N' = ~w\n\n",
      [Narg]),
   findall(T,termNarg(Narg,T),LT), piszListWTabeli(LT),!
). % end of 'piszReguły(Narg)'

%
% 'piszReguły.' - wypisuje all dostępne dla usera reguły 
% (tzn nie wpisane na listę 'regPom') z podziałem an arność
% od 0 do maxArność (def na pocz pliku - wśród flag i stałych)
%

piszReguły :- (
   maxArność(MA),
   between(0,MA,N),piszReguły(N),false
). % end of 'piszReguły'


%
% gdy 'piszKom' = 'false' ('zwykłe' używanie), po prostu zwraca 'true'
% gdy 'piszKom' = 'true', wypisuje 'InfoTestowe' i też zwraca 'true' :)
% gdy 'czyOK' = 'jestOK' (true) -> wypisuje na zielono,
% gdy 'czyOK' = "nieOK' (flse)  -> wypisuje na czerwono,
% 'stringFormat' - string formatujący wg zasad dla format/3 (ansi_format/3)
% 'listaTekst' - lista zawierająca dane do wypisania - zależne od 'stringFormat'
%                (może być pusta: [])
%

piszKomunikat(CzyOK, StringFormat, ListaTekst) :- (
    kolorStringJestOK(KolorJestOK),
    kolorStringNieOK( KolorNieOK),
    % gdy piszKom='false' to nic nie pisz... 
    (piszKom,  
    % gdy masz pisać komunikt, wybierz jego 'odcień znaczeniowy': '+' czy '-'
    (CzyOK ->(ansi_format(KolorJestOK, StringFormat,ListaTekst),!);
             (ansi_format(KolorNieOK,  StringFormat,ListaTekst)),!)
    );
    true % zwracaj zawsze true
). % koniec 'piszKomunikat'


%
% piszTestInfo - wypisuje komunikaty diagnostyczne podczas testów
% wypisanie komunikatu zależy od stanu flagi 'testy' (a ta od 'flgTesty')
% =true -> będzie komunikat, =false -> nie będzie komunikatu
%
% 'Ret' -> wartość bool, jaka ma być zwrócona - by to info diagnostyczne
%          było niezmiennikiem ciągu w którym jest:
%      - gdy w ciągu 'OR'   (średniki) - musi zwracać 'false'
%      - gdy w ciągu "AND' (przecinki) - musi zwracać 'true'
% 'Kto' -> 'string' - nazwa/skrót reguły wołającej - by  wiadomo, skąd to info
%        przewidziałem na to max 10 znaków
% 'Co'  -> 'string' - właściwy komunikat - może być bez \n - jest dodane
%       chyba nie jest to krytyczne, ale przewidziałem na to 55 znaków
% UWAGA!!! - 'kto' i 'co' muszą być w '..' (w apostrofach) - jeśli w środku,
%      (w tekście) też jest apostrof - trzeba przed nim dać '\'
%
% EDIT:
% usunąłem ogranicznie komunikatu do 55 znaków
% zmieniłem string formatujący komunikat 'Co' z '%s' na '%t'
% => może przyjmować nie tylko stringi, ale też termy...
%
% UWAGA!!! w żaden sposób nie sprawdzam przekazywanych ciągów,
% to nie jest dla usera - zakładam, że 'wiem, co robię'
%

piszTestInfo(Ret,Kto,Co):-
    ((testy -> writef("TstInfo :%12C: %t\n",[Kto,Co]);true),Ret).



%=======================================================================
%
% C3) reguły do testowania bazy
%



% czy jest zdefiniowany jakikolwiek człowiek?

czySąLudzie() :- (
   ((m(_); k(_))->
      %piszKomunikat sam sprawdza flagi 'piszKom'/'flgKom' i zwraca zawsze 'true'
      (piszKomunikat(jestOK, 
         "Tak! W bazie są zdefiniowani jacyś ludzie - czuję radość!\n",
         [])
      ) % koniec 'then' od '(m(_); k(_))->'
      ; 
      (piszKomunikat(nieOK,"Ojej... \nW bazie nie ma żadnego człowieka - \n\c
         ni mężczyzny, ni kobiety - smutek...\n",
         []),false
      ) % koniec 'else' od '(m(_); k(_))->'
   ) % koniec '(m(_); k(_))->'
). % koniec 'czySąLudzie()


% czy są jacyś ludzie zdefiniowani jako 'm' _i_ jako 'k'
% czyli 'niezdecydowani płciowo'?

czyWszyscyZdecydowani() :- (
    findall(X,(m(X),k(X)),LX), % szukaj 'niezdecydowanych'

    ((LX = []) ->    % 'then' === nie ma 'niezdecydowanych'
	 (piszKomunikat(jestOK,
            "'czyAllZdec':Tak!, wszyscy w bazie są pewni swojej płci.\n",[]))
         % 'piszKomunikat' przy okazji zwarca true
	 % koniec 'then' od '(LX = []) ->' czyli bloku, gdy brak 'niezdecydowanych'
	 ; 
         ( % tutaj w LX mamy 'niezdecydowanych płciowo' 
           % UWAGA: LX może zawierać duplikaty - 'zagregujemy je':

           listZnajdźDuplikaty(LX,D,false,true), % przy okazji sortujemy
           % tu możemy użyć 'listZnajdźDuplikaty' w ten sposób,
           % bo już wiemy, że one są (jesteśmy w 'else'testu 'LX=[]'
           % czyli wiemy, że 'listZnajdźDuplikaty' zwróci 'true'
           % (czyli nie wyrzuci na 'wyżej')
           % a tylko  chcemy poznać te duplikaty - przy okazji sortujemy...

           piszKomunikat(nieOK, 
            "'czyAllZdec':UWAGA!!! W bazie są elementy ('k' i 'm'), czyli\n\t\c
            'o niepewnej tożsamości płciowej' - niżej wdoczne jako pary:\n\t\c
            [<element>,<il.powt.w bazie>]:\t~q\n",D),

           false % zwróć 'false' jako 'kod powrotu' 'czyWszyscyZdecydowani()'
	 )  % koniec 'else' od '((LX = []) ->' czyli bloku gdy są 'niezdecydowani'
    ) % koniec '((LX = []) ->'
). % koniec czyWszyscyZdecydowani()


% czy wszyscy faceci w bazie są unikalni?
% gdy są jacyś faceci i są unikalni -> zwraca 'true'
% nie ma żadnych facetów lub są duplikaty -> zwraca 'false'

czyUnikalni :- (
   piszKomunikat(jestOK,
      "'czUnikalni': Sprawdzam unikalność wpisów na liście panów.\n",[]),
   listCzyUnikEl('m')
). % koniec 'czyUnikalni'

% i analogicznie dla kobiet:

czyUnikalne :- (
   piszKomunikat(jestOK,
      "'czUnikalne': Sprawdzam unikalność wpisów na liście pań.\n",[]),
   listCzyUnikEl('k')
). % koniec 'czyUnikalni'



czyMałżonkowieOK :- (
   piszKomunikat(jestOK,
         "'czMałżonOK': Sprawdzam, czy wszyscy mażonkowie są ludźmi.\n",[]),
   findall(X1,((małżonek(X1,_);małżonek(_,X1)),\+ osoba(X1)),LX1),
   (listCzyNiePusta(LX1,_Wyn1) ->(
         piszKomunikat(nieOK,"'czMałżonOK': Wśród małżonków są stwory \c
            nie znane mi jako ludzie:\n\t\t~q\n",[LX1])
      ) % koniec 'then' od 'listCzyNiePusta(L, Wyn) ->'
      ;
      (  piszKomunikat(jestOK,
             "'czMałżonOK': Wszyscy małżonkowie są znani jako ludzie.\n",[])
      ) % koniec 'else' od 'listCzyNiePusta(L, Wyn) ->'
   ), % koniec 'listCzyNiePusta(L, Wyn) ->'

   piszKomunikat(jestOK,
         "'czMałżonOK': Sprawdzam, czy nikt nie wziął ślubu sam ze sobą.\n",[]),
   findall(X2,małżonek(X2,X2),LX2),
   (listCzyNiePusta(LX2, _Wyn2) ->(
         piszKomunikat(nieOK,"'czMałżonOK': Wśród małżonków jest 'Supernarcyz'\n\c
            wziął ślub sam ze sobą: ~q",[LX2])
      ) % koniec 'then' od 'listCzyNiePusta(L, Wyn) ->'
      ;
      (  piszKomunikat(jestOK,
             "'czMałżonOK': Wszyscy małżonkowie pobrali się z kimś innym.\n",[])
      ) % koniec 'else' od 'listCzyNiePusta(L, Wyn) ->'
   ) % koniec 'listCzyNiePusta(L, Wyn) ->'

%findall((X,Y),małżonek(X,Y),LX1),findall((X,Y),małżonek(Y,X),LX2),append(LX1,LX2,LX12),listZnajdźDuplikaty(LX12,D,false,true), piszListWTabeli(D),false.

). % koniec 'czyMałżonkowieOK'



% 'funcDoMapL' - funkcja 'functor' przystosowana do wywołania w maplist
% wywołanie np: maplist(funcDoMapL('rodzic'),LA,LF), gdzie:
% Naz - we-nazwa termu, LA - we-lista arności uzysk.od 'findall(X,termNarg(X,Nazwa),LA),
% TWy - wy-term utworzony z nazwy i ilośći arg = arności

funcDoMapL(Naz,LA,TWy) :-functor(TWy,Naz,LA). 

funcNumbVarsDoMapL(Naz,LA,LWy) :-
    functor(TWy,Naz,LA), numbervars(TWy,0,End), LWy=[TWy,End].


% 'listCzyUnikEl(Nazwa, D)'
% pobiera Nazwę termu, wyszukuje sobie jego argumenty i zwraca:
% - true, jeśli znajdzie taki term 
%   i NIE znajdzie zduplikowanych wartości przez niego zwracanych
% - false, jeśli nie znajdzie termu
% - false, jeśli znajdzie duplikaty
% - w 'D' zwróci listę duplikatów postaci [[nazwa1, ilość1],[nazwa2,ilość2],...]
%   (jeśli  znajdzie  oczywiście)
%   przy wywołaniu D musi być nieprzypisane (ta wersja nie sprawdza tego)

listCzyUnikEl(Nazwa) :- listCzyUnikEl(Nazwa,_).

listCzyUnikEl(Nazwa,D) :- (

   set_flag(flgTestyTmp,flgTesty),  % zapamiętaj stan 'flgTesty'
   testFlagOn, % włącz, bo termNarg ma znaleźć all termy/arności - też te 'na indeksie'

   % przekazujemy nazwę, szukamy arności dla termów o danej nazwie
   % nie znajdzie termu -> zwraca []
   % np dla Nazwa ='dziecko' zwraca [2,3]
   % dla Nazwa ='m' -> [1], a np dla 'panie' -> [0]
   % 'N' - zmienna wyłącznie pomocnicza

   findall(N,termNarg(N,Nazwa),LNArg),
   % LNArg-lista liczb (N) Arności dla 'Nazwa'

   set_flag(flgTesty, flgTestyTmp), % przywróć pierwotny stan 'flgTesty'

   % w LNArg - lista arnośći - ilości argumentów termu 'Nazwa', 
   ((LNArg = []) -> % pusta - znaczy się nie znalazł takiego termu - uciekamy
      (piszKomunikat(nieOK,
         "'lCzyUnikEl': Nie znalazłem żadnych termów o nazwie:'~q'\n",
         [Nazwa]),false)  % jak nie ma nikogo, to zwróć false, czyli uciekaj
      ; % koniec 'then' od '(LNArg=[])->'
      (%term_string_clever(LNArg,StrLNArg),
      piszKomunikat(jestOK, "'lCzyUnikEl': Tak, znam term '~q' o arności ~q\n",
         [Nazwa,LNArg]),
      true
      ) % koniec 'else' od '(LNArg = []) ->'
   ), % koniec '(LNArg = []) ->'

   % tu wiemy, że LNArg niepusta - być może zawiera [0], ale niepusta

   msort(LNArg,SLNArg), % msort/2, inaczej niż sort/2 NIE usuwa duplikatów
   % wprawdzie 'msort' nie radzi sobie z polskim sortowaniem 
   % (od tego jest local_sort), ale tutaj nie o to chodzi, a msort chyba szybsze
   
   % na wejście dajemy: 'Nazwa', 
   % znalezioną wcześniej (i posortowaną) listę arności 'SLNArg'
   % otrzymujemy LTA 'List Termów/Arności' sparowanych razm:
   %     nazwy, argumentów, arności

   maplist(funcNumbVarsDoMapL(Nazwa),SLNArg,LTA),

   (testy-> (write("LTA="),writeq(LTA),nl);true),
   % teraz w 'LTA' (Lista Termy-Arności)
   % mamy listę list (par): [[T1,N1], [T2,N2],...]
   % gdzie np:T1=dziecko(A,B),N1=2; T2=dziecko(A,B,C),N23
   % te T(ermy) można teraz wykorzystać w różny sposób:
   % przekszałcać na listy / atomy itd....
   % m.in. komendą: T=.. LTA,


   % uporaliśmy się z wyznaczaniem nazwy/arności termów
   % teraz przychodzimy po same dane do sprawdzenia...

   findall(X,call(Nazwa,X),LX),

   % teraz w 'LX' - lista info szukanych do sprawdzenia

   

   (listZnajdźDuplikaty(LX,D1) -> ( % 'then' gdy są jakieś  powtórzenia
      piszKomunikat(nieOK,
         "'lCzyUnikEl': Term '~w' zwraca duplikaty [<powtórzony wpis>,<ile razy>]:\n",
         [Nazwa]),
      swritef(StrD1,'\t\t%t\n',[D1]), piszKomunikat(nieOK,StrD1,[]),
      piszKomunikat(jestOK,
         "'lCzyUnikEl': Jeśli zduplikowane są tylko 'dane testowe'\n",[]),
      piszKomunikat(jestOK,"\t\tczyli osoby 'ktoś...' i ich relacje,\n",[]),
      piszKomunikat(jestOK,
         "\t\tto możesz je usunąć komendą 'testuj(false).',\n",[]),
      piszKomunikat(nieOK,
         "\t\ta wpisy dot.innych osób/rel.musisz usunąć samodzielnie.\n",[]),
         (var(D) -> (% parametr 'D' jest wolną zmienną-możemy zwrócić listę dupl.
            D=D1   % listę znalezionych duplikatów przekazujemy 'wyżej'
            ) % koniec 'then' od 'var(D) ->'
            ;
            (
               piszKomunikat(nieOK,"'lCzyUnikEl': Niestety nie mogę ich przekazać:\n",[]),
               piszKomunikat(nieOK,"'lCzyUnikEl': 'D' nie jest zmienną wolną.\n",[])
            )  % koniec 'else' od 'var(D) ->'
         ), % koniec 'var(D) ->'
         false % skoro są duplikaty, to 'listCzyUnikEl' zwraca 'false'
      ) % koniec 'then' od 'listCzyNiePusta(D1) ->'
      ;
      (
         piszKomunikat(jestOK,"'lCzyUnikEl': Term '~q' zwraca unikalne wartości.\n",
             [Nazwa]),
         true % nie ma duplikatów -> 'listCzyUnikEl' zwraca true
      ) % koniec 'else' od 'listCzyNiePusta(D1) ->'
   ) % koniec 'listCzyNiePusta(D1) ->'
). % koniec 'listCzyUnikEl'



% testy na człowieczeństo - gdy przekazujemy konkretną nazwę
% typu 'ela', 'ala', 'karol', 'tomek'
% to zwraca true / false (gdy false, dodatkowo komunikat)
% a wyrażenie czyCzłowiek(X) zwraca 'true', gdy są  zdefiniowane
% jakiekolwiek kobiety / jacykolwiek mężczyźni
% a 'false', gdy nie zdefiniowano (żadnych) k(..) / m(..)

czyCzłowiek(X) :- (czySąLudzie(),
   (var(X)->(
         piszKomunikat(nieOK,
            "'czyCzłowiek': No tak... człowiek... ale który?",[]),
         false
      )% koniec 'then' 'var(X)->'
      ;
      (true
      ) % koniec 'else' 'var(X)->'
   ), % koniec 'var(X)->'
                                  
   (człowiek(X)-> (
        piszKomunikat(jestOK,
           "'czyCzłowiek': Tak! Jest mi znany fakt, że '~w' jest człowiekiem!\n",
           [X|[]]),!,true
      ) % koniec 'then' 'człowiek(X)->'
      ; 
      (piszKomunikat(nieOK,
          "Niestety, '~w' nie jest mi znany/a ani jako kobieta, ani mężczyzna!\n",
          [X|[]]),!,false
      ) % koniec 'else' 'człowiek(X)->'
   ) % koniec 'człowiek(X)->'
). % koniec 'czyCzłowiek()'


% zwraca true, jeśli X jest zdefiniowany 
% tylko jako m, albo tylko jako k (mężczyzna albo kobieta).

czyZdecydowanaPłeć(X) :- czyCzłowiek(X),
   ((m(X) exor k(X))->
   (piszKomunikat(jestOK,
      "Tak! '~w' ma tylko jedną płeć..., czyli nie jest źle...\n",
      [X|[]]),true),!,true; % koniec częsci 'then'
   (piszKomunikat(nieOK, 
      "UWAGA!!!,\n'~w' w bazie jest jako K i M jednocześnie!\n\c
      Czyli ma problemy z tożsamością płciową...\n",
      [X|[]]),false),!,false
).

czyDobryNaRodzica(X) :- (czyZdecydowanaPłeć(X) ->
    (piszKomunikat(jestOK,
        "Tak! '~w' - jesteś człowiekiem zdecydowanym co do swojej płci.\n",
        [X|[]]),
    !,true); % koniec części 'then' pytania o zdecydowaną płeć
    (piszKomunikat(nieOK, "Sorry '~w'!\n\c
        Osoby nieznanie lub o nieustalonej tożsamości płciowej\n\c
        nie nadają się na rodziców...\n",
        [X|[]]),
    !,false)), % koniec  'else' pytania o zdecydowaną płeć i całego pytania
    (rodzic(X,_) ->
         (piszKomunikat(jestOK,
              "Brawo '~w'!\nJak widzę już jesteś rodzicem. GRATULUJĘ.\n",
              [X|[]]),
         !,true); % koniec części 'then' pytania o bycie już rodzicem
         (piszKomunikat(jestOK,
            "Hej '~w'!\nWidzę, że jeszcze nie masz dzieci,\n\c
            ale masz szanse być rodzicem w przyszłości.\n",
            [X|[]]),
         !,true) % koniec części 'else' pytania o bycie już rodzicem
). % koniec pytania o bycie już rodzicem i całej formuły 'czyDobryNaRodzica'


czyDobryNaOjca(X) :- czyDobryNaRodzica(X), (m(X) ->
    (piszKomunikat(jestOK,
        "Tak! '~w' - nadajesz się, tylko bądź dobrym ojcem.\n",
        [X|[]]),!,true); % koniec 'then' pytania o płeć
    (piszKomunikat(nieOK, 
        "Hej '~w'!\nZastanów się! Jesteś kobietą - NIE możesz być ojcem.\n",
        [X|[]]),!,false) % koniec 'else' pytania o płeć i całej formuły
).


czyDobraNaMatkę(X) :- czyDobryNaRodzica(X), (k(X) ->
    (piszKomunikat(jestOK, 
        "Tak! '~w' - nadajesz się, tylko bądź dobrą matką.\n",
        [X|[]]),!,true); % koniec 'then' pytania o płeć
    (piszKomunikat(nieOK, 
        "Hej '~w'!\nZastanów się! Jesteś mężczyzną - NIE możesz być matką.\n",
    [X|[]]),!,false) % koniec 'else' pytania o płeć i całej formuły
).


%=======================================================================
%
% reguł z grup C2), C3) (czyli tych powyżej tego miejsca)
% NIE wyświetlimy użytkownikowi (tylko w fazie testów)
% nie dotyczą bezpośrednio logiki bazy - pełnią rolę  pomoczniczą/testową
% my o nich wiemy, a user nie musi - jak zajrzy, to na własną odpowiedzialność
%
% poniżej lista termów (atomów i reguł), które w 'zwykłej' fazie prolog ma
% 'ukryć' przed użytkowniekiem - nie wyświetlać wśród dostępnych komend
% jako ukryte NIE są też sprawdzane przez formułę 'osobyWRel'


% grupa termów związanych z rozruchem i testami, własny operator itp

regPom(startuj).   % używane 'wewnętrznie' do  startu bazy i ustawienia flag
regPom(go).        % odmiany 'wzywania helpa' - są podane w helpie, też w jego
regPom(helpme).      % wersji 'skróconej' - wyświetlanej gdy wył.komunikaty
regPom(pomoc).
regPom(pomocy).
regPom(run).

regPom(plikNazwaPełna). % nazwa 'ścieżkowa' tego pliku - do szukania
                        % zdefiniowanych tu rzeczy: atomów / formuł
regPom(spc).
regPom(przec).
regPom(średn).
regPom(tab).
regPom(beep).
regPom(jestOK).
regPom(nieOK).
regPom(albo).
regPom(exor).
regPom(spc).
regPom(maxArność).
regPom(functorDoMaplist).
regPom('__aux_maplist/3_atom_chars+0').


% zmienne konfiguracyjne - pogranicze rozruchu i wyświetlania komunikatów

regPom(testy).   % term związany z flgTesty - zostały testy/0, /1->testuj/1
regPom(piszKom). % term związany z flgKom
regPom(testFlagOFF).
regPom(testFlagOff).
regPom(testFlagON).
regPom(testFlagOn).
regPom(daneTestowe).
regPom(testuj).


% grupa termów związanych z wyświetlaniem komunikatów, kolorami itp

regPom(clear_screen).
regPom(kolorStringBold1).
regPom(kolorStringBold2).
regPom(kolorStringJestOK).
regPom(kolorStringNieOK).
regPom(kolorStringNorm).

regPom(separatorPreferredChars).
regPom(justifyCenterTag).
regPom(justifyRightTag).
regPom(justifyLeftTag).
regPom(piszKom).
regPom(piszKomunikat).
regPom(piszTestInfo).


% termy z pogranicza - wyświetlania i obsługi list

regPom(piszListWTabeli).
regPom(piszListElWKol).
regPom(piszListElWKolPom).
regPom(piszListElWKolTestL).
regPom(piszListElWKolTestJus).
regPom(piszListElWKolTestKolSzer).
regPom(piszListElWKolTestSep).


regPom(piszTerm1El).
regPom(piszTerm2El).
regPom(term_string_clever).
regPom(string_concat_many).
regPom(listStrElMaxDl).
regPom(listReorgIndx).
regPom(listReorganizuj).
regPom(listyPrzodków).
regPom(listaRodziców).
regPom(listyPotomków).
regPom(listaDzieci).
regPom(liczbaPotomków).
regPom(liczbaPrzodków).
regPom(listaDrógDoKorzeni).
regPom(listaDrógOdKorzeni).
regPom(drogaCzłDoKorzenia).
regPom(drogaCzłDoLiścia).
regPom(listaDrógDoLiści).
regPom(listaDrógOdLiści).
regPom(listaWspólnychDzieci).
regPom(dystans).     % jeszcze nie zrobiona reguła
regPom(rodzinaMała). % jeszcze nie zrobiona reguła


% termy pomocnicze dotyczące obsługi list

regPom(funcNumbVarsDoMapL).
regPom(funcDoMapL).
regPom(listCzyUnikEl).
regPom(listDodaj).
regPom(listDodajGdyBrak).
regPom(listElem).
regPom(listCzyNiePusta).
regPom(listLen). % są 2 wersje: listLen/2, listLen/3
regPom(listLen1).
regPom(listLiczElemN).
regPom(listZnajdźDuplikaty).
regPom(localeSortAll).


% termy z pogranicza obsługi list i właściwej logiki bazy

regPom(atomNarg).
regPom(regułaNarg).
regPom(termNarg).
regPom(regPom).
regPom(daneTestowe).
regPom(piszReguły).


% termy - reguły dot.testowania spójności bazy
% uznałem, że można pokazać je userowi -> są wyświetlane wśród
% dostępnych reguł też w 'zwykłej' fazie (nie-testów)
% nie umożliwiają 'grzebania' w bazie, tylko pokazują jej stan
% jeśli zechcę je ukryć przed userem - wystarcz 'odkomentować'

regPom(czyCzłowiek).
regPom(czyDobraNaMatkę).    
regPom(czyDobryNaOjca).
regPom(czyDobryNaRodzica).
regPom(czyMałżonkowieOK).
regPom(czySąLudzie).
regPom(czyUnikalni).
regPom(czyUnikalne).
regPom(czyWszyscyZdecydowani).
regPom(czyZdecydowanaPłeć). 
regPom(czyRelacjeOsób). % jeszcze nie zrobiona reguła


% termy dotyczące danych w bazie, o których user ma podane 'na tacy'
% info w helpie - i nie musi ich samodzielnie szukać w spisach...
% np te bez parametrów, które najprościej użyć,
% albo te, które mają parametry, ale są uproszczonymi 'nakładkami'
% na dające większe możliwości, ale trudniejsze w użyciu wersje...
% dopóki nie wie, o co chodzi, niech ich sam nie szuka - i tak nie wykorzysta

%regPom(osoba).
%regPom(człowiek).
%regPom(k).
%regPom(m).

regPom(osoby).    % jest info w helpie - 'nakładka' na 'człowiek' / 'osoba'
regPom(panie).    % jest info w helpie - 'nakładka' na 'k'
regPom(panowie).  % jest info w helpie - 'nakładka' na 'm'
regPom(małżeństwa).
regPom(osobyWRel).
regPom(piszOsobyWRel).





%=======================================================================
%
% B) 'koligacje rodzinne' - reguły istotne dla logiki bazy
%


%=======================================================================
%
% przypomnienie: 
% 'pierwotne' (definiowane przez fakty/przykłady) są:
%
%   m(X), k(X), rodzic(X,Y), małżonek(X,Y)
%
%   np m('Adam K'), k('Marta S'), 
%   rodzic('Adam K','Kaśka K'), rodzic('Hanka K','Magda K').
%
%
% wszystkie inne realcje rodzinne są definiowane poniżej 
% jako 'relacje pochodne' - wynikające z tamtych:
%





%=======================================================================
%
% B1) relacje pokrewieństwa
%

%% UWAGA!!! chyba lepiej jest robić zapytania ',' zamiast ';'
%% dlatego przerobilem m.in.: babcia,  dziadek, dziadkowie
%% chodzi o prologowe 'nawroty/powroty' - wydajność zapytań itd
%% reguły z ',' szybciej stają się 'false' i nie trzeba szukać dalej...


%
% zapytanie 'ogólne', np: m(X) zwróci listę osób spełniających tę relację
% zapytanie 'szczeółowe', np: m('Asia SK') zwróci 'true'/'false'
% w zależności, czy dana osoba spełnia tę relację/regułę
%

człowiek(X)     :- m(X);k(X).       
osoba(X)        :- człowiek(X).     
                                    
                                    

%
% ad.'ojciec' - 1sza reguła:
% jak ktoś (Y) jest osobą i mamy daną lub znajdziemy
% drugiego kogoś (X), kto jednocześnie jest facetem i rodzicem (Y),
% to znaczy, że TO JEST ojciec (Y) i nie ma sensu szukać innego
% dlatego możemy dać '!' (tzw.odcięcie).
% Jeśli jest jakiś inny ojciec, to jest to błąd danych w bazie
% i powinine być wychwycony na wcześniejszych testach...
%
% ad.'ojciec' - 2ga reguła:
% jak ktoś (Y) jest osobą, to na pewno ma/miał/a ojca,
% co najwyżej my go nie znamy - czyli dla nas ten ojciec jest 'NN'
%
% ad.'ojciec' - 3cia reguła:
% jak ktoś (X) jest facetem i pytamy, czy ma dzieci,
% to jeśli ich nie znamy, to może ma,  może nie ma...
% w każdym razie dla nas jest bezdzietny - czyli 'false'
% (inna sytuacja niż 'w drugą stronę' - przy pytaniu o ojca...
%
% ad.'ojciec' - 4ta reguła:
% no i 'przypadek ogólny' - gdy obie zmienne są 'nieskonkretyzowane'
% - szukamy dalej...
% 

ojciec(X,Y)     :- (osoba(Y)->(rodzic(X,Y),m(X))),!,rodzic(X,Y).  
ojciec(X,Y)     :- \+ (rodzic(X,Y),m(X)), osoba(Y),var(X),X='NN'. 
ojciec(X,Y)     :- \+ (rodzic(X,Y),m(X)), m(X),var(Y),false.      
ojciec(X,Y)     :- rodzic(X,Y),m(X).                              


%
% ad.'matka' - reguła 1sza:
% jak ktoś (Y) jest osobą i mamy daną lub znajdziemy drugiego kogoś (X),
% kto jednocześnie jest kobietą 'k(X)' i 'rodzic(Y)',
% to znaczy, że (Y) TO JEST matka i nie ma sensu szukać innej
% dlatego możemy dać '!' (tzw.odcięcie).
% Jeśli jest jakaś inna matka, to jest to błąd danych w bazie
% i powinine być wychwycony na wcześniejszych testach...
%
% ad.'matka' - reguła 2ga:
% jak ktoś (Y) jest osobą, to na pewno ma/miał/a matkę,
% co najwyżej my jej nie znamy - czyli dla nas ta matka jest 'NN'
%
% ad.'matka' - reguła 3cia:
% jak ktoś (X) jest kobietą i pytamy, czy ma dzieci,
% to jeśli ich nie znamy, to może ma, może nie ma...
% w każdym razie dla nas jest bezdzietna - czyli 'false'
% (tu inna sytuacja niż 'w drugą stronę' - przy pytaniu o matkę...
%
% ad.'matka' - reguła 4ta:
% no i 'przypadek ogólny' - gdy obie zmienne są 'nieskonkretyzowane'
% szukamy dalej...

matka(X,Y)     :- (osoba(Y)->(rodzic(X,Y),k(X))),!,rodzic(X,Y).   
matka(X,Y)     :- \+ (rodzic(X,Y),k(X)), osoba(Y),var(X),X='NN'.  
matka(X,Y)     :- \+ (rodzic(X,Y),k(X)), k(X),var(Y),false.       
matka(X,Y)     :- rodzic(X,Y),k(X).                               


%
% rodzice(X,Y,Z) oznacza, że     
% (X,Y) to rodzice 'Z' (X-ojciec, Y-matka)
%
% dla danej osoby (Z), jak znajdziemy ojca i matkę,
% to nie trzeba szukać dalej... można dać '!' (cut)
%
%rodzice(X,Y,Z)  :- (osoba(Z),ojciec(X,Z),matka(Y,Z),!).
rodzice(X,Y,Z)  :- ojciec(X,Z),matka(Y,Z).


%
% w drugą stronę: dziecko(X,Y,Z) oznacza:
% 'X to dziecko (Y,Z) (Y-ociec, Z-matka)
%
dziecko(X,Y)    :- rodzic(Y,X).  
dziecko(X,Y,Z)  :- rodzice(Y,Z,X).

syn(X,Y)        :- m(X),dziecko(X,Y).
córka(X,Y)      :- k(X),dziecko(X,Y).
syn(X,Y,Z)      :- m(X),dziecko(X,Y,Z).
córka(X,Y,Z)    :- k(X),dziecko(X,Y,Z).


%
% gdy znamy tylko jednego rodzica, uznajemy 2 dzieci za rodzeństwo
% (kredyt zaufania, że ich drugi rodzic jest ten sam...)
% natomiast NIE uznajemy za rodzeństwo osób,
% które OBOJE rodziców  mają 'NN'
% gdybyśmy ich też uznali za rodzeństwo, to 'z automatu'
% wszycy 'ludzie korzenie' (których rodziców nie znamy)
% byliby uznani za rodzeństwo - a to bzdura...
% 

rodzeństwo(X,Y) :- osoba(X), osoba(Y), (X \= Y),
                   dziecko(X,O1,M1), dziecko(Y,O2,M2),
                   O1=O2, M1=M2,\+ (O1='NN', M1='NN').

%
% w brat/siostra nie ma testu, czy to różne osoby,
% bo 'rodzeństwo' już zawiera test, czy X i Y to różne osoby
%

brat(X,Y)       :- m(X),rodzeństwo(X,Y). 
siostra(X,Y)    :- k(X),rodzeństwo(X,Y).


rodzeństwoPrzyrodnie(X,Y) :- osoba(X), osoba(Y), (X \= Y),
            dziecko(X,O1,M1),dziecko(Y,O2,M2), 
% dla żadnej z testowanych osób nie pozwalamy, by oboje rodzice byli 'NN'
            \+ (O1='NN', M1='NN'), \+ (O2='NN', M2='NN'), 
% warunki powyżej są w koniunkcji z poniższą alternatywą
% ona sprawdza, czy jeden z rodziców X,Y, jest ten sam, a drugi różny
% ale ci, co są tacy sami, to NIE mogą być 'NN'
            (((O1 = O2),\+ O1='NN',( M1 \= M2))
            ;
            ((M1=M2),\+M1='NN',(O1\=O2))). 

bratPrzyrodni(X,Y)     :- m(X), rodzeństwoPrzyrodnie(X,Y).
siostraPrzyrodnia(X,Y) :- k(X), rodzeństwoPrzyrodnie(X,Y).

/*
  TO DO - dokończyć sensownie
%
% 'rodzinaMała' = rodzice (niekoniecznie małżonkowie + wspólne dzieci)
%
% wejście: O, M - ojciec/matka - żadne (szuka all par) lub jedno lub oboje
% wyjście: LD - lista wspólnych dzieci, LR - lista rodziców,
% LRD - lista złożona z: pary rodziców i listy dzieci

% TO DO - dokończyć sensownie - na wyjściu ma być lista,
% którą da się wypisać przez piszListWTabeli

rodzinaMała(R1,R2,LR,LD,LRD) :-
    % najpierw ustalamy, czy O i M mają jakieś wspólne dzieci
    % zał.: O - ojciec, M - matka
    (rodzice(R1,R2,_);rodzice(R2,R1,_)),
    % już wiemy,że są wspólne dzieci - ustalamy, kto ojciec, kto matka
    ((m(R1), O=R1, M=R2);(m(R2),O=R2,M=R1)),
    findall(D,(ojciec(O,D),matka(M,D)),LD),
    % w LD powinna być lista wspólnych dzieci
    LR=(O,M), LRD1 =[(LR,LD)], sort(LRD1,LRD).
*/


    

babciaOdMatki(X,Y)    :- matka(M,Y),matka(X,M).
babciaOdOjca(X,Y)     :- ojciec(O,Y), matka(X,O).
babcia(X,Y)           :- rodzic(R,Y),matka(X,R).                 


dziadekOdMatki(X,Y)   :- matka(M,Y), ojciec(X,M).
dziadekOdOjca(X,Y)    :- ojciec(O,Y),ojciec(X,O).
dziadek(X,Y)          :- rodzic(R,Y),ojciec(X,R).               

%
% 'dziadkowie/2' zwraca 'pojedynczo' dziadków i babcie osoby Y
%

dziadkowie(X,Y)         :- rodzic(R,Y),rodzic(X,R).

%
% a 'dziadkowie/3' zwraca już 'parami' - grupując wg rodziców
% tak lepiej, niż gdyby wyświetlał 'matkę ojca' w parze z 'ojcem matki'
% jeśli znamy rodzica, a nie znamy dziadków, wyświetla w tej parze 'NN'
% (odpowiadają za to moje definicje ojciec/matka
% natomiast jeśli nie znamy żadnego z rodziców osoby Z, to wyświetla 'false'
%

dziadkowie(X,Y,Z)       :- rodzic(R,Z),ojciec(X,R),matka(Y,R). 


% 'wnuk/2' - chłopak X będący wnukiem osoby Y (Y to każdy/a dziadek/babcia)

wnuk(X,Y)           :- m(X),dziadkowie(Y,X).


% dla 'wnuk/3' jest: 'X' to wnuk (chłopak) dziadka Y i babci Z

wnuk(X,Y,Z)         :- m(X),dziadkowie(Y,Z,X).


% 'wnuczka/2' i 'wnuczka/3' - analogicznie jak dla wnuka, tylko dziewczyna

wnuczka(X,Y)        :- k(X),dziadkowie(Y,X).
wnuczka(X,Y,Z)      :- k(X),dziadkowie(Y,Z,X).


% 'wnuczę/2', 'wnuczę/3' - bez sprecyzowania płci wnuczęcia

wnuczę(X,Y)         :- dziadkowie(Y,X).                  
wnuczę(X,Y,Z)       :- dziadkowie(Y,Z,X).
wnuczęta(X,Y)       :- wnuczę(X,Y).
wnuczęta(X,Y,Z)     :- wnuczę(X,Y,Z).


% w rodzeństwie już jest sprawdzenie \+ (R1=R2).
% w 'kuzyni/2' i 'kuzynostwo/2' płeć obojętna

kuzyni(X,Y)         :- rodzic(R1,X),rodzic(R2,Y),rodzeństwo(R1,R2).
kuzynostwo(X,Y)     :- kuzyni(X,Y).


% tu szukamy X, który jest chłopakiem (kuzyn) lub dziewczyną (kuzynka)
% osoby Y (płeć Y obojętna)

kuzyn(X,Y)          :- m(X),kuzyni(X,Y).
kuzynka(X,Y)        :- k(X),kuzyni(X,Y).


% wuj to brat matki, ale też mąż siostry rodzica  

wuj(X,Y)            :- matka(M,Y),brat(X,M).                
wuj(X,Y)            :- rodzic(R,Y), siostra(C,R),mąż(X,C). 
wujek(X,Y)          :- wuj(X,Y).


% a stryj to już tylko 'brat ojca'

stryj(X,Y)          :- ojciec(O,Y),brat(X,O).
stryjek(X,Y)        :- stryj(X,Y).


% ciotka to siostra rodzica, ale też żona brata rodzica

ciotka(X,Y)         :- rodzic(R,Y),siostra(X,R).            
ciotka(X,Y)         :- rodzic(R,Y),brat(B,R),żona(X,B).     
ciocia(X,Y)         :- ciotka(X,Y).


pradziadek(X,Y)     :- rodzic(R,Y),dziadek(X,R).
prababcia(X,Y)      :- rodzic(R,Y),babcia(X,R).

pradziadkowie(X,Y)  :- rodzic(R,Y),dziadkowie(X,R).                 


% tradycyjnie: X - pradziadek, Y - prababcia dla Z

pradziadkowie(X,Y,Z) :- rodzic(R,Z), dziadkowie(X,Y,R).


% i prapra...

prapradziadkowie(X,Y,Z) :-dziadkowie(X,Y,D),dziadkowie(D,Z).


% 'prawnuczę', 'prawnuczęta' - bez sprawdzania płci
% dla '../3': X to prawnuczę dla  pradziadka Y i parabaci Z

prawnuczę(X,Y)      :- pradziadkowie(Y,X).
prawnuczę(X,Y,Z)    :- pradziadkowie(Y,Z,X).
prawnuczęta(X,Y)    :- prawnuczę(X,Y).
prawnuczęta(X,Y,Z)  :- prawnuczę(X,Y,Z).


% tu tylko chłopacy

prawnuk(X,Y)        :- m(X), prawnuczę(X,Y).
prawnuk(X,Y,Z)      :- m(X), prawnuczę(X,Y,Z).


% tu tylko dziewczyny

prawnuczka(X,Y)     :- k(X), prawnuczę(X,Y).
prawnuczka(X,Y,Z)   :- k(X), prawnuczę(X,Y,Z).


% nie rozróżniam płci-nie znam 'przodkini'
% X jest przodkiem dla Y
% jak widać, def rekurencyjna

przodek(X,Y)        :- rodzic(X,Y). 
przodek(X,Y)        :- rodzic(X,P), przodek(P,Y).
przodkowie(X,Y)     :- przodek(X,Y).


% alternatywne nazwy przodków

antenat(X,Y)        :- przodek(X,Y).   
antenaci(X,Y)       :- antenat(X,Y).
ascendent(X,Y)      :- przodek(X,Y). 
ascendenci(X,Y)     :- ascendent(X,Y).

wstępni(X,Y)        :- przodkowie(X,Y).


% i z podziałem na panów/panie:

wstępny(X,Y)        :- m(X), przodek(X,Y).
wstępna(X,Y)        :- k(X), przodek(X,Y).


% nie rozróżniam płci-nie znam 'potomkini'

potomek(X,Y)        :- przodek(Y,X). 
potomkowie(X,Y)     :- potomek(X,Y).


% alternatywne nazwy potomków

descendent(X,Y)     :- potomek(X,Y).
descendenci(X,Y)    :- descendent(X,Y).


zstępni(X,Y)        :- potomkowie(X,Y).

% i z podziałem na panów/panie:

zstępna(X,Y)        :- k(X), potomek(X,Y).
zstępny(X,Y)        :- m(X), potomek(X,Y).


% X jest siostrzeńcem/icą dla Y

siostrzeńcy(X,Y)  :- matka(M,X), siostra(M,Y), M \='NN'.  


% i z podziałem na płeć:

siostrzeniec(X,Y) :- m(X), siostrzeńcy(X,Y).
siostrzenica(X,Y) :- k(X), siostrzeńcy(X,Y).


% X jest bratankiem/icą dla Y

bratankowie(X,Y)  :- ojciec(O,X), brat(O,Y), O \='NN'.


% i z podziałem na płeć:

bratanek(X,Y)     :- m(X), bratankowie(X,Y).
bratanica(X,Y)    :- k(X), bratankowie(X,Y).



%
% człowiek liść nie ma w bazie danych o dzieciach
% znalezienie all 'ludzi liści', lub sprawdzenie, 
% czy dany człowiek 'jest liściem'
%

człowiekLiść(X)    :- człowiek(X), \+rodzic(X,_).


%
% człowiek korzeń nie ma w bazie danych o rodzicach
% znalezienie all 'ludzi korzeni', lub sprawdzenie, 
% czy dany człowiek 'jest korzeniem'
%

człowiekKorzeń(X)  :- człowiek(X), \+rodzic(_,X).      


%
% człowiek, dla którego nie mamy w bazie danych
% ani o potomkach, ani o przodkach - np 'Janina S'
% w tej wersji bazy nie da się zdefiniować 'rodzeństwa'
% bez danych o wspólnych rodzicach - potrzebne są
% chociaż takie dane: 'to rodzic adama i pawła NN'
%

człowiekBezKrewnych(X) :- człowiekLiść(X), człowiekKorzeń(X). 


% X to dla Y taki _przodek_,
% którego żadnego z rodziców nie ma w bazie

przodekKorzeń(X,Y) :- człowiekKorzeń(X),przodek(X,Y).



%
% jaki X jest korzeniem dla Y
% jeśli nie  mamy info o rodzicach Y,
% to sam Y jest korzeniem
%

korzeń(X,Y) :- człowiekKorzeń(X),(X=Y).
korzeń(X,Y) :- przodekKorzeń(X,Y).


%
% X to dla Y taki potomek, którego żadnych dzieci nie ma w bazie
%

potomekLiść(X,Y) :- człowiekLiść(X), potomek(X,Y).   

%
% jaki X jest liściem dla Y
% jeśli nie mamy info o dzieciach Y,
% to sam Y jest liściem
%

liść(X,Y) :- człowiekLiść(X),(X=Y).
liść(X,Y) :- potomekLiść(X,Y).


%
% UWAGA!!! poniżej tylko ostatni argument: LXK jest / ma być listą
%

%
% UWAGA 2 !!! w 'drogaCzłDoKorzenia' i 'listaDrógDoKorzeni'
% trochę inaczej niż zwykle - to dany człowiek jest 1szym argumentem,
% a nie jego korzeń/korzenie
%

drogaCzłDoKorzenia(X,K,LXK) :- \+ człowiek(X), LXK =[], K =false.
drogaCzłDoKorzenia(X,K,LXK) :- człowiek(X), \+ rodzic(_,X),
                               LXK=[X|[]], K=X.
drogaCzłDoKorzenia(X,K,LXK) :- człowiek(X), rodzic(R,X), % R jak rodzic
                               LXK =[X|LXK1], K=K1,
                               drogaCzłDoKorzenia(R,K1,LXK1). 

% tutaj tylko interesuje nas, czy jest, nie odczytujemy wyznaczonej drogi
drogaCzłDoKorzenia(X,K)     :- drogaCzłDoKorzenia(X,K,_). 



%
% UWAGA!!! tutaj  drugi I trzeci argument są / mają być listami!!!
% wejście:
%    X - osoba, dla której dróg do korzeni szukamy
%    LK => lista 'korzeni', do których dróg chcemy szukać
%        LK = lista konkretnych korzeni => LDK = lista dróg do nich
%        LK = [] lub '' lub "" => LDK =[], 
%        LK ='_' => LDK = drogi do wszystkich korzeni
%        LK = Y (zmienna niezwiązana) => LDK = lista dróg do all korzeni,
%             dodatkowo Y jest WY i = lista znanych korzeni
% wyjście:
%    LDK - lista dróg od osoby X do jej 'korzeni' - patrz opis WE wyżej
%        każdy element LDK ma postać:
%        (X, K, ListElemLDK=[lista osób od X do K razem z nimi]).
%


%
% dla 'pustych' X/osób nie mamy czego szukać...
% także na razie nawet nie sprawdzamy K
%

listaDrógDoKorzeni([],_K,LDK) :- LDK =[],!.
listaDrógDoKorzeni('',_K,LDK) :- LDK =[],!.
listaDrógDoKorzeni("",_K,LDK) :- LDK =[],!.

% tę część wykonujemy, gdy 2gi param jest 'niezwiązaną zmienną'
% wtedy w LK zwracamy listę korzeni, 
% a w LDK listę dróg do tych korzeni

listaDrógDoKorzeni(X,LK,LDK) :- var(LK),
   findall(K,korzeń(K,X),LK),
   findall((X,K,LXK),drogaCzłDoKorzenia(X,K,LXK),LDK),!.

     
% tę część wykonujemy, gdy  LK jest listą pustą
% odpłacamy 'pięknym za nadobne'
     
listaDrógDoKorzeni(_X,[],LDK) :- LDK = [],!.


% tę część wykonujemy, gdy  LK jest niepustą listą korzeni

listaDrógDoKorzeni(X,LK,LDK) :- is_list(LK),length(LK,N),N>0,
   findall((X,K,LXK),(member(K, LK),drogaCzłDoKorzenia(X,K,LXK)),LDK).


% a tę, gdy przekazany K NIE jest listą,
% tylko np pojedynczym korzeniem

listaDrógDoKorzeni(_X,'',LDK) :- LDK=[],!.
listaDrógDoKorzeni(_X,"",LDK) :- LDK=[],!.
listaDrógDoKorzeni(X,K,LDK) :- atomic(K),
   findall((X,K,LXK),drogaCzłDoKorzenia(X,K,LXK),LDK).


listaDrógDoKorzeni(X,LDK) :- listaDrógDoKorzeni(X,_,LDK).





%
% listaDróg ~O~D~ korzeni - teraz korzeń/nie K są 1szym arg.
%

% kazdy element LOK ma mieć postać: (K, X, reverse(ListElemLDK)).
% tutaj K może być listą, a X - człowiekiem
listaDrógOdKorzeni(K,X,LOK) :- (listaDrógDoKorzeni(X,K,LDK), 
    ((LDK=[]) -> ( LOK =[]              
        ) % end of 'then' of'LDK=[]'    
        ;(                              
            maplist([IN,OUT] >> (
                    IN=(Xi,Ki,LDKi), % rozłożyliśmy 'IN' na 'czynniki pierwsze'
                    reverse(LDKi,LOKi),  % odwracamy listę osób Xi <-> Ki
                    OUT=(Ki,Xi,LOKi)), % end of 'lambda function'
                LDK,LOK
            ) % end of 'maplist'
        ) % end of 'else' of'LDK=[]'
    ) % end of 'LDK=[]'
). % end of 'listaDrógOdKorzeni(K,X,LOK) :-'

listaDrógOdKorzeni(X,LOK) :- listaDrógOdKorzeni(_,X,LOK).


% UWAGA!!! poniżej tylko ostatni arg - LXL jest / ma być listą!!!
drogaCzłDoLiścia(X,L,LXL) :- \+ człowiek(X), LXL =[], L=false.
drogaCzłDoLiścia(X,L,LXL) :- człowiek(X), \+ rodzic(X,_), LXL=[X|[]], L=X.
drogaCzłDoLiścia(X,L,LXL) :- człowiek(X), rodzic(X,P), LXL =[X|LXL1], L=L1, drogaCzłDoLiścia(P,L1,LXL1). % P jak potomek
drogaCzłDoLiścia(X,L)   :- drogaCzłDoLiścia(X,L,_).

%
% dla 'pustych' X/osób nie mamy czego szukać...
% także na razie nawet nie sprawdzamy K
%

listaDrógDoLiści([],_L,LDL) :- LDL =[],!.
listaDrógDoLiści('',_L,LDL) :- LDL =[],!.
listaDrógDoLiści("",_L,LDL) :- LDL =[],!.

% tę część wykonujemy, gdy 2gi param jest 'niezwiązaną zmienną'
% wtedy w LL zwracamy listę liści, 
% a w LDL listę dróg do tych liści

listaDrógDoLiści(X,LL,LDL) :- var(LL),
   findall(L,liść(L,X),LL),
   findall((X,L,LXL),drogaCzłDoLiścia(X,L,LXL),LDL),!.

     
% tę część wykonujemy, gdy  LL jest listą pustą
% odpłacamy 'pięknym za nadobne'
     
listaDrógDoLiści(_X,[],LDL) :- LDL = [],!.



% tę część wykonujemy, gdy LL jest niepustą listą liści
listaDrógDoLiści(X,LL,LDL) :- is_list(LL), length(LL,N), N>0,
   findall((X,L,LXL),(member(L,LL),drogaCzłDoLiścia(X,L,LXL)),LDL).

% a tę, gdy przekazany L NIE jest listą,
% tylko np pojedynczym liściem

listaDrógDoLiści(_X,'',LDL) :- LDL=[],!.
listaDrógDoLiści(_X,"",LDL) :- LDL=[],!.
listaDrógDoLiści(X,L,LDL) :- atomic(L),
   findall((X,L,LXL),drogaCzłDoLiścia(X,L,LXL),LDL).

listaDrógDoLiści(X,LDL) :- listaDrógDoLiści(X,_,LDL).

listaDrógOdLiści(X,LOL) :- listaDrógOdLiści(_,X,LOL).

listaDrógOdLiści(L,X,LOL) :- (listaDrógDoLiści(X,L,LDL), 
    ((LDL=[]) -> ( LOL =[]              % każdy element LDL ma postać: 
        ) % end of 'then' of'LDL=[]'    % (X, L, ListElemLDL=[lista osób od X do L razem z nimi]).
        ;(                              % kazdy element LOK ma mieć postać: (L, X, reverse(ListElemLDL)).
            maplist([IN,OUT] >> (
                    IN=(Xi,Li,LDLi), % rozłożyliśmy 'IN' na 'czynniki pierwsze'
                    reverse(LDLi,LOLi),  % odwracamy listę osób Xi <-> Li
                    OUT=(Li,Xi,LOLi)), % end of 'lambda function'
                LDL,LOL
            ) % end of 'maplist'
        ) % end of 'else' of'LDL=[]'
    ) % end of 'LDL=[]'
). % end of 'listaDrógOdLiści(L,X,LOK) :-'


wspólnyKorzeń(K,X,X) :- korzeń(K,X).
wspólnyKorzeń(K,X,Y) :- człowiek(X),człowiek(Y),X\=Y,korzeń(K,X),korzeń(K,Y).
wspólnyKorzeń(X,Y)   :- wspólnyKorzeń(_,X,Y).

krewni(X,Y)         :- wspólnyKorzeń(X,Y). % tutaj jesteś swoim krewnym
krewny(X,Y)         :- m(X), krewni(X,Y).
krewna(X,Y)         :- k(X), krewni(X,Y).




% 'dystans' między osobami: 
% od siebie do siebie jest =0
% między niespokrewnionymi (brak w bazie wspólnego korzenia) =+inf (+nieskończoność),
% między spokrewnionymi - ilość 'przeskoków' jakie minimalnie trzeba wykonać 
% by od jednej osoby 'dojść' do drugiej, np:
% między rodzicami, a dziećmi =1, między rodzeństwem =2
% mięzy kuzynami (gdy rodzice są rodzeństwem) =3
% między dziadkami, a wnukami =2, itd...
% między rodzeństwem przyrodnim (gdy mają wspólnego rodzica) =2
dystans(X,X,N) :- N=0,!.
dystans(X,Y,N) :- \+ wspólnyKorzeń(X,Y), N=inf. % (+niesk. <=> niespokrewnieni)

% TO DO: DOKOŃCZYĆ DYSTANS 'RZECZYWISTY'  - NIE '0' I NIE 'INF'



/*
   listaRodziców/2 - tworzy listę znanych rodziców danej osoby lub listy osób
      gdy podana lista osób, nie sprawdza pokrewieństwa,
      gdy podana nieznana osoba / lista pusta -> zwraca pustą listę rodziców
*/
listaRodziców(X,LRX) :- (is_list(X)->(X=[],LRX=[])),!.
listaRodziców(X,LRX) :- ((is_list(X))->(
      (X=[G|T])-> (
         listaRodziców(G,LRG), 
         listaRodziców(T,LRT),
         append(LRG,LRT,LRGT),
         sort(LRGT,LRX)
      ) % end od 'then' ' (X=[G|T])->'
   ) % end of 'then' '(is_list(X))->'
),!.
listaRodziców(X,LRX) :- (( \+ osoba(X))->LRX=[]),!.
listaRodziców(X,LRX) :- osoba(X)->(
   findall(R,rodzic(R,X),LR),sort(LR,SLR),LRX=SLR
).

/*
   listyPrzodków/2 - dla podanej osoby X tworzy 'listę list' przodków 
      kolejnych 'poziomów' w stronę 'korzenia', z podaniem 'poziomu' 'od X' 
      i ilością przodków na danym poziomie
      gdy X nie jest osobą / nieznaną osobą / nie ma znanych rodziców
         - zwraca listę pustą

      natomiast nie przewiduję podawania tutaj jako X 'listy osób'
      z tego jako wynik musiałaby wyjść już bardzo 'piętrowa' konstrukcja
*/

listyPrzodków(X,LWy) :-(
   \+ osoba(X) -> LWy=[] 
   ;(
      listyPrzodków(X,0,LP), 
      LWy=LP
   ) % end of 'else' of '\+ osoba(X) ->' (i całego '\+ osoba(X) ->'
).


%
% do listyPrzodków/3 jako Xwe przekazujemy osobę lub listę osób
% z tym, że na 'poziomie wywołania' ma sens podawać TYLKO 1 osobę,
% wtedy kolejne 'poziomy' to kolejne generacje przodków tej osoby
% jeśli na poziomie wywołania podamy różne osoby, to otrzymamy bzdurę
% Nwe - który poziom mnie woła (pierwszy wołający = 0)
% wtedy kolejne poziomy  to "odległość" od wołacza
%

listyPrzodków(X,Nwe,LWy) :- (
%   Nnast is Nwe + 1,       % NIE widać tego w środku bloków ->();()
   (\+ osoba(X),X=[])->( % tu wchodzimy, gdy NIE jest osobą I jest pustą listą
      Nnast is Nwe+1,       % dlatego definiuję wewnątrz...
      LWy =[[Nnast, 0,[]]]
   ) % end of 'then' of '(X=[]; \+ osoba(X))->'
   ;(  % tu wchodzimy, gdy JEST osobą LUB NIE pustą listą
      Nnast is Nwe+1,      % i tutaj też
      listaRodziców(X,LR),
      length(LR,LRLen),
      (LRLen = 0-> LWy =[[Nnast,LRLen,[]]]
         ;( listyPrzodków(LR,Nnast,LP),
            LWy =[[Nnast,LRLen,LR]|LP]
         )
      )
   ) % end of 'else' of '(X=[]; \+ osoba(X))->'
). % end of 'listyPrzodków(X,LX,Nwe,Nwy) :-'


/*
   UWAGA !!! ACHTUNG !!! WNIMANIJE !!! ATTENTION

   zbiór reguł 'listaDzieci/2' wreszcie działa tak, jak chcę
   i dla 'atomów' i dla 'list'...
   radzi sobie też z '_','',"",[] i listami zagnieżdżonymi
   np: 
      '_' obsługuje tylko jak jest 'samo', a nie w liście
      podobnie z 'X' (zmiennymi nieprzypisanymi)

   TO DO: przejrzeć pozostałe reguły i przerobić wg tego schematu!!!

*/


/*
   listaDzieci/2 - tworzy listę znanych dzieci danej osoby lub listy osób
      gdy podana lista osób, nie sprawdza pokrewieństwa/powinowactwa,
      gdy podana nieznana osoba / lista pusta -> zwraca pustą listę dzieci
*/

listaDzieci(X,LDX) :- (is_list(X),X=[G|T],
         (listaDzieci(G,LDG), listaDzieci(T,LDT)),
         append(LDG,LDT,LDGT), sort(LDGT,LDX),!
). % end of 'listaDzieci(X,LDX) :-'

listaDzieci([],LDX) :- LDX=[].
listaDzieci('',LDX) :- LDX=[].
listaDzieci("",LDX) :- LDX=[].

listaDzieci(X,LDX) :- \+ osoba(X),LDX=[].
listaDzieci(X,LDX) :- (osoba(X),\+rodzic(X,_)),LDX=[].

listaDzieci(X,LDX) :- osoba(X),findall(D,rodzic(X,D),LD),sort(LD,SLD),LDX=SLD.


/*


  TO DO - dokończyć 'listaWspólnychDzieci'

% 
% listaWspólnychDzieci(R1,R2,LWD) - zwraca listę wspólnych dzieci
% (jeśli istnieją) pary (R1, R2)
%


%
% czy chociaż 1 param (X,Y) skonkretyzowany
% 

listaWspólnychDzieci(X,Y,LWD) :- (var(X),var(Y)),
   piszKomunikat(nieOK,
      "'listaWspDz': Podaj chociaż jednego z rodziców\n",[]),
   LWD=[],!,false.

%
% czy żaden param (X,Y) nie pusty
%

listaWspólnychDzieci(X,Y,LWD) :- 
   ((nonvar(X),(X=[];X='';X="")) ; (nonvar(Y),(Y=[];Y='';Y=""))) ,
   piszKomunikat(nieOK,
      "'listaWspDz': Któryś argument (lub obydwa) jest/są  puste.\n",[]),
   LWD=[],!,false.

% 
% czy żaden param (X,Y) nie jest listą - na razie to sobie darowałem
% TO DO: obsłużyć przypadek, gdy jeden/oba param (X,Y) są listami
%

listaWspólnychDzieci(X,Y,LWD) :- (is_list(X);is_list(Y)),
   piszKomunikat(nieOK,
      "'listaWspDz': ~w\n~w\n\n",
      ['Któryś argument (lub obydwa) jest/są listą.',
       'Sorry, nie obsługuję tego przypadku - muszą być ludzie.']),
   LWD=[],!,false.

%
% czy (X,Y) są różnej płci
%

listaWspólnychDzieci(X,Y,LWD) :- (atomic(X),atomic(Y)),
   ((m(X),m(Y));(k(X),k(Y))),
   piszKomunikat(nieOK,
      "'listaWspDz': ~w\n",
      ['Obydwie osoby podane jako rodzice są tej samej płci.']),
   LWD=[],!,false.

%
% czy obydwoje (X,Y) mają dzieci
%

listaWspólnychDzieci(X,Y,LWD) :-
   ((rodzic(X,_),rodzic(Y,_))->( % obydwoje mają dzieci -> szukamy wspólnych
         listaDzieci(X,LDX), listaDzieci(Y,LDY),
         findall(D,(member(D,LDX),member(D,LDY)),LWD),
         (LWD=[] -> (
               piszKomunikat(nieOK,
               "'listaWspDz': I'm so sorry... ~q i ~q nie mają wspólnych dzieci.\n",
                  [X,Y]),
               false
            ) % end of 'then' of 'LWD=[] ->'
            ; ( true
            ) % end of 'else' of 'LWD=[] ->'
         ) % end of 'LWD=[] ->'
      ) % end of 'then' of '(rodzic(X,_),rodzic(Y,_))->'
      ;(
         piszKomunikat(nieOK,
            "'listaWspDz': ~w\n",
            ['Któraś (lub obydwie) z podanych osób w ogóle nie ma dzieci.']),
         LWD=[]
      ) % end of 'else' of '(rodzic(X,_),rodzic(Y,_))->'
   ) % end of '(rodzic(X,_),rodzic(Y,_))->'
. % end of 'listaWspólnychDzieci(X,Y,LWD)'

*/
  

/*
   listyPotomków/2 - dla podanej osoby X tworzy 'listę list' przodków 
      kolejnych 'poziomów' w stronę 'korzenia', z podaniem 'poziomu' 'od X' 
      i ilością przodków na danym poziomie
      gdy X nie jest osobą / nieznaną osobą / nie ma znanych rodziców
         - zwraca listę pustą

      natomiast nie przewiduję podawania tutaj jako X 'listy osób'
      z tego jako wynik musiałaby wyjść już bardzo 'piętrowa' konstrukcja
*/

listyPotomków(X,LWy) :-(
   \+ osoba(X) -> LWy=[] 
   ;(
      listyPotomków(X,0,LP), 
      LWy=LP
   ) % end of 'else' of '\+ osoba(X) ->' (i całego '\+ osoba(X) ->'
).

%
% do listyPotomków/3 jako Xwe przekazujemy osobę lub listę osób
% z tym, że na 'poziomie wywołania' ma sens podawać TYLKO 1 osobę,
% wtedy kolejne 'poziomy' to kolejne generacje przodków tej osoby
% jeśli na poziomie wywołania podamy różne osoby, to otrzymamy bzdurę
% Nwe - który poziom mnie woła (pierwszy wołający = 0)
% wtedy kolejne poziomy  to "odległość" od wołacza
%

listyPotomków(X,Nwe,LWy) :- (
%   Nnast is Nwe + 1,       % NIE widać tego w środku bloków ->();()
   (\+ osoba(X),X=[])->( % tu wchodzimy, gdy NIE jest osobą I jest pustą listą
      Nnast is Nwe+1,       % dlatego definiuję wewnątrz...
      LWy =[[Nnast, 0,[]]]
   ) % end of 'then' of '(X=[]; \+ osoba(X))->'
   ;(  % tu wchodzimy, gdy JEST osobą LUB NIE pustą listą
      Nnast is Nwe+1,      % i tutaj też
      listaDzieci(X,LD),
      length(LD,LDLen),
      (LDLen = 0-> LWy =[[Nnast,LDLen,[]]]
         ;( listyPotomków(LD,Nnast,LP),
            LWy =[[Nnast,LDLen,LD]|LP]
         )
      )
   ) % end of 'else' of '(X=[]; \+ osoba(X))->'
). % end of 'listyPotomków(X,LX,Nwe,Nwy) :-'


%
% 'liczbaPrzodków/2' - w N zwraca liczbę znanych przodków osoby X
%

liczbaPrzodków(X,N) :- (                   % w T jest lista krewnych 
   listyPrzodków(X,LP),                    % na danym poziomie 
   foldl(({}/[IN,V,OUT]>>                  % tutaj nas nie interesuje
             (IN=[_Poziom,IlośćLudzi|_T], 
             OUT is IlośćLudzi+V)),
        LP,0,Wyn), 
   N=Wyn
).


%
% 'liczbaPotomków/2' - w N zwraca liczbę znanych potomków osoby X
%

liczbaPotomków(X,N) :- (                   % w T jest lista krewnych 
   listyPotomków(X,LP),                    % na danym poziomie 
   foldl(({}/[IN,V,OUT]>>                  % tutaj nas nie interesuje
             (IN=[_Poziom,IlośćLudzi|_T], 
             OUT is IlośćLudzi+V)),
        LP,0,Wyn), 
   N=Wyn
).


/*
    TO DO - przemyśleć i dodefiniować krewnych/~w lini prostej/~w lini bocznej
            oraz linię_rodową - może jednak nie połączenie korzeń-liść,
            a lista (raczej lista list ludzi) dla których 'X' jest krewnym w linii prostej
            
linia_rodowa(K,L):- człowiekKorzeń(K), człowiekLiść(L), przodek(K,L). 
% ścieżka rodowa między 'krańcowymi' ludźmi

krewni_w_linii_prostej(X,Y):- (przodek(X,Y);przodek(Y,X)),(X\=Y).
krewni_w_linii_bocznej(X,Y):- (przodek(P,X), przodek(P,Y),człowiek(P)),(X\=Y),
             write('\nwspólny przodek '),write(X),write(' i '), writeln(Y),
             write('to: '),writeln(P).
to już jest: krewni(X,Y) :- krewni_w_linii_prostej(X,Y);krewni_w_linii_bocznej(X,Y).
*/


%=======================================================================
%
% B2) relacje powinowactwa
%


/*
% uwagi dot. reprezentacji małżeństw w bazie
%
% z małżeństwem/małżonkami i in.'relacjami symetrycznymi' 
% jest ten problem, że  zachodzą tzw. 'odwołania cykliczne'
%
% najpierw stosowałem sposób ze strony:
% http://www.swi-prolog.org/pldoc/man?section=tabling
% m.in.sekcja A.35.3
% na rozwiązanie problemu symetrycznych relacji
% (normalnie prowadzą do nieskończonego zapętlenia
% taką symetryczną relacją jest małżonek(X,Y).
% patrz też dyrektywa :- discontiguous 'małżonek tabled'/2
% na początku  pliku
% UWAGA!!!
% czasem (nie odkryłem reguły) wyświetlało tylko 'współmałżonka'
% (tak ma być), a czasem też 'siebie'
%
% EDIT - było rozwiązanie problemu symterii z użyciem tablicowania
:- use_module(library(tabling)).
:- table małżonek/2.
małżonek(X,Y) :- małżonek(Y,X).
%
% EDIT - jednak zmieniłem to na rozwiązanie z użyciem dodatkowej relacji
% w ten sposób wszystkie rzeczy definiowane faktami (m, k, rodzic, małżonek)
% wyświetla w jednej kategorii: 'atomNarg'
% wcześniej 'rodzic' był zaliczany do atomów, a 'małżonek' do relacji
*/


małżeństwo(X,Y)         :- mąż(X,Y).


% fakty 'małżonek/2' mogą być wpisane w dowolną stronę; jednak małżeństwo
% jako relację zdefiniowałem jako 'uporządkowaną' parę (X,Y), gdzie m(X), k(y)


żona(X,Y)               :- k(X),(małżonek(X,Y);małżonek(Y,X)).
mąż(X,Y)                :- m(X),(małżonek(X,Y);małżonek(Y,X)).


ojczym(X,Y)             :- m(X), k(M), mąż(X,M), matka(M,Y), \+ ojciec(X,Y).
przybranyOjciec(X,Y)    :- ojczym(X,Y).


macocha(X,Y)            :- k(X), m(O), żona(X,O),ojciec(O,Y), \+ matka(X,Y).
przybranaMatka(X,Y)     :- macocha(X,Y).


przybranyRodzic(X,Y)    :- przybranyOjciec(X,Y); przybranaMatka(X,Y).
przybraniRodzice(X,Y)   :- przybranyRodzic(X,Y).


%
% chyba nie ma czegoś  takiego (albo bardzo rzadko), jak 'oboje przybrani rodzice' 
% którzy _oboje_ byliby małżonkami rodziców biologicznych 
% => NIE daję 'przybraniRodzice(X,Y,Z)'
% bo jak to... chyba najpierw musiałby umrzeć/odejść jeden z rodziców biologicznych,
% i ten drugi wziąć nowego małżonka, a potem umrzeć/odejść też  ten drugi
% no ale jeśli ten 'pierwszy przybrany' wziąłby sobie małżonka,
% to byłby _jego_ małżonek, a NIE rodzica biologicznego 
% => czyli nie byłby 'przybrany' w sensie tych relacji...
% wiem, są rodzice zastępczy, ale to trochę co innego => nie mieszam tego z przybranymi
%
        
pasierb(X,Y)            :- m(X), rodzic(R,X),
                                 (małżonek(R,Y);małżonek(Y,R)),
                                 \+ rodzic(Y,X).
pasierbowie(X,Y)        :- pasierb(X,Y).


pasierbica(X,Y)         :- k(X), rodzic(R,X),
                                 (małżonek(R,Y);małżonek(Y,R)),
                                 \+ rodzic(Y,X).
pasierbice(X,Y)         :- pasierbica(X,Y).


pasierby(X,Y)           :- pasierbowie(X,Y); pasierbice(X,Y).


% definicje szwagier / szwagierka /bratowa /teść /teściowa/powinowaty wg:
% https://pl.wikipedia.org/wiki/Powinowactwo_(prawo)
% jak widać NIE są analogiczne =>
% skoro jest 'bratowa', to druga def 'szwagra' powinna być 'siostrowy'
% wtedy szwagier / szwagierka byliby tylko rodzeństwem małżonka


szwagier(X,Y) :- brat(X,M),(małżonek(M,Y);małżonek(Y,M)).
szwagier(X,Y) :- mąż(X,S),siostra(S,Y).


szwagierka(X,Y) :- siostra(X,M),(małżonek(M,Y);małżonek(Y,M)).
bratowa(X,Y)    :- żona(X,B), brat(B,Y).


teść(X,Y)     :- ojciec(X,M), (małżonek(M,Y);małżonek(Y,M)).
teściowa(X,Y) :- matka(X,M),  (małżonek(M,Y);małżonek(Y,M)).

zięć(X,Y)     :- mąż(X,M), rodzic(Y,M).
synowa(X,Y)   :- żona(X,M), rodzic(Y,M).

/*
   UWAGA!!! przemyśleć 'powinowatych' - obecna wersja jest baaaardzo
   zasobo- i czaso- żerna....

% pytanie: czy pokrewieństwo jest silniejsze od powinowactwa?
% chyba tak....
% czyli jeśli ktoś jest krewnym, to wykreślam go z listy powinowatych...
% dotyczy np moich dziadków i ich rodzin...

% poniższy zapis ma oznaczać, że powinowactwo występuje wtedy, 
% gdy X jest krewnym małżonka Y i nie jest krewnym Y
powinowactwo(X,Y) :- (mąż(M,Y); żona(M,Y)),krewni(X,M),\+krewni(X,Y).
listaPowinowatych(X,Y,LPow) :-findall((X,Y),(powinowactwo(X,Y);powinowactwo(Y,X)),LP1),sort(LP1,SLP1),LPow=SLP1.
% a to, że powinowactwo zachodzi 'w obie strony' 
% tak, jak przy małżeństwie występuje  problem z cyklicznością odwołań...
powinowaci(X,Y) :- member((X,Y),LPow),listaPowinowatych(X,Y,LPow).

*/




%=======================================================================
%
% A) 'koligacje rodzinnne'
%    definicje faktów: m/1, k/1 (mężczyźni i kobiety zdef.w bazie
%    relacje definiowane przez fakty/przykłady: rodzic/2, małżonek/2
%



%=======================================================================
%
% A1) definiujemy mężczyzn
%


m('Krzysztof Grzegorz S').  % dziadek z ig
m('Cymbalista').            % 1szy mąż józefy kordasiewicz
m('Ks Leon B').             % ks leon b., syn cym.i józefyK
m('Ks Adam W').             % ks adam w, syn ks leona
m('Włodzimierz K').         % ojciec piotra - dziadka tadeusza
m('Piotr Ł').               % dziadek z g.
m('Krzysiek S').            % wujek k.
m('Łukasz S').              % łukasz z ig.
m('Józek Ł').               % wujek j.
m('Marian Ł').              % wujek m.
m('Paweł Ł').               % paweł ł.
m('Marcin Ł').              % marcin ł.
m('Kamil Ł').               % kamil ł.
m('Piotruś S').             % syn łukasza
m('Piotr K').               % dziadek tadeusza
m('Adam K').                % wuj tadeusza
m('Andrzej K').             % wuj tadeusza
m('Piotruś K').             % syn tadeusza
m('Piotrek S').             % brat asi
m('Michał K').              % mąż ewy
m('Arek K').                % kuzyn tadeusza
m('Tadeusz K').             % :)
m('Grzegorz S').            % tata asi
m('Paweł K').               % brat arka (zmarły)
m('Jaś NN').                % syn magdy - kuzynki tadeusza
m('Bartek J').              % syn kaśki - kuzynki tadeusza
m('Roman NN').              % tzw.ojciec tadeusza
m('Sławek J').              % mąż kaśki - kuzynki tadeusza
m('Teo S').                 % syn piotrka, brata asi
m('Jurek K').               % syn ewy
m('Karol K').               % ojciec michała
m('Tomek T').               % tomek turzyński
m('Ryszard T').             % ryszard turzyński
m('Mikołaj Ł').             % mikołaj łapiński, syn pawła
m('Szymon Ł').              % szymon łapiński, syn pawła
m('Florian S').             % florian stan. - ojciec Hanki K   
m('Rafał W').               % szwagier Michała K, mąż marty w           
m('Jakub K').               % brat Michała K                            
m('Wojtek S').              % brat Hanki K                              
m('Franek W').              % syn Marty i Rafała W                      
m('Andrzej K XIXw').        % ojciec Włodzimierza K / dziadek Piotra K
m('NN Ślusarczyk').         % ojciec Marii Ireny Śl



%=======================================================================
%
% A2) definiujemy kobiety
%


k('Antonina B').            % antonina boles. - siostra ks leona
k('Józefa K').              % józefa korda. - matka piotra, dziadka tadeusza
k('Grażyna Ł').             % ciotka grażyna
k('Bożena Ł').              % ciotka bożena
k('Irena Joanna S').        % babcia z ig.
k('Irena Ł').               % babcia prababcia z goł.
k('Dominika S').            % córka łukasza z ig.
k('Kaśka S').               % kaśka siostra łukasza z ig.
k('Marta S').               % marta siostra łukasza z ig.
k('Ulcia S').               % ula, córka kaśki z ig.
k('Maja S').                % maja, córka kaśki z ig.
k('Ida S').                 % ida, córka marty z ig.
k('Ewa T').                 % ciotka ewa
k('Maria Irena Śl').        % babcia tadeusza,żona piotra
k('Ula SS').                % żona piotrka
k('Ewa K').                 % siostra asi
k('Zosia S').               % córka piotrka i uli
k('Irenka K').              % córka ewy i michała
k('Halina K').              % matka tadeusza
k('Maria Cimer').           % matka arka
k('Kaśka J').               % kuzynka tadeusza
k('Magda K').               % kuzynka tadeusza
k('Marta J').               % córka kaśki i sławka
k('Ania K').                % córka tadeusza
k('Asia SK').               % asia :)
k('Marysia S').             % mama asi
k('Hanka K').               % żona adama, ciotka tadeusza
k('Teresa SS').             % mama uli
k('Teresa S').              % ciotka teresa z ig.
k('Anna S').                % żona łukasza z ig.
k('Anna P').                % anna pysz. - córka marianaŁ
k('Renata Ł').              % żona pawła łap.
k('Marta Ł').               % żona marcina łap.
k('Janina S').              % janina st. - 2. żona andrzejaK
k('Małgosia Ł').            % córka marcinaŁ i martyŁ
k('Marta W').               % siostra Michała K                 
k('Gertruda S').            % matka Hanki K, żona Floriana S        
k('Ela AK').                % matka Michała K                       
k('Apolonia Petrus').       % matka Włodzimierza K (babcia Piotra K)
k('Anna K XIXw').           % matka 'Marii Ireny Śl', córka 'Andrzeja K XIXw' i 'Apolonii Petrus')



%=======================================================================
%
% A3) definiujemy rodziców
%


rodzic('Piotr K',           'Andrzej K').
rodzic('Piotr K',           'Halina K').
rodzic('Piotr K',           'Adam K').
rodzic('Maria Irena Śl',    'Andrzej K').
rodzic('Maria Irena Śl',    'Halina K').
rodzic('Maria Irena Śl',    'Adam K').
rodzic('Andrzej K',         'Arek K').
rodzic('Andrzej K',         'Paweł K').
rodzic('Maria Cimer',       'Arek K').
rodzic('Maria Cimer',       'Paweł K').
rodzic('Roman NN',          'Tadeusz K').
rodzic('Halina K',          'Tadeusz K').
rodzic('Adam K',            'Kaśka J').
rodzic('Adam K',            'Magda K').
rodzic('Hanka K',           'Kaśka J').
rodzic('Hanka K',           'Magda K').
rodzic('Magda K',           'Jaś NN').
rodzic('Sławek J',          'Bartek J').
rodzic('Sławek J',          'Marta J').
rodzic('Kaśka J',           'Bartek J').
rodzic('Kaśka J',           'Marta J').
rodzic('Tadeusz K',         'Piotruś K').
rodzic('Tadeusz K',         'Ania K').
rodzic('Asia SK',           'Piotruś K').
rodzic('Asia SK',           'Ania K').
rodzic('Marysia S',         'Asia SK').
rodzic('Grzegorz S',        'Asia SK').
rodzic('Grzegorz S',        'Ewa K').
rodzic('Grzegorz S',        'Piotrek S').
rodzic('Marysia S',         'Piotrek S').
rodzic('Marysia S',         'Ewa K').
rodzic('Michał K',          'Jurek K').
rodzic('Michał K',          'Irenka K').
rodzic('Ewa K',             'Jurek K').
rodzic('Ewa K',             'Irenka K').
rodzic('Piotrek S',         'Teo S').
rodzic('Piotrek S',         'Zosia S').
rodzic('Ula SS',            'Teo S').
rodzic('Ula SS',            'Zosia S').
rodzic('Karol K',           'Michał K').
rodzic('Teresa SS',         'Ula SS').
rodzic('Krzysztof Grzegorz S',  'Grzegorz S').
rodzic('Krzysztof Grzegorz S',  'Ewa T').
rodzic('Krzysztof Grzegorz S',  'Krzysiek S').
rodzic('Irena Joanna S',    'Grzegorz S').
rodzic('Irena Joanna S',    'Ewa T').
rodzic('Irena Joanna S',    'Krzysiek S').
rodzic('Krzysiek S',        'Łukasz S').
rodzic('Krzysiek S',        'Kaśka S').
rodzic('Krzysiek S',        'Marta S').
rodzic('Teresa S',          'Łukasz S').
rodzic('Teresa S',          'Kaśka S').
rodzic('Teresa S',          'Marta S').
rodzic('Cymbalista',        'Ks Leon B').
rodzic('Cymbalista',        'Antonina B').
rodzic('Ks Leon B',         'Ks Adam W').
rodzic('Józefa K',          'Ks Leon B').
rodzic('Józefa K',          'Antonina B').
rodzic('Józefa K',          'Piotr K').
rodzic('Włodzimierz K',     'Piotr K').
rodzic('Ryszard T',         'Tomek T').
rodzic('Ewa T',             'Tomek T').
rodzic('Piotr Ł',           'Marysia S').
rodzic('Piotr Ł',           'Józek Ł').
rodzic('Piotr Ł',           'Marian Ł').
rodzic('Irena Ł',           'Marysia S').
rodzic('Irena Ł',           'Józek Ł').
rodzic('Irena Ł',           'Marian Ł').
rodzic('Łukasz S',          'Piotruś S').
rodzic('Łukasz S',          'Dominika S').
rodzic('Anna S',            'Piotruś S').
rodzic('Anna S',            'Dominika S').
rodzic('Marta S',           'Ida S').
rodzic('Marian Ł',          'Anna P').
rodzic('Bożena Ł',          'Anna P').
rodzic('Józek Ł',           'Kamil Ł').
rodzic('Józek Ł',           'Marcin Ł').
rodzic('Józek Ł',           'Paweł Ł').
rodzic('Grażyna Ł',         'Kamil Ł').
rodzic('Grażyna Ł',         'Marcin Ł').
rodzic('Grażyna Ł',         'Paweł Ł').
rodzic('Kaśka S',           'Ulcia S').
rodzic('Kaśka S',           'Maja S').
rodzic('Paweł Ł',           'Mikołaj Ł').
rodzic('Paweł Ł',           'Szymon Ł').
rodzic('Renata Ł',          'Mikołaj Ł').
rodzic('Renata Ł',          'Szymon Ł').
rodzic('Marcin Ł',          'Małgosia Ł').
rodzic('Marta Ł',           'Małgosia Ł').
rodzic('Marta W',           'Franek W').        
rodzic('Rafał W',           'Franek W').
rodzic('Florian S',         'Hanka K').
rodzic('Florian S',         'Wojtek S').
rodzic('Gertruda S',        'Hanka K').
rodzic('Gertruda S',        'Wojtek S').
rodzic('Karol K',           'Marta W').
rodzic('Karol K',           'Jakub K').
rodzic('Ela AK',            'Jakub K').
rodzic('Ela AK',            'Marta W').
rodzic('Ela AK',            'Michał K').
rodzic('Andrzej K XIXw',    'Włodzimierz K').
rodzic('Apolonia Petrus',   'Włodzimierz K').
rodzic('NN Ślusarczyk',     'Maria Irena Śl').
rodzic('Anna K XIXw',       'Maria Irena Śl').
rodzic('Andrzej K XIXw',    'Anna K XIXw').
rodzic('Apolonia Petrus',   'Anna K XIXw').



%=======================================================================
%
% A4) definiujemy małżonków
%


małżonek('Krzysztof Grzegorz S',    'Irena Joanna S').
małżonek('Cymbalista',      'Józefa K').
małżonek('Włodzimierz K',   'Józefa K').
małżonek('Piotr Ł',         'Irena Ł').
małżonek('Krzysiek S',      'Teresa S').
małżonek('Łukasz S',        'Anna S').
małżonek('Józek Ł',         'Grażyna Ł').
małżonek('Marian Ł',        'Bożena Ł').
małżonek('Paweł Ł',         'Renata Ł').
małżonek('Marcin Ł',        'Marta Ł').
małżonek('Piotr K',         'Maria Irena Śl').
małżonek('Adam K',          'Hanka K').
małżonek('Andrzej K',       'Maria Cimer').
małżonek('Andrzej K',       'Janina S').
małżonek('Piotrek S',       'Ula SS').
małżonek('Michał K',        'Ewa K').
małżonek('Tadeusz K',       'Asia SK').
małżonek('Grzegorz S',      'Marysia S').
małżonek('Sławek J',        'Kaśka J').
małżonek('Ryszard T',       'Ewa T').
małżonek('Florian S',       'Gertruda S').              
małżonek('Marta W',         'Rafał W').
małżonek('Karol K',         'Ela AK').
małżonek('Andrzej K XIXw',  'Apolonia Petrus').
małżonek('NN Ślusarczyk',   'Anna K XIXw').




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% T) dane testowe
%     dane jakie  wprowadzimy do bazy na czas testów
%     niektóre zaburzają jej spójność - chcemy sprawdzić,
%     jak reguły sobie z nimi poradzą...
%
%     wstawiać przez 'assertz(daneTestowe).'
%     usuwać przez 'retract' lub 'retractall'
%


daneTestowe(m('ktoś1')).            % niezdecydowany co do płci
daneTestowe(k('ktoś1')).  
daneTestowe(m('ktoś1a')).
daneTestowe(k('ktoś3')).
daneTestowe(rodzic('ktoś2','ktoś1a')). % def jako rodzic, bez def m/k
daneTestowe(rodzic('ktoś2','ktoś2a')). % i rodzic i dziecko bez def m/k
daneTestowe(rodzic('ktoś3','ktoś2')).
daneTestowe(rodzic('ktoś1a','ktoś3')). % ktoś1a jest swoim pradziadkiem
daneTestowe(m('ktoś4')).
daneTestowe(małżonek('ktoś4', 'ktoś4')).
daneTestowe(małżonek('ktoś2a','ktoś3')). % ktoś2a małżonkiem babci
daneTestowe(małżonek('Ktoś2a','ktoś1a')).
            % ktoś2a małżonkiem rodzeństwa i prababci jednocześnie  
            % obie rzeczy podejrzane

/*
TO DO:
testować też:
    - powtórzone def pary rodzic/dziecko, powtórzeni rodzice dla dziecka
    - powtózone dzieci dla rodziców
    - powtórzone def pary małżonków np (X,Y) i (Y,X)
    - małżeństwa ze sobą
    - małżeństwa z dziećmi/rodzicami, krewnymi(?), powinowatymi(?)
    - zrobić porównywanie / wyszukiwanie czy jakieś osoby są
      względem siebie jednocześnie na różnych 'poziomach' pokoleń
      pamiętać, że porównanie poziomów może mieć 4(!!!) stany: 
        'starszy/poprzedni', 'równy', 'młodszy/następny', 'NIE DA SIĘ OKREŚLIĆ'
        (gdy np druga osoba spoza krewnych, izolowana itd...)
    - testować, czy małżeństwa nie biorą osoby spokrewnione (w jakim stopniu)
      i chyba też spowinowacone (w jakim stopniu) 
*/


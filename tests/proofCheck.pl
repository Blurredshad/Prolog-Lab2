
verify(InputFileName) :- see(InputFileName),
read(Prems), read(Goal), read(Proof),
seen,
valid_proof(Prems,  Proof, []), 
valid_conclusion(Goal, Proof).


%------------checking if proof in last line is the same as the conclusion of the sekvent--------------

%checks if the proof in the last line is the same as the conclusion of the sekvent
valid_conclusion(Goal, Proof) :-
    get_last(Proof, FinalRow),      %get last proofline
    get_value(FinalRow, Elem),      %get the proof in the proofline
    Goal == Elem.                   %check if the proof is same as the conclusion

%get the proof in the last row(which is the second element, middle element)
get_value([_, Head, _], Head).

%get the last row
get_last([Head | []], Head).
get_last([_| Tail], Head) :- get_last(Tail, Head).


%------------------helper predicates for natural deduction---------------------------------

%get the first row
firstRow([H | _], H).

%get the last row
lastRow([Last | []], Last).
lastRow([_ | Tail], H) :- lastRow(Tail, H).

%find a box by using row number(I) and the proof in the row(Elem)
%searches through lists to find a specific box where the element matches [I, Elem, _], and returning that entire box once it's found.
getBox(_, [], _) :- not(true).
getBox([I, Elem, _], [[[I, Elem, _] | BoxTail] | _], [[I, Elem, _] | BoxTail]).
getBox([I, Elem, _], [ _ | Tail], ReturnBox) :- getBox([I, Elem, _], Tail, ReturnBox).

%get the specific row using rowline I and the proof Elem
getRow(_, [], _) :- not(true).
getrow(I,[[I,Elem, _]|_],Elem).
getrow(I, [_|Tail],CurrentRow) :- getrow(I,Tail,CurrentRow).

%used in the copy rule
%verify that first argument exist in 2nd argument
copyRow([I, Elem, Arg], [[I, Elem, Arg] | _]).
copyRow([I, Elem, Arg], [_ | Tail]) :- copyRow([I, Elem, Arg], Tail).


%used for checking if the premise is valid
validPremise([], _) :- not(true).
validPremise(Elem, [Elem | _]).
validPremise(Elem, [_ | Tail]) :- validPremise(Elem, Tail).


%  Box
%The box starts with an assumption [I, Elem, assumption], followed by the rest of the box represented by Boxtail. 
%The remaining proof after the box is in RestRows.
valid_proof(Prems,[[[I, Elem, assumption] | Boxtail ] | RemainingRows],  TrackList) :-

                        %we are inside the Box and iterate through each row in the boxtail
                        valid_proof(Prems,   Boxtail, [[I, Elem, assumption] |  TrackList]),

                        %lastly put the box in TrackList, and continue with the proofs outisde the box.
                        valid_proof(Prems,   RemainingRows, [[[I, Elem, assumption] | Boxtail ] |  TrackList]).

%   Premise
% checks if the proof matches the structure of a premise, by using "premise" atom 
valid_proof(Prems,[[I, Elem, premise] | RemainingRows],  TrackList) :-

                        %check if the premise exists in the given premises (Prems), 
                        validPremise(Elem, Prems), 

                        %continue checking next proofline
                        valid_proof(Prems,   RemainingRows, [[I, Elem, premise] |  TrackList]).



%--------------------natural deduction rules-------------


%   Implication introduction
% To introduce an impication the rule must refer to a row which is first 
% in a box where the last row in the box's the variable we're introducing implication for
valid_proof(Prems,[[I, imp(A,B), impint(X,Y)] | RemainingRows],  TrackList) :-

                        %extract A and X, and using them search for the box in list "TrackList", then put the box in Box
                        getBox([X, A, _],  TrackList, ReturnBox),

                        %get the first row in the box
                        firstRow(ReturnBox, [X, A, _]),

                        %get the second row in the box
                        lastRow(ReturnBox, [Y, B, _]),

                        %continue checking next proof
                        valid_proof(Prems,   RemainingRows, [[I, imp(A,B), impint(X,Y)] |  TrackList]).

%   Implication elimination
% Row 1 with its proof exists in TrackList
% Row 1's value implicating Row 2's value must exist in TrackList
valid_proof(Prems,[[I, Elem, impel(X,Y)] | RemainingRows],  TrackList) :-

                        %find the row1 thats implicating
                        getrow(X,  TrackList, A),

                        %find the row with its value being implicated by the value of row1
                        getrow(Y,  TrackList, imp(A, Elem)),

                        %continue check next proof, and put this proof-row in TrackList
                        valid_proof(Prems,   RemainingRows, [[I, Elem, impel(X,Y)] |  TrackList]).

%   Copy
% Make sure that in list TrackList, there is the row number which is being copied from
% and thats its the same value as the row we're copying to
valid_proof(Prems,[[I, X, copy(Z)] | RemainingRows],  TrackList) :-
                        copyRow([Z, X, premise],  TrackList),
                        valid_proof(Prems, RemainingRows, [[I, X, copy(Z)] |  TrackList]).

%   And introduction 
% when matched with and(), check if the elements that are being anded exists in TrackList.
valid_proof(Prems,[[I, and(A,B), andint(X,Y)] | RemainingRows],  TrackList) :-
                          getrow(X, TrackList,A),
                          getrow(Y, TrackList,B),
                          valid_proof(Prems, RemainingRows,[[I, and(A,B), andint(X,Y)] |  TrackList]).

%   And deletion1
% Checks if A exists in TrackList and is in row X
valid_proof(Prems,[[I, A, andel1(X)] | RemainingRows],  TrackList) :-
                          getrow(X, TrackList,and(A,_)),
                          valid_proof(Prems, RemainingRows,[[I, A, andel1(X)] |  TrackList]).

%   And deletion2
% Checks if B exists in TrackList and is in row X
valid_proof(Prems,[[I, B, andel2(X)] | RemainingRows],  TrackList) :-
                          getrow(X, TrackList,and(_,B)),
                          valid_proof(Prems, RemainingRows,[[I, B, andel2(X)] |  TrackList]).


%   Negation introduction
% if negint() is matched, check whether we have a box that has value in neg() in first line, and has a contradition at the end of box
valid_proof(Prems,[[I, neg(A), negint(X,Y)] | RemainingRows],  TrackList) :-

                        %look for the box using the value in neg() and its row-number 
                        getBox([X, A, _],  TrackList, ReturnBox),

                        %see if the first row has A and last row has a contradiction
                        firstRow(ReturnBox, [X, A, _]),
                        lastRow(ReturnBox, [Y, cont, _]),

                        %continue to next proofline
                        valid_proof(Prems, RemainingRows,[[I, neg(A), andint(X,Y)] |  TrackList]).


%   Negation elimination
% when cont is matched
% Checks if the row X has a value A and thr row Y has neg(A)
valid_proof(Prems,[[I, cont, negel(X,Y)] | RemainingRows],  TrackList) :-
                          getrow(X,  TrackList, A),
                          getrow(Y,  TrackList, neg(A)),
                          valid_proof(Prems, RemainingRows,[[I, cont, negel(X,Y)] |  TrackList]).



%   LEM
% A or B has to be the neg() countpart of the other.
valid_proof(Prems,[[I, or(A, B), lem] | RemainingRows],  TrackList) :-
                          A = neg(B),
                          valid_proof(Prems, RemainingRows,[[I, or(A, B), lem] |  TrackList]).

valid_proof(Prems,[[I, or(A, B), lem] | RemainingRows],  TrackList) :-
                          B = neg(A),
                          valid_proof(Prems, RemainingRows,[[I, or(A, B), lem] |  TrackList]).


%   PBC
% looks for a box which begins with a neg(Elem) and ends with a contradiction, which then results to Elem.
valid_proof(Prems,[[I, Elem, pbc(X,Y)] | RemainingRows],  TrackList) :-
                          getBox([X, neg(Elem), _],  TrackList, ReturnBox),
                          firstRow(ReturnBox, [X, neg(Elem), _]),
                          lastRow(ReturnBox, [Y, cont, _]),
                          valid_proof(Prems,   RemainingRows, [[I, Elem, pbc(X,Y)] |  TrackList]).





% Fall: Contradiction elimination
% When contel() is matched, check if the row with the contradiction is the value in contel()
valid_proof(Prems,[[I, Elem, contel(X)] | RemainingRows],  TrackList) :-
                          getrow(X,  TrackList, cont),
                          valid_proof(Prems, RemainingRows,[[I, Elem, contel(X)] |  TrackList]).


%   Or introduction 1
% Checks if A is in TrackList and in row X
valid_proof(Prems,[[I, or(A,B), orint1(X)] | RemainingRows],  TrackList) :-
                          getrow(X, TrackList,A),
                          valid_proof(Prems, RemainingRows,[[I, or(A,B), orint1(X)] |  TrackList]).


%   Or introduction 2
% Checks if A is in TrackList and in row X
valid_proof(Prems,[[I, or(A,B), orint2(X)] | RemainingRows],  TrackList) :-
                          getrow(X, TrackList,B),
                          valid_proof(Prems, RemainingRows,[[I, or(A,B), orint2(X)] |  TrackList]).


%   Or elimination
% Check that there exists a row with "or" containing two values.
% Both of these mustbe the first lines in two separate boxes 
% Both boxes should end with the value given on the row that has orel
valid_proof(Prems,[[I, Elem, orel(X, OpenOrBox1, CloseOrBox1, OpenOrBox2, CloseOrBox2)] | RemainingRows],  TrackList) :-
                        
                        %find row with (A or B)
                        getrow(X,  TrackList, or(A, B)),

                        %find box where A leads to something
                        getBox([OpenOrBox1, A, _],  TrackList, ReturnBox1),
                        %find box where B leads to something
                        getBox([OpenOrBox2, B, _],  TrackList, ReturnBox2),

                        %find the first and last rows for respective boxes
                        firstRow(ReturnBox1, [OpenOrBox1, A, _]),
                        lastRow(ReturnBox1, [CloseOrBox1, Elem, _]),
                        firstRow(ReturnBox2, [OpenOrBox2, B, _]),
                        lastRow(ReturnBox2, [CloseOrBox2, Elem, _]),
                        valid_proof(Prems, RemainingRows,[[I, Elem, orel(X, OpenOrBox1, CloseOrBox1, OpenOrBox2, CloseOrBox2)] |  TrackList]).


%   Double negation introduction
% Check that value on the row-number in negnegint() is already a neg(Elem), and then doublenegates it.
valid_proof(Prems,[[I, neg(neg(Elem)), negnegint(X)] | RemainingRows],  TrackList) :-
                          getrow(X,  TrackList, ReturnElem),
                          ReturnElem == Elem,
                          valid_proof(Prems, RemainingRows,[[I, neg(neg(Elem)), negnegint(X)] |  TrackList]).

%   Double negation elimination
% Checks whether the row in negnegel(), has a doubleneg(Elem).
valid_proof(Prems,[[I, Elem, negnegel(X)] | RemainingRows],  TrackList) :-
                          getrow(X,  TrackList, neg(neg(Elem))),
                          valid_proof(Prems,   RemainingRows,[[I,Elem,negnegel(X)] |  TrackList]).

%   Modus tollens
% Checks if row X has an implication(A->B), and if row Y has a neg(B).
valid_proof(Prems,[[I, neg(Elem), mt(X,Y)] | RemainingRows],  TrackList) :-

                        %Checks if row X has an implication(A->B),
                        getrow(X, TrackList, imp(Elem, Z)),

                        %if row Y has a neg(B).
                        getrow(Y, TrackList, neg(Z)),

                        valid_proof(Prems,   RemainingRows, [[I, neg(Elem), mt(X,Y)] |  TrackList]).



%   Correct proof
% This is the base case and if reached, then the whole proof is valid
valid_proof(_,[],_) :- !.



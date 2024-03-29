(*<*)
theory "02_Earleys_Algorithm"
  imports
    "MyLaTeXSugar"
begin
(*>*)

(*<*)
syntax
  "length" :: "'a list \<Rightarrow> nat"  ("|_|")
(*>*)

chapter \<open>Earley Recognizer \label{chapter:2}\<close>

text\<open>
We present a slightly simplified version of Earley's original recognizer algorithm \cite{Earley:1970},
omitting Earley's proposed look-ahead since its primary purpose is to increase the efficiency of the
resulting recognizer. Throughout this thesis we are working with a running example. The considered grammar is a tiny excerpt of a toy
arithmetic expression grammar @{term "\<G>"}: $\, S ::= x \,\, \vert \,\, S + S$ and
the, rather trivial, input is @{term \<omega>} $= x + x + x$.

Intuitively, an Earley recognizer works in principle like a top-down parser carrying along all possible
parses simultaneously in an efficient manner.
In detail, the algorithm works as follows: it parses the input @{term \<omega>} $=a_0,\dots,a_n$, constructing
$n+1$ Earley bins $B_i$ that are sets of Earley items. An inital bin $B_0$ and one bin $B_{i+1}$ for
each symbol $a_i$ of the input.
In general, an Earley item $A \rightarrow \, \alpha \bullet \beta, i, j$ consists of four parts: a production rule of the grammar that we are currently
considering, a bullet signalling how much of the productions right-hand side we have recognized so far,
an origin $i$ describing the position in @{term \<omega>} where we started parsing, and an end $j$ indicating
the position in @{term \<omega>} we are currently considering next for the remaining right-hand side of the production rule.
Note that there will be only one set of Earley items or only one bin $B$ and we say an item is conceptually part of bin $B_j$ if its end is the index $j$.
Table \ref{tab:earley_bins} lists the items for our example grammar. Bin $B_4$ contains for example the item $S \rightarrow \, S + \bullet S, 2, 4$.
Or, we are considering the rule $S \rightarrow \, S + S$, have recognized the substring from $2$ to $4$ of @{term \<omega>} (the first index being
inclusive the second one exclusive) by $\alpha = S +$, and are trying to parse $\beta = S$ from position 4 in \omega. 

The algorithm initializes $B$ by applying the \textit{Init} operation. It then proceeds to execute
the \textit{Scan}, \textit{Predict} and \textit{Complete} operations listed in Figure \ref{fig:inference_rules}
until there are no more new items being generated and added to $B$. Next we describe these four operations
in detail:

\begin{enumerate}
  \item The \textit{Init} operation adds items
    $S \rightarrow \, \bullet\alpha, 0, 0$ for each production rule containing the start symbol $S$ on its left-hand side.

    For our example \textit{Init} adds the items $S \rightarrow \, \bullet x, 0, 0$ and $S \rightarrow \, \bullet S + S, 0 , 0$.
  \item The \textit{Scan} operation applies if there is a terminal to the right-hand side of the bullet, or items of the form $A \rightarrow \, \alpha \bullet a \beta, i, j$,
    and the $j$-th symbol of @{term \<omega>} matches the terminal symbol following the bullet. We add one new item $A \rightarrow \, \alpha a \bullet \beta, i, j+1$
    to $B$ moving the bullet over the parsed terminal symbol.

    Considering our example, bin $B_3$ contains
    the item $S \rightarrow \, S \bullet + S, 2, 3$, the third symbol of @{term \<omega>} is the terminal symbol $+$, so we add the
    item $S \rightarrow \, S + \bullet S, 2, 4$ to the conceptual bin $B_4$.
  \item The \textit{Predict} operation is applicable to an item when there is a non-terminal to the right-hand side of
    the bullet or items of the form $A \rightarrow \, \alpha \bullet B \beta, i, j$. It adds one new item $B \rightarrow \, \bullet \gamma, j, j$
    to the bin for each alternate $B \rightarrow \, \gamma$ of that non-terminal.

    E.g. for the item  $S \rightarrow \, S + \bullet S, 0, 2$ in $B_2$
    we add the two items $S \rightarrow \, \bullet x, 2, 2$ and $S \rightarrow \, \bullet S + S, 2, 2$ corresponding
    to the two alternates of $S$. The bullet is set to the beginning of the right-hand side of the production
    rule, the origin and end are set to $j = 2$ to indicate that we are starting to parse in the current bin and
    have not parsed anything so far.
  \item The \textit{Complete} operation applies if we process an item with the bullet at the end of the
    right-hand side of its production rule. For an item $B \rightarrow \, \gamma \bullet, j, k$ we have successfully parsed the substring
    $\omega [ j..k \rangle$, indices $j$ and $k$ being inclusive respectively exclusive, and are now going back to the origin bin $B_j$ where we predicted this non-terminal. There we look for any item of the form
    $A \rightarrow \, \alpha \bullet B \beta, i, j$ containing a bullet in front of the non-terminal we completed, or the reason we
    predicted it in the first place. Since we parsed the predicted non-terminal successfully, we are allowed to
    move over the bullet, resulting in one new item $A \rightarrow \, \alpha B \bullet \beta, i, k$. Note in particular
    the origin and end indices.

    Looking back at our example, we can add the item $S \rightarrow \, S + S \bullet, 0, 5$ to bin $B_5$
    for two different reasons corresponding to the two different ways we can derive \omega.
    When processing $S \rightarrow \, x \bullet, 4, 5$ we find $S \rightarrow \, S + \bullet S, 0, 4$ in the origin
    bin $B_4$ which corresponds to recognizing $(x + x) + x$. We would add the same item again
    while applying the \textit{Complete} operation to $S \rightarrow \, S + S \bullet, 2, 5$ and $S \rightarrow \, S + \bullet S, 0, 2$
    which corresponds to recognizing the input as $x + (x + x)$.
\end{enumerate}

If the algorithm encounters an item of the form $S \rightarrow \, \alpha, 0, \lvert \omega \rvert$,
it returns \textit{true}, otherwise it returns \textit{false}. For the tiny arithmetic expression grammar
we generate the item $S \rightarrow \, S + S \bullet, 0, 5$ and return the correct answer \textit{true},
since there exist derivations for $\omega = x + x + x$, e.g.
$S \Rightarrow S + S \Rightarrow x + S \Rightarrow x + S + S \Rightarrow^{\ast} x + x + x$ or
$S \Rightarrow S + S \Rightarrow S + x \Rightarrow S + S + x \Rightarrow^{\ast} x + x + x$.

To prove correctness of Earley's recognizer algorithm we need to show the following theorem:

$$S \rightarrow \, \alpha \bullet, 0, \lvert \omega \rvert \in B \,\,\, \textrm{iff} \,\,\, S \, \Rightarrow^{\ast} \, @{term \<omega>}$$

It follows from the following three lemmas about Earley items:

\begin{enumerate}
  \item Soundness: for every generated item there exists an according derivation: \\
     $A \rightarrow \, \alpha \bullet \beta, i, j \in B \,\,\, \textrm{implies} \,\,\, A \, \Rightarrow^{\ast} \, \omega [ i..j \rangle \beta$
  \item Completeness: for every derivation we generate an according item: \\
     $A \, \Rightarrow^{\ast} \, \omega [ i..j \rangle \beta \,\,\, \textrm{implies} \,\,\, A \rightarrow \, \alpha \bullet \beta, i, j \in B$
  \item Finiteness: there only exist a finite number of Earley items
\end{enumerate}
\<close>

text\<open>
  \begin{figure}[htpb]
    \centering

    \begin{mathpar}
      \inferrule [Init]
      {\\}
      {$S \rightarrow \, \bullet\alpha, 0, 0$}
  
      \inferrule [Scan]
      {$A \rightarrow \, \alpha \bullet a \beta, i, j$ \\ $@{term "\<omega>"}[j] = a$}
      {$A \rightarrow \, \alpha a \bullet \beta, i, j+1$}
  
      \inferrule [Predict]
      {$A \rightarrow \, \alpha \bullet B \beta, i, j$ \\ $(B \rightarrow \, \gamma) \, \in \, @{term "\<G>"}$}
      {$B \rightarrow \, \bullet \gamma, j, j$}
  
      \inferrule [Complete]
      {$A \rightarrow \, \alpha \bullet B \beta, i, j$ \\ $B \rightarrow \, \gamma \bullet, j, k$}
      {$A \rightarrow \, \alpha B \bullet \beta, i, k$}
    \end{mathpar}
    \caption[Earley inference rules]{Earley inference rules}\label{fig:earley-inference-rules}
    \label{fig:inference_rules}
  \end{figure}
\<close>

text\<open>
  \begin{table}[htpb] 
    \caption[Earley items running example]{Earley items for the grammar @{term \<G>}: $\, S ::= x \,\, \vert \,\, S + S$}\label{tab:earley-items}
    \centering
    \begin{tabular}{| l | l | l |}
        $B_0$                                   & $B_1$                                    & $B_2$                                \\
      \midrule
        $S \rightarrow \, \bullet x, 0, 0$      & $S \rightarrow \, x \bullet, 0, 1$     & $S \rightarrow \, S + \bullet S, 0, 2$ \\
        $S \rightarrow \, \bullet S + S, 0 , 0$ & $S \rightarrow \, S \bullet + S, 0, 1$ & $S \rightarrow \, \bullet x, 2, 2$     \\
                                                &                                        & $S \rightarrow \, \bullet S + S, 2, 2$ \\

      \midrule

        $B_3$                                  & $B_4$                                    & $B_5$                                \\
      \midrule
        $S \rightarrow \, x \bullet, 2, 3$     & $S \rightarrow \, S + \bullet S, 2, 4$ & $S \rightarrow \, x \bullet, 4, 5$     \\
        $S \rightarrow \, S + S \bullet, 0, 3$ & $S \rightarrow \, S + \bullet S, 0, 4$ & $S \rightarrow \, S + S \bullet, 2, 5$ \\
        $S \rightarrow \, S \bullet + S, 2, 3$ & $S \rightarrow \, \bullet x, 4, 4$     & $S \rightarrow \, S + S \bullet, 0, 5$ \\
        $S \rightarrow \, S \bullet + S, 0, 3$ & $S \rightarrow \, \bullet S + S, 4, 4$ & $S \rightarrow \, S \bullet + S, 4, 5$ \\
                                               &                                        & $S \rightarrow \, S \bullet + S, 2, 5$ \\
                                               &                                        & $S \rightarrow \, S \bullet + S, 0, 5$ \\
    \end{tabular}
    \label{tab:earley_bins}
  \end{table}
\<close>

(*<*)
end
(*>*)
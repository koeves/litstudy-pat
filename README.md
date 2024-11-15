---
author:
- |
  Daniel Köves  
  [`d.koves@student.vu.nl`](mailto:d.koves@student.vu.nl)  
  Supervisors  
  Femke van Raamsdonk  
  Jörg Endrullis
bibliography:
- cite.bib
date: October 2024
title: |
  Literature Study on Algorithms  
  for Pattern Completeness  
  Vrije Universiteit Amsterdam  
  <embed src="images/vu-griffioen.pdf" style="height:28mm" />
---

# Introduction

The following literature review aims to explore pattern completeness and
the related notion of quasi-reducibility of term rewriting systems.
Pattern completeness denotes the property that given a term rewrite
system with left hand sides $`L`$, for any given term $`f(t)`$ where
$`f`$ is a defined symbol, it is matched by some left hand side
$`\ell \in L`$. Quasi-reducibility relaxed this definition, allowing for
matches to happen under the root, i.e. given any term $`t = f(x)`$, a
left hand side $`\ell \in L`$ matches a subterm of $`t`$. Pattern
completeness intuitively means that the definition of $`f`$ is
*complete*, e.g. when we think about functional programs that use
pattern matching. Whereas with quasi-reduciblity we mean that the term
can further be reduced in the system, or the execution of a program
doesn’t get stuck.

The main entry-point of the review is the paper by Thiemann and Yamada ,
in which the authors present a novel algorithm to decide pattern
completeness. The algorithm, described in detail in section
<a href="#thiemann-yamada" data-reference-type="ref"
data-reference="thiemann-yamada">2.1</a>, is compared against other
implementations, namely the *complement algorithm* of Lazrek et al. .
Moreover, tree automata-based solution proved useful at determining
pattern completeness, therefore a short introduction at that
construction is also detailed. Furthermore, other notable works of
literature are also briefly presented.

The organisation of the paper is the following: the rest of section
<a href="#intro" data-reference-type="ref" data-reference="intro">1</a>
introduces some mathematical preliminaries and details the problem at
hand – pattern completeness and quasi-reducibility of term rewrite
systems. The algorithm in the Thiemann and Yamada paper is explored in
detail and analysed in section
<a href="#thiemann-yamada" data-reference-type="ref"
data-reference="thiemann-yamada">2.1</a>, whereas the complement
algorithm is presented in the sections following it. The paper also
briefly mentions further notable related work, such as
quasi-reducibility and decidability thereof as presented by Kapur et al
, further techniques for pattern matching and pattern completeness in
section <a href="#notable-work" data-reference-type="ref"
data-reference="notable-work">2.4</a>. Following the review, the main
algorithms are compared and their differences are discussed in section
<a href="#discussion" data-reference-type="ref"
data-reference="discussion">3</a>, and finally, concluding remarks are
found in section <a href="#conclusion" data-reference-type="ref"
data-reference="conclusion">4</a>.

The main focus of the review is to discuss algorithms for deciding
pattern completeness. The notion of pattern completeness comes up in
functional programming, namely, most languages that work by means of
pattern matching require (or in other cases – warn) that the defined
patterns are incomplete. Running a program with an incomplete pattern
would result in untimely termination of the program with an exception.
Figure <a href="#fig:haskell-incomplete" data-reference-type="ref"
data-reference="fig:haskell-incomplete">1</a> shows such an example, the
case matching `Nothing` is missing.

<figure id="fig:haskell-incomplete">
<div class="sourceCode" id="cb1"><pre
class="sourceCode haskell"><code class="sourceCode haskell"><span id="cb1-1"><a href="#cb1-1" aria-hidden="true" tabindex="-1"></a><span class="ot">maybeAddOne ::</span> <span class="dt">Maybe</span> <span class="dt">Int</span> <span class="ot">-&gt;</span> <span class="dt">Int</span></span>
<span id="cb1-2"><a href="#cb1-2" aria-hidden="true" tabindex="-1"></a>maybeAddOne (<span class="dt">Just</span> n) <span class="ot">=</span> n <span class="op">+</span> <span class="dv">1</span></span></code></pre></div>
<figcaption>Haskell snippet with an incomplete pattern</figcaption>
</figure>

It is, therefore, crucial to ensure that patterns are complete. A
related notion for term rewriting systems is quasi-reducibility
introduced in , that ensures that the evaluation cannot get stuck. The
difference between the two notions are discussed in section
<a href="#quasi-intro" data-reference-type="ref"
data-reference="quasi-intro">1.3</a>.

## Preliminaries and Notation

Given a signature $`\Sigma`$ a set of function symbols $`f \in \Sigma`$
and a set of variables $`\mathcal{X}`$, we say that terms
$`\mathcal{T}(\Sigma, \mathcal{X})`$ are the smallest set such that
$`\mathcal{X} \subseteq \mathcal{T}(\Sigma, \mathcal{X})`$ and
$`f(t_1, ..., t_n) \in \mathcal{T}(\Sigma, \mathcal{X})`$ given
$`f \in \Sigma`$ of arity $`n`$ and variables
$`t_1, ..., t_n \in \mathcal{X}`$. By $`\mathcal{V}ar(t)`$ we denote the
set of variables in $`t`$. Ground terms, denoted as $`T(\Sigma)`$ are
terms without variables. A term $`s`$ is subterm of $`t`$ if $`s = t`$
or $`t = f(t_1, ..., t_n)`$ and s is subterm of some $`t_i`$ given
$`1 \leq i \leq n`$. A set of positions $`\mathcal{P}os(t)`$ of term
$`t`$ is defined as the set $`\{\epsilon\}`$ when $`t \in \mathcal{X}`$,
otherwise the set
$`\{\epsilon\} \cup \{ip \mid p \in \mathcal{P}os(t_i)\}`$. By $`t|_p`$
we note the subterm of $`t`$ at position $`p`$.

Given a set of sorts $`\mathcal{S}`$, a sorted set $`\mathcal{V}`$ is a
set in which each element is associated with a sort
$`\iota \in \mathcal{S}`$ written as $`v : \iota \in \mathcal{V}`$.
Given a sorted signature $`\mathcal{F}`$ and sorted set of variables
$`\mathcal{V}`$, we define sorted terms as
$`\mathcal{T}(\mathcal{F}, \mathcal{V})`$.

A substitution $`\sigma`$ is a mapping
$`\mathcal{X} \rightarrow \mathcal{T}(\Sigma, \mathcal{X})`$. Notations
include $`\sigma(t)`$, $`t\sigma`$ or $`t^\sigma`$, all meaning the
substitution $`\sigma`$ applied to term $`t`$.

A rewrite rule $`(\ell \rightarrow r)`$ is a pair $`(\ell, r)`$ such
that $`\ell \notin \mathcal{X}`$ and
$`\mathcal{V}ar(r) \subseteq \mathcal{V}ar(\ell)`$.

A term rewrite system $`\mathcal{R}`$ is a pair $`(\Sigma, R)`$ where
$`R`$ is a set of rewrite rules between
$`\mathcal{T}(\Sigma, \mathcal{X})`$. In a TRS $`\mathcal{R}`$ over
$`\Sigma`$, defined symbols $`\mathcal{D}`$ are the root function
symbols of the left hand sides of the rewrite rules, and constructor
terms $`\mathcal{C}`$ are defined as $`\Sigma \setminus \mathcal{D}`$.
Inputs to functions are therefore represented by constructor ground
terms.

<div class="example">

**Example 1**. Consider the following term rewrite system representing
Combinatory Logic $`\mathcal{R}_{CL}`$ given
$`\Sigma = \{S, K, I, \cdot\}`$ with arities $`\{0,0,0,2\}`$ in this
order. Rewrite rules are given as:
``` math
\begin{aligned}
    I \cdot x &\rightarrow x \\
    (K \cdot x) \cdot y &\rightarrow x \\
    ((S \cdot x) \cdot y) \cdot z &\rightarrow (x \cdot z) \cdot (y \cdot z)
\end{aligned}
```

</div>

## Pattern Completeness and the Pattern Problem

The *matching problem* asks, given two terms $`s`$ and $`t`$, whether
there exists a substitution $`\sigma`$ such that $`s\sigma = t`$. A
matching problem $`mp`$ is represented as a set
$`\{(t_1, \ell_1), ..., (t_n, \ell_n)\} \subseteq \mathcal{T}(\mathcal{F}, \mathcal{V}) \times \mathcal{T}(\mathcal{F}, \mathcal{X})`$,
assuming $`\mathcal{V}`$ and $`\mathcal{X}`$ do not overlap. A pattern
problem $`pp`$ is a finite set of matching problems. A matching problem
is complete, if given a constructor ground substitution
$`\sigma : \mathcal{V} \mapsto \mathcal{T}(\mathcal{C})`$, there is
substitution $`\gamma : \mathcal{X} \mapsto \mathcal{T}(\mathcal{F})`$
such that $`t\sigma = \ell\gamma`$ for all $`(t, \ell) \in mp`$. A
pattern problem is complete if for each constructor ground substitution
$`\sigma`$ there is some $`mp \in pp`$ that is complete. A set $`P`$ of
pattern problems is complete if all $`pp \in P`$ are complete.

A program with left-hand sides $`L`$ is pattern complete, if every basic
ground term of the form $`f(t_1, ..., t_n)`$ with $`f \in \mathcal{D}`$
and
$`\{t_1, ..., t_n\} \subseteq \mathcal{T}(\mathcal{C}, \mathcal{X})`$ is
matched by some $`\ell \in L`$. The question whether a program with left
hand sides $`L`$ and defined symbols $`\mathcal{D}`$ is pattern complete
can be expressed with the following set of pattern problems:
``` math
P = \{\{\{(f(x_1, ..., x_n), \ell)\} \mid \ell \in L\} \mid f: \iota_1, ..., \iota_n \rightarrow \iota_0 \in \mathcal{D}\}
```

<div id="example-even" class="example">

**Example 2**. Consider as example the following sorted term rewrite
system to calculate whether a natural number is even. The TRS
$`\mathcal{R}_\mathbb{N}`$ is given as, adapted from Example 1 in :
``` math
\begin{aligned}
   \mathcal{C}_{\mathbb{N}} &= \{\text{true}: \mathbb{B}, \text{false}: \mathbb{B}, 0: \mathbb{N}, s: \mathbb{N} \rightarrow \mathbb{N}\} \\
\mathcal{D}_{\mathbb{N}} &= \{\text{even}: \mathbb{N} \rightarrow \mathbb{B}\} 
\end{aligned}
```
with the following rules:
``` math
\begin{aligned}
    \text{even}(0) &\rightarrow \text{true} & \text{even}(s(0)) &\rightarrow \text{false} & \text{even}(s(s(x))) &\rightarrow \text{true}
\end{aligned}
```
In this setting consider the following matching problems:
``` math
\begin{aligned}
    mp_1 &= \{(z, 0)\} & mp_2 &= \{(\text{even}(z), 0)\}
\end{aligned}
```
Matching problem $`mp_1`$ is complete with respect to
$`\sigma = \{z \mapsto 0\}`$, however $`mp_2`$ is incomplete since there
exists no $`\sigma`$ such that $`\text{even}(x)^\sigma = 0`$. The set of
pattern problems describing this program would be:
``` math
P = \{\{\{(\text{even}(z), \text{even}(0))\}, \{(\text{even}(z), \text{even}(s(x)))\}, \{(\text{even}(z), \text{even}(s(s(x))))\}\}\}
```

</div>

## Quasi-reducibility

A related notion to pattern completeness is quasi-reducibility, the
difference being that as per the definition in Section
<a href="#def-pattern-complete" data-reference-type="ref"
data-reference="def-pattern-complete">1.2</a>, pattern completeness does
not allow for matching below the root term. This condition is relaxed
when talking about quasi-reducibility. The notion of quasi-reducibility
aligns with *sufficient* or *relative completeness* in . Take as example
the extended version of Example
<a href="#example-even" data-reference-type="ref"
data-reference="example-even">2</a> for integers using
successor-predecessor notation, taken from Example 4 of the Thiemann and
Yamada paper .

<div id="quasi-ex-complete" class="example">

**Example 3**. Given TRS $`\mathcal{R}_{\mathbb{Z}}`$ using
``` math
\begin{aligned}
    \mathcal{C}_{\mathbb{Z}} &= \{\text{true}: \mathbb{B}, \text{false}: \mathbb{B}, 0: \mathbb{Z}, s: \mathbb{Z} \rightarrow \mathbb{N}, p: \mathbb{Z} \rightarrow \mathbb{N}\} \\
    \mathcal{D}_{\mathbb{Z}} &= \{\text{even}: \mathbb{Z} \rightarrow \mathbb{B}\}
\end{aligned}
```
with rules:
``` math
\begin{aligned}
    \text{even}(0) &\rightarrow \text{true} & \text{even}(s(0)) &\rightarrow \text{false} & \text{even}(s(s(x))) &\rightarrow \text{true} \\
    \text{even}(p(0)) &\rightarrow \text{false} &
    \text{even}(p(p(x))) &\rightarrow \text{even}(x) \\ 
    s(p(x)) &\rightarrow x & p(s(x)) &\rightarrow x
\end{aligned}
```

</div>

The term rewriting system is quasi-reducible, every term in the form
$`even(z)`$ has a subterm that matches one of the rules. All integers
are covered by the first rules and if our term contains both $`s`$ and
$`p`$, the last two rules apply. However, the system is not pattern
complete, because e.g. the term $`\text{even}(s(p(0)))`$ is not matched
by any left hand side.

The difference between the notions of pattern completeness and
quasi-reducibility is also illustrated by Example
<a href="#quasi-ex" data-reference-type="ref"
data-reference="quasi-ex">8</a>, in which it is algorithmically
confirmed that $`\mathcal{R}_{\mathbb{Z}}`$ is not pattern complete, and
in Example <a href="#quasi-ex-alg" data-reference-type="ref"
data-reference="quasi-ex-alg">11</a> in which it is algorithmically
confirmed to be quasi-reducible.

# Literature Review

This section, describes the bodies of literature the paper is interested
in. It begins by examining the main interest, namely the paper by
Thiemann and Yamada. Most attention is spent on this paper, their
algorithm is introduced and its correctness and properties are
discussed. Furthermore, some examples of certain are used to illustrate
the behaviour of the algorithm.

Following, the *complement algorithm* by Lazrek et al. is detailed, an
algorithm to decide sufficient completeness (and indirectly also pattern
completeness, as shown later). Finally, a tree automata-based
construction is presented that can be used to decide pattern
completeness. At the end of the section, further literature of interest
is briefly listed.

## Thiemann and Yamada

The algorithm presented in the paper of Thiemann and Yamada works on
multisets of pattern problems and applies rules on the innermost
matching problems, pattern problems and sets of pattern problems. Two
iterations are presented, one dealing with only linear inputs (where no
variable appears multiple times in the left-hand sides), and a further
iteration with additional rules to handle non-linearity. The rules of
the algorithm are presented here in a slightly different notation.

Matching problems (denoted as $`mp`$) are reduced using the following
rules:
``` math
\begin{aligned}
\textbf{decompose} & & \{(f(t_1, ..., t_n), f(l_1, ..., l_n))\} &\rightarrow \{(t_1, l_1), ..., (t_n, l_n)\} \\
\textbf{match} & & \{(t, x)\} &\rightarrow \varnothing \text{ if } \forall (t', l) \in mp \text{. } x \notin Var(l) \\
\textbf{clash} & & \{(f(...), g(...))\} &\rightarrow \bot_{mp}\text{ if }f \neq g
\intertext{For pattern problems (sets of matching problems – denoted as $pp$), the following rules apply:}
\textbf{remove-mp} & & \{\bot_{mp}\} &\rightarrow \varnothing \\
\textbf{success} & & \{\varnothing\} &\rightarrow \top_{pp}
\intertext{Finally for sets of pattern problems (which is the input of the algorithm, denoted as $P$), the rules are as follows:}
\textbf{failure} & & \{\varnothing\} &\rightarrow \bot_P \\
\textbf{remove-pp} & & \{\top_{pp}\} &\rightarrow \varnothing \\
\textbf{instantiate} & & \{pp\} &\rightarrow \text{Inst$(pp,x)$ if }\{(x, f(...))\} \in pp
\end{aligned}
```

The last rule is applicable in case variable $`x`$ is tried to be
matched with some non-variable term $`f(...)`$. In this case, we
construct a new pattern problem $`pp\sigma_{x,c}`$ for each constructor
in $`\mathcal{C}`$, given as:
``` math
pp\sigma_{x,c} = \{\{ (t\sigma_{x,c},l) \mid (t,l) \in mp\} \mid mp \in pp\}
```
where
``` math
\sigma_{x,c} = [x \mapsto c(x_1, ..., x_n)]
```
for each $`c \in \mathcal{C}`$ of arity n, and fresh variables
$`x_1, ..., x_n`$.

In order the deal with non-linearity, further rules are introduced so
that the algorithm does not get stuck on non-linear input. These rules
are as follows:

``` math
\begin{aligned}
\textbf{clash'} & & \{(t,x), (t',x)\} \in mp &\rightarrow \bot_{mp}\text{ if $t$ and $t'$ clash} \\
\textbf{instantiate'} & & \{\{(t,x), (t',x)\}\} \in P &\rightarrow \text{Inst$(pp,x)$} \\
\textbf{failure'} & & \{pp\} \in P &\rightarrow \bot_P
\end{aligned}
```

In case of **instantiate’**, we can apply the rule if $`t`$ and $`t'`$
differ in variable $`x`$ of finite sort.

In case of **failure’**, we need to fail the algorithm if within each
$`mp \in pp`$ there exists $`\{(t,x),(t',x)\}`$ such that $`t`$ and
$`t'`$ differ in variable $`x`$ of infinite sort. This special case is
needed, as it would be impossible to instantiate a variable of infinite
sort, if we find that terms differ in such variable. In case not all
matching problems differ in such a variable, we can mark those problems
locally as $`\bot_{mp}`$ (via **clash’**).

We say a term $`t`$ and $`t'`$ clash if
$`t|_p=f(...) \neq g(...)=t'|_p`$. Terms $`t`$ and $`t'`$ differ in
variable $`x`$ if $`t|_p \neq t'|_p`$ and $`x \in \{t|_p, t'|_p\}`$.

The order, in which the reduction steps are applied in the list-based
implementation are given as follows:

1.  Exhaustively apply **decompose**, **clash** and **clash’**

2.  Exhaustively apply **match** and try to apply **failure’**

3.  Invoke **instantiate** or **instantiate’** with preference for the
    former

### Examples

The following examples illustrate certain executions of the algorithm.
We assume the sort of natural numbers with one defined symbol
$`f : \mathbb{N} \rightarrow \mathbb{N}`$, using the following
constructors
$`\mathcal{C}_{\mathbb{N}} = \{0 : \mathbb{N}, s(x) : \mathbb{N} \rightarrow \mathbb{N}\}`$.

<div id="ex-thiemann-lin" class="example">

**Example 4**. Linear case

Given a left-hand side of $`\{f(0), f(s(x))\}`$, the linear algorithm
would compute:
``` math
\begin{aligned}
    P &= \{\{\{(f(a), f(0))\}, \{(f(a), f(s(x)))\}\}\}\\
\text{decompose} &\Rrightarrow^{*} \{\{\{(a, 0)\}, \{(a, s(x))\}\}\} \\
\text{instantiate} &\Rrightarrow^{*} \{\{\{(0, 0)\}\}, \{\{(s(z), s(x))\}\}\} \\
\text{match} &\Rrightarrow \{\{\bot_{mp}\}, \{\{(s(z), s(x))\}\}\} \\
\text{remove-mp} &\Rrightarrow^{*} \{\{\varnothing\}, \{\{(s(z), s(x))\}\}\} \\
\text{decompose} &\Rrightarrow \{\{\varnothing\}, \{\{(z, x)\}\}\} \\
\text{match} &\Rrightarrow \{\{\varnothing\}, \{\varnothing\}\} \\
\text{success} &\Rrightarrow^{*} \{\top_{pp}, \top_{pp}\} \\
\text{remove-pp} &\Rrightarrow^{*} \varnothing
\end{aligned}
```

</div>

The algorithm concludes that the left hand sides are pattern complete.

<div id="ex-thiemann-lin-fail" class="example">

**Example 5**. Linear case failure

The following example demonstrates how the algorithm would find an
incomplete pattern:
``` math
\begin{aligned}
    P &= \{\{\{(f(a), f(s(x))\}\}\}\\
\text{decompose} &\Rrightarrow \{\{\{(a, s(x))\}\}\} \\
\text{instantiate} &\Rrightarrow \{\{\{(0, s(x))\}\}, \{\{(s(z), s(x))\}\}\} \\
\text{clash} &\Rrightarrow \{\{\bot_{mp}\}, \{(s(z), s(x))\}\} \\
\text{remove-mp} &\Rrightarrow \{\varnothing, \{(s(z), s(x))\}\} \\
\text{failure} &\Rrightarrow \bot_{P}
\end{aligned}
```

</div>

Here we could have further reduced the pattern problem
$`\{\{(s(z), s(x))\}\}`$, however, do the incomplete case
$`\{\{(0, s(x))\}\}`$ resulting in $`\varnothing`$, the whole pattern
problem reduces to $`\bot_{P}`$.

<div id="example-general" class="example">

**Example 6**. General case

Given defined symbol
$`f : \mathbb{N} \times \mathbb{N} \rightarrow \mathbb{N}`$ the
following left-hand sides:  
$`\{\{f(x, x)\}, \{f(x, y)\}\}`$ the algorithm would compute:
``` math
\begin{aligned}
    P &= \{\{\{(f(a, b), f(x, x))\}, \{(f(a, b), f(x, y))\}\}\\
\text{decompose} &\Rrightarrow^{*} \{\{\{(a, x), (b, x)\}, \{(a, x), (b, y)\}\}\} \\
\text{clash'} &\Rrightarrow \{\{\bot_{mp}, \{(a, x), (b, y)\}\}\} \\
\text{remove-mp} &\Rrightarrow \{\{\{(a, x), (b, y)\}\}\} \\
\text{match} &\Rrightarrow^{*} \{\{\varnothing\}\} \\
\text{success} &\Rrightarrow^{*} \{\top_{pp}\} \\
\text{remove-pp} &\Rrightarrow^{*} \varnothing
\end{aligned}
```

</div>

<div class="example">

**Example 7**. Linear algorithm with non-linear input

The following example illustrates that the additional rules to match
non-linear inputs are necessary to decide pattern completeness, using
the non-linear left-hand side from Example
<a href="#example-general" data-reference-type="ref"
data-reference="example-general">6</a>:
``` math
\begin{aligned}
    P &= \{\{\{(f(a, b), f(x, x))\}\}\}\\
\text{decompose} &\Rrightarrow^{*} \{\{\{(a, x), (b, x)\}, \{(a, x), (b, y)\}\}\}
\end{aligned}
```
At this stage, the only rule we might want to apply is **match**.
However, due to the condition in that rule that the variable $`x`$
cannot appear in any right hand side within the matching problem, we
fail to apply the rule. Therefore, the algorithm is stuck, indeed no
other rule apply (not even **instantiate**, since $`x`$ is not a
constructor term). The correct step in this case would be to apply
**clash’**, available in the extension of the algorithm to the general
case.

</div>

<div id="quasi-ex" class="example">

**Example 8**. Quasi-reducible LHS is not pattern complete

Let us apply the algorithm to Example
<a href="#quasi-intro" data-reference-type="ref"
data-reference="quasi-intro">1.3</a>. In that example the following term
rewriting system $`\mathcal{R}_{\mathbb{Z}}`$ is presented, using
``` math
\mathcal{C}_{\mathbb{Z}} = \{\text{true}: \mathbb{B}, \text{false}: \mathbb{B}, 0: \mathbb{Z}, s: \mathbb{Z} \rightarrow \mathbb{N}, p: \mathbb{Z} \rightarrow \mathbb{N}\}
```
with one defined symbol
$`\mathcal{D}_{\mathbb{Z}} = \{\text{even}: \mathbb{Z} \rightarrow \mathbb{B}\}`$:
``` math
\begin{aligned}
    \text{even}(0) &\rightarrow \text{true} & \text{even}(s(0)) &\rightarrow \text{false} & \text{even}(s(s(x))) &\rightarrow \text{true} \\
    \text{even}(p(0)) &\rightarrow \text{false} &
    \text{even}(p(p(x))) &\rightarrow \text{even}(x) \\ 
    s(p(x)) &\rightarrow x & p(s(x)) &\rightarrow x
\end{aligned}
```
The algorithm would compute:
``` math
\begin{aligned}
    P = &\{\{\{(even(z), even(0))\}, \{(even(z), even(s(0)))\}, \\
    &\{(even(z), even(s(s(x))))\}, \{(even(z), even(p(0)))\}, \\
    &\{(even(z), even(p(p(x))))\}, \{(even(z), even(p(p(0))))\}, \\
    &\{(even(z), s(p(x)))\}, \{(even(z), p(s(x)))\}\} \\
    \Rrightarrow^{*} &\{\{\{(s(z), 0)\},  \{(s(z), p(x))\}\}, \{\{(p(z), 0)\},\{(p(z), s(x))\}\}\}
\end{aligned}
```

Previous steps are omitted for brevity, the only problematic pattern
problems are the ones above, all other cases are resolved with
$`\top_{pp}`$. These cases, however, would result in clashes, therefore
the whole pattern problem reduces to an empty set, marking $`P`$ as
$`\bot_{P}`$.

</div>

### Analysis

In this section we shall explore the correctness of the algorithm.

The normal forms of the reduction steps is one of
$`\{\varnothing, \bot_{P}\}`$. The algorithm iteratively removes
matching problems with **match** or marks them incomplete with
**clash**. Using the definition of completeness in Section
<a href="#def-pattern-complete" data-reference-type="ref"
data-reference="def-pattern-complete">1.2</a>, a pattern problem $`pp`$
is complete if for each constructor ground substitution $`\sigma`$,
there exists a matching problem $`mp \in pp`$ that is complete.
Therefore, the pattern problem is marked $`\top_{pp}`$ by **success**
when the pattern problem reduces to $`\varnothing`$ by removing all
clashed and matching problems via **remove-mp**. When the pattern
problem reduces to the empty set we can conclude that at least one
**match** has taken place, therefore, the pattern is complete. On the
other hand, when no match has taken place, the matching problem reduces
to $`\{\bot_{mp}\}`$. The notation here is bit subtle, due to the nested
empty sets. Namely, what leads to a pattern problem being marked
successful is an empty pattern problem $`\{\varnothing\}`$. Furthermore,
what leads to the whole execution marked as failure is a pattern problem
containing only $`\bot_{mp}`$. The reader can refer to the examples in
Section <a href="#examples-alg" data-reference-type="ref"
data-reference="examples-alg">2.1.1</a> for further clarification.

Furthermore, the algorithm is shown to be decidable and terminating when
the set of pattern problems are left-linear. The termination proof is
given by defining a measure of difference $`\abs{\ell - t}`$ between
terms $`(\ell, t)`$ of a matching problem as:

- $`\abs{\ell - x}`$ the number of function symbols in $`\ell`$

- $`\abs{f(\ell_1, ..., \ell_n) - f(t_1,...,t_n)} = \sum_{i=1}^{n} \abs{\ell_i - t_i}`$

- $`\abs{\ell - t} = 0`$ otherwise

This measure is lifted to pattern problems by:
``` math
\abs{pp}_{\text{diff}} = \sum_{mp \in pp, (t, \ell) \in mp} \abs{\ell - t}
```
Then, the relation $`\succ`$ is defined for sets of pattern problems by
extending $`>`$ to multisets $`>^{\text{mul}}`$ by:
``` math
P \succ P' \iff \{\abs{pp}_\text{diff} \mid pp \in P\} >^{\text{mul}} \{\abs{pp'}_\text{diff} \mid pp' \in P'\}
```
. The relation $`\succ`$ is strongly normalizing, each step of the
algorithm weakly decreases, while the instantiate rule strictly
decreases with respect to $`\succ`$ .

## Lazrek et al.

The *complement algorithm* presented by Lazrek et al. in , represents a
mechanism to conclude whether in a TRS $`\mathcal{R}`$, a defined symbol
$`f`$ (called operator in the paper) is convertible to a set of
constructors, denoted as *relative* completeness. The algorithm can also
be used to decide quasi-reducibility and indirectly pattern
completeness, as demonstrated by Example
<a href="#quasi-ex-alg" data-reference-type="ref"
data-reference="quasi-ex-alg">11</a>. The main idea behind the algorithm
is to compute the *complement* of matched terms, then iteratively check
whether the complement can be further reduced or matched. The complement
of a term $`t`$ means the ground terms of $`t`$ and the complement of
$`t`$ equal the set of constructor terms.

The algorithm works on pairs of sets $`M_i`$ and $`N_i`$, each iteration
$`M_{i+1}`$ and $`N_{i+1}`$ are constructed from their previous
counterpart. The algorithm starts by setting $`M_0`$ as the set
representing the left-hand sides of $`\mathcal{R}`$, and the set $`N_0`$
as the set of ground instances of $`f`$ of the form $`f(x_1, ..., x_n)`$
where $`f \in \mathcal{D}`$. The algorithm then iteratively tries to
unify elements of $`N_0`$ with the elements of $`M_0`$ with a linear
substitution $`\sigma`$. In case such a linear substitution is found,
the matched elements $`m \in M`$ and $`n \in N`$ are removed from
$`M_i`$ and $`N_i`$ and new sets $`M_{i+1}`$ and $`N_{i+1}`$ are
constructed. Elements $`m`$ and $`n`$ are removed from their respective
sets and new elements in $`\{m\rho\}`$ and $`\{n\rho\}`$ are added.
Substitution $`\rho_i`$ is the set $`C(\sigma)`$ of complement of
substitution of $`\sigma`$, i.e.:
``` math
\begin{aligned}
    M_{i+1} &= M_{i-1} \setminus \{m\} \cup \{m\rho \mid \rho \in C(\sigma), m\rho \neq m\sigma\} \\
    N_{i+1} &= N_{i-1} \setminus \{n\} \cup \{n\rho \mid \rho \in C(\sigma), n\rho \neq n\sigma\}
\end{aligned}
```

The complement of a substitution $`\sigma`$ defined as the set
$`C(\sigma)`$ of all substitutions $`\rho`$ different from $`\sigma`$,
having the same domain and mapping elements to complementary terms.

The *complement* of a ground term $`t = c_j(t_1, ... , t_n)`$ given
$`\mathcal{C} = \{c_1, ..., c_n\}`$, $`1 \leq j \leq n`$ is the set
$`C(t)`$, such that $`C(x) = \{x\}`$ given $`x \in \mathcal{X}`$,
otherwise the set
$`\{c_i(C(t_1), ..., C(t_n) \mid 1\leq i \leq n, i \neq j\}`$.

The algorithm continues until $`M_{last}`$ or $`N_{last}`$ are empty
(i.e. the last pair of $`M`$ and $`N`$ sets), or no further unification
is possible. If both $`M_{last}`$ and $`N_{last}`$ are empty, $`f`$ is
convertible to the constructors ($`f`$ covers all input terms and/or the
complement can be further reduced by the rules). If $`M_{last}`$ is
empty but $`N_{last}`$ is not empty, $`f`$ is not defined on the terms
in $`N_{last}`$.

The set $`N_{last}`$ is interesting, as it contains the patterns not
matched by $`f`$. It can, therefore, be used in a functional programming
setting, warning the user of incomplete patterns (and hinting on actual
constructor patterns currently unmatched).

From these, quasi-reducibility is determined when either each input term
is matched by the LHS of $`f`$ (both $`M_{last}`$ and $`N_{last}`$ are
empty), or the elements of $`N_{last}`$ can further be reduced.

Pattern completeness is given in case both $`M_{last}`$ and $`N_{last}`$
are empty.

<div class="example">

**Example 9**. Let us take an example execution of the algorithm on the
same input as Example
<a href="#ex-thiemann-lin" data-reference-type="ref"
data-reference="ex-thiemann-lin">4</a>.

``` math
\begin{aligned}
    M_0 &= \{f(0), f(succ(x))\} \\
    N_0 &= \{f(z)\} \\
    \Rightarrow M_1 &= \{f(succ(x))\} \\
    N_1 &= \{f(succ(z))\} \\
    \Rightarrow M_2 &= \varnothing \\
    N_2 &= \varnothing
\end{aligned}
```

The sets $`M_0`$ and $`N_0`$ are the starting steps, we would like to
check whether $`f(z)`$ is convertible with the left-hand sides of the
system. In the first iteration the case of $`f(0)`$ and $`f(z)`$ are
unified by the substitution $`\sigma = \{z \mapsto 0\}`$. Then we pick a
substitution $`\rho`$ from the set of complement substitutions
$`C(\sigma)`$, take $`\rho = \{z \mapsto succ(z)\}`$. In the last step,
we take $`\sigma = \{z \mapsto x\}`$. Since both $`M_2`$ and $`N_2`$ are
empty, the definition of $`f`$ is said to be *relatively complete*.

</div>

<div class="example">

**Example 10**. The counterpart of Example
<a href="#ex-thiemann-lin-fail" data-reference-type="ref"
data-reference="ex-thiemann-lin-fail">5</a>:

``` math
\begin{aligned}
    M_0 &= \{f(succ(x))\} \\
    N_0 &= \{f(z)\} \\
    \Rightarrow M_1 &= \varnothing \\
    N_1 &= \{f(0)\} \\
\end{aligned}
```

In the first step we try to unify $`f(succ(x))`$ with $`f(z)`$. This we
can do via $`\sigma = \{z \mapsto succ(x)\}`$. Then we take $`\rho`$
from $`C(\sigma)`$ as $`\rho = \{z \mapsto 0\}`$, after which we try to
unify $`f(succ(x))`$ and $`f(0)`$, which fails. In $`N_1`$ we find the
term that is not covered by the definition of $`f`$ (it is not further
reducable), therefore $`f`$ is not relatively complete.

</div>

<div id="quasi-ex-alg" class="example">

**Example 11**. Finally, the quasi-reducible system
$`\mathcal{R}_\mathbb{Z}`$ from Examples
<a href="#quasi-ex-complete" data-reference-type="ref"
data-reference="quasi-ex-complete">3</a>,
<a href="#quasi-ex" data-reference-type="ref"
data-reference="quasi-ex">8</a>:
``` math
\begin{aligned}
    M_0 &= \{even(0), even(s(0)), even(s(s(x))), even(p(0)), even(p(p(x)))\} \\
    N_0 &= \{even(z)\} \\
    \Rightarrow M_1 &= \{even(s(0)), even(s(s(x))), even(p(0)), even(p(p(x)))\} \\
    N_1 &= \{even(s(z)), even(p(z))\} \\
    \Rightarrow M_2 &= \{even(s(s(x))), even(p(p(x)))\} \\
    N_2 &= \{even(s(s(z))), even(s(p(z))), even(p(s(z))), even(p(p(z)))\} \\
    \Rightarrow M_3 &= \varnothing \\
    N_3 &= \{even(s(p(z))), even(p(s(z)))\}
\end{aligned}
```

Note the fact that $`M_0`$ does not contain left-hand sides $`s(p(x))`$
and $`p(s(x))`$ since they are not about ground terms of $`even(z)`$.

In the first step we unify via $`\sigma = \{z \mapsto 0\}`$, then apply
$`C(\sigma)`$, i.e.: $`\{z \mapsto s(z)\}`$ and $`\{z \mapsto p(z)\}`$.
We apply the same substitutions again to arrive at $`M_2`$. There, terms
$`even(s(s(x)))`$ and $`even(p(p(x)))`$ are trivially matched by
$`even(s(s(z)))`$ and $`even(p(p(z)))`$, therefore these pairs are
removed. Finally, $`M_3`$ is empty so the algorithm stops. $`N_3`$
contains the patterns that are not defined for $`even`$, however, both
these terms are further $`\mathcal{R}_\mathbb{Z}`$-reducible by the
rules. Therefore, the definition of $`even`$ is relatively complete. We
can notice that the algorithm indirectly also proven pattern
incompleteness, as $`N_3`$ contains patterns where the function $`even`$
needs to be defined.

</div>

## Tree automata-based algorithms

Pattern completeness of left-linear systems can also be verified using
tree automata based solution, e.g. with the framework developed by
Middeldorp et al. in or by Bouhoula et al. in . The experiments done by
Thiemann in Yamada in construct tree automata $`\mathcal{A}`$ and
$`\mathcal{B}`$ for their test cases and verify the language inclusion
problem $`\mathcal{L}(\mathcal{A}) \subseteq \mathcal{L}(\mathcal{B})`$
via the framework.

Tree automaton $`\mathcal{A}`$ over an alphabet $`\mathcal{F}`$ is
defined as the 4-tuple $`(Q,\mathcal{F},Q_f,\Delta)`$, where $`Q`$ is
the set of states, $`Q_f \subseteq Q`$ are the final states, $`\Delta`$
are the transition rules between states. A term is accepted by
$`\mathcal{A}`$ if $`t \xrightarrow[\mathcal{A}]{*} q(t), q \in Q_f`$.
Bottom-up tree automata start their computation at the leaves of the
tree and move upwards, in contrast with top-down tree automata which
start at the root. The language $`\mathcal{L}(\mathcal{A})`$ of tree
automaton $`\mathcal{A}`$ is defined as the set of ground terms accepted
by $`\mathcal{A}`$ .

To translate pattern problems to tree automata domain, the following
construction can be used, as demonstrated in the paper of Thiemann and
Yamada. Firstly, for the term rewrite system two tree automata
$`\mathcal{A}`$ and $`\mathcal{B}`$ are constructed. Tree automata
$`\mathcal{A}`$ accepts each valid input of the term rewrite system,
whereas tree automata $`\mathcal{B}`$ accepts each left hand side of the
system. The pattern problem then reduces to the language inclusion
problem $`\mathcal{L}(\mathcal{A}) \subseteq \mathcal{L}(\mathcal{B})`$.
Namely, that for each term recognised by tree automaton $`\mathcal{A}`$,
there exist a matching term recognised by tree automaton
$`\mathcal{B}`$. Conversely, if there is an input term recognised by
tree automaton $`\mathcal{A}`$, but not recognised by tree automaton
$`\mathcal{B}`$, then there is an incomplete pattern.

The framework by Middeldorp et al. constructs bottom-up tree automata to
verify properties thereof, whereas the algorithm by Bouhoula et al.
construct many-rooted top-down tree automata.

## Further notable work

In , Thiel introduces calculus of components, on which the paper by
Lazrek et al. is based. The complement of a term $`t`$ in
$`\mathcal{T}(\mathcal{C}, \mathcal{X})`$ is defined as the finite set
$`T \subseteq \mathcal{T}(\mathcal{C}, \mathcal{X})`$ such that
$`G(t) \cup G(T) = \mathcal{T}(\mathcal{C})`$, i.e. the union ground
terms of $`t`$ and $`T`$ equal the constructor ground terms. Their
algorithm detail a way to decide sufficient completeness, similar to the
complement algorithm of .

Decidability of quasi-reducibility was shown by Kapur et al. in . Their
algorithm, however, is impractical in practice, as it has exponential
best-case complexity. The *complement algorithm* by Lazrek et al. is a
refinement on this paper.

In , Aoto and Toyama introduce *strong quasi-reducibility*, in their
paper Ground Confluence Prover based on Rewriting Induction. Strong
quasi-reducibility extends quasi-reducibility to term rewriting systems
with non-free constructors, i.e. constructors that can be further
reduced in the system.

Cynthia Kop derived quasi-reducibility in logically constrained term
rewriting systems in . These logically constrained TRSs are of the
nature: e.g. "rule $`x \rightarrow y`$ is applicable only if $`x > 5`$".

Bouhoula et al. constructed a tree-automata based framework to decide
sufficient completeness of logically constrained term rewrite systems in
.

The Glasgow Haskell Compiler performs pattern completeness checks by
enabling `-Wincomplete-patterns`. It applies, however, only to linear
patterns, as non-linear patterns like `f a a = ...` are not allowed by
the language, they need to be simulated by guards like
`f x y | x == y = ...`.

# Discussion

Both algorithms presented by Thiemann and Yamada in and by Lazrek et al.
in are able to decide whether a given term rewrite system is pattern
complete. The focus of the complement algorithm is to conclude relative
completeness, however, one can make use of $`N_{last}`$ to conclude
whether the program is also pattern complete. Namely, when that is not
empty, the set contains the patterns where the program still needs to be
defined. One notable difference between the two algorithms is that the
refined version of Thiemann and Yamada’s proven to work with non-linear
patterns, whereas, the algorithm by Lazrek et al. might not. The paper
by Lazrek et al. mentions certain examples of non-linearity where the
algorithm successfully completes, but also in cases where it would get
stuck.

Another aspect that makes the complement algorithm interesting is its
ability of counterexample generation. By default the contents of
$`N_{last}`$, after checking for irreducibility, contains the patterns
where the function $`f`$ still needs to be defined. The algorithm by
Thiemann and Yamada, by default, does not have this ability – though it
is mentioned as an easy improvement in the paper.

Tree automata have proven useful for deciding pattern completeness and
related notions, but current algorithms e.g. in are restricted to
left-linear systems.

One question that might arise after reviewing the above papers, is that
it remains to be seen how these algorithms would perform on a more
exhaustive performance testing against each other. Namely, the examples
created by Thiemann and Yamada clearly give the upper hand to their
algorithm, however, their method of example generation seems a bit
contrived. One might wonder how the algorithms would fare on more
"typical" inputs such as small functional programs from existing
projects. Moreover, the algorithms the Thiemann and Yamada paper check
against are not implemented or in any case tuned by the authors, but are
being used from 3rd party tools such as the ground confluence prover of
Aoto and Toyama , or the tree automata framework developed by Middeldorp
et al.. This fact might explain the constant factor performance
difference between the runtimes.

Finally, as suggested by Thiemann and Yamada, it remains to be seen
whether their algorithm can be adjusted to decide quasi-reducibility, or
whether a similar syntax-directed algorithm can be constructed.

# Conclusion

The paper set out to explore algorithms for deciding pattern
completeness in term rewrite systems. Pattern completeness is the notion
that given a term rewrite system with left hand sides $`L`$ and basic
ground term $`f(t)`$, the term is matched by some left hand side
$`\ell \in L`$. The notion of quasi-reducibility was also introduced
that relaxes the pattern completeness definition, allowing for matching
to happen under the root.

The main focus of the literature review is to detail the algorithm by
Thiemann and Yamada and compare and contrast it with the *complement
algorithm* of Lazrek et al. . Moreover, frameworks using tree automata
are proven useful for deciding pattern completeness and related
definitions. Therefore, a short introduction of this construction is
also discussed. Finally, a short survey of related literate is also
included at the end of Section
<a href="#review" data-reference-type="ref"
data-reference="review">2</a>.

Further research, as discussed in Section
<a href="#discussion" data-reference-type="ref"
data-reference="discussion">3</a>, could explore a more detailed and
exhaustive performance comparison of the discussed algorithms. Moreover,
as per , it remains open to construct a similar syntax-based algorithm
to decide quasi-reducibility.

---
nocite: \[@\*\]
references:
- annote: "Keywords: Isabelle/HOL, pattern matching, term rewriting"
  author:
  - family: Thiemann
    given: René
  - family: Yamada
    given: Akihisa
  collection-title: Leibniz international proceedings in informatics
    (LIPIcs)
  container-title: 9th international conference on formal structures for
    computation and deduction (FSCD 2024)
  doi: 10.4230/LIPIcs.FSCD.2024.27
  editor:
  - family: Rehof
    given: Jakob
  id: thiemann
  isbn: 978-3-95977-323-2
  issn: 1868-8969
  issued: 2024
  page: "27:1-27:17"
  publisher: Schloss Dagstuhl – Leibniz-Zentrum für Informatik
  publisher-place: Dagstuhl, Germany
  title: <span class="nocase">A Verified Algorithm for Deciding Pattern
    Completeness</span>
  type: paper-conference
  url: "https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2024.27"
  volume: 299
- author:
  - family: Kapur
    given: Deepak
  - family: Narendran
    given: Paliath
  - family: Zhang
    given: Hantao
  container-title: Acta Inf.
  doi: 10.1007/BF00292110
  id: kapur
  issn: 0001-5903
  issue: 4
  issued: 1987-08
  page: 395-415
  publisher: Springer-Verlag
  publisher-place: Berlin, Heidelberg
  title: On sufficient-completeness and related properties of term
    rewriting systems
  type: article-journal
  url: "https://doi.org/10.1007/BF00292110"
  volume: 24
- author:
  - family: Middeldorp
    given: Aart
  - family: Lochmann
    given: Alexander
  - family: Mitterwallner
    given: Fabian
  doi: 10.1007/s10817-023-09661-7
  id: middeldorp
  issn: 0168-7433
  issue: 2
  issued: 2023-04
  keyword: Term rewriting, First-order theory, Tree automata,
    Formalization
  publisher: Springer-Verlag
  publisher-place: Berlin, Heidelberg
  title: "First-order theory of rewriting for linear variable-separated
    rewrite systems: Automation, formalization, certification"
  title-short: First-order theory of rewriting for linear
    variable-separated rewrite systems
  type: article-journal
  url: "https://doi.org/10.1007/s10817-023-09661-7"
  volume: 67
- author:
  - family: Lazrek
    given: Azeddine
  - family: Lescanne
    given: Pierre
  - family: Thiel
    given: Jean-Jacques
  container-title: Information and Computation
  doi: "https://doi.org/10.1016/0890-5401(90)90033-E"
  id: lazrek
  issn: 0890-5401
  issue: 1
  issued: 1990
  page: 47-70
  title: Tools for proving inductive equalities, relative completeness,
    and $`\omega`$-completeness
  type: article-journal
  url: "https://www.sciencedirect.com/science/article/pii/089054019090033E"
  volume: 84
- annote: "Keywords: Ground Confluence, Rewriting Induction,
    Non-Orientable Equations, Term Rewriting Systems"
  author:
  - family: Aoto
    given: Takahito
  - family: Toyama
    given: Yoshihito
  collection-title: Leibniz international proceedings in informatics
    (LIPIcs)
  container-title: 1st international conference on formal structures for
    computation and deduction (FSCD 2016)
  doi: 10.4230/LIPIcs.FSCD.2016.33
  editor:
  - family: Kesner
    given: Delia
  - family: Pientka
    given: Brigitte
  id: aoto
  isbn: 978-3-95977-010-1
  issn: 1868-8969
  issued: 2016
  page: "33:1-33:12"
  publisher: Schloss Dagstuhl – Leibniz-Zentrum für Informatik
  publisher-place: Dagstuhl, Germany
  title: <span class="nocase">Ground Confluence Prover based on
    Rewriting Induction</span>
  type: paper-conference
  url: "https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2016.33"
  volume: 52
- author:
  - family: Team
    given: GHC
  id: ghc
  issued: 2024
  note: "Accessed: 2024-10-05"
  publisher: "<https://www.haskell.org/ghc/>"
  title: The glasgow haskell compiler
- author:
  - family: Kop
    given: Cynthia
  id: cynthia
  issued: 2017
  title: Quasi-reductivity of logically constrained term rewriting
    systems
  url: "https://arxiv.org/abs/1702.02397"
- author:
  - family: Thiel
    given: Jean Jacques
  collection-title: POPL ’84
  container-title: Proceedings of the 11th ACM SIGACT-SIGPLAN symposium
    on principles of programming languages
  doi: 10.1145/800017.800518
  id: thiel
  isbn: 0897911253
  issued: 1984
  keyword: Completeness, Data types specifications, Equational theories,
    Substitutions, Term rewriting systems, Unification
  page: 76-82
  publisher: Association for Computing Machinery
  publisher-place: New York, NY, USA
  title: Stop losing sleep over incomplete data type specifications
  type: paper-conference
  url: "https://doi.org/10.1145/800017.800518"
- author:
  - family: Bouhoula
    given: Adel
  - family: Jacquemard
    given: Florent
  container-title: Journal of Applied Logic
  doi: "https://doi.org/10.1016/j.jal.2011.09.001"
  id: bouhoula
  issn: 1570-8683
  issue: 1
  issued: 2012
  keyword: Sufficient completeness, Conditional and constrained term
    rewriting, Narrowing, Tree grammars
  note: Special issue on Automated Specification and Verification of Web
    Systems
  page: 127-143
  title: Sufficient completeness verification for conditional and
    constrained TRS
  type: article-journal
  url: "https://www.sciencedirect.com/science/article/pii/S1570868311000413"
  volume: 10
- author:
  - family: Comon
    given: Hubert
  - family: Dauchet
    given: Max
  - family: Gilleron
    given: Rémi
  - family: Jacquemard
    given: Florent
  - family: Lugiez
    given: Denis
  - family: Löding
    given: Christof
  - family: Tison
    given: Sophie
  - family: Tommasi
    given: Marc
  id: tata
  issued: 2008
  page: 262
  title: <span class="nocase">Tree Automata Techniques and
    Applications</span>
  type: book
  url: "https://inria.hal.science/hal-03367725"
---


---
title: 'Triangle decompositions II: Robust absorption for typed triangles'
author: 'Juan Pablo Traverso Gianini'
date: '20 October 2026'
---

**Paper I of the series:** *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean* [1].

**Paper II of the series:** *Triangle decompositions II: Robust absorption for typed triangles* (this article).

**Preprint 1.0 — 20 October 2026.**

**DOI:** https://doi.org/10.5281/zenodo.23502224.

## Abstract

We study triangle decompositions in which every triangle must use a prescribed multiset of part labels. The necessary divisibility conditions record both the global numbers of edge types and the degree profile at each vertex. We prove a typical-host decomposition theorem under a finite three-step condition on the links and the forbidden-partner condition (3.2), and deduce the nearly complete four-part results used in Paper I. A separate theorem handles semidense two-part graphs with mixed triangles. The proofs combine real corrections respecting local profiles, bounded integer certificates, and a fixed absorber chosen before the remainder. Vertex splitting and corrections of parity, balance, charge and torsion extend the construction beyond three-step links; a fixed cyclic catalogue handles the conserved families. Together with an exact finite classification, these constructions establish the typical-host property for all 765 admissible four-label families up to permutation. We give the construction arguments and their quantitative assembly, and separate the finite certificate data from the universal arguments that use them.

**Keywords:** triangle decomposition; partitioned graphs; absorption; integer lattices; Nash–Williams theorem.

## 1. Introduction

Let the vertices of a graph be assigned labels, and prescribe which multisets of three labels a triangle may have. When can its edges be partitioned into triangles of those types? Even for two labels, the restrictions impose more than the familiar conditions that all degrees be even and the number of edges be divisible by three. They constrain the numbers of edges between parts and the degrees of each vertex into each part. In a host with additional internal structure, there may be further obstructions that these counts do not detect.

The problem occurs in the extremal branches of Delcourt and Postle's proof of the Nash–Williams theorem [2]. Those branches produce partitioned residual graphs and then apply their Theorem 13.16. For the proof of that theorem, they refer to their manuscript *Refined absorption for partitioned hypergraphs and beyond* [3], listed as reference 17 in [2]. We have not found a publicly available version of that manuscript when preparing the source development. We do not identify the results below with its unexamined statement.

Paper I [1] follows Delcourt and Postle's case analysis. The present paper supplies decomposition results for the particular residual hosts needed there, as well as a more general formulation for suitable type families. The mathematical inputs shared by the two papers are as follows.

| Result here | Host or input | Use in Paper I |
|---|---|---|
| Corollary 4.2 | Nearly complete, nearly balanced four-part hosts for F₁–F₃ | The typed extremal branches; F₃ supplies the four-colour corollary |
| Theorem C | Semidense two-part hosts for F₀, away from two balanced templates on at least one side | The branch through Delcourt–Postle 14.6 |
| Lemma SC | A signed certificate, common neighbours and a supply of physical hinges | The terminal absorber in the non-extremal branch |

The protected covering round and its iteration remain in Paper I. Neither that application nor the three results in the table requires a complete classification of type families.

The absorption framework is inherited from refined absorption [4]. Our typical-host formulation uses regular triangle weights and common-neighbourhood extension, in the setting of labelled decomposition problems studied by Keevash [5]. We state these conditions directly for graphs; no theorem about an unspecified labelled complex is used as an implicit hypothesis. The contribution developed here is the construction of the requisite certificates and absorbers for the stated families, together with the deductions that match the residual hosts in Paper I.

We begin with the definitions and a finite link condition. Section 4 gives the nearly complete deduction and the three families used in Paper I. Section 5 isolates the different assumptions needed for F₀. Section 6 contains the signed-certificate absorption argument. Section 7 explains the physical-lattice and weight obstructions. Section 8 gives the physical realization of the conserved core and its application to the seventeen additional families. Section 9 states the full family theorem. Appendix G states the auxiliary inputs and their scope; Appendix H proves their construction and quantitative estimates.


Related decomposition results address several parts of this setting. Barber, Kühn, Lo, Osthus and Taylor [11] treat dense balanced multipartite clique decompositions and their connection with Latin-square completion; Montgomery [12] provides fractional clique decompositions in dense balanced partite graphs. Those results concern rainbow cliques, whereas our type families may repeat a part label and permit several triangle types. Iterative absorption converts approximate decompositions into exact ones in the work of Barber, Kühn, Lo and Osthus [13], and in the hypergraph design framework of Glock, Kühn, Lo and Osthus [14]. Keevash's design theorems [5,15] give the broader regularity, extension and lattice framework. These are antecedents of the method, not consequences of the present paper. Section 2.3 states the precise limits of our comparison with [5].

The packing arguments belong to the nibble tradition of Rödl [16], Frankl–Rödl [17] and Pippenger–Spencer [18]. Haxell–Rödl [19] compare integral and fractional packing sizes in dense graphs; that global comparison does not by itself give the local remainder bound used here. Ehard–Glock–Joos [20] supply a weighted pseudorandom matching theorem under its own degree, codegree and weight hypotheses. We do not invoke it without those hypotheses: Appendices H.7–H.8 give the particular local estimates and parameter choices used in this paper.

### 1.1. Reading the proof

The main text states the decomposition results, proves the nearly complete deductions and the finite absorber lemma, and explains the physical realization and classification. Appendices A–F give the long construction arguments. They share one principle: the reserve and its entire catalogue are fixed before the residue is known. The bounds therefore control the load of all catalogue members, not just the members used by a particular residue.

| Task | Argument | Where it is used |
|---|---|---|
| Correct real weights while retaining local profiles | Appendix A.2–A.3 | Theorem A and the component assembly |
| Convert integer certificates into private absorbers | Appendix A.4–A.6 | Three-step, BAL and conserved families |
| Refine and eliminate global charges | Appendix B | Theorem A |
| Obtain physical certificates and exact weights in the semidense host | Appendix C | Theorem C |
| Split disconnected links and correct component invariants | Appendices D–E | Theorem D |
| Construct one conserved catalogue with bounded total load | Appendix F and Section 8 | The seventeen conserved cases |
| Prove the auxiliary constructions and their constants | Appendix H | B.3–B.4, C.5a, G.2 and G.4 |

The letters attached to appendices are independent of Theorems A–D. In the appendices $F$ denotes the same type family as $\mathcal F$ in the main text. Their equations carry an appendix prefix. The finite family tables are in the frozen sources, located in [8, Sections 7–8]; the theorem for all families is a theorem with explicit finite certificate data, not a classification obtained without such data.

## 2. Types, divisibility and host conditions

All graphs are finite, simple and undirected. Write
$$
V(G)=V_0\sqcup\cdots\sqcup V_{t-1},\qquad n_i=|V_i|,\qquad n=|V(G)|,
$$
and let $p(v)=i$ for $v\in V_i$. A *type* is a multiset of three labels in $\{0,\ldots,t-1\}$. Fix a family $\mathcal F$ of types. A pair $\{i,j\}$, with repetition permitted, is *allowed* if it is contained in a member of $\mathcal F$. An *$\mathcal F$-triangle* is an actual triangle of $G$ whose label multiset belongs to $\mathcal F$. An *$\mathcal F$-decomposition* partitions $E(G)$ into such triangles.

### 2.1. Two levels of integer divisibility

For a type $\tau$, let $b_\tau$ be its vector of edge counts, indexed by unordered pairs of labels. Repeated labels count with their multiplicities. For example, the type $001$ has one edge of type $00$ and two of type $01$.

If $i$ occurs in $\tau$, let $a_{\tau,i}$ be the vector counting the other two labels at a corner labelled $i$. The *global type lattice* and *local profile lattices* are
$$
\mathcal L_E=\langle b_\tau:\tau\in\mathcal F\rangle_{\mathbb Z},
\qquad
\mathcal L_i=\langle a_{\tau,i}:\tau\in\mathcal F,\ i\in\tau\rangle_{\mathbb Z}.
\tag{2.1}
$$
We say that $G$ is *integrally $\mathcal F$-divisible* if its vector of edge counts lies in $\mathcal L_E$ and
$$
\bigl(|N_G(v)\cap V_j|\bigr)_{j=0}^{t-1}\in\mathcal L_{p(v)}
\quad\text{for every }v\in V(G).
\tag{2.2}
$$
We state separately the requirement that all edges have allowed types. Both (2.1) and (2.2) are necessary: sum the contributions of the triangles in a decomposition, globally and at a fixed vertex respectively.

The *physical triangle lattice* retains the individual edges of the host:
$$
\Lambda_{\mathcal F}(G)
=\left\langle\mathbf1_{E(T)}:T\text{ an }\mathcal F\text{-triangle of }G\right\rangle_{\mathbb Z}
\subseteq\mathbb Z^{E(G)}.
\tag{2.3}
$$
A *signed certificate* for an edge vector $x$ is an identity
$$
x=\sum_T c_T\mathbf1_{E(T)},\qquad c_T\in\mathbb Z.
\tag{2.4}
$$
Its cost is $\sum_T|c_T|$. Integral divisibility records type counts and local profiles; (2.4) records a representation using actual triangles. They are different conditions. Section 7 gives an elementary obstruction to confusing them.

### 2.2. Regular weights and extension

For $\omega,c>0$, the host has *$(\omega,c)$-regular triangle weights* if there is a weight $y(T)$ for every $\mathcal F$-triangle such that
$$
\frac{\omega}{n}\le y(T)\le\frac1{\omega n},\qquad
\left|\sum_{T\ni e}y(T)-1\right|\le c
\quad(e\in E(G)).
\tag{2.5}
$$
The lower bound applies to every permitted physical triangle, not merely to the triangles assigned positive weight by a chosen fractional decomposition.

For $h\in\mathbb N$, the host has *$(\omega,h)$-extension* if the following holds. For every $S\subseteq V(G)$ with $|S|\le h$, every $A\subseteq S$ and every label $i$ allowed with all labels in $p(A)$,
$$
\left|\{v\in V_i\setminus S:A\subseteq N_G(v)\}\right|\ge\omega n.
\tag{2.6}
$$
The exclusion of $S$ permits successive choices of distinct auxiliary vertices. Notice that (2.6) requires common neighbours for bounded sets of vertices, not just for pairs.

Say that a family has the *typical-host decomposition property* if
$$
\forall\gamma>0\ \exists h\in\mathbb N,\omega_0>0\ 
\forall\omega\in(0,\omega_0]\ \exists c>0,N\in\mathbb N
\tag{2.7}
$$
such that every integrally $\mathcal F$-divisible host of order $n\ge N$, with only allowed edges, $n_i\ge\gamma n$ for every $i$, regularity (2.5), and extension (2.6), has an $\mathcal F$-decomposition. This names a precise property; asserting the property for a family still requires a proof.

### 2.3. Relation with the labelled design theorem

Property (2.7) is modelled on the regularity–extension–lattice formulation of Keevash [5, Theorem 3.1]. That theorem requires a finite adapted labelled complex, an elementary molecule system, membership in its actual decomposition lattice, regular weights and extendability with the specified type restrictions. It also imposes its own size and parameter inequalities. The following correspondence distinguishes the proposed encoding from hypotheses proved in this paper.

| Item in (2.7) | Correspondence and verification needed |
|---|---|
| Permitted triangle types | Use a finite labelled molecule for each type, retaining repeated labels as distinct slots. One must specify the relabelling action, adapted complex and elementary edge-coordinate system. |
| Weights (2.5) | Distribute each triangle weight among its labelled representations and check the normalization and all type-coordinate loads in [5, Definition 2.37]. The finite multiplicities affect the constants. |
| Extension (2.6) | Successive common-neighbour choices give embeddings for compatible bounded patterns. To invoke [5, Definitions 2.9–2.10], one must identify every required restricted pattern and translate its rank and supply parameters. |
| Divisibility (2.1)–(2.2) | These are aggregate type and vertex-profile conditions. Identifying them with membership in the actual physical decomposition lattice is a separate assertion. |

The last distinction matters even before parameters are chosen. The available complete-host lattice identification applies to a complete allowed blowup with at least five vertices in every class. A typical host in (2.7) need not be complete. Thus that identification alone does not justify substituting (2.1)–(2.2) for the lattice hypothesis in [5]. The family-specific constructions below supply physical certificates and absorbers; they are not replaced by this bibliographic comparison.

We therefore use (2.7) as a graph-level property proved here for the stated families. We do not claim that its full hypotheses have been shown equivalent to those of [5, Theorem 3.1], or that the present existence statement is stronger than that general theorem. The additional three-step and forbidden-partner assumptions delimit our constructive route. The contributions to be compared are the explicit family constructions, their quantitative assembly and the interfaces required in Paper I.

## 3. A finite condition on the type family

Fix four labels. For a root label $r$, its link has the labels as vertices and has an edge $ab$ when $\{r,a,b\}\in\mathcal F$. Loops are retained: repeated labels are legitimate types. A link vertex is active if it is incident with some link edge.

The family has *three-step links* if, for every $r$ and every two active link vertices $a,b$, there are labels $v,w$ such that
$$
\{r,a,v\},\quad\{r,v,w\},\quad\{r,w,b\}\in\mathcal F.
\tag{3.1}
$$
The endpoints may coincide, and this is a walk condition, not a requirement of a simple path. We also require that each label have a forbidden partner:
$$
\forall i\ \exists j\quad\{i,j\}\text{ is not allowed}.
\tag{3.2}
$$
This restricts the scope of the following theorem; it is not asserted to be necessary for every decomposition. In the proof it supplies a degree gap: the forbidden class for a vertex contains no neighbours of that vertex. Section B.6 uses this gap in the initial near-load packing.

### Theorem A (typical hosts with three-step links)

Let $\mathcal F$ be a family of three-element multisets on four labels satisfying (3.1) and (3.2). Then $\mathcal F$ has the typical-host decomposition property (2.7).

The theorem is stronger than a statement about nearly complete hosts: (2.5) and (2.6) do not require every allowed pair to be present. Conversely, these hypotheses cannot be omitted merely because many small switching gadgets exist.

### 3.1. How the construction is organized

The proof has an algebraic part and a physical part. The algebraic part must preserve both the edge-type totals and the local profiles. Solving only the global equations would leave a demand that need not be a boundary at individual vertices. The physical part realizes the resulting identities by permitted triangles and chooses auxiliary vertices with bounded load.

The real correction is applied to the load defect of the current weighted triangle family. Divisibility of the host and the profiles of that weighted family put this defect in the required compatible span. A bounded inverse on the complete allowed host supplies a correction there. Its transfer to the actual host uses extension, with all already reserved vertices and edges accounted for. Integer certificates and the family absorber then handle the divisible remainder. The family absorber must be fixed before that remainder is selected. In particular, separate certificates of bounded cost are insufficient: their auxiliary vertices could accumulate excessive load. The construction chooses one physical catalogue and reserve for all permitted remainders and controls incidence at every vertex. Section 8 proves this realization step for the conserved core.

The dependency order is therefore
$$
\text{family construction}\ \longrightarrow
\text{protected reserve and absorber}\ \longrightarrow
\text{packing and remainder}\ \longrightarrow
\text{absorption}.
\tag{3.3}
$$
The arrow from packing to remainder does not authorize a new choice of absorber. That order of quantifiers is part of the construction.

**Proof of Theorem A: structure and parameters.** Appendix A first constructs a real inverse on the complete allowed host. The correction is made in three stages: global type totals, local profiles, and the remaining zero-profile edge vector. Its transfer to the actual host uses bounded common-neighbourhood sets. Integer certificates are obtained separately; a real inverse alone would not establish integer divisibility or binary decomposability.

Appendix B uses the three-step walk identity to identify each local lattice with the even-sum lattice on its active labels. The global quotient group is retained, including torsion. An ordinary even refiner is routed through the host, and a fixed finite ledger removes its remaining global charges. The resulting catalogue has bounded pieces and bounded total incidence over **all** its members. Appendix A then embeds a private absorber for every catalogue member while controlling accumulated degree. This gives a single absorber for every divisible subgraph of the reserved edge set.

Finally, Appendix B.6 chooses the correction tolerance and the sparse reserve scale before the host. It fixes the reserve and absorber, recomputes regular weights after deleting their decomposable edges, and applies the packing and cover-down lemmas to leave a divisible residue inside the reserve. The already fixed absorber closes the decomposition. The explicit inequalities in Appendices A.6 and B.5–B.6 ensure that each construction fits the supply left by the preceding one. These auxiliary packing, cover-down, ordinary-refiner and finite matching results are used in their stated roles; the conclusion of Theorem A is not assumed by them.

## 4. Nearly complete hosts

For a vertex $v$, its *missing allowed degree* is the number of vertices $u\ne v$ for which $\{p(u),p(v)\}$ is allowed but $uv\notin E(G)$. A nearly complete host will have missing allowed degree at most an integer $d\le\delta n$ at every vertex.

For labels $a,b$ and a type $\tau$, put
$$
q_\tau(a,b)=\frac1n
\sum_{\substack{c:\{a,b,c\}=\tau}}
\bigl(n_c-\operatorname{mult}_c\{a,b\}\bigr).
\tag{4.1}
$$
Here the sum is over labels, not over ordered embeddings. It is the normalized count of possible third vertices in the complete allowed host, with the endpoints excluded.

### Theorem B (the nearly complete deduction)

Fix a family $\mathcal F$ on $t$ labels with the typical-host decomposition property. For every $\gamma,\omega_1>0$ there are $\varepsilon,\delta>0$ and $N\in\mathbb N$ such that the following holds. Let $G$ have order $n\ge N$, only allowed edges, $n_i\ge\gamma n$ for every $i$, and missing allowed degree at most $d\le\delta n$. Suppose that $G$ is integrally $\mathcal F$-divisible and there are type weights $w_\tau$ satisfying
$$
\omega_1\le w_\tau\le\omega_1^{-1}\quad(\tau\in\mathcal F),\qquad
\left|\sum_{\tau\in\mathcal F}w_\tau q_\tau(a,b)-1\right|\le\varepsilon
\quad\text{for every allowed }\{a,b\}.
\tag{4.2}
$$
Then $G$ has an $\mathcal F$-decomposition.

*Proof.* Apply (2.7) with $\gamma$, obtaining $h$ and $\omega_0$. Choose
$$
\omega=\min\{\omega_1,\omega_0,\gamma/2\},\qquad
\varepsilon=\frac{c}{4(1+|\mathcal F|/\omega_1)},\qquad
\delta=\min\left\{\frac\varepsilon4,\frac\gamma{4(h+1)}\right\},
\tag{4.3}
$$
where $c>0$ and $N_0$ are the regularity tolerance and threshold supplied for this $\omega$. Take
$$
N\ge\max\left\{N_0,1,
\left\lceil\frac{4(t+h+1)}{\min\{\varepsilon,\gamma\}}\right\rceil\right\}.
\tag{4.4}
$$

To check extension, fix $S,A,i$ as in (2.6). At most $|S|$ vertices of $V_i$ are excluded by $S$, and each member of $A$ excludes at most $d$ further vertices. The number of choices is consequently at least
$$
n_i-|S|-|A|d\ge\gamma n-h-hd\ge\gamma n/2\ge\omega n.
\tag{4.5}
$$
The middle inequality follows from (4.3)–(4.4).

For an edge $uv$ and a type $\tau$, let $t_\tau(u,v)$ count the actual third vertices of that type. The missing allowed edges at $u$ and $v$, together with the endpoint exclusions, give the bound
$$
|t_\tau(u,v)-nq_\tau(p(u),p(v))|\le2d+2t\le\varepsilon n.
\tag{4.6}
$$
The harmless $2t$ term retains the uniform counting bound used in the construction. Assign each physical triangle of type $\tau$ the weight $w_\tau/n$. The bounds on $w_\tau$ imply the weight bounds in (2.5), since $\omega\le\omega_1$. Equations (4.2) and (4.6) imply
$$
\left|\sum_{T\ni uv}\frac{w_{p(T)}}n-1\right|
\le\varepsilon\left(1+\sum_{\tau\in\mathcal F}w_\tau\right)
\le\varepsilon(1+|\mathcal F|/\omega_1)=c/4\le c.
\tag{4.7}
$$
Thus the same host satisfies regularity, extension, integral divisibility and the class-size conditions. Apply (2.7).

### 4.1. Balanced type weights

A positive weight $w_\tau$ on each type is *balanced* if, for every allowed pair,
$$
\sum_{\substack{c:\{a,b,c\}\in\mathcal F}}w_{\{a,b,c\}}=t.
\tag{4.8}
$$
This is a finite condition on the family. It is not an automatic consequence of integral divisibility of a host.

### Corollary 4.1

Suppose $t\ge1$, $\mathcal F$ has the typical-host decomposition property, and (4.8) has a positive solution. There are $\eta,\delta>0$ and $N$ such that every integrally $\mathcal F$-divisible graph of order $n\ge N$, with only allowed edges,
$$
(1/t-\eta)n\le n_i\le(1/t+\eta)n,
\tag{4.9}
$$
and missing allowed degree at most $d\le\delta n$, has an $\mathcal F$-decomposition.

*Proof.* Because the family is finite and the weights are positive, choose $\omega_1>0$ with $\omega_1\le w_\tau\le\omega_1^{-1}$ for every type. Apply Theorem B with $\gamma=1/(2t)$ and this $\omega_1$. If $\varepsilon,N_1,\delta$ are its constants, take
$$
\eta=\min\{\varepsilon/(2t),1/(2t)\},\qquad
N\ge\max\{N_1,\lceil8t/\varepsilon\rceil\}.
\tag{4.10}
$$
Then all parts have size at least $n/(2t)$. Reindexing the sum in (4.2) by completing labels and using (4.8) gives
$$
\left|\sum_\tau w_\tau q_\tau(a,b)-1\right|
\le\sum_{c:\{a,b,c\}\in\mathcal F}
w_{\{a,b,c\}}(\eta+2/n)
=t\eta+2t/n\le\varepsilon.
\tag{4.11}
$$
Theorem B applies.

### 4.2. The families used in Paper I

With labels $0,1,2,3$, let
$$
\begin{aligned}
\mathcal F_1&=\{002,003,112,113,022,122,033,133\},\\
\mathcal F_2&=\{002,003,112,113,023,123\},\\
\mathcal F_3&=\{012,013,023,123\}.
\end{aligned}
\tag{4.12}
$$
Each allowed pair has exactly two completing labels. Therefore $w_\tau=2$ satisfies (4.8). The active part of each root link is either a triangle or a three-vertex path with a loop at each endpoint. The first shape occurs for every root of F₃ and for roots zero and one of F₂; all remaining links have the second shape. Both shapes admit a three-step walk between every two vertices, including coincident endpoints: on the path, endpoint loops supply the odd step, and on the triangle one can use a closed triangle or backtrack along an edge. Thus (3.1) holds. In F₁ and F₂, zero and one are forbidden partners of each other; for F₁, two and three are forbidden partners, while for F₂, pairs $22$ and $33$ are forbidden. In F₃ every repeated pair is forbidden. This verifies (3.2) without any condition on the host.

### Corollary 4.2 (the balanced four-part input)

For each $\mathcal F\in\{\mathcal F_1,\mathcal F_2,\mathcal F_3\}$ there are $\eta,\delta>0$ and $N$ such that every graph on $n\ge N$ vertices with only allowed edges, missing allowed degree at most $d\le\delta n$, part sizes in $[(1/4-\eta)n,(1/4+\eta)n]$, and integral $\mathcal F$-divisibility has an $\mathcal F$-decomposition.

*Proof.* Theorem A gives the typical-host property. The weight $2$ and Corollary 4.1 give the conclusion.

For $\mathcal F_1$ and $\mathcal F_2$, Paper I also uses the idealized form: each part has size at least $(1-\varepsilon)n/4$ and each vertex has at least $|V_j|-\varepsilon n$ neighbours in every allowed part $V_j$. For sufficiently small $\varepsilon>0$ this is covered by Corollary 4.2. Indeed, summing the other three lower class-size bounds gives the upper bound $(1/4+3\varepsilon/4)n$, and summing the missing degrees into the four parts gives at most $4\varepsilon n$ missing allowed neighbours. Choose $\varepsilon$ so that $\varepsilon\le\eta$ and $4\varepsilon\le\delta$. Only allowed edge types may occur, and integer compatibility remains a hypothesis in this idealized form.

The F₃ application is the four-colour reduction. It requires the global and local lattice checks for the residual graph; a proper colouring alone is not a divisibility condition. Paper I carries out those checks and joins the resulting decomposition to its cleanup packing.

## 5. A separate semidense theorem

Let $\mathcal F_0=\{001,011\}$. An $\mathcal F_0$-triangle has two vertices in one part and one in the other. In this case integral divisibility is equivalent to
$$
d_G(v)\text{ even for every }v,\qquad e_{01}=2(e_{00}+e_{11}).
\tag{5.1}
$$
The edge-type generators are $(1,2,0)$ and $(0,2,1)$, in the order $00,01,11$. At a vertex in part zero, the local generators are $(1,1)$ and $(0,2)$; their lattice is the set of pairs with even sum. The corresponding statement holds in part one. This proves the equivalence.

For a set $D$, consider every split $D=X\sqcup(D\setminus X)$ with $|X|=\lfloor|D|/2\rfloor$. Its two *balanced templates* are the complete bipartite graph across that split and the disjoint union of the two cliques. Say that $G[D]$ is $\alpha$-close to a balanced template if at most $\alpha|D|^2$ unordered edge edits produce one of these graphs.

### Theorem C (the semidense two-part input)

For every $\alpha>0$ there are $\varepsilon_0>0$ and $N$ such that the following holds. Let $G$ be integrally $\mathcal F_0$-divisible, of order $n\ge N$, with a partition $V_0\sqcup V_1$ satisfying
$$
|V_i|\ge(1-\varepsilon_0)n/2\quad(i=0,1),
\tag{5.2}
$$
and, for every $v\in V_i$,
$$
(1/4-\varepsilon_0)n\le |N_G(v)\cap V_i|\le(1/4+\varepsilon_0)n,
\qquad |N_G(v)\cap V_{1-i}|\ge(1/2-\varepsilon_0)n.
\tag{5.3}
$$
If at least one of $G[V_0]$ and $G[V_1]$ is not $\alpha$-close to either balanced template, then $G$ has an $\mathcal F_0$-decomposition.

The internal degree in (5.3) is about half the size of its part. This is not the nearly complete allowed-host setting of Theorem B. The absence of the two templates on one side is a substantive hypothesis. It supplies the geometry needed for the F₀ construction; it must not be replaced by aggregate divisibility alone.

Counting ordered pairs instead of unordered edits doubles the distance. Thus the condition above corresponds to an ordered disagreement bound $2\alpha|D|^2$, with the same $\alpha$. Keeping this factor explicit avoids changing the exceptional region when the theorem is applied.

**Proof of Theorem C: the separate geometric argument.** Appendix C starts from the exclusion of the two balanced templates in the good part. A short-walk stability argument supplies many walks of lengths three and four there. Those walks provide signed certificates on physical mixed triangles and explicit hinges; their counts retain the four fixed roots. Thus the integer terminal construction is available with constants depending only on the nonextremality parameter.

The fractional input is built independently. On the complete crossing graph, an internal incidence inverse corrects the two internal edge loads and the crossing loads together. Removing the missing crossing pairs changes this operator by a controlled amount; a convergent correction gives exact bounded nonnegative weights on the actual graph. The deletion estimate in Appendix C.6 shows that this construction can be repeated after reserving the absorber. A second weight construction, followed by cover-down, leaves the divisible residue for that absorber. All scales and the order threshold are specified in Appendix C.6. This argument uses neither Theorem A nor the unavailable manuscript [3].

## 6. From signed certificates to finite absorbers

This section concerns ordinary triangles. Its construction does not require non-extremality or a fractional decomposition.

For distinct $u,v,a,b$, a *hinge* between triangles $uva$ and $uvb$ is an edge set $H\subseteq E(G)$, disjoint from both triangles, such that
$$
H\cup\{ua,va\}\quad\text{and}\quad H\cup\{ub,vb\}
\tag{6.1}
$$
have triangle decompositions. Its order is the number of vertices incident with its edges. All four roots belong to this support: covering a wedge edge without the excluded base $uv$ requires hinge edges at its ends. Once the roots are fixed, an order-$i$ hinge has $i-4$ free vertices.

We require that every pair of triangles sharing one edge have, for some integer $i$ with $6\le i\le C_0$, at least $\beta n^{i-4}$ distinct order-$i$ hinges, counted as physical edge sets. Call this a *$(\beta,C_0)$-hinge supply*.

### Lemma SC (signed certificates give absorbers)

Let $G$ have order $n$, let $\alpha,\beta>0$, and let $C_0,K,z$ be nonnegative integers. Suppose every two distinct vertices have at least $\alpha n$ common neighbours and $G$ has a $(\beta,C_0)$-hinge supply. Let $P\subseteq E(G)$ have a certificate by actual triangles
$$
\mathbf1_P=\sum_j c_j\mathbf1_{E(T_j)},\qquad c_j\in\mathbb Z,
\qquad \sum_j|c_j|\le K.
\tag{6.2}
$$
Suppose $V(P)\subseteq Z$ and $|Z|\le z$. Set
$$
m=\binom{C_0+1}{2},\qquad B=z+3K+4KC_0+1.
$$
If
$$
B<\alpha n,\qquad 2^mB<\beta n,
\tag{6.3}
$$
there is an edge set $A\subseteq E(G)$ such that $A$ and $A\cup P$ have triangle decompositions,
$$
A\cap E(G[Z])=\varnothing,\qquad |A|\le4K(m+2).
\tag{6.4}
$$
In particular, $A$ is edge-disjoint from $P$.

*Proof.* Fix four hinge roots and a forbidden set $U$ of non-root vertices. For each $w\in U$, at most $n^{i-5}$ choices of additional vertices and $2^m$ edge sets give an order-$i$ hinge through $w$. Thus at most $2^m|U|n^{i-5}$ hinges meet $U$. The second inequality in (6.3) will leave a hinge whenever $|U|\le B$.

Expand each coefficient in (6.2) into $|c_j|$ signed occurrences of its triangle. There are at most $K$ occurrences and three edge slots per occurrence. Include every vertex of these triangles in the initial used set, even if its contribution later cancels.

For an occurrence $abc$, choose a fresh common neighbour $x$ of $a,b$, then a hinge $H$ between $abc$ and $abx$ with fresh non-root support. In a decomposition of $H\cup\{ac,bc\}$, let $acy$ and $bcz$ cover $ac$ and $bc$. The excluded triangle edges force $y,z$ outside $\{a,b,c,x\}$. Also $y\ne z$, since otherwise the two triangles share $cy$. Put
$$
W_{ab}=\{ax,bx\},\quad W_{ac}=\{ay,cy\},\quad W_{bc}=\{bz,cz\},
\qquad Y=H\setminus\{ay,cy,bz,cz\}.
\tag{6.5}
$$
Removing $acy$ and $bcz$ proves that $Y$ is decomposable. The other decomposition of the hinge proves that
$$
Y\,\dot\cup\,W_{ab}\,\dot\cup\,W_{ac}\,\dot\cup\,W_{bc}
=H\cup\{ax,bx\}
\tag{6.6}
$$
is decomposable. Each wedge closes its slot edge to a triangle. No edge of this occurrence gadget joins two of its certificate roots.

For each physical edge $e$, identity (6.2) says that the number of positive slots on $e$ equals the number of negative slots plus $\mathbf1_P(e)$. Match the negative slots bijectively to positive slots on the same edge, leaving exactly one positive slot for each edge of $P$.

For every matched pair on $uv$, let its apices be $a_-,a_+$. Choose a fresh hinge $J$ between $uva_-$ and $uva_+$. Its two decompositions use respectively the negative and positive wedge. These choices are edge-disjoint from the preceding construction. The base and the four wedge edges are excluded from $J$. The only remaining pair among its roots joins $a_-$ to $a_+$; no occurrence gadget contains this pair, since these apices come from different occurrences. No earlier slot hinge contains it either, since a slot is matched only once and each occurrence has three distinct apices. All other intersections are prevented by freshness.

Let $A$ be the union of all occurrence closures $Y$, all wedges and all slot hinges. Its two decompositions are described by the following table.

| Decomposition of $A$ | Decomposition of $A\cup P$ |
|---|---|
| Positive occurrences use (6.6); negative occurrences use $Y$. | Negative occurrences use (6.6); positive occurrences use $Y$. |
| Slot hinges use their negative wedges. | Slot hinges use their matched positive wedges. |
| Every positive wedge has already been used with its occurrence. | Each unmatched positive wedge closes its edge of $P$. |

Every wedge is used exactly once in each column. This proves both decomposition claims.

There are at most $3K$ certificate roots, $K$ occurrence hinges and $3K$ slot hinges. Each hinge has at most $C_0$ support vertices, including its roots. Including $Z$, the used set therefore has size at most $z+3K+4KC_0$. The additional one in $B$ pays for the current choice. The first inequality in (6.3) permits every fresh common neighbour, and the hinge count at the start of the proof permits every fresh hinge.

An occurrence contributes at most $m+2$ edges, and each slot hinge at most $m$. Hence
$$
|A|\le K(m+2)+3Km\le4K(m+2).
$$
Finally every added edge has an endpoint outside $Z$. In an occurrence gadget this follows from freshness and the exclusion of the certificate-root edges. In a slot hinge the only possible pair of roots entirely in $Z$ is its excluded base. This proves (6.4).

The same slot-matching construction has a typed version: all occurrence gadgets and hinge decompositions must use permitted triangle types. This is the version used in the separate semidense construction of Theorem C. For an internal demand edge of $F_0$, choose its auxiliary common neighbour in the opposite part. For a crossing demand edge use a completing label permitted by $F_0$. The hinge replacements are the mixed configurations listed in C.4. The private placement in C.5a and C.6 applies these typed choices, rather than the ordinary-triangle Lemma SC without modification.

For the eight-vertex hinges used in Paper I, the bounds are
$$
B=z+35K+1,\qquad 2^{36}B<\beta n,\qquad |A|\le152K,
\tag{6.7}
$$
along with $B<\alpha n$. Paper I supplies the signed certificate and the common-neighbour and hinge estimates. Lemma SC performs the conversion. It constructs an absorber for a specified $P$; a universal absorber for a collection of possible residues requires a further simultaneous construction. That extra quantifier is not part of this lemma.

## 7. Scope and obstructions

### 7.1. Aggregate divisibility need not give a physical certificate

For $r\ge3$, set
$$
a_\pm=2r^2\pm2r+1,\qquad b=2r^2+3,
\qquad G_r=(K_{a_+}\sqcup K_{a_-})\vee(K_b\sqcup K_b).
\tag{7.1}
$$
Label the two cliques on the left zero and the two on the right one. Consider $\mathcal F_0=\{001,011\}$. This graph is integrally $\mathcal F_0$-divisible but has no $\mathcal F_0$-decomposition.

Indeed, all four clique sizes are odd, so all degrees in the join are even. Write $u=2r^2$. The internal and crossing edge counts are
$$
e_{00}=u^2+3u,\qquad e_{11}=u^2+5u+6,
\qquad e_{01}=(2u+2)(2u+6)=2(e_{00}+e_{11}).
\tag{7.2}
$$
Thus (5.1) holds. Let $W$ be the set of crossing edges between the clique of size $a_+$ and one fixed clique of size $b$. Every permitted triangle meets $W$ in zero or two edges, since its internal edge lies inside one of the four cliques. But $|W|=a_+b$ is odd. The parity functional
$$
x\longmapsto\sum_{e\in W}x_e\pmod2
\tag{7.3}
$$
therefore vanishes on every physical triangle generator and not on $\mathbf1_{E(G_r)}$. The edge indicator is outside the physical lattice (2.3), and a decomposition is impossible.

This proves the precise distinction needed here. We do not use this calculation alone to claim that the example satisfies every fractional or hinge hypothesis of another theorem. Those stronger claims require their own verifications.

### 7.2. Hinge counts and fixed roots

The normalization in Section 6 follows from the number of free vertices. For fixed triangles sharing an edge, every order-$i$ physical hinge contains their four roots. There are at most a constant depending on $i$, times $n^{i-4}$, such edge sets. In particular, a lower bound of order $n^{i-2}$ for fixed $i$ cannot hold for all sufficiently large $n$ when such a root pair exists.

A discrepancy in normalization and a counterexample to a corrected statement are different matters. Neither determines the content of the manuscript listed as [17] in [2]. Our applications use the explicit normalization and hypotheses stated here. Paper I, Appendix A.2, uses eight-vertex hinges with supply proportional to $n^4$, exactly the case $i=8$ in Section 6.

### 7.3. Families beyond three-step links

Three-step links are a sufficient condition for the construction of Theorem A. Failure of that condition does not prove that a host has no decomposition. For example, in the single rainbow family $\{012\}$, a root link is bipartite, and there is no odd closed walk at an active link vertex. A different terminal construction is needed to handle that family by this method.

The wider development uses splitting of label classes (the PAR route) and balanced corrections retaining charge and torsion information (the BAL route). These are construction theorems, not a definition that assumes decomposability. The constructions cover 748 representatives, and the conserved-core construction supplies the remaining seventeen. The exhaustive census and the transport to arbitrary admissible families are now proved in Lean. Section 9 states the resulting theorem with intrinsic hypotheses and explains what the finite verification establishes. The census is not needed by Corollary 4.2 or Theorem C.

Appendix D proves the vertex-splitting reduction. Appendix E develops the component constructions: local parity and balance, the additional global charge when present, and the torsion correction in the appropriate order. Appendix F constructs the fixed abstract catalogue used by Section 8. The finite component certificates remain part of the data of the classification; their locations and the checked coverage are recorded in [8].

### 7.4. Positive type weights are a separate hypothesis

Consider $\mathcal F=\{001,012\}$ on four labels with equal class proportions. Equation (4.8) for the allowed pair $00$ forces $w_{001}=4$, and the equation for $02$ forces $w_{012}=4$. The equation for $01$ would then require $w_{001}+w_{012}=4$, a contradiction. Thus even the finite balancing equations need not have a solution. This example explains the weight hypothesis in Theorem B and Corollary 4.1; it is not a counterexample to Theorem D, since label three is unused.

## 8. Physical realization of the conserved core

Appendix F constructs the abstract catalogue used below. Its absolute constant is $C=C_m$ from (F.10); the bounds (F.12)–(F.16) provide the input and whole-catalogue load estimates needed in the physical embedding.

### A fixed physical reserve

For a directed edge set $D$, write $d_D(v)=d_D^+(v)+d_D^-(v)$.
An edge set is balanced if its in-degree and out-degree agree at every vertex.
If $\mathcal P$ is a finite collection of directed edge sets, its catalogue load is

$$\ell_{\mathcal P}(v)=\sum_{P\in\mathcal P}d_P(v).$$

This counts all pieces in the catalogue, not just those chosen for one residue.

Let $C$ be the absolute constant in the abstract catalogue construction and set

$$q=4096(C+1)\cdot21.$$

**Physical realization lemma.** Let $G$ be a graph on $n$ vertices with a
partition $V_0,V_1,V_2$. Suppose each part has at least $\omega n$ vertices,
and every set of at most two vertices whose labels differ from $i$ has at
least $\omega n$ common neighbours in $V_i$. Let $X$ be a directed edge set
supported in $G$, oriented cyclically from $V_i$ to $V_{i+1}$, with indices
taken modulo three. Suppose

$$0<t\le1,\qquad 1\le t^2n,\qquad32qt\le\omega,$$

$$|X|\le t^2n^2,\qquad d_X(v)\le2t^2n\quad(v\in V(G)).$$

There exist a cyclically oriented reserve $R$ supported in $G$ and a finite
catalogue $\mathcal P$, chosen before any balanced $L\subseteq X$, such that

$$R\cap X=\varnothing,\qquad d_R(v)\le3qtn,$$

$$P\subseteq R\cup X,\quad |P|\le80,\quad P\text{ balanced}
\qquad(P\in\mathcal P),$$

$$|\mathcal P|\le(49C+16)|X|,\qquad
\ell_{\mathcal P}(v)\le3qtn.$$

For every balanced $L\subseteq X$, some subcollection of $\mathcal P$ is an
edge-disjoint partition of $R\cup L$.

The bound is on total directed degree, not on the larger of the in-degree
and out-degree separately. Since $X$ is cyclically oriented, its total degree
is also the degree of its underlying undirected graph.

*Proof.* Apply the abstract catalogue construction to $X$. It supplies a set
of ports, prescribed maps from the original ports to their physical roots,
an auxiliary reserve $R_0$, and a catalogue $\mathcal P_0$. Write $I_0$ for
the lifted original input. The construction has the following properties.
Every piece is contained in $R_0\cup I_0$ and has at most twenty arcs;
$R_0$ and $I_0$ are disjoint; and, for each balanced $L\subseteq X$, a
subcollection partitions $R_0$ together with the lifted copy of $L$.
Its pieces are either balanced or unused channels whose two end ports have
the same prescribed physical root. In particular, those channels need not
be balanced on the port set.

For a catalogue arc $e$, let $w(e)$ be the number of pieces containing it.
For a port $a$, put

$$s(a)=\sum_{e\ni a}w(e).$$

The abstract construction gives $|\mathcal P_0|\le(49C+16)|X|$ and
$\sum_e w(e)\le(980C+48)|X|$. At an old port its catalogue load is at most
$1257$; at a new vertex it is at most $7C\sqrt{|X|}$. The total load already
pinned to a physical vertex $v$ is at most $1257d_X(v)$. Consequently, with

$$T=W=qtn,\qquad M=qt^2n^2,$$

we have $s(a)\le W$, $\sum_a s(a)\le M$, and pinned load at most $T$ at
every physical vertex. These estimates follow from the choice of $q$,
$\sqrt{|X|}\le tn$, $t\le1$, and $1\le t^2n$.

Choose the images of the remaining ports, one at a time, in their prescribed
parts. Keep the images of pinned ports fixed. For a free port choose a vertex
with current load below $T$. At most $M/T$ vertices can have load at least
$T$; since $M<\omega nT$, a candidate exists in the required part. Assigning
the port adds at most $W$. The resulting map $f$ therefore has load at most
$T+W$ at every physical vertex. It need not be injective.

Keep the catalogue arcs belonging to $I_0$ as their original physical arcs.
For each remaining arc $e=ab$, choose a path

$$f(a),x_e,y_e,z_e,f(b)$$

of length four. If $a$ has label $i$, its successive labels are
$i,i+1,i+2,i,i+1$. Require the paths to avoid all underlying edges of $X$
and all paths chosen earlier. Charge each path with its actual multiplicity
$w(e)$ in the fixed catalogue. The endpoint charges are assigned before the
interior vertices are selected.

The weighted path-selection lemma applies with forbidden degree
$d=2t^2n$, because

$$\frac{4M}{T}+4+2(d+T+2W)<\omega n.$$

Indeed the left-hand side is at most $(12+6q)tn<32qtn\le\omega n$.
The same lemma bounds the combined load of retained input arcs and all
weighted paths by $T+2W=3qtn$. This is why the weights must count occurrences
in the whole catalogue: bounding only the union of the paths would not
control the catalogue load.

Replace each non-retained catalogue arc by its path, using this one choice
of $f$ and paths for all residues. For an oriented arc $ab$, the signed
vertex boundary of its replacement is $e_{f(b)}-e_{f(a)}$. Thus a balanced
abstract piece remains balanced after replacement, even when $f$ identifies
ports. An unused channel also becomes balanced: its two end ports have the
same physical root. Every resulting piece has at most $4\cdot20=80$ arcs.
All arcs have the required cyclic orientation.

Let $A$ be the union of the abstract catalogue arcs and let $I=A\cap I_0$.
The partition for the empty residue shows $R_0\subseteq A$. Since every
piece is supported in the disjoint union $R_0\cup I_0$, it follows that
$A\setminus I=R_0$. Define $R$ to be the union of the paths replacing $R_0$,
and let $\mathcal P$ consist of the replaced pieces. Then $R$ is supported
in $G$ and avoids $X$.

Replacement blocks for distinct abstract arcs are edge-disjoint. This follows
from path selection, avoidance of $X$, and the fact that distinct retained
input arcs have distinct physical images. Hence replacement carries every
abstract partition to an edge-disjoint physical partition. Prescribed roots
identify the lifted copy of each balanced $L$ with exactly $L$, so its union
is $R\cup L$. No new choice depends on $L$.

Finally, the weighted path estimate bounds $\ell_{\mathcal P}(v)$ by $3qtn$;
identifying equal pieces cannot increase that sum. Replacement does not
increase the number of pieces. Applying the partition assertion to the empty
residue bounds $d_R(v)$ by the same catalogue load. This proves all claims. $\square$

### Returning to the seventeen families

Each of the seventeen conserved families has an explicit vertex-splitting
whose components consist of one conserved core and the separately certified
non-core components. On the core, the split triangle types are precisely
the triples with three distinct colours. The common-neighbour supply needed
for this assertion is taken from the core component family itself. It is
not inferred by enlarging that family.

The physical realization lemma, followed by the bounded-piece terminal
absorber construction, gives a universal three-colour absorber certificate
with an absolute exponent $L_C$ in the scale conditions below. Passing to the induced physical core and
pulling its absorber back gives the core component certificate. For the
finitely many non-core components, take a common scale $2^{-L_N}$ for their
existing certificates. Increasing a scale exponent only strengthens the
sparsity assumption. We may therefore use

$$L=\max\{L_C,L_N\}$$

for every occupied component. The vertex-splitting transfer gives a universal
family certificate at exponent $L+11$. This choice precedes the host graph.
The typical-host decomposition theorem then applies to each of the seventeen
families without an unproved Latin-producer hypothesis.

This proves the missing existence assertions for those representatives. The
separate finite census in Section 9 establishes exhaustiveness; this does not
follow from the physical construction alone.

**Scale convention and the loss of eleven.** A certificate with exponent $L$ supplies the universal absorber whenever the guarded-supply hypotheses hold and
$$
0<\omega\le1,\quad 0<\delta,\quad 2^{63}\delta\le\omega,\qquad
2^{24}\rho\le\left(\frac{\omega^2\delta}{2^L}\right)^2,
\quad 1\le\rho n.
$$
Thus $L$ enters the upper bound on reserve density; it does not mean that $\delta=2^{-L}$. The certificate uses guarded supply of order $2^{21}$ with parameter $\omega n$ and an allowed host. Its conclusion is a universal absorber of maximum degree at most $2\delta n$ for an input reserve of maximum degree at most $2\rho n$.

Here is the rescaling needed when labels are split. Let $1\le t'\le8$, $n\le n'\le t'n$, and $x=n/n'$. Use
$$
\omega'=\omega x,\qquad \delta'=\delta x/t',\qquad \rho'=\rho x.
$$
The degree and order conditions persist. Write $P=(\omega^2\delta/2^L)^2$. The original certificate condition at exponent $L+11$ gives $2^{24}\rho'\le Px/2^{22}$, whereas the target condition at exponent $L$ has right side $Px^6/(t')^2$. It is sufficient that
$$
(t')^2\le2^{22}x^5.
$$
Indeed, $x\ge1/8$ and $(t')^2\le64$, so the right side is at least $2^{22}/8^5=128$. Also $\rho'n'=\rho n$ and $\delta'n'=\delta n/t'$. The latter allocates each component its share of the degree budget before projection. This proves the stated exponent loss; the companion identifies the rescaling lemma and its use in the conserved-family assembly.

## 9. All admissible four-label families

Call a family on four labels *admissible* if every member is a three-element multiset, every label occurs in some member, and every label has a forbidden partner as in (3.2). This is a condition on the types alone; it neither assumes a decomposition nor refers to a list of successful constructions.

### Theorem D (four-label families; computer-assisted finite classification)

Every admissible four-label family has the typical-host decomposition property (2.7). There are exactly 765 such families up to permutation of the four labels.

The classification part uses explicit finite certificate tables checked in Lean; the universal host constructions are the separate arguments described below.

The first assertion retains all the host hypotheses in (2.7), including regular triangle weights, extension, and both integer lattice conditions. It does not assert that every nearly balanced host has positive type weights. Theorem B applies to each of these families when its additional weight hypothesis holds.

*Finite reduction and transport.* List the twenty nondecreasing triples on four labels. Sending a family to the subset of indices of its triples gives an invertible encoding. A permutation of the four labels acts on this encoding through the corresponding permutation of triples. Encoding followed by decoding, and relabelling followed by its inverse, are identities.

For an admissible family, choose a forbidden partner for each label. The exclusion of the corresponding pairs places its encoding in one of twenty-six finite boxes of permitted types. Each box has at most twelve types. The finite coverage check considers every subset of each box that uses all four labels. For each such subset it provides one of the twenty-four actual label permutations taking it to a recorded representative. The certificate therefore supplies a permutation, not merely equality of numerical invariants.

The recorded list contains 765 distinct masks. Each is checked to be admissible and minimal in its permutation orbit. If two listed masks represent the same orbit, minimality gives both inequalities between their masks, hence equality. Coverage and this uniqueness give the claimed orbit count. The finite assertions, encoding identities and their assembly are proved in Lean; the Python search that generated candidate certificates is not a premise of the result.

For each representative, the construction library supplies the typical-host property. This includes the seventeen conserved cases of Section 8. To pass from a representative to the original family, relabel the parts of the same host by the inverse permutation. Allowed pairs, triangle types, edge-type vectors and corner profiles are carried bijectively to their relabelled counterparts. In particular the two integer lattices are carried to the corresponding lattices, regular weights remain weights on the same physical triangles, and the extension sets are unchanged apart from their labels. Apply the representative's theorem and undo the relabelling. This proves the property for the original family; no catalogue-membership premise remains.

The construction part is supplied by Appendices A–F. The PAR route covers 271 representatives; the BAL route covers 357, comprising 301 balance-only, 52 charged and four torsion cases. Together with the 120 earlier cases and the seventeen conserved cases, these are the 765 representatives of the finite certificate. The counts alone are not a coverage proof: the explicit component data and permutation certificates are essential. The universal constructions explain how those data imply decomposition; the finite verification establishes that every representative has the required data.

## Formalization and reproducibility

The development has been checked in Lean 4 with Mathlib [6,7]. The aligned campaign compiled the full 1,510-module closure of three explicit Paper II targets and recorded fifteen final axiom queries using only propositional extensionality, classical choice and quotient soundness. Its scope includes the seventeen conserved-family existence certificates, the census and transport to every admissible four-label family. It uses the same four-colour bridge as Paper I. The selected archive corrects author headers after compilation while preserving every proof-body byte; its reversible source map binds the historical receipts to the corrected files. The companion [8], preprint 1.0, records the archive hashes, declaration map, finite certificate locations, campaign evidence and reproduction limits. This editorial integration runs no Lean build and does not claim independent reproduction. The companion distinguishes final entry queries from module-level axiom evidence, including the nearly complete corollary.

## Acknowledgments

The author is deeply grateful to his wife María Paz and his children Lucas, Juan Cristóbal, Francisca, Raimundo and Benjamín for their love, patience and support. The author thanks Delcourt and Postle for the mathematical work that motivated this development, and the Lean and Mathlib communities for the infrastructure used in the formalization.

## Use of artificial intelligence and computational tools

Claude, by Anthropic, and ChatGPT/Codex, by OpenAI, were used to explore and check arguments and to prepare the manuscript. Aristotle, by Harmonic, contributed to exploring approaches, searching for counterexamples, developing proofs, and formalizing and reviewing them in Lean. Its role was not limited to translating finished proofs.

Certo [9] and Jacobian [10] were used to explore finite instances, check identities and assess candidate constructions. Finite checks were not treated as proofs of universal statements. The census search generated finite certificates. Lean then verified coverage of the admissible universe, uniqueness up to actual permutations, and the connection to the construction theorems; these are stronger assertions than compiling a list of examples.

The author remains responsible for the arguments, citations, code and presentation. No AI system is listed as an author.

## References

[1] J. P. Traverso Gianini, *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean*, preprint 1.0 (2026). https://doi.org/10.5281/zenodo.23428173. [Document](https://github.com/jtraverso/nash-williams-triangle-decompositions/blob/main/preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.0_en.md).

[2] M. Delcourt and L. Postle, *A Proof of Nash-Williams' Conjecture*, arXiv:2606.11178v1 (2026). https://arxiv.org/abs/2606.11178v1.

[3] M. Delcourt and L. Postle, *Refined absorption for partitioned hypergraphs and beyond*, manuscript, 2026. Bibliographic description as listed in [2, reference 17]; no public version located in the preparation of this series.

[4] M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*, arXiv:2402.17855 (2024). https://arxiv.org/abs/2402.17855.

[5] P. Keevash, *The existence of designs II*, arXiv:1802.05900 (2018). https://arxiv.org/abs/1802.05900.

[6] L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 28 (2021), 625–635. https://doi.org/10.1007/978-3-030-79876-5_37.

[7] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381. https://doi.org/10.1145/3372885.3373824.

[8] J. P. Traverso Gianini, *Formalization and reproducibility companion to Triangle decompositions II*, preprint 1.0 (2026), accompanying source freeze `PAPER_II_LEAN_20261020_ALIGNED_v4`. The companion identifies the immutable source archive and its SHA-256 hash. [Document](https://github.com/jtraverso/nash-williams-triangle-decompositions/blob/main/preprints/PAPER_II/05_formalization/FORMALIZATION_COMPANION_preprint_v1.0_en.md).

[9] J. P. Traverso Gianini, *Certo*, software repository. https://github.com/jtraverso/certo-math.

[10] *Jacobian*, software repository. https://github.com/morluto/jacobian.


[11] B. Barber, D. Kühn, A. Lo, D. Osthus and A. Taylor, *Clique decompositions of multipartite graphs and completion of Latin squares*, Journal of Combinatorial Theory, Series A 151 (2017), 146–201. https://doi.org/10.1016/j.jcta.2017.04.005.

[12] R. Montgomery, *Fractional clique decompositions of dense partite graphs*, Combinatorics, Probability and Computing 26 (2017), 911–943. https://doi.org/10.1017/S0963548317000165. https://arxiv.org/abs/1603.01039.

[13] B. Barber, D. Kühn, A. Lo and D. Osthus, *Edge-decompositions of graphs with high minimum degree*, Advances in Mathematics 288 (2016), 337–385. https://doi.org/10.1016/j.aim.2015.09.032.

[14] S. Glock, D. Kühn, A. Lo and D. Osthus, *The existence of designs via iterative absorption: hypergraph F-designs for arbitrary F*, arXiv:1611.06827v3 (2020). https://arxiv.org/abs/1611.06827v3.

[15] P. Keevash, *The existence of designs*, arXiv:1401.3665v4 (2024; first version 2014). https://arxiv.org/abs/1401.3665v4.

[16] V. Rödl, *On a packing and covering problem*, European Journal of Combinatorics 6 (1985), 69–78. https://doi.org/10.1016/S0195-6698(85)80023-8.

[17] P. Frankl and V. Rödl, *Near perfect coverings in graphs and hypergraphs*, European Journal of Combinatorics 6 (1985), 317–326. https://doi.org/10.1016/S0195-6698(85)80045-7.

[18] N. Pippenger and J. Spencer, *Asymptotic behavior of the chromatic index for hypergraphs*, Journal of Combinatorial Theory, Series A 51 (1989), 24–42. https://doi.org/10.1016/0097-3165(89)90074-5.

[19] P. E. Haxell and V. Rödl, *Integer and fractional packings in dense graphs*, Combinatorica 21 (2001), 13–38. https://doi.org/10.1007/s004930170003.

[20] S. Ehard, S. Glock and F. Joos, *Pseudorandom hypergraph matchings*, Combinatorics, Probability and Computing 29 (2020), 868–885. https://doi.org/10.1017/S0963548320000280.

[21] S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press (2013), Chapter 2. https://doi.org/10.1093/acprof:oso/9780199535255.001.0001.

\clearpage

## Appendix A. Algebra, integer certificates and finite absorbers

In these appendices, “integer-compatible” and “integrally $F$-divisible” mean the same local and global lattice conditions of Section 2.

### A.1. Conventions and compatibility

Let $F$ be a family of multisets of size three on a finite label set $I$.
Vertices are partitioned into classes $V_i$, and $n_i=|V_i|$,
$n=\sum_i n_i$. A pair of labels is allowed if it occurs in a member of
$F$, with multiplicity when the two labels coincide. The complete allowed
graph contains precisely the non-loop edges with allowed label pairs.
An allowed triangle is an unordered set of three distinct vertices whose
multiset of labels lies in $F$. Its edge vector is denoted by $[abc]$.
For a triangle chain $z$, write $\partial z$ for its edge vector and
$\|z\|_1$ for the sum of the absolute values of its coefficients.

An edge vector $r$ is symmetric and has zero diagonal. Its local profile and
its **ordered** global counts are
$$
d_r(v)_j=\sum_{w\in V_j}r_{vw},\qquad
T_{ij}(r)=\sum_{v\in V_i}d_r(v)_j.
$$
Thus an internal edge contributes twice to $T_{ii}$. Off the diagonal,
$T_{ij}=T_{ji}$, and each of these two coordinates counts an edge once.
All global columns below use this convention. In particular,
$\sum_{v\in V_i}d_r(v)=T_{i\bullet}(r)$.

Let $g_\tau$ be the global count vector of a triangle of type $\tau$.
For $i\in\tau$, let
$$
b_{\tau,i}(j)=\operatorname{mult}_\tau(j)-\mathbf1_{j=i}
$$
be its profile at a corner of label $i$. We call $r$ real-compatible if
$T(r)$ lies in the real span of the $g_\tau$, and every $d_r(v)$ lies
in the real span of the $b_{\tau,p(v)}$. Integer compatibility means the
same assertions for the integer spans. These are two separate requirements.

For an edge vector, $\|r\|_1$ counts unordered edges. Consequently
$$
\sum_v\|d_r(v)\|_1\le 2\|r\|_1,
\qquad \|\partial z\|_1\le3\|z\|_1.
\tag{A.1.1}
$$

### A.2. A real inverse with the local profiles included

**Proposition A.2.1.** Suppose $|I|=4$, $0<\gamma\le1$, and
$n_i\ge\gamma n\ge8$ for every label. There is a constant $C_F>0$,
depending only on $F$, such that every real-compatible vector $r$
supported on the complete allowed graph, with $\|r\|_\infty\le\epsilon$,
has a triangle preimage $z$ satisfying
$$
\partial z=r,\qquad
\|z\|_\infty\le \frac{C_F\epsilon}{\gamma^6n}.
\tag{A.2.1}
$$

**Proof.** A linear map between finite-dimensional real spaces has a linear
right inverse on its image: choose a basis of the image, choose one preimage
of each basis vector, and extend linearly. Its operator norm is finite.
Apply this observation to the matrix with columns $g_\tau$, and to each
matrix with columns $b_{\tau,i}$. Choose positive constants $K_1,K_2$
bounding the resulting coordinate norms. We use the *same* local right
inverse at every vertex of a given class. This choice will preserve sums.

#### Global correction

Since every global coordinate of $r$ has absolute value at most
$\epsilon n^2$, choose coefficients $c_\tau$ such that
$$
\sum_{\tau\in F}c_\tau g_\tau=T(r),\qquad
|c_\tau|\le K_1\epsilon n^2.
$$
Put $m=\gamma n$. The number $N_\tau$ of physical triangles of a
specified type is at least $m^3/64$. Indeed, choose an ordered triple of
vertices with its prescribed labels, excluding previous vertices at each
choice, and divide by at most six. For $m\ge8$,
$m(m-1)(m-2)/6\ge m^3/64$.

Give each triangle of type $\tau$ weight $c_\tau/N_\tau$, obtaining
$z_1$. Then $T(\partial z_1)=T(r)$ and
$$
\|z_1\|_\infty\le\frac{64K_1\epsilon}{\gamma^3n}.
$$
An edge is in at most $n$ triangles. Therefore $r_1=r-\partial z_1$
has zero global counts and
$$
\|r_1\|_\infty\le E_1,
\qquad E_1=\frac{(1+64K_1)\epsilon}{\gamma^3}.
\tag{A.2.2}
$$
Subtracting a triangle chain preserves real compatibility.

#### Profile correction

Apply the chosen local right inverse to each $d_{r_1}(v)$. Its coefficients
$c_{v,\tau}$, defined for types containing $i=p(v)$, satisfy
$$
\sum_{\tau\ni i}c_{v,\tau}b_{\tau,i}=d_{r_1}(v),\qquad
|c_{v,\tau}|\le K_2nE_1,
\qquad \sum_{v\in V_i}c_{v,\tau}=0.
\tag{A.2.3}
$$
The last equality follows by linearity from $T(r_1)=0$; independent
choices of preimages would not justify it.

We record the exact multiplier for the next construction. Fix $\tau$ and
numbers $\phi_\tau(v)$ with sum zero on each class, equal to zero on
classes absent from $\tau$. Give a triangle $abc$ of type $\tau$
weight $\phi_\tau(a)+\phi_\tau(b)+\phi_\tau(c)$. At a vertex $v$ of
label $i\in\tau$, its profile is
$\kappa_{\tau,i}\phi_\tau(v)b_{\tau,i}$. The multipliers are as follows;
write $\tau=\{i,x,y\}$.

| Labels | $\kappa_{\tau,i}$ |
|---|---:|
| $i,x,y$ distinct | $n_xn_y$ |
| $i=x\ne y$ | $(n_i-2)n_y$ |
| $i=y\ne x$ | $n_x(n_i-2)$ |
| $x=y\ne i$ | $n_x(n_x-1)/2$ |
| $i=x=y$ | $(n_i-2)(n_i-3)/2$ |

Here is a direct verification, including the repeated-label cases. At a root
of label $i$, the degree towards label $l$ is obtained by summing over
ordered choices of the other corner of label $l$ and the completing corner
of label $z$. Replacing each complete class sum of $\phi$ by zero leaves
the coefficient
$$
(n_l-2\mathbf1_{i=l})
(n_z-\mathbf1_{i=z}-\mathbf1_{l=z})
-\mathbf1_{i=z}(n_l-\mathbf1_{i=l})
+\mathbf1_{l=z}\mathbf1_{i=l}.
\tag{A.2.4}
$$
Only completions with $\{i,l,z\}=\tau$ occur. Substitution in (A.2.4)
gives the table, with division by two when the profile column itself has
entry two. This also explains why treating the three labels as distinct
would give the wrong correction.

Every multiplier in the table is at least $m^2/8$. Set
$\phi_\tau(v)=c_{v,\tau}/\kappa_{\tau,p(v)}$. The denominators are
constant within a class, so these functions still have class sums zero.
Let $z_2$ be the resulting chain. Equation (A.2.3) and the multiplier identity
give $d_{\partial z_2}(v)=d_{r_1}(v)$ for all $v$. Moreover,
$$
\|z_2\|_\infty\le\frac{24K_2E_1}{\gamma^2n},\qquad
\|r_2\|_\infty\le E_2:=\frac{(1+24K_2)E_1}{\gamma^2},
\tag{A.2.5}
$$
where $r_2=r_1-\partial z_2$ has every local profile zero.

#### Edge correction

For an allowed label pair $ij$, let $q_{ij}$ be the number of types
containing that pair. For such a type $\tau$, let $k$ be its uniquely
determined remaining label and put
$$
e_{\tau,ij}=n_k-2\mathbf1_{i=k}-2\mathbf1_{j=k}\ge m-4\ge m/2.
$$
Define a symmetric edge function
$$
h_\tau(u,v)=\frac{r_2(u,v)}{q_{ij}e_{\tau,ij}}
\quad (u\in V_i,v\in V_j),
$$
and set it to zero on pairs absent from $\tau$ and on the diagonal.
Each of its class row sums is zero, since its denominator is constant on
each label block. Give a triangle of type $\tau$ weight
$h_\tau(a,b)+h_\tau(a,c)+h_\tau(b,c)$.

For a fixed edge $uv$, summing over its third vertex initially counts
$h_\tau(u,v)$ exactly $n_k-\mathbf1_{i=k}-\mathbf1_{j=k}$ times.
The two remaining sums are zero class sums with forbidden endpoints removed;
they subtract another $\mathbf1_{i=k}+\mathbf1_{j=k}$ copies. Thus this
type contributes $e_{\tau,ij}h_\tau(u,v)=r_2(u,v)/q_{ij}$. Summing over
the $q_{ij}$ types proves $\partial z_3=r_2$, with
$$
\|z_3\|_\infty\le\frac{6E_2}{\gamma n}.
$$
Finally $z=z_1+z_2+z_3$ proves (A.2.1), for the explicit choice
$$
C_F=64K_1+24K_2(1+64K_1)
+6(1+24K_2)(1+64K_1).
\tag{A.2.6}
$$
The replacement of smaller powers of $\gamma^{-1}$ by $\gamma^{-6}$
uses $\gamma\le1$. $\square$

**Corollary A.2.2 (compatibility of the actual defect).** If $H$ is
integer-compatible and $\varphi$ is any real weighting of its allowed
triangles, then $r=\mathbf1_{E(H)}-\partial\varphi$ is real-compatible.
If $B\subseteq G$ has an allowed triangle decomposition and $G$ is
integer-compatible, the same conclusion holds for $H=G-B$.

**Proof.** Globally, subtract the sum of $\varphi(T)g_{\tau(T)}$ from
the integer-compatible count vector of $H$. Locally, at $v$, subtract
$\sum_{T\ni v}\varphi(T)b_{\tau(T),p(v)}$ from its integer-compatible
profile. Both differences belong to the required real spans. Deleting a
decomposable graph subtracts integer sums of the same columns, so it preserves
integer compatibility. $\square$

### A.3. Moving the real inverse into the host graph

**Proposition A.3.1 (signed transfer).** Suppose that the host graph supplies at
least $s>0$ choices in any prescribed compatible class adjacent to any
set of at most four prescribed vertices. Let $z$ be a real chain on the
complete allowed graph such that $r=\partial z$ is supported on host
edges. Suppose
$$
\|r\|_\infty\le\epsilon,\qquad
\sum_T|z(T)|\le S,\qquad
\max_v\sum_{T\ni v}|z(T)|\le U.
$$
Then there is a chain $w$ on actual host triangles with $\partial w=r$
and, for each host triangle $Q$,
$$
|w(Q)|\le\frac{9\epsilon}{s}+
\frac{81U}{s^2}+\frac{108S}{s^3}.
\tag{A.3.1}
$$

**Proof.** We average two explicit substitutions. Random choices below are
only a way to define real coefficients by finite averages; no asymptotic
probability theorem is used.

For each virtual triangle $abc$, choose $A$ of the label of $a$
adjacent to $b,c$; then $B$ of the label of $b$ adjacent to
$a,c,A$; finally $C$ of the label of $c$ adjacent to $a,b,A,B$.
Choose uniformly from the available vertices at each step. There are at least
$s$ choices. The edge-vector identity
$$
[abc]=[abC]+[aBc]+[Abc]-[aBC]-[AbC]-[ABc]+[ABC]
\tag{A.3.2}
$$
holds by cancelling edges. The last four triangles are host triangles.
The first three consist of an old edge and a physical two-edge wedge.
No global distinctness of $a,b,c,A,B,C$ is needed: every displayed
triangle has three distinct vertices, as forced by the adjacency conditions.

Fix an old edge $ab$. The wedge occurrences over this edge have signed
masses $u_j$, total mass $\sum_j u_j=r_{ab}$, and total absolute mass
$m_{ab}=\sum_{T\supset ab}|z(T)|$. Each apex law has point probabilities
at most $1/s$, also for choices made later in the preceding experiment.
Pair positive and negative masses, splitting masses if necessary. The
unpaired mass has size $|r_{ab}|$ and one sign. For a paired positive
apex $c$ and negative apex $d$, choose independently from their two
apex laws, then choose $A$ of the label of $a$ adjacent to $b,c,d$
and $B$ of the label of $b$ adjacent to $a,c,d,A$. The identity
$$
[abc]-[abd]=
[aBc]+[Abc]+[ABd]-[aBd]-[Abd]-[ABc]
\tag{A.3.3}
$$
replaces the pair by six host triangles. In particular, it does not require
$ab$ to be a host edge. The unmatched occurrences already are host
triangles: their mass vanishes when $ab\notin E(G)$, because $r$ is
supported on $G$. Equations (A.3.2) and (A.3.3) prove the boundary assertion.

For completeness we bound the coefficients of this average. Fix a host
triangle $Q$, and put
$O_Q=\sum_T|z(T)|\,|T\cap Q|\le3U$.
An adaptive sequence of $k$ choices, each with conditional point
probabilities at most $1/s$, has probability at most $(3/s)^k$ of
putting all its choices in $Q$. Consequently the four host faces in
(A.3.2) contribute in absolute value at most
$$
S(3/s)^3+O_Q(3/s)^2.
$$
For a paired wedge over $ab$, the six faces in (A.3.3) contribute at most
$$
2\bigl((\mathbf1_{a\in Q}+\mathbf1_{b\in Q})(3/s)^2+(3/s)^3\bigr)
$$
times its paired mass. Twice the paired mass is at most $m_{ab}$.
Furthermore,
$$
\sum_{ab}m_{ab}=3\sum_T|z(T)|\le3S,\qquad
\sum_{ab}m_{ab}(\mathbf1_{a\in Q}+\mathbf1_{b\in Q})=2O_Q.
$$
The unmatched wedges can contribute only over the three edges of $Q$;
their contribution is at most $3\epsilon(3/s)$. The total is therefore
$$
3\epsilon(3/s)+3O_Q(3/s)^2+4S(3/s)^3,
$$
which is (A.3.1). $\square$

**Corollary A.3.2 (a quantitative repair).** In Proposition A.2.1 take
$\gamma=\omega$, where $0<\omega\le1$, and assume the host supplies
$s=\omega n/2$ choices as in Proposition A.3.1. Then a compatible defect
of norm at most $\epsilon$ has a host-supported correction bounded by
$$
\|w\|_\infty\le
\frac{(18+1188C_F)\epsilon}{\omega^9n}.
\tag{A.3.4}
$$
Indeed, (A.2.1) gives $S\le C_F\epsilon n^2/\omega^6$ and
$U\le C_F\epsilon n/\omega^6$. Substitution in (A.3.1), followed by
$\omega\le1$, gives (A.3.4). Thus weights initially in
$[\omega^2/n,27/(\omega n)]$ remain positive and are at most
$54/(\omega n)$ after correction whenever
$$
(18+1188C_F)\epsilon\le\omega^{11}/2.
\tag{A.3.5}
$$
Their edge loads are then exactly one.

Deletion estimates used with this corollary are explicit. If a decomposable
graph $B$ of maximum degree at most $\kappa n$ is removed, the supply
for four prescribed neighbours loses at most $4\kappa n$ choices.
Restricting the old triangle weights loses at most $2\kappa n$ triangles
at each retained edge. Under the upper weight bound just stated, an original
load error $\epsilon$ becomes at most
$\epsilon+54\kappa/\omega$. Corollary A.2.2 supplies both compatibility
conditions for this new defect. In particular, the algebraic inverse is not
being applied on the basis of global counts alone.

### A.4. Integer certificates for bounded pieces

**Proposition A.4.1.** Fix $F$ and an integer $K\ge0$. There is an integer
$C=C(F,K)\ge0$ with the following property. In a complete allowed graph
with five designated distinct representatives in every class, every
integer-compatible edge set $P$, with $|P|\le K$, has an integer
triangle certificate of cost at most $C$, using only the vertices of
$P$ and the representatives.

**Proof.** For a fixed integer matrix, there are only finitely many vectors
of its integer image in a bounded coordinate box. Choose an integer preimage
of each and take the maximum of their costs. This argument does not assert
that arbitrary integer vectors in the real span have integer preimages.

Apply it first to the global columns, in the box $[-2K,2K]$, and call the
resulting bound $C_1$. Realize the selected combination of types on the
representatives. Its chain $z_0$ has cost at most $C_1$; the residual
$u=\mathbf1_P-\partial z_0$ has zero global counts, remains
integer-compatible, and satisfies
$$
\|u\|_1\le L:=K+3C_1.
$$
Choose in each class a distinguished representative $o_i$. Apply the
finite-box argument to every local profile matrix in the box
$[-2L,2L]$, and let $C_2$ bound all selected preimage costs.

For $v\in V_i\setminus\{o_i\}$, represent $d_u(v)$ by its local
columns. A column corresponding to $\tau=\{i,j,k\}$ is transferred
from $o_i$ to $v$ by
$$
[vab]-[o_iab],
\tag{A.4.1}
$$
where $a,b$ are representatives of labels $j,k$, distinct from each
other and from $v,o_i$. Five representatives suffice even when labels
coincide. At $a,b$ the class profiles cancel because $v,o_i$ have
the same label. The global counts also cancel.

Use zero correction if the desired profile is zero. Otherwise its integer
$\ell^1$ norm is at least one. The correction at $v$ therefore costs
at most $2C_2\|d_u(v)\|_1$. By (A.1.1), their total cost is at most
$C_g=4C_2L$. After subtraction, the profiles at all non-distinguished
vertices are zero. The profile at $o_i$ is zero too, because the sum of
the profiles in $V_i$ was the zero global row. The residual $u'$ has
all profiles zero and
$$
\|u'\|_1\le L+3C_g.
\tag{A.4.2}
$$

We now give the kernel calculation that includes internal clique blocks.
For an edge $xy$, of labels $i,j$, introduce the formal vector
$$
q(xy)=[xy]-[x o_j]-[o_i y]+[o_i o_j].
\tag{A.4.3}
$$
Formal loops are allowed in this calculation only. Summing (A.4.3) with
coefficients $u'_{xy}$ gives $u'$: the terms involving a distinguished
vertex vanish by the zero profiles, and the final terms vanish by the zero
global counts. In a diagonal block this last assertion uses half the ordered
diagonal count, which is also zero.

For $i\ne j$, (A.4.3) is a quadrilateral, or zero if an endpoint is
distinguished. It has a triangle certificate of cost at most four, obtained
by choosing a completing apex and coning its four edges with alternating
signs. A fifth representative of the completing label ensures that the apex
avoids the four corners, even if that label equals $i$ or $j$.

For an internal block, fix representatives $p_i,r_i$ distinct from
$o_i$ and each other. Subtract $q(p_ir_i)$ from $q(xy)$ whenever
$x,y\ne o_i$. This does not change the total sum: the sum of the
coefficients on internal edges not incident with $o_i$ is the total
internal sum minus the zero row at $o_i$, hence zero. The formal loop
$[o_io_i]$ now cancels in every such difference.

Write
$C(a,b,c,d)=[ab]-[bc]+[cd]-[da]$. When $x,y$ avoid $p_i,r_i$,
$$
q(xy)-q(p_ir_i)
=C(x,y,o_i,p_i)+C(x,p_i,r_i,o_i).
\tag{A.4.4}
$$
All four corners of each quadrilateral are distinct. If one endpoint equals
$p_i$, the expression is $C(p_i,y,o_i,r_i)$; if it equals $r_i$,
exchange $p_i,r_i$. Reverse the edge to cover coincidences at the other
endpoint. If its endpoints are precisely $p_i,r_i$, the expression is
zero. This exhausts the cases. Coning these at most two quadrilaterals gives
cost at most eight per original edge coefficient. No formal loop is ever
used as an actual edge.

We have proved that $u'$ has a certificate of cost at most
$8\|u'\|_1$. Adding the two previous corrections proves the proposition
with
$$
C=8(L+3C_g)+C_1+C_g,
\qquad L=K+3C_1,\quad C_g=4C_2L.
\tag{A.4.5}
$$
All choices involved only the original vertices and the five representatives
per class. $\square$

### A.5. From a signed certificate to a physical absorber

**Proposition A.5.1.** Let $P$ have an integer certificate with $k$ signed
triangle occurrences on a labelled vertex set $W$. There is an abstract
labelled graph $A$, with no edge between two vertices of $W$, such that
both $A$ and $A\cup P$ have allowed triangle decompositions. It has
at most $9k$ new vertices and $30k$ edges. The new vertices admit an
ordering in which each has at most four neighbours among $W$ and the
earlier new vertices.

**Proof.** Expand every integer coefficient into unit occurrences, retaining
its sign. For an occurrence $uvw$, introduce private clones
$u',v',w'$ of the same respective labels. Take the nine-edge graph formed
by the clone triangle and the six edges joining an old vertex to clones of
the other two corners. It has a decomposition
$$
(u v'w'),\quad(v u'w'),\quad(w u'v').
\tag{A.5.1}
$$
Alternatively, set aside its clone triangle. The remaining edges are three
two-edge wedges, one over each side of the original triangle. The wedge over
$uv$ has apex $w'$.

For each old edge $uv$, match its negative side occurrences injectively
to its positive side occurrences. The certificate equation says that exactly
one positive side is left unmatched if $uv\in P$, and none otherwise.
For a matched pair, let $c,d$ be the negative and positive wedge apices.
Introduce two private vertices $a,b$, of the labels of $u,v$, and the
seven-edge graph
$$
H=\{ub,av,ab,ac,bc,ad,bd\}.
$$
Then $H$ together with the wedge of apex $c$ is decomposed by
$(ubc),(avc),(abd)$, and with the wedge of apex $d$ by
$(ubd),(avd),(abc)$. All these triangles are allowed: each has the
type of one of the two original occurrences.

Let $A$ be the union of the nine-edge occurrence graphs and these
seven-edge hinges. To decompose $A$, use (A.5.1) for positive occurrences,
the clone triangle for negative occurrences, and each hinge with its
negative wedge. To decompose $A\cup P$, use (A.5.1) for negative
occurrences, the clone triangle for positive occurrences, and each hinge
with its matched positive wedge. Each unmatched positive wedge is completed
by its corresponding edge of $P$. These lists partition the edges:
clones and hinge vertices are private, and side matching is injective.

If there are $k_-$ negative occurrences, there are $3k_-$ hinges.
Thus $|E(A)|=9k+21k_-\le30k$ and the number of new vertices is
$3k+6k_-\le9k$. Order all occurrence clones first, then the first vertex
of each hinge, then its second. An occurrence clone has at most two old and
two earlier clone neighbours. The first hinge vertex has neighbours
$v,c,d$; the second has $u,c,d,a$. This proves the ordering claim.
$\square$

**Corollary A.5.2 (terminal absorption in the host).** Let $C=C(F,K)$ be as
in Proposition A.4.1. Suppose a host on $t$ labels supplies at least $a$
compatible choices for every set of at most four neighbours. Let $D$ be
a forbidden edge ledger of maximum degree at most $d$, and $Z$ a set
of forbidden auxiliary vertices. If
$$
|Z|+2K+5t+9C+4d<a,
\tag{A.5.2}
$$
then every integer-compatible $P\subseteq G$, $|P|\le K$, has an
absorber $A\subseteq G$ with at most $30C$ edges, disjoint from
$D\cup P$, using no vertex of $Z$ outside $V(P)$.

**Proof.** Choose five fresh representatives in each class outside
$Z\cup V(P)$. This is possible by (A.5.2), using the supply with no
neighbour constraints. Apply Proposition A.4.1 in the virtual complete allowed
graph on these representatives and $V(P)$, whose size is at most
$2K+5t$, and then Proposition A.5.1. Embed its new vertices in the ordering
provided there. At each step the required host adjacencies leave at least
$a$ candidates. Excluding $Z$, the fixed vertices, previous new
vertices, and forbidden-ledger neighbours of the at most four earlier
neighbours removes fewer than $a$ candidates by (A.5.2). The embedding is
therefore injective and avoids the ledger. There are no edges of the gadget
between fixed vertices, so it also avoids $P$. The two abstract
decompositions become physical decompositions in the host. $\square$

### A.6. Absorbing a fixed catalogue without concentrating auxiliary load

The following assembly statement separates the construction of a catalogue
from its use. It is not an existence assertion for the Latin catalogue.

**Proposition A.6.1.** Let $X,R\subseteq G$ be edge-disjoint, and let
$(B_j)_{j=1}^M$ be a fixed catalogue of integer-compatible subgraphs of
$X\cup R$, each with at most $K$ edges. Suppose that for every
admissible $L\subseteq X$, including $L=\varnothing$, a subcollection
of the catalogue partitions $R\cup L$ into edge-disjoint pieces. Assume
$$
\Delta(X\cup R)\le D_0,\qquad
\sum_j d_{B_j}(v)\le\Lambda\quad\hbox{for every }v.
\tag{A.6.1}
$$
Put $C=C(F,K)$ and $c=30C$. Suppose the four-neighbour supply is at least $a$,
and choose $T>0,D$ such that
$$
\begin{split}
4(|X\cup R|+Mc)&\le Ta,\\
\max\{D_0,T+c\}+c\Lambda&\le D,\\
2K+5t+9C+4D&<a/2.
\end{split}
\tag{A.6.2}
$$
Then there is a fixed graph $A\subseteq G-X$ with $\Delta(A)\le D$
such that $A\cup L$ has an allowed triangle decomposition for every
admissible $L$.

**Proof.** Construct private absorbers $A_j$ successively. Before step
$j$, the ledger is $X\cup R\cup\bigcup_{i<j}A_i$; mark vertices of
ledger degree greater than $T$ as heavy. The total number of ledger edges
is at most $|X\cup R|+Mc$, so (A.6.2) implies that at most $a/2$
vertices are heavy. Apply Corollary A.5.2 to $B_j$, taking the ledger as
forbidden edges and the heavy vertices as forbidden auxiliaries.

Here is the degree induction needed to justify each application, without
assuming the conclusion. A step adds at most $c$ at any vertex. If a
vertex is used as an auxiliary, its degree immediately before that step was
at most $T$. After its last auxiliary use, it can receive contributions
only at steps where it is a root of $B_j$. Each such step contributes
at most $c$, and the number of these steps is at most
$\sum_j d_{B_j}(v)\le\Lambda$. A vertex never used as an auxiliary
starts with degree at most $D_0$. Therefore every prefix ledger has
maximum degree at most $\max\{D_0,T+c\}+c\Lambda\le D$.
Together with the last inequality of (A.6.2), this validates (A.5.2) at the next
step and completes the induction.

Set $A=R\cup\bigcup_j A_j$. For an admissible $L$, choose indices
$J$ whose pieces partition $R\cup L$. Decompose $A_j\cup B_j$
for $j\in J$, and $A_j$ for $j\notin J$. These decompositions are
edge-disjoint and cover exactly $A\cup L$, because all the private
absorbers avoid $X\cup R$ and each other. The degree bound follows from
the ledger bound. The case $L=\varnothing$ also decomposes $A$.
Every choice made in constructing $A$ precedes the selection of $L$.
$\square$

\bigskip

## Appendix B. Three-step links and quantitative assembly

### B.1. The claim and the order of construction

Write $F$ for a fixed family of triples of a finite label set, and call
$ij$ active if $ijk\in F$ for some $k$. A host is labelled by $p$.
An $s$-vertex guarded supply of size $a$ means that every set of at most
$s$ vertices whose labels are active with $i$ has at least $a$ common
neighbours of label $i$. We use the local and global integer divisibility
conditions of this article, including the multiplicities of repeated labels.

We prove the following intermediate assertion. If $F$ has three-step links,
there is an integer $S=S(F)\ge4$ such that, for every $0<\omega\le1$ and
$\delta>0$, there are $\rho>0,N$ with this property: in every allowed
host of order $n\ge N$ with guarded supply $(S,\omega n)$, every
$X\subseteq E(G)$ with $\Delta(X)\le2\rho n$ has a fixed set
$A\subseteq E(G)\setminus X$ satisfying

$$
\Delta(A)\le2\delta n,\qquad
A\text{ and }A\cup L\text{ have }F\text{-decompositions}
\tag{B.1.1}
$$

for every integrally divisible $L\subseteq X$. The choices are made in the
order $F,S;\omega,\delta,\rho,N;G;X;A;L$. In particular, neither the
library nor its physical realization is chosen after $L$.

Combined with Appendix A's real inverse and the packing/cover-down lemmas, (B.1.1)
proves Theorem A of Paper II. The hypothesis that each label has a forbidden
partner remains part of that theorem's family interface; it is not used to
replace any of the local lattice conditions below.

### B.2. What a three-step link actually supplies

Fix a root label $r$. Let $L_r$ be its link, with loops allowed. Its
integer incidence columns are $e_a+e_b$ for $rab\in F$; a loop gives
$2e_a$. Along a walk $a,v,w,b$ of length three,

$$
(e_a+e_v)-(e_v+e_w)+(e_w+e_b)=e_a+e_b.
\tag{B.2.1}
$$

Thus three-step links put every active pair column in the local lattice.
Conversely, every link column has even coordinate sum. Fix an active label
$a$. If a supported integer vector $d$ has sum $2z$, then

$$
d=\sum_jd_j(e_j+e_a)-z(2e_a).
\tag{B.2.2}
$$

Equations (B.2.1)–(B.2.2) prove that local divisibility is precisely even total
degree on the active support. This does **not** remove the global lattice
condition. Let $\mathcal Q_F$ be the group of integer type-edge vectors
modulo the subgroup generated by triangle columns. A loopless active graph
is integrally divisible exactly when its degrees are even and its class
in $\mathcal Q_F$ is zero. We retain this abelian group, including torsion.

### B.3. A fixed even library, followed by physical routing

We first recall the ordinary refiner in the form used here. Throughout B.3, $n$ is the ambient order, whereas H.6 first uses the local order $N=|W|$. Its concluding rescaling gives the ambient-parameter formulation below; in particular, $M=2^h$ in (B.3.2). The input $X$ is a loopless graph on $W$ with $\Delta(X)\le2\rho n$. Its precise scope and source are given in Appendix G.4. On a vertex
set $W$, its auxiliary graph may be complete. For positive parameters
$\lambda,\rho$ with

$$
64\lambda n\le |W|,\quad 2^{24}\rho\le\lambda^2,
\quad \rho n\ge1,\quad\lambda n\ge256,
\tag{B.3.1}
$$

it refines all even, edge-count-divisible-by-three subgraphs of $X[W]$
into a fixed indexed library of even pieces of at most 42 edges. Its fixed
remainder has maximum degree at most $4\lambda n$, the number of indices
is at most $1224\rho n^2$, and the sum of the degrees of **all** library
pieces at any vertex is at most $4096\lambda n$.

The finite mechanism behind this auxiliary theorem is useful here. A binary
heap sends each vertex to a hub in a set of size $2^h$, and then sends each
hub to its parent. Choose

$$
64\rho n\le\lambda2^h\le128\rho n.
\tag{B.3.2}
$$

At each level the selected edge bits are transported along endpoint chains
and hub-pair chains. A chain with bits $x_j$ uses the carries
$c_{j+1}=c_j+x_j\pmod2$. Its two alternative two-edge paths are allocated
according to the incoming carry. Every wire is allocated once, and its
boundary cancels the two adjacent carries. The last heap level has no
remaining pair. A second chain carries the edge count modulo three, using
three alternative four-cycles per wire. Up to two always-used adjustment
cycles fix the remainder's residue. Keeping all alternatives beforehand
gives the universal library. The bounds above count all alternatives and
all requested paths, not just the paths in one eventual selection.
This is the ordinary universal refiner used here; in particular
the bound 42 refers to its final modulo-three pieces.

Apply it to the vertex sets of the connected components of the active
label graph. The restriction of an integrally divisible $L$ to such a
component is even and has edge count divisible by three: each triangle
column is wholly inside one component. Distinct component vertex sets are
disjoint. Enlarging the bounds, set

$$
K_v=4096t,\qquad \ell=t+1,
$$

where $t$ is the number of labels. We obtain a virtual remainder $R_v$
and a library $P_i^v$ with size at most 42, number at most
$K_v\rho n^2$, and total vertex load at most $K_v\lambda n$.
Virtual remainder edges need not be allowed host edges.

Replace each virtual remainder edge once by a physical path. Its endpoint
labels lie in one active component. A shortest label path, with a two-edge
detour if necessary, has length between two and $t+1$. All its consecutive
pairs are active. Give a virtual edge weight

$$
w(e)=|\{i:e\in P_i^v\}|.
\tag{B.3.3}
$$

The empty-residue selection covers $R_v$, so $w(e)\ge1$ there. Moreover

$$
\sum_{e\ni v}w(e)\le K_v\lambda n,
\qquad \sum_{e\in R_v}w(e)\le42K_v\rho n^2.
\tag{B.3.4}
$$

Route the paths successively, avoiding $X$, previous path edges, repeated
vertices of the current path, and vertices whose accumulated auxiliary
weighted load is at least $4K_v\lambda n$. The total auxiliary load is
at most $2\ell\sum_e w(e)$; hence the number of heavy vertices is at
most $21\ell\rho n/\lambda$. A final internal vertex may require two
specified adjacencies, which is why supply of order two is used. The
sufficient margins are

$$
64K_v\lambda\le\omega,\quad
128\ell\rho\le\omega\lambda,\quad
\rho\le\lambda,\quad4(\ell+1)\le\omega n.
\tag{B.3.5}
$$

They leave a candidate at every step. An internal vertex receives at most
one overshoot of size $2w(e)\le2K_v\lambda n$, so its auxiliary weighted
load is at most $6K_v\lambda n$. Including original endpoints gives
total library load at most $7K_v\lambda n$. The same physical path is
used in every alternative containing its virtual edge. Consequently any
disjoint virtual selection maps to a disjoint physical selection; all its
edges are exactly the fixed routed remainder together with $L$.
Subdivision preserves evenness. Piece size is at most $42(t+1)$.

For reference, the frozen producer uses

$$
c_0=\min\left\{2^{-24},\frac1{1024(4096t)(t+1)}\right\},\quad
m_0=42(t+1),\quad K_0=7\cdot4096t.
\tag{B.3.6}
$$

Taking $\lambda\le c_0\omega$, $\rho\le c_0\lambda^2$,
$\rho n\ge1$, and $c_0\lambda n\ge1$ implies (B.3.1) and (B.3.5).
We have produced even pieces, not yet globally divisible pieces.

### B.4. Eliminating every global charge

There are finitely many labelled loopless active even graphs with at most
$m_0$ edges and at most $2m_0$ vertices. List their classes in
$\mathcal Q_F$ as $g_1,\ldots,g_r$. Every piece of the library has one
of these classes. For each generator choose its pattern as a positive
token. To construct a negative token, replace each edge $ab$ of that
pattern by $az_e,z_eb$, choosing the label of $z_e$ so that $abz_e$
is an allowed triangle. Modulo triangle columns this changes the edge's
class to its negative. Both tokens are even; their sizes are at most
$2m_0$. These are actual finite graphs, not formal negative edges.

Use the descending chain

$$
H_0=\langle g_1,\ldots,g_r\rangle\supseteq H_1
=\langle g_2,\ldots,g_r\rangle\supseteq\cdots\supseteq H_r=0.
\tag{B.4.1}
$$

Suppose the current pieces have values in $H_{j-1}$. Choose integers
$c_i$ with $[P_i]-c_ig_j\in H_j$. If the order of $g_j+H_j$ is
$d>0$, choose $0\le c_i<d$. If its order is infinite, put $d=0$
and use any integer representatives. The bounded size of the current
pieces gives a fixed bound $a_j\ge\max_i|c_i|,d$.

For every selected family $T$ refining $R\cup L$, divisibility of $L$
gives
$$
\sum_{i\in T}[P_i]=[R].
\tag{B.4.2}
$$

Let $T_0$ be a selection for the empty residue. With
$K=(\sum_{i\in T_0}c_i)\bmod d$, where reduction modulo zero is the
identity, (B.4.2) implies

$$
d\mid \sum_{i\in T}c_i-K.
\tag{B.4.3}
$$

For $d=0$, all demands sum exactly to $K$. For $d>0$, adjoin
$a_j|\mathcal P|$ **fixed empty slots** with demand $-d$, and select
exactly

$$
s_T=\frac{\sum_{i\in T}c_i-K}{d}
$$

of them. The representative convention proves $0\le s_T\le a_j|\mathcal P|$.
All augmented selections now have the same total demand. An empty slot
will receive $d$ positive tokens, whose combined class belongs to $H_j$.
This is the step that retains torsion; replacing (B.4.3) by an equality
without these slots would be incorrect.

Here is the fixed token ledger. A piece of demand $c>0$ takes $c$
negative tokens. A piece of demand $c<0$ takes $-c$ private positive
tokens. Each private positive token has a negative mate; if its parent
piece is not selected, the pair is selected as a release piece. The
remaining negative variable slots have cardinality
$\sum_i\max(c_i,0)-K$, independent of $T$. The bounded robust matching
lemma supplies a fixed bipartite graph matching precisely that many
variable slots together with its fixed buffer slots to positive buffers,
for every allowed choice of the variable slots. A graph edge specifies a
two-token cancellation piece. A perfect matching therefore consumes each
remaining token exactly once. Selected old pieces, release pairs and
matching pairs partition the old selection and **all** the new tokens.

In the quantitative version used in the freeze, a ledger with total
absolute demand $z$ needs at most $9z$ tokens; each token occurs in at
most 44 library pieces; the number of new indices is at most the old
number plus $97z$. Including the empty slots gives

$$
\#\text{tokens}\le9a_j(a_j+1)|\mathcal P|,\qquad
|\mathcal P'|\le[1+98a_j(a_j+1)]|\mathcal P|.
\tag{B.4.4}
$$

The robust matching lemma is a finite auxiliary theorem, not a request
for new host resources depending on $L$: its graph and every token are
fixed before $T$. The host embedding takes place next.

Embed the tokens greedily, edge-disjointly and outside $R\cup X$, using
guarded supply up to the maximum token order. Cap their accumulated vertex
load by $\Delta=\lceil\lambda n\rceil+2m_0+1\le2\lambda n$.
Mark vertices of load exceeding $\Delta-2m_0$; total edge mass bounds
their number. Avoiding those vertices prevents more than one overshoot.
The constants in this iteration are fixed by a finite recursion, rather than by the host. Put $N_0=2m_0$ and list, with repetitions allowed, the charges of all active loopless even patterns on $N_0$ labelled positions having at most $m_0$ edges. Denote this list by $g_1,\ldots,g_r$. In particular,
$$
r\le t^{N_0}2^{\binom{N_0}{2}}.
$$
Let $H_j=\langle g_{j+1},\ldots,g_r\rangle$. The quotient $H_{j-1}/H_j$ is cyclic; write $d_j=0$ for infinite order and otherwise let $d_j$ be its order. Choose an integer coefficient $a_j(x)$ representing each $x\in H_{j-1}$ modulo $H_j$, using $0\le a_j(x)<d_j$ when $d_j>0$. For a piece-size bound $m_j$, the possible charges belong to the finite set $\mathcal V(m_j)$ of images of ordered type-edge vectors with coordinates in $\{0,\ldots,2m_j\}$. Starting with $m_1=m_0$, define
$$
\begin{aligned}
A_j&=d_j+\max\bigl(\{0\}\cup\{|a_j(x)|:x\in\mathcal V(m_j)\cap H_{j-1}\}\bigr),\\
m_{j+1}&=m_j+2m_0A_j+4m_0,\\
L_j&=1+98A_j(A_j+1).
\end{aligned}
$$
Set $\mathcal L_{r+1}=1$, $\mathcal T_{r+1}=0$, and, backwards through the list, set
$$
\mathcal L_j=45L_j\mathcal L_{j+1},\qquad
\mathcal T_j=9A_j(A_j+1)+L_j\mathcal T_{j+1}.
$$
We use $m=m_{r+1}$, $L_c=\mathcal L_1$ and $T_c=\mathcal T_1$; for an empty list these are $m_0,1,0$. The one-layer construction uses at most $9A_j(A_j+1)$ tokens per incoming index, multiplies the index count by at most $L_j$, and bounds the new multiplicity load by the factor $45L_j$. Applying these bounds successively gives exactly the recursion above. Coefficient choices and maxima are made in the fixed finitely generated abelian group, before the host or residue. Thus these are defined finite constants, although no optimized closed-form bound is claimed.

One explicit sufficient choice is the following. Put $N_0=2m_0$,
$U=N_0+N_0(N_0+1)/2$, and

$$
B=(U+1)(K_0+r+3)(2m_0+3)(8m_0T_c+1)(K_0+1),\qquad
c=\min\{c_0,1,(8B)^{-1}\}.
\tag{B.4.5}
$$

The hypotheses $\lambda\le c\omega$, $\rho\le c\lambda^2$,
$\rho n\ge1$, $c\lambda n\ge1$ give both

$$
U+U(K_0\lambda n+2\rho n+r\Delta+\Delta)<\omega n/2,
$$
$$
8m_0T_cK_0\rho n^2\le(\Delta-2m_0)\omega n.
\tag{B.4.6}
$$

The first inequality pays for used neighbours and distinctness; the
second pays for heavy vertices. They justify every token embedding.
After the last layer every piece has zero class in $\mathcal Q_F$,
and remains even. Section B.2 proves its full integer divisibility. Enlarging
$K$ to $L_c(K_0+2r+2)$, the result is a fixed divisible library with

$$
|P_i|\le m,\quad |\mathcal P|\le K\rho n^2,\quad
\Delta R\le K\lambda n,\quad
\sum_i d_{P_i}(v)\le K\lambda n.
\tag{B.4.7}
$$

### B.5. Turning the library into a universal absorber

Let $C_{\rm cert}=C(F,m)$ be the signed-certificate cost supplied by A.4, and put $C_{\rm abs}=30C_{\rm cert}$. Corollary A.5.2 bounds absorber edges by $C_{\rm abs}$; these two constants have different roles. Define
$$
S_t=\left\lceil\max\{4,2m+5t+9C_{\rm cert}\}\right\rceil,
\qquad S=\max(S_t,U,S_{\rm ref},4).
$$
Here $U$ is the template order in (B.4.5), and $S_{\rm ref}=\max(2,U)$ suffices for the routed refiner and its charge templates. The larger value of $S_t$ is a budget bound as well as a supply order. Reduce the desired degree budget to

$$
\delta'=\min\{\delta,\omega/[8(S_t+1)]\}.
$$

Use the following parameters in (B.4.7):

$$
\lambda=\frac{\min(c,1)\omega\delta'}{16(K+1)(C_{\rm abs}+1)},\qquad
\rho=\frac{\min(c,1)\lambda^2}{16(K+1)(C_{\rm abs}+1)}.
\tag{B.5.1}
$$

It suffices to take

$$
N\ge\lceil1/\rho\rceil+\lceil1/(c\lambda)\rceil
+\lceil2C_{\rm abs}/\delta'\rceil+\lceil4(S_t+1)/\omega\rceil.
\tag{B.5.2}
$$

Give each library index a private terminal absorber $A_i$, disjoint from
$X,R$, and from previously embedded $A_j$. The load-controlled embedding
of Appendix A, Section A.6 applies because

$$
S_t+2S_t\delta'n<\omega n/2,
$$
$$
\max\{(2\rho+K\lambda)n,\delta'n+C_{\rm abs}\}+C_{\rm abs}K\lambda n\le2\delta'n,
$$
$$
4(2\rho+K\lambda+K\rho C_{\rm abs})\le\delta'\omega.
\tag{B.5.3}
$$

These inequalities respectively control avoidance of used edges, load at
roots, and the number of heavy vertices. They follow by substitution in
(B.5.1), using $2C_{\rm abs}\le\delta'n$. Set $A=R\cup\bigcup_i A_i$.
For a chosen divisible $L\subseteq X$, use a disjoint library selection
$R\cup L=\dot\bigcup_{i\in T}P_i$. Decompose $A_i\cup P_i$ for
$i\in T$ and $A_i$ for all remaining indices. Taking $L=\varnothing$
also decomposes $A$. This proves (B.1.1), with its universal quantifiers.

The implication to A.6 can now be checked without an implicit constant. Set $K=m$, $a=\omega n$, $T=\delta'n$, $D=2\delta'n$, $c=C_{\rm abs}$ and $\Lambda=K_{\rm lib}\lambda n$, where $K_{\rm lib}$ denotes the library constant written $K$ in (B.4.7). The second inequality of (B.5.3) gives the load inequality of A.6 directly; multiplying the third by $n^2$ gives its mass inequality. The remaining condition follows from
$$
2m+5t+9C_{\rm cert}+8\delta'n
\le S_t+2S_t\delta'n<\omega n/2.
$$
Indeed (B.5.2) gives $S_t<\omega n/4$, while $\delta'\le\omega/[8(S_t+1)]$ gives $2S_t\delta'n<\omega n/4$. This also explains why the certificate cost cannot be substituted for the absorber-edge bound in the load or mass inequalities.

### B.6. Quantitative deduction of Theorem A

In (2.7), choose $h=S$, $\omega_0=1$, and take its regularity tolerance $c$ to be $\varepsilon$ in (B.6.2). All constants defining $S$ depend only on the family.

Let $C_F$ be the complete inverse constant of Appendix A, Section A.2 and let $H_F>0$
be the corresponding physical-host inverse constant of Appendix A, Section A.3. Set

$$
\kappa=\min\{\omega/8,\omega^{12}/(216H_F)\},\qquad
\varepsilon_{\rm inv}=\omega^{11}/(4H_F).
\tag{B.6.1}
$$

Call (B.1.1) with $\delta=\kappa/8$, obtaining $\rho_0,N_0$, and set
$\rho=\min(\rho_0,\kappa/8)$. If $\tau(\eta)$ denotes the load
tolerance of the typed packing lemma, take

$$
\varepsilon=\tfrac12\min\{\varepsilon_{\rm inv},
\tau(\min(\omega/8,1,\omega^2))\}.
\tag{B.6.2}
$$

In addition to $N_0$, the order threshold is the maximum of

$$
\lceil8/\omega\rceil,\quad
\lceil2^{27}\rho^{-9}\omega^{-6}\rceil,\quad
N_{\rm pack}(27/\omega,\min(\omega/8,1,\omega^2)),\quad
N_{\rm cover}(54/\omega,\rho^2\omega/12).
\tag{B.6.3}
$$

These are thresholds of the packing and cover-down lemmas, fixed before
the host. The original regular weights lie in
$[\omega/n,1/(\omega n)]\subseteq[\omega^2/n,27/(\omega n)]$.
The common-neighbour assumption gives the guarded supply used above.

To check the remaining hypothesis of the initial packing, fix a vertex $v$ and choose a forbidden partner $j$ for its label using (3.2). Guarded supply with no prescribed neighbours gives $|V_j|\ge\omega n$. Since all edges have allowed types, $N_G(v)\cap V_j=\varnothing$, including when $j=p(v)$. Consequently
$$
d_G(v)+|V_j|\le n,\qquad \Delta(G)\le(1-\omega)n.
$$
Guarded supply for two roots also gives the anti-edge condition of Appendix G.1. These are precisely the extra hypotheses of the near-load packing and reserve-selection statements in Appendix G.2; the local lattice conditions are used separately.

The packing lemma first provides a large triangle packing from which one
selects a triangle-decomposable reserve $X$, of maximum degree at most
$2\rho n$, retaining anti-edge supply $\rho^2\omega n/12$. Construct
$A$ using (B.1.1). Both $A$ and $X$ are decomposable. Therefore deleting
$A\cup X$ preserves the local and global compatibility required by Appendix A's
real inverse. The deleted maximum degree is at most
$(2\delta+2\rho)n\le\kappa n/2$. Equations (B.6.1)–(B.6.2) pay for the
initial weight defect and for the loss of triangles through deleted edges.
The real repair gives exact nonnegative weights on $G-(A\cup X)$, with
upper bound $54/(\omega n)$.

The cover-down lemma, applied with those repaired weights and the reserved
anti-edge supply, packs $G-A$ leaving an integrally divisible $L\subseteq X$.
Now decompose $A\cup L$. These two edge-disjoint decompositions cover
$G$, proving Theorem A. Recomputing the weights after deletion is essential:
restriction of the original weights alone would not establish this step.

\bigskip

## Appendix C. The semidense mixed-triangle theorem

### C.1. Statement and conventions

Let $F_0=\{001,011\}$. For every $\alpha>0$ there are
$\varepsilon>0,N$ such that the following holds for $n\ge N$.
Suppose $V(G)=V_0\dot\cup V_1$, and

$$
|V_i|\ge(1-\varepsilon)n/2,\qquad
(1/4-\varepsilon)n\le d(v,V_i)\le(1/4+\varepsilon)n
\quad(v\in V_i),
\tag{C.1.1}
$$
$$
d(v,V_{1-i})\ge(1/2-\varepsilon)n\quad(v\in V_i).
\tag{C.1.2}
$$

For at least one part $D=V_i$, the graph $G[D]$ has edge-edit distance
greater than $\alpha|D|^2$ from both the union of two cliques and the
complete bipartite graph associated with **each** cut $X,D\setminus X$
with $|X|=\lfloor|D|/2\rfloor$. Distances count unordered edges.
If all degrees of $G$ are even and

$$
e(V_0,V_1)=2[e(V_0)+e(V_1)],
\tag{C.1.3}
$$

then $G$ has a decomposition into mixed triangles.

The conditions in (C.1.3) and even degrees are exactly $F_0$-integer
divisibility. Globally each mixed triangle has one internal and two crossing
edges. Locally the columns at either label generate all two-coordinate
integer vectors of even sum: the columns are $(1,1)$ and $(0,2)$,
or their interchange. This proves the equivalence, not merely necessity.

### C.2. Nonextremality supplies short walks in the good part

We give the elementary stability estimate that is used repeatedly. Let
$J$ be a graph on a set $D$ of $m$ vertices with degrees in
$[(1/2-\theta)m,(1/2+\theta)m]$, where $0<\theta\le1/100$ and
$\theta m\ge1$. For subsets $U,W$, let $a(U,W)$ count ordered
adjacent pairs. Suppose $|U|=(1/2\pm\theta)m$,
$|W|\ge(1/2-\theta)m$, and $a(U,W)\le\theta m^2$.
Writing $w=|U\cap W|$, we have

$$
|D\setminus(U\cup W)|\le2\theta m+w,
\qquad
w[(1/2-3\theta)m-w]\le2\theta m^2.
\tag{C.2.1}
$$

For the second inequality, sum the degree lower bound over $U\cap W$.
Neighbours outside $U\cup W$ contribute at most $w(2\theta m+w)$;
neighbours in $U\cup W$ contribute at most $2a(U,W)$.
If $w\le m/4$, the bracket in (C.2.1) is at least $m/8$, whence
$w\le16\theta m$. Otherwise (C.2.1) gives
$w\ge(1/2-11\theta)m$.

Move at most $\theta m+1$ vertices to make $U$ a balanced set $X$.
In the first case, $W$ differs little from $D\setminus X$, and

$$
a(X,D\setminus X)\le20\theta m^2+m.
$$

In the second case, $U\setminus W$ has size at most $12\theta m$,
so $a(U,U)\le13\theta m^2$ and

$$
a(X,X)\le15\theta m^2+2m.
$$

The degree bounds and these estimates give edit distance at most
$80\theta m^2$ to, respectively, the union-of-cliques or bipartite
balanced model. To see why the conclusion uses edit distance, use the
identities

$$
|E(J)\triangle E(K_X\cup K_{D\setminus X})|
=e(K_X\cup K_{D\setminus X})-e(J)+2e_J(X,D\setminus X)
$$

and the corresponding identity with the complete bipartite model. The
terms linear in $m$ are at most their coefficients times $\theta m^2$.

Consequently, when the distance from both models exceeds
$100\theta m^2$, every ordered pair $u,v\in D$, including $u=v$,
has more than $\theta m^2$ length-three walks: apply the contrapositive
with $U=N_J(u)$, $W=N_J(v)$. Excluding a set of $z$ possible internal
vertices discards at most $2zm$ such walks. A preceding edge gives a
similar supply of length-four walks. These estimates persist when the
walk is required to lie in the common crossing neighbourhood of a fixed
bounded collection of vertices, because each such vertex misses at most
$3\varepsilon n/2$ crossing neighbours.

In all subsequent uses choose

$$
\theta=\min(a,1)/100,\qquad e=\theta/2^{30},\qquad
\theta n\ge4096.
\tag{C.2.2}
$$

Here $a$ is the nonextremality parameter of the host under consideration.
The part sizes in (C.1.1) convert the degree bounds to the half-regular bounds
above, using $100e\le\theta$. In particular, the good internal graph
has many rooted triangles, by taking $u=v$. No analogous nonextremality
of the other part is needed.

### C.3. An explicit integral certificate on physical triangles

Let $P\subseteq E(G)$ be divisible and $|P|\le m_0$, where ultimately
$m_0=214$. Subtract one actual mixed triangle at each internal edge of
$P$. Such a triangle exists by (C.1.2). Denote their signed sum by $L$.
The residual integer edge function $R=1_P-\partial L$ is supported on
crossing edges, has even degree at every vertex, and has total coefficient
zero by (C.1.3). Also

$$
\|L\|_1\le |P|,\qquad\|R\|_1\le4|P|.
\tag{C.3.1}
$$

View $R$ as a matrix from the good part $D$ to the other part $B$.
Write its row sums as $2r_u$. Its total is zero, so $\sum_u r_u=0$.
Choose a single internal edge $bb'\in E(G[B])$ whose endpoints are
adjacent to every row root with $r_u\ne0$. The number of residual roots
is at most $8m_0$; the union bound on missing crossing neighbours and
the internal minimum degree ensure this edge exists. In detail it suffices
that $e(10m_0+10)\le1/100$, which holds for (C.2.2) and $m_0=214$.

Subtract $\sum_u r_u[ubb']$. The internal edge $bb'$ cancels because
$\sum r_u=0$; the remaining crossing matrix $R'$ has zero row sums
and even column sums. Its coefficient norm satisfies

$$
\|R'\|_1\le\|R\|_1+2\sum_u|r_u|\le2\|R\|_1.
\tag{C.3.2}
$$

Choose an anchor $b_0\in B$ adjacent to all row roots. For each nonzero
column $c$, work in the internal graph on
$D\cap N(c)\cap N(b_0)$, which contains all roots of that column and
a common anchor. Section C.2 supplies a length-four walk from each root to
the anchor. If its vertices are $v_0,\ldots,v_4$, the alternating edge
chain has signless incidence

$$
[v_0v_1]-[v_1v_2]+[v_2v_3]-[v_3v_4]
\longmapsto e_{v_0}-e_{v_4}.
\tag{C.3.3}
$$

It costs four. A neighbour $w$ of the anchor $v_*$, minus the chain
for $e_w-e_{v_*}$, gives $2e_{v_*}$ at cost at most five. Thus an
integer vector $x$ of even total $2z$ has a physical internal-edge
presentation

$$
\sum_u x_u T_u+zD_*,\qquad
\text{cost}\le4\|x\|_1+5|z|\le\tfrac{13}{2}\|x\|_1.
\tag{C.3.4}
$$

For each internal edge $uv$ in this presentation, take
$[uvc]-[uvb_0]$. The internal edges cancel and the result has crossing
boundary $\sum_u x_u([uc]-[ub_0])$. Both triangles are physical, by
the common-neighbour restriction. The cost is at most $13\|x\|_1$.
Summing over columns cancels all $b_0$-edges because the rows of $R'$
sum to zero. Combining (C.3.1)–(C.3.4), the row correction and all columns
cost at most $27\|R\|_1$; hence the full certificate costs at most
$109|P|\le126|P|$.

We have proved a signed triangle certificate in the actual host with a
bound independent of $n$. A class-pair lattice certificate alone would
not have supplied the physical identities used in (C.3.3)–(C.3.4).

### C.4. Physical hinges and bounded terminal absorbers

Two distinct mixed triangles sharing an edge have roots $012$ and
$013$. The following finite trades specify the hinge completely. In each
row, the first and second mode cover the same hinge edges plus, respectively,
the two nonshared edges of $012$ and $013$.

| Case | New vertices | First mode | Second mode |
|---|---|---|---|
| Internal shared edge in good part | 4,5 in that part | 042,453,512 | 043,452,513 |
| Internal shared edge in other part | 4 in that part; 5,6,7 in good part | 042,125,456,167,473 | 043,425,156,467,173 |
| Crossing shared edge | 4,5 with suitable labels | 052,142,453 | 053,143,452 |

For the first row the hinge edges are
(04,45,51,42,43,52,53). For the second they are
(04,42,43,25,56,67,73,45,46,47,15,16,17). For the last they are
(05,14,42,52,43,53,45). Listing the edges in each mode verifies both
identities and pairwise edge-disjointness. Every listed triangle is mixed.

For an internal good edge, choose the path (0,4,5,1) from the walk
supply, with its internal vertices also adjacent across the partition to
2 and 3. For an internal bad edge, first choose 4 among the internal
neighbours of 0 and common crossing neighbours of 2,3. There are at least
$n/8$ choices. Then choose the path (2,5,6,7,3) in the good part with
its internal vertices adjacent to 1 and 4. There are at least
$\theta |D|^3/16$ choices. For a crossing shared edge, the four possible
label patterns of 2,3 permit two sequential choices, using one internal
neighbourhood and boundedly many almost-complete crossing neighbourhoods
at each step; there are at least $n^2/64$ ordered choices.

For clarity, the labels of 4,5 in the crossing case, when the labels of
0,1 are (i,1-i), are respectively ((1-i,1-i)), ((i,i)), ((i,1-i)),
((i,1-i)) for the patterns ((i,i)), ((1-i,1-i)), ((i,1-i)),
((1-i,i)) of 2,3; in the last pattern exchange the two root triangles
before using the third pattern. The adjacency choices follow the same
exchange. This avoids demanding two large internal-neighbourhood
intersections in the uncontrolled part.

Remove choices with repeated vertices. The walk bounds with avoided
vertices in Section C.2 already pay for this loss. Passing from labelled choices
to distinct physical edge sets divides by at most $i^{i-4}$ for support
order $i\in\{6,8\}$. With $|D|\ge n/3$, the preceding bounds imply

$$
\#\{\text{physical hinges of order }i\}
\ge\beta n^{i-4},\qquad \beta=\theta/2^{30}.
\tag{C.4.1}
$$

The exponent is $i-4$, because the four roots are fixed. These are
positive decompositions of simple edge sets, not signed trades counted
with multiplicity.

The signed-certificate-to-absorber lemma now applies to Section C.3. Each certificate
occurrence is separated using fresh vertices; matching positive and negative
edge occurrences is implemented by the hinges above. Its two modes give
decompositions of $A_P$ and $A_P\cup P$, with $A_P\cap P=\varnothing$.
For $|P|\le214$, its size is at most

$$
C=310\cdot126\cdot214.
\tag{C.4.2}
$$

Put $K=41(126\cdot214)+1$. It suffices that $K<n/8$ and
$2^{36}K<\beta n$; these inequalities allow avoidance of all previously
used vertices and edges in the finite construction. A terminal order
threshold is therefore

$$
N_t=\lceil4096/\theta\rceil+\lceil8K+1\rceil
+\lceil(2^{36}K+1)/\beta\rceil+1.
\tag{C.4.3}
$$

### C.5. Exact bounded weights: complete crossing graph, then restriction

We next construct weights needed by the packing theorem, independently of
the preceding integer certificates. Let $A=D$ be the good part and $B$
the other part. Temporarily complete all crossing edges, keeping both
internal graphs. Let $I,J$ be their signless vertex-edge incidence
matrices. A triangle weighting is described by two arrays
$X\in\mathbb R^{E(A)\times B}$, $Y\in\mathbb R^{A\times E(B)}$.
Its internal loads are $X\mathbf1,Y^{\mathsf T}\mathbf1$, and its
crossing load is

$$
IX+YJ^{\mathsf T}.
\tag{C.5.1}
$$

For every $u\in A$, average the identity

$$
\tfrac12([uv]+[uw]-[vw])\longmapsto e_u
\tag{C.5.2}
$$

over all ordered triangles through $u$ in the good part. It defines a
linear right inverse $Q$ of $I$. The lower bound on rooted triangles
from Section C.2 gives a norm bound of order $1/(\theta n)$.

Here is an explicit solution of the complete-crossing problem. For desired
internal loads $f,g$ and crossing loads $Z$, balancedness means
$\sum Z=2(\sum f+\sum g)$. Start with
$X_0=f\mathbf1^{\mathsf T}/|B|$ and
$Y_0=\mathbf1g^{\mathsf T}/|A|$. Put

$$
R=Z-IX_0-Y_0J^{\mathsf T},\quad r=R\mathbf1,\quad
Y_1=\frac{r\mathbf1^{\mathsf T}}{2|E(B)|},\quad
X_1=Q(R-Y_1J^{\mathsf T}).
\tag{C.5.3}
$$

The total of $R$, hence of $r$, is zero. Since each column of $J$
has sum two, $Y_1J^{\mathsf T}\mathbf1=r$. Thus $X_1\mathbf1=0$
and $Y_1^{\mathsf T}\mathbf1=0$. Equation (C.5.1), with
$X=X_0+X_1,Y=Y_0+Y_1$, has exactly the required loads.

Set $\tau=\theta/100$. The geometric bounds give
$|A|,|B|\ge n/3$, $|E(B)|\ge n^2/40$, and at least
$2\tau n^2$ ordered triangles at each vertex of $A$. Substituting in
(C.5.2)–(C.5.3) gives the following norm estimate. If every demand
coordinate is at most $M$ in absolute value, $X_0,Y_0$ are at most
$3M/n$; hence $R$ is at most $7M$, $r$ at most $7Mn$,
$Y_1$ at most $140M/n$, and $R-Y_1J^{\mathsf T}$ at most $147M$.
The coefficient norm of $Q$ is at most $3/(2\tau n)$, by counting
the appearances of a fixed edge in the averaged identity (C.5.2).
The resulting uniform bound is
$(143+147\cdot3/(2\tau))M/n\le512M/(\tau n)$, since $0<\tau\le1$.
Thus

$$
\|Sx\|_\infty\le\frac{512}{\tau n}\|x\|_\infty
\tag{C.5.4}
$$

for the complete-crossing inverse. The deliberately loose constant absorbs
the row-degree bounds in both internal incidence matrices.

Return to $G$. A surviving edge loses at most $3en$ mixed triangles
when the missing crossing edges are removed: each discarded third vertex
must be a missing crossing neighbour of one endpoint. Extend a balanced
edge demand by zero to the completed graph, apply $S$, and retain only
physical triangles. The resulting boundary operator is $I-E$, with

$$
\|E\|_\infty\le3e(512/\tau)\le1/2,
\tag{C.5.5}
$$

because $307200e\le\theta$. All residual demands are balanced, since
physical triangles have zero balance. The convergent geometric series
$S_{\rm phys}\sum_{j\ge0}E^j$ is therefore an exact inverse on that
space, bounded by $1024/(\tau n)$.

Give every mixed triangle the seed weight

$$
\phi_0(T)=\frac2{(1+4e)n}.
\tag{C.5.6}
$$

Direct third-vertex counting using (C.1.1)–(C.1.2) gives edge loads in
$[1-14e,1]$ and seed weights in $[1/n,2/n]$. By (C.1.3), the defect
$1-\partial\phi_0$ is balanced. Repair it with the physical inverse.
The correction has absolute value at most
$14e(1024/\tau)/n\le1/n$, since $e=\theta/2^{30}$.
The repaired weights have exact edge load one and lie in $[0,4/n]$.
Nonnegativity, rather than a strictly positive lower bound, is the contract
needed here. This completes the weight producer.

### C.5a. The compatible semidense library

The semidense host does not supply arbitrary internal two-neighbour queries. We therefore use the following compatible-library result, proved in H.1–H.4. Its formal declarations are located in [8, Section 8]. It is distinct from the routed refiner of Appendix B.

Let $n\ge3$ and fix a loopless reserve $X\subseteq E(G)$ with $\Delta(X)\le\Delta_X$, an integer $a\ge0$, $M=2^a$ and an integer degree bound $\Delta_X$. There is an abstract fixed library with remainder $R$, compatible with the two root labels, that refines $R\cup L$ for every integrally $F_0$-divisible $L\subseteq X$. Its pieces have at most 214 edges. Its number of indices is at most
$$
I_X=57635(|X|+2M^2).
$$
The total multiplicity loads at old vertices, request middles, token vertices and hubs are bounded, respectively, by
$$
99d_X(v),\qquad66,\qquad88,\qquad
330(\lfloor n/M\rfloor+1)\Delta_X+1452M.
$$
If all four bounds are at most $L_{\max}\le q$, where $q$ is a positive integer, then an $\alpha$-anti-edgeful host realizes this entire library by one map, avoiding a forbidden edge graph of maximum degree $d$, provided
$$
2\cdot214L_{\max}+\frac{2\cdot214 I_X}{q}
+2(d+\Delta_X+2q)<\alpha n.
$$
The map fixes the old vertices, is injective on each piece and on the union of its edge identities, and leaves physical multiplicity load at most $2q$. Hence the same embedded library works for every later choice of $L$.

The construction first compresses the parity heap into $M$ hubs. Its physical parity pieces have at most 22 edges. The intermediate label of each two-edge request is chosen to complete an $F_0$ triangle with the two endpoint labels. Charge correction is then constructed with these labels already fixed; relabelling a previously corrected library would not justify this step. Its piece bound is $9|P|+16$, giving
$$
9\cdot22+16=214.
$$
The charge-layer and heap counts give the four multiplicity bounds and $I_X$ above. These are bounds on the entire library, not on one selected decomposition. The shared embedding uses only the resulting permitted two-edge requests. Its exclusions comprise piece collisions, vertices whose multiplicity load has reached its quota, and forbidden or previously used neighbours. Their bounds are the three terms in the strict inequality. Thus anti-edge supply suffices; common neighbours for an impermissible triple are never requested. Sections H.1–H.4 derive the finite heap, charge-layer and shared-embedding bounds; H.5 proves the robust-slot input used in the charge layer.

For the application in C.6 take $\alpha=1/8$, $d=0$ and
$$
\Delta_X=\lceil\kappa^2n\rceil,\quad
\kappa n\le M\le2\kappa n,\quad
q=L_{\max}=\lceil8192\kappa n\rceil.
$$
A power of two $M$ in this interval exists because $\kappa n\ge1$. The conditions (C.6.1) imply
$$
I_X\le524288(\kappa n)^2,\qquad
\Delta_X+2q\le32768\kappa n.
$$
They also bound each of the four abstract loads by $q$. Indeed $\Delta_X\le2\kappa^2n$, $q\ge8192\kappa n$, and the hub expression is at most $4224\kappa n$. Since $q\le8193\kappa n$, the embedding exclusions are at most
$$
(428\cdot8193+32768+65536)\kappa n
=3604908\kappa n<n/8,
$$
where the last inequality follows from $2^{27}\kappa\le1$. Here the middle term was bounded using $2\cdot214I_X/q\le32768\kappa n$.

Finally let $C$ be the bounded private absorber's **edge** bound in C.6. The mass and degree conditions for placing one such absorber per library index are
$$
\begin{aligned}
\max\{\Delta_X+2q,d_*n/4+C\}+2Cq&\le d_*n,\\
4\{n(\Delta_X+2q)+CI_X\}&\le(d_*n/4)(d_*n).
\end{aligned}
$$
In this display $d_*$ denotes the parameter called $d$ in (C.6.1), not the forbidden degree above. The bounds $2^{19}C\kappa\le d_*$, $2^{21}C\kappa\le1$, $2^{22}\kappa\le d_*^2$ and $C\le d_*n/4$ imply these inequalities: the maximum is at most $d_*n/2$, $2Cq\le16386C\kappa n<d_*n/2$, and $CI_X\le\kappa n^2/4$. This verifies the private-placement interface and gives (C.6.3) with the same order of quantifiers.

### C.6. Robustness and the final reserve

The terminal producer must remain usable after avoiding already used
vertices and edges. Start with nonextremality $2a$ and error $0\le d\le1/3$.
Delete at most $\eta n/2$ vertices and edges of maximum degree at most
$\delta n$. If $\eta,\delta\le a/100$, the retained host has
nonextremality $a$; its degree and size error is bounded by
$2(d+\eta+\delta)$. For the model-distance assertion, extend a balanced
cut of the retained part to a balanced cut of the original part without
changing the sides of retained vertices. Writing $D'$ for the retained
part and $B_{\rm del}$ for deleted edges, the additional edit cost is at most
$$
|D\setminus D'|\,|D|+|B_{\rm del}|
\le(\eta/2+\delta)n^2\le an^2/9\le a|D|^2.
$$
Here $|D|\ge n/3$, and the deliberately loose edge bound
$|B_{\rm del}|\le\delta n^2$ suffices. The original distance exceeds
$2a|D|^2$, so the retained distance exceeds
$a|D|^2\ge a|D'|^2$. This is
why the original parameter is doubled before applying the local producers.

Now fix the original $\alpha>0$, and put $a=\alpha/2$. Use (C.2.2),
(C.4.2), and let $N_0$ dominate both the terminal and weight thresholds.
Set

$$
d=\min\{e/16,a/1000,1/1000\},
$$
$$
\kappa=\min\{2^{-27},d/(2^{19}C),(2^{21}C)^{-1},d^2/2^{22}\},
\quad\rho=\kappa^2,\quad\sigma=\rho/2,\quad\gamma=\sigma^2/96.
\tag{C.6.1}
$$

These choices give $\kappa^2\le d$, $2^{19}C\kappa\le d$,
$2^{21}C\kappa\le1$, and $2^{22}\kappa\le d^2$.
Let $N_n$ be the typed packing threshold with weight bound $4/n$ and
residual maximum degree $n/64$, and $N_c$ the typed cover-down threshold
for weight bound $4/n$ and anti-edge parameter $\gamma$. Take

$$
N=2N_0+N_n+N_c+
\left\lceil2^{27}\sigma^{-9}(1/8)^{-6}\right\rceil
+\lceil1/\rho\rceil+\lceil4C/d\rceil+1.
\tag{C.6.2}
$$

Use the exact weights of Section C.5 to obtain the first packing. The reserve-selection
lemma selects a triangle-decomposable $X$ of maximum degree
$2\sigma n=\kappa^2n$, with anti-edge parameter $\gamma$. The host
itself has anti-edge parameter $1/8$, from its crossing and internal
degree bounds. The compatible semidense library of C.5a produces divisible pieces of at most 214 edges with a single shared embedding. Apply the
robust terminal construction above successively to that whole library.
Equations (C.6.1)–(C.6.2) are precisely the budgets that bound used root load,
avoid heavy vertices, and pay the constant cost $C$. The resulting
absorber $A\subseteq G-X$ satisfies

$$
\Delta A\le dn,\qquad A\text{ decomposable},\qquad
A\cup L\text{ decomposable for every divisible }L\subseteq X.
\tag{C.6.3}
$$

Its construction precedes the second packing. Since $A,X$ are disjoint
and decomposable, $G-(A\cup X)$ remains integrally divisible. Its
deleted maximum degree is at most $2dn$. The robustness estimate puts
this graph inside the hypotheses of Section C.5, so construct **new exact weights**
there. The cover-down theorem with these weights leaves a divisible
$L\subseteq X$ in $G-A$. Decompose $A\cup L$ by (C.6.3).
This proves the theorem with $\varepsilon=d$ and $N$ from (C.6.2).

\bigskip

## Appendix D. Splitting vertices along link components

### D.1. Splitting the labels

Let $F$ be a family of triangle types on a finite set $I$, with every
label appearing in at least one type. For $r\in I$, its link $L_r$
has an edge $ab$ precisely when $\{r,a,b\}\in F$. Loops are allowed
in this *label graph*. They represent repeated labels, not loops in the host.
Retain only the active vertices of $L_r$, and let $\mathcal C_r$ be
its connected components. Write $C_r(s)$ for the component containing an
active label $s$. The split label set is
$$
I'=\{(r,C):r\in I,\ C\in\mathcal C_r\},\qquad t'=|I'|,
$$
with projection $\pi(r,C)=r$.

If $\{a,b,c\}\in F$, the edge $bc$ in $L_a$ gives
$C_a(b)=C_a(c)$. Hence
$$
\sigma\{a,b,c\}
=\{(a,C_a(b)),(b,C_b(a)),(c,C_c(a))\}
\tag{D.1.1}
$$
is well defined as a multiset, independently of the enumeration of its
corners. This remains true when labels repeat. Put $F'=\sigma(F)$.
Projection recovers the original type, so $\sigma$ is injective.

**Lemma D.1.1.** The active link at $(r,C)$ in $F'$ is isomorphic to
$L_r[C]$. The isomorphism, including loops, is
$$
s\longmapsto (s,C_s(r)),\qquad s\in C.
\tag{D.1.2}
$$

**Proof.** The map is injective because its first coordinate recovers $s$.
An edge $sq$ of $L_r[C]$ is the type $\{r,s,q\}$. Its split
type contains $(r,C)$ and contributes the edge between the two images in
(D.1.2). Conversely, every type containing $(r,C)$ is the split of such
a type: projection gives $r,s,q$, and its corner at $r$ specifies
that $s,q$ lie in $C$. These statements also hold for $s=q$.
$\square$

In particular, all active split links are connected. Splitting does not
remove bipartiteness: the split link is bipartite exactly when the original
component is. Thus this operation alone cannot settle a family whose
remaining difficulty is a bipartite link.

### D.2. Splitting the host

Let $G$ be a simple graph with label map $p:V\to I$, all of whose
edges have allowed label pairs. Replace $v$ by one copy $(v,C)$ for
each $C\in\mathcal C_{p(v)}$, with label $(p(v),C)$. Send an edge
$uv$ to
$$
\Phi(uv)=
(u,C_{p(u)}(p(v)))\,(v,C_{p(v)}(p(u))).
\tag{D.2.1}
$$
Let $G'$ have exactly these edges. There are no edges between two copies
of the same original vertex. Projection onto original vertices is a left
inverse of $\Phi$, so $\Phi$ is injective and preserves cardinality,
unions, and disjointness of edge sets.

**Lemma D.2.1.** For every $E\subseteq E(G)$, $\Phi$ gives a bijection
between the allowed triangle decompositions of $E$ and the
$F'$-triangle decompositions of $\Phi(E)$.

**Proof.** For an allowed triangle $uvw$, its two incident edges at
$u$ choose the same copy of $u$, by the component identity preceding
(D.1.1). The same holds at $v,w$. Its image is therefore one triangle,
of type $\sigma\{p(u),p(v),p(w)\}$.

Conversely, an $F'$-triangle in $G'$ projects to three distinct original
vertices, since every two of its corners are joined and copies of a single
vertex are never joined. Its projected type is in $F$. Each of its
edges is the unique image under $\Phi$ of its projection, so lifting the
projected triangle recovers the original triangle. The edge bijection then
transports decompositions in both directions. $\square$

**Lemma D.2.2.** Integer compatibility of $E$ is equivalent to integer
compatibility of $\Phi(E)$.

**Proof.** For the global counts use the ordered convention of Appendix A. On allowed ordered pairs define the coordinate embedding
$$
e_{rs}\longmapsto e_{(r,C_r(s)),(s,C_s(r))}.
\tag{D.2.2}
$$
It is injective, since projection recovers $r,s$. The global count vector
of $\Phi(E)$ is the image of that of $E$, and the image of the
column for $\tau$ is the column for $\sigma(\tau)$. For repeated
labels this assertion counts the same corner pairs with their multiplicities;
in particular a diagonal entry is still counted twice. Since $F'=\sigma(F)$
and (D.2.2) is injective, membership in the global integer spans is equivalent.

At a vertex of label $r$, the local integer lattice is the incidence
lattice of its link:
$$
\Lambda_r=\left\langle e_s+e_q:sq\in E(L_r)\right\rangle_{\mathbb Z}
=\bigoplus_{C\in\mathcal C_r}
\left\langle e_s+e_q:sq\in E(L_r[C])\right\rangle_{\mathbb Z}.
\tag{D.2.3}
$$
The direct sum is literal: the components have disjoint coordinate supports.
For a loop, the generator is $2e_s$. The profile at the copy $(v,C)$
is the restriction of the profile at $v$ to $C$, transported by
(D.1.2). Lemma D.1.1 identifies its lattice with the corresponding summand of
(D.2.3). Membership of the original profile is therefore equivalent to
membership at all copies. Together with the global assertion this proves the
lemma. $\square$

### D.3. Supply and degree bounds

**Lemma D.3.1.** Vertex splitting has the following quantitative properties.

1. A split class $(r,C)$ has exactly $|V_r|$ vertices.
2. If $n'=|V(G')|$, then $n\le n'\le t'n$.
3. For every edge set $X$,
   $\Delta(\Phi(X))\le\Delta(X)$.
4. For $A'\subseteq E(G')$, its projected edge set satisfies
   $\Delta(\Phi^{-1}(A'))\le t'\Delta(A')$.
5. A compatible common-neighbour supply for at most $h$ prescribed
   vertices passes to $G'$ with the same $h$ and the same *absolute*
   number of candidates.

**Proof.** The first two assertions follow directly from the definition of
the copies; every original label has an active link. Edges incident with a
particular copy form a subset of those incident with its original vertex,
which proves the third. The edges incident with an original vertex partition
among its copies. It has at most $t'$ copies, proving the fourth.

For the last assertion, prescribe split roots and a compatible target label
$(r,C)$. Project the roots to $V$; this cannot increase their number.
A common neighbour $w\in V_r$ of the projected roots gives the candidate
$(w,C)$. Compatibility of the split target with each split root forces
exactly the two copy classes in (D.2.1), so this candidate is adjacent to all
the split roots. Distinct $w$'s give distinct candidates. The common
neighbour supply in $G$ is therefore a lower bound for that in $G'$.
$\square$

The distinction between absolute and relative bounds matters. A class of
size at least $\gamma n$ is guaranteed to have size at least
$(\gamma/t')n'$, not necessarily $\gamma n'$. A supply of $an$
becomes at least $(a/t')n'$. Missing-neighbour bounds in each allowed
class pass unchanged in absolute terms: the relevant candidate class in the
split graph is a copy of the original class and the adjacency test is the
same. None of these observations asserts automatic transport of every
weighted pattern-regularity condition used elsewhere in the paper.

### D.4. The universal absorber transfers back

For clarity, say that $G$ has the universal absorber property at
$(\rho,\delta)$ if every $X\subseteq G$ with
$\Delta(X)\le2\rho|V(G)|$ has a graph $A\subseteq G-X$, fixed
before the residual is chosen, with $\Delta(A)\le2\delta|V(G)|$, such
that $A$ and $A\cup L$ decompose for every integer-compatible
$L\subseteq X$.

**Proposition D.4.1.** If $G'$ has this property for $F'$ at
$(\rho,\delta/t'^2)$, then $G$ has it for $F$ at
$(\rho,\delta)$.

**Proof.** Let $X$ be given and set $X'=\Phi(X)$. By Lemma D.3.1,
$\Delta(X')\le2\rho n\le2\rho n'$. Obtain its fixed absorber
$A'\subseteq G'-X'$, and project it to $A$. Its edges are genuine
edges of $G$, and it is disjoint from $X$ by injectivity of $\Phi$.
Its maximum degree satisfies
$$
\Delta(A)\le t'\Delta(A')
\le t'\frac{2\delta n'}{t'^2}
\le2\delta n.
\tag{D.4.1}
$$
For an integer-compatible $L\subseteq X$, Lemma D.2.2 makes $\Phi(L)$
integer-compatible. Thus $A'\cup\Phi(L)$ decomposes. By Lemma D.2.1 its
projection $A\cup L$ decomposes as well. The same argument projects the
decomposition of $A'$. No choice of $A$ depends on $L$.
$\square$

The square $t'^2$ in this safe bound pays for two distinct effects:
the possible increase in the number of vertices and the merging of several
copies into one root. It is not legitimate to bound the degree of a projected
absorber by the degree of a single copy.

Finally, if the allowed-pair graph of the split family has several components,
every triangle type is contained in one component. Both its global columns
and its local columns have support in that component. Restricting an
integer-compatible edge set to a component therefore preserves integer
compatibility. Fixed absorbers constructed inside these components may be
united: the components are vertex-disjoint, so their maximum-degree bounds
do not add. This permits separate constructions on the connected split
families, followed by Proposition D.4.1.

### D.5. Scope in the classification argument

The PAR cases use this reduction to pass from disconnected links to their
connected components and then apply the appropriate proved absorber
construction there. The finite data must still establish that each resulting
component satisfies the hypotheses of that construction. The proof above
does not infer an absorber merely from connectedness of the links, nor does
it assert that bipartite links become non-bipartite after splitting.

\bigskip

## Appendix E. Parity, balance, charge and torsion

### E.1. Finite data, and what must be proved from them

Let $K$ be a component family on a finite label set. Let $c$ identify
the components of its active pair graph. All triples of $K$ lie inside
one component. Splitting as in Appendix D makes the relevant root links connected
on their active supports. There are then two local lattice possibilities.

* In a connected nonbipartite link, the signless incidence lattice consists
  of the integer vectors of even total.
* In a connected bipartite link with sides $L_r,R_r$, it consists of the
  integer vectors with equal sums on the two sides.

For the second assertion, multiply rows on one side by $-1$. The link's
signless incidence matrix becomes an oriented incidence matrix. Eliminating
leaves of a spanning tree represents every integer vector of total zero,
which proves sufficiency. For the first assertion, alternating along a
walk gives endpoint sums or differences according to its parity; an odd
closed walk gives $2e_a$. Transporting this to a fixed anchor and using
the even total proves sufficiency. These are integer arguments; connectedness
alone would not distinguish the two lattices.

Let $B_c$ be the labels with bipartite links and let
$\sigma_r(j)\in\{-1,0,1\}$ be their side signs, zero off active support.
For a physical vertex $v$ define its imbalance

$$
b_v(P)=\sum_j\sigma_{p(v)}(j)d_P(v,V_j).
\tag{E.1.1}
$$

The finite local certificate asserts that even supported profiles, with
$b_v=0$ when $p(v)\in B_c$, belong to the local lattice. It may be
given either by the walk/tree proof above or explicit integer coefficient
formulae. Each triangle has zero imbalance at its bipartite-link vertices.

For global counts use $u_{ij}=u_{ji}$, counting an internal edge once
on the diagonal. Its ordered incidence count is
$(1+\mathbf1_{i=j})u_{ij}$. The global certificate provides integer
triangle coefficients for every nonnegative supported count vector having
even class degree sums, edge total divisible by three, the class-summed
balances, and the indicated extra conditions. The three BAL regimes are

$$
\text{balances only};\qquad
\text{balances and }\chi(P)=0;\qquad
\text{balances and }g_0q\mid\psi(P).
\tag{E.1.2}
$$

Here $\chi,\psi$ are specified integer weights on ordered label pairs.
The corresponding scalar certificates are integer solution formulae, not
tests of real rank. Summing (E.1.1) over a label class gives exactly

$$
\sum_{v:p(v)=r}b_v(P)
=\sum_j\sigma_r(j)(1+\mathbf1_{r=j})u_{rj}.
\tag{E.1.3}
$$

Thus the local and scalar certificates together imply full integer
divisibility of a physical piece satisfying (E.1.2). This implication is the
last step of each construction, rather than an assumption on its output.

### E.2. The common starting library inside one component

Apply the ordinary heap refiner of Appendix B, Section B.3 inside the component vertex set.
Route every virtual edge by an allowed label walk of length exactly four,
as supplied by the finite component certificate. Each virtual edge is
weighted by one plus its multiplicity in the entire library. Greedy routing
avoids used edges and vertices above a weighted-load threshold $Q$.
It produces even, edge-count-divisible-by-three pieces of size at most
$S_0=168$, a physical remainder $R$, and the bounds

$$
|\mathcal P_0|\le1224\rho n^2,\qquad
\sum_{P\in\mathcal P_0}d_P(v)\le\Lambda_0,
$$
$$
\Lambda_0=4096\lambda n+2(Q+4096\lambda n+1),
\quad
\Delta(R\cup X)\le d_0:=2\rho n+4\lambda n+2(Q+4096\lambda n+1).
\tag{E.2.1}
$$

Replacing one edge by four adds three edges, so the walking construction
retains the modulo-three invariant of this component refiner. Its finite
alternatives, routing data and remainder are
fixed before the residue. For every divisible $L\subseteq X$, some
disjoint subfamily covers exactly $R\cup L$. Weighted routing is necessary:
bounding the degree of $R$ without bounding all library occurrences would
not justify the later private absorbers.

For PAR components with parity-only local lattices, three finite global
certificates occur in the existing component library: ordinary divisibility
already suffices; one integer charge remains; or one cyclic congruence
remains. In the first case (E.2.1) is already a divisible library. For a charge,
use the fixed ledger of Appendix B, Section B.4 with physical positive/negative tokens; for
a congruence, use the cyclic chain of Section E.5 below. The finite templates have
at most six edges. In the one-charge normalization used by the PAR
components, their charges are $\pm12$, the pair weights have absolute
value at most four, and the resulting pieces have at most 840 edges.
The finite lattice certificate and the terminal of Appendix A, Sections A.4–A.5 then close
each such component. This is the mathematical content reused by the PAR
splitting tables; the table does not assume a decomposition conclusion.

### E.3. Rooted balance tokens, including a concrete component

For every bipartite-link root label $r$, the BAL data specify two finite
rooted graphs $T_r^+,T_r^-$, with at most $g$ edges and at most $m+1$
vertices. They are loopless, active, even and contained in the component.
Their root has label $r$, and

$$
b_{\rm root}(T_r^\pm)=\pm2,\qquad
b_y(T_r^\pm)=0\quad(y\ne\text{root}).
\tag{E.3.1}
$$

Every vertex appearing in (E.3.1) is physical; the two tokens are graphs
with positive edges. They also satisfy $M\mid e(T_r^\pm)$, where
$M\in\{1,3\}$. If $M=1$, a separate local potential proves that
balanced even pieces have size divisible by three. This alternative is
necessary: not every valid root token has size divisible by three.

For example, take $K=\{001\}$. At a label-0 root,
$b=d(\cdot,V_0)-d(\cdot,V_1)$; label 1 has no balance condition. The
positive token is the cycle (0,1,2,3,0), with successive vertex labels
(0,0,1,0). Its root has imbalance 2, and the other label-0 vertices each
have one neighbour of either label. The negative token is the cycle
(0,1,2,3,4,0), labelled (0,1,0,0,1). Its root has imbalance $-2$,
and every other label-0 vertex is balanced. Both are active and even.
Their sizes are four and five, so use $M=1$. Once all label-0 vertices
are balanced,

$$
e_{01}=2e_{00},\qquad e(P)=3e_{00}.
\tag{E.3.2}
$$

This proves the required size divisibility and supplies the global triangle
coefficient $e_{00}$. At label 0 the local coefficient is $d_0=d_1$;
at label 1 it is $d_0/2$. This is the full component behind each of the
two components of the example $F_{\rm BAL000}=\{001,223\}$.

In general the finite potential mechanism has the same form. If a pair
weight is congruent modulo $q$ to the sum of two endpoint potentials,
and each vertex potential vanishes modulo $q$ on balanced even profiles,
then summing over vertices proves the global divisibility modulo $q$.
For charge divisibility by six one uses a potential for $\chi$ modulo
two and for $\chi-1$ modulo three, together with

$$
(\chi-1)(P)=\chi(P)-2e(P).
\tag{E.3.3}
$$

Equations (E.3.2)–(E.3.3) explain why the component tables include both local
coefficient formulae and potentials; a rational nullspace would not prove
the required congruences.

### E.4. Balancing all host vertices without an exponential loss

Process the vertices whose labels belong to $B_c$. At a current vertex
$x$, each library piece has even imbalance: its degree is even and each
active sign is odd. Its integer demand is $c_i=b_x(P_i)/2$. For a divisible
residue $L$, $b_x(L)=0$; hence every selected family has the same total
demand, namely $b_x(R)/2$. Use the fixed ledger from Appendix B, Sections B.4, realizing
its positive and negative tokens by rooted copies of $T_{p(x)}^\pm$
at $x$. Every new piece has imbalance zero at $x$. Previously treated
vertices remain balanced by (E.3.1), and pending imbalances are unchanged
on the descendant of an old piece; token-only pieces have no pending
imbalance.

The key size invariant is

$$
\mathcal V(P)=e(P)+g\sum_{y\ \mathrm{pending}}|b_y(P)/2|.
\tag{E.4.1}
$$

An old piece needs at most $|b_x(P)/2|$ tokens, adding at most that
quantity times $g$ edges, while exactly that term disappears from the
sum. Thus its descendant has no larger potential. A release or matching
piece consists of two tokens and has potential at most $2g$. Initially,
$\sum_y|b_y(P)/2|\le e(P)\le S_0$, so all pieces throughout have size
at most $S_0(1+g)$, which also dominates $2g$. This bound does not
depend on how many vertices are processed.

The same inheritance argument gives a uniform bound on future demands.
Let $N\ge9\Lambda_0$. At any pending vertex $y$,

$$
9\sum_i|b_y(P_i)/2|\le N.
\tag{E.4.2}
$$

Initially this follows from $|b_y(P_i)|\le d_{P_i}(y)$; later, the
only nonzero values are inherited by the unique old-piece descendants.
Consequently a layer uses at most $N$ new tokens. If $U$ is the union
of tokens placed so far, the inductive bounds are

$$
e(U)\le gN\cdot\#\{\text{treated roots}\},\quad
d_U(v)\le\theta+g+gN\mathbf1_{\{v\text{ treated}\}},
\tag{E.4.3}
$$
$$
\sum_{P\in\mathcal P}d_P(v)\le\Lambda_0+44d_U(v),\qquad
|\mathcal P|\le|\mathcal P_0|+11N\cdot\#\{\text{treated roots}\}.
\tag{E.4.4}
$$

The coefficient 44 is additive over the physically disjoint token sets;
it is not multiplied at each layer. The bound 11 pays for the at most
$97N/9$ new ledger indices.

To realize a layer, forbid nonroot vertices of current token load exceeding
$\theta$, of which there are at most $2gNn/\theta$ by (E.4.3). Also
forbid used vertices within the current batch and neighbours along already
used edges. A sufficient guarded-supply inequality is

$$
(m+1)+\frac{2gNn}{\theta}+(m+1)N
+(m+1)(d_0+\theta+g+2gN)<\omega n.
\tag{E.4.5}
$$

The four terms pay respectively for distinctness within a template, heavy
vertices, vertex disjointness of the current batch outside its fixed root,
and edge avoidance. At each step a remaining candidate embeds the next
template vertex. A nonroot has at most one load overshoot of $g$, while
the fixed root receives at most $gN$; this proves (E.4.3) for the next
layer. It proves existence of the required supply, rather than assuming
the existence of all root tokens at once.

After all layers, every piece is balanced and even. It retains size
divisibility by $M$; the finite potential implication gives divisibility
by three. In the balance-only regime the scalar certificate of Section E.1 now
proves full integer divisibility. The maximum degree, total library load,
and library count are those of (E.4.3)–(E.4.4).

### E.5. Extra global charge and torsion

#### One global charge

If the root tokens are $\chi$-neutral, their addition leaves the charge
of an old-piece descendant unchanged; token-only pieces have zero charge.
If instead their charges are $\pm c_r$, a token-only piece still has
charge zero, since it uses equally many tokens of both signs. A piece
with zero charge and no pending imbalance receives no tokens. Therefore
the number of pieces carrying either charge or a pending imbalance never
increases. It is bounded by the initial library size, not the much larger
number in (E.4.4).

After the vertex layers, let $u>0$ be the charge unit specified by the
finite potential certificate. Each piece's charge is divisible by $u$.
The component data include two even balanced templates of at most six
edges and charges $\pm u$. Use the same fixed ledger with demand
$\chi(P)/u$. The new tokens leave all vertex balances unchanged. Charge
vanishes on each new piece. In the normalization $|\chi_{ij}|\le4$,

$$
|\chi(P)|\le8e(P),\qquad
K_\chi=8S_0(1+g)|\mathcal P_0|
\tag{E.5.1}
$$

bounds the total absolute demand, also for the charged-root variant.
The extra ledger uses at most $9K_\chi$ tokens, at most $54K_\chi$
edges and at most $97K_\chi$ indices. Piece size is at most
$49S_0(1+g)$: six edges per token times $8e(P)$, plus the old piece.
Now apply the charged scalar certificate from (E.1.2).

#### One cyclic congruence

Suppose every preliminary even, size-divisible-by-three piece has charge
divisible by $g_0>0$, and the obstruction is
$\psi(P)/g_0\pmod q$. The finite data include a six-edge even token
with size divisible by three and value one modulo $q$. Its physical
copies need not initially be balanced. Apply this layer **before** the
vertex-balance layers.

Enumerate the old library in $s$ rows. Between consecutive rows place
$q$ private value-one tokens. An alternative at row $i$ has a bit
specifying whether it uses the old piece, an incoming carry $b<q$, and
outgoing carry $a=(b+x_i)\bmod q$, where $x_i$ is its selected old
value. Except at the last row, it receives $b$ tokens from the preceding
wire and $q-a$ from the following wire. The total value is
$x_i+b+q-a=0\pmod q$.
The next row receives the remaining $a$ tokens, so every wire is
partitioned exactly. The first carry is zero. The last carry is the fixed
value $r$ of the old remainder. At the last row there is no following
wire: its outgoing contribution is replaced by $(q-r)\bmod q$ fixed
tail tokens. They cancel $x_i+b\equiv r\pmod q$.
Divisible residues have value zero, so they all have this same
last carry. The empty selection fixes $r$ before any later residue.

There are at most $2qs$ alternatives and at most $qs$ tokens in the
fixed remainder. A piece receives at most $3q$ tokens, so its size is
at most $S_0+18q$. Its library load is at most $q\Lambda_0$ plus
$4q$ times the token load. Now balance vertices with tokens whose
$\psi$-charge is exactly zero. Congruence zero is preserved throughout;
the potential argument in Section E.4 applies with starting size $S_0+18q$.
Finally the torsion scalar certificate gives integer divisibility. Exact
neutrality of these later tokens is necessary; merely knowing that their
root imbalances are correct would not preserve the congruence.

### E.6. Quantitative choices and terminal assembly

Let the largest terminal certificate for the bounded pieces above have
constant $C_t$, so a private absorber uses at most $30C_t$ edges, as
in Appendix A. These constants are fixed by the finite component data before the
host is chosen. Choose an exponent $L$ large enough that

$$
2^{40}(30C_t+1)(g+1)(m+2)(t+1)\le2^L.
\tag{E.6.1}
$$

For the torsion components, where the frozen tables have $q\le12$, use
$2^{46}$ in place of $2^{40}$. Impose

$$
0<\omega\le1,\quad 0<\delta,\quad2^{63}\delta\le\omega,\quad
\lambda=\omega^2\delta/2^L,\quad
0<2^{24}\rho\le\lambda^2,\quad\rho n\ge1.
\tag{E.6.2}
$$

For the balance-only case choose

$$
Q=2^{15}\lambda n/\omega,\quad
\Lambda_0=4096\lambda n+2(Q+4096\lambda n+1),\quad
N=\lceil9\Lambda_0\rceil,\quad
\theta=2^6(g+1)N/\omega.
\tag{E.6.3}
$$

To verify that these choices suffice, measure costs in
$b=\lambda n/\omega^2$. Then

$$
\delta n=2^Lb,\quad \omega n\ge2^{63}\delta n,\quad
Q\le2^{15}b,\quad \Lambda_0\le2^{17}b,\quad
N/\omega\le2^{21}b,\quad\theta\le2^{27}(g+1)b,
\tag{E.6.4}
$$

The stronger intermediate estimate $\Lambda_0/\omega\le2^{17}b$
proves the bound for $N/\omega$, including its ceiling. This is needed
when dividing by $\omega$ in the definition of $\theta$.
Moreover, $2gNn/\theta\le\omega n/32$. Also
$\lambda n\ge2^{12}$, so ceilings and constant-sized templates are
absorbed in these bounds. Equations (E.6.1)–(E.6.4) imply (E.4.5) and the three
private-absorber inequalities of Appendix A, Section A.6: the forbidden-neighbour budget
is less than half the supply, the root plus auxiliary load is at most
$2\delta n$, and the total edge mass allows avoidance of heavy vertices.
Explicitly, with $D_U=\theta+g+gN$, those three inequalities are
$$
2S_0(1+g)+5t+9C_t+8\delta n<\omega n/2,
$$
$$
\max\{d_0+D_U,\delta n+30C_t\}
+30C_t(\Lambda_0+44D_U)\le2\delta n,
$$
$$
4\{2\rho n^2+16\lambda n^2+gNn
+30C_t(1224\rho n^2+11Nn)\}\le\delta\omega n^2.
\tag{E.6.5}
$$
In particular, the degree bound counts all library occurrences at a root;
using only the degree of their union would not prove it.

The charged-root variant uses the bound (E.5.1), a separate token density
$\rho_T=2^{11}(g+1)\rho$, and
$\lambda_T=2^{26}(g+1)\delta/2^L$; the charge-neutral variant is its
simpler case. Take $K_\chi$ to be the ceiling of
$8S_0(1+g)1224\rho n^2$, which bounds (E.5.1). These
extra scales are chosen from the already fixed component data. In the
torsion case take $\lambda_T=\Lambda_0/n$,
$\rho_T=2^{11}\rho$, and $N=\lceil45q\Lambda_0\rceil$. The same
estimates hold with $b'=64b$ and $2^{L'}=2^L/64$. This explains the
additional factor $2^6$ in (E.6.1). The source modules containing the explicit extra inequalities and their substitutions are identified in the companion [8, Section 7, Appendix E map].

Embed a private absorber for every final library piece, avoiding $X$,
the fixed remainder and all earlier private absorbers. They exist by Appendix A, Sections A.4–A.6 and the budgets just checked. For any later divisible residue $L$,
choose the refining subfamily, use the absorbing mode at its indices and
the empty mode at all other indices. The result is a component universal
absorber of maximum degree at most $2\delta n$. This construction also
handles an empty component by taking an empty absorber.

### E.7. Transport, finite certificates, and the family conclusion

PAR does not assert that a component is solvable because it is called
PAR. Its certificate consists of explicit splitting maps, a finite list
of reduced triples, a component map, and component isomorphisms to the
proved constructions in Sections E.2–E.6. For example,

$$
F_{\rm PAR000}=\{000,001,002,111,113\}
$$

splits into the two disjoint components

$$
\{000,001,003\}\quad\text{and}\quad\{222,224\}.
\tag{E.7.1}
$$

The first is a relabelling of the recorded mono-family component FM01;
the second is the two-label component KE2. A label-1 vertex of the original
graph has two copies, one for its link component containing label 0 and
one for that containing labels 1,3. The explicit pair map determines which
copy each edge uses. Thus every edge has exactly one lift, and every
allowed triangle has a consistent lifted triple. Appendix D proves preservation
of integer divisibility, guarded supply and projection of decompositions.

Absorbers for distinct reduced components are vertex-disjoint on the split
host. Their maximum degrees therefore do not add there. Upon projection,
Appendix D pays the stated $t'^2$ loss, where $t'$ is the number of split
labels. This loss is incorporated by reducing the component budget before
constructing the absorbers. It must not be omitted by confusing a split
vertex with the original vertex containing all its copies.

BAL tables specify, for each reduced component, the actual signs,
coefficient formulae, potentials, root templates, and optional charge or
torsion templates satisfying Sections E.1,E.3,E.5. They contain more information than
the names of families. Their finite identities are part of the accompanying certificate tables [8], with the universal component arguments proved above. The
following table records how that finite evidence enters the theorem.

| Route | Finite evidence | Universal argument |
|---|---|---|
| PAR | Splitting maps, component isomorphisms and base-component certificates [8] | Appendix D plus parity, charge or torsion components of Section E.2 |
| BAL without extra global charge | Local coefficient solutions, scalar solutions, balanced root tokens and potentials [8] | Sections E.1,E.3,E.4,E.6 |
| BAL with one charge | The preceding data plus the charge unit, annihilation identity, root-token charges and balanced global tokens | Sections E.1,E.3–E.6, including active-piece inheritance |
| BAL with torsion | Integral modulus, value-one token, neutral balancing tokens and a scalar solution under the congruence | Sections E.1,E.3–E.6, with the cyclic layer first |

The frozen aggregate has 271 PAR representatives and 357 BAL representatives
in these routes (301 without an extra charge, 52 with one charge, four with
torsion), in addition to 120 previously covered representatives. The
remaining seventeen conserved representatives use the construction of Appendix F.
The full finite enumeration, permutation transport and coverage theorem
are separate proved objects in the freeze. Exhaustive coverage uses the separate finite certificate and transport argument of Section 9; it does not follow merely by adding these counts.

For each component, the terminal and real-inverse constants are finite.
Taking maxima over its finitely many components, and then over the finite
family tables, fixes all parameters before choosing a host. Apply the
real-inverse, reserve and cover-down assembly of Appendix B, Section B.6 (with the flexible
scales (E.6.2) in the BAL case). It converts these universal absorbers and
regular weights into an exact decomposition. Relabelling back gives the
claimed typical-host result for each PAR/BAL family. Together with the
Appendix F and the census theorem this supplies the construction part
of Theorem D. The real inverse of Proposition A.2.1 is applied on the original four-label host; splitting labels for the component absorber does not require applying that proposition to more than four labels.

\bigskip

### E.8. The connected cases and the padded interface

The 120 representatives referred to as earlier cases have connected non-bipartite active root links. Of these, 93 have three-step links and are covered directly by Theorem A. The other 27 require their finite parity-component certificates; connected non-bipartite links alone do not establish the three-step condition. The same certificate route covers the 271 PAR representatives after the component separation of Appendix D. Thus the 27 cases are not being inferred from Theorem A, nor from the numerical total of the census.

We describe the intermediate interface to make this distinction explicit. A padded pattern has $m+3$ labelled positions in each of the $t$ classes, so its order is $q=t(m+3)$. For a triangle type, three of these positions are distinguished; an embedding must preserve all position labels and be injective, but only the three distinguished pairs are required to form that triangle. Padded regularity assigns weights to these embeddings in $[\omega n^{2-q},\omega^{-1}n^{2-q}]$ with edge loads within tolerance $c$ of one. Template extension requires at least $\omega n^{k-|S|}$ extensions of every prescribed injective labelled root map on $S$ in each template of order $k\le K$, imposing allowed pairs with a new endpoint. It does not require missing edges on forbidden pairs to become present.

The padded decomposition property uses
$$
h=2^{50q^3},\qquad d_q=2^{-1000q^5},\qquad
c=\omega^{h^{20}},\qquad K=qh.
$$
For each $m$ it chooses a positive upper density bound and an order threshold before the host. It gives a decomposition for integrally divisible hosts with allowed edges, classes of size at least $n/h$, padded regularity and template extension as above, provided $n^{-d_q}<\omega$ and the upper density bound holds. This is an interface to be proved for a family, not an assumption that all families satisfy it.

The finite component certificates provide a universal absorber and a complete-host inverse. The padded reduction sums the embedding weights over all padded embeddings of a physical triangle, obtaining weights between $\omega^2/n$ and $27/(\omega n)$ with the same edge-load tolerance. Template extension gives guarded supply by taking a template with one new vertex. The forbidden partner condition gives the degree gap. The reserve, correction and cover-down arguments then prove the padded property. These are separate inputs and reductions in the source map of [8, Section 8]; none assumes the decomposition conclusion under another name.

Conversely, the padded property implies (2.7). Given the class lower bound $\gamma n$, take $m=\lceil1/\gamma\rceil$. Distribute each physical triangle weight among its injective padded extensions. For sufficiently large $n$ there are enough unused vertices in every class; the extension counts bound every resulting embedding weight and preserve its total edge load. Sequentially applying the common-neighbour condition gives template extension. Reducing the density and tolerance and enlarging the order threshold, all before the host, therefore gives the padded hypotheses. A decomposition obtained there consists of the original physical triangles. This is the bridge used for the 120 connected cases and the PAR families, with the finite certificates furnishing the family-specific inputs. The complete finite tables remain necessary evidence; a representative example is not a substitute for them.

## Appendix F. A fixed catalogue for the conserved families

Throughout, a cyclic digraph has three vertex classes, and every arc goes from
class i to class i+1 modulo 3. Digraphs have no repeated arcs. The degree d(v)
means **in-degree plus out-degree**. A signed circulation is an integer vector
on the arcs with equal incoming and outgoing sums at every vertex. A positive
piece is a nonempty set of arcs which is balanced in the same sense. It need not
be a single cycle. Its size is its number of arcs.

For a finite catalogue C of pieces, its load at v is

$$
\operatorname{load}_{\mathcal C}(v)=\sum_{P\in\mathcal C}d_P(v).
$$

This counts the entire catalogue, not merely the pieces selected for a
particular residual graph. All reserves and catalogues below are chosen before
the residual L. Only the partition selected from the catalogue depends on L.

### F.1. Integer rounding and a two-sided inverse

Orient the edges of a finite simple graph arbitrarily and let B be its signed
incidence matrix, with a column $e_{v}-e_{u}$ for an edge oriented from u to v.

**Flow rounding.** If Bf is integral, there is an integral vector z with $Bz=Bf$
and $\lfloor f_e\rfloor\le z_e\le\lceil f_e\rceil$ for every edge e. In particular $|z_{e}-f_{e}|<1$.

To see this, consider the edges on which f is not integral. No vertex has exactly
one such incident edge: its incidence equation would have a nonintegral left
side and an integral right side. If any such edge remains, their underlying
graph therefore contains a cycle. Add a signed multiple of its cyclic incidence
vector. This preserves Bf. Increase the multiple until an edge first reaches an
integer endpoint of its allowed interval. No other coordinate leaves its
interval, and at least one nonintegral coordinate disappears. Previously
integral coordinates are not changed. Iteration terminates, proving the claim.

Suppose G satisfies the cut inequality

$$
|\partial_G S|\ge h\min\{|S|,|V(G)\setminus S|\},\qquad h>0.\tag{F.1}
$$

Every zero-sum real vector g with $|g_{v}|\le M$ has a real preimage under B of
supremum norm at most M/h. Indeed,

$$
\left|\sum_{v\in S}g_v\right|\le M\min\{|S|,|V(G)\setminus S|\}\le(M/h)|\partial_G S|.
$$

These cut inequalities imply the flow assertion. For completeness, the image
of the box $[-M/h,M/h]^E$ under B is a compact convex set. If g were outside it,
a separating potential p would satisfy

$$
\langle p,g\rangle>(M/h)\sum_{uv\in E}|p_u-p_v|.
$$

Subtract a constant from p, which does not change the left side, and express p
as a sum of indicators of its nested level sets multiplied by consecutive
level differences. Apply the cut inequality to each term and sum. This gives
the reverse inequality, a contradiction. Integral g can then be rounded as
above without changing its divergence.

**Two-sided inverse.** Let A and B be connected graphs with expansion constants
$h_{A},h_{B}$. If X is an integral matrix with zero row and column sums and
$|X_{ab}|\le M$, then

$$
B_A Z B_B^{\mathsf T}=X,\qquad |Z_{ef}|<\frac{2M}{h_Ah_B}+2.\tag{F.2}
$$

for an integral matrix Z.

First lift each column of X through $B_{A}$, obtaining columns $u_{b}$ bounded by
$M/h_{A}$. Set $s_b=u_b-\operatorname{mean}_{b\prime}u_{b\prime}$. Then $B_{A}$ $s_{b}=X_{b}$, because the rows of X sum
to zero; the rows of the matrix s also sum to zero, and $|s_{eb}|\le 2M/h_{A}$. Lift
each row through $B_{B}$. This gives a real matrix C with

$$
B_A C B_B^{\mathsf T}=X,\qquad |C_{ef}|\le\frac{2M}{h_Ah_B}.\tag{F.3}
$$

There is also an integral preimage $C_{0}$, without a claimed norm bound: express
X as a sum of $X_{ab}(e_a-e_{a_0})(e_b-e_{b_0})^{\mathsf T}$, for fixed roots $a_0,b_0$, and lift the
two differences along paths in A and B.

We round C while preserving its two-sided image. Choose a spanning tree of A.
Let P send an edge vector to the unique vector supported on that tree with the
same incidence. Thus $B_AP=B_A$ and P vanishes on $\ker B_A$. Put

$$
D=C-C_0,\qquad V=PD,\qquad U=D-V.
$$

Then $B_AU=0$. Also $B_A D B_B^{\mathsf T}=0$, so $P(DB_B^{\mathsf T})=0$ and hence $VB_B^{\mathsf T}=0$.
Round every column of U as a zero-divergence flow on A, and every row of V as
a zero-divergence flow on B. The resulting integral $U_{Z},V_{Z}$ retain those
identities and change each entry by less than one. Therefore
$Z=C_{0}+U_{Z}+V_{Z}$ proves (F.2). No bound on P is used. In particular this argument
does not assume that a tensor product of incidence matrices is totally
unimodular.

### F.2. A bounded-degree expander at every size

For each $n\ge 1$ there is a simple graph G on n vertices with maximum degree at
most eight and expansion $h=1/20$. The one-vertex case is immediate. For larger
n, take four independent uniform permutations and form the undirected union
of their permutation edges, discarding loops and repetitions.

Here is the counting argument, including its numerical estimate. Fix a set S
of size $1\le s\le n/2$ and put $r=\lfloor (s-1)/20\rfloor$. A permutation with at most r images
leaving S maps S into $S\cup R$ for some r-set R outside S. Its probability is
at most

$$
\binom nr\binom{s+r}s\big/\binom ns.
$$

Consequently the probability that some s-set is bad for all four permutations
is at most

$$
U_s=\binom ns\left[\binom nr\binom{s+r}s\big/\binom ns\right]^4.
$$

We verify $U_{s}\le 2^{-s}$. Write $A=\binom{n}{r}$, $B=\binom{s+r}{s}$,
$\alpha=s/n$ and $x=(s+r)/n$. Since $B\le A$ and
$B/\binom{n}{s}\le x^{s}$ (compare factors of the two binomial coefficients),

$$
U_s\le A^5x^{3s}.
$$

The elementary estimate $\binom{n}{r}\le (3n/r)^{r}$ for $r\ge 1$ gives
$A^{20}\le (60/\alpha)^{s}$ when $20r\le s$. One way to see the latter implication is to
use the monotonicity of $(60n/t)^{t}$ for $0<t\le n$, at $t=20r$ and $t=s$.
The case $r=0$ gives the same inequality directly. Further,

$$
x^{20}\le(21/20)^{20}\alpha^{20}\le3\alpha^{20}.
$$

Raising the bound for $U_{s}$ to the twentieth power gives

$$
U_s^{20}\le[60^5\cdot27\cdot\alpha^{55}]^s\le(2^{-20})^s,
$$

because $\alpha\le 1/2$ and $60^{5}\cdot 27\le 2^{35}$. Summing $2^{-s}$ over the finite range
$1\le s\le \lfloor n/2\rfloor$ gives a number strictly less than one. Thus one tuple of
permutations works for every such set. For each S, some permutation has at
least $r+1\ge s/20$ outgoing images. These give distinct edges of the simple
boundary, even after repetitions between permutations are discarded. Taking
complements proves (F.1) for every set. Each permutation contributes at most two
incident edges per vertex, giving degree at most eight. The cut inequality
also implies connectedness.

### F.3. A bounded signed filling in the complete cyclic host

Let Q have three classes A,B,C, each indexed by $\mathbb Z/n\mathbb Z$, and all cyclic arcs
between consecutive classes. Fix an orientation of the graph G from Section F.2
on the index set. For indices a,b,c, write

$$
t(a,b,c)=[A_aB_b]+[B_bC_c]+[C_cA_a].
$$

Use the following fixed signed circulations as faces:

1. the $n^{2}$ Latin triangles t(a,b,a+b);
2. for every oriented edge $f\to s$ of G and every a, the two moves

$$
\begin{aligned}m_B(e,a)&=t(a,s,a+f)-t(a,f,a+f),\\m_C(e,a)&=t(a,f-a,s)-t(a,f-a,f);\end{aligned}
$$

3. in each of the three consecutive-class blocks, the rectangles
   $(e_s-e_f)(e_{s\prime}-e_{f\prime})^{\mathsf T}$ indexed by two oriented edges of G.

Each face is nonzero, has coefficients in {-1,0,1}, and has at most four
nonzero arcs. The moves have four, rather than six, arcs because a common
triangle side cancels. The only outgoing-profile change of $m_{B}$ is $e_{s}-e_{f}$
in class B; that of $m_{C}$ is $e_{s}-e_{f}$ in class C. Each rectangle has zero row
and column sums and therefore zero outgoing profile in every class.

There are at most $57n^{2}$ faces: G has at most $4n$ edges, so the three counts
are $n^{2}$, at most $8n^{2}$, and at most $48n^{2}$. For a fixed arc, bounds for the
numbers of incident faces in the four groups (triangles, B-moves, C-moves,
rectangles) are respectively

$$
3,\quad32,\quad32,\quad256.\tag{F.4}
$$

For the moves, choosing which of their two varying endpoints equals a fixed
index reduces the count to incident edges of G, with at most four such choices;
once this edge is fixed the remaining index is determined. For rectangles,
choose one endpoint of each oriented edge, giving the safe bound
$(2\cdot 8)^{2}$. The bound three for the Latin faces is deliberately loose. These
counts remain valid if different indexed faces have the same arc vector.

Let L be any balanced subgraph of Q. Denote its outgoing degrees in the three
classes by $d_{A},d_{B},d_{C}$. Their sums agree and every degree is at most n. Choose

$$
z_{ab}=\begin{cases}1,&\text{if the representative of }b-a\pmod n\text{ is }<d_A(a),\\0,&\text{otherwise.}\end{cases}
$$

The chain sum $z_{ab}$ t(a,b,a+b) has the required A-profile. Its B- and C-profile
errors have sum zero and absolute value at most n. By Section F.1 each error has
an integral flow on G with coefficients of absolute value less than $20n+1$.
Split each coefficient into n integral summands of absolute value at most 21.
Use these summands as coefficients of $m_{B}(e,a)$, respectively $m_{C}(e,a)$.
The two corrections affect only their respective profiles. We obtain a signed
circulation Y with exactly the outgoing profile of L in all three classes.

By (F.4), the absolute face usage on any arc in this construction is at most

$$
3+2\cdot21\cdot32=1347.
$$

The residual $X=1_{L}-Y$ consequently has entries bounded by 1348. All its
outgoing profiles vanish. As it is a circulation, its incoming profiles also
vanish. Each consecutive-class matrix therefore has zero rows and columns.
Apply (F.2) with both expansion constants 1/20 to each of these three matrices.
The rectangle coefficients are integers with absolute value less than

$$
2\cdot1348\cdot20^2+2=1078402,
$$

hence at most 1078401. Combining this with (F.4) gives a signed filling of $1_{L}$
whose total absolute usage on every arc is at most the fixed integer

$$
T=3+2\cdot21\cdot32+1078401\cdot256.\tag{F.5}
$$

The faces and T were fixed before L. The filling coefficients depend on L.

### F.4. Converting signed fillings to a positive catalogue

Fix D subset Q. For each arc $e=u\to v$ of Q, introduce T internally private
positive paths from u to v of length four and T internally private negative
paths from v to u of length five. Distinct paths have distinct internal
vertices and distinct arcs. Their lengths have the appropriate residues
modulo three, so all paths are cyclic. Let R be their union, disjoint from D.

The catalogue consists of three types of positive balanced pieces:

- for every face, either sign, and every choice of a channel on each of its
  nonzero arcs, replace each signed arc by a path in its indicated direction;
- for every arc of Q, the union of any positive and any negative channel;
- for every e in D, e together with the zeroth negative channel for e.

Replacing an integral circulation by directed paths preserves balance.
Every listed piece is nonempty and contains at most 20 arcs. In particular,
the first type is not asserted to be a single directed cycle; balance is the
property used by the subsequent construction.

We prove exact coverage, not just coverage of L. Given balanced L subset D,
take the filling from Section F.3 and expand its coefficients into signed unit
occurrences. At an arc e, let $p_{e},n_{e}$ be their positive and negative counts.
Then

$$
p_e-n_e=\mathbf1_L(e),\qquad p_e+n_e\le T.
$$

For e in L first select the third-type piece using negative channel zero.
Assign distinct positive channels to the $p_{e}$ positive occurrences and distinct
remaining negative channels to the $n_{e}$ negative occurrences. There is enough
space, since $n_{e}+1_{L}(e)=p_{e}\le T$. The unassigned positive and negative channels
both number $T-p_{e}$, so pair them and select the second-type pieces. The
first-type pieces realize the signed face occurrences. Every arc of $R\cup L$
is now used exactly once. Pieces selected this way are distinct, since they
are nonempty and arc-disjoint. Thus they form a subset of the fixed catalogue,
not a multiset requiring extra copies of a physical arc.

The catalogue has size at most $C_{\rm card}n^2$ and vertex load at most $C_{\rm load}n$,
where the frozen constants are

$$
\begin{aligned}C_{\rm card}&=114T^4+9T^2+9,\\C_{\rm load}&=(646T^4+T^2+1)(120T+22),\\C_d&=C_{\rm card}+C_{\rm load}.\end{aligned}\tag{F.6}
$$

For the first estimate there are at most $2\cdot 57n^{2}\cdot T^{4}$ face pieces,
$9n^{2}\cdot T^{2}$ paired-channel pieces, and $9n^{2}$ input pieces. The bounds $9n^{2}$ count
all ordered pairs, so they safely overestimate the arcs of Q.

For the load estimate, a physical arc belongs to at most
$2\cdot 323\cdot T^{4}+T^{2}+1$ catalogue pieces. A base vertex touches at most $6n$ reference
arcs. Counting at most five arcs per channel and allowing one additional
channel token for a private vertex gives at most

$$
2[5(2T\cdot6n+1)+6n]\le(120T+22)n.
$$

incident physical arcs, for $n\ge 1$. Double counting pairs (piece, incident arc)
proves (F.6). These deliberately loose bounds cover both base and private
vertices. An arbitrary cyclic digraph D on N vertices embeds in Q with N
indices per class; padding preserves its original vertices. Formula (F.6) gives
a fixed reserve and catalogue with count $\le C_dN^2$ and load $\le C_dN$.
For $N=0$ use the empty reserve and catalogue. This proves the dense producer
with piece size twenty; it is not an additional hypothesis.

### F.5. Reducing a degree-seventeen input to square-root load

Let Y be cyclic with $d_{Y}(v)\le 17$ and $m=|Y|>0$. Put

$$
s=\lfloor\sqrt{2m}\rfloor+1,\quad M=307+290s,\quad A_0=9\cdot597^2\cdot8.\tag{F.7}
$$

We assign the support of Y to M groups in each colour, each with at most s
vertices, so that distinct arcs of Y have distinct ordered pairs of groups.
Process vertices one at a time. In addition to group capacity, maintain that
vertices at undirected distance at most two receive different group indices.
At a new vertex the forbidden group indices are bounded by:

- $17+17^{2}=306$ from vertices at distance at most two;
- $17^2s=289s$ from existing arcs whose group pair would coincide with an arc
  to a previously processed neighbour;
- at most s-1 full groups, since the processed support has size less than $s^{2}$.

For the second count, a group contains at most s old vertices, each meeting at
most seventeen arcs; there are at most seventeen relevant neighbours. Distinct
new arcs cannot collide with each other, because their old endpoints have
different group indices. Opposite orientations at the new vertex cannot
collide: their endpoint colours differ. Since M is larger than the sum of the
three exclusions, a group is always available. This establishes the claimed
assignment, rather than merely assuming a simple quotient.

Let p(v) be the group of v and let D be the cyclic quotient, with one hub per
group. The map e->(p(tail e),p(head e)) is injective. There are $N=3M$ hubs and
at most $17s$ input arcs incident with any one hub. Since $s^{2}\le 8m$ and $M\le 597s$,

$$
N^2\le A_0m,\qquad(\text{hub incidence})^2\le A_0m.\tag{F.8}
$$

Use Section F.4 on D. For each original arc $e=u\to v$ introduce five private
vertices and the following paths:

$$
\begin{aligned}P_e&:v\to x_0\to u,\\O_e&:u\to x_1\to x_2\to p(u),\\I_e&:p(v)\to x_3\to x_4\to v,\\Q_e&:p(u)\to p(v).\end{aligned}
$$

The colours of p(u),p(v) equal those of u,v. Thus the indicated paths are
cyclic. The base cycle $P_{e}+O_{e}+Q_{e}+I_{e}$ has length nine. The reserve consists
of all these base cycles and the dense reserve on the hubs. Its catalogue
contains the dense catalogue and:

- the triangle $e+P_{e}$, for each e in Y;
- the base cycle of length nine for each e;
- $I_{e}+O_{f}$, a cycle of length six, whenever $head(e)=tail(f)$.

Given balanced L subset Y, select the base cycle for each e outside L and the
triangle for each e in L. At each old vertex pair its incoming L-arcs with
its outgoing L-arcs, and use the corresponding six-cycles. The remaining
arcs are exactly the dense reserve plus Q(L). The latter is balanced, because
the group map preserves sums of divergences, and is a subgraph of D by
injectivity. Section F.4 partitions this remainder. All selections are
arc-disjoint; all pieces belong to the catalogue fixed before L.

There are at most $17m$ compatible ordered pairs (e,f), so the total catalogue
size is at most (19+C_d A_0)m. The following load calculation records the
stronger bound needed later for vertices which will be identified.
At a vertex w let $S_{w}$ be the sum of its degrees in all base nine-cycles.
The triangles contribute at most $S_{w}+d_{Y}(w)$, the base cycles at most $S_{w}$,
and the six-cycles at most $34S_{w}$: an arc can be the first or second member
of at most seventeen pairs. The dense catalogue contributes at most $C_{d}$ N
and does not meet any old vertex. In particular $S_{v}=2d_{Y}(v)$ at an old vertex,
and hence

$$
\operatorname{load}(v)\le73d_Y(v)\quad\text{for every old vertex}.\tag{F.9}
$$

At a general vertex, let ell be its hub incidence if it is a hub, and zero
otherwise. The number of base cycles meeting it is at most 17+ell, giving

$$
\operatorname{load}(w)\le1241+(72+C_d)(\ell+N).
$$

By (F.8), $(\ell+N)^2\le(2A_0)^2m$. Since $m\ge 1$, the frozen constant

$$
C_m=19+C_dA_0+1241+(72+C_d)(2A_0).\tag{F.10}
$$

therefore bounds catalogue size by $C_{m}$ m and gives
$\operatorname{load}(w)^2\le C_m^2m$ at every vertex. Every piece has size at most twenty.
For $m=0$ the empty catalogue satisfies the same assertions. The distinction
between (F.9) and the square-root bound is essential: a square-root bound per
port would be inadequate after many ports are assigned to one physical root.

### F.6. A fixed eight-permutation network at each root

For every finite set P there are eight permutations such that, for every
S subset P, the total number of directed permutation channels leaving S,
counted with their permutation labels, is at least

$$
\min\{|S|,|P\setminus S|\}.\tag{F.11}
$$

Here parallel channels are retained as different channels; this is not the
simple graph used in Section F.2. For $|P|\le 1$ the assertion is immediate. Let
$n=|P|$ and fix S with $1\le s\le n/2$, $p=s/n$. For a uniform permutation let I be the
number of images from S which stay in S. Its factorial moments satisfy

$$
\mathbb E\binom Ik=\frac{\binom sk^2}{\binom nk}\le\binom skp^k.
$$

Thus E $\lambda^{I}$ $\le (1+p(\lambda-1))^{s}$ for $\lambda\ge 1$. If eight independent
permutations have fewer than s outgoing channels, their total internal count
exceeds $7s$. Markov's inequality with $\lambda=4/p$, followed by
$\binom{n}{s}\le (3/p)^{s}$, bounds the probability of a bad s-set by

$$
\left[3(5-p)^8p^6/4^7\right]^s\le2^{-s}.
$$

For the last inequality, $p^{3}(5-p)^{4}$ is increasing for $0<p\le 1/2$ and is less
than 52 there, while $3\cdot 52^{2}<4^{7}/2$. The sum over s is strictly less than one.
Some tuple therefore works for all small sets. The outgoing count across a
cut equals that across its complement for each permutation, proving (F.11).

Discard fixed points and regard each remaining channel as having unit
capacity. The in-degree and out-degree are each at most eight. If integers
$b_{p}$ satisfy $|b_{p}|\le 1$ and sum $b_{p}=0$, then

$$
\left|\sum_{p\in S}b_p\right|\le\min\{|S|,|P\setminus S|\}.
$$

By (F.11) all directed cut conditions for routing this imbalance hold. An
integral unit-capacity flow therefore selects channels with the required
divergence. This last assertion also follows directly by adjoining a source
and sink for the positive and negative demands and augmenting along residual
paths: if augmentation stops before all demand is routed, the source-reachable
set violates precisely one of these cut inequalities. Integral capacities
keep every selected channel at value zero or one. The network works for all
such b; it is not chosen after b is known.

### F.7. Root ports and the completed catalogue

Let X be an arbitrary cyclic digraph and put $x=|X|$. Split each input arc into
two distinct ports, one assigned to its tail root and one to its head root.
The lifted input is a matching on $2x$ ports. A port retains the colour of its
root. For each root apply Section F.6 to its set of ports. Replace every selected
network channel by a private path of length three, whose endpoints are its
ports. The endpoints have the same colour, so this path is cyclic. Let N be
the union of all network paths and I the lifted input.

Every port has network total degree at most sixteen, every network internal
vertex has degree two, and the lifted matching adds at most one. Hence

$$
\max_v d_{N\cup I}(v)\le17,\qquad |N\cup I|\le49x.\tag{F.12}
$$

Indeed there are at most eight channels per port, each with three arcs, so
$|N|\le 24\cdot (2x)$. The networks are fixed for X. If L subset X is balanced, its
lift has divergence in {-1,0,1} at every port and the sum of divergences in
each root fibre is zero. Section F.6 selects whole channels whose paths A
cancel these divergences. Thus A union I(L) is balanced, with A subset N.

Apply Section F.5 once to $Y=N\cup I$, producing a reserve R disjoint from Y
and its fixed catalogue. Enlarge this catalogue by every individual channel
path of N. Given L, first use the mesoscopic partition for A union I(L).
Then add the individual channel paths not selected in A. This partitions

$$
R\cup N\cup I(L).\tag{F.13}
$$

exactly, using a subset of the enlarged fixed catalogue.

An individual added channel path is not balanced on the split port set. Its
two endpoints belong to the same root. After identification with that root,
its incoming and outgoing contributions cancel. All other pieces were already
balanced. The physical embedding must preserve distinct arcs; that separate
step in Section 8 of this article is not replaced by an arbitrary quotient
of the abstract graph. Under an arc-injective realization, balance descends
by summing divergences over fibres, and the partitions in (F.13) descend too.

There are at most $16x$ extra channel pieces. Their load at an old vertex is
at most its network degree, since the paths have disjoint arcs. Equations
(F.9) and (F.12) therefore give the uniform old-vertex bound

$$
\operatorname{load}(v)\le73\cdot17+16=1257.\tag{F.14}
$$

For a genuinely new mesoscopic vertex u there are no extra channel pieces,
so $load(u)^{2}\le C_{m}^{2}\cdot 49x$. The remaining bounds are

$$
\begin{aligned}|\mathcal C|&\le(49C_m+16)x,\\\sum_{P\in\mathcal C}|P|&\le(980C_m+48)x.\end{aligned}\tag{F.15}
$$

and every piece has at most twenty arcs. The second bound keeps the sizes
twenty and three separate; replacing both by twenty is unnecessary.

There are exactly $d_{X}(r)$ ports assigned to a physical root r. The total
catalogue precharge carried by those ports is therefore at most

$$
1257d_X(r).\tag{F.16}
$$

not 1257 times the total number of input arcs. Network internal vertices are
not pinned to r. This is the root budget used by the weighted physical
embedding. Taking L empty in (F.13) also proves that the support of the catalogue
contains R union N, which is needed when its arc weights are defined.

Equations (F.12)--(F.16) complete the abstract catalogue construction. Together
with an arc-injective physical realization and the terminal absorber proved
in Appendix A, they supply the missing abstract input
to the conserved-family construction. This statement concerns that input; the separate PAR/BAL and semidense proofs are given in Appendices E and C, respectively.

### F.8. Why the pieces meet the terminal divisibility conditions

For the three-colour core the only triangle type is 012. At a vertex of colour
i in a balanced cyclic piece P, the numbers of neighbours of colours i-1 and
i+1 agree: they are its incoming and outgoing degrees. Its local profile is
therefore an integral multiple of the corner profile of 012. Summing balance
over each colour class also shows that the numbers of arcs in the three
consecutive-class blocks agree. The global edge-count vector is consequently
an integral multiple of (1,1,1). Thus P satisfies both integer divisibility
conditions; total edge-count divisibility alone is not the argument.

After the physical replacement in this article, the same reasoning applies
because every piece is balanced and cyclic, including the extra channels
whose ends were identified with their common root. Each piece has at most
eighty physical edges. The bounded integer-certificate result in Appendix A may therefore be used with the single size bound eighty. Its
certificate is constructed in the complete allowed host; one must not assert
that all of its auxiliary triangles already lie in the incomplete host.
Instead the terminal gadget is embedded using extension. Its graph has no
edge between two old roots, and its construction orders the new vertices
with at most four previously exposed neighbours, as proved in Appendix A.
The supply and avoidance inequalities there are the conditions used for this
embedding.

Finally, apply the fixed-catalogue assembly lemma to the physical catalogue.
Its count and whole-catalogue load, rather than the load of any particular
residual selection, are the inputs to that lemma. The terminal gadgets and
their physical embeddings are fixed for all pieces before L is selected.
The partition for L then chooses one of the two decompositions of each
already embedded gadget. This explains precisely where (F.15), (F.16) and the
physical load estimate enter; it does not introduce a new absorber depending
on L. The quantitative choice of the host scales remains the one in the
frozen producer and the physical realization lemma of Section 8.

## Appendix G. Auxiliary statements and their uses

The proofs above use the following auxiliary results. We state the contracts needed by the applications, so that their hypotheses can be checked separately from the construction of the typed absorber. These quantitative versions are results of the accompanying development [8], not quotations of an unspecified general decomposition theorem. The companion's Section 8 gives exact declarations and source locations. Appendix H gives mathematical proofs of the compatible library, robust slots, ordinary refiner, packing and reserve-selection results, including their numerical bounds. The reductions for cover-down and weighted paths are proved below.

### G.1. Anti-edges

An anti-edge for distinct roots $u,v$ and completing label $k$ is a two-edge path $uwv$, where $p(w)=k$. The edge $uv$ need not be present. A graph is *$\alpha$-anti-edgeful for $F$* if, for every ordered presentation $\{i,j,k\}\in F$ and every pair of distinct vertices $u\in V_i$, $v\in V_j$, there are at least $\alpha n$ such vertices $w$. This is a typed common-neighbour condition, not a statement that $uv$ is a missing edge. Guarded supply of order at least two implies it by taking the two roots as the prescribed neighbours. In the semidense application only the completing labels of $F_0$ are requested; arbitrary internal common-neighbour queries are not required.

### G.2. Packing and selection of a decomposable reserve

The method is the classical nibble [16–18]; the global fractional-to-integral comparison [19] and weighted matching result [20] provide related context. The particular local remainder bound and explicit constants below are proved in H.7–H.8, rather than inferred from those references without checking their hypotheses.

**Auxiliary packing statement.** For $b>0$ and $0<\eta\le1$ there are a positive tolerance $\tau(\eta)$ and an integer threshold $N_{\rm pack}(b,\eta)$. For $\xi>0$, put $\zeta=\min\{\eta,1,\xi^2\}$. If $n\ge N_{\rm pack}(b,\zeta)$, $\Delta(J)\le(1-\xi)n$, and the allowed triangles of $J$ have weights in $[0,b/n]$ whose load on every edge differs from one by at most $\tau(\zeta)$, then $J$ has a packing of allowed triangles leaving maximum degree at most $\eta n$. With exact unit loads there is also a packing statement without the degree-gap hypothesis, with a threshold depending only on $b,\eta$.

These functions are chosen uniformly before the label set, host and weights. The implementation of the near-load statement permits
$$
N_{\rm pack}(b,\zeta)\le
\left\lceil2^{6500}(b+1)^{40}\zeta^{-4000}\right\rceil
\quad(0<\zeta\le1).
$$
The particular tolerance and threshold used in B.6 are those of this statement. Section H.8 specifies the tolerance and proves positivity and the displayed upper bound. No assertion about the integral lattice follows from the weights alone.

**Auxiliary reserve statement.** Suppose there are at most four labels, $0<\rho,\omega\le1$, $G$ is $\omega$-anti-edgeful and $Q\subseteq E(G)$ is the edge set of an allowed triangle packing with $\Delta(E(G)\setminus Q)\le\omega n/8$. If
$$
n\ge2^{27}\rho^{-9}\omega^{-6},
$$
there is a decomposable reserve $X\subseteq E(G)$ with $\Delta(X)\le2\rho n$, and the graph on $X$ is $(\rho^2\omega/12)$-anti-edgeful. The selection takes whole triangles of the supplied decomposition. Applying the near-load packing statement first requires the additional bound $\Delta(G)\le(1-\omega)n$; this is the reason for the check in B.6.

### G.3. Cover-down with an absorber already fixed

**Auxiliary cover-down statement.** Fix $b>0$ and $0<\alpha\le1$. There is a threshold depending only on these parameters. Let $A,X\subseteq E(G)$ be disjoint. Assume that $G$ is integrally $F$-divisible, that $A\cup L$ is decomposable for every integrally divisible $L\subseteq X$, and that the graph on $X$ is $\alpha$-anti-edgeful. If $J=G-(A\cup X)$ has exact unit triangle loads with weights in $[0,b/n]$, then $G$ has an $F$-decomposition above that threshold.

To see the reduction, take a packing in $J$ leaving $\Delta(L_0)\le\eta n$, where $\eta=\alpha^2/256$. Put $r=\lceil\eta n\rceil$, $q=\lfloor\alpha n/16\rfloor$ and $m=|L_0|\le nr/2$. For $n\ge256/\alpha^2$, the bounds $q\ge\alpha n/32$, $q\le\alpha n/16$ and $r\le2\eta n$ give
$$
\frac m q+2(r+2q)<\alpha n.
$$
Cover the edges of $L_0$ successively by triangles whose other two edges lie in $X$. Exclude vertices already used as a new centre $q$ times and exclude previously spent reserve neighbours of the two endpoints. The three terms in the inequality pay for precisely those exclusions. Each uncovered edge has a completing type, because its original unit load was positive. The unused reserve $L\subseteq X$ is integrally divisible: subtract the packing and the new triangles from $E(G)$, and use that $A$ is decomposable (take $L=\varnothing$ in its absorption property). The fixed absorber handles this $L$. It never has to be selected after the packing.

The effective near-load variant in [8] uses $\tau(\min\{\alpha^2/256,1,\alpha^2\})$ and threshold
$$
\max\left\{N_{\rm pack}(b,\min\{\alpha^2/256,1,\alpha^2\}),
\left\lceil256/\alpha^2\right\rceil\right\}.
$$
Exact loads satisfy its tolerance automatically. Its degree gap is derived from the disjoint anti-edgeful reserve, not imposed as a new assumption in the cover-down statement.

### G.4. Ordinary refiners and robust slots

The ordinary-refiner input of B.3 assumes $X$ is loopless, $\Delta(X)\le2\rho n$, and the four scalar inequalities (B.3.1). Its conclusion is a single remainder and a fixed library, with the bounds stated there: piece size 42, remainder degree $4\lambda n$, at most $1224\rho n^2$ indices, and multiplicity load $4096\lambda n$. Every even subgraph of $X$ whose edge count is divisible by three has a selection from that same library. The virtual complete host supplies the paths needed by the heap construction; B.3 subsequently proves that the library can be routed in the actual host. Neither an actual-host embedding nor global typed divisibility is supplied by this ordinary input.

The robust-slot input has a different purpose. For integers $0\le s\le z$, there are $m\le3z$ fixed slots and a bipartite graph from $m+s$ left vertices to $m$ fixed and $z$ flexible right vertices. Its left degrees are at most 24, its right degrees at most 18, and every selection of exactly $s$ flexible slots admits a perfect matching with all left vertices. Section H.5 proves this finite statement by a permutation construction and Hall’s theorem. In B.4 each flexible slot represents a unit of charge, not a host vertex. Together with the two direct token roles it gives the bounds on token multiplicity and new indices used in the layer construction. The factors 9, 44 and 97 refer to those ledger counts, not to degrees of the robust bipartite graph.

### G.5. Weighted path selection

Here is the precise greedy step used in Section 8. Suppose two-neighbour guarded supply for three distinct labels is at least $a$, forbidden edges have maximum degree at most $d\ge0$, and a nonnegative load function has total at most $S$ and pointwise bound $T+2W$, where $T>0$. If
$$
S/T+4+2d<a,
$$
then, for roots of two different labels and $0\le w\le W$, a four-edge path can be chosen with the prescribed third label at its middle. Its three internal vertices are new, it avoids forbidden edges, and charging $2w$ to each of them preserves the pointwise bound and increases total load by $6w$.

Indeed at most $S/T$ vertices have load at least $T$. Choose the first and last internal vertices outside that set, the roots, and forbidden neighbours; choose the middle vertex in the common neighbourhood of the two chosen vertices, in the third label. At each choice there are at most four distinctness exclusions and at most $2d$ forbidden-neighbour exclusions. The displayed strict inequality leaves a choice. Every new internal load is at most $T+2W$. Endpoint charges are assigned separately before this step, as required in Section 8.

\clearpage

## Appendix H. Proofs of the auxiliary constructions

This appendix supplies the auxiliary constructions used in C.5a, G.2 and G.4; the cover-down reduction is given separately in G.3. A library is an indexed family: two indices are retained even if their edge sets agree. Its load is the sum of the degrees over all indices. Every remainder and every library below is fixed before the divisible residue is selected.

### H.1. Parity chains

For bits $x_0,\ldots,x_{N-1}$, put $c_{-1}=0$ and $c_j=c_{j-1}+x_j$ in $\mathbb F_2$. Between consecutive positions put two distinct paths $A_j,B_j$ with common endpoints. Position $j$ receives $B_{j-1}$ when $c_{j-1}=1$; if it is not last, it also receives $A_j$ and receives $B_j$ when $c_j=0$. Every wire path is assigned once. At a nonterminal position the number received has parity
$$
c_{j-1}+1+(1-c_j)=x_j\pmod2.
$$
At the last position the parity is $x_{N-1}+c_{N-1}$. There are at most three paths per position. This includes a chain of length one, which has no wires.

Apply this rule to a link family $\Lambda$ and a map $h$ with no fixed link endpoint. For each vertex $u$, form a chain of its incident links with path endpoints $u,h(u)$. For each nondegenerate projected pair $\sigma=\{h(u),h(v)\}$, form a chain of its preimages, with path endpoints $\sigma$, and two terminal paths $f_\sigma,f'_\sigma$. Paths with the same endpoints remain distinct requests.

For each link, include all sixteen alternatives determined by its selection bit and the three incoming carries. An alternative contains the selected link, the paths received from its two endpoint chains, and those from its projected-pair chain. At the last position of that chain, add $f_\sigma$ if the outgoing carry is one. Include also the piece $f_\sigma\cup f'_\sigma$. Discard alternatives with nonzero boundary modulo two.

For an even selected input, the endpoint chains have zero terminal carry. Their boundaries cancel the input endpoints and leave the projected endpoints; the pair chains cancel these. A degenerate projected pair contributes zero. The projected pairs with odd preimage count form an even next input, because their boundary is the image of the previous zero boundary. If the final pair carry is zero, select $f_\sigma\cup f'_\sigma$; if it is one, $f_\sigma$ is already used and $f'_\sigma$ is the next input link. This proves disjoint coverage from one level to the next. A hierarchy ending with no links therefore refines every even input using one fixed library.

Write $S=\sum_\ell|\Lambda_\ell|$. There are at most $17S$ indices and $8S$ requests: per level, endpoint wires cost at most $4|\Lambda_\ell|$, pair wires $2|\Lambda_\ell|$, and terminals $2|\Lambda_\ell|$. A piece has at most $1+3+3+4=11$ atoms. An atom occurs in at most $33$ pieces, since a wire meets at most two positions with sixteen alternatives each and a terminal may also meet its cycle piece. Realizing each request by its own two-edge path gives
$$
|P_i|\le22,\qquad
\sum_i|P_i|\le66(8S+|X|).
$$
At a root the load is at most $33(d_X+\text{request root load})$; at a fresh middle it is at most $66$. The request root load of one level at $u$ is at most
$$
2d_\Lambda(u)+10\sum_{v:h(v)=u}d_\Lambda(v).
$$
The first term counts its endpoint wires; the second pays for incoming endpoint wires, pair wires and terminals. These estimates count all alternatives.

### H.2. The compressed heap and compatible labels

For C.5a introduce $2M$ hub identities, disjoint from the old vertices, where $M=2^a$. Send old vertex $j$ to hub $M+(j\bmod M)$ and subsequent hubs $i$ to $\lfloor i/2\rfloor$. The positive levels have widths $M,M/2,\ldots,1$; the last has no nondegenerate links. Thus
$$
S\le|X|+2M^2.
$$
An old vertex has request root load at most $2d_X(v)$ and therefore library load at most $99d_X(v)$. A hub receives at most $10(\lfloor n/M\rfloor+1)\Delta_X$ from the first map. At a positive level of width $w$, its own degree is at most $w$ and it has at most two children, giving root load at most $22w$. Summing widths gives the hub library bound
$$
330(\lfloor n/M\rfloor+1)\Delta_X+1452M.
$$

Keep the old labels and give hubs label zero. A request with equally labelled endpoints gets a middle of the opposite label; one with differently labelled endpoints gets a middle of label zero. Every requested triple is therefore in $F_0=\{001,011\}$. These labels are fixed before charge correction.

For a labelled edge set define
$$
\chi(E)=2e_{01}(E)-4e_{00}(E)-4e_{11}(E).
$$
Even degrees imply $4\mid\chi(E)$, since the crossing count is even. An even graph with zero charge is integrally $F_0$-divisible: its global coefficients are $e_{00}$ and $e_{11}$, and its local profiles lie in the lattices generated by $(1,1),(0,2)$ or their reversals. These are precisely the even-sum lattices.

Use a four-cycle with labels $0011$ as a charge $-4$ token, and an eight-cycle with labels $01011001$ as a charge $4$ token. They have respectively two and six crossing edges, and each has two internal edges. Each token has maximum degree two and at most eight edges, on fresh identities.

### H.3. The charge ledger and its counts

For the parity pieces put $c_i=\chi(P_i)/4$, so $|c_i|\le|P_i|$. Every selection for a divisible residue has the same sum $K=\chi(R_{\rm par})/4$. Put
$$
p_i=\max(-c_i,0),\quad m_i=\max(c_i,0),\quad
z=\sum_i(p_i+m_i),\quad s=\sum_i m_i-K.
$$
A positive-demand parent receives $m_i$ variable negative tokens. A negative-demand parent receives $p_i$ private positive tokens, each with a variable negative mate. Include the release piece consisting of each such pair. For a chosen selection, use its parents and the release pieces of unselected negative-demand parents. The remaining negative variable tokens number exactly $s$: they belong to unselected positive parents or are mates of selected negative parents. The empty-residue selection shows $0\le s\le z$.

Use H.5 to fix a graph with $b\le3z$ fixed negative slots, $b+s$ positive slots and $z$ flexible negative slots. Introduce the corresponding buffer tokens and, for each graph edge, a cancellation piece consisting of its two tokens. For any residue, its $s$ remaining variable slots admit a perfect matching with the positive slots and fixed negative slots. Parents, release pieces and matching pieces cover every token once and cover $R_{\rm par}\cup L$. Each selected piece is even and has charge zero. This proves universality.

There are at most $9z$ tokens and, if the old library has $N$ indices, at most
$$
N+z+24(b+s)\le N+97z
$$
new indices. A token occurs at most $1+1+24+18=44$ times, accounting for its parent, release and possible matching roles. Old loads are unchanged; token vertices have load at most $88$. Parent pieces have size at most $9|P_i|$ and cancellation pieces at most $16$. Consequently the uniform size bound is $9\cdot22+16=214$, and
$$
17S+97\cdot66(8S+|X|)
=51233S+6402|X|\le57635(|X|+2M^2).
$$

The same count explains B.4. If a layer has coefficient and finite-order bound $A$, its at most $AN$ empty padding indices contribute demand at most $A^2N$ in addition to the original $AN$. Empty indices have no edge load. Thus the demand is at most $A(A+1)N$, giving $9A(A+1)N$ tokens and
$$
N+AN+97A(A+1)N\le L_jN,\qquad L_j=1+98A(A+1).
$$
The inequality has slack $A^2N$. If the token union has load at most $\Delta$, one layer changes library load $\Lambda$ to at most $\Lambda+44\Delta$. The next inductive bound includes a further $\Delta$, so
$$
L_{\rm next}(\Lambda+45\Delta)
\le45L_jL_{\rm next}(\Lambda+\Delta).
$$
The remaining token count is $9A(A+1)N+T_{\rm next}L_jN$. These are the factors and backward recurrences in B.4; they bound the full library.

### H.4. One physical realization for every residue

Place old vertices first, then hubs, request middles and token vertices in cycle order. Every new identity has at most two earlier neighbours. The closing queries of the two token cycles have labels $(0,1,1)$ and $(0,0,1)$, respectively. The earlier neighbours of each two-root query coappear in a piece, so piecewise injectivity makes their images distinct. All two-root queries are permitted. Positive anti-edgefulness and $n\ge3$ force both labels to occur; adding an opposite-label root also supplies every needed one-root query. The empty query has the same supply bound.

Write $B=214$, let $I$ bound the number of indices and let $\Lambda(v)\le L_{\max}\le q$ be the abstract library load. Charge a physical vertex by $\Lambda(v)$ when placing $v$, and use only vertices whose accumulated load is below $q$. Afterwards their load is at most $2q$. There are at most $2BI/q$ saturated vertices, since the total degree sum is at most $2BI$. At most $2BL_{\max}$ earlier identities coappear with the new identity: each piece has at most $2B$ nonisolated vertices, and the number of pieces containing it is at most its load. Excluding their images preserves injectivity within every piece.

At each of the at most two earlier neighbours, exclude neighbours in the forbidden graph, in $X$, and in the already realized edge union. Their degree bounds are $d,\Delta_X,2q$. Thus the total exclusion is at most
$$
2BL_{\max}+\frac{2BI}{q}+2(d+\Delta_X+2q)<\alpha n.
$$
A candidate remains. This proves the induction, including edge injectivity of the entire support. The single map fixes roots and labels; transporting any abstract selection preserves disjointness, exact coverage and divisibility. H.1–H.4 therefore prove C.5a, including its constants.

### H.5. The robust-slot graph

For $k\ge1$, take $3k$ left vertices and two right sets $Y,Z$ of size $2k$ each. Give a left vertex two ports and a right vertex three ports. For each right set independently choose six uniform permutations of the $6k$ ports and join their owners. Degrees are at most $24$ on the left and $18$ on the right.

A left set of size $a\le k$ has all its $Y$-neighbours in a specified set of size $a$ with probability at most $(a/(2k))^{12a}$. A right set of size $b\le2k$ has all neighbours in a specified left set of size $b$ with probability at most $(b/(3k))^{18b}$. These use sampling without replacement, whose probability is at most the corresponding power. The union bounds are at most $1/15$ each, because $\binom Na\le(3N/a)^a$ gives
$$
\binom{3k}{a}\binom{2k}{a}(a/(2k))^{12a}\le16^{-a},\qquad
\binom{4k}{b}\binom{3k}{b}(b/(3k))^{18b}\le16^{-b}.
$$
Indeed the bases are $(27/2)x^{10}\le1/16$ for $x\le1/2$ and $12y^{16}\le1/16$ for $y\le2/3$. There is therefore a graph in which both neighbourhoods strictly exceed the tested set size.

For any $k$-subset $Z'$ of $Z$, Hall's condition holds between the left side and $Y\cup Z'$. Small left sets use expansion into $Y$. A larger failing set $A$ leaves a right set $B$ of size greater than $3k-|A|$, with neighbours in its complement. If $|B|\le2k$, right expansion is a contradiction; otherwise apply it to a $2k$-subset, whose neighbours would have to fit in fewer than $2k$ left vertices. This proves the perfect matching assertion. For $k=0$ use the empty graph.

For arbitrary $0\le s\le z$, take $k=\max(z-s,s)$, $p=\max(z-2s,0)$ and $b=2k+p$. Keep $z$ flexible positions, make the next $p$ positions fixed and discard any others. The identities $s+p=k$, $b+s=3k$ and $b\le3z$ prove the required contract by extending each chosen $s$-subset with the fixed positions.

### H.6. The ordinary refiner and its constants

Work first on $N$ vertices with local parameters $\lambda,\rho$. Choose a power of two
$$
64\rho N/\lambda\le M\le128\rho N/\lambda.
$$
The assumptions in B.3 give $2\le M$ and $2M\le N$. Enumerate vertices from zero. The first map is $j\mapsto M+((j+1)\bmod M)$; it has no fixed point and fibres of size at most $\lfloor N/M\rfloor+1$. Subsequent maps are heap parents. H.1 gives $S\le|X|+2M^2\le2\rho N^2$. Add at most two disjoint four-cycles to make the remainder's size divisible by three, including them as separate pieces. The even library then has $N_0\le17S+2\le34\rho N^2+2$ indices.

Between consecutive positions of this library put three fresh four-cycles. An alternative $(x,a,b)\in\{0,1\}\times\{0,1,2\}^2$ takes the old piece when $x=1$, cycles numbered at least $a$ on its left wire, and cycles numbered below $b$ on its right wire. Omit end wires and keep alternatives of size divisible by three. Choose the carries as minus the running selected edge count modulo three. Each piece has size congruent to $x|P_i|-a+b=0$; initial and final carries are zero. Each wire cycle is assigned once. Evenness persists and piece size is at most $22+12+8=42$.

Give wire $j$ roots $j\bmod N,(j+1)\bmod N$. Each of its cycles uses two separate path requests. If $D=\lfloor2\rho N\rfloor$, all request roots have load at most
$$
r_0=2D+10(\lfloor N/M\rfloor+1)D+44M+8
+12(\lfloor(N_0+1)/N\rfloor+1).
$$
There are at most $8S+4+6N_0\le512\rho N^2$ requests. The scalar assumptions give
$$
\rho\le\lambda/2^{30},\quad
\lfloor N/M\rfloor D\le\lambda N/32,\quad
44M\le\lambda N/2000,\quad
\lfloor(N_0+1)/N\rfloor\le34\rho N+1.
$$
Hence $r_0\le432\rho N+(5/16+1/2000)\lambda N+32\le\lambda N$, using $\lambda N\ge256$.

Set $q=\lfloor\lambda N/64\rfloor\ge\lambda N/128$. Route requests successively, avoiding middles already used $q$ times and edges in $X$ or previous requests. The exclusions number at most
$$
\frac{512\rho N^2}{q}+2(2\rho N+r_0+2q)
\le\frac{65536\rho N}{\lambda}+4\rho N+\frac{33}{16}\lambda N
<8\lambda N.
$$
Thus common-neighbour supply $8\lambda N$ suffices. The remainder degree is at most $r_0+2q\le4\lambda N$. An old atom occurs at most $18\cdot33$ times; a mod-three wire occurs at most $36$ times. Consequently
$$
\sum_i d_{P_i}(v)\le594d_X(v)+630(r_0+2q)\le4096\lambda N,
\qquad |I|\le18N_0\le1224\rho N^2.
$$
For the subset $W$ in B.3 use $N=|W|$, $\lambda'=\lambda n/N$ and $\rho'=\rho n/N$. Its four scalar hypotheses persist, and the complete host on $W$ supplies $N-2\ge8\lambda n$ common neighbours. Finally $1224\rho'N^2\le1224\rho n^2$, while the degree and load bounds rescale exactly. This proves the stated virtual interface.

### H.7. Progress, conflicts and surviving loads in one packing round

Let the distinct physical candidate triangles of an active edge set $B$ have weights $0\le w_i\le\beta$, with edge loads in $[1-\delta,1+\delta]$. Assume $\delta\le1/4$, $0<\gamma\le1/128$ and $\gamma\beta\le1/4$. Retain triangle $i$ independently with probability $\gamma w_i$, and keep only those sharing no edge with another retained triangle. If $Q$ is the touched edge set, put $B'=B\setminus Q$ and $W=Q\setminus E(\mathcal P)$. Then
$$
B\setminus E(\mathcal P)=B'\mathbin{\dot\cup}W.
$$

We use the following product-space bound. If changing Bernoulli coordinate $i$, of probability $p_i$, changes $f$ by at most $c_i\le L$, either tail at distance $t$ from its mean is at most
$$
\exp\left(-\frac{t^2}{2(V+Lt)}\right),\qquad V=\sum_i p_ic_i^2.
$$
This is a Bernstein-type concentration estimate; see [21, Chapter 2] for the exponential-moment method. For completeness, in the exposure martingale an increment is $(X_i-p_i)d_i$, with $|d_i|\le c_i$. Its conditional variance is at most $p_ic_i^2$ and its higher moments are bounded by $L^{k-2}$ times that variance. Expanding the exponential, multiplying the conditional bounds and applying Markov's inequality gives Bernstein's denominator $2(V+Lt/3)$, and hence the weaker displayed bound. It applies also after fixing a disjoint collection of coordinates.

Fix $v$ and put $d=d_B(v)$. Let $R_v$ count retained triangles through $v$. Summing edge loads gives $\mathbb ER_v\ge3\gamma d/8$, whence
$$
\mathbb P(R_v<\gamma d/4)\le e^{-\gamma d/64}.
$$
For each triangle $U$ outside $v$, let $b_U$ be the total weight of triangles through $v$ sharing an edge with $U$, and set $Y_v=\sum_U b_UX_U$. There are at most three such triangles for each $U$, so $b_U\le3\beta$. Conversely, an outside triangle blocks a triangle through $v$ only on its opposite edge. Exchanging sums gives $\mathbb EY_v\le\gamma(1+\delta)^2d/2\le\gamma d$. Therefore
$$
\mathbb P(Y_v\ge\gamma d+t)
\le\exp\left(-\frac{t^2}{2(3\beta\gamma d+3\beta t)}\right).
$$
Let $Z_v$ count retained triangles through $v$ blocked from outside. Conditional on the outside coins, their blocked mean is at most $\gamma Y_v$. The remaining coins are independent. At exponential parameter $1/2$, the inequality $e^{1/2}-1\le3/4$ gives
$$
\mathbb P(Y_v\le y,\ Z_v\ge z)\le e^{-z/2+3\gamma y/4}.
$$

For $u\ne v$, let $D_u$ count retained triangles containing $vu$ and put $F_v=\sum_u\binom{D_u}{2}$. We have $\mathbb ED_u\le\gamma(1+\delta)\le1/2$, so $\mathbb P(D_u\ge K)\le e^{-K/8}$ for $K\ge1$. Independence gives $\mathbb EF_v\le\gamma^2d$. Truncate to $\widehat F_v=\sum_u\binom{\min(D_u,K)}2$. A through-$v$ coin changes two summands by at most $K$ each; outside coins have no effect. Thus
$$
\mathbb P(\widehat F_v\ge\gamma^2d+t)
\le\exp\left(-\frac{t^2}{2(4K^2\gamma d+2Kt)}\right).
$$
When all $D_u<K$, the truncation equals $F_v$. A discarded retained triangle through $v$ is either outside-blocked or belongs to an inside conflict, giving the deterministic inequalities
$$
R_v\le d_{\mathcal P}(v)/2+Z_v+2F_v,\qquad
d_W(v)\le2Z_v+4F_v.
$$
For $d\ge\theta n$, use the thresholds $\gamma d/4,d/32,\gamma d/16,\gamma d/16$ for $R_v,Y_v,Z_v,\widehat F_v$. For waste use $2\gamma n,4\gamma^2n,4\gamma^2n$ for the last three variables. The respective choices of deviation in the $Y$ and $\widehat F$ bounds are $d/64,\gamma d/24,\gamma n,2\gamma^2n$. Outside the resulting bad events,
$$
d_{\mathcal P}(v)\ge\gamma d/8\quad(d\ge\theta n),\qquad
d_W(v)\le24\gamma^2n.
$$
Their failure probability per vertex is at most the sum of the following eight quantities:
$$
\begin{gathered}
e^{-\gamma\theta n/64},\quad
e^{-\theta n/[24576\beta(\gamma+1/64)]},\quad
e^{-\gamma\theta n/128},\quad
e^{-\gamma\theta n/(4608K^2+96K)},\\
e^{-\gamma n/(12\beta)},\quad e^{-\gamma^2n/2},\quad
e^{-\gamma^3n/(2K^2+2K\gamma)},\quad ne^{-K/8}.
\end{gathered}
$$
For example, the blocked-triangle exponent is $-\gamma d/32+3\gamma d/128=-\gamma d/128$. Substituting $t=\gamma d/24$ in the truncated-conflict bound gives the denominator $4608K^2+96K$. The other terms follow by the displayed substitutions.

For an edge $e$, condition only on its being untouched. All coins through $e$ are then zero and the others retain their product law. For a triangle $i$ through $e$, the sum of the weights of outside competitors is the sum of the loads of its other two edges minus $2w_i$, and hence lies in $[2(1-\delta-\beta),2(1+\delta)]$. Using $e^{-x-2x^2}\le1-x\le e^{-x}$ for $0\le x\le1/4$, its survival probability lies between
$$
e^{-2\gamma(1+\delta)-5\gamma^2\beta}
\quad\text{and}\quad e^{-2\gamma(1-\delta-\beta)}.
$$
If $f_e$ is the surviving load, summing these bounds and using $e^x\le1+2x$ for $0\le x\le1$ yields
$$
|e^{2\gamma}\mathbb E(f_e\mid e\text{ untouched})-1|
\le(1+5\gamma)\delta+5\gamma\beta.
$$
One outside coin changes $f_e$ by at most $3\beta$. Exchanging sums of its influence against retention probability gives at most $2\gamma(1+\delta)^2$, and therefore a variance proxy at most $10\beta\gamma$. Since $e^{2\gamma}\le2$, an additional error greater than $\varepsilon$ has conditional probability at most
$$
2\exp\left(-\frac{(\varepsilon/2)^2}
{2(10\beta\gamma+3\beta\varepsilon/2)}\right).
$$
Multiplication by the probability that $e$ is untouched only decreases this bound. Union-bound the eight vertex estimates over $n$ vertices and this estimate over at most $n^2$ edges. This proves all three round conclusions simultaneously; no conditioning on the vertex-good events has been used.

### H.8. Iteration and the explicit threshold

Set
$$
\begin{gathered}
\zeta=\min\{\eta,1,\xi^2\},\quad \gamma=\zeta^2/2^{16},\quad
r=\left\lceil8\log(2/\zeta)/\gamma\right\rceil,\\
a=1+5\gamma,\quad c=(8ra^r)^{-1},\quad
\theta=\zeta/2,\quad\varepsilon=c/2,\quad B_{\max}=be^{2\gamma r}.
\end{gathered}
$$
Choose $\tau(\zeta)=c$. The inequalities $\log(2/\zeta)\le2/\zeta$ and $\gamma r\le8\log(2/\zeta)+\gamma$ give
$$
\begin{gathered}
r<2^{21}\zeta^{-3},\quad a^r\le2^{41}\zeta^{-40},\quad
c\ge\zeta^{43}/2^{65},\quad B_{\max}\le2^{17}(b+1)\zeta^{-16},\\
(1-\gamma/8)^r\le\zeta/2,\qquad24r\gamma^2\le\zeta/4.
\end{gathered}
$$
For the last estimate, $24r\gamma^2\le192\gamma\log(2/\zeta)+24\gamma^2\le384\zeta/2^{16}+24\zeta^4/2^{32}<\zeta/4$.

Take $K=\lfloor\sqrt{\lfloor\sqrt n\rfloor}\rfloor$ and $\beta\le B_{\max}/n$. Then $K^4\le n<16K^4$. With
$$
\kappa=\frac{\zeta^{102}}{2^{160}(b+1)},
$$
each exponential in H.7 is at most $e^{-\kappa K}$. For the edge estimate, $\varepsilon\ge\zeta^{43}/2^{66}$ and $8(10B_{\max}\gamma+3B_{\max}\varepsilon/2)\le128B_{\max}$ give rate at least $\zeta^{102}/[2^{156}(b+1)]$. For the other terms use the displayed bounds and $4608K^2+96K\le4704K^2$, $2K^2+2K\gamma\le4K^2$. The union bound is at most $2560K^8e^{-\kappa K}$.

Since $e^{\kappa K}>(\kappa K)^9/9!$, this is less than one if $K>2560\cdot9!/\kappa^9$. It suffices that
$$
n\ge\left\lceil2^{6500}(b+1)^{40}\zeta^{-4000}\right\rceil.
$$
Indeed $K>n^{1/4}/2$, the latter lower bound is at least $2^{1624}(b+1)^{10}\zeta^{-1000}$, and the required right side is less than $2^{1470}(b+1)^9\zeta^{-918}$. This threshold also gives $\gamma B_{\max}/n\le1/4$ and $5\gamma B_{\max}/n\le c/2$.

For exact initial loads start at time zero. At time $j$ multiply base weights by $e^{2\gamma j}$ on surviving triangles. Keep the active set $B_j$ and all discarded touched edges $W_j$. Inductively the packing avoids both, every uncovered edge belongs to their union, and
$$
\begin{gathered}
\Delta(W_j)\le24\gamma^2nj,\qquad
d_{B_j}(v)\le\max\{\theta n,(1-\gamma/8)^jn\},\\
|\operatorname{load}_j(e)-1|\le cja^j.
\end{gathered}
$$
For near-unit initial loads, instead use base weights $e^{-2\gamma}w$ and start at time one with no packing. The actual weights then equal $w$. The degree gap gives $(1-\xi)n\le(1-\gamma/8)n$, and the initial error $c$ is at most $ca$. At every subsequent step $cja^j\le cra^r=1/8$ and the weight bound is $B_{\max}/n$. H.7 increases the error to at most $a(cja^j)+c\le c(j+1)a^{j+1}$, the waste degree by at most $24\gamma^2n$, and decreases each large active star by its $\gamma/8$ fraction. Small stars only decrease. The disjoint residual identity preserves the packing invariant. At time $r$, the uncovered maximum degree is at most $\zeta n/2+\zeta n/4\le\eta n$. This proves G.2, including the separate exact-load version, obtained with $\zeta=\min\{\eta,1\}$ and time zero.

### H.9. Selecting whole triangles for the reserve

Select each triangle of the supplied packing independently with probability $\rho$. At a vertex there are at most $n/2$ blocks, so the selected degree exceeds $2\rho n$ with probability at most $e^{-\rho n/8}$. For a permitted two-root query, at least $3\omega n/4$ witnesses have both edges covered by the packing: each uncovered star removes at most $\omega n/8$. A witness survives with probability $\rho$ or $\rho^2$, according as its edges belong to one or two blocks.

A block influences at most two witnesses. If its influence is $c_i$, then $c_i\le2$, $\sum_i c_i\le2n$ and $\sum_i c_i^2\le4n$. The exposure variance proxy is at most $4\rho n$. Bernstein's bound with $t=\rho^2\omega n/2$ shows that fewer than $\rho^2\omega n/4$ surviving witnesses has probability at most $e^{-\rho^3\omega^2n/48}$. This accounts for shared-block dependence explicitly.

There are at most $4n^2$ queries and $n$ degree conditions. Put $c_0=\rho^3\omega^2/48$. The failure bound is at most $5n^2e^{-c_0n}$. If $n\ge2^{27}\rho^{-9}\omega^{-6}$, then $c_0^3n>30$, and $e^{c_0n}>(c_0n)^3/6$ makes this bound less than one. The selected graph is decomposable and has the required degree bound; its query supply is even stronger than $\rho^2\omega n/12$. Together with the explicit reductions in G.3 and G.5, this completes the auxiliary proofs.

Copyright © 2026 Juan Pablo Traverso Gianini. This document is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

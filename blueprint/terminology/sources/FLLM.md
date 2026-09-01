# FLLM — terminology record

**Paper.** Antongiulio Fornasiero, Noa Lavi, Sonia L'Innocente, Vincenzo Mantova, *Irreducibility in generalized power series* (title as rendered in the transcription; see the note on the title below), arXiv:2405.13815v1 [math.AC], 22 May 2024; dated "27th November 2023" in the front matter.

**Source used.** The 549-line Markdown transcription at
`blueprint/references/fornasiero_lavi_linnocente_mantova_2024_irreducibility.md`. No PDF or TeX
source was available for this audit, so the record was not checked against the published rendering.
Doubtful readings are flagged “(unverified)” or discussed in Part G.

**Locations.** Each entry gives the section / numbered result, the page of the arXiv v1 (inferred from the transcription's `<!-- page N -->` markers; text before the first marker is page 1), and the line number(s) in the transcription file, written `L123`. Line numbers refer to the transcription file and are the most checkable pointer we have. Page map: p.1 = L1–L27; p.2 = L31–L73; p.3 = L77–L116; p.4 = L120–L157; p.5 = L161–L203; p.6 = L207–L239; p.7 = L243–L272; p.8 = L276–L316; p.9 = L320–L359; p.10 = L363–L397; p.11 = L401–L437; p.12 = L441–L473; p.13 = L477–L523; p.14 = L527–L549.

**Read in full.** Abstract; §1 Introduction; §2 Preliminaries; §3 Hereditary rv_J; §4 Irreducible principal elements (§4.1 The successor case, §4.2 The case ω^{α1}+ω^{α2}, §4.3 The case ω^{α1}+ω^{α2}+ω^{α3}); References; addresses. The paper has no appendix and no index of notation.

**Note on the title.** The transcription's title line reads `IRREDUCIBILITY IN GENERALIZED POWER SERIES` (L1) with the American spelling, whereas the authors' own prose in the body uses "generalised" (British): L21 "Call **generalised power series**", L179 "'generalised coefficients'"; the abstract (L7) has "generalized power series". Counts in the whole file: "generalised" 3 (two in prose, one in the [LM24] reference title), "generalized" 4 (title, abstract, and the [Ber00], [Pit01], [PS06] reference titles). The spelling of the published title could not be verified. Also, the transcription has "generalization of randomness" (L77) and "Factorization" only inside reference titles; the paper's own prose has no other -ize/-ise words to decide the matter.

**Organisation.**
- Part A — What it defines (own terms, notation, conventions), in order of first appearance.
- Part B — What it reuses (attributed borrowings, with the attribution quoted).
- Part C — What it assumes you have read (field background used without definition or citation).
- Part D — Generic machinery presupposed (standard mathematics outside the field).
- Part E — How it talks: verbs, phrasing templates, proof idiom, with model sentences.
- Part F — Passages where the paper disagrees with, corrects, or departs from another paper's usage.
- Part G — Transcription issues, apparent typos, and readings that could not be verified.

Entry format: **Term / symbol** — kind — location — verbatim defining text — notes (variants, counts, conventions). Counts are of occurrences in the transcription file, by `grep -o`, and are approximate where a string has more than one meaning.

---

## Part A — What it defines

Each entry below is something the paper itself introduces (by a "Definition", by "we define", "we let", "let ... denote", "call", "we say", or by fixing a notation in passing). Where a definition is explicitly attributed to another paper the entry is in Part B instead, with a cross-reference here when the paper also changes something.

### A.1 generalised power series; exponents; coefficients; support

- Kind: own definition (in-line, bold), §1, p.1, L21.
- Verbatim: "Call **generalised power series** a formal sum $b = \sum_\gamma b_\gamma t^\gamma$ where the **exponents** $\gamma$ vary in an ordered abelian group $G$, the **coefficients** $b_\gamma$ are taken from some field $K$, and its **support** $\{\gamma \in G : b_\gamma \neq 0\}$ is well-ordered, namely every nonempty subset has a minimum."
- Notes / conventions:
  - Series are written with the formal variable $t$ and the exponent as a superscript: $t^\gamma$, $t^{x}$, $t^{-\frac{1}{n}}$. The letter $t$ is never defined separately; it is fixed by this sentence.
  - The series is named $b$ (not $f$, $x$, $a$); the coefficient of $t^\gamma$ in $b$ is $b_\gamma$ (subscript = exponent). This "coefficient as subscripted exponent" convention is used throughout: $b_x$ (Def 2.4, L144: "$b = \sum_\beta b_x t^x$"), $b_{i\gamma}$ for the coefficient of $t^\gamma$ in $b_i$ (L256, L260), $\varepsilon_{1\gamma_0}$ (L397), $u_{j\gamma_i}$ (L262).
  - Well-ordered is glossed as "every nonempty subset has a minimum". Spelled "well-ordered" (L7, L21) and once "well ordered" (L215, "all well ordered subsets of $\mathbb{R}$ are countable").
  - The word for the object is overwhelmingly "series" (47 occurrences), sometimes "power series" (8, e.g. L27 "a power series $b \in K((\mathbb{R}^{\leq 0}))$"), "generalised/generalized power series" only in title, abstract, L21. Plural "series" unchanged. Never "Hahn series", never "transseries". "element(s)" is used when the ring-theoretic role is foregrounded (see A.40).
  - Support is written $\mathrm{supp}(b)$ throughout (41 occurrences of `\mathrm{supp}`); its topological closure is $\mathrm{cl}(\mathrm{supp}(b))$ (15 occurrences of `\mathrm{cl}`). "Support" in prose: "the supremum of the support of $b$" (L37), "series with finite support" (L233), "the supports are pairwise disjoint" (L268), "the closure of the supports are disjoint" (L282).
  - Set difference is written both as "$\setminus$" and as "$-$": "$\mathrm{cl}(\mathrm{supp}(b)) - \{0\}$" (L51, L171, L173, L175, L255), versus "$K((\mathbb{R}^{\leq 0})) \setminus J$" (L31, L151), "$\mathrm{Res}(b) \setminus \mathrm{Big}^{\omega^{\alpha_2}}(r)$" (L371) vs "$(\mathrm{Res}(b) - \mathrm{Big}^{\deg_J^r(b)}(r))$" (L467, L507). Both forms occur; the "$- \{0\}$" form is systematic for removing $0$ from a closed support.

### A.2 $K((G))$ — the field of generalised power series

- Kind: notation fixed in passing; §1, p.1, L21 (and abstract L7).
- Verbatim (L21): "It is well known that the collection $K((G))$ of such series forms a field, when equipped with the obvious operations of sum and product [Hah07]."
- Verbatim (abstract, L7): "A classical tool in the study of real closed fields are the fields $K((G))$ of generalized power series (i.e., formal sums with well-ordered support) with coefficients in a field $K$ of characteristic 0 and exponents in an ordered abelian group $G$."
- Conventions:
  - Double-parenthesis notation $K((G))$, $K((\mathbb{R}))$, $K((\mathbb{R}^{\leq 0}))$, $K((G^{\leq 0}))$, $K((G^{<0}))$, $\mathbb{R}((G))$, $\mathbb{R}((G^{<0}))$.
  - Characteristic 0 is stated in the abstract only ("a field $K$ of characteristic 0"); the body never restates it, and Definition 1.3 / Prop 3.4 use $\mathbb{Q}$-linear and algebraic independence "over $\mathbb{Q}$", which presupposes $\mathbb{Q} \subseteq K$.
  - $K$ is "some field" (L21), "a field $K$" (L7). $K$ is never given further adjectives (not "real closed", not "ordered") in the body.
  - Attribution of the field structure: "[Hah07]" — the only place Hahn is cited; "It is well known that".

### A.3 The rings $K((G^{\leq 0}))$, $Z + K((G^{<0}))$, $\mathbb{Z} + \mathbb{R}((G^{<0}))$, and the working ring $K((\mathbb{R}^{\leq 0}))$

- Kind: notation fixed in passing; §1, p.1, L23–L25.
- Verbatim (L23): "We are interested in the irreducible series in the subrings of the form $K((G^{\leq 0}))$ or $Z + K((G^{<0}))$. Such rings appear in different contexts; for instance, $\mathbb{Z} + \mathbb{R}((G^{<0}))$ is always an integer part of the field $\mathbb{R}((G))$, which in turn implies that every real closed field admits an integer part [MR93]. Regarding irreducibility, the first question was posed by Conway [Con76], who conjectured that the series $1 + \sum_n t^{-\frac{1}{n}}$ is irreducible in the ring of omnific integers, which can be written in the form $\mathbb{Z} + \mathbb{R}((G^{<0}))$ (modulo some set-theoretic details which are irrelevant here)."
- Verbatim (L25): "Conway's conjecture was proved by Berarducci [Ber00]. A crucial part of the argument, first suggested by Gonshor [Gon86], is the reduction to the ring $K((\mathbb{R}^{\leq 0}))$. In this paper, we work exclusively in this ring. We refer the reader to [BKK06, LM24] for extensive considerations on how to use irreducibility in $K((\mathbb{R}^{\leq 0}))$ in order to find irreducibles in rings of the form $Z + K((G^{<0}))$."
- Conventions:
  - Superscript order-restriction notation on the exponent group: $G^{\leq 0}$, $G^{<0}$, $\mathbb{R}^{\leq 0}$, $\mathbb{R}^{<0}$. Also $\mathbb{R}^{\leq}$ with no "0" in $K[\mathbb{R}^{\leq}]$ (see A.36).
  - The ring $K((\mathbb{R}^{\leq 0}))$ is the ambient ring for the whole paper (30 occurrences of `\mathbb{R}^{\leq 0}`). It is never given a short name (no "$\mathbb{K}$", no "$R$", no "$\mathcal{R}$"): it is always written out in full, or referred to as "this ring".
  - "$Z + K((G^{<0}))$" with an unadorned $Z$ at L23 and L25, versus blackboard $\mathbb{Z} + \mathbb{R}((G^{<0}))$ twice at L23. The $Z$ may be a deliberately generic subring $Z \subseteq K$ (as in the [BKK06]-style general integer-part constructions), or a transcription loss of blackboard bold. (unverified)
  - "subrings" (L23) is the noun; "ring" elsewhere ("the ring of omnific integers", "the ring $K((\mathbb{R}^{\leq 0}))$", "in this ring").
  - "integer part", "omnific integers", "real closed field" are used without definition (Part C).

### A.4 order type, $\mathrm{ot}(b)$

- Kind: own definition (in-line, bold); §1, p.1, L27.
- Verbatim: "Let the **order type** $\mathrm{ot}(b)$ of a power series $b \in K((\mathbb{R}^{\leq 0}))$ be the ordinal number representing the order type of its support."
- Notes:
  - Symbol $\mathrm{ot}(\cdot)$ (upright), 32 occurrences; applied to series ($\mathrm{ot}(b)$, $\mathrm{ot}(bc)$, $\mathrm{ot}(r)$) and directly to sets of reals ($\mathrm{ot}(T)$ L140, $\mathrm{ot}(\Gamma)$ L355, $\mathrm{ot}(\mathrm{Res}(b))$ L371, $\mathrm{ot}(\mathrm{supp}(c) \cap [\gamma_i, \gamma_{i+1}))$ L365).
  - One occurrence as plain italic "$ot(r)$" in Conjecture 1.9 (L81): "$ot(r) < \omega^{\deg(b)}$" — a typesetting inconsistency, not a distinct symbol.
  - Prose forms: "has order type $\omega^{\omega^\alpha}$" (L31), "of order type $\omega$" (L33), "admits irreducibles of order type $\alpha$" (L7), "for a wide class of order types" (L35), "of order types $\omega^2$ and $\omega^3$" (L33, L69), "their order types are respectively $2$ and $\omega + 1$" (L39), "a set of order type $\mathrm{ot}(T) = \omega^2$" (L140), "has order type $\omega^{\omega^{\alpha_2}}$" (L371), "$\Gamma$ has order type $\omega^{\alpha_{n+1}}$" (L457), "its order type is $\omega^2$" (L195).
  - "ordinal number" (L27, L89 "the class $\mathbf{On}$ of ordinal numbers") and "ordinal" (passim) both used.

### A.5 $J$ — the ideal generated by $t^\gamma$, $\gamma<0$

- Kind: own notation (defined twice, §1 and §2).
- Verbatim (§1, p.1, L27): "Let $J$ be the ideal of the series that are divisible by $t^\gamma$ for some $\gamma \in \mathbb{R}^{<0}$ (such series cannot be factored into irreducibles, since $t^\gamma = t^{\frac{\gamma}{2}} t^{\frac{\gamma}{2}} = \ldots$)."
- Verbatim (§2, p.4, L120): "Let $J$ be the (proper) ideal of $K((\mathbb{R}^{\leq 0}))$ generated by the series of the form $t^x$ for $x < 0$."
- Notes:
  - Letter $J$ with no decoration. The quotient $K((\mathbb{R}^{\leq 0}))/J$ is never named; instead the paper writes "$\equiv \ldots \mod J$", "$= \ldots \mod J$", "$b \in J$", "$\notin J$", and "$J + K$" (the ideal plus constants, 7 occurrences: "$b \in (J + K) \setminus J$" L122, "$c \equiv b \mod J + K$" L122, "$a \in J + K$" L249, "$p_i^{|\gamma} \notin J + K$" L341, "$p$ and $q$ are not in $J + K$" L455, "$p^{|\gamma}$ is not $J + K$" L459).
  - Equivalence modulo $J$ written both "$\equiv \ldots \mod J$" (L122, L183) and "$= \ldots \mod J$" (L249 "$ac = d \mod J$", L397 "$\varepsilon_i^{|\gamma_0} = \mu_i \mod J$"). The "$=$ ... mod" form dominates in §4 (see A.35).
  - Variable for exponents: $\gamma$ in §1 ($t^\gamma$), $x$ in §2 ($t^x$). Greek $\gamma, \delta, \varepsilon, \epsilon$ are reals in §§2–4, $x_i$ in normal form (Def 2.1). $\alpha, \beta$ are reserved for ordinals except in Def 2.4's "$\sum_\beta b_x t^x$" (L144; probable typo for $\sum_x$, see Part G) and the proof of Prop 3.6 where $\beta, \beta'$ are reals in supports (L282).

### A.6 $P_\alpha$; principal series

- Kind: own definition; Definition 1.2, §1, p.2, L37.
- Verbatim: "**Definition 1.2.** Let $P_\alpha$ denote the set of all series $b \in K((\mathbb{R}^{\leq 0}))$ such that $\mathrm{ot}(b) = \omega^\alpha$ and the supremum of the support of $b$ (also denoted by $\sup(b)$) is $0$. A series $b$ in $P_\alpha$ is said to be **principal**."
- Examples given (L39): "For instance, $P_0 = K \setminus \{0\}$, and the series $\sum_n t^{-\frac{1}{n}}$ is in $P_1$; on the other hand, $t^{-1} + 1$ and $1 + \sum_n t^{-\frac{1}{n}}$ are not principal since their order types are respectively $2$ and $\omega + 1$, while $\sum_n t^{-1-\frac{1}{n}}$ is also not principal, this time because the supremum of its support is $-1$."
- Notes:
  - Index convention: $P_\alpha$ is the set of series of order type $\omega^\alpha$ (the index is the Cantor degree, not the order type). So $P_0 = K\setminus\{0\}$, $P_1$ = order type $\omega$. Note $0 \notin P_\alpha$ for any $\alpha$.
  - "principal" is used as an adjective of series: "principal series" (L41, L47, L61, L63, L71, L221, L357), "$b$ principal" (L453, L511 "Let $b$ principal such that"), "$b$, $c$ principal" (L47, L138, L221), "principal elements" (L235), "non-principal elements" (L191, L235), "non-principal series" (L245), "principal not in $K$" (L306). 36 occurrences of "principal" including "additively/multiplicatively principal" (7) and "principal value" (1).
  - The definition itself (Def 1.2) is not attributed, but the next paragraph credits "Berarducci's analysis on principal series" (L41) — see B.6.
  - $\sup(b)$ is defined here as the supremum of the support: "(also denoted by $\sup(b)$)". Used 14 times: "$\sup(b) = 0$" (L73, L81, L237, L421, L515), "$\sup(S) = 0$" (L140), "$\sup(\Gamma) = 0$" (L355, L371, L457), "$\sup(\mathrm{Res}(b)) = 0$" (L371), "$t^{\sup(d)}$" (L233), "$\sup(b + r) = 0$" (L73).
  - Sum-notation conventions: "$\sum_n t^{-\frac{1}{n}}$" (index $n$ with no range) in §1; "$\sum_{n \in \mathbb{N}} t^{-\frac{1}{n+1}}$" in §2 (L155, L195, L211), which indicates $0 \in \mathbb{N}$ — consistent with $k \in \mathbb{N}$ allowing $k=0$ in Theorem 1.4(2) (L59), $n=0$ in Cor 4.5 (L326, base case $\alpha = \omega^\beta$), and $\mathbb{N}[\ldots]$ as the coefficient semiring at L101. So the paper's convention is $0 \in \mathbb{N}$ (inferred from usage; never stated).

### A.7 $\sup(b)$

- See A.6. Kind: own notation (parenthetical), Def 1.2, L37: "the supremum of the support of $b$ (also denoted by $\sup(b)$)". Also applied to sets of reals: $\sup(S)$, $\sup(\Gamma)$, $\sup(\mathrm{Res}(b))$.

### A.8 $R_\alpha$ — the reducible principal series

- Kind: own notation; §1, p.2, L45 (item 3 of the list of properties).
- Verbatim (L41–L45): "By Berarducci's analysis on principal series, all series in $P_\alpha$ satisfy the following properties: for all ordinals $\alpha$, $\beta$, $\gamma$,
  1. $P_\alpha \cdot P_\beta \subseteq P_{\alpha \oplus \beta}$ ([Ber00, Cor. 9.9]);
  2. all divisors of $b \in P_\alpha$ are principal ([LM17, Cor. 4.6]);
  3. $R_\alpha := \{b \in P_\alpha : b \text{ is reducible}\} \overset{(2)}{=} \bigcup^{\beta,\gamma\neq 0}_{\beta \oplus \gamma = \alpha} P_\beta \cdot P_\gamma \subseteq P_\alpha$."
- Notes:
  - Defining symbol "$:=$" used for definitions throughout the paper (also $v_J(b) :=$, $b_{|\gamma} :=$, $J_\alpha :=$, $A_\alpha :=$, $\deg(0) :=$, $\mathrm{RV}_\nu^\alpha :=$, $v_J^p(b) :=$, $\deg_J^p(b) :=$).
  - "$\overset{(2)}{=}$" — equality justified by item (2), written over the equals sign.
  - Product of sets $P_\beta \cdot P_\gamma$ is the set of products.
  - "reducible" (as a property of a series) is used without definition (Part C); "$b$ is reducible".
  - Later (Def 4.1, L306): "$A_\alpha := J_\alpha + \mathrm{Span}_K(R_\alpha)$"; Cor 1.6 (L67) / Conj 1.10 (L85): "$\mathrm{Span}_K(R_\alpha)$ is infinite co-dimensional in $\mathrm{Span}_K(P_\alpha)$". Theorem 1.4 (L63): "$\mathrm{ot}(p_i q_i) = \omega^\alpha$ (that is, $p_i q_i \in R_\alpha$)".

### A.9 Hessenberg's natural sum and product, $\oplus$, $\odot$

- Kind: notation fixed + standard notion re-defined (the paper says it will "give a minimal account"); §1 L47 and §2 p.3 L89–L101.
- Verbatim (L47): "Here $\oplus$, $\odot$ denote Hessenberg's natural (commutative) operations. Note that (1) is equivalent to stating that $\mathrm{ot}(bc) = \mathrm{ot}(b) \odot \mathrm{ot}(c)$ for all principal series $b$, $c$. One can easily deduce that every principal $b$ of order type $\omega^{\omega^\alpha}$ is irreducible: there are no $\beta, \gamma \neq 0$ such that $\beta \oplus \gamma = \omega^\alpha$, so $R_\alpha = \varnothing$."
- Verbatim (L89): "We assume that the reader has familiarity with the class $\mathbf{On}$ of ordinal numbers and the classical (non-commutative) operations on them, but we will give a minimal account of Hessenberg's commutative operations."
- Verbatim definition (L97): "Given $\alpha = \omega^{\gamma_1} + \omega^{\gamma_2} + \ldots + \omega^{\gamma_n}$ and $\beta = \omega^{\gamma_{n+1}} + \omega^{\gamma_{n+2}} + \ldots + \omega^{\gamma_{n+m}}$ in Cantor normal form, let $\pi$ be a permutation of the integers $1, \ldots, n+m$ such that $\gamma_{\pi(1)} \geq \ldots \geq \gamma_{\pi(n+m)}$. Then $\alpha \oplus \beta$ is defined to be $\omega^{\gamma_{\pi(1)}} + \ldots + \omega^{\gamma_{\pi(n)}}$, and $\alpha \odot \beta$ to be $\bigoplus_{1 \leq i \leq n, n+1 \leq j \leq n+m} \omega^{\gamma_i \oplus \gamma_j}$. Note that by definition $\omega^\alpha \odot \omega^\beta = \omega^{\alpha \oplus \beta}$ for all $\alpha, \beta \in \mathbf{On}$. Moreover, $\omega^{\beta_1} + \cdots + \omega^{\beta_n} = \omega^{\beta_1} \oplus \cdots \oplus \omega^{\beta_n}$ if (and only if) the left hand side is in Cantor normal form. These are **Hessenberg's natural sum and product**."
- Verbatim (L99–L101, the polynomial isomorphism): "We remark that in Cantor normal form, Hessenberg's operations can be interpreted as sum and product for polynomials in the variables $\omega^{\omega^\alpha}$, for $\alpha \in \mathbf{On}$. We summarise this consideration with the isomorphism $$(\mathbf{On}, \oplus, \odot) \cong \left( \mathbb{N}\left[ \omega^{\omega^0}, \omega^{\omega^1}, \ldots, \omega^{\omega^\alpha}, \ldots \right], +, \cdot \right).$$"
- Notes:
  - Symbols: $\oplus$ (18 occurrences), $\odot$ (8), $\bigoplus$ (1). Names: "Hessenberg's natural (commutative) operations" (L47), "Hessenberg's commutative operations" (L89), "Hessenberg's natural sum and product" (L97), "Hessenberg's operations" (L99). Never "natural sum" alone, never "Hessenberg sum", never "#" or "⊗".
  - In the displayed definition of $\alpha\oplus\beta$ the transcription reads "$\omega^{\gamma_{\pi(1)}} + \ldots + \omega^{\gamma_{\pi(n)}}$" — the upper index should be $\pi(n+m)$; transcription or source typo (Part G).
  - Classical ordinal addition and multiplication are written with "+" and juxtaposition or "$\cdot$": "$\omega^\beta \cdot \mathrm{ot}(\ldots)$" (L359), "$\omega^\beta \cdot \alpha$" (L369), "$m\omega^\alpha + \beta$" (L73), "$3\omega+1$", "$3\omega + 2$" (L429), "$\omega + \omega$" (L195). Note the order "$3\omega$" and "$m\omega^\alpha$" (natural number on the left) where classical arithmetic would require $\omega\cdot 3$, $\omega^\alpha \cdot m$ — see Part G.
  - "(non-commutative)" / "(commutative)" parentheticals used to distinguish classical vs natural operations.
  - $\mathbf{On}$ in bold for the class of ordinals (5 occurrences).
  - British "summarise" (L99).

### A.10 Cantor normal form; Cantor degree, $\deg(\alpha)$, of an ordinal

- Kind: own definition (bold), §2, p.3, L91–L95.
- Verbatim: "Recall that for all $\alpha \in \mathbf{On}$, there is a maximum $\beta$ such that $\omega^\beta \leq \alpha$ and a unique $\gamma$ such that $\alpha = \omega^\beta + \gamma$. By repeating the argument, we find a unique finite sequence $\beta_1 \geq \beta_2 \geq \ldots \geq \beta_n \geq 0$ of ordinals such that $$\alpha = \omega^{\beta_1} + \ldots + \omega^{\beta_n}. \tag{1}$$ The expression on the right-hand side is called **Cantor normal form** of $\alpha$. We let $\beta_1$ be the **Cantor degree of** $\alpha$, denoted by $deg(\alpha)$."
- Notes:
  - Cantor normal form is written as a sum of $\omega$-powers with repetition allowed (no integer coefficients): "$\omega^{\beta_1} + \ldots + \omega^{\beta_n}$", $\beta_1 \ge \cdots \ge \beta_n$. This is the convention used everywhere (Thm 1.4 L58–L59, Lemma 4.14 L435, Prop 4.15 L453, Cor 4.18 L511) — e.g. "$\alpha = \omega^{\beta_1} + \omega^{\beta_2} + k$ where ... $k \in \mathbb{N}$" (L59) mixes in a finite tail $k$; Lemma 4.14's proof writes "$\deg_J(pq) = \sum_{i=1}^n \omega^{\alpha_i}$ where $\alpha_i \geq \alpha_{i+1}$" (L435).
  - Spelling of the phrase: "Cantor normal form" (7), "Cantor Normal form" (2: L381, L463), "Cantor Normal Form" (1: L451). Lower-case dominates. Also "the Cantor normal form has length three" (L463).
  - The degree of an *ordinal* is "Cantor degree", written $deg(\alpha)$ (L95, italic in transcription). The abstract also says "ordinals $\alpha$ of non-additively principal Cantor degree" (L7). The same symbol $\deg$ is reused for the degree of a *series* (Def 2.12, B.14), defined as the Cantor degree of its order type; and $\deg_J(b)$ is "the Cantor degree of $v_J(b)$" (L132). "Cantor degree" occurs 4 times.
  - Introductory "Recall that" signals standard material (Part D).
  - Equation tag "(1)" — the only numbered display in the paper; it is never referred back to. (The "(1)" in L47 "Note that (1) is equivalent to" refers to item 1 of the list at L43, not to the display.)

### A.11 additively principal; multiplicatively principal (ordinals)

- Kind: standard notions defined in the paper's own words; §2, p.3, L103.
- Verbatim: "An ordinal is **additively principal** if it cannot be written as a sum of two strictly smaller ordinals (equivalently, it is of the form $\omega^\alpha$) and **multiplicatively principal** if it cannot be written as a product of two strictly smaller ordinals (equivalently, it is of the form $\omega^{\omega^\alpha}$)."
- Second gloss (L169): "Note that $\deg_J^p(b)$ is **additively principal**: the ordinals strictly less than $\deg_J^p(b)$ are closed under addition."
- Notes: "additively principal" 6 occurrences (abstract "non-additively principal Cantor degree", L7; Def 2.11 "for $\alpha$ additively principal also a ring", L189; Rem 4.2 "if $\alpha$ is additively principal, then $R_\alpha = \varnothing$", L308; proof of Lemma 4.9 "Since $\deg_J^p(e)$ is additively principal", L381). "multiplicatively principal" once. The word "principal" thus has three uses in the paper: principal series ($P_\alpha$), additively/multiplicatively principal ordinals, and principal value $v_J^p$.

### A.12 ordinal value $v_J(b)$ — attributed to [Ber00, p. 558] (see B.8); the paper gives its own displayed case-formula

- Kind: reused definition with own formula; §2, p.4, L120–L124.
- Verbatim (L120–L124): "Given $b \in K((\mathbb{R}^{\leq 0}))$, the **ordinal value** of $b$ ([Ber00, p. 558]) is $$v_J(b) := \begin{cases} 0 & \text{if } b \in J, \\ 1 & \text{if } b \in (J + K) \setminus J, \\ \min\{\mathrm{ot}(c) : c \equiv b \mod J + K\} & \text{otherwise.} \end{cases}$$ The keystone of [Ber00] is that $v_J$ is a multiplicative semi-valuation."
- Notes:
  - Symbol $v_J$ (37 occurrences). The subscript $J$ is on the $v$. Prose: "ordinal value" (4 occurrences: L120, L282 "By comparing the ordinal values", L304 "elements of ordinal value $\omega^\alpha$", L343 "the series of ordinal value $\omega^\alpha$").
  - "multiplicative semi-valuation" (L124) is the paper's characterisation of Berarducci's keystone; "semi-valuation" occurs only here. "keystone" is the paper's word for the central result of [Ber00].
  - One bare "$v(b_j^{|\gamma_i})$" at L411 ("such that $v(b_j^{|\gamma_i}) = \deg_J^r(b)$") — inconsistent with the rest; should be $\deg_J$ (Part G).

### A.13 $\deg_J(b)$; convention $\deg_J(b) = -\infty$ for $b \in J$, $\omega^{-\infty} = 0$

- Kind: own notation; §2, p.4, L132–L136.
- Verbatim (L132): "The values of $v_J$ are all of the form $\omega^\alpha$ ([Ber00, Rem. 5.3]), thus we add the following notation: let $\deg_J(b)$ denote the Cantor degree of $v_J(b)$, where by convention we set $\deg_J(b) = -\infty$ when $b \in J$, and $\omega^{-\infty} = 0$. Thus we have $v_J(b) = \omega^{\deg_J(b)}$, and we may rephrase the above properties as:
  - $\deg_J(b + c) \leq \max\{\deg_J(b), \deg_J(c)\}$;
  - $\deg_J(bc) = \deg_J(b) \oplus \deg_J(c)$;
  - $\deg_J(b) = -\infty$ if and only if $\deg_J(b) = -\infty$."
- Notes:
  - $\deg_J$ is by far the paper's dominant measure: 220 occurrences of `deg_J` (including $\deg_J^p$, $\deg_J^r$). It has no prose name — never "$J$-degree" — the paper just writes the symbol, or speaks of "ordinal value(s)". Contrast: "the degree" for $\deg$ (Def 2.12).
  - The third bullet as transcribed is tautological; the intended statement is "$\deg_J(b) = -\infty$ if and only if $b \in J$" (Part G).
  - Convention: $-\infty$ as the value on $J$, and the explicit convention "$\omega^{-\infty} = 0$" so that $v_J(b) = \omega^{\deg_J(b)}$ holds for all $b$.
  - One lower-case "$\deg_j(b_1)$" at L225 ("by induction on $\deg_j(b_1)$") — typo for $\deg_J$.
  - Typical comparisons: "$\deg_J(b) > 0$", "$\deg_J(p) \le \deg_J(q)$", "$\deg_J(r) < \deg_J(b)$", "$\deg_J(r^{|\gamma}) < \deg_J^r(b)$", "By looking at the Cantor Normal form of $\deg_J(e)$" (L381).

### A.14 "few cancellation" — the correction of [Ber00] (Example 2.3)

- Kind: own observation correcting an inherited claim; §2, p.4, L138–L140. Quoted in full in Part F (F.1). Defines no term, but fixes the paper's word "cancellations" for coefficient cancellation in a product.
- Phrasing: "the coefficient of $t^{s_m + s_n}$ in $bc$ is $(-1)^m + (-1)^n = 1 - 1 = 0$" (L140); "thus cancellations occurs on a set of order type $\mathrm{ot}(T) = \omega^2$" (L140; grammatical slip in source or transcription).

### A.15 truncation $b_{|\gamma}$; translated truncation $b^{|\gamma}$; germ of $b$ at $\gamma$

- Kind: own definition; Definition 2.4, §2, p.4, L142–L149. Preceded by "The following notions are fundamental in our work." (L142).
- Verbatim (L144–L149): "**Definition 2.4.** Given $b = \sum_\beta b_x t^x \in K((\mathbb{R}^{\leq 0}))$ and $\gamma \in \mathbb{R}^{\leq 0}$, we define:
  - the **truncation** of $b$ at $\gamma$ is $b_{|\gamma} := \sum_{x \leq \gamma} b_x t^x$,
  - the **translated truncation** of $b$ at $\gamma$ is $b^{|\gamma} := t^{-\gamma} b_{|\gamma}$.
  The equivalence class $b^{|\gamma} + J$ is the **germ of** $b$ **at** $\gamma$."
- Notes / conventions:
  - Truncation is *at and below* $\gamma$: the sum is over $x \leq \gamma$ (inclusive), i.e. the truncation keeps the *smaller* exponents (those further from $0$), not the larger ones. The translated truncation multiplies by $t^{-\gamma}$ so that the exponent $\gamma$ is moved to $0$ and $b^{|\gamma} \in K((\mathbb{R}^{\leq 0}))$.
  - Notation: subscript bar for truncation $b_{|\gamma}$ (2 occurrences), superscript bar for translated truncation $b^{|\gamma}$ (188 occurrences of `^{|` — the workhorse notation). All later arguments use $b^{|\gamma}$; plain truncation $b_{|\gamma}$ is never used again after Def 2.4.
  - Translated truncations appear at many kinds of argument: $b^{|\gamma}$, $b^{|\delta}$, $b^{|-1}$, $b^{|-2}$ (Rem 2.6, L155), $b_i^{|\gamma_{i,j}}$, $(ab)^{|\gamma}$, $(cd)^{|\gamma}$, $\left(\sum_i \varepsilon_i c_i\right)^{|\gamma_0}$ (L395), $(\ldots)^{|\gamma-\varepsilon}$ (L487), $p^{|\epsilon}$ (L487).
  - "germ of $b$ at $\gamma$" = the class $b^{|\gamma} + J$. The word "germ" occurs only here and in the title of [LM17] ("Factorisation of germ-like series"). The paper then avoids "germ" and writes "$\ldots \mod J$" instead.
  - Prose for the operation: "the truncation of $b$ at $\gamma$"; "translated truncations behave like a sort of 'generalised coefficients'" (L179); "If we now consider $b^{|\gamma}$ for some arbitrary $\gamma \in \mathrm{Res}(b)$" (L353).
  - The index "$\sum_\beta$" in "$b = \sum_\beta b_x t^x$" should be $\sum_x$; Part G.

### A.16 $J$-critical point, $\mathrm{crit}_J(b)$

- Kind: own definition (distinguished from Berarducci's $\mathrm{crit}(b)$); Definition 2.5, §2, p.4, L151.
- Verbatim: "**Definition 2.5.** Let $b \in K((\mathbb{R}^{\leq 0})) \setminus J$. The $J$**-critical point** of $b$, denoted by $\mathrm{crit}_J(b)$, is the minimal $\gamma \in \mathrm{supp}(b)$ such that for every $\gamma < \delta < 0$ we have $v_J(b^{|\delta}) < v_J(b)$."
- Immediately following (L153): "We note that if $b \in P_\alpha$, then $\mathrm{crit}_J(b) = \min(\mathrm{supp}(b))$."
- Notes: 7 occurrences of $\mathrm{crit}_J$. Used in Def 2.7 ("$\gamma > \mathrm{crit}_J(b)$", L171, L173) and the proof of Lemma 4.10 ("For every $\mathrm{crit}_J(c) < \gamma < 0$ we have $\deg_J(c^{|\gamma}) < \deg_J(c)$", L387). The contrast with $\mathrm{crit}(b)$ is Remark 2.6 (B.11 and F.2). Note $\min(\mathrm{supp}(b))$ is written with $\min$ applied to a set.

### A.17 principal value $v_J^p(b)$; residual value $v_J^r(b)$; $\deg_J^p(b)$; $\deg_J^r(b)$

- Kind: reused definition ([Ber00, Def. 6.4]) for $v_J^p$, $v_J^r$; own notation for $\deg_J^p$, $\deg_J^r$; §2, pp.4–5, L157–L169.
- Verbatim (L157–L162): "Given $b \in K((\mathbb{R}^{\leq 0}))$ with $v_J(b) > 1$, we know that $v_J(b)$ has the form $\omega^\beta$ for some ordinal $\beta > 0$. From the Cantor normal form of $\beta$ it follows that $v_J(b)$ can be written uniquely as a product $\omega^{\omega^{\beta_1}} \cdots \omega^{\omega^{\beta_n}}$, where $\beta_1 \geq \beta_2 \geq \ldots \geq \beta_n$. We define ([Ber00, Def. 6.4]):
  1. $v_J^p(b) := \omega^{\omega^{\beta_n}} = $ the **principal value** of $b$,
  2. $v_J^r(b) := \omega^{\omega^{\beta_1}} \cdots \omega^{\omega^{\beta_{n-1}}} = $ the **residual value** of $b$."
- Verbatim (L164–L169): "For instance, if $v_J(b) = \omega^3$, then $v_J^p(b) = \omega$ and $v_J^r(b) = \omega^2$. Note that $v_J(b) = v_J^r(b) v_J^p(b)$. For the sake of readability, we introduce the following notation to remove the base $\omega$.
  1. $\deg_J^p(b) := \omega^{\beta_n}$,
  2. $\deg_J^r(b) := \omega^{\beta_1} + \cdots + \omega^{\beta_{n-1}}$.
  We have $\deg_J(b) = \deg_J^r(b) + \deg_J^p(b)$. Note that $\deg_J^p(b)$ is **additively principal**: the ordinals strictly less than $\deg_J^p(b)$ are closed under addition."
- Notes / conventions:
  - The *principal* value is the *last* (smallest) factor $\omega^{\omega^{\beta_n}}$; the *residual* value is the product of all the others. Correspondingly $\deg_J^p(b) = \omega^{\beta_n}$ is the last (smallest) term of the Cantor normal form of $\deg_J(b)$ and $\deg_J^r(b)$ is the rest, with $\deg_J(b) = \deg_J^r(b) + \deg_J^p(b)$ (residual on the left, principal on the right; classical sum). The product is written $v_J^r(b) v_J^p(b)$ (residual first).
  - Superscripts $p$ and $r$ (not subscripts). Counts: $v_J^p$ 4, $v_J^r$ 3, $\deg_J^p$ 32, $\deg_J^r$ 29. The $\deg$-forms dominate; $v_J^p$ reappears only at L355 ("$\mathrm{ot}(\Gamma) = v_J^p(b) = \omega^{\omega^{\alpha_2}}$").
  - Only defined for $v_J(b) > 1$; the paper does not say what $\deg_J^p$, $\deg_J^r$ are when $\deg_J(b) \in \{0, -\infty\}$. The condition "$\deg_J(b_1) \neq \deg_J^p(b_1)$" (Axiom 2 of Q) is the paper's way of saying the Cantor normal form of $\deg_J(b_1)$ has more than one term; restated at L284: "when $\deg_J(b_1) \neq \deg_J^p(b_1)$, that is $\deg_J^r(b_1) > 0$".
  - "For the sake of readability" (L164), "to remove the base $\omega$" — phrases explaining a notational move.

### A.18 big point; $\mathrm{Big}(b)$; $\mathrm{Big}^\alpha(b)$

- Kind: own definition; Definition 2.7, §2, p.5, L171–L173.
- Verbatim (L171): "**Definition 2.7.** Let $b \in K((\mathbb{R}^{\leq 0}))$. We say that $\gamma \in \mathrm{cl}(\mathrm{supp}(b)) - \{0\}$ is a **big point** of $b$ if $\deg_J(b^{|\gamma}) \geq \deg_J^r(b)$ and $\gamma > \mathrm{crit}_J(b)$. The set of all big points of $b$ is denoted by $\mathrm{Big}(b)$."
- Verbatim (L173): "More generally, let $\mathrm{Big}^\alpha(b)$ denote all the numbers $\gamma \in \mathrm{cl}(\mathrm{supp}(b)) - \{0\}$ such that $\deg_J(b^{|\gamma}) \geq \alpha$ and $\gamma > \mathrm{crit}_J(b)$."
- Remark 2.8 (L177): "By construction, the big points of a series must accumulate to $0$. Moreover, they are accumulation points of $\mathrm{cl}(\mathrm{supp}(b))$ as soon as $\deg_J^r(b) > 0$."
- Notes: "big point(s)" 5 occurrences; $\mathrm{Big}$ 14 (including $\mathrm{Big}^{\omega^{\alpha_1}}(r)$, $\mathrm{Big}^{\omega^{\alpha_2}}(r)$, $\mathrm{Big}^\alpha(r)$, $\mathrm{Big}^{\deg_J^r(b)}(r)$). So $\mathrm{Big}(b) = \mathrm{Big}^{\deg_J^r(b)}(b)$. Points are taken in the *closure* of the support minus $\{0\}$. Phrasing: "the $b_i$'s do not have big points in common" (L286), "recall that each $\gamma_{i,j}$ is in $\mathrm{Big}(b_i)$" (L284), "allow dependence between either the isolated points or the big points" (L286), "$\mathrm{Big}(b_i) \cap \mathrm{Big}(b_{i'}) = \varnothing$" (L282).
  - Inconsistency between L371 "$\mathrm{Big}^{\omega^{\alpha_1}}(r) \cap [\delta, 0]$ has order type strictly smaller that $\omega^{\omega^{\alpha_2}}$" and, in the same line, "$\Gamma = \mathrm{Res}(b) \setminus \mathrm{Big}^{\omega^{\alpha_2}}(r)$" (superscript $\alpha_1$ vs $\alpha_2$; the argument needs $\omega^{\alpha_1}$ in both). Part G.

### A.19 residual point; $\mathrm{Res}(b)$ (= Berarducci's $X(b)$)

- Kind: own name and symbol for an inherited set; Definition 2.7 (continued), §2, p.5, L175.
- Verbatim: "We say that $\gamma \in \mathrm{cl}(\mathrm{supp}(b)) - \{0\}$ is a **residual point** of $b$ if $\deg_J(b^{|\gamma}) = \deg_J^r(b)$. The set of all these point $\mathrm{Res}(b)$ was defined in [Ber00, Def. 6.6] (where it is called $X(b)$)."
- Notes: "residual point" occurs once; $\mathrm{Res}$ 17 times. Re-symbolled from Berarducci's $X(b)$ (see B.13, F.3). As transcribed, residual points do not carry the condition $\gamma > \mathrm{crit}_J(b)$ that big points carry. Used as: "For every $\gamma \in \mathrm{Res}(b)$ we have by Proposition 2.10" (L337), "since $\mathrm{Res}(b)$ is infinite" (L341), "$\gamma_1, \ldots, \gamma_k \in \mathrm{Res}(b)$ arbitrarily close to $0$" (L343), "$\mathrm{ot}(\mathrm{Res}(b)) = \omega^{\omega^{\alpha_2}}$ and $\sup(\mathrm{Res}(b)) = 0$ by [Ber00, Lem. 6.8]" (L371), "$\Gamma = \mathrm{Res}(b) \setminus \mathrm{Big}^{\ldots}(r)$" (L371, L457, L467, L507), "for every $\gamma \in \mathrm{Res}(c)$ close enough to $0$" (L407).

### A.20 $\Gamma$ — the working subset $\mathrm{Res}(b) \setminus \mathrm{Big}^{\ldots}(r)$

- Kind: own local notation (re-introduced in each proof); §4.2 L355, L371; §4.3 L457, L467, L507.
- Verbatim (L355): "To overcome this issue, we find a large $\Gamma \subseteq \mathrm{Res}(b)$, namely $\mathrm{ot}(\Gamma) = v_J^p(b) = \omega^{\omega^{\alpha_2}}$ and $\sup(\Gamma) = 0$, on which we have $\deg_J(r^{|\gamma}) < \deg_J^r(b) = \omega^{\alpha_1}$."
- Verbatim (L371): "It follows at once that for some $\delta < 0$ sufficiently small, $\mathrm{Big}^{\omega^{\alpha_1}}(r) \cap [\delta, 0]$ has order type strictly smaller that $\omega^{\omega^{\alpha_2}}$, while $\mathrm{ot}(\mathrm{Res}(b)) = \omega^{\omega^{\alpha_2}}$ and $\sup(\mathrm{Res}(b)) = 0$ by [Ber00, Lem. 6.8]. Therefore, $\Gamma = \mathrm{Res}(b) \setminus \mathrm{Big}^{\omega^{\alpha_2}}(r)$ has order type $\omega^{\omega^{\alpha_2}}$ and $\sup(\Gamma) = 0$. By construction, for $\gamma \in \Gamma$ we have $\deg_J(r^{|\gamma}) < \omega^{\alpha_1}$."
- Verbatim (L457): "Let $\Gamma = \mathrm{Res}(b) \setminus \mathrm{Big}^\alpha(r)$. Note that by Lemma 4.8, $\Gamma$ has order type $\omega^{\alpha_{n+1}}$ and $\sup(\Gamma) = 0$."
- Verbatim (L467): "Let $\Gamma = (\mathrm{Res}(b) - \mathrm{Big}^{\deg_J^r(b)}(r))$, which, as observed in the proof of Proposition 4.15, is infinite with supremum $0$."
- Notes: "a large $\Gamma$" — "large" here means of the full order type $v_J^p(b)$ with supremum $0$. (L457 "order type $\omega^{\alpha_{n+1}}$" vs L355's "$\omega^{\omega^{\alpha_2}}$": by the same reasoning one expects $\omega^{\omega^{\alpha_{n+1}}}$ at L457; Part G.) The letter $\Gamma$ is not used for anything else; $S$ is the analogous finite set in Prop 3.6's proof (L272) and the support-union in Lemma 4.11's proof (L397); $T$ is the cancellation set in Example 2.3 (L140).

### A.21 $J_\alpha$ — series of $J$-degree $< \alpha$

- Kind: own definition; Definition 2.11, §2, p.5, L189.
- Verbatim: "**Definition 2.11.** For every $\alpha$ we let $J_\alpha := \{b \in K((\mathbb{R}^{\leq 0})) : \deg_J(b) < \alpha\}$. $J_\alpha$ is a $K$-vector space, and for $\alpha$ additively principal also a ring, which would allow the use of $J_\alpha$-linear combinations in our proofs."
- Notes: 33 occurrences of `J_`. Strict inequality: $J_\alpha$ = degree strictly less than $\alpha$; so $J_0 = J$ and $J_1 = J + K$. Used as modulus: "$\mod J_\alpha$" (L339), "$\mod J_{\omega^{\alpha_1}}$" (L375, L403), "$\mod J_{\deg_J(c)}$" (L389), "$\mod J_{\deg_J^r(pq)}$" (L433), "$\mod J_{\deg_J(q)}$" (L473, L479, L491), "$\mod J_{\deg_J(c_1)}$" (L395). Also "$\sum_{i=1}^n k_i b_i = r \in J_\alpha$" (L262), "Now $J_{\omega^{\alpha_1}}$ is an integral domain, thus the series $b^{|\gamma}$ for $\gamma \in \Gamma$ lie in a finitely generated $J_{\omega^{\alpha_1}}$-module" (L377), "linearly independent over $J_\alpha = A_\alpha$" (L320), "$\mathrm{RV}_J^\alpha = J_{\alpha+1}/J_\alpha$" (L219), "$\varepsilon_1, \ldots, \varepsilon_\ell \in J_{\deg_J^p(c_1)}$" (L393).

### A.22 degree valuation; degree $\deg(b)$ of a series — attributed to [LM24, p. 5] (see B.14); $\deg(0) := -\infty$

- Kind: reused definition with own convention; Definition 2.12, §2, p.5, L191–L195.
- Verbatim (L191): "In this work we also make use of the *degree valuation*, in order to prove irreducibility results for non-principal elements."
- Verbatim (L193): "**Definition 2.12** ([LM24, p. 5]). Given $b \in K((\mathbb{R}^{\leq 0}))$ with $b \neq 0$, let the **degree** of $b$, denoted by $\deg(b)$, be the Cantor degree of $\mathrm{ot}(b)$. We also let $\deg(0) := -\infty$."
- Examples (L195): "For instance, $t^{-\sqrt{2}} + t^{-1} + 1$ has degree $0$, while $\sum_{n \in \mathbb{N}} t^{-1-\frac{1}{n+1}} + \sum_{n \in \mathbb{N}} t^{-\frac{1}{n+1}}$ has degree $1$ because its order type is $\omega + \omega$, and $\sum_{(m,n) \in \mathbb{N}} t^{-\frac{1}{(n+1)(m+1)}}$ has degree $2$, as its order type is $\omega^2$. In [LM24] it is proved by the 3rd and the 4th authors that the degree is an **multiplicative valuation** in the following sense:"
- Also in §1 (L83): "Here $\deg(b)$ is the maximum ordinal $\alpha$ such that $\omega^\alpha \leq \mathrm{ot}(b)$."
- Notes: "degree valuation" (L191, italic) is the name for $\deg$ as a valuation; "the degree" is the prose name. 20 occurrences of `\deg(`. Prose: "has degree $2$" (L195, L213), "irreducible elements of degree $\alpha$ which are not principal" (L221). "multiplicative valuation" in bold at L195. "$\sum_{(m,n) \in \mathbb{N}}$" should be $\mathbb{N}^2$ (Part G; cf. L211 where $\mathbb{N}^2$ is written).

### A.23 $\mathrm{rv}_\nu$, $\mathrm{RV}_\nu$, $\mathrm{RV}_\nu^\alpha$; $\mathrm{rv}_J$, $\mathrm{RV}_J$, $\mathrm{RV}_J^\alpha$; $\mathrm{rv}_{\deg}$, $\mathrm{RV}_{\deg}$; the unsubscripted $\mathrm{rv}(b)$

- Kind: own definition; Definition 2.15, §2, p.6, L217–L221.
- Verbatim (L217): "**Definition 2.15.** For $\nu \in \{\deg, \deg_J\}$ let $\mathrm{rv}_\nu(b) = \mathrm{rv}_\nu(c)$ if and only if $\nu(b - c) < \nu(b)$ or $b = c$, and let $\mathrm{RV}_\nu$ be the quotient of $K((\mathbb{R}^{\leq 0}))$ by this equivalence relation. For the sake of notation, we write $\mathrm{rv}_J$, $\mathrm{RV}_J$ for respectively $\mathrm{rv}_{\deg_J}, \mathrm{RV}_{\deg_J}$."
- Verbatim (L219): "For both $\nu$ as above, $\mathrm{RV}_\nu$ is the union over $\alpha < \omega_1$ of the quotients $\mathrm{RV}_\nu^\alpha := \{b : \nu(b) \leq \alpha\}/\{c : \nu(b) < \alpha\}$. In particular, each $\mathrm{RV}_\nu^\alpha$ is naturally a $K$-vector space, $\mathrm{RV}_\nu^\alpha \cap \mathrm{RV}_\nu^\beta = \{\mathrm{rv}_\nu(0)\}$ for $\alpha \neq \beta$, and notably $\mathrm{RV}_J^\alpha = J_{\alpha+1}/J_\alpha$."
- Verbatim (L221, the unsubscripted $\mathrm{rv}$): "Moreover, for $b$, $c$ principal, we have $\deg(b - c) < \deg(b) = \deg_J(b)$ if and only if $\deg_J(b - c) < \deg_J(b)$. This means that $\mathrm{rv}_J$ and $\mathrm{rv}_{\deg}$ agree on the principal series. On the other hand, by definition of $\deg_J$, for every $b$ there is a principal $c$ such that $\mathrm{rv}_J(b) = \mathrm{rv}_J(c)$: in this case we simply write $\mathrm{rv}(b)$. Therefore, each $\mathrm{RV}_J^\alpha$ embeds into $\mathrm{RV}_{\deg}^\alpha$ as $K$-vector space and coincides with the image of the principal series under the quotient map. However, $\mathrm{RV}_{\deg}^\alpha$ is much richer, for instance $\mathrm{RV}_J^0 \cong K$ while $\mathrm{RV}_{\deg}^0 \cong K[\mathbb{R}^{\leq}]$, the space of the series with finite support. Thanks to $\mathrm{RV}_{\deg}$ and its properties proved in [LM24] we are able to find irreducible elements of degree $\alpha$ which are not principal, as we shall see in the following sections."
- Notes / conventions:
  - Lower-case $\mathrm{rv}$ is the map (class of $b$), upper-case $\mathrm{RV}$ the quotient structure; both upright. Counts: $\mathrm{rv}(\cdot)$ unsubscripted 35, $\mathrm{rv}_J$ 16, $\mathrm{rv}_{\deg}$ 1, $\mathrm{rv}_\nu$ 3; $\mathrm{RV}_J$ 11, $\mathrm{RV}_{\deg}$ 5, $\mathrm{RV}_\nu$ 6. The unsubscripted $\mathrm{rv}(b)$ dominates in §§3–4 and, per L221, is licensed when $\mathrm{rv}_J$ and $\mathrm{rv}_{\deg}$ agree; the paper nonetheless writes $\mathrm{rv}(b)$ for non-principal $b$ in Lemma 3.1/Prop 3.2 ("$p(\mathrm{rv}(b)) = t^{\gamma_m}$", L243), where the $\deg$-version must be meant.
  - The name "rv" is never expanded (no "leading term", no "residue value", no "RV-sort"). The section title is "Hereditary $\mathrm{rv}_J$" (L223).
  - The quotient formula "$\{b : \nu(b) \leq \alpha\}/\{c : \nu(b) < \alpha\}$" has a variable slip ($\nu(b)$ for $\nu(c)$); Part G.
  - Phrases: "$\mathrm{rv}_J(b_1), \ldots, \mathrm{rv}_J(b_n)$ are linearly independent" (L260), "$\{\mathrm{rv}(b_1), \ldots, \mathrm{rv}(b_m)\}$ is a part of a base of $\mathrm{RV}_J^\alpha$" (L239), "$\mathrm{rv}(A_\alpha)$ has infinite co-dimension as a $K$-vector subspace of $\mathrm{RV}_J^\alpha$" (L329), "cannot be represented as a sum of reducible elements in $\mathrm{RV}_J^\alpha$" (L328, L419), "$b$, $\mathrm{rv}(b)$ are irreducible" (L328, L419, L453, L503, L511; with $c$ at L247). Irreducibility of $\mathrm{rv}(b)$ is a notion in $\mathrm{RV}$ — the paper treats $\mathrm{RV}_J$ / $\mathrm{RV}_{\deg}$ as rings (products $AC = B$ of classes, L249) without stating the ring structure.
  - "a base" (L239, twice) rather than "a basis".

### A.24 hereditarily $\mathrm{rv}_J$-independent, $\mathrm{Q}(b_1,\ldots,b_n)$; Axiom 1; Axiom 2

- Kind: own definition (the paper's central new notion); §3, p.6, L225–L231 (section title "Hereditary $\mathrm{rv}_J$", L223).
- Verbatim (L225–L231): "Given $b_1, \ldots, b_n$ with $\deg_J(b_1) = \deg_J(b_i)$ for every $i = 1, \ldots, n$, we give the following definition by induction on $\deg_j(b_1)$. The series $b_1, \ldots, b_n$ are said to be **hereditarily $\mathrm{rv}_J$-independent**, written $\mathrm{Q}(b_1, \ldots, b_n)$, if:
  1. $(\mathrm{rv}_J(b_i))_{1 \leq i \leq n}$ are $K$-linearly independent;
  2. when $\deg_J(b_1) \neq \deg_J^p(b_1)$, there exists some $\delta < 0$ such that for all $\alpha$ with $\deg_J^r(b_1) \leq \alpha < \deg_J(b_1)$, for all $\gamma_{1,1}, \ldots, \gamma_{n,1}, \ldots, \gamma_{n,m(n)} \geq \delta$ with $\deg_J(b_i^{|\gamma_{i,j}}) = \alpha$ and $\gamma_{i,j} \neq \gamma_{i,j'}$ whenever $j \neq j'$, we have $$\mathrm{Q}(b_1^{|\gamma_{1,1}}, \ldots, b_1^{|\gamma_{1,m(1)}}, \ldots, b_n^{|\gamma_{n,1}}, \ldots, b_n^{|\gamma_{n,m(n)}}).$$
  Note that the above definition is obviously well founded."
- Naming of the clauses (Remark 3.3, L251): "In the proof above we used only Axiom 1 – linear independence in $\mathrm{RV}_J$. In the next section where we use induction arguments we will make heavy use of Axiom 2." Also "proving Axiom 1" (L268), "as in Axiom 2" (L276), "to verify Axiom 2 it suffices to test the independence on the points of $\mathrm{supp}(b_i)$ only, rather than all of $\mathrm{cl}(\mathrm{supp}(b_i))$. Likewise, for Axiom 1, it is sufficient to check that the supports of the $b_i$'s pairwise intersect only on accumulation points, or alternatively that the $b_i$'s do not have big points in common, again pairwise." (L286).
- Notes / conventions:
  - The symbol is an upright $\mathrm{Q}$ applied to a tuple; 32 occurrences. Prose: "$\mathrm{Q}(b_1, \ldots, b_n)$ holds" (L264, L293, L300, L312, L347, L413, L507), "with $\mathrm{Q}(b)$" (L328, L419, L453, L455; with $c$ at L247), "such that $\mathrm{Q}(b)$" (L503, L511), "$\mathrm{Q}(b^{|\gamma})$ does not hold, a contradiction against $\mathrm{Q}(b)$" (L459), "another contradiction against $\mathrm{Q}(b)$" (L461), "$\mathrm{Q}(b_1, ., b_n)$" (L266, L293, L300 — the "." is a transcription artefact for "$\ldots$"). Also applied to an angle-bracket tuple: "$\mathrm{Q}(\langle b_j^{|\gamma_i} : \deg_J(b_j^{|\gamma_i}) = \alpha \rangle)$" (L345).
  - The two clauses are called "Axiom 1", "Axiom 2" (capital A, no quotes).
  - In §1 this is announced as: "In Section 3 we define an independence relation which is a generalization of randomness, and can substitute it in all of the above." (L77).
  - Only defined for tuples of equal $\deg_J$; $\delta<0$ is the uniform closeness-to-$0$ threshold.
  - "hereditarily $\mathrm{rv}_J$-independent" occurs once (the definition); the section title says "Hereditary".

### A.25 $p(b)$ — the monic maximal finite-support divisor

- Kind: own notation built on [LM24, Prop. 5.5.1]; §3, p.6, L233.
- Verbatim: "By [LM24, Prop. 5.5.1], we know that every $b$ has a maximal divisor in $K[\mathbb{R}^{\leq}]$ (the series with finite support), which is unique up to a multiplication by an element in $K$. Clearly, for every $b$ there is a unique maximal divisor $d$ such that the coefficient of $t^{\sup(d)}$ is $1$, denoted by $p(b)$."
- Notes: normalisation convention: the coefficient of the top exponent $t^{\sup(d)}$ is $1$. Used: "$p(b) = 1$" (L237, L249), "$p(\mathrm{rv}(b)) = t^{\gamma_m}$" (L243), "As $p(B) = 1$ then also $p(A) = 1$" (L249), "$\frac{\mathrm{rv}(b)}{p(\mathrm{rv}(b))}$" (L249). Related phrases: "a maximal divisor of finite support of $\mathrm{rv}(b)$" (L243), "$p(b)$ must be a unit" (L243), "$t^{\gamma_m} = \gcd(t^{\gamma_1}, \ldots, t^{\gamma_m})$" (L243), "As $\mathrm{rv}(p(b)) = p(b)$ it follows that $p(b)$ divides $\mathrm{rv}(b)$, hence by maximality it divides also $p(\mathrm{rv}(b))$" (L243).

### A.26 random (series); mutually random

- Kind: own definition; Definition 1.3 (§1, p.2, L49–L52) and §3 p.7 L253–L258.
- Verbatim (Def 1.3, L49–L52): "**Definition 1.3.** We say that $b = \sum_\gamma b_\gamma t^\gamma \in K((\mathbb{R}^{\leq 0}))$ is *random* if one of the following holds:
  - $\mathrm{cl}(\mathrm{supp}(b)) - \{0\}$ is a $\mathbb{Q}$-linearly independent set;
  - the tuple $\langle b_\gamma : \gamma \in \mathrm{supp}(b) \rangle$ is algebraically independent over $\mathbb{Q}$."
- Verbatim (L253–L258): "We say that $b_1, \ldots, b_m \in K((\mathbb{R}^{\leq 0}))$ are *mutually random* if one of the following holds:
  - $\mathrm{cl}(\mathrm{supp}(b_i)) \cap \mathrm{cl}(\mathrm{supp}(b_j)) = \{0\}$ for every $1 \leq i \neq j \leq m$ and $\bigcup_i \mathrm{cl}(\mathrm{supp}(b_i)) - \{0\}$ is $\mathbb{Q}$-linearly independent set.
  - $\langle b_{i\gamma} : 1 \leq i \leq m, \gamma \in \mathrm{supp}(b_i) \rangle$ is algebraically independent over $\mathbb{Q}$.
  We show now that $b_1, \ldots, b_m$ mutually random implies $\mathrm{Q}(b_1, \ldots, b_m)$."
- Notes: "random" 9 occurrences, "mutually random" 2. Italic rather than bold at definition. Prose: "If $b \in P_\alpha$ is random, then $b$ is irreducible" (L61), "all random series are irreducible" (L79), "*most* series are irreducible" (L35), "a generalization of randomness" (L77). Tuples written with angle brackets $\langle \ldots \rangle$ and called "the tuple" (L52, L343) or just written (L256, L260). "is $\mathbb{Q}$-linearly independent set" (missing article; source or transcription).

### A.27 $\mathrm{Lim}(b)$ — accumulation points of the closed support

- Kind: own notation; §3, p.8, L286.
- Verbatim: "Let $\mathrm{Lim}(b)$ be the set of all accumulation points in $\mathrm{cl}(\mathrm{supp}(b))$."
- Notes: 5 occurrences, all in Cor 3.7, 3.8 as "$\mathrm{supp}(b_i) \setminus \mathrm{Lim}(b_i)$" (the isolated points of the support). Words used: "accumulation points" (L177, L286 twice), "accumulate to $0$" (L177), "limit point" (L284: "it is a limit point"), "isolated" (6: "isolated within the set", "the isolated points themselves have order type $v_J(b_1^{|\gamma_{1,j}})$" L284, "we can find $\beta$, $\beta'$ isolated" L284, "$\gamma_0 \in S$ be an isolated point arbitrarily close to $0$" L397, "Since $\gamma_0$ is isolated" L397).

### A.28 $A_\alpha$

- Kind: own definition; Definition 4.1, §4, p.8, L306.
- Verbatim: "**Definition 4.1.** We let $A_\alpha$ be the $K$-vector space generated by $J_\alpha$ and all the elements of the form $bc$ where $b$, $c$ are principal not in $K$ and $\deg_J(bc) = \alpha$; in other words, $A_\alpha := J_\alpha + \mathrm{Span}_K(R_\alpha)$."
- Remark 4.2 (L308): "As observed in the introduction, if $\alpha$ is additively principal, then $R_\alpha = \varnothing$, hence $A_\alpha = J_\alpha$."
- Notes: 24 occurrences ($A_\alpha$, $A_{\alpha+1}$, $A_{\deg_J(q)}$, $A_{\omega^{\alpha_1}+\omega^{\alpha_2}}$). Phrases: "$K$-linearly independent over $A_\alpha$" (L312), "$b \in A_\alpha$", "$b \notin A_\alpha$" (L333), "$\mod A_\alpha$" (L341), "in the $K$-linear span of $\{q_1, \ldots, q_\ell\} \cup A_\alpha$" (L341), "a non-trivial $K$-linear dependence over $A_\alpha$" (L341), "$\mathrm{rv}(A_\alpha)$ has infinite co-dimension" (L329, L420).

### A.29 The property $(*)_\alpha$

- Kind: own definition; §4, p.8, L310–L314.
- Verbatim: "We define the following property for $\alpha < \omega_1$.
  $(*)_\alpha$ For every $n \in \mathbb{N}$ and $b_1, \ldots, b_n \in P_\alpha$ such that $\mathrm{Q}(b_1, \ldots, b_n)$ holds we have that $b_1, \ldots, b_n$ are $K$-linearly independent over $A_\alpha$.
  Note in particular that if the above property holds, then $b_1, \ldots, b_n$ are irreducile. We shall verify that $(*)_\alpha$ implies $(*)_{\alpha+\beta}$ for certain choices of $\beta$, and thus prove that the property holds for many ordinals. First, we observe the following easy base case."
- Notes: 11 occurrences; "$(*)_{\omega^\beta}$ is true for every $\beta$" (L316), "$(*)_\alpha \Rightarrow (*)_{\alpha+1}$" (L324), "$(*)_{\omega^{\alpha_1} + \omega^{\alpha_2}}$ holds for all $\alpha_1 \geq \alpha_2$" (L351), "which contradicts $(*)_\alpha$" (L347), "this contradicts $(*)_{\omega^{\alpha_1} + \omega^{\alpha_2}}$" (L507), "in this induction we do not obtain $(*)_\alpha$, but irreducibility only" (L427). "irreducile" is a typo for "irreducible" (L314). "$K$-linearly independent over $A_\alpha$" = no nontrivial $K$-combination lies in $A_\alpha$.

### A.30 $\mathrm{Span}_K(\cdot)$, $\mathrm{Span}_{\mathbb{Q}}(\cdot)$; "infinite co-dimensional"; "linearly independent over"

- Kind: notation fixed in passing; Cor 1.6 (L67), Conj 1.10 (L85), Cor 3.7/3.8 (L291, L298), Def 4.1 (L306).
- Verbatim (Cor 1.6, L67): "**Corollary 1.6.** *Let $\alpha$ be as in Theorem 1.4(2). Then $\mathrm{Span}_K(R_\alpha)$ is infinite co-dimensional in $\mathrm{Span}_K(P_\alpha)$ as a $K$-vector space.*"
- Verbatim (Cor 3.7, L291): "$\bigcup_{i=1}^n \mathrm{supp}(b_i) \setminus \mathrm{Lim}(b_i)$ is $\mathbb{Q}$-linearly independent over $\mathrm{Span}_{\mathbb{Q}}(\bigcup_{i=1}^n \mathrm{Big}(b_i))$."
- Notes: "co-dimension"/"co-dimensional" hyphenated, 4 occurrences ("is infinite co-dimensional in ... as a $K$-vector space" L67, L85; "has infinite co-dimension as a $K$-vector subspace of $\mathrm{RV}_J^\alpha$" L329; "has an infinite co-dimension as a vector space in $\mathrm{RV}_J^\alpha$" L420). "$\mathbb{Q}$-linearly independent over $\mathrm{Span}_{\mathbb{Q}}(X)$" = independent modulo the span. Hyphenated compounds: "$K$-linearly independent", "$\mathbb{Q}$-linearly independent", "$K$-linear span", "$K$-linear dependence", "$J_\alpha$-linear combinations", "$K$-vector space", "$K$-vector subspace", "$J_{\omega^{\alpha_1}}$-module".

### A.31 Normal form of a series — attributed to [LM24, Def. 3.3.6] (see B.9); used in the proof of Prop 3.2: "Let $a = \sum_{i=1}^s a_i t^{\delta_i} + a_0$ be the normal form of $a$, then $a_0 \in K^\times$" (L249).

### A.32 $K^\times$; $K \setminus \{0\}$; names of scalar coefficients

- Kind: notation in passing. $K^\times$ (5 occurrences: L249, L337, L343, L407, L469) for nonzero field elements; also "$P_0 = K \setminus \{0\}$" (L39). Scalars in linear combinations are named $\lambda_i$ (L337, L405), $k_i$ / $k_{i,j}$ (L262, L278, L407, L477), $\mu_i$ (L393, L401), $\delta_i$ (L343 "$\delta_1, \ldots, \delta_k \in K^\times$"; but L377 "$\delta_1, \ldots \delta_k \in J_{\omega^{\alpha_1}}$" — the same letter for ring coefficients). "not all zero" (L262, L280, L353, L377, L393, L401), "not both $0$" (L465, L477, L507).

### A.33 $\omega_1$; countability of all invariants

- Kind: remark fixing the range of invariants; §2, p.6, L215.
- Verbatim: "We also remark that all well ordered subsets of $\mathbb{R}$ are countable, thus $\mathrm{ot}$, $v_J$, $\deg_J$ and $\deg$ all take values below $\omega_1$, the first uncountable ordinal. One can easily verify that all values below $\omega_1$ are in the images of $\mathrm{ot}$, $\deg_J$, $\deg$ (but not $v_J$ which is always of the form $\omega^\alpha$)."
- Notes: hence $(*)_\alpha$ is defined "for $\alpha < \omega_1$" (L310) and $\mathrm{RV}_\nu$ is "the union over $\alpha < \omega_1$" (L219).

### A.34 The decomposition $b = \sum_{i=1}^m p_i q_i + r$, $b = pq + r$, and the letters $p, q, r$

- Kind: convention (recurring shape of a reducibility witness); Thm 1.4 (L63), proof of Prop 4.4 (L337), §4.2 (L353), Prop 4.15 (L455), Prop 4.16 (L465), Cor 4.17 (L507).
- Verbatim (Thm 1.4, L63): "*If $\alpha$ is of the form (2), then there are no principal series $p_1, \ldots, p_m$, $q_1, \ldots, q_m$, $r$ such that $b = \sum_{i=1}^m p_i q_i + r$, where $\mathrm{ot}(r) < \omega^\alpha$ and for every $1 \leq i \leq m$ we have $1 < \mathrm{ot}(p_i) \leq \mathrm{ot}(q_i)$, $\mathrm{ot}(p_i q_i) = \omega^\alpha$ (that is, $p_i q_i \in R_\alpha$).*"
- Verbatim (L337): "Write $b = \sum_{i=1}^m p_i q_i + r$ where $\deg_J(q_i) \geq \deg_J(p_i) > 0$, $\deg_J(p_i q_i) = \alpha + 1$ and $r \in J_{\alpha+1}$."
- Verbatim (L455): "Suppose by contradiction that $b = pq + r$ where $p$ and $q$ are not in $J + K$ and $\deg_J(r) < \deg_J(b)$. After possibly swapping $p$ and $q$, we may assume that $\deg_J^p(q) > \deg_J^p(p)$, and so that $\deg_J^p(p) = \omega^{\alpha_{n+1}} > 1$. Here $\deg_J^r(b) = \alpha$."
- Notes: $p$ is the factor of smaller (or equal) degree, $q$ the larger; $r$ the remainder/error term of lower degree; $r_\gamma$ (L457, L471) for a $\gamma$-dependent remainder. General series are $b$ (main), $c$, $a$, $d$, $e$; $u_i$ for modified series (L262); classes in $\mathrm{RV}$ are capitals $A, B, C$, $C_i$ (L239, L249).

### A.35 "$= \ldots \mod J_\alpha$" — congruence written with "$=$"

- Kind: convention. Verbatim examples: "$b^{|\gamma} = \sum_{i=1}^m p_i^{|\gamma} q_i + q_i^{|\gamma} p_i \mod J_\alpha$" (L339); "$(cd)^{|\gamma} = cd^{|\gamma} \mod J_{\deg_J(c)}$" (L385, L389); "$ac = d \mod J$" (L249). The "$\equiv$" sign appears only in the definition of $v_J$ (L122) and Prop 2.9 (L183). 15 occurrences of "mod J". In prose "modulo" appears once, non-mathematically ("modulo some set-theoretic details", L23).

### A.36 $K[\mathbb{R}^{\leq}]$ — series with finite support

- Kind: notation in passing; L221 ("$\mathrm{RV}_{\deg}^0 \cong K[\mathbb{R}^{\leq}]$, the space of the series with finite support"), L233 ("a maximal divisor in $K[\mathbb{R}^{\leq}]$ (the series with finite support)"), L239, L249 ("Hence $a \in K[\mathbb{R}^{\leq}]$, and therefore $a \in K$"). Single square brackets for finite sums (group-ring style), with superscript "$\leq$" and no "0" as transcribed — possibly $\mathbb{R}^{\leq 0}$ in the source (unverified).

### A.37 Names "convolution formula" and "Leibniz rule" for Props 2.9 and 2.10 — see B.15, B.16.

### A.38 "close enough to $0$" / "sufficiently close to $0$" / "arbitrarily close to $0$" / "sufficiently small"

- Kind: convention of phrasing for eventual behaviour as $\gamma \to 0^-$. Counts: "close enough to $0$" 13, "sufficiently close to $0$" 3, "arbitrarily close to $0$" 7, "sufficiently small" 2 ("for some $\delta < 0$ sufficiently small", L371; "When $\gamma$ is sufficiently small", L485 — "small" here means close to $0$ from below, i.e. of small absolute value). Models: "Then for every $\gamma$ sufficiently close to $0$ we have $(bc)^{|\gamma} = b^{|\gamma} c + c^{|\gamma} b + r$" (L187); "for every $\gamma \in \Gamma$ close enough to $0$ we have" (L373, L457, L461, L471); "$\gamma_1, \ldots, \gamma_k \in \mathrm{Res}(b)$ arbitrarily close to $0$" (L343); "$\gamma_0$ arbitrarily close to $0$" (L393, L401); "as soon as $\gamma_1, \ldots, \gamma_k$ are sufficiently close to $0$" (L347); "for every $\gamma \in \mathrm{Res}(c)$ close enough to $0$" (L407).

### A.39 $M_{n\times n}(K)$, $A[i,j]$, $\overline{v}$, $\overline{0}$

- Kind: local notation, proof of Prop 3.4 (L262): "We define $A \in M_{n \times n}(K)$ such that for every $1 \leq i, j \leq n$ we have $A[i,j] = u_{j\gamma_i}$, and let $\overline{v} = [k_1, \ldots, k_n] \neq \overline{0}$. Then we have $A\overline{v} = \overline{0}$ and hence $\det(A) = 0$. Hence, the elements of $A$ are not algebraically independent, a contradiction."

### A.40 "element" vs "series"

- Kind: usage convention. The objects are "series" in definitions and theorems; "element(s)" is used when the ring-theoretic role is foregrounded: "Irreducible principal elements" (§4 title, L302), "non-principal elements" (L191, L235), "principal elements" (L235), "irreducible elements of degree $\alpha$" (L221), "reducible elements in $\mathrm{RV}_J^\alpha$" (L328, L419), "two elements of $K((\mathbb{R}^{\leq 0}))$" (L138), "elements of ordinal value $\omega^\alpha$" (L304), "an element in $K$" (L233), "all the elements of the form $bc$" (L306), "Existence of prime elements" (title of [Pit01], L532). But "non-principal series" (L245) and "irreducible series" (L23, L33) also occur.

### A.41 "irreducible(s)", "reducible", "prime", "divisor", "divides", "unit", "factored into irreducibles"

- Kind: ring-theoretic vocabulary used without definition (Part C), but the *forms* are the paper's choice: noun "irreducibles" ("admits irreducibles of order type $\alpha$" L7; "to find irreducibles in rings of the form" L25; "cannot be factored into irreducibles" L27); adjective "irreducible series" (L23, L33), "irreducible principal series" (L69), "irreducible elements" (L221); "then both $b$ and $b+1$ are irreducible" (L31); "$b$ and $b+1$ are prime" (L33); "all divisors of $b \in P_\alpha$ are principal" (L44); "a maximal divisor" (L233); "$p(b)$ divides $\mathrm{rv}(b)$" (L243); "$p(b)$ must be a unit" (L243); "$\mathrm{rv}(b^{|\gamma})$ is not irreducible" (L459); "Hence, $B$ is irreducible" (L249). "irreducibility" as the topic noun: "Regarding irreducibility" (L23), "how to use irreducibility in $K((\mathbb{R}^{\leq 0}))$" (L25), "prove irreducibility results for non-principal elements" (L191), "to obtain irreducibility for non-principal elements using irreducibility results for principal elements" (L235), "we may deduce irreducibility by a different induction" (L427), "but irreducibility only" (L427).

### A.42 "$\mathrm{rv}(b)$ irreducible" and "irreducible in $\mathrm{RV}_J^\alpha$" — irreducibility of classes

- Kind: own usage (never defined). Verbatim (Cor 4.5, L328): "*For every $b \in P_\alpha$ with $\mathrm{Q}(b)$ we have that $b$, $\mathrm{rv}(b)$ are irreducible and cannot be represented as a sum of reducible elements in $\mathrm{RV}_J^\alpha$.*" Verbatim (proof of Prop 3.2, L249): "By [LM24, Lem. 7.1.1] it is enough to prove that $\frac{\mathrm{rv}(b)}{p(\mathrm{rv}(b))}$ is irreducible. Let $B = \frac{\mathrm{rv}(b)}{t^{\gamma_m}}$ and suppose that $AC = B$. Then there exist some $a$, $c$, $b'$ such that $\mathrm{rv}(a) = A$, $\mathrm{rv}(b') = B$, $\mathrm{rv}(c) = C$ and $ac = b'$." Division of classes by $t^{\gamma_m}$ and the fraction notation $\frac{\mathrm{rv}(b)}{p(\mathrm{rv}(b))}$ are used without comment.

---

## Part B — What it reuses

Every attributed borrowing, in order of first appearance, with the attribution quoted. The paper's citation keys are: [Ber00], [BKK06], [Con76], [Gon86], [Hah07], [LM17], [LM24], [MR93], [Pit01], [PS06] (References, L521–L533). Attributions are placed in parentheses immediately after a result label ("**Fact 2.2** ([Ber00, Lem. 5.5, Thm. 9.7])", "**Definition 2.1** ([LM24, Def. 3.3.6])", "**Theorem 1.1** ([Ber00, Thm. 10.5])") or in-line ("([Ber00, p. 558])", "by [Ber00, Lem. 4.7]", "By [LM24, Prop. 5.5.1]"). Pinpoint citations give result type and number: "Thm.", "Cor.", "Lem.", "Def.", "Rem.", "Prop.", "p." (page).

### B.1 The field $K((G))$ — [Hah07]

- Verbatim (L21): "It is well known that the collection $K((G))$ of such series forms a field, when equipped with the obvious operations of sum and product [Hah07]."
- Status: result reused unchanged; the name "generalised power series" is the paper's own (L21, "Call ...") and is not attributed to Hahn.

### B.2 Integer parts and real closed fields — [MR93]

- Verbatim (L23): "for instance, $\mathbb{Z} + \mathbb{R}((G^{<0}))$ is always an integer part of the field $\mathbb{R}((G))$, which in turn implies that every real closed field admits an integer part [MR93]."
- Status: background result; the term "integer part" is not defined (Part C).

### B.3 Conway's conjecture; omnific integers — [Con76]

- Verbatim (L23): "Regarding irreducibility, the first question was posed by Conway [Con76], who conjectured that the series $1 + \sum_n t^{-\frac{1}{n}}$ is irreducible in the ring of omnific integers, which can be written in the form $\mathbb{Z} + \mathbb{R}((G^{<0}))$ (modulo some set-theoretic details which are irrelevant here)."
- Status: the conjecture is reported, the series is written in the paper's own $t$-notation (Conway's $\omega$-notation is not used). "Conway's conjecture" (L25). "omnific integers" is a keyword (L13) and is used without definition.

### B.4 Proof of Conway's conjecture; reduction to $K((\mathbb{R}^{\leq 0}))$ — [Ber00], [Gon86]

- Verbatim (L25): "Conway's conjecture was proved by Berarducci [Ber00]. A crucial part of the argument, first suggested by Gonshor [Gon86], is the reduction to the ring $K((\mathbb{R}^{\leq 0}))$. In this paper, we work exclusively in this ring."
- Status: the *reduction* is credited to Gonshor as a suggestion and to Berarducci as the argument. The paper adopts the ring $K((\mathbb{R}^{\leq 0}))$ unchanged as its sole setting.

### B.5 Passing from $K((\mathbb{R}^{\leq 0}))$ to $Z + K((G^{<0}))$ — [BKK06, LM24]

- Verbatim (L25): "We refer the reader to [BKK06, LM24] for extensive considerations on how to use irreducibility in $K((\mathbb{R}^{\leq 0}))$ in order to find irreducibles in rings of the form $Z + K((G^{<0}))$."
- Status: delegated; no term taken. This is the only citation of [BKK06].

### B.6 Berarducci's main theorem — Theorem 1.1 = [Ber00, Thm. 10.5]

- Verbatim (L27–L31): "Berarducci's main result reads as follows.
  **Theorem 1.1** ([Ber00, Thm. 10.5]). *If $b \in K((\mathbb{R}^{\leq 0})) \setminus J$ (equivalently, $b \in K((\mathbb{R}^{\leq 0}))$ not divisible by $t^\gamma$ for any $\gamma < 0$) has order type $\omega^{\omega^\alpha}$ for some ordinal $\alpha$, then both $b$ and $b+1$ are irreducible.*"
- Status: restated in the paper's own notation ($J$, $\mathrm{ot}$), with the parenthetical gloss "(equivalently, ... not divisible by $t^\gamma$ for any $\gamma<0$)" added by the paper. The phrase "reads as follows" introduces a restated result.

### B.7 Irreducibles of order type $\omega^2$, $\omega^3$; primes of order type $\omega$ — [PS06], [LM17], [Pit01]

- Verbatim (L33): "Further irreducible series of order types $\omega^2$ and $\omega^3$ were exhibited in [PS06] and in [LM17]; in parallel, Pitteloud [Pit01] proved that for $b$ of order type $\omega$, $b$ and $b+1$ are prime, answering a question of Gonshor."
- Verbatim (Remark 1.7, L69): "As a special case, we find irreducible principal series of order types $\omega^2$ and $\omega^3$, as in respectively [PS06] and [LM17]."
- Verbatim (abstract, L7): "we enlarge the family of ordinals $\alpha$ of non-additively principal Cantor degree for which $K((\mathbb{R}^{\leq 0}))$ admits irreducibles of order type $\alpha$ far beyond $\alpha = \omega^2$ and $\alpha = \omega^3$ known prior to this work."
- Status: results reported; "prime" is used for Pitteloud's result and never for the paper's own (the paper proves irreducibility only). "exhibited", "proved", "answering a question of Gonshor" are the verbs.

### B.8 Berarducci's analysis on principal series — [Ber00, Cor. 9.9]; [LM17, Cor. 4.6]

- Verbatim (L41–L45): "By Berarducci's analysis on principal series, all series in $P_\alpha$ satisfy the following properties: for all ordinals $\alpha$, $\beta$, $\gamma$,
  1. $P_\alpha \cdot P_\beta \subseteq P_{\alpha \oplus \beta}$ ([Ber00, Cor. 9.9]);
  2. all divisors of $b \in P_\alpha$ are principal ([LM17, Cor. 4.6]);
  3. $R_\alpha := \ldots$"
- Status: (1) from Berarducci, (2) from L'Innocente–Mantova 2017, (3) the paper's own consequence. The word "principal" for series is thereby associated with Berarducci ("Berarducci's analysis on principal series"), though Definition 1.2 itself carries no citation. Immediately after (L47): "One can easily deduce that every principal $b$ of order type $\omega^{\omega^\alpha}$ is irreducible" — the paper's re-derivation of Theorem 1.1 for principal series.

### B.9 Normal form of a series — Definition 2.1 = [LM24, Def. 3.3.6]; uniqueness [LM24, Prop. 3.3.7]

- Verbatim (L105–L116): "**Definition 2.1** ([LM24, Def. 3.3.6]). Given $b \in K((\mathbb{R}))$, we call the sum $$b = b_1 t^{x_1} + \cdots + b_n t^{x_n}$$ the **normal form** of $b$ when:
  - $x_1 \leq \cdots \leq x_n$;
  - $b_i$ is principal for all $i = 1, \ldots, n$;
  - $\mathrm{ot}(b_1) \leq \cdots \leq \mathrm{ot}(b_n)$;
  - $x_i + \mathrm{supp}(b_i) < x_{i+1} + \mathrm{supp}(b_{i+1})$ for all $i = 1, \ldots, n-1$.
  By [LM24, Prop. 3.3.7], every $b \in K((\mathbb{R}^{\leq 0}))$ has a unique normal form."
- Status: taken unchanged (as far as this paper shows) and named "normal form" (bold). Note the definition is stated for $b \in K((\mathbb{R}))$ (the whole field) while uniqueness is stated for $K((\mathbb{R}^{\leq 0}))$. Conventions in the form: exponents $x_1 \le \cdots \le x_n$ non-decreasing (smallest exponent first); "$x_i + \mathrm{supp}(b_i)$" is a translate of a set; "$<$" between sets means every element of the left is below every element of the right (not stated). "normal form" occurs 10 times (including "Cantor normal form" 7+2+1 — so the bare "normal form" of a series occurs at L109, L116, L249).

### B.10 Ordinal value $v_J$ — [Ber00, p. 558]; its properties — Fact 2.2 = [Ber00, Lem. 5.5, Thm. 9.7]; values are $\omega^\alpha$ — [Ber00, Rem. 5.3]

- Verbatim (L120–L130): "Given $b \in K((\mathbb{R}^{\leq 0}))$, the **ordinal value** of $b$ ([Ber00, p. 558]) is $$v_J(b) := \ldots$$ The keystone of [Ber00] is that $v_J$ is a multiplicative semi-valuation.
  **Fact 2.2** ([Ber00, Lem. 5.5, Thm. 9.7]). *For all $b, c \in K((\mathbb{R}^{\leq 0}))$ we have:*
  - *$v_J(b + c) \leq v_J(b) \oplus v_J(c)$;*
  - *$v_J(bc) = v_J(b) \odot v_J(c)$;*
  - *$v_J(b) = 0$ if and only if $b \in J$.*"
- Verbatim (L132): "The values of $v_J$ are all of the form $\omega^\alpha$ ([Ber00, Rem. 5.3]), thus we add the following notation: let $\deg_J(b)$ denote the Cantor degree of $v_J(b)$".
- Status: name "ordinal value" and symbol $v_J$ taken from Berarducci (the paper does not say whether Berarducci's symbol is the same; it cites a page, not a definition number); the case-formula is the paper's restatement. The paper's own addition is $\deg_J$ ("we add the following notation", A.13). Results imported as "Fact" with pinpoint citations.

### B.11 The "few cancellation" claim of [Ber00] — declined (see F.1)

- Verbatim (L138): "We note that to prove $\mathrm{ot}(bc) = \mathrm{ot}(b) \odot \mathrm{ot}(c)$ for $b$, $c$ principal, it was stated with no proof in [Ber00] that there are "few cancellation" in the product of two elements of $K((\mathbb{R}^{\leq 0}))$. We observe that not only the above is not required (and in fact not used) in order to prove the multiplicativity of $v_J$, it is neither true."

### B.12 Critical point $\mathrm{crit}(b)$ — [Ber00, Def. 10.2] (contrasted with the paper's $\mathrm{crit}_J$; see F.2)

- Verbatim (Remark 2.6, L155): "One should not confuse this with the notion of *critical point* $\mathrm{crit}(b)$, which is the minimum $\gamma \in \mathbb{R}^{\leq 0}$ such that $v_J(b^{|\gamma})$ is maximum possible [Ber00, Def. 10.2]. For example for $b = \sum_{n \in \mathbb{N}} t^{-1-\frac{1}{n+1}} + \sum_{n \in \mathbb{N}} t^{-\frac{1}{n+1}} + \sum_{n \in \mathbb{N}} t^{-2-\frac{1}{n+1}}$, we have that $v_J(b) = \omega = v_J(b^{|-1}) = v_J(b^{|-2})$, and one can verify that $\mathrm{crit}(b) = -2$ and $\mathrm{crit}_J(b) = -1$."
- Status: Berarducci's "critical point" $\mathrm{crit}(b)$ is kept with its name and symbol for Berarducci's notion; the paper's own different notion is given the distinct name "$J$-critical point" and symbol $\mathrm{crit}_J$.

### B.13 Principal value and residual value — [Ber00, Def. 6.4]

- Verbatim (L157–L162): "We define ([Ber00, Def. 6.4]): 1. $v_J^p(b) := \omega^{\omega^{\beta_n}} = $ the **principal value** of $b$, 2. $v_J^r(b) := \omega^{\omega^{\beta_1}} \cdots \omega^{\omega^{\beta_{n-1}}} = $ the **residual value** of $b$."
- Status: names taken from Berarducci; the symbols $v_J^p$, $v_J^r$ are presented as the paper's (it says "We define ([Ber00, Def. 6.4])" — attribution of the notion, not necessarily of the symbol). Then re-symbolled to $\deg_J^p$, $\deg_J^r$ "to remove the base $\omega$" (L164; F.4).

### B.14 $\mathrm{Res}(b)$ = Berarducci's $X(b)$ — [Ber00, Def. 6.6] (see F.3)

- Verbatim (L175): "The set of all these point $\mathrm{Res}(b)$ was defined in [Ber00, Def. 6.6] (where it is called $X(b)$)."
- Status: set taken, renamed "residual point(s)" and re-symbolled $\mathrm{Res}(b)$; the paper explicitly records Berarducci's symbol $X(b)$.

### B.15 Convolution formula — Proposition 2.9 = [Ber00, Lem. 7.5(2)]

- Verbatim (L179–L183): "It turns out that translated truncations behave like a sort of 'generalised coefficients', as they satisfy the following equation.
  **Proposition 2.9** ([Ber00, Lem. 7.5(2)]). *For all $a, b \in K((\mathbb{R}^{\leq 0}))$ and $\gamma \in \mathbb{R}^{\leq 0}$ we have:* $$(ab)^{|\gamma} \equiv \sum_{\delta + \varepsilon = \gamma} a^{|\delta} b^{|\varepsilon} \mod J \quad \text{(convolution formula)}.$$"
- Status: result taken from Berarducci, restated in the paper's translated-truncation notation, and labelled "(convolution formula)" inside the display. Invoked later as "Proposition 2.9 implies that" (L387), "By Proposition 2.9," (L489). The sum "$\sum_{\delta+\varepsilon=\gamma}$" ranges over pairs of reals; finiteness mod $J$ is not discussed.

### B.16 Leibniz rule — Proposition 2.10 = [Ber00, Lem. 7.7]

- Verbatim (L185–L187): "And one further more may obtain a kind of a Leibniz rule.
  **Proposition 2.10** ([Ber00, Lem. 7.7]). *Let $b, c \in K((\mathbb{R}^{\leq 0}))$ such that $\deg_J^p(b) \leq \deg_J^p(c)$. Then for every $\gamma$ sufficiently close to $0$ we have $(bc)^{|\gamma} = b^{|\gamma} c + c^{|\gamma} b + r$ where $\deg_J(r) < \deg_J^r(b) \oplus \deg_J(c) < \deg_J(bc)$.*"
- Status: result taken from Berarducci, restated with $\deg_J^p$, $\deg_J^r$ (the paper's notation). Called "a kind of a Leibniz rule"; invoked as "we have by Proposition 2.10" (L337), "We may now apply Proposition 2.10 and deduce that" (L373). The bound "$\deg_J^r(b) \oplus \deg_J(c)$" uses the natural sum.

### B.17 Degree of a series — Definition 2.12 = [LM24, p. 5]; degree is a multiplicative valuation — Fact 2.13 = [LM24, Thm. D]

- Verbatim (L193–L201): "**Definition 2.12** ([LM24, p. 5]). Given $b \in K((\mathbb{R}^{\leq 0}))$ with $b \neq 0$, let the **degree** of $b$, denoted by $\deg(b)$, be the Cantor degree of $\mathrm{ot}(b)$. We also let $\deg(0) := -\infty$. [...] In [LM24] it is proved by the 3rd and the 4th authors that the degree is an **multiplicative valuation** in the following sense:
  **Fact 2.13** ([LM24, Thm. D]). For all non-zero $b, c \in K((\mathbb{R}^{\leq 0}))$,
  1. $\deg(b + c) \leq \max\{\deg(b), \deg(c)\}$ (ultrametric inequality);
  2. $\deg(bc) = \deg(b) \oplus \deg(c)$ (multiplicativity);
  3. $\deg(b) = -\infty$ if and only if $b = 0$."
- Verbatim (L203): "This makes the degree is quite similar to $\deg_J$, but in a sense more precise: $\deg(b) = -\infty$ only when $b = 0$, whereas $\deg_J(b) = -\infty$ for all $b \in J$."
- Status: name "degree", symbol $\deg$, and the "degree valuation" (L191) taken from [LM24]; the paper adds (or restates) the convention $\deg(0) := -\infty$ ("We also let"). The three properties are labelled "(ultrametric inequality)", "(multiplicativity)". Reference to the authors by position: "the 3rd and the 4th authors".

### B.18 Properties of $\mathrm{RV}_{\deg}$ — [LM24] (unspecified)

- Verbatim (L221): "Thanks to $\mathrm{RV}_{\deg}$ and its properties proved in [LM24] we are able to find irreducible elements of degree $\alpha$ which are not principal, as we shall see in the following sections."
- Status: the $\mathrm{rv}$/$\mathrm{RV}$ notation itself (Def 2.15) is presented as the paper's own definition, while "its properties" are credited to [LM24]. Whether [LM24] uses the same symbols is not stated.

### B.19 Maximal finite-support divisor — [LM24, Prop. 5.5.1]

- Verbatim (L233): "By [LM24, Prop. 5.5.1], we know that every $b$ has a maximal divisor in $K[\mathbb{R}^{\leq}]$ (the series with finite support), which is unique up to a multiplication by an element in $K$."
- Status: result reused; the normalised divisor $p(b)$ is the paper's notation (A.25).

### B.20 Base of $\mathrm{RV}_J^\alpha$ generating $\mathrm{RV}_{\deg}^\alpha$ over $K[\mathbb{R}^{\leq}]$ — [LM24, Prop. 5.3.1]; the algorithm — [LM24, Rem. 5.4.7]; reduction to $\mathrm{rv}(b)/p(\mathrm{rv}(b))$ — [LM24, Lem. 7.1.1]

- Verbatim (L239–L243): "**Proof.** By [LM24, Prop. 5.3.1] we have that if $\{C_i\}_{i \in I}$ is a base for $\mathrm{RV}_J^\alpha$ then for every $B \in \mathrm{RV}_{\deg}^\alpha$ we have that $B = q_i C_i$ where $q_i \in K[\mathbb{R}^{\leq}]$ and $q_i \neq 0$ for finitely many $i \in I$. As $\{\mathrm{rv}(b_1), \ldots, \mathrm{rv}(b_m)\}$ is a part of a base of $\mathrm{RV}_J^\alpha$ then by the algorithm described in [LM24, Rem. 5.4.7] we have that $t^{\gamma_m} = \gcd(t^{\gamma_1}, \ldots, t^{\gamma_m})$ is a maximal divisor of finite support of $\mathrm{rv}(b)$, hence $p(\mathrm{rv}(b)) = t^{\gamma_m}$."
- Verbatim (L249): "By [LM24, Lem. 7.1.1] it is enough to prove that $\frac{\mathrm{rv}(b)}{p(\mathrm{rv}(b))}$ is irreducible."
- Status: three results reused inside proofs. "$B = q_i C_i$" is presumably "$B = \sum_i q_i C_i$" (Part G). Note "$\gcd$" of monomials and "maximal divisor of finite support" are used as if standard.

### B.21 Order type of supports and ordinal value — [Ber00, Lem. 4.7]; $\mathrm{Res}(b)$ has order type $v_J^p(b)$ and supremum $0$ — [Ber00, Lem. 6.8]

- Verbatim (L367–L369): "It follows by [Ber00, Lem. 4.7] that $$v_J(c) = \mathrm{ot}(c) \geq \mathrm{ot}(\mathrm{supp}(c) \cap [\gamma_0, 0)) \geq \omega^\beta \cdot \alpha.$$"
- Verbatim (L371): "while $\mathrm{ot}(\mathrm{Res}(b)) = \omega^{\omega^{\alpha_2}}$ and $\sup(\mathrm{Res}(b)) = 0$ by [Ber00, Lem. 6.8]."
- Status: results reused inside proofs, unchanged. (In the first, $c$ is principal, so $v_J(c) = \mathrm{ot}(c)$ is used without comment.)

### B.22 "techniques from [LM24]" (general)

- Verbatim (L71): "Combining the above result with techniques from [LM24], we are also able to produce irreducible series that are not principal, at least for certain order types."

### B.23 Keywords and MSC (front matter)

- Verbatim (L11–L13): "*2020 Mathematics Subject Classification.* Primary 13F25, 13F15, secondary 13A05, 03E10. *Key words and phrases.* omnific integers, surreal numbers, pre-Schreier domain, valued ring."
- Status: "pre-Schreier domain" and "valued ring" occur **only** here — nowhere in the body. "surreal numbers" occurs only here and in the [Gon86] title. These keywords appear to be inherited from the [LM24] framing rather than chosen for this paper's content.

### B.24 Reference list titles (the field's own spellings)

- [Ber00] "Factorization in generalized power series" (L521); [BKK06] "Primes and irreducibles in truncation integer parts of real closed fields" (L522); [Con76] *On numbers and games* (L523); [Gon86] *An introduction to the theory of surreal numbers* (L527); [Hah07] "Über die nichtarchimedischen Größensysteme" (L528); [LM17] "Factorisation of germ-like series" (L529); [LM24] "A factorisation theory for generalised power series and omnific integers" (L530); [MR93] "Every real closed field has an integer part" (L531); [Pit01] "Existence of prime elements in rings of generalized power series" (L532); [PS06] "Unique factorization in generalized power series rings" (L533).
- Note: the paper cites only one Pitteloud paper, as [Pit01], the "Existence of prime elements" one (J. Symbolic Logic 66(3)).

---

## Part C — What it assumes you have read

Notions from the field used without definition or citation. For each: the term, how the paper uses it, a representative quote, and a plain statement that the paper does not define it. Meanings I attach are inferences, not the paper's testimony.

### C.1 irreducible / irreducibles / irreducibility
- Used from the abstract on as the paper's central property of a series in $K((\mathbb{R}^{\leq 0}))$ (or of a class in $\mathrm{RV}$); never defined. Quote (L31): "then both $b$ and $b+1$ are irreducible." Quote (L47): "every principal $b$ of order type $\omega^{\omega^\alpha}$ is irreducible". The paper does not define it. Inference: the standard ring-theoretic sense (non-zero non-unit with no factorisation into two non-units); units of $K((\mathbb{R}^{\leq 0}))$ are implicitly $K^\times$ up to $J$-considerations (cf. L249 "$a \in K$" concluding irreducibility, and L243 "$p(b)$ must be a unit").

### C.2 reducible
- Used in "$R_\alpha := \{b \in P_\alpha : b \text{ is reducible}\}$" (L45) and "reducible elements in $\mathrm{RV}_J^\alpha$" (L328). Not defined. Inference: product of two non-units; in $R_\alpha$ it is made concrete as $P_\beta \cdot P_\gamma$ with $\beta, \gamma \ne 0$, i.e. "principal not in $K$" factors (L306).

### C.3 prime
- Only for Pitteloud's result (L33): "$b$ and $b+1$ are prime, answering a question of Gonshor." Not defined; the paper never proves primality.

### C.4 unit; divisor; divides; maximal divisor; gcd
- L243: "$p(b)$ must be a unit"; L44: "all divisors of $b \in P_\alpha$ are principal"; L233 "a maximal divisor in $K[\mathbb{R}^{\leq}]$"; L243 "$t^{\gamma_m} = \gcd(t^{\gamma_1}, \ldots, t^{\gamma_m})$". Not defined. Inference: maximal with respect to divisibility among finite-support divisors; $\gcd$ of monomials $t^{\gamma_i}$ in $K((\mathbb{R}^{\leq 0}))$ is $t^{\max \gamma_i}$ (here $t^{\gamma_m}$ since $\gamma_1 < \cdots < \gamma_m$).

### C.5 integer part
- L23: "$\mathbb{Z} + \mathbb{R}((G^{<0}))$ is always an integer part of the field $\mathbb{R}((G))$, which in turn implies that every real closed field admits an integer part [MR93]." Not defined. Inference: a discretely ordered subring $Z$ of an ordered field $F$ such that every element of $F$ is within distance $<1$ of an element of $Z$ (the standard sense, as in [MR93]).

### C.6 real closed field
- L7, L23. Not defined; standard.

### C.7 omnific integers; surreal numbers
- L23: "irreducible in the ring of omnific integers, which can be written in the form $\mathbb{Z} + \mathbb{R}((G^{<0}))$ (modulo some set-theoretic details which are irrelevant here)." Keywords L13. Not defined. Inference: Conway's ring $\mathbf{Oz}$ inside the surreal numbers $\mathbf{No}$, with $G = \mathbf{No}$ (a proper class, hence "set-theoretic details").

### C.8 ordered abelian group $G$
- L21. Not defined; standard. The paper passes immediately to $G = \mathbb{R}$.

### C.9 valuation; semi-valuation; multiplicative valuation; ultrametric inequality
- L124: "$v_J$ is a multiplicative semi-valuation"; L191 "the *degree valuation*"; L195 "the degree is an **multiplicative valuation** in the following sense:" followed by the three properties (L199–L201) with labels "(ultrametric inequality)" and "(multiplicativity)". The paper gives the *sense* for $\deg$ but never defines "semi-valuation" or says in what sense $v_J$ is one. Inference: "valuation" here is used loosely for an ordinal-valued map satisfying an ultrametric inequality for $+$ (w.r.t. $\oplus$ or $\max$) and multiplicativity for $\cdot$ (w.r.t. $\odot$ or $\oplus$), with values ordered *increasingly* with complexity (larger value = more complicated), the opposite of the usual valuation convention; "semi-" presumably because $v_J$ vanishes on the whole ideal $J$ rather than only at $0$ (cf. L203).

### C.10 pre-Schreier domain; valued ring
- Keywords only (L13). Not used, not defined.

### C.11 germ / germ-like
- "germ of $b$ at $\gamma$" is defined (A.15), but the word's background sense (and "germ-like series", [LM17] title, L529) is taken as known.

### C.12 "the reduction to the ring $K((\mathbb{R}^{\leq 0}))$"
- L25. The paper assumes the reader knows what this reduction is (from [Gon86], [Ber00]) and why irreducibility in $K((\mathbb{R}^{\leq 0}))$ transfers; it refers to [BKK06, LM24] for the transfer.

### C.13 "Berarducci's analysis on principal series"
- L41. Assumes familiarity with [Ber00] §§5–10 as a body of results on principal series.

### C.14 The ring structure of $\mathrm{RV}$ and irreducibility in it
- Products $AC = B$ of $\mathrm{RV}$-classes (L249), fractions $\frac{\mathrm{rv}(b)}{t^{\gamma_m}}$ (L249), "$\mathrm{rv}(b)$ irreducible" (L247 etc.), "$\mathrm{rv}(p(b)) = p(b)$" (L243). None of this is set up in the paper; it presupposes [LM24]'s treatment of $\mathrm{RV}$ as a (graded) ring. Inference: $\mathrm{RV}_{\deg} = \bigoplus_\alpha \mathrm{RV}^\alpha_{\deg}$ with multiplication induced by the series product (well defined by Fact 2.13(2)).

### C.15 "(that is, $p_i q_i \in R_\alpha$)"; "principal not in $K$"
- The equivalence between "$1 < \mathrm{ot}(p_i) \le \mathrm{ot}(q_i)$, $\mathrm{ot}(p_i q_i) = \omega^\alpha$ with $p_i, q_i$ principal" and membership of the product in $R_\alpha$ (L63) relies on (1)–(3) at L41–L45 and is stated as an aside.

---

## Part D — Generic machinery presupposed

Standard mathematics from outside the field, listed briefly. Choices among standard variants are quoted.

- **Ordinals, the class $\mathbf{On}$, classical ordinal arithmetic.** "We assume that the reader has familiarity with the class $\mathbf{On}$ of ordinal numbers and the classical (non-commutative) operations on them" (L89). Choice fixed: bold $\mathbf{On}$; classical operations written $+$, $\cdot$ / juxtaposition; $\omega$ for the first infinite ordinal; $\omega_1$ "the first uncountable ordinal" (L215). Finite ordinals are identified with natural numbers ($k \in \mathbb{N}$ as a Cantor normal form tail, L59; "$\alpha = n$", L331).
- **Cantor normal form.** Introduced with "Recall that" (L91) and then defined (A.10). Choice: powers of $\omega$ with repetitions, no integer coefficients.
- **Hessenberg natural operations.** Treated as standard but given "a minimal account" (A.9).
- **Well-orders, order types.** "well-ordered, namely every nonempty subset has a minimum" (L21). "all well ordered subsets of $\mathbb{R}$ are countable" (L215) — asserted as known.
- **Well-founded induction.** "Note that the above definition is obviously well founded." (L231); "we give the following definition by induction on $\deg_j(b_1)$" (L225); "We show by induction that $(*)_\alpha$ holds" (L333); "induction on the Cantor normal form of $\alpha$" (L304, L427).
- **Topology of $\mathbb{R}$.** closure $\mathrm{cl}(\cdot)$, "accumulation points", "limit point", "isolated", "accumulate to $0$", half-open intervals "$[\gamma_i, \gamma_{i+1})$", "$[\gamma_0, 0)$", closed "$[\delta, 0]$" (L365, L369, L371).
- **Linear algebra over a field.** $K$-vector spaces, "$K$-linearly independent", "linearly dependent", "a base" (not "basis", L239), "infinite co-dimension(al)", $\mathrm{Span}_K$, matrices $M_{n\times n}(K)$, $\det$, column vector $\overline{v}$ (L262).
- **$\mathbb{Q}$-linear independence of reals; algebraic independence over $\mathbb{Q}$.** Used in Definition 1.3 and §3 as the two "randomness" hypotheses; not defined. Choice: independence is "over $\mathbb{Q}$" (not over the prime field of $K$ in general, not over $\mathbb{Z}$).
- **Commutative algebra.** "ideal", "(proper) ideal" (L120), "generated by", "integral domain" (L377), "finitely generated $J_{\omega^{\alpha_1}}$-module" (L377), "quotient", "$K$-vector space", "ring", "subrings", "unit", "gcd", "characteristic 0" (L7).
- **Congruences.** "$\equiv \ldots \mod J$" and "$= \ldots \mod J_\alpha$" (A.35); "$\mod J + K$" (L122) for congruence modulo the subspace $J + K$.
- **Set notation.** $\{\ldots : \ldots\}$ set-builder with colon; $\varnothing$ for the empty set (L47, L282, L308, L441); "$\setminus$" and "$-$" for set difference; $\langle \ldots \rangle$ for tuples/families; $(\mathrm{rv}_J(b_i))_{1 \leq i \leq n}$ for an indexed family (L227); $\{C_i\}_{i \in I}$ (L239); $\overline{0}$ for the zero vector.
- **Natural numbers.** $\mathbb{N}$ with $0 \in \mathbb{N}$ (inferred, A.6). "$k \in \mathbb{N}$", "$n \in \mathbb{N}$", "$\mathbb{N}[\ldots]$" polynomial semiring (L101).
- **Convention for $-\infty$.** "$\deg_J(b) = -\infty$ when $b \in J$, and $\omega^{-\infty} = 0$" (L132); "$\deg(0) := -\infty$" (L193). Comparisons like "$\deg_J(r) < \deg_J(b)$" silently allow $-\infty$.
- **"$\sum_{\delta + \varepsilon = \gamma}$" over reals** (L183) — a formal convolution sum, finiteness mod $J$ presupposed.

---

## Part E — How it talks

Verbs, phrase templates and proof idiom, with model sentences quoted verbatim. Grouped by what is being talked about.

### E.1 Talking about series and their invariants

- A series *has* an order type / a degree: "has order type $\omega^{\omega^\alpha}$" (L31); "$t^{-\sqrt{2}} + t^{-1} + 1$ has degree $0$" (L195); "has degree $2$ while $\deg_J(b) = 1$" (L213). Also "of order type $\omega$" (L33), "series of ordinal value $\omega^\alpha$" (L343), "elements of ordinal value $\omega^\alpha$" (L304), "irreducible elements of degree $\alpha$" (L221).
- A series *is* principal / random / irreducible / reducible / in $P_\alpha$: "A series $b$ in $P_\alpha$ is said to be **principal**" (L37); "$b \in P_\alpha$ is random" (L61); "$b$ is reducible" (L45); "Let $b$ in $P_n$" (L65); "Let $b$ principal such that $\deg_J(b) = \alpha$ and $\mathrm{Q}(b)$" (L511); "for $b$, $c$ principal" (L221); "Pick $b$ principal with $\mathrm{Q}(b)$" (L455).
- Supremum of the support is said in words or as $\sup(b) = 0$: "the supremum of the support of $b$ ... is $0$" (L37); "the supremum of its support is $-1$" (L39); "such that $\sup(b) = 0$" (L73, L237); "is infinite with supremum $0$" (L467).
- Divisibility: "divisible by $t^\gamma$ for some $\gamma \in \mathbb{R}^{<0}$" (L27); "not divisible by $t^\gamma$ for any $\gamma < 0$" (L31); "$p(b)$ divides $\mathrm{rv}(b)$" (L243).
- Coefficients: "the coefficient of $t^{s_m + s_n}$ in $bc$ is" (L140); "the coefficient of $t^{\sup(d)}$ is $1$" (L233); "If we replace each coefficient $b_{i\gamma}$ with $0$ for $\gamma \in \mathrm{supp}(r)$" (L262); "Let $\mu_1, \ldots, \mu_\ell$ be the coefficients $\varepsilon_{1\gamma_0}, \ldots, \varepsilon_{\ell\gamma_0}$ respectively" (L397); "improve the coefficients $\delta_i$ so that they lie in $K$" (L377).
- Truncations: "$b^{|\gamma}$ for some arbitrary $\gamma \in \mathrm{Res}(b)$" (L353); "the series $b^{|\gamma}$ for $\gamma \in \Gamma$ lie in a finitely generated $J_{\omega^{\alpha_1}}$-module" (L377); "an enumeration of the exponents $\gamma_i$ such that" (L411) — the truncation points are called "exponents".
- Cancellation: "cancellations occurs on a set of order type" (L140); "For $\delta$ to cancel, there must be" (L282); "thus most of them must cancel out" (L284).
- "accumulate to $0$" (L177); "accumulation points of $\mathrm{cl}(\mathrm{supp}(b))$" (L177).

### E.2 Stating results

- Theorem hypotheses as "Let ... be such that ...": "*Let $b \in K((\mathbb{R}^{\leq 0}))$ be such that $\sup(b) = 0$ and $\mathrm{ot}(b) = m\omega^\alpha + \beta$, where $\alpha$ is as in Theorem 1.4, $m \in \mathbb{N}$ non-zero, and $\beta < \omega^\alpha$.*" (L73). "*Let $\alpha$ be an ordinal of the following forms:*" (L56). "*Let $\alpha$ be such that for every $c \in P_\alpha$ with $\mathrm{Q}(c)$ we have that $c$, $\mathrm{rv}(c)$ are irreducible.*" (L247).
- Conclusion "then $b$ is irreducible, and so is $b + r$": "*If $b \in P_\alpha$ is random, then $b$ is irreducible, and so is $b + r$ for any principal series $r$ of order type less than $\omega^\alpha$.*" (L61). "*then $b$ is irreducible and so is $b + r$ for any $r$ such that $\mathrm{ot}(r) < \omega^\alpha$ and $\sup(b + r) = 0$.*" (L73). "*Then $b$ is irreducible and so is $b + r$ for any series $r$ with $ot(r) < \omega^{\deg(b)}$.*" (L81).
- "we have that $b$, $\mathrm{rv}(b)$ are irreducible" (L328, L419, L453, L503, L511) — the pair "$b$, $\mathrm{rv}(b)$" with a comma, no "and".
- "*$(*)_\alpha \Rightarrow (*)_{\alpha+1}$.*" (L324) — a proposition stated as a bare implication. "*$(*)_{\omega^\beta}$ is true for every $\beta$.*" (L316). "*$(*)_{\omega^{\alpha_1} + \omega^{\alpha_2}}$ holds for all $\alpha_1 \geq \alpha_2$.*" (L351).
- "Then $\mathrm{Q}(b_1, \ldots, b_n)$ holds." (L293, L300, L264).
- Non-existence of decompositions: "*there are no principal series $p_1, \ldots, p_m$, $q_1, \ldots, q_m$, $r$ such that $b = \sum_{i=1}^m p_i q_i + r$, where ...*" (L63).
- Co-dimension statements: "*$\mathrm{Span}_K(R_\alpha)$ is infinite co-dimensional in $\mathrm{Span}_K(P_\alpha)$ as a $K$-vector space.*" (L67).
- Imported results are labelled "Fact" (Fact 2.2, Fact 2.13) when quoted as black boxes, but "Theorem 1.1 ([Ber00, Thm. 10.5])", "Proposition 2.9 ([Ber00, Lem. 7.5(2)])", "Proposition 2.10 ([Ber00, Lem. 7.7])", "Definition 2.1 ([LM24, Def. 3.3.6])", "Definition 2.12 ([LM24, p. 5])" when restated in the paper's notation. Own results: Theorem (1.4, 1.8), Corollary, Proposition, Lemma, Definition, Remark, Example, Conjecture.
- Conjectures: "We conjecture that in fact all random series are irreducible, and more precisely, we expect the following to hold." (L79). "**Conjecture 1.9.** *Suppose that ... Then ...*" (L81).
- Announcing results: "In the current work we prove the following:" (L54); "We will show that, in an appropriate sense, *most* series are irreducible for a wide class of order types, and give explicit examples of such series." (L35); "In this paper we enlarge the family of ordinals $\alpha$ ... for which $K((\mathbb{R}^{\leq 0}))$ admits irreducibles of order type $\alpha$" (L7); "we are also able to produce irreducible series that are not principal, at least for certain order types" (L71); "we are able to find irreducible elements of degree $\alpha$ which are not principal" (L221).
- Wrapping up: "The above includes the conclusions of Theorems 1.4, 1.8 for the ordinals of the form $\alpha = \omega^{\alpha_1} + \omega^{\alpha_2} + k$." (L423); "This concludes the proofs of Theorems 1.4, 1.8." (L517).

### E.3 Invoking results and constructions

- "By Proposition 2.10" / "we have by Proposition 2.10" (L337); "We may now apply Proposition 2.10 and deduce that for every $\gamma \in \Gamma$ close enough to $0$ we have" (L373); "Proposition 2.9 implies that" (L387); "By Proposition 2.9," (L489); "By Lemma 4.14, for every $\gamma \in \Gamma$ close enough to $0$ we have" (L457); "then by Lemma 4.11 there exist" (L477); "By a further application of Lemma 4.9" (L489); "with the former implied by Lemma 4.9" (L489); "thus by Lemma 4.9 we have" (L387); "we can ensure thanks to Lemma 4.12 that" (L411); "Note that by Lemma 4.8, $\Gamma$ has order type" (L457); "Using Lemma 4.11, we obtain some $\gamma_0$" (L401).
- Citing the literature inside a proof: "By [LM24, Prop. 5.3.1] we have that" (L239); "by the algorithm described in [LM24, Rem. 5.4.7] we have that" (L243); "By [LM24, Lem. 7.1.1] it is enough to prove that" (L249); "It follows by [Ber00, Lem. 4.7] that" (L367); "by [Ber00, Lem. 6.8]" (L371); "By [LM24, Prop. 5.5.1], we know that" (L233); "By [LM24, Prop. 3.3.7], every $b$ ... has a unique normal form" (L116).
- Chaining results: "Combining with Proposition 4.4 and with Proposition 3.2 we obtain:" (L415); "Combining with Proposition 4.15 we obtain:" (L509); "By Proposition 3.2, we obtain the following:" (L513); "the conclusion follows from Propositions 4.7, 4.15; for $\alpha_3 = 0$, from Corollary 4.13" (L505); "The induction base is $\alpha = \omega^\beta$, thus Proposition 4.3. The induction step is Proposition 4.4." (L333).
- "as in the proof of Proposition 4.15" (L469); "as observed in the proof of Proposition 4.15" (L467); "we continue as in the proof of Proposition 4.15" (L507); "As observed in the introduction" (L308); "By Berarducci's analysis on principal series" (L41).
- Constructing: "we find a large $\Gamma \subseteq \mathrm{Res}(b)$, namely ..., on which we have ..." (L355); "Let $\Gamma = \mathrm{Res}(b) \setminus \mathrm{Big}^\alpha(r)$." (L457); "enumerate $\{\gamma : \deg_J(c^{|\gamma}) \geq \beta\}$ as $\{\gamma_i : i < \alpha\}$" (L363); "Pick some $\delta_1, \ldots, \delta_k \in K^\times$ and $\gamma_1, \ldots, \gamma_k \in \mathrm{Res}(b)$ arbitrarily close to $0$ such that" (L343); "Write $b = \sum_{i=1}^m p_i q_i + r$ where" (L337, L353); "Expanding the definition of $b$, we find that the tuple ... is linearly dependent over $A_\alpha$" (L343); "after rearranging the indices, we may write" (L341); "after reordering the $b_i$'s" (L409); "We arrange the enumeration so that $\alpha_{\ell+1} < \alpha_\ell$" (L441).

### E.4 Proof idiom

- Openers: "**Proof.**" then "Suppose by contradiction that" (L262, L337, L409, L455, L507), "suppose by contradiction that there are" (L276), "Let $c$, $\beta$ as in the assumptions" (L363), "For simplicity assume $b_1, \ldots, b_n \in P_{\deg_J(b_1)}$" (L268), "Pick $b$ principal with $\mathrm{Q}(b)$" (L455), "Suppose $\deg_J(pq) = \sum_{i=1}^n \omega^{\alpha_i}$ where" (L435). Deferred proofs are headed "**Proof of Corollary 4.5.**" (L333), "**Proof of Proposition 4.4.**" (L335); a long proof spread over several lemmas ends with "$\square_{\text{Prop. 4.7}}$" (L413).
- Reductions: "After possibly swapping $p$ and $q$, we may assume that" (L455); "without loss of generality, $a \in J + K$" (L249); "Therefore, we may assume that $\alpha_2 = \alpha_3 > 0$" (L505); "we may further require $\delta$ to be isolated" (L284); "we may weaken the condition and allow" (L286); "it suffices to test the independence on the points of $\mathrm{supp}(b_i)$ only" (L286); "it is sufficient to check that" (L286); "it is enough to prove that" (L249).
- Consequence markers: "Hence" (sentence-initial, 7+), "Therefore," (7), "thus" (lower-case mid-sentence, 13), "Thus" (2), "It follows that" (L377, L447, L461), "It follows at once that" (L371), "It follows by [...] that" (L367), "By construction," (L177, L363, L371), "By comparing the ordinal values," (L282), "By looking at the Cantor Normal form of $\deg_J(e)$, we observe that" (L381), "By assumption, we must have" (L441), "By the assumption on $\alpha$," (L459), "Note that moreover" (L405), "Observe that" (L411), "Recall that" (L343), "In particular," (L219, L284, L341, L411, L467), "which means exactly that" (L320), "equivalently," (L31, L103, L249).
- Contradiction closers: "a contradiction" (L262, L282), "which contradicts $(*)_\alpha$" (L347), "which contradicts $\mathrm{Q}(b_1^{|\gamma}, \ldots, b_s^{|\gamma})$" (L409), "a contradiction against $\mathrm{Q}(b)$" (L459), "another contradiction against $\mathrm{Q}(b)$" (L461), "this contradicts $(*)_{\omega^{\alpha_1} + \omega^{\alpha_2}}$" (L507).
- Closers: "as required" (L397, L501), "then we are done" (L481), "□", "$\qquad \square$" inside displays (L369, L383, L389).
- Navigation / narrative: "We wish to proceed as in the proof of Proposition 4.4, but we now face new obstacles. Let us retrace the proof." (L353); "To overcome this issue, we find ..." (L355); "To conclude, we need to improve the coefficients $\delta_i$ so that they lie in $K$." (L377); "We now can show that one can find a linear combination with coefficients in $K$ rather than just in $J_{\omega^{\alpha_1}}$." (L391); "It now remains to give a bound on $\deg_J(b_j^{|\gamma_i})$." (L405); "We start by proving a crucial lemma for the inductive step:" (L431); "We now apply the above statement in two slightly different settings." (L451); "We then prove a very similar conclusion when ... We do this with a preliminary lemma." (L463); "We are now ready to prove irreducibility for non-principal series:" (L245); "The following allows us to obtain irreducibility for non-principal elements using irreducibility results for principal elements." (L235); "First, we observe the following easy base case." (L314); "The successor stage is rather simple, because there are no ordinals between $\alpha$ and $\alpha + 1$." (L335); "The following notions are fundamental in our work." (L142).
- Self-reference: "In this paper" (L7, L25), "In the current work" (L54), "In this work" (L191), "in our work" (L142), "in our proofs" (L189), "prior to this work" (L7), "We obtain our results using induction on" (L304).
- Induction language: "by induction on $\deg_j(b_1)$" (L225); "We show by induction that" (L333); "The induction base is ... The induction step is ..." (L333); "an inductive step on the Cantor Normal Form of $\alpha$" (L451); "a crucial lemma for the inductive step" (L431); "a different induction on the Cantor normal form of $\alpha$" (L427); "The successor stage" (L335); "the following easy base case" (L314).
- Ease markers: "One can easily deduce" (L47), "One can easily verify" (L215), "one can verify that" (L155), "Clearly," (L233), "obviously" (L231), "It follows at once" (L371), "rather simple" (L335), "Note in particular" (L314).

### E.5 Talking about the literature and about the state of knowledge

- "It is well known that" (L21); "Rings and fields of power series are classical tools in various areas, such as valuation theory." (L21); "A classical tool in the study of real closed fields are the fields $K((G))$" (L7).
- "the first question was posed by Conway [Con76], who conjectured that" (L23); "Conway's conjecture was proved by Berarducci [Ber00]" (L25); "first suggested by Gonshor [Gon86]" (L25); "More irreducible series have been presented in the literature." (L27); "Berarducci's main result reads as follows." (L27); "were exhibited in [PS06] and in [LM17]; in parallel, Pitteloud [Pit01] proved that ... answering a question of Gonshor" (L33); "The keystone of [Ber00] is that" (L124); "it was stated with no proof in [Ber00] that" (L138); "In [LM24] it is proved by the 3rd and the 4th authors that" (L195); "its properties proved in [LM24]" (L221); "We refer the reader to [BKK06, LM24] for extensive considerations on" (L25).
- State of knowledge: "far beyond $\alpha = \omega^2$ and $\alpha = \omega^3$ known prior to this work" (L7); "In fact, $3\omega + 2$ is now the smallest $\alpha$ for which we do not know whether there exists any irreducible element in $P_\alpha$." (L429); "Unlike the previous cases, in this induction we do not obtain $(*)_\alpha$, but irreducibility only." (L427).

### E.6 Explaining notation and conventions

- "Here $\oplus$, $\odot$ denote Hessenberg's natural (commutative) operations." (L47); "Here $\deg(b)$ is the maximum ordinal $\alpha$ such that" (L83); "thus we add the following notation: let $\deg_J(b)$ denote" (L132); "where by convention we set" (L132); "For the sake of readability, we introduce the following notation to remove the base $\omega$." (L164); "For the sake of notation, we write $\mathrm{rv}_J$, $\mathrm{RV}_J$ for respectively" (L217); "in this case we simply write $\mathrm{rv}(b)$" (L221); "in other words, $A_\alpha := \ldots$" (L306); "(also denoted by $\sup(b)$)" (L37); "denoted by $\mathrm{crit}_J(b)$" (L151); "The set of all big points of $b$ is denoted by $\mathrm{Big}(b)$" (L171); "(where it is called $X(b)$)" (L175); "We summarise this consideration with the isomorphism" (L99); "that is, $\deg_J^r(b_1) > 0$" (L284); "(that is, $p_i q_i \in R_\alpha$)" (L63); "(equivalently, it is of the form $\omega^\alpha$)" (L103).

### E.7 Degree-comparison sentences (the paper's commonest sentence type)

- "$\deg_J(r) < \deg_J(b)$" (L455, L465, L507); "where $\deg_J(r_\gamma) < \alpha$" (L457); "$\deg_J(q_i) \geq \deg_J(p_i) > 0$" (L337); "$0 < \deg_J(p) \leq \deg_J(q)$" (L507); "$\deg_J(q) = \deg_J^r(b) > \deg_J(p) > 0$" (L465); "Suppose $\deg_J^p(q) > \deg_J^p(p) > 1$." (L433); "and if the inequality is strict, then $b_j^{|\gamma_i} \in A_\alpha$" (L343); "Recall that $\deg_J(b_j^{|\gamma_i}) \leq \alpha$" (L343); "If $\deg_J(k_1 b^{|\gamma_1} + k_2 b^{|\gamma_2}) < \deg_J(q)$ then we are done." (L481).
- Comparisons of the two degrees: "Note that by construction $v_J(b) \leq \mathrm{ot}(b)$, thus $\deg_J(b) \leq \deg(b)$." (L207); "The above inequality is often strict, and not just for series $b \in J$" (L209); "This makes the degree is quite similar to $\deg_J$, but in a sense more precise" (L203).

---

## Part F — Where the paper disagrees with, corrects, or departs from another paper's usage

### F.1 Berarducci's "few cancellation" claim — declared unnecessary, unused, and false (§2, p.4, L138–L140)
- Verbatim: "We note that to prove $\mathrm{ot}(bc) = \mathrm{ot}(b) \odot \mathrm{ot}(c)$ for $b$, $c$ principal, it was stated with no proof in [Ber00] that there are "few cancellation" in the product of two elements of $K((\mathbb{R}^{\leq 0}))$. We observe that not only the above is not required (and in fact not used) in order to prove the multiplicativity of $v_J$, it is neither true.
  *Example* 2.3. Let $S = \{s_1, s_2, \ldots\}$ be a strictly increasing sequence of $\mathbb{Q}$-linearly independent real numbers such that $\sup(S) = 0$. Let us define two series $b = \sum_{n \in \mathbb{N}} t^{s_n}$ and $c = \sum_{n \in \mathbb{N}} (-1)^n t^{s_n}$. If $m$ and $n$ have different parities, the coefficient of $t^{s_m + s_n}$ in $bc$ is $(-1)^m + (-1)^n = 1 - 1 = 0$. Consider $T = \{s_m + s_n : m - n \text{ is odd}\}$, then for every $p \in T$ we have $p \notin \mathrm{supp}(bc)$, thus cancellations occurs on a set of order type $\mathrm{ot}(T) = \omega^2$, which is the same as $\mathrm{ot}(b) \odot \mathrm{ot}(c)$."
- Nature: correction of a claim in [Ber00] (not of a term). The phrase "few cancellation" is quoted in the source's own double quotes.

### F.2 $\mathrm{crit}_J(b)$ vs Berarducci's $\mathrm{crit}(b)$ (Remark 2.6, L155)
- Verbatim: "One should not confuse this with the notion of *critical point* $\mathrm{crit}(b)$, which is the minimum $\gamma \in \mathbb{R}^{\leq 0}$ such that $v_J(b^{|\gamma})$ is maximum possible [Ber00, Def. 10.2]. For example for $b = \ldots$, we have that $v_J(b) = \omega = v_J(b^{|-1}) = v_J(b^{|-2})$, and one can verify that $\mathrm{crit}(b) = -2$ and $\mathrm{crit}_J(b) = -1$."
- Nature: the paper introduces a *different* notion and deliberately distinguishes it by name ("$J$-critical point") and symbol ($\mathrm{crit}_J$) from Berarducci's "critical point" $\mathrm{crit}(b)$, which it leaves intact.

### F.3 $\mathrm{Res}(b)$ for Berarducci's $X(b)$ (L175)
- Verbatim: "The set of all these point $\mathrm{Res}(b)$ was defined in [Ber00, Def. 6.6] (where it is called $X(b)$)."
- Nature: renaming/re-symbolling of an inherited object, with the old symbol recorded; the new name "residual point" is coined alongside.

### F.4 $\deg_J^p$, $\deg_J^r$ for Berarducci's $v_J^p$, $v_J^r$ (L164)
- Verbatim: "For the sake of readability, we introduce the following notation to remove the base $\omega$. 1. $\deg_J^p(b) := \omega^{\beta_n}$, 2. $\deg_J^r(b) := \omega^{\beta_1} + \cdots + \omega^{\beta_{n-1}}$."
- Nature: re-symbolling with stated reason ("readability", "remove the base $\omega$"); the old symbols and names "principal value", "residual value" are kept and used alongside (A.17). Likewise $\deg_J$ for $v_J$ (L132: "thus we add the following notation").

### F.5 $\deg(0) := -\infty$ added to [LM24]'s degree (L193)
- Verbatim: "**Definition 2.12** ([LM24, p. 5]). Given $b \in K((\mathbb{R}^{\leq 0}))$ with $b \neq 0$, let the **degree** of $b$, denoted by $\deg(b)$, be the Cantor degree of $\mathrm{ot}(b)$. We also let $\deg(0) := -\infty$."
- Nature: a convention stated by the paper as an addition ("We also let"); whether [LM24] already has it cannot be determined from this paper.

### F.6 Restatement of Berarducci's Theorem 10.5 with an added gloss (L31)
- Verbatim: "*If $b \in K((\mathbb{R}^{\leq 0})) \setminus J$ (equivalently, $b \in K((\mathbb{R}^{\leq 0}))$ not divisible by $t^\gamma$ for any $\gamma < 0$) has order type $\omega^{\omega^\alpha}$ for some ordinal $\alpha$, then both $b$ and $b+1$ are irreducible.*"
- Nature: not a disagreement; a restatement in the paper's own $J$-notation with an explanatory equivalent.

### F.7 Convolution formula and Leibniz rule restated in $\deg_J^p$/$\deg_J^r$ notation (L181–L187)
- Nature: Berarducci's Lemmas 7.5(2) and 7.7 are restated using the paper's translated-truncation and $\deg_J$ notations (B.15, B.16); no disagreement is expressed.

### F.8 Positioning against [PS06], [LM17] (Remark 1.7, L69; abstract L7)
- Verbatim: "As a special case, we find irreducible principal series of order types $\omega^2$ and $\omega^3$, as in respectively [PS06] and [LM17]."; "far beyond $\alpha = \omega^2$ and $\alpha = \omega^3$ known prior to this work" (L7).
- Nature: claims of generalisation, not of correction.

### F.9 No other explicit disagreements
- The paper does not dispute any other term, symbol or result. In particular it adopts from [LM24] without comment: "normal form", "degree", "$\deg$", the maximal finite-support divisor, and the $\mathrm{RV}$ results; from [Ber00]: "ordinal value" $v_J$, "principal value", "residual value", "critical point" $\mathrm{crit}$, the convolution formula and Leibniz rule, Lemmas 4.7, 5.5, 6.8, Theorem 9.7, Cor. 9.9, Thm. 10.5, Rem. 5.3.

---

## Part G — Transcription issues, apparent typos, unverified readings

No PDF was available; the following are places where the transcription is suspect or where the source itself seems to contain a slip. Each is flagged so that no entry above is relied on for the affected detail.

1. **Title spelling** (L1): "GENERALIZED" vs body "generalised" (L21). Unverified which the published title uses.
2. **$Z$ vs $\mathbb{Z}$** (L23, L25): "$Z + K((G^{<0}))$" with plain $Z$ alongside "$\mathbb{Z} + \mathbb{R}((G^{<0}))$". Possibly intentional (generic subring $Z$), possibly lost blackboard bold. Unverified.
3. **Hessenberg sum display** (L97): "$\alpha \oplus \beta$ is defined to be $\omega^{\gamma_{\pi(1)}} + \ldots + \omega^{\gamma_{\pi(n)}}$" — should end at $\pi(n+m)$. Source or transcription slip.
4. **Third bullet of the $\deg_J$ properties** (L136): "$\deg_J(b) = -\infty$ if and only if $\deg_J(b) = -\infty$" — tautological; intended "$\ldots$ if and only if $b \in J$".
5. **"$\sum_\beta b_x t^x$"** (L144) in Definition 2.4: index should be $x$.
6. **"$\sum_{(m,n) \in \mathbb{N}}$"** (L195): should be $\mathbb{N}^2$ (as at L211).
7. **"$\{c : \nu(b) < \alpha\}$"** (L219) in $\mathrm{RV}_\nu^\alpha$: should be $\nu(c)$.
8. **"$\deg_j(b_1)$"** (L225): lower-case $j$ for $J$.
9. **"$B = q_i C_i$"** (L239): presumably "$B = \sum_i q_i C_i$"; the summation sign appears lost.
10. **"$\mathrm{Q}(b_1, ., b_n)$"** (L266, L293, L300): "." for "$\ldots$".
11. **"irreducile"** (L314) for "irreducible"; "for ever $b$" (L333) for "for every $b$"; "strictly smaller that" (L371) for "than"; "cancellations occurs" (L140); "is $\mathbb{Q}$-linearly independent set" (L255, missing article); "an **multiplicative valuation**" (L195); "This makes the degree is quite similar" (L203); "The set of all these point" (L175); "And one further more may obtain a kind of a Leibniz rule" (L185); "it is neither true" (L138). These look like source-level English slips rather than transcription errors, but cannot be distinguished without the PDF.
12. **$\mathrm{Big}^{\omega^{\alpha_1}}(r)$ vs $\mathrm{Big}^{\omega^{\alpha_2}}(r)$** (L371): the two superscripts differ within one sentence; the argument needs $\omega^{\alpha_1}$ in both.
13. **"$\Gamma$ has order type $\omega^{\alpha_{n+1}}$"** (L457): by the reasoning of L355 one expects $\omega^{\omega^{\alpha_{n+1}}}$ ($= v_J^p(b)$). Possibly a source slip; content of A.20 should not be relied on for the exact exponent here.
14. **"$v(b_j^{|\gamma_i})$"** (L411): bare $v$ where $\deg_J$ is meant (the value compared is $\deg_J^r(b)$, an ordinal in "degree" scale).
15. **"$3\omega + 1$", "$3\omega + 2$"** (L429) and **"$m\omega^\alpha + \beta$"** (L73): natural number written on the left of $\omega$ where classical ordinal arithmetic would read $\omega \cdot 3$, $\omega^\alpha \cdot m$. Whether the source writes it this way (as an informal convention) or the transcription reordered it is unverified; the intended meaning is clear from context (Cantor normal form $\omega+\omega+\omega+1$, and $\mathrm{ot}(b)$ with $m$ copies of $\omega^\alpha$).
16. **"Lemma 4.16"** (L507): refers to Proposition 4.16 (labelled "**Proposition 4.16**" at L465). Also L463 says "We do this with a preliminary lemma" before stating Proposition 4.16.
17. **Proof of Lemma 4.12** (L409) uses $b_i$, $b$ where the statement (L407) uses $c_i$, $c$ — variable mismatch in the source.
18. **$ot(r)$** (L81) in italic vs $\mathrm{ot}$ elsewhere.
19. **Proof of Prop 3.6** (L268–L282): the statement (L266) quantifies "for every $1 \leq i \neq j \leq m$" but the tuple is $b_1, \ldots, b_n$ — $m$/$n$ mismatch; similarly Cor 3.5 (L264) mixes $m$ and $n$.
20. **Prop 4.16's statement vs proof**: proof says "as observed in the proof of Proposition 4.15, is infinite with supremum $0$" (L467) — fine; but the statement's "$\deg_J(q) = \deg_J^r(b) > \deg_J(p) > 0$" (L465) is later used with "$\deg_J(p) = \deg_J^p(b)$" (L467), which needs $\deg_J(b) = \deg_J(pq)$, assumed silently.
21. **Example 2.3** (L140): "$S = \{s_1, s_2, \ldots\}$" indexed from $1$ but the series sum "$\sum_{n \in \mathbb{N}}$" — if $0 \in \mathbb{N}$, $s_0$ is undefined. Minor source slip.
22. **Definition 2.1** is stated for "$b \in K((\mathbb{R}))$" (L105) while everything else is in $K((\mathbb{R}^{\leq 0}))$; possibly faithful to [LM24]. Unverified.
23. **$K[\mathbb{R}^{\leq}]$** (L221, L233, L239, L249): superscript "$\leq$" with no "0". May be the source's notation or a transcription loss of "0". Unverified.
24. **Page boundaries** are inferred from `<!-- page N -->` markers and may not correspond exactly to the published pagination (this is the arXiv v1).
25. **Footnotes, running heads, and any figures** would not survive this transcription; none are visible. No footnotes appear in the transcription.

---

## Closing note

Entries: Part A 42, Part B 24, Part C 15, Part D 14 bullets, Part E 7 groups, Part F 9, Part G 25 items. Source: transcription only (arXiv v1, 2405.13815v1); no PDF or TeX in the library, so every verbatim quotation above reproduces the transcription's rendering, including its apparent slips, and none could be checked against the published article. Line numbers are to the transcription file.

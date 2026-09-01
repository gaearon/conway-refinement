# Pit01b — terminology record

**Paper.** Daniel Pitteloud, "Existence of Prime Elements in Rings of Generalized Power Series", *The Journal of Symbolic Logic* 66 (3), Sep. 2001, pp. 1206–1216. Received February 15, 1999; revised March 15, 2000.

**Source read.** The 460-line Markdown transcription at
`blueprint/references/pitteloud_2001_existence_prime_elements_generalized_power_series.md`. No PDF
was available for this audit, so the record was not checked against the published article.
Doubtful readings are flagged `[UNVERIFIED]`; figure descriptions are second-hand.

**Sections read.** Abstract; §1 Introduction (incl. "Contents of this paper" and the Remark on [8]); §2 The formula (B); §3 Primes in K((R^{≤0})) (Lemma 3.1, complexity map, big points, Proposition 3.2, Notation u^L, Theorem 3.3); §4 Primes in K((G^{≤0})) when G admits a maximal proper convex subgroup (Theorems 4.1, 4.2, Example); Acknowledgements; References; address block. That is the whole paper.

**Locations.** Given as `L<n>` = line number of the transcription, and `p.<n>` = published page. Page numbers are inferred from the transcription's `<!-- page N -->` markers on the assumption that marker "page 2" (where the abstract starts) is p.1206, so p = 1204 + N: page 2 → 1206, page 3 → 1207, page 4 → 1208, page 5 → 1209, page 6 → 1210, page 7 → 1211, page 8 → 1212, page 9 → 1213, page 10 → 1214, page 11 → 1215, page 12 → 1216. Without the PDF this mapping is an inference; line numbers are exact.

**Quoting.** Quotes are verbatim from the transcription, including its LaTeX. Where the transcription's rendering of a symbol is itself in question I say so. Counts are rough `grep` counts over the transcription (they include headings and the statement/proof repetitions).

**Four kinds.** Entries are tagged **[DEF]** (the paper's own term/notation/convention), **[REUSE]** (taken from a cited source), **[ASSUMED]** (used without definition or citation — field background; my gloss is inference), **[GENERIC]** (standard mathematics from outside the field).

---

## Part A. What the paper defines: terms, notation, conventions

### A.0 Global standing conventions

**A.0.1 [DEF] Standing hypotheses on K and G.**
> "From now on, $K$ will always denote a field of characteristic 0 and $G$ an ordered additive abelian divisible group." (L29, p.1206)

Note the word order "ordered additive abelian divisible group" here; elsewhere "ordered additive abelian group" (L20, L14 abstract: "the ordered additive abelian group $G$"), and in §4 "ordered abelian divisible group" (L398, L407: "Let $G$ be an ordered abelian divisible archimedean group." / "Let $G$ be an ordered abelian divisible group which contains a maximal proper convex subgroup $G_0$."). Counts: "ordered additive abelian" ×3, "ordered abelian divisible" ×2. Divisibility is a blanket assumption from L29 on, but the §4 theorem statements restate it.

Characteristic 0 is assumed throughout; the abstract says "coefficients in the field $K$ of characteristic 0" (L14). Note in §3 the proof of Lemma 3.1 divides by $k a_\gamma$ (L178: "By dividing if necessary $a$ and $d$ by $k a_\gamma$ and $(k a_\gamma)^k$ respectively") — this is where char 0 is used, though the paper does not say so.

**A.0.2 [DEF] Convention: the group written additively, exponents written as $x^\gamma$.** The series is $\sum_{\gamma\in G} a_\gamma x^\gamma$ (L22); the formal variable is always $x$; the group is always written additively with order relation $\leq$. Never uses $t^\gamma$ or multiplicative monomial notation.

**A.0.3 [DEF] Convention: the "non-positive exponents" ring is the object of study, written $K((G^{\leq 0}))$.** See A.2.3. The abstract calls it "the ring $K((G^{\leq 0}))$ of series with non-positive exponents" (L14). No separate name (no "Berarducci ring", no "$\mathbb{K}((G^{\leq 0}))$", no script letters) — always the explicit symbol. Counts: `K((\mathbb{R}^{\leq 0}))` ×32, `K((G^{\leq 0}))` ×23, `K((G))` ×12.

**A.0.4 [DEF] Convention: the real case is the model case; general $G$ is treated by reduction.** §2 and §3 are stated entirely for $K((\mathbb{R}^{\leq 0}))$; §4 reduces to it. Definitions in §2 are given only for $\mathbb{R}$: "Let $b = \sum_{\delta \in \mathbb{R}^{\leq 0}} b_\delta x^\delta \in K((\mathbb{R}^{\leq 0}))$, and $\gamma \in \mathbb{R}^{<0}$." (L72, p.1207).

**A.0.5 [DEF] Convention: $\mathbb{N}$ includes 0; $\mathbb{N}^*$ and $\mathbb{Z}^*$ exclude 0.** Not stated, but forced by usage: "$n, r, s \in \mathbb{N}$" with "$v_0(b) = \omega^{\delta+n}$" where $n=0$ is allowed (Case 1: "$r = 0$", L194), and "$k, l \in \mathbb{N}^*$" for exponents that must be $\geq 1$ (L159, L168). Also "$p \in \mathbb{Z},\ q \in \mathbb{Z}^*$" (L412). The star on sets is defined for subsets of $\mathbb{R}$ at L91: "If $X \subseteq \mathbb{R}$, $X^* := X \setminus \{0\}$." — and then used for $\mathbb{N}$ and $\mathbb{Z}$ too.

**A.0.6 [DEF] Convention: square-bracket asides.** Parenthetical clarifications are set in square brackets inside running text, e.g. "[ $a \,|\, c$ means $a$ divides $c$ ]." (L148), "[ It was proved in [1] for $G = (\mathbb{R}, +)$ ]." (L64), "[$\oplus$ denotes the natural sum of ordinals, see e.g., [9]]." (L350), "[As in Lemma 3.1, we can assume that $k a^{|\gamma} = 1 \bmod (J)$ ]." (L242), "[ First observe that such $Q$ and $a$ always exist: ... ]" (L411–412), "[ If $\alpha$ is close to 0, ... ]" (L380).

**A.0.7 [DEF] Convention: end-of-proof sign $\dashv$.** Used at L212, L338, L392, L403, L425 (5 proofs). Not $\square$ or $\blacksquare$.

**A.0.8 [DEF] Convention: citation style "(see [n])".** E.g. "(Hahn 1907, see [5])" (L25), "(see e.g., [12])" (L31), "Berarducci (see [1]) proved" (L39), "(see [2, 4])" (L14, L39).

**A.0.9 [DEF] Convention: the series variable letters.** $a$ is reserved in §3 for the candidate prime (fixed, $v_0(a)=\omega$); $b, c, d$ for the other terms of the equation $ab = cd$ / $a^k b = c^l d$; $e, \varepsilon$ for quotients and error terms; $u$ for a generic series (L215, L225, L342, L401). Coefficients are subscripted: $a_\gamma$, $b_\delta$ (L22, L72). Exponents/points of the group: $\gamma, \delta, \eta, \xi, \beta, \alpha, \theta, \mu$ (Greek lower-case), but $\alpha, \beta, \delta, \gamma$ also serve as ordinals (L99, L105, L136, L168, L354) — the paper does not separate ordinal letters from group-element letters.

### A.1 Series and support

**A.1.1 [DEF] "formal series" / the series $a = \sum_{\gamma\in G} a_\gamma x^\gamma$.**
> "If $K$ is any field and $G$ any ordered additive abelian group, $K((G))$ is the set of all formal series $$a = \sum_{\gamma \in G} a_\gamma x^\gamma, \text{ where } a_\gamma \in K \quad \forall \gamma \in G,$$ having well-ordered support $S_a := \{\gamma \in G : a_\gamma \neq 0\}$." (L20–24, p.1206)

"formal series" occurs once (L22); afterwards the bare word "series" (≈15 occurrences) or the full name "generalized power series" (×5: title, abstract, L18, L26, L37). The elements are just "series" or, once, "elements" ("prime elements", L14, L45).

**A.1.2 [DEF] Support, $S_a$.** Defined in the displayed sentence above: "having well-ordered support $S_a := \{\gamma \in G : a_\gamma \neq 0\}$" (L24). Symbol: $S_a$, $S_b$, $S_u$, $S_{b_i'}$ — always capital $S$ with the series as subscript. Counts: `S_a` ×6, `S_b` ×10. The word "support" ×9. Never "supp".

**A.1.3 [DEF] "well-ordered support".** The defining condition on a series (L24). Occurs once; the paper never again says "well-ordered".

**A.1.4 [DEF] Coefficient notation.** $a_\gamma$ is the coefficient of $x^\gamma$ in $a$ (L22). Used as $k a_\gamma$ (L178). No "coefficient" word for a specific one except "coefficients in $K$" (L14, L26).

**A.1.5 [DEF] Order type of a series, $ot(b)$.**
> "7. If $b \in K((\mathbb{R}^{\leq 0}))$, $ot(b) := ot(S_b)$." (L92, p.1208)
> "3. ot abbreviates order type." (L88)

So "$b$ is of order type $\omega$" means $S_b$ (including $0$ if $0\in S_b$) has order type $\omega$. Phrasing: "is of order type $\omega$ or $\omega + 1$" (L142, L344, L399), "be of order type $\omega$" (L408), "has order type $\omega + 1$ in ..." (L423). Also the hyphenated coinages "$\omega-$series" and "$\omega + 1-$series" (L51: "all $\omega-$series (and some $\omega + 1-$series) whose support is cofinal to 0 are prime") and "primes of type $\omega + 1$" (L52). Counts: "order type" ×6, `ot(` ×19, "$\omega-$series" ×1, "of type" ×1. The dominant form is "of order type $\omega$".

### A.2 The field and the ring

**A.2.1 [DEF] $K((G))$, "the field of generalized power series with coefficients in $K$ and exponents in $G$".**
> "$K((G))$ is called the field of generalized power series with coefficients in $K$ and exponents in $G$." (L26, p.1206)
> "With obvious operations $+$ and $\cdot$, $K((G))$ is a field (Hahn 1907, see [5])." (L25)

Note "obvious operations" — the product is not written out anywhere; the only formula about it is the convolution formula (C), which is mod $J$.

**A.2.2 [DEF] Convention: the ordering on $K((G))$ when $K$ is ordered — sign of the leading (minimal-exponent) coefficient.**
> "If $K$ is an ordered field, so is $K((G))$: We simply put $a = \sum_{\gamma \in G} a_\gamma x^\gamma > 0$ iff $a_\delta > 0$, where $\delta := \min S_a$." (L25, p.1206)

So the *smallest* exponent is the leading one: $x^\gamma$ with $\gamma$ very negative is infinitely large. (Consistent with the "series with non-positive exponents" being the "integers"-like ring, see A.2.3, and with $x^{-1} + x^{-1/2} + \dots$ being written in increasing exponent order, L144.) The paper never uses the words "leading term", "leading exponent", "valuation" for $\min S_a$.

**A.2.3 [DEF] $K((G^{\leq 0}))$ and $G^{\leq 0}$.**
> "$K((G^{\leq 0}))$ denotes the subring of $K((G))$ whose series have their support included in $G^{\leq 0} := \{\gamma \in G : \gamma \leq 0\}$." (L27, p.1206)

Called "the ring $K((G^{\leq 0}))$ of series with non-positive exponents" (L14) and "the subring of $K((G))$" (L27). Variants of the exponent-set notation: $G^{\leq 0}$, $\mathbb{R}^{\leq 0}$, $\mathbb{R}^{<0}$, $G^{<0}$ (L411), $Q^{<0}$ (L408), $H^{\leq 0}$ (L421), $\mathbb{R}^{<\gamma}$ (L90). General rule: "$\mathbb{R}^{<\gamma} := \{\delta \in \mathbb{R} : \delta < \gamma\}$ etc..." (L90).

**A.2.4 [DEF] $K((Q^{<0}))$, $K((G_0))((H^{\leq 0}))$, $\mathbb{R}((\mathbb{R}^{<0}))$ — iterated/variant constructions used without separate definition.** "$a \in K((Q^{<0}))$" (L408); "$i : K((G)) \longrightarrow K((G_0))((H))$ and $i(K((G^{\leq 0}))) \subseteq K((G_0))((H^{\leq 0}))$" (L421); "$\mathbb{R}((\mathbb{R}^{<0})) \oplus \mathbb{Z}$" (L144). These are read by the same convention $K((X))$ = series with support in $X$, here applied to a subset $X$ that is not a group.

### A.3 Truncations and the ideal $J$ (the "basic definitions")

These are introduced with "we recall some basic definitions which all appear in [1]" (L70) — so they are **[REUSE]** by attribution, but the paper gives its own wording and symbols, recorded here verbatim; the lineage is recorded again in Part B.

**A.3.1 [REUSE, worded here] Truncation $b_{|\gamma}$.**
> "**Definitions.** Let $b = \sum_{\delta \in \mathbb{R}^{\leq 0}} b_\delta x^\delta \in K((\mathbb{R}^{\leq 0}))$, and $\gamma \in \mathbb{R}^{<0}$.
> 1. $b_{|\gamma} := \sum_{\delta \leq \gamma} b_\delta x^\delta$ is the truncation of $b$ at $\gamma$." (L72–74, p.1207)

Note: the truncation is the part with exponents $\leq \gamma$ (inclusive), i.e. the "big" part (large in absolute value, far from 0), and $\gamma<0$. Symbol: subscript bar-gamma, $b_{|\gamma}$. The word "truncation" occurs once; the phrase is "the truncation of $b$ at $\gamma$". The complementary piece is written $b - b_{|\gamma}$ (L131, L380) or, for a block, $b_{|\theta_i} - b_{|\theta_{i-1}}$ (L360); no name is given to it.

**A.3.2 [REUSE, worded here] Shifted truncation $b^{|\gamma}$.**
> "2. $b^{|\gamma} := x^{-\gamma} b_{|\gamma}$" (L75, p.1207)

Superscript bar-gamma. No name is given; it is the truncation at $\gamma$ re-based so that its last exponent is $0$. This is the object that carries the whole of §3 (the convolution formula, Corollary 2.2, big points, Lemma 3.1). The paper never calls it a "coefficient", "slice", or "germ".

**A.3.3 [REUSE, worded here] The ideal $J$.**
> "3. $J := \{\, b \in K((\mathbb{R}^{\leq 0})) : \exists \gamma < 0$ such that $S_b \leq \gamma$ i.e., $\alpha \leq \gamma \ \forall \alpha \in S_b \,\}$." (L76, p.1207)
> "**Remark.** It is easy to prove that $J$ is an ideal of $K((\mathbb{R}^{\leq 0}))$, which is generated by the set of monomials with negative exponents." (L82, p.1208)

And in §1 for general $G$: "the ideal $J \subseteq K((G^{\leq 0}))$ generated by the set of monomials $\{\, x^\gamma : \gamma \in G$ and $\gamma < 0 \,\}$" (L64). Symbol always plain $J$ (no subscript) for this ideal; the subscripted $J_{\omega^\alpha}$ is a different (notational) device, see A.6.

**A.3.4 [DEF] "monomial".** Used for $x^\gamma$: "the set of monomials $\{\, x^\gamma : ... \}$" (L64), "monomials with negative exponents" (L82), "not divisible by any monomial $x^\gamma$ for $\gamma \in Q^{<0}$" (L408). Count ×3. Not defined; standard.

### A.4 Ordinal notation

**A.4.1 [DEF] Notations block (verbatim, L84–92, p.1208).**
> "**Notations.**
> 1. $OR$ denotes the class of all ordinals.
> 2. $\mathrm{Lim}$ denotes the class of all limit ordinals.
> 3. ot abbreviates order type.
> 4. C.n.f. abbreviates Cantor normal form.
> 5. If $X, Y \subseteq \mathbb{R}$ and $\gamma \in \mathbb{R}$, $X \leq Y$ means $x \leq y \ \forall x \in X \ \forall y \in Y$, $X \leq \gamma$ means $X \leq \{\gamma\}$, $\mathbb{R}^{<\gamma} := \{\delta \in \mathbb{R} : \delta < \gamma\}$ etc...
> 6. If $X \subseteq \mathbb{R}$, $X^* := X \setminus \{0\}$.
> 7. If $b \in K((\mathbb{R}^{\leq 0}))$, $ot(b) := ot(S_b)$."

Notes on rendering: $OR$ is set in italic math (two letters), not $\mathbf{On}$ or $\mathrm{Ord}$; $\mathrm{Lim}$ is upright in the transcription at L87 and L136 but italic "$Lim$" at L227 — treat as the same symbol. "ot" is lower-case roman in "ot abbreviates" and appears as $ot(\cdot)$ in math (sometimes `\mathrm{ot}` at L99, L105 — same symbol). $X^*$ for removing $0$ is defined only for $X\subseteq\mathbb{R}$ but used for $\mathbb{N}^*$, $\mathbb{Z}^*$.

Convention: $\mathrm{Lim}\cup\{0\}$ is the recurring set of "limit or zero" ordinals used to write every $v_0$-value as $\omega^{\delta+n}$ with $\delta\in\mathrm{Lim}\cup\{0\}$, $n\in\mathbb{N}$ (L136, L168, L225, L227). This decomposition $\omega^{\delta+n}$ is the paper's standard normal form for a $v_0$-value.

**A.4.2 [DEF] Convention: set–scalar inequalities $S_b \leq \gamma$, $S_{b_1'} < S_{b_2'} < \dots \leq 0$.** Defined in item 5 above; used at L76, L97, L98, L356, L363 ("$S_{b_i} < S_{b_{i+1}} \ \forall\, i$").

**A.4.3 [REUSE] Natural sum and product, $\oplus$, $\odot$.**
> "where $\odot$ denotes the commutative (natural) product of ordinals (see [9])." (L111, p.1208)
> "[$\oplus$ denotes the natural sum of ordinals, see e.g., [9]]." (L350, p.1213)

Also "using the natural product, by the formula $v_0(bc) = v_0(b) \odot v_0(c)$" (L43). Symbols: $\odot$ ×10, $\oplus$ ×12 (the latter count includes the direct-sum uses $G = H \oplus G_0$ L414, L418 and $\mathbb{R}((\mathbb{R}^{<0})) \oplus \mathbb{Z}$ L144 — the same glyph is used for natural sum of ordinals and for direct sum of groups). Mixed expressions such as "$\omega^{\delta_1 \odot (l+1) \oplus \delta_2 + r(l+1)+s-1}$" (L248) combine natural and ordinary operations in one exponent; the paper does not state precedence.

**A.4.4 [REUSE] Cantor normal form, "C.n.f.".** "C.n.f. abbreviates Cantor normal form" (L89). Used as a relation decoration: "$\mathrm{ot}(S_b \setminus \{0\}) \stackrel{C.n.f.}{=} \omega^{\alpha_1} + ... + \omega^{\alpha_n}$ (with $\alpha_1 \geq ... \geq \alpha_n > 0$)" (L105); "Considering the Cantor normal form $\omega^{\beta_1} + \omega^{\beta_2} + ... + \omega^{\beta_r}$ of $S_b$ ($\beta_1 \geq \beta_2 \geq ... \geq \beta_r \geq 0$)" (L354); "$c_1$ is the first part of the C.n.f. of $c$" (L388). Note: C.n.f. is applied to a *set* ($S_b$) and to a *series* ($c$), meaning the C.n.f. of its order type. Convention: the C.n.f. is written in base $\omega$ with repeated terms (no coefficients), exponents non-increasing.

### A.5 The ordinal-valued map $v_0$ and its formulas

**A.5.1 [REUSE, defined here] $v_0$: "ordinal valuation" / "ordinal valued map".** Attributed to Berarducci (B.1.2); the definition is reproduced in full:
> "**Definition.** of $v_0 : K((\mathbb{R}^{\leq 0})) \longrightarrow OR$.
> Let $b \in K((\mathbb{R}^{\leq 0}))$ (Refer to figure 1).
> i) If there is some $\gamma \in \mathbb{R}^{<0}$ such that $S_b \leq \gamma$, then $v_0(b) := 0$.
> ii) If there is some $\gamma \in \mathbb{R}^{<0}$ such that $S_b \setminus \{0\} \leq \gamma$ and $0 \in S_b$, then $v_0(b) := 1$.
> iii) Otherwise, $v_0(b) := \omega^\delta$, where $\delta$ is defined by $\mathrm{ot}(S_b \cap [-\varepsilon, 0[) = \omega^\delta$ for $\varepsilon > 0$ sufficiently small." (L94–99, p.1208)

Names: "an ordinal valued map $v_0 : K((G^{\leq 0})) \longrightarrow OR$" (L41, §1) and "an "ordinal valuation" $v_0 : K((G^{\leq 0})) \longrightarrow OR$" (L70, §2, with the scare quotes in the original). Each once. In §1 the codomain statement is for general $G$, in §2 it is defined only for $\mathbb{R}$. Symbol: $v_0$ throughout (×173 occurrences of `v_0(`). Note the interval notation "$[-\varepsilon, 0[$" (French-style half-open interval) at L99. Case iii) covers $0 \in S_b$ or not alike; the value is always $0$, $1$, or a power $\omega^\delta$ with $\delta\geq 1$.

Conventions fixed here: $v_0(0) = 0$ (case i with empty support — not stated, but implied and used: "$a^k b = c^l d \bmod (J_{v_0(a^k b)})$" etc.); $v_0$ of a series with $0$ in its support and nothing near 0 is $1$, not $\omega^0$ written differently. Remark 3 (L105) shows $v_0(b)$ is the *last* term of the C.n.f. of $ot(S_b\setminus\{0\})$:
> "3. If we are in Case iii) of the definition of $v_0$ and if $\mathrm{ot}(S_b \setminus \{0\}) \stackrel{C.n.f.}{=} \omega^{\alpha_1} + ... + \omega^{\alpha_n}$ (with $\alpha_1 \geq ... \geq \alpha_n > 0$), then $v_0(b) = \omega^{\alpha_n}$." (L105, p.1208)

**A.5.2 [DEF] Remarks on $v_0$ (L101–105, p.1208), verbatim.**
> "1. $b = c \bmod (J)$ iff $v_0(b - c) = 0$.
> 2. If $b \neq 0$, $v_0(b^{|\gamma}) < v_0(b)$ for all $\gamma \in \mathbb{R}^{<0}$ sufficiently close to 0."
(Remark 3 quoted in A.5.1.) Remark 1 fixes the convention that congruence mod $J$ is the same as "$v_0$ of the difference is $0$"; this is what the later $J_{\omega^\alpha}$ notation generalises.

**A.5.3 [DEF name, REUSE content] "Berarducci's formula, which we call (B)".**
> "Berarducci's formula, which we call **(B)**, states that $$v_0(bc) \stackrel{(B)}{=} v_0(b) \odot v_0(c) \quad \forall\, b, c \in K((\mathbb{R}^{\leq 0}))\,,$$ where $\odot$ denotes the commutative (natural) product of ordinals (see [9])." (L107–111, p.1208)

The *label* "(B)" is this paper's coinage (section title "§2. The formula (B)", L68; "the formula ( **B** )", L59). Used as a bare tag in proofs: "(1), Lemma 2.1 and **(B)** imply that" (L211), "then $(B)$ implies that $k$ is determined by" (L223), "dividing by $a$ and using $(B)$" (L254), "using $(B)$ and the convolution formula it is easy to prove that" (L368), "Using **(B)**, Lemma 2.1 and the convolution formula we get" (L380). Count "(B)" ×9. The same content also appears as Lemma 2.1 d) (L132).

**A.5.4 [DEF name; content attribution unclear] "the convolution formula", (C).**
> "The main tool for proving **(B)** is the convolution formula:
> If $b, c \in K((\mathbb{R}^{\leq 0}))$ and $\gamma \in \mathbb{R}^{<0}$, then $$(bc)^{|\gamma} = \sum_{\beta_i + \xi_i = \gamma} b^{|\beta_i} c^{|\xi_i} \bmod (J) \qquad \text{(C)}$$" (L113–116, p.1208)

Followed by:
> "**Remarks.**
> 1. For each $\gamma \in \mathbb{R}^{<0}$, there is only a finite number of pairs $(\beta, \xi) \in \mathbb{R}^{\leq 0} \times \mathbb{R}^{\leq 0}$ such that $b^{|\beta} c^{|\xi} \neq 0 \bmod (J)$. Hence the right member of (C) does make sense.
> 2. (C) holds for a product of several factors: $(b_1 b_2 ... b_n)^{|\gamma} = \sum_{\beta_1 + ... + \beta_n = \gamma} b_1^{|\beta_1} ... b_n^{|\beta_n} \bmod (J)$." (L118–121)

Name: "the convolution formula" (×4: L113, L134 "the convolution formula (for several factors)", L368, L380); tag "(C)" ×3. Whether (C) is Berarducci's or the author's is not stated; it sits in the §2 block introduced by "we recall some basic definitions which all appear in [1]" and "The main tool for proving (B)", so the reader is meant to take it as the known tool behind Berarducci's proof. **[UNVERIFIED]**: the indices in "$\sum_{\beta_i + \xi_i = \gamma}$" (subscript $i$ on the summation variables, but $(\beta,\xi)$ without $i$ in Remark 1) may be a transcription inconsistency or the original's; the sum ranges over the finitely many pairs $(\beta,\xi)$ with $\beta+\xi=\gamma$, $\beta, \xi \in \mathbb{R}^{\leq 0}$, for which the term is nonzero mod $J$. Note also that in (C) the indices $\beta_i, \xi_i$ range over $\mathbb{R}^{\leq 0}$ *including* $0$, whereas $b^{|\gamma}$ was defined only for $\gamma \in \mathbb{R}^{<0}$ (L72); the paper silently allows $b^{|0} = b$.

**A.5.5 [REUSE] Lemma 2.1 (facts from [1], "which we will repeatedly use (without mention)").**
> "Finally let us recall the following facts (see [1]) which we will repeatedly use (without mention) in all this paper.
> **Lemma 2.1.** *Let $b, c \in K((\mathbb{R}^{\leq 0}))$.*
> *a) $v_0(b + c) \leq max(v_0(b), v_0(c))$*
> *b) $v_0(b + c) = max(v_0(b), v_0(c))$ if $v_0(b) \neq v_0(c)$*
> *c) $v_0(bc) = v_0((b - b_{|\gamma})(c - c_{|\eta}))$ for all $\gamma, \eta$ sufficiently close to $0$*
> *d) $v_0(bc) = v_0(b) \odot v_0(c)$.*" (L125–132, p.1209)

Phrase to note: "repeatedly use (without mention)". In practice Lemma 2.1 is cited by name 5 times anyway (L196, L211, L380, ...).

**A.5.6 [DEF] Corollary 2.2 (the paper's own derivative formula).**
> "As a consequence of the convolution formula (for several factors) and Lemma 2.1, we get the following:
> **Corollary 2.2.** *Let $a, b \in K((\mathbb{R}^{\leq 0}))$ be such that $v_0(a) = \omega$ and $v_0(b) = \omega^{\delta+n}$, where $\delta \in \mathrm{Lim} \cup \{0\}$ and $n \in \mathbb{N}$. Let $\gamma \in \mathbb{R}^{<0}$. Then for each $k \geq 1$ we have* $$(a^k b)^{|\gamma} = k a^{k-1} a^{|\gamma} b + a^k b^{|\gamma} + \varepsilon, \text{ where } v_0(\varepsilon) < \omega^{\delta+n+k-1}.$$" (L134–138, p.1209)

No proof is given. This is the "Leibniz-like" derivative formula for the shifted truncation; the paper does not use the words "derivative", "derivation" or "Leibniz". Invoked as "Corollary 2.2 yields" (L174, L238).

### A.6 Congruence and divisibility "mod $(J_{\omega^\alpha})$"

**A.6.1 [DEF] $a = b \bmod (J_{\omega^\alpha})$ and $a \,|\, b \bmod (J_{\omega^\alpha})$.**
> "**Definitions.** Let $\alpha \in OR$ and let $a, b \in K((\mathbb{R}^{\leq 0}))$.
> 1. $a = b \bmod (J_{\omega^\alpha})$ iff $v_0(b - a) < \omega^\alpha$.
> 2. $a | b \bmod (J_{\omega^\alpha})$ iff $\exists e, \varepsilon \in K((\mathbb{R}^{\leq 0}))$ such that $b = ae + \varepsilon$ and $v_0(\varepsilon) < \omega^\alpha$." (L163–166, p.1209)

Points to note for comparison:
- $J_{\omega^\alpha}$ is never defined as a set; only the two relations "$= \bmod (J_{\omega^\alpha})$" and "$| \bmod (J_{\omega^\alpha})$" are defined. The subscript is always an ordinal of the form $\omega^\alpha$ (a $v_0$-value), most often written as $J_{v_0(\cdot)}$ (×66: e.g. "$J_{v_0(a^k b)}$", "$J_{v_0(c)}$") or $J_{\omega^{\dots}}$ (×24: e.g. "$J_{\omega^{\delta+n+k-1}}$"). With $\alpha = 0$, $J_{\omega^0} = J_1$ would give $v_0 < 1$, i.e. $v_0 = 0$, i.e. congruence mod $J$ (Remark 1, A.5.2) — the paper writes this case as plain "$\bmod (J)$" (×6).
- The relation "$= \bmod$" is written with an ordinary equals sign and "mod" in parentheses after the right-hand side: "$a^k b = c^l d \bmod (J_{v_0(a^k b)})$". Never $\equiv$. Transcription renders it variously as `\bmod (J_...)` (×80), `\ mod\, (J_...)` (×10, inside italic theorem statements), `mod (J)`. Treat as one notation.
- Non-divisibility: "$a \nmid c \bmod (J_{v_0(c)})$" (×16). Plain divisibility: "$a \,|\, c$" (×46 incl. mod variants), with "[ $a \,|\, c$ means $a$ divides $c$ ]" (L148). The word "divides" occurs once (that gloss); "divisible" as in "not divisible by any monomial" (L408).
- The standard statement shape is "$a\,|\,c \ mod\, (J_{v_0(c)})$ or $a\,|\,d \ mod\, (J_{v_0(d)})$" (Proposition 3.2, L227), i.e. divisibility *modulo the term's own $v_0$-level*.

**A.6.2 [DEF] "almost" prime.**
> "Following these general ideas we will first prove that $a$ is "almost" prime (see Proposition 3.2). It will follow quite easily that $a$ is prime (see Theorem 3.3)." (L161, p.1209)

Informal, in scare quotes, once; it refers to the mod-$J_{v_0}$ primality of Proposition 3.2.

### A.7 The equation, its complexity, and big points

**A.7.1 [DEF] "the equation $ab = cd$" / "$a^k b = c^l d$" and "the complexity of the equation".**
> "Assume that $a$ is fixed as above, and let $b, c, d \in K((\mathbb{R}^{\leq 0}))$ be such that $ab = cd$. We want to prove that $a \,|\, c$ or $a \,|\, d$ in $K((\mathbb{R}^{\leq 0}))$." (L148, p.1209)
> "The idea (given in Lemma 3.1 below) is to transform the equation $ab = cd$ into a simpler one, where it is easier to see that $a \,|\, c$ or $a \,|\, d$. We are then led to associate a complexity to such equations in such a way that the complexity of the new equation is smaller than that of the initial one." (L150–152)
> "2. For this proof by induction on the complexity of the equation, some experimental computations show that we have to consider all equations of the form $a^k b = c^l d$, ($a$ fixed, $k, l \in \mathbb{N}^*$, $b, c, d \in K((\mathbb{R}^{\leq 0}))$)." (L159)

Phrases: "the initial equation" (×3, L298, L308, L328), "the equation" (×5), "complexity" (×8).

**A.7.2 [DEF] The set $A$ and the complexity map $Cpl$.**
> "We now define the **complexity map.**
> Let $A := \{u \in K((\mathbb{R}^{\leq 0})) : v_0(u) \geq 1\}$. We set $$Cpl : A^3 \times \mathbb{N}^* \longrightarrow (OR)^4, \quad (b, c, d, l) \mapsto (v_0(c), v_0(d), l, v_0(b))$$ where $(OR)^4$ is ordered lexicographically." (L214–219, p.1210)

Note the order of the tuple: $(v_0(c), v_0(d), l, v_0(b))$ — $b$ last, $l$ (a natural number) third. Used as "$Cpl(b', c', d', l) < Cpl(b, c, d, l)$" and once with a blank slot "$Cpl(-, c, d, l-1) < Cpl(b, c, d, l)$" (L272) and with an implicit argument "$Cpl(b', c, d^{|\gamma}, l+1)$" (L250). Symbol $Cpl$ ×17 (roman multi-letter). Supporting remark:
> "**Remark.** If $a^k b = c^l d \bmod (J_{v_0(a^k b)})$ with $a, b, c, d$ as in Lemma 3.1, then $(B)$ implies that $k$ is determined by $b, c, d, l$." (L223, p.1211)

**A.7.3 [DEF] "big point".**
> "**Definition.** If $u \in K((\mathbb{R}^{\leq 0}))$ and $v_0(u) = \omega^{\alpha+m}$, where $\alpha \in \mathrm{Lim} \cup \{0\}$ and $m \in \mathbb{N}$, then we say that $\gamma \in \mathbb{R}^{<0}$ is a big point of $u$ if $m > 0$ and $v_0(u^{|\gamma}) = \omega^{\alpha+m-1}$." (L225, p.1211)

Phrasing: "$\gamma$ is a big point of $d$" / "is not a big point of $c$" (case headings L244, L264, L280, L296, L306, L314, L320, L324). Count ×10. At L306 the transcription reads "ii) $\gamma$ is a not big point of $b$" — word-order slip (transcription or original; **[UNVERIFIED]**).

**A.7.4 [DEF] $u^L$, the supremum of the support.**
> "**Notation.** If $u \in K((\mathbb{R}^{\leq 0}))$, $u^L$ denotes the supremum of $S_u$ : $u^L := \sup(S_u) \in \mathbb{R}^{\leq 0}$." (L342, p.1213)

Used once, in the normalisation "Multiplying $b, c, d$ by $x^{-b^L}, x^{-c^L}, x^{-d^L}$ respectively, we can as well assume that $b^L = c^L = d^L = 0$." (L348). The letter $L$ is unexplained (superscript roman $L$).

**A.7.5 [DEF] The block decomposition $b = b_1 + \dots + b_r$ along the C.n.f.; the cut points $\theta_i$ (and $\mu_i$, $\eta_i$ for $c$, $d$).**
> "Considering the Cantor normal form $\omega^{\beta_1} + \omega^{\beta_2} + ... + \omega^{\beta_r}$ of $S_b$ ($\beta_1 \geq \beta_2 \geq ... \geq \beta_r \geq 0$), it is clear that we can write in a unique way $b = b_1' + b_2' + ... + b_r'$ such that
> i) $S_{b_1'} < S_{b_2'} < ... < S_{b_r'} \leq 0$
> ii) $ot(b_i') = \omega^{\beta_i} \ \forall\, i$.
> We now slightly modify the $b_i's$ in the following way:
> Put $\theta_i := \sup S_{b_i'} \ \forall\, i$ (so $\theta_1 < \theta_2 < ... < \theta_{r-1} \leq \theta_r = 0$) and define inductively $b_1 := b_{|\theta_1}$ and $b_i := b_{|\theta_i} - b_{|\theta_{i-1}}$ for $i \geq 2$. Then we have:
> i) $b = b_1 + b_2 + ... + b_r$ (if $b_r = 0$ remove $b_r$)
> ii) $S_{b_i} < S_{b_{i+1}} \ \forall\, i$
> iii) $\omega^{\beta_i} \leq ot(b_i) \leq \omega^{\beta_i} + 1 \ \forall\, i$.
> We do the same for $c$ and $d$ (see Figure 2, where we assume that $v_0(b), v_0(c), v_0(d)$ are $> 1$)." (L354–366, p.1213)

Per the transcriber's Figure 2 description (L334): blocks $c_1,\dots,c_s$ cut at $\mu_1,\dots,\mu_{s-1}$ with $ot(c_i) = \omega^{\gamma_i}$ or $\omega^{\gamma_i}+1$; blocks $d_1,\dots,d_t$ cut at $\eta_1,\dots,\eta_{t-1}$ with $ot(d_i) = \omega^{\delta_i}$ or $\omega^{\delta_i}+1$. The paper has no name for these pieces ("parts": "$c_1$ is the first part of the C.n.f. of $c$", L388). Note the $\theta_i$ here are group elements, distinct from the ordinal $\theta$ at L268.

**A.7.6 [DEF] The "induction on $ot(c) \oplus ot(d)$".**
> "We prove that $a|c$ or $a|d$ by induction on $ot(c) \oplus ot(d)$: [$\oplus$ denotes the natural sum of ordinals, see e.g., [9]]." (L350, p.1213)

### A.8 Named results of the paper (statements verbatim)

**A.8.1 [DEF] Lemma 3.1 (the transformation step).**
> "**Lemma 3.1.** *Let $a, b, c, d \in K((\mathbb{R}^{\leq 0}))$ be such that $v_0(a) = \omega$, $v_0(b) = \omega^{\delta+n}$, $v_0(c) = \omega^{\delta_1 + r}$, $v_0(d) = \omega^{\delta_2 + s}$; where $\delta, \delta_1, \delta_2 \in \mathrm{Lim} \cup \{0\}$ and $n, r, s \in \mathbb{N}$. Let $k, l \in \mathbb{N}^*$ and assume that $a^k b = c^l d \ mod\, (J_{v_0(a^k b)})$. Let $\gamma \in S_a \setminus \{0\}$ be fixed sufficiently close to $0$, and assume furthermore that $a^{k-1} \,|\, c^{|\gamma} \ mod\, (J_{\omega^{\delta_1 + r - 1}})$ if $r \geq 1$; $a \nmid c \ mod\, (J_{v_0(c)})$ and $a \nmid d \ mod\, (J_{v_0(d)})$. Then there exist $b', c', d' \in K((\mathbb{R}^{\leq 0}))$ such that $a^{k+1} b' = (c')^l d'$ $mod\, (J_{v_0(a^{k+1} b')})$, $v_0(c') = v_0(c)$, $v_0(d') = v_0(d)$, and $v_0(b') < v_0(b)$. Moreover we have $a \nmid c' \ mod\, (J_{v_0(c')})$ and $a \nmid d' \ mod\, (J_{v_0(d')})$.*" (L168–172, pp.1209–1210; statement straddles the page break)

**A.8.2 [DEF] Proposition 3.2 ("almost prime").**
> "**Proposition 3.2.** *Let $a, b, c, d \in K((\mathbb{R}^{\leq 0}))$ be such that $v_0(a) = \omega, v_0(b) = \omega^{\delta+n}, v_0(c) = \omega^{\delta_1+r}, v_0(d) = \omega^{\delta_2+s}$; where $\delta, \delta_1, \delta_2 \in Lim \cup \{0\}$ and $n, r, s \in \mathbb{N}$. Let $k, l \in \mathbb{N}^*$ and assume that $a^k b = c^l d \ mod\, (J_{v_0(a^k b)})$. Then $a\,|\,c \ mod\, (J_{v_0(c)})$ or $a\,|\,d \ mod\, (J_{v_0(d)})$.*" (L227, p.1211)
> "**Proof.** By induction on the complexity of $(b, c, d, l)$." (L229)

**A.8.3 [DEF] Theorem 3.3 ("the main result").**
> "We are now ready to prove the main result." (L340)
> "**Theorem 3.3.** *Let $a \in K((\mathbb{R}^{\leq 0}))$ of order type $\omega$ or $\omega + 1$, and such that $v_0(a) = \omega$. Then $a$ is prime in $K((\mathbb{R}^{\leq 0}))$.*" (L344, p.1213)

Section-opening paraphrase: "We prove in this section that if $a \in K((\mathbb{R}^{\leq 0}))$ is of order type $\omega$ or $\omega + 1$ and satisfies $v_0(a) = \omega$, then $a$ is prime in $K((\mathbb{R}^{\leq 0}))$." (L142). Note the hypothesis form: "of order type $\omega$ or $\omega+1$" together with "$v_0(a) = \omega$" (the latter rules out a series of type $\omega$ whose support is bounded away from 0 plus a constant, and says the $\omega$-part accumulates at 0).

**A.8.4 [DEF] Theorem 4.1 (archimedean case).**
> "**Theorem 4.1.** *Let $G$ be an ordered abelian divisible archimedean group. Let $a \in K((G^{\leq 0}))$ be of order type $\omega$ or $\omega + 1$ and such that $S_a \setminus \{0\}$ is cofinal to $0$. Then $a$ is prime in $K((G^{\leq 0}))$.*" (L398–399, p.1214)

Here the condition "$v_0(a) = \omega$" is replaced by "$S_a \setminus \{0\}$ is cofinal to $0$" (because $v_0$ was defined only over $\mathbb{R}$). Also in §1: "whose support is cofinal to 0" (L51). "cofinal" ×2.

**A.8.5 [DEF] Theorem 4.2 (maximal proper convex subgroup).**
> "**Theorem 4.2.** *Let $G$ be an ordered abelian divisible group which contains a maximal proper convex subgroup $G_0$. Let $Q$ be a divisible archimedean subgroup of $G$ such that $Q \cap G_0 = \{0\}$. Let $a \in K((Q^{<0}))$ be of order type $\omega$ such that $a$ is not divisible by any monomial $x^\gamma$ for $\gamma \in Q^{<0}$. Then $a + 1$ is prime in $K((G^{\leq 0}))$.*" (L407–409, p.1214)

Existence aside: "[ First observe that such $Q$ and $a$ always exist: Choose $\gamma_0 \in G^{<0} \setminus G_0$ and set $Q := \{\frac{p \gamma_0}{q} \ ; \ p \in \mathbb{Z},\ q \in \mathbb{Z}^*\}$, $a := \sum_{n \geq 1} x^{\gamma_0 / n}$ ]. See Figure 3." (L411–412). The decomposition and isomorphism: "As $G$ is divisible, there exists a subgroup $H$ of $G$ such that $G = H \oplus G_0$. $H$ can be chosen such that $H \supseteq Q$ because $Q \cap G_0 = \{0\}$. Moreover, as $G_0$ is a maximal proper convex subgroup, $H$ is archimedean and the order of $G$ is the lexicographic order on $G = H \oplus G_0$. Hence there is a canonical ordered fields isomorphism $i : K((G)) \longrightarrow K((G_0))((H))$ and $i(K((G^{\leq 0}))) \subseteq K((G_0))((H^{\leq 0}))$." (L414–421, pp.1214–1215). Note "canonical ordered fields isomorphism" (sic, plural "fields") and the letter $i$ for it.

**A.8.6 [DEF] Example ($G = \mathbb{R}^\alpha$).**
> "**Example.** Let $\alpha \in OR$ and $G = \mathbb{R}^\alpha$ ordered lexicographically, where $$\mathbb{R}^\alpha := \{(x_0, x_1, ..., x_\beta, ...) \mid x_\beta \in \mathbb{R} \ \forall\, \beta < \alpha\}.$$ Let $a = x^{-1} + x^{-1/2} + x^{-1/3} + x^{-1/4} + ...$, where $-1/n := (-1/n, 0, 0, 0, ...) \in \mathbb{R}^\alpha \ \forall\, n \in \mathbb{N}^*$. Then $a + 1$ is prime in $K((G^{\leq 0}))$." (L427–431, p.1215)

Also in §1: "(e.g., $G = \mathbb{R}^\alpha$ with lexicographic order, $\alpha$ ordinal)" (L47). Convention: $\mathbb{R}^\alpha$ is the full product (all functions $\alpha\to\mathbb{R}$), not the Hahn group of well-ordered-support functions; the transcription shows no restriction.

**A.8.7 [DEF/ASSUMED] "Conway's series".**
> "In particular, this implies that Conway's series $x^{-1} + x^{-1/2} + x^{-1/3} + ... + 1$ is prime in the model of open induction $\mathbb{R}((\mathbb{R}^{<0})) \oplus \mathbb{Z}$." (L144, p.1209)

The name "Conway's series" is used once, for the specific series with the $+1$. Written with exponents in increasing order, the constant last.

### A.9 Synonym inventory (one object, several words)

| Object | Forms used | Dominant |
|---|---|---|
| element of $K((G))$ | "formal series" (×1), "series" (≈15), "generalized power series" (×5), "element(s)" (L14, L45) | "series" |
| $K((G^{\leq 0}))$ | "the ring $K((G^{\leq 0}))$ of series with non-positive exponents" (L14), "the subring of $K((G))$" (L27), bare symbol | bare symbol |
| $v_0$ | "ordinal valued map" (L41), ""ordinal valuation"" (L70), bare symbol $v_0$ | $v_0$ |
| $v_0(bc) = v_0(b)\odot v_0(c)$ | "Berarducci's formula", "(B)", "Lemma 2.1 d)" | "(B)" |
| natural product / sum | "$\odot$ ... the commutative (natural) product of ordinals" (L111), "the natural product" (L43), "$\oplus$ ... the natural sum" (L350) | symbols |
| order type of a series | "of order type $\omega$", "$ot(b)$", "$\omega-$series", "primes of type $\omega+1$", "has order type $\omega+1$ in" | "of order type" |
| prime element | "prime elements (i.e., elements generating prime ideals)" (L45), "prime i.e., generate a prime ideal" (L14), "primes" (L52, L54, section titles), "$a$ is prime in $R$" | "is prime in" (×8) |
| irreducible | "irreducible elements" (L14, L39), "irreducibles" (×4), "non-standard irreducible" (L14) | "irreducible(s)" |
| divisibility | "$a \,|\, c$", "$a$ divides $c$" (gloss, L148), "divisible by" (L408), "$a \nmid c$" | "$a\,|\,c$" |
| congruence | "$a = b \bmod (J)$", "$a = b \bmod (J_{\omega^\alpha})$" | "$= \bmod (J_{v_0(\cdot)})$" |
| group $G$ | "ordered additive abelian group", "ordered additive abelian divisible group", "ordered abelian divisible group", "ordered abelian divisible archimedean group" | — |
| "maximal proper convex subgroup" (×5) vs "maximal convex proper subgroup" (×1, L47) | | "maximal proper convex subgroup" |
| $G=\mathbb{R}$ | "$G = (\mathbb{R}, +)$ is the additive group of the reals" (L14), "the additive group of the reals $G = (\mathbb{R}, +)$" (L43), "$G = (\mathbb{R}, +)$" | "$G = (\mathbb{R}, +)$" |
| archimedean | "archimedean (i.e., $G$ is isomorphic to a subgroup of $G = (\mathbb{R}, +)$)" (L51), "non - archimedean groups" (L43), "$G$ embeds in $\mathbb{R}$" (L401) | "archimedean" (lower-case a) |
| the point $0$ of the group | "0", "close to 0", "sufficiently close to $0$", "cofinal to 0", "accumulating towards 0" (figure caption, transcriber's) | — |

---

## Part B. What the paper reuses (with attribution quoted)

Reference list as printed (L437–455): [1] Berarducci, *Factorization in generalized power series*, Trans. AMS 352 (2000); [2] Conway, *On numbers and games* (1976); [3] Ecalle (1992); [4] Gonshor, *An introduction to the theory of surreal numbers* (1986); [5] Hahn, *Uber die nichtarchimedischen grossensysteme* (1907); [6] Kaplanski [sic], *Maximal fields with valuations* (1942); [7] Mourgues and Ressayre, *Every real closed field has an integer part*, this Journal (1993); [8] Pitteloud, *Algebraic properties in rings of generalized power series*, APAL, to appear; [9] Pohlers, *Proof Theory* (1989); [10] Ressayre, *Integers parts of real closed exponential fields* (1993); [11] Ressayre, *Survey on transfinite series and their applications* (1995, manuscript); [12] Ribenboim, *Fields, algebraically closed and others* (1992); [13] van den Dries, Macintyre, Marker, *The elementary theory of restricted analytic fields with exponentiation* (1994); [14] same, *Logarithmic-exponential power series* (1997); [15] same, *Logarithmic-exponential power series*, preprint 1998 [sic — [14] and [15] carry the same title in the transcription; **[UNVERIFIED]** whether the original has "Logarithmic-exponential series" for [15]]; [16] van der Hoeven, *Asymptotique automatique* (1997). Note: [7] Mourgues–Ressayre is listed but **never cited in the body**; the body's "an idea of Gonshor and Mourgues" (L43) carries no citation.

### B.1 From Berarducci [1]

**B.1.1 [REUSE] The result that irreducibles exist, and the question answered.**
> "Berarducci (see [1]) proved that $K((G^{\leq 0}))$ does have irreducible elements, but it remained open whether the irreducibles are prime i.e., generate a prime ideal." (L14, abstract)
> "Very recently, Berarducci (see [1]) proved that $K((G^{\leq 0}))$ does have irreducible elements, hence answering a question of Conway and Gonshor (see [2, 4])." (L39, p.1207)
> "He left open the question whether $K((G^{\leq 0}))$ contains prime elements (i.e., elements generating prime ideals) even if $G = (\mathbb{R}, +)$." (L45)

**B.1.2 [REUSE] The map $v_0$ — taken unchanged, with Berarducci's symbol.**
> "In order to prove the existence of irreducibles, Berarducci introduces an ordinal valued map $v_0 : K((G^{\leq 0})) \longrightarrow OR$ (see section 2)." (L41, p.1207)
> "In order to prove the existence of irreducibles in $K((G^{\leq 0}))$, Berarducci introduced an "ordinal valuation" $v_0 : K((G^{\leq 0})) \longrightarrow OR$. Before defining this map, we recall some basic definitions which all appear in [1]." (L70, p.1207)

Symbol $v_0$ kept; the name is given as "ordinal valuation" in scare quotes (once) and "ordinal valued map" (once). Full definition reproduced — see A.5.1. Whether Berarducci's definition is word-for-word the same is not stated.

**B.1.3 [REUSE] The formula $v_0(bc) = v_0(b)\odot v_0(c)$ — kept, newly labelled "(B)".**
> "He first considers the case of the additive group of the reals $G = (\mathbb{R}, +)$ and shows that $v_0(bc)$ can be computed in terms of $v_0(b)$ and $v_0(c)$ using the natural product, by the formula $v_0(bc) = v_0(b) \odot v_0(c)$ (see section 2)." (L43)
> "Berarducci's formula, which we call **(B)**, states that ..." (L107)

**B.1.4 [REUSE] The "basic definitions" $b_{|\gamma}$, $b^{|\gamma}$, $J$ — "which all appear in [1]" (L70). See A.3. Whether the symbols are Berarducci's or re-symbolled is not said; the paper presents them as recalled.

**B.1.5 [REUSE] Lemma 2.1 — "the following facts (see [1]) which we will repeatedly use (without mention) in all this paper" (L125). See A.5.5.

**B.1.6 [REUSE] $J$ prime for $G=\mathbb{R}$.**
> "[ It was proved in [1] for $G = (\mathbb{R}, +)$ ]." (L64) — referring to "the ideal $J \subseteq K((G^{\leq 0}))$ generated by the set of monomials $\{\, x^\gamma : \gamma \in G$ and $\gamma < 0 \,\}$ is prime".

**B.1.7 [REUSE] The reduction from general $G$ to the archimedean case — "an idea of Gonshor and Mourgues" as used in [1]; the proof of Theorem 4.2 is Berarducci's.**
> "And then to deal with the general case (i.e., non - archimedean groups) he uses an idea of Gonshor and Mourgues." (L43)
> "The proof of the next theorem is exactly the same as in [1], so we only sketch it." (L405, p.1214)

**B.1.8 [REUSE] Berarducci's second question — settled in [8], the author's companion paper.**
> "**Remark.** In our paper [8] we solved affirmatively another question of [1] by proving that the ideal $J \subseteq K((G^{\leq 0}))$ generated by the set of monomials $\{\, x^\gamma : \gamma \in G$ and $\gamma < 0 \,\}$ is prime for any $G$. [ It was proved in [1] for $G = (\mathbb{R}, +)$ ]. The results of this paper and [8] are independent." (L64–66, p.1207)

### B.2 From Conway [2] and Gonshor [4]

**B.2.1 [REUSE] The problem: irreducible/prime omnific integers, and its equivalence to $K((G^{\leq 0}))$.**
> "Conway and Gonshor (see [2, 4]) considered the problem of existence of non-standard irreducible (respectively prime) elements in the huge "ring" of omnific integers, which is indeed equivalent to the existence of irreducible (respectively prime) elements in the ring $K((G^{\leq 0}))$ of series with non-positive exponents." (L14, abstract)

Note the scare quotes on "ring" (omnific integers form a proper class) and the adjective "huge". The equivalence is asserted without proof or citation. "Conway's series" (L144) — see A.8.7.

### B.3 From Hahn [5], Ribenboim [12], Kaplansky [6]

**B.3.1 [REUSE]** "With obvious operations $+$ and $\cdot$, $K((G))$ is a field (Hahn 1907, see [5])." (L25) — the field structure attributed to Hahn.

**B.3.2 [REUSE]** "These fields $K((G))$ play an important role in the theory of real closed fields because if $K$ is real closed and $G$ is divisible, then $K((G))$ is still real closed (see e.g., [12])." (L31)

**B.3.3 [REUSE]** "Moreover, it is a classical fact that if $F$ is a real closed field, then $F$ embeds in some $\mathbb{R}((G))$, see [6]." (L33)

### B.4 From Pohlers [9]

**B.4.1 [REUSE]** Natural product and sum of ordinals, $\odot$ and $\oplus$ — "the commutative (natural) product of ordinals (see [9])" (L111); "[$\oplus$ denotes the natural sum of ordinals, see e.g., [9]]" (L350). Symbols $\odot$, $\oplus$ — whether these are Pohlers's symbols is not said (Pohlers is a proof-theory text; the paper cites it for the definitions only).

### B.5 Background literature cited as a block

**B.5.1 [REUSE]** "Generalized power series and some variants have been studied by van den Dries, Ecalle, van der Hoeven, Macintyre, Marker, Ressayre and others, in connection with the study of asymptotic functions and o-minimal structures (see e.g., [13, 14, 15, 3, 16, 11, 10])." (L37, p.1207) — no terms or symbols taken from these.

### B.6 From the author's own [8]

**B.6.1 [REUSE]** Primality of $J$ for all $G$ (quoted in B.1.8). Nothing else from [8] is used; "The results of this paper and [8] are independent." (L66).

---

## Part C. What the paper assumes you have read (field notions used without definition or citation)

For each: the term, how it is used, a representative quote, and — marked as **my inference** — the meaning I attach. The paper does not define any of these.

**C.1 [ASSUMED] "prime" (element), "prime ideal", "generate a prime ideal".** Used as the target property; glossed only by "i.e., generate a prime ideal" (L14) / "(i.e., elements generating prime ideals)" (L45). The working definition in §3 is the one actually used: "let $b, c, d \in K((\mathbb{R}^{\leq 0}))$ be such that $ab = cd$. We want to prove that $a \,|\, c$ or $a \,|\, d$" (L148). *Inference:* prime = nonzero non-unit generating a prime ideal; the paper never says "non-unit" or "nonzero" explicitly for $a$ — it relies on $v_0(a)=\omega$ (which forces $a\notin K$ and $a\ne0$). Statement form: "$a$ is prime in $K((\mathbb{R}^{\leq 0}))$" (×8 "is prime in").

**C.2 [ASSUMED] "irreducible".** "$K((G^{\leq 0}))$ does have irreducible elements" (L14, L39); "the existence of irreducibles" (L41, L70); "whether all irreducibles in $K((G^{\leq 0}))$ are prime even if $G = (\mathbb{R}, +)$" (L54). Not defined. *Inference:* standard ring-theoretic irreducible (non-unit, not a product of two non-units).

**C.3 [ASSUMED] "omnific integers", "non-standard".** "non-standard irreducible (respectively prime) elements in the huge "ring" of omnific integers" (L14). Not defined; attributed to Conway/Gonshor for the *problem* but the term itself is taken as known. *Inference:* Conway's $\mathbf{Oz}$, the integer part of the surreals; "non-standard" = not in $\mathbb{Z}$.

**C.4 [ASSUMED] "real closed field", "ordered field".** "plays an important role in the study of real closed fields" (L14); "if $K$ is real closed and $G$ is divisible, then $K((G))$ is still real closed" (L31); "If $K$ is an ordered field, so is $K((G))$" (L25). Standard; not defined.

**C.5 [ASSUMED] "the model of open induction $\mathbb{R}((\mathbb{R}^{<0})) \oplus \mathbb{Z}$".** L144, once. Not defined and not cited (though [7], [10] in the reference list are about integer parts). *Inference:* the integer part of $\mathbb{R}((\mathbb{R}))$ consisting of series with negative exponents plus an integer constant, known to be a model of open induction (Shepherdson-type); $\oplus$ here is internal direct sum of additive groups. Note this object is *not* $K((\mathbb{R}^{\leq 0}))$ (the constant term is restricted to $\mathbb{Z}$); the paper passes from primality in $K((\mathbb{R}^{\leq 0}))$ to primality there with "In particular, this implies" and no argument.

**C.6 [ASSUMED] "archimedean" (group), "$G$ embeds in $\mathbb{R}$".** Glossed once: "archimedean (i.e., $G$ is isomorphic to a subgroup of $G = (\mathbb{R}, +)$)" (L51); used: "As $G$ is archimedean, $G$ embeds in $\mathbb{R}$. So we can assume that $G \subseteq \mathbb{R}$." (L401); "non - archimedean groups" (L43); "$H$ is archimedean" (L418). Lower-case "archimedean" throughout (×7). The embedding theorem (Hölder) is used without name or citation.

**C.7 [ASSUMED] "convex subgroup", "maximal proper convex subgroup".** Title of §4 and L47, L52, L407, L414–418. Not defined. *Inference:* convex = order-convex subgroup; "maximal proper convex subgroup" = the largest convex subgroup $\ne G$ (exists iff the value set of $G$ has a greatest element / $G$ has a "last" archimedean class). The paper uses: "as $G_0$ is a maximal proper convex subgroup, $H$ is archimedean and the order of $G$ is the lexicographic order on $G = H \oplus G_0$" (L418) — this is assumed known.

**C.8 [ASSUMED] "divisible" group; complement of a convex subgroup.** "As $G$ is divisible, there exists a subgroup $H$ of $G$ such that $G = H \oplus G_0$." (L414). Uses that divisible abelian groups are injective, without saying so.

**C.9 [ASSUMED] "lexicographic order" / "ordered lexicographically".** On $H\oplus G_0$ (L418), on $\mathbb{R}^\alpha$ (L47, L427), on $(OR)^4$ (L219). ×4. Not defined. *Inference:* first coordinate dominates — consistent with $H$ (the archimedean quotient-like part) being the *first* summand in $G = H\oplus G_0$ and with $-1/n := (-1/n, 0, 0, \dots)$ in $\mathbb{R}^\alpha$ being the "large" coordinate.

**C.10 [ASSUMED] "cofinal to $0$".** "whose support is cofinal to 0" (L51); "$S_a \setminus \{0\}$ is cofinal to $0$" (L399). Not defined. *Inference:* $\sup (S_a\setminus\{0\}) = 0$ with $0\notin S_a\setminus\{0\}$, i.e. the negative support accumulates at $0$ from below. This is the $G$-version of "$v_0(a) = \omega$" for a type-$\omega$ series.

**C.11 [ASSUMED] "sufficiently close to $0$" / "close to $0$" / "sufficiently small".** The paper's standing idiom for "for all $\gamma\in\mathbb{R}^{<0}$ in some neighbourhood $]-\varepsilon,0[$": "for all $\gamma \in \mathbb{R}^{<0}$ sufficiently close to 0" (L104); "for all $\gamma, \eta$ sufficiently close to $0$" (L131); "Let $\gamma \in S_a \setminus \{0\}$ be fixed sufficiently close to $0$" (L168); "as $\gamma$ is close to 0" (L201); "($\gamma$ is close to 0)" (L266); "for $\varepsilon > 0$ sufficiently small" (L99). Counts: "sufficiently close to" ×5, "close to 0" ×6. Never "eventually", never "germ", never "for $\gamma$ near $0$".

**C.12 [ASSUMED] "the iterated construction $K((G_0))((H))$ and the canonical isomorphism $K((G)) \cong K((G_0))((H))$ for $G = H \oplus G_0$ lexicographic".** "Hence there is a canonical ordered fields isomorphism $i : K((G)) \longrightarrow K((G_0))((H))$" (L420–421). Presented as known ("Hence"). *Inference:* the standard Hahn-field decomposition along a convex subgroup.

**C.13 [ASSUMED] $a\,|\,c$ in a ring; "$a \,|\, 0$".** "if $b, c$ or $d$ is 0, then the result is obvious because $a\,|\,0$" (L352).

**C.14 [ASSUMED] "question of Conway and Gonshor".** Named as a known open problem (L39, L45); no statement of the question beyond the abstract's paraphrase.

**C.15 [ASSUMED] "asymptotic functions", "o-minimal structures".** L37, background only.

---

## Part D. Generic machinery presupposed (standard mathematics from outside the field)

Listed briefly; quotes only where the paper fixes a choice among variants.

- **Ordinals, the class $OR$, limit ordinals, ordinal exponentiation $\omega^\alpha$, Cantor normal form.** Choice fixed: C.n.f. written as a sum of powers $\omega^{\alpha_1}+\dots+\omega^{\alpha_n}$ with $\alpha_1\ge\dots\ge\alpha_n$ (no multiplicities), L105, L354. Every $v_0$-value is written $\omega^{\delta+n}$, $\delta\in\mathrm{Lim}\cup\{0\}$, $n\in\mathbb{N}$ (L136 etc.).
- **Natural (Hessenberg) sum and product** — cited to [9] (B.4.1); symbols $\oplus$, $\odot$.
- **Order types of well-ordered subsets of $\mathbb{R}$**; "$ot$"; the fact that a well-ordered set of reals has countable order type is not mentioned.
- **Lexicographic order on tuples** $(OR)^4$ (L219) and on products of groups.
- **Transfinite induction** — "by induction on the complexity" (L229) over the lexicographically ordered $(OR)^4$; "by induction on $ot(c) \oplus ot(d)$" (L350). Phrase "by induction" ×11; "Applying again induction $(k-3)$- times" (L258).
- **Ideals, quotients, congruence "mod" an ideal** — written "$= \bmod (J)$" with an equals sign (A.6.1).
- **Binomial theorem** — the expansion in the proof of Lemma 3.1: "$\sum_{2 \leq i \leq l} \binom{l}{i} c^{l-i} (c^{|\gamma})^i a^{i-2}$" (L190), introduced by "Elementary algebra shows that this last equation can be written as" (L184).
- **Supremum / minimum in $\mathbb{R}$** — $\min S_a$ (L25), $\sup(S_u)$ (L342), $\sup S_{b_i'}$ (L360).
- **Divisible abelian groups split off direct summands** (L414).
- **Hölder's theorem** (archimedean ⇒ embeds in $\mathbb{R}$), L401, unnamed.
- **Field of fractions / "As $K((G))$ is a field, $u = c/a \in K((G))$"** (L403) — used to pull a quotient back into the subring: "So $u \in K((\mathbb{R}^{\leq 0})) \cap K((G)) = K((G^{\leq 0}))$ and we are done." (L403). The intersection identity is asserted without comment.
- **Interval notation** $[-\varepsilon, 0[$ (L99) — French/Bourbaki half-open bracket style.
- **Set-builder with semicolon** "$\{\frac{p \gamma_0}{q} \ ; \ p \in \mathbb{Z},\ q \in \mathbb{Z}^*\}$" (L412) vs colon elsewhere ("$\{\gamma \in G : a_\gamma \neq 0\}$", L24) — both occur.

---

## Part E. How the paper talks: verbs, phrases, statement shapes

Representative sentences, grouped by what is being done. These are the models.

### E.1 Introducing the objects
- "If $K$ is any field and $G$ any ordered additive abelian group, $K((G))$ is the set of all formal series ... having well-ordered support $S_a := \{\gamma \in G : a_\gamma \neq 0\}$." (L20–24)
- "$K((G))$ is called the field of generalized power series with coefficients in $K$ and exponents in $G$." (L26)
- "$K((G^{\leq 0}))$ denotes the subring of $K((G))$ whose series have their support included in $G^{\leq 0}$" (L27)
- "From now on, $K$ will always denote ... and $G$ ..." (L29)
- Definitions are introduced by bold "**Definitions.**"/"**Definition.**"/"**Notation(s).**" headings followed by numbered items using "$:=$"; names are attached with "is the truncation of $b$ at $\gamma$" (L74), "we say that $\gamma \in \mathbb{R}^{<0}$ is a big point of $u$ if" (L225), "$u^L$ denotes the supremum of $S_u$" (L342), "$OR$ denotes the class of all ordinals" (L86), "ot abbreviates order type" (L88).

### E.2 Stating primality / divisibility
- "$a$ is prime in $K((\mathbb{R}^{\leq 0}))$" (L142, L344); "Then $a + 1$ is prime in $K((G^{\leq 0}))$" (L409, L431); "$i(a + 1)$ is prime in $K((G_0))((H^{\leq 0}))$ by theorem 3.3" (L425).
- "$K((G^{\leq 0}))$ does have irreducible elements" / "does have prime elements" (L14, L39) — emphatic "does have".
- "$K((G^{\leq 0}))$ contains primes of type $\omega + 1$" (L52); "contains prime elements" (L45).
- "We want to prove that $a \,|\, c$ or $a \,|\, d$ in $K((\mathbb{R}^{\leq 0}))$." (L148)
- "Then $a\,|\,c \ mod\, (J_{v_0(c)})$ or $a\,|\,d \ mod\, (J_{v_0(d)})$." (L227)
- "$a$ is not divisible by any monomial $x^\gamma$ for $\gamma \in Q^{<0}$" (L408)
- "the ideal $J$ ... is prime for any $G$" (L64)

### E.3 Talking about $v_0$, order type, support
- "$a \in K((\mathbb{R}^{\leq 0}))$ is of order type $\omega$ or $\omega + 1$ and satisfies $v_0(a) = \omega$" (L142); "Let $a \in K((\mathbb{R}^{\leq 0}))$ of order type $\omega$ or $\omega + 1$, and such that $v_0(a) = \omega$." (L344)
- "be such that $v_0(a) = \omega$ and $v_0(b) = \omega^{\delta+n}$, where $\delta \in \mathrm{Lim} \cup \{0\}$ and $n \in \mathbb{N}$" (L136)
- "$i(a + 1)$ has order type $\omega + 1$ in $K((G_0))((H^{\leq 0}))$" (L423)
- "whose support is cofinal to 0" (L51); "such that $S_a \setminus \{0\}$ is cofinal to $0$" (L399)
- "for $\gamma \in \mathbb{R}^{<0}$ sufficiently close to 0" (L104); "Let $\gamma \in S_a \setminus \{0\}$ be fixed sufficiently close to $0$" (L168); "Let $\gamma \in S_a \setminus \{0\}$ be fixed, sufficiently close to 0." (L238)
- "we assume that $v_0(b), v_0(c), v_0(d)$ are $> 1$" (L366)
- "$v_0(bc)$ can be computed in terms of $v_0(b)$ and $v_0(c)$ using the natural product" (L43)

### E.4 Invoking results
- "Corollary 2.2 yields" (L174, L238); "(5) yields" (L326); "Then (\*) yields" (L316).
- "(1), Lemma 2.1 and **(B)** imply that" (L211); "then $(B)$ implies that $k$ is determined by $b, c, d, l$" (L223).
- "Using Lemma 2.1 and $v_0(c^{|\gamma}) < \omega^{\delta_1}$, we easily prove that" (L196).
- "using $(B)$ and the convolution formula it is easy to prove that" (L368); "Using **(B)**, Lemma 2.1 and the convolution formula we get" (L380).
- "By Proposition 3.2, $a\,|\,x^{-\mu_1} c_1 \bmod (J_{\omega^{\gamma_1}})$ or ..." (L370).
- "by Theorem 3.3 $\exists u \in K((\mathbb{R}^{\leq 0}))$ such that, say, $c = au$" (L401).
- "applying Lemma 3.1 we get" (L234); "we can apply Lemma 3.1 for the equation $a^k b = c^l d \bmod (J_{v_0(a^k b)})$, and we get" (L276).
- "which we will repeatedly use (without mention) in all this paper" (L125).
- "The proof of the next theorem is exactly the same as in [1], so we only sketch it." (L405)
- "(Refer to figure 1)" (L95); "See Figure 3." (L412); "(see Figure 2, where we assume that ...)" (L366).

### E.5 Normalising / reducing without loss of generality
- "By dividing if necessary $a$ and $d$ by $k a_\gamma$ and $(k a_\gamma)^k$ respectively, we can as well assume that $k a^{|\gamma} = 1 \bmod (J)$." (L178)
- "Multiplying $b, c, d$ by $x^{-b^L}, x^{-c^L}, x^{-d^L}$ respectively, we can as well assume that $b^L = c^L = d^L = 0$." (L348)
- "By replacing $e$ by $e - e_{|\alpha}$ for $\alpha \in \mathbb{R}^{<0}$ sufficiently close to 0, we still have an equality like (6) and we can assume that $ot(ea) = \omega^{\gamma_1}$ or $\omega^{\gamma_1} + 1$." (L380)
- "So we can assume that $G \subseteq \mathbb{R}$." (L401)
- "$H$ can be chosen such that $H \supseteq Q$ because $Q \cap G_0 = \{0\}$." (L414)
Counts: "we can as well assume" ×2, "we can assume" ×3. Never "WLOG"/"without loss of generality".

### E.6 Manipulating the equation
- "By multiplying (\*) by $a$ and using $a^k b = c^l d \ \bmod (J_{v_0(a^k b)})$, we get" (L180); "Multiplying (\*) by $c$ and using ..., we get" (L246).
- "Elementary algebra shows that this last equation can be written as" (L184); "hence (\*\*) can be written as" (L206).
- "Write $d^{|\gamma} = ae + \varepsilon$, where $v_0(\varepsilon) < v_0(d^{|\gamma})$." (L254); "and write $x^{-\mu_1} c_1 = ea + \varepsilon$, where $v_0(\varepsilon) < \omega^{\gamma_1}$." (L376–378)
- "By substituting this in (1), dividing by $a$ and using $(B)$, we get" (L254); "Substituting (4) in the initial equation ..., we get" (L298); "By substituting (\*\*) in (\*), we get ... for some $b_0 \in A$" (L262).
- "Then equation (4) reduces to $b = c^l e \bmod (J_{v_0(b)})$." (L308)
- "whence" (×4: L298, L326, L384, L392); "Hence" (frequent); "So" (frequent); "we get" (×20).
- "for some $e \in K((\mathbb{R}^{\leq 0}))$ which is given by" (L188); "for some $b' \in A$" (L248).
- Equation tags: "(\*)", "(\*\*)", "(1)"–"(6)" restarted per proof; "(B)", "(C)" global.

### E.7 Structuring the induction
- "By induction on the complexity of $(b, c, d, l)$." (L229)
- "Assume that ... and that the result holds for all $(b', c', d', l') \in A^3 \times \mathbb{N}^*$ such that $Cpl(b', c', d', l') < Cpl(b, c, d, l)$." (L230)
- "By contradiction, suppose that $a \nmid c \bmod (J_{v_0(c)})$ and $a \nmid d \bmod (J_{v_0(d)})$." (L232)
- "As $Cpl(b', c', d', l) < Cpl(b, c, d, l)$ ... Hence by induction we get $a\,|\,c' \bmod (J_{v_0(c')})$ or $a\,|\,d' \bmod (J_{v_0(d')})$, which contradicts Lemma 3.1." (L235–236)
- "we have by induction" (L250, L302, L336); "we get by induction" (L272, L390); "By induction we get as before" (L256).
- Case structure: "**Case 1:** $r = 0$" / "**Case 2:** $r > 0$" (L194, L204); "**Case 1:** $\gamma$ **is a big point of** $d$." (L244); sub-cases "a) Assume that $\gamma$ is a big point of $c$" (L264), "b) Assume that $\gamma$ is not a big point of $c$" (L280), "We have to consider two subcases: i) ... ii) ..." (L294–306).
- Closing: "a contradiction." (×4); "This completes the proof of Case 1 (i.e., if $\gamma$ is a big point of $d$)." (L312); "This completes the proof of Proposition 3.2. $\dashv$" (L338); "which completes the proof of the lemma. $\dashv$" (L212); "So $a\,|\,c$ and we are done. $\dashv$" (L392); "and we are done. $\dashv$" (L403, L425).

### E.8 Hedging / ease markers
- "It is easy to prove that" (L82); "it is easy to prove that" (L368); "it is easy to conclude that" (L382); "we easily prove that" (L196); "We trivially have" (L200); "it is clear that" (L154, L354); "the result is obvious because" (L352); "With obvious operations" (L25); "It will follow quite easily that" (L161); "some experimental computations show that" (L159).
- "Now let us give the general idea of the proof." (L146); "Following these general ideas we will first prove that" (L161); "We will make this very precise later." (L158); "we have to be careful" (L158).

### E.9 Talking about the literature and open questions
- "Very recently, Berarducci (see [1]) proved that ... hence answering a question of Conway and Gonshor (see [2, 4])." (L39)
- "He left open the question whether ..." (L45); "it remained open whether the irreducibles are prime" (L14).
- "However, for general groups $G$ the existence of primes is still open, and it is also an open question whether all irreducibles in $K((G^{\leq 0}))$ are prime even if $G = (\mathbb{R}, +)$." (L54)
- "In our paper [8] we solved affirmatively another question of [1] by proving that" (L64)
- "More precisely we show that: 1. ... 2. ..." (L49–52)
- "it is a classical fact that" (L33); "plays an important role in the theory of real closed fields because" (L31).
- "We prove that this is the case if" (L47).

### E.10 The word "equation" and the word "complexity" together
- "When we speak of the complexity of the equation $ab = cd$, we have to be careful: If say $cd = c'd'$, does it follow that the complexity of $ab = cd$ is the same of that of $ab = c'd'$ ?" (L158) — note "the same of that of" (sic).

---

## Part F. Where the paper disagrees with, corrects, or departs from another paper's usage

Collected exhaustively; the paper is deferential to [1] and there are few such passages.

**F.1 Relabelling Berarducci's formula.** "Berarducci's formula, which we call **(B)**" (L107) — a new local name for an inherited result; not a correction.

**F.2 Scare-quoting Berarducci's name for $v_0$.** "Berarducci introduced an "ordinal valuation" $v_0$" (L70) — the quotation marks distance the author from the word "valuation" (the map is not a valuation in the usual sense: it is multiplicative via $\odot$, not additive, and is defined only on the subring). In §1 the author's own description is the neutral "an ordinal valued map" (L41). This is the only place where the paper visibly hesitates over an inherited word.

**F.3 Restricting the scope of $v_0$ to $\mathbb{R}$.** In §1 $v_0$ is described with domain $K((G^{\leq 0}))$ (L41, L70) but the definition given (L94) is for $K((\mathbb{R}^{\leq 0}))$ only, and Theorem 4.1 replaces "$v_0(a) = \omega$" by "$S_a \setminus \{0\}$ is cofinal to $0$" (L399). Not an explicit disagreement — a scoping choice.

**F.4 Extending [1]'s primality of $J$ from $\mathbb{R}$ to all $G$** (done in [8], reported here): "is prime for any $G$. [ It was proved in [1] for $G = (\mathbb{R}, +)$ ]." (L64). Generalisation, not correction.

**F.5 The "huge "ring" of omnific integers".** (L14) Scare quotes on "ring" — a quiet departure from Conway/Gonshor's usage of "ring" for a proper class; no comment beyond the quotes.

**F.6 Uncited attribution.** "he uses an idea of Gonshor and Mourgues" (L43) — attributes the archimedean-reduction idea to Gonshor and Mourgues rather than to Berarducci, without citing where it comes from (Mourgues–Ressayre [7] is in the reference list but never cited).

No passage says "unlike [n]", "contrary to", "we prefer", "we do not follow", or corrects an error in another paper.

---

## Part G. Source notes for a later reader

1. **Transcription only; no PDF.** Nothing was verified against the published article. Figures 1–3 exist only as the transcriber's bracketed prose (L80, L334, L374); Figure 2 is placed at L334 in the middle of the proof of Proposition 3.2 but belongs to the proof of Theorem 3.3 (L366 "see Figure 2"), and Figure 3 at L374 interrupts the proof of Theorem 3.3 but belongs to Theorem 4.2 (L412 "See Figure 3") — page-layout artefacts.
2. **Page mapping** is inferred (p = 1204 + transcription page marker); line numbers are exact.
3. **Typographic variance in the transcription** that should not be read as distinct notation: `\bmod (J_...)` vs `\ mod\, (J_...)` (italic statements); `\mathrm{Lim}` vs `Lim`; `\mathrm{ot}` vs `ot`; `max` unformatted (L129–130); "theorem 3.3" lower-case at L425.
4. **Passages that look garbled or doubtful** (flagged `[UNVERIFIED]` above): (a) L116 index letters $\beta_i, \xi_i$ in (C) vs $(\beta,\xi)$ at L120; (b) L306 "is a not big point"; (c) L158 "the same of that of"; (d) L208 equation (1) in Case 2 of Lemma 3.1 introduces $b'$ before it is defined (the definition comes at L210 only for $c', d'$; $b'$ is implicitly the coefficient of $a^{k+1}$ after using the hypothesis $a^{k-1}\,|\,c^{|\gamma}$) — this may be the original's terseness; (e) references [14] and [15] carry identical titles; (f) "Mathematicall", "Kaplanski", "Uber die nichtarchimedischen grossensysteme" (missing umlauts), "INSTITUTE D' INFORMATIQUE" — transcription or original typos, immaterial to terminology; (g) L51 "isomorphic to a subgroup of $G = (\mathbb{R}, +)$" reuses the letter $G$ for $\mathbb{R}$ inside a statement about $G$; (h) L248 and L266, L268 exponents mixing $\odot$, $\oplus$ and ordinary $+$ with no parentheses — precedence unverifiable; (i) L144 "the model of open induction $\mathbb{R}((\mathbb{R}^{<0})) \oplus \mathbb{Z}$" — the transcription's exponent set is $\mathbb{R}^{<0}$ (strict), which is what makes the $\oplus\mathbb{Z}$ a direct sum; plausible but unverified.
5. **Things the paper never does**, useful for the comparison: never writes $\equiv$; never uses "valuation" except in the quoted Berarducci phrase; never says "leading term/exponent/coefficient"; never says "germ", "derivative", "Leibniz", "UFD", "unit", "associate", "Hahn field", "Hahn series", "Mal'cev–Neumann", "$\mathbf{No}$", "surreal" (except in the title of [4]); never names the element $0$ of $G$ specially; never uses "supp"; never uses $\mathbf{On}$; never uses "well-ordered" after L24; never uses "transfinite".
6. **Entry count.** Part A: 47 entries (A.0.1–A.0.9, A.1.1–A.1.5, A.2.1–A.2.4, A.3.1–A.3.4, A.4.1–A.4.4, A.5.1–A.5.6, A.6.1–A.6.2, A.7.1–A.7.6, A.8.1–A.8.7) plus the synonym table (16 rows); Part B: 15 entries; Part C: 15 entries; Part D: 13 items; Part E: 10 phrase groups; Part F: 6 passages.

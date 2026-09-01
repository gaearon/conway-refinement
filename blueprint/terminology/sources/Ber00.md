# Ber00 — terminology record

**Paper.** Alessandro Berarducci, "Factorization in generalized power series", *Transactions of the American Mathematical Society* 352 (2), Feb. 2000, pp. 553–577. Received Sept. 12, 1996; revised July 22, 1997.

**Source used.** The 754-line Markdown transcription with LaTeX at
`blueprint/references/berarducci_2000_factorization_generalized_power_series.md`. No PDF or TeX
source was available for this audit, so no entry below was checked against the published rendering.
Where a reading depends on typography, it rests on the transcription and is flagged.

**How locations are given.** `§n` = paper section; `Def./Lemma/Thm./Cor./Rem./Fact n.m` = the paper's own numbering; `p. NNN` = journal page, recovered from the transcription's `<!-- page k -->` markers via journal page = k + 551 (page marker 2 = p. 553, the first page of the article; marker 26 = p. 577). `l. NNN` = line in the transcription file. Quotations are verbatim from the transcription, LaTeX included, except that display-math delimiters `$$` are dropped when a formula is quoted inline.

**Sections read.** All of them: title page/abstract (p. 553), §1 Introduction (1.1–1.6, pp. 553–559), §2 Outline (pp. 559–560), §3 Natural sum and product (pp. 561–562), §4 Well-ordered subsets (pp. 562–563), §5 Ordinal-value (pp. 563–565), §6 Principal and residual ordinal-values (pp. 565–566), §7 Convolution product (pp. 567–569), §8 Main lemma (pp. 569–570), §9 Induction (pp. 570–572), §10 Irreducible elements (pp. 572–573), §11 Series with finite support (p. 573), §12 Appendix (pp. 573–575), §13 Concluding remarks (pp. 575–576), Acknowledgments, References (pp. 576–577).

**Transcription oddities noticed while reading** (flagged again at the relevant entries):
- l. 124 (p. 557): "Hessemberg's product" — almost certainly "Hessenberg" in the original; the transcription may be reproducing a typo in the printed article or introducing one. Unverifiable.
- l. 252 (p. 561): "iff and only if" — a doubled connective; likely a typo in original or transcription.
- l. 294 (p. 563): "$< ot(B) \odot (C)$" — missing `ot`; should read `ot(B) \odot ot(C)`.
- l. 328 (p. 564): Remark 5.4 cites "Lemma 4.1 and Lemma 4.4"; the result needed is Lemma 4.5 (Lemma 4.4 is a definition). Probably an error in the published article, not the transcription.
- l. 458 (p. 568): "$c = \sum_{\gamma} c_{\xi} t^{\xi}$" — index should be $\xi$, not $\gamma$.
- l. 640 (p. 573): "who explained me how" — as printed presumably (non-native phrasing), not a mathematical issue.
- l. 650 (p. 574): "$K(\mathbf{G}^{\leq 0})$" with single parentheses — should be `K((\mathbf{G}^{\leq 0}))`.
- l. 696 (p. 575): "omnific interger" — typo.
- l. 160 (p. 558): "an **non-archimedean absolute value**" — article typo.
- l. 417 (p. 567): "under more general hypothesis" — singular, presumably as printed.
- The figure (Figure 1, p. 567) is described in brackets by the transcriber, not reproduced.

---

## Part A. What the paper defines (its own terms, notation, conventions)

Entries are numbered A1, A2, … and grouped by topic. For each: the term/symbol, the defining sentence verbatim, location, variants and rough counts, and notes.

### A.I The ambient objects: field, group, series ring

**A1. $K((\mathbf{G}))$ — "the field $K((\mathbf{G}))$ of generalized power series".**
Defining sentence (§1.1, p. 553, l. 19): "Given a field $K$ and an ordered abelian group $\mathbf{G} = (\mathbf{G}, +, 0, \leq)$, the field $K((\mathbf{G}))$ of generalized power series consists of all formal sums $a = \sum_{\gamma} a_{\gamma} t^{\gamma}$ with coefficients $a_{\gamma}$ in $K$, exponents $\gamma \in \mathbf{G}$ and well-ordered **support** $$S_a = \{\gamma \in \mathbf{G} \mid a_{\gamma} \neq 0\}$$ in the induced order of $\mathbf{G}$."
- Alternative notation acknowledged and declined (l. 23): "Another notation for $K((\mathbf{G}))$ is $K((t))^{\mathbf{G}}$, where the formal variable $t$ is displayed. We always use $t$ for the formal variable." The paper never uses $K((t))^{\mathbf{G}}$ again.
- Counts: `K((\mathbf{G}))` 15 occurrences; `\mathbf{R}((\mathbf{G}))` frequent in §1.1–1.3.
- Convention: the group is written in bold ($\mathbf{G}$), the coefficient field in roman italic ($K$), the reals/rationals/integers bold ($\mathbf{R}, \mathbf{Q}, \mathbf{Z}$). Whether the bold is the transcriber's rendering of blackboard bold or of printed boldface cannot be verified without the PDF.
- Convention: the group is written additively with identity 0 and the order symbol $\leq$ in the signature tuple $(\mathbf{G}, +, 0, \leq)$ (l. 19); once as $(\mathbf{G}, +, 0, <)$ (§4, l. 268).
- Convention: coefficients are indexed by the exponent, $a_{\gamma}$; the series is $a = \sum_{\gamma} a_{\gamma} t^{\gamma}$. Series are denoted by lower-case $a, b, c$; exponents by Greek letters $\alpha, \beta, \gamma, \delta, \xi$ (note: $\xi$ is used as a group element / exponent throughout §7–§10, and also as an ordinal in Cor. 9.9).

**A2. "support" $S_a$.**
Defined inside A1 (l. 19–21): "well-ordered **support** $S_a = \{\gamma \in \mathbf{G} \mid a_{\gamma} \neq 0\}$". Bold in the transcription, i.e. the paper's own emphasis. Also written $S_b$, $S_c$, and in §7 the support of $b$ is denoted by the capital letter $B$ ("the support $B$ of $b$", l. 451). Count: "support" 59 occurrences. Phrasing: "the support of $b$", "has support of order type $\omega$", "series with finite support", "the supports of $b, c$ are included in $Fin^{\leq 0}$" (l. 650).

**A3. Well-ordered.**
Explanation in passing (l. 23): "The fact that the support is well ordered (i.e. it contains no infinite descending chain) makes it possible to define the multiplication of two series by the usual convolution product". Spelling: both "well ordered" (9) and "well-ordered" (11) occur; hyphenated when attributive ("well-ordered subsets", "well-ordered support"), open when predicative ("is well ordered"). "anti-well-ordered" once (l. 72). "a fixed well ordering" once (Def. 9.3, l. 554).

**A4. Multiplication — "the usual convolution product".**
(l. 23): "the multiplication of two series by the usual convolution product: $(\sum_{\alpha} a_{\alpha} t^{\alpha})(\sum_{\beta} b_{\beta} t^{\beta}) = \sum_{\gamma} c_{\gamma} t^{\gamma}$, where $c_{\gamma} = \sum_{\alpha + \beta = \gamma} a_{\alpha} b_{\beta}$. (One must check that only finitely many terms in this summation are non-zero and that the set of $\gamma$ with $c_{\gamma} \neq 0$ is well ordered.)" Addition: "Addition of two series is defined in the obvious way." (l. 23).

**A5. $t$ — the formal variable.**
(l. 23): "We always use $t$ for the formal variable." Also "the formal variable $t$ is displayed". Convention: exponents of Conway's series are negative; see A44 for the change-of-variables remark.

**A6. The natural valuation $v$.**
(§1.1, p. 554, l. 34–38): "On $K((\mathbf{G}))$ we have a **natural valuation**: $v \colon K((\mathbf{G})) \to \mathbf{G}$, $a \mapsto \text{least element of } S_a$". Used again only in the proof of Thm. 12.1 (l. 650): "($v$ is the natural valuation into $\mathbf{G}$, not the ordinal value)". Convention: $v$ takes values in $\mathbf{G}$ (not in a "value group" $-\mathbf{G}$); $v(a) = \min S_a$; the paper explicitly distinguishes it from the ordinal value $v_J$.

**A7. Leading coefficient; order on $K((\mathbf{G}))$.**
(l. 40): "If $K$ is an ordered field, then we can define an order on $K((\mathbf{G}))$ by declaring an element $a \in K((\mathbf{G}))$ positive if its leading coefficient (i.e. the coefficient of $t^{v(a)}$) is a positive element of $K$." "leading coefficient" occurs once.

**A8. $\mathbf{G}^{<0}$, $\mathbf{G}^{>0}$, $\mathbf{G}^{\leq 0}$, $\mathbf{G}^{\geq 0}$ and the rings $K((\mathbf{G}^{<0}))$, $K((\mathbf{G}^{\leq 0}))$, etc.**
(§1.3, p. 554, l. 48–52): "$$\mathbf{R}((\mathbf{G})) = \mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{R} \oplus \mathbf{R}((\mathbf{G}^{>0}))$$ where $\mathbf{R}((\mathbf{G}^{<0}))$ consists of the series with negative exponents and $\mathbf{R}((\mathbf{G}^{>0}))$ consists of those with positive exponents."
Then (p. 555, l. 62–64): "the ring $$\mathbf{R}((\mathbf{G}^{\leq 0})) := \mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{R}$$ has any irreducible element, and we will consider the problem in this latter form."
- The superscript notation $\mathbf{G}^{\leq 0}$ etc. is never defined separately; it is introduced through these displays. Later also $Q^{<0}$, $Q^{\leq 0}$, $H^{<0}$, $H^{\leq 0}$, $\mu^{\leq 0}$, $Fin^{\leq 0}$, $\mathbf{R}^{\leq 0}$, $\mathbf{R}^{<0}$, $\mathbf{Q}^{\leq 0}$, $\mathbf{G}^{\geq 0}$ (l. 699), $\mathbf{G}^{>0}$ (for $\varepsilon \in \mathbf{G}^{>0}$, l. 324).
- The paper's main ring is written $K((\mathbf{G}^{\leq 0}))$ (44 occurrences) and $K((\mathbf{R}^{\leq 0}))$ (34); $\mathbf{R}((\mathbf{G}^{\leq 0}))$ (9) and $\mathbf{R}((\mathbf{G}^{<0}))$ (9) occur in the introduction when discussing the Conway–Gonshor problem with real coefficients.
- The paper never gives this ring a name; it says "the ring $K((\mathbf{G}^{\leq 0}))$", "the subring $K((\mathbf{G}^{\leq 0})) \subset K((\mathbf{G}))$" (l. 124), "our ring $\mathbf{R}((\mathbf{G}^{\leq 0}))$" (l. 64).
- Description in words (abstract, l. 13): "the ring $\mathbf{R}((\mathbf{G}^{\leq 0}))$ consisting of the generalized power series with non-positive exponents".
- Convention: $\oplus$ is used for internal direct sum of additive groups in these displays (and later for $Fin = H \oplus \mu$), and *also* for the natural sum of ordinals (A22). The two uses coexist without comment.

**A9. Units of $K((\mathbf{G}^{\leq 0}))$; irreducible elements.**
(p. 555, l. 64): "The units of $\mathbf{R}((\mathbf{G}^{\leq 0}))$ are the elements of $\mathbf{R}$, so the irreducible elements (if any) are those series $a \in \mathbf{R}((\mathbf{G}^{\leq 0}))$ which do not admit a factorization $a = bc$ with $b, c \notin \mathbf{R}$." Restated for general $K$ in §12 (l. 670): "the units of $F((H^{\leq 0}))$ are the elements of $F = K((\mu))$, while those of $K((Fin^{\leq 0}))$ are the elements of $K$."
- "irreducible" is never formally defined; it is used in the standard sense, made explicit by the sentence above. Counts: "irreducible" 61, "irreducibles" 5 (as a noun: "the absence of irreducibles", l. 68; "a ring without irreducibles", l. 64; "existence of irreducibles", l. 74, 90), "reducible" 2 ("trivially reducible", l. 140; "of course reducible", l. 78).
- "non-trivial factorization" (3): "Suppose $a = bc$ is a non-trivial factorization in $K((\mathbf{R}^{\leq 0}))$" (l. 630); defined in passing (l. 670): "(where "non-trivial" means $b, c \notin K$)". Also "with $b, c$ not invertible in $K((\mathbf{R}^{\leq 0}))$" (l. 618). "factorization" (10) with American spelling throughout; "factorisation" 0.
- Verbs: "is irreducible in $K((\mathbf{R}^{\leq 0}))$" (the ring is always named with "in"), "remains irreducible" (l. 102, 121: "Any irreducible element of $K[\mathbf{R}^{\leq 0}]$ remains irreducible in $K((\mathbf{R}^{\leq 0}))$"; "The primes of $\mathbf{Z}$ remain prime in …", l. 62), "does have irreducible elements" (l. 92), "has any irreducible element" (l. 64), "contains irreducible elements not in $\mathbf{Z}$" (l. 62).

**A10. Divisibility by a monomial; the ideal $J$.**
First (§1.6, p. 558, l. 140): "Let $J \subset K((\mathbf{G}^{\leq 0}))$ be the ideal generated by the set of monomials $\{t^{\gamma} \mid \gamma \in \mathbf{G}^{<0}\}$. An element is in $J$ iff it is divisible by a monomial, so all the elements of $J$ are trivially reducible."
Formal definition (Def. 5.1, p. 563, l. 312): "Let $J \subset K((\mathbf{G}^{\leq 0}))$ be the ideal generated by all the monomials $t^{\gamma}$ with $\gamma < 0$. We call the elements of the quotient ring $K((\mathbf{G}^{\leq 0}))/J$ **germs of power series**."
Characterisation (l. 314): "Clearly $J$ consists of all the series with negative support bounded away from zero: $b \in J$ iff $\exists \gamma \in \mathbf{G}$ such that $S_b \leq \gamma < 0$."
- Symbol: always $J$; never named other than "the ideal $J$" / "the ideal generated by the monomials".
- "monomial" (12): always "the monomial $t^{\gamma}$", "divisible by any monomial $t^{\gamma}$ with $\gamma < 0$" (Thm. 10.5, l. 616; Thm. 12.1: "with $\gamma \in Q^{<0}$"), "After multiplying by suitable monomials we can reduce to the case $b, c \notin J$" (l. 600), "the normalization factor $t^{-\gamma}$" (l. 184).
- Hypothesis phrasing for irreducibility theorems: "is not divisible by any monomial $t^{\gamma}$ with $\gamma < 0$" (l. 98, 616); "as otherwise the series is divisible by a monomial" (l. 104).

**A11. The maximal ideal $\mathcal{M}$.**
(l. 140): "Note that $J$ is not maximal, since it is properly contained in the maximal ideal $\mathcal{M} \subseteq K((\mathbf{G}^{\leq 0}))$ consisting of all series without constant term. We clearly have $$K((\mathbf{G}^{\leq 0}))/J \supsetneq K((\mathbf{G}^{\leq 0}))/\mathcal{M} = K$$". $\mathcal{M}$ appears only here (2 occurrences). "constant term" once.

**A12. Germs of power series; "have the same germ"; "common final part".**
(l. 144): "The elements of $K((\mathbf{G}^{\leq 0}))/J$ can be thought of as **germs of power series**. Two series (both not in $J$) have the same germ if they have a common final part."
(Def. 5.1, l. 312, quoted in A10.) Then (l. 314): "Two series $b, c \in K((\mathbf{G}^{\leq 0}))$ have the same germ iff for every $\gamma \leq 0$ sufficiently close to zero, the coefficients of $t^{\gamma}$ in $b$ and $c$ coincide. In particular, for $\gamma$ sufficiently close to zero, $\gamma \in S_b$ iff $\gamma \in S_c$."
- "germ" 7 occurrences total (including "germ at $\gamma$", A32). The quotient is otherwise always written $K((\mathbf{G}^{\leq 0}))/J$ or $K((\mathbf{R}^{\leq 0}))/J$, never given a letter.
- "final part" (4): "a common final part" (l. 144); "every ordinal has a final segment of type $\omega^{\alpha}$ (and the final part of a product of two series depends only on the final parts of the factors)" (l. 130). "final segment" (10) is the dominant term for the tail of a well-ordered set: "every sufficiently small non-empty final segment of $X(b)$" (Lemma 6.8), "every non-empty final segment of $B_i$ has order type $\geq \rho$" (Lemma 4.7), "a sufficiently small final segment of $b$" (l. 148).

**A13. $\equiv$ — congruence modulo $J$.**
(§2, l. 172): "In the sequel we write $\equiv$ for congruence modulo the ideal $J$." Re-stated locally several times: "Let $\equiv$ be the congruence relation modulo $J$" (Lemma 7.7, l. 476); "We write $\equiv$ for congruence modulo the ideal $J$" (proof of Lemma 8.2, l. 494; proof of Lemma 10.4, l. 614). Written in formulas as "$\equiv \ldots \bmod J$" (17 `\bmod`, 33 `\equiv`), e.g. "$b^{|\gamma} \equiv c^{|\gamma} \bmod J$", "$b^{|\beta} c^{|\xi} \not\equiv 0 \bmod J$".
- Variant: congruence modulo $J + K$, written "$c \equiv b \bmod J + K$" (Def. 5.2, l. 316–318): "We write as usual $c \equiv b \bmod J + K$ for $b - c \in J + K$."

**A14. $J + K$.**
(Def. 5.2, l. 316): "Let $J + K$ be the additive subgroup of $K((\mathbf{G}^{\leq 0}))$ generated by the ideal $J$ and the additive subgroup $K$." 12 occurrences. Convention: $K$ is identified with the constants inside $K((\mathbf{G}^{\leq 0}))$ without comment ("the additive subgroup $K$").

**A15. $K[\mathbf{G}]$ — "the ring of G-polynomials"; $K[\mathbf{G}^{\leq 0}]$.**
(Def. 11.1, p. 573, l. 626): "$K[\mathbf{G}]$, the ring of **G-polynomials**, is defined as the subring of $K((\mathbf{G}))$ consisting of all the series with finite support. We then define $K[\mathbf{G}^{\leq 0}]$ as $K[\mathbf{G}] \cap K((\mathbf{G}^{\leq 0}))$."
- Earlier, informally (l. 64): "the subring $\mathbf{R}[\mathbf{Q}^{\leq 0}]$ of $\mathbf{R}((\mathbf{Q}^{\leq 0}))$ consisting of the series with finite support"; (l. 84): "the subring $K[\mathbf{G}^{\leq 0}]$ of $K((\mathbf{G}^{\leq 0}))$ consisting of all series with finite support".
- "G-polynomials" appears once (the transcription has "G" in plain bold within the bolded term; whether the printed form is $\mathbf{G}$-polynomials is unverifiable). The dominant description is "series with finite support" (8 occurrences of "finite support").

**A16. $\mathbf{R}[\mathbf{Q}^{\leq 0}]$ — the Wilkie example.**
(l. 64): "Alex Wilkie noted that the Puiseux series with real coefficients form a real closed subfield of $\mathbf{R}((\mathbf{Q}))$ which has a standard part (and also an integer part) without irreducible elements. Such a standard part is given by the subring $\mathbf{R}[\mathbf{Q}^{\leq 0}]$ of $\mathbf{R}((\mathbf{Q}^{\leq 0}))$ consisting of the series with finite support. We thus have a nice example of a ring without irreducibles."

### A.II Integer parts, standard parts, truncation closure (§1.2–1.3)

**A17. Integer part.**
(§1.2, p. 554, l. 44): "An **integer part** of an ordered field $F$ (usually assumed to be real closed) is an ordered subring $Z$ having 1 as its least positive element and such that for each $a \in F$ there is $b \in Z$ (necessarily unique) such that $b \leq a < b + 1$." 22 occurrences. Phrasing: "has an integer part", "extract an integer part", "$\mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{Z}$ is an integer part of $\mathbf{R}((\mathbf{G}))$" (l. 54), "exponential integer part (in the sense of Ressayre)" (l. 694).

**A18. Discrete ring; infinitesimal / finite / infinite elements.**
(p. 555, l. 58): "Any integer part is a discrete ring, so in particular it contains no infinitesimal elements. The set of all infinitesimal elements of $\mathbf{R}((\mathbf{G}))$ is easily seen to be $\mathbf{R}((\mathbf{G}^{>0}))$, while $\mathbf{R}((\mathbf{G}^{>0})) \oplus \mathbf{R}$ is the set of all finite elements. All the elements of $\mathbf{R}((\mathbf{G}^{<0}))$ are infinite." Also "these discrete rings" (l. 46). None of these is defined; see Part C.

**A19. Truncation closed; truncations.**
(l. 60): "The ring $\mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{Z}$ is not the only integer part of $\mathbf{R}((\mathbf{G}))$, but it is the only one which is **truncation closed**, namely it has the property that if a series $\sum_{\beta} b_{\beta} t^{\beta}$ belongs to it, then also its truncations $\sum_{\beta < \alpha} b_{\beta} t^{\beta}$ belong to it. Truncation closedness plays a crucial role in the work of Ressayre and his collaborators." Note the truncation here is at $\beta < \alpha$ (strict), whereas Def. 6.1's "truncation of $b$ at $\gamma$" is $\beta \leq \gamma$ (non-strict) — see A31. Also "is *not* truncation closed" (l. 88).

**A20. Standard part.**
(l. 64): "The ring $\mathbf{R}((\mathbf{G}^{\leq 0}))$ is a **standard part** of $\mathbf{R}((\mathbf{G}))$ in the sense that every element of $\mathbf{R}((\mathbf{G}))$ is within infinitesimal distance from one and only one element of $\mathbf{R}((\mathbf{G}^{\leq 0}))$." 4 occurrences. "It is not true in general that a standard part of a real closed field necessarily has some irreducible element" (l. 64).

### A.III Ordinals (§3)

**A21. $OR$, $LIM$; ordinal arithmetic conventions.**
(§3, p. 561, l. 228): "We denote by $OR$ the class of all ordinals and by $LIM$ the class of all limit ordinals. The ordinal sum $\alpha + \beta$, ordinal product $\alpha \cdot \beta$ and ordinal exponentiation $\alpha^{\beta}$ are defined by induction on their second argument and are continuous in their second argument: $\alpha + 0 = \alpha, \alpha + (\beta + 1) = (\alpha + \beta) + 1$ and $\alpha + \lambda = \sup_{\xi < \lambda} \alpha + \xi$ for $\lambda \in LIM$; similarly for $\alpha \cdot \beta$ and $\alpha^{\beta}$. The product $\alpha \cdot \beta$ will also be written as $\alpha\beta$."
- $OR$ is first introduced at l. 120: "Let $OR$ be the class of all ordinal numbers." Written in italic/roman capitals $OR$, $LIM$ (not bold, not blackboard) in the transcription.
- Convention: ordinal product written by juxtaposition $\rho\alpha$, $\rho \cdot \lambda$; "ordinal multiplication is continuous in the second argument (unlike the natural product)" (l. 508).
- "$\omega$" is the first infinite ordinal, used without comment; "$\omega_1$" (first uncountable) used once (l. 238). "$k < \omega$", "$p \in \omega$" for natural numbers (l. 486, 572); also "$k_i \in \mathbf{N}$" (l. 170) and "$n$ ranges over the positive integers" (l. 70).

**A22. Additive principal; $\mathbf{H}$.**
(Def. 3.1, l. 230): "An ordinal $\rho$ is **additive principal** if it cannot be written as the ordinal sum of two ordinals strictly smaller than $\rho$. Let $\mathbf{H}$ be the class of all additive principal ordinals."
(Fact 3.2, l. 232–234): "1. $\rho \in \mathbf{H}$ iff for every $\alpha, \beta < \rho$, $\alpha + \beta < \rho$, 2. $\rho \in \mathbf{H}$ iff either $\rho = 0$ or there is $\alpha$ such that $\rho = \omega^{\alpha}$". Convention worth noting: **0 is additive principal** under this definition (Fact 3.2.2), and $1 = \omega^0$ too. 8 occurrences of "additive principal"; $\mathbf{H}$ 14.

**A23. Cantor normal form; principal part.**
(Fact 3.3, l. 238): "(Cantor normal form) For every ordinal $\alpha \neq 0$, there are uniquely determined ordinals $\alpha_1 \geq \ldots \geq \alpha_n$ such that $\alpha = \omega^{\alpha_1} + \ldots + \omega^{\alpha_n}$. The right-hand side is the **Cantor normal form** of $\alpha$, and we call $\omega^{\alpha_n}$ the **principal part** of $\alpha$."
- Convention: the CNF is written with **repetition of equal exponents** rather than with finite coefficients ($\omega^{\alpha_1} + \ldots + \omega^{\alpha_n}$ with $\alpha_1 \geq \ldots \geq \alpha_n$, not $\omega^{\alpha_1} c_1 + \ldots$).
- "principal part" = the *last* (smallest) term $\omega^{\alpha_n}$. Key fact (l. 240): "A fact that we will repeatedly use is that every sufficiently small final segment of a non-zero ordinal $\alpha$ has order type equal to the principal part of $\alpha$." 4 occurrences.

**A24. Natural sum $\oplus$, natural product $\odot$.**
(Def. 3.4, l. 242): "The **natural sum** $\oplus$ and **natural product** $\odot$ of two ordinals are commutative variants of the ordinal sum $+$ and ordinal product $\cdot$ (see [Hausdorff 27, p. 68] or [Pohlers 80]). To define the natural sum of two non-zero ordinals we consider the Cantor normal forms $\alpha = \omega^{\alpha_1} + \ldots + \omega^{\alpha_n}$ and $\beta = \omega^{\alpha_{n+1}} + \ldots + \omega^{\alpha_{n+m}}$, and we set $\alpha \oplus \beta = \omega^{\alpha_{\pi(1)}} + \ldots + \omega^{\alpha_{\pi(n+m)}}$, where $\pi$ is a permutation of the integers $1, \ldots, n+m$ such that $\alpha_{\pi(1)} \geq \ldots \geq \alpha_{\pi(n+m)}$. If $\alpha = 0$ we set $\alpha \oplus \beta = \beta \oplus \alpha = \beta$. The natural product is first defined on $\mathbf{H}$ by: $\omega^{\alpha} \odot \omega^{\beta} = \omega^{\alpha \oplus \beta}$ and $\gamma \odot 0 = 0 \odot \gamma = 0$. We then extend $\odot$ to all the ordinals using the Cantor normal form and distributivity: $\gamma \odot (\alpha \oplus \beta) = (\alpha \oplus \beta) \odot \gamma = (\alpha \odot \gamma) \oplus (\beta \odot \gamma)$."
- Introduced in §1.6 (l. 124) as "a commutative variant of it known as "**natural product**" or "Hessemberg's product" [Hausdorff 27], which we write as $\odot$" [sic: "Hessemberg"]; and (l. 128): "In general $\omega^{\alpha} \odot \omega^{\beta} = \omega^{\alpha \oplus \beta}$, where $\oplus$ is the "**natural sum**" of ordinals."
- Symbols: $\oplus$, $\odot$ throughout (never $\#$ or $\times$). Counts: "natural sum" 10, "natural product" 8. The ordered structure is written "$(OR, \oplus, \odot, \leq)$" (l. 160, 696) and "$(OR, \odot)$" (l. 692).
- (l. 246): "Clearly $\alpha \cdot \beta \leq \alpha \odot \beta$ and $\alpha + \beta \leq \alpha \oplus \beta$."
- Lemma 3.5 (l. 248–250): "1. *If $\alpha < \beta$, then $\alpha \oplus \gamma < \beta \oplus \gamma$.* 2. *If $\alpha < \beta$, then $\alpha \odot \gamma < \beta \odot \gamma$ provided $\gamma \neq 0$.*" — the paper proves this itself ("We now prove that $\oplus$ and $\odot$ are strictly increasing").
- Proof sentence fixing a convention for comparing ordinals (l. 252): "In other words, to compare two ordinals we compare lexicographically the exponents in their Cantor normal forms."

**A25. Iterated natural product $\overset{k}{\bigodot} \alpha$.**
(Def. 8.1, p. 569, l. 486): "For $\alpha \in OR$ and $k < \omega$, let $\overset{k}{\bigodot} \alpha = \alpha \odot \ldots \odot \alpha$ with $k$ occurrences of $\alpha$." Rendering of the superscript $k$ over $\bigodot$ is the transcriber's; unverifiable.

**A26. Multiplicative principal; $\mathbf{MP}$.**
(Def. 3.6, p. 562, l. 258): "$\mathbf{MP}$ is the class of all the **multiplicative principal** ordinals, namely the class of all $\alpha \in OR$ such that $\alpha > 0$ and for every $\beta, \gamma < \alpha$ we have $\beta\gamma < \alpha$."
(Fact 3.7, l. 262): "*Suppose $\beta, \gamma < \alpha$. If $\alpha \in \mathbf{H}$, then $\beta \oplus \gamma < \alpha$. If $\alpha \in \mathbf{MP}$, then $\beta \odot \gamma < \alpha$.*"
(Fact 3.8, l. 264): "*$\rho \in \mathbf{MP}$ if and only if $\rho = 1$ or $\rho$ is of the form $\omega^{\omega^{\alpha}}$.*"
- Convention: $\mathbf{MP}$ excludes 0 but includes 1 (and 2 is *not* of the form $\omega^{\omega^\alpha}$, so the paper's Fact 3.8 implicitly excludes 2 — this is a consequence of the definition with $\beta\gamma<\alpha$ for all $\beta,\gamma<\alpha$: $1\cdot 1 = 1 < 2$, so 2 would be in $\mathbf{MP}$ by Def. 3.6 but not by Fact 3.8. A later reader should be aware that Def. 3.6 and Fact 3.8 disagree at $\alpha = 2$; this is in the source as transcribed and may be in the original.)
- Prose description in §1.5 (l. 108): "The ordinals which appear in our criterion are exactly the infinite ordinals which cannot be obtained as a sum or product of two smaller ordinals: so what our criterion says is that if the order type is irreducible the series is irreducible." Note the phrase "the order type is irreducible" — an informal usage, once.
- 9 occurrences of "multiplicative principal"; $\mathbf{MP}$ 11.

**A27. Notation $[\alpha_0, \ldots, \alpha_m]$.**
(Def. 9.2, p. 570, l. 552): "Given ordinals $\alpha_0, \ldots, \alpha_m$, let $[\alpha_0, \ldots, \alpha_m] = \omega^{\alpha_0} \oplus \ldots \oplus \omega^{\alpha_m}$. Note that $[\alpha_0, \ldots, \alpha_m]$ decreases if any $\alpha_i$ is replaced by any finite number of smaller ordinals."

### A.IV Well-ordered subsets of a group (§4)

**A28. $B, C, \ldots$; $B \leq \gamma$; $\sup B$; $B + C$; $\overline{B}$.**
(§4, l. 268): "In the sequel $B, C, \ldots$ denote well-ordered subsets of $\mathbf{G}$. We write $B \leq \gamma$ if all elements of $B$ are $\leq \gamma$. Thus $\sup B = \gamma$ iff $B \leq \gamma$ and $\forall \beta < \gamma$, $B \not\leq \beta$. Since we do not (yet) assume that $\mathbf{G}$ is complete, the supremum might not exist."
(Def. 4.4, l. 284): "$B + C = \{x + y \mid x \in B, y \in C\}$."
(§7, l. 417): "Given a subset $B$ of $\mathbf{G}$, we denote by $\overline{B}$ its closure with respect to the order topology of $\mathbf{G}$."
- Convention: Minkowski sum is written $B + C$ with no special symbol; closure is overline. Also "$x \geq B_j$" for "$x$ is $\geq$ every element of $B_j$" (l. 306).

**A29. $ot$ — order type map (of a set, and of a series).**
Of a set: used from Lemma 4.1 on, "$ot(B \cup C) \leq ot(B) \oplus ot(C)$" (l. 270), never defined for sets (taken as standard, see Part C).
Of a series (§1.6, l. 120–124): "Consider the order type map $$ot \colon K((\mathbf{G})) \to OR$$ which assigns to each series the order type of its support."
(Def. 5.2, l. 316): "Given $b \in K((\mathbf{G}^{\leq 0}))$, we define its **order type** $ot(b) \in OR$ as the order type of the support $S_b$ of $b$."
- Counts: `ot(` 125; "order type" 57, "order types" 10, "ordinal type" 1 (l. 152: "which only speaks about ordinal types"). Phrasing: "has support of order type $\omega$" (l. 100), "the order type of the support of $a$ is either $\omega$ or of the form $\omega^{\omega^{\beta}}$" (l. 98), "series of order type $\omega$" (l. 706), "$B$ has limit order type" (Lemma 4.2), "additive principal order type $> 1$" (Lemma 4.3), "$b$ has limit order type" (l. 148).
- Convention: in the special case $\mathbf{G} = \mathbf{R}$, "the order types of the well-ordered subsets of $\mathbf{G}$ are exactly the countable ordinals" (l. 268); "any well-ordered subset of $\mathbf{R}$ is countable" (l. 606).

**A30. Lemmas 4.1–4.7 (the paper's own lemmas on order types).**
- Lemma 4.1 (l. 270): "$ot(B \cup C) \leq ot(B) \oplus ot(C)$."
- Lemma 4.2 (l. 278): "*If $B$ has limit order type and $B \leq 0$, then for every proper initial segment $H$ of $B$ there is $\gamma < 0$ such that $H \leq \gamma$.*"
- Lemma 4.3 (l. 282): "*If $\sup B = \sup C = 0$ and $B, C$ have additive principal order type $> 1$, then $ot(B \cup C) = \max\{ot(B), ot(C)\}$.*"
- Lemma 4.5 (l. 286): "$ot(B + C) \leq ot(B) \odot ot(C)$."
- Lemma 4.6 (l. 300): "*If $\lambda$ is a limit ordinal, then $\lambda$ coincides with the order type of the set $I \subseteq \lambda$ of all successor ordinals $\beta < \lambda$.*"
- Lemma 4.7 (l. 304): "*Let $\lambda$ be a limit ordinal and let $\{B_i \mid i < \lambda\}$ be a family of well-ordered subsets of $\mathbf{G}$ with the property that if $i < j < \lambda$, then $B_j$ has an element bigger than all elements of $B_i$. Suppose that for each $i < \lambda$ every non-empty final segment of $B_i$ has order type $\geq \rho$. If $\bigcup_{i<\lambda} B_i$ is well ordered, then it has order type $\geq \rho \cdot \lambda$.*"
- Prose restatement used repeatedly: "the order type of the union of two sets is bounded by the natural sum of the respective order types" (l. 294); "The order type of the union of finitely many sets is bounded by the natural sum of the respective order types" (l. 296).

### A.V The ordinal-value (§1.6, §5)

**A31. $v_J$ — "ordinal-value" (or "value").**
Announcement (§1.6, p. 558, l. 146–148): "We will define a map called **ordinal-value** $$v_J \colon K((\mathbf{G}^{\leq 0})) \to OR$$ which is similar to the order type map $ot$ but only assumes values of the form $\omega^{\alpha}$ or 0. If $b$ has limit order type and does not belong to $J$, then $v_J(b)$ is the order type of a sufficiently small final segment of $b$."
Definition (Def. 5.2, pp. 563–564, l. 316–322): "We define the **ordinal-value** (or **value**) $v_J \colon K((\mathbf{G}^{\leq 0})) \to OR$ as follows. 1. $v_J(b) = 0$ iff $b \in J$. 2. $v_J(b) = 1$ iff $b$ is congruent to a non-zero element of $K$ modulo $J$. 3. $v_J(b) = \min\{ot(c) \mid c \equiv b \bmod J + K\}$ in the remaining cases."
- Spelling variants and counts: "ordinal-value" (hyphenated) 21 + "ordinal-values" 2; "ordinal value" (open) 13; bare "value" when $v_J$ is meant: "of value $> 1$" (l. 383), "have value 1" (l. 586), "terms of value $<$ …" (Lemma 7.7, 8.2, 10.4), "terms of small value" (§2, 6 occurrences), "big ordinal-value" (l. 208). Hyphenated form dominates in §1–2, §5, §9 and in section titles ("5. The ordinal-value of a generalized power series", "6. Principal and residual ordinal-values"); open form dominates in §6 and §13. Both are the paper's.
- Other descriptions of the same map: "the ordinal value map $v_J$" (l. 691), "the ordinal-value map $v_J \colon K((\mathbf{G}^{\leq 0})) \to (OR, \odot)$" (l. 692), "a new kind of valuation taking ordinal numbers as values" (title of §1.6; abstract l. 13: "a new kind of valuation taking ordinal numbers as values"), "the valuation $v_J$" (l. 166), "the valuation-theoretic approach developed in this paper" (l. 706), "the existence of a suitable valuation" (l. 138).
- Convention: the subscript $J$ is always present ($v_J$, 371 occurrences of `v_J`); the bare $v$ is reserved for the natural valuation (A6).
- Convention: $v_J$ is *defined* modulo $J + K$ (not modulo $J$) in clause 3; the paper explains why: "Note that we consider the open interval $(-\varepsilon, 0)$ rather than the half-open one $(-\varepsilon, 0]$ which would seem more natural. This ensures the validity of the following remark and corresponds to the fact that in clause 3 we work modulo $J + K$ rather than modulo $J$." (l. 324).
- The quotient map: "we can pass to the quotient and obtain a map $$v_J \colon K((\mathbf{G}^{\leq 0}))/J \to OR$$" (l. 156), same symbol.
- Three listed properties (l. 148–152): "1. $v_J(b) = 0$ iff $b \in J$, 2. $v_J(b + c) \leq \max\{v_J(b), v_J(c)\}$, 3. $v_J(bc) = v_J(b) \odot v_J(c)$ (**multiplicative property**)."

**A32. "stable interval"; the geometrical definition.**
(Def. 5.2 continuation, l. 324): "A more geometrical definition of $v_J$ can be obtained as follows. For $\varepsilon \in \mathbf{G}^{>0}$ let $(-\varepsilon, 0)$ be the interval $\{x \in \mathbf{G} \mid -\varepsilon < x < 0\}$ and let $B_{\varepsilon}$ be the intersection of the support $S_b$ of $b$ with $(-\varepsilon, 0)$. If there is some $\varepsilon$ with $B_{\varepsilon} = \emptyset$, then $v_J(b)$ is 1 or 0 depending on whether 0 is in the support of $b$ or not. If instead for every $\varepsilon$ the set $B_{\varepsilon}$ is non-empty, then there must be some $\varepsilon$ such that for every smaller $\varepsilon'$ the sets $B_{\varepsilon}$ and $B_{\varepsilon'}$ have the same order type. We then say that $B_{\varepsilon}$ is a **stable interval** for $b$. The order type of any stable interval is the ordinal-value of $b$, and it coincides with the principal part of the Cantor normal form of $ot(b)$ provided $ot(b)$ is a limit ordinal and the supremum of $S_b$ is 0." 3 occurrences; used in proof of Lemma 6.8 ("let $(-\varepsilon, 0) \cap S_b$ be a stable interval for $b$", l. 401).

**A33. Remark 5.3 / Remark 5.4.**
(l. 326): "The map $v_J \colon K((\mathbf{G}^{\leq 0})) \to OR$ has image contained in $\mathbf{H}$."
(l. 328–332): "Given $b, c \in K((\mathbf{G}))$, the support of $b + c$ is included in the union $S_b \cup S_c$ of the respective supports, and the support of $bc$ is contained in $S_b + S_c$. By Lemma 4.1 and Lemma 4.4 we obtain: 1. $ot(b + c) \leq ot(b) \oplus ot(c)$, 2. $ot(bc) \leq ot(b) \odot ot(c)$." [Citation "Lemma 4.4" should be 4.5 — see oddities list.]

**A34. Submultiplicative property; multiplicative property.**
(Lemma 5.5, l. 336–338): "1. $v_J(b + c) \leq \max\{v_J(b), v_J(c)\}$, *with equality holding if* $v_J(b) \neq v_J(c)$. 2. $v_J(bc) \leq v_J(b) \odot v_J(c)$ (***submultiplicative property***)."
(§2, l. 168): "It is easy to show that $v_J$ is **submultiplicative**: $v_J(bc) \leq v_J(b) \odot v_J(c)$. This corresponds to the fact that the order type of a product $bc$ is less than or equal to the natural product of the order types of $b$ and $c$."
(Thm. 9.7, p. 571, l. 588): "*For $b, c \in K((\mathbf{R}^{\leq 0}))$, $v_J(bc) = v_J(b) \odot v_J(c)$.*"
- "multiplicative property" 19 occurrences; "submultiplicative" 8. The paper says (l. 152): "The proof of the multiplicative property is the most difficult result of this paper, and the irreducibility results can be derived from it. It implies in particular that the ideal $J$ is prime." Section 2 is titled "Outline of the proof of the multiplicative property of the ordinal-value".
- Phrasing when invoked: "By the submultiplicative property it suffices to show that…" (l. 480); "By the submultiplicative property, we can now divide by $c$ and conclude that…" (l. 539); "The opposite inequality also holds (by the submultiplicative property), and we are done." (l. 549); "By Theorem 9.7, by the choice of $x, y$ and by Lemma 7.5 we have…" (l. 614).
- Phrase for multi-factor version (l. 170): "It is actually more convenient to prove the multiplicative property for several factors".

**A35. Non-archimedean absolute value; $w_J$; Krull valuation.**
(l. 160): "Thus $v_J$ is an **non-archimedean absolute value** on $K((\mathbf{R}^{\leq 0}))/J$ except for the fact that usually absolute values are defined on fields, and $K((\mathbf{R}^{\leq 0}))/J$ is only a domain." [sic "an"]. Extension: "So if we define $v_J(b/c) = v_J(b)/v_J(c)$ we obtain an absolute value into the surreal numbers."
(Remark 1.1, l. 162): "Using the fact that $v_J$ has image contained in $\{\omega^{\alpha} \mid \alpha\} \cup \{0\}$, we can define a new map $w_J \colon K((\mathbf{R}^{\leq 0}))/J \to OR \cup \{-\infty\}$ which behaves like a polynomial degree: $\omega^{w_J(b)} = v_J(b)$ (with $w_J(b) = -\infty$ if $v_J(b) = 0$). We have $w_J(bc) = w_J(b) \oplus w_J(c)$ and $w_J(b + c) \leq \max\{w_J(b), w_J(c)\}$. We can obtain a Krull valuation [Endler 72] by reversing the order." $w_J$ appears only in this remark.
(Remark 1.2, l. 164–168): "$K((\mathbf{R}^{\leq 0}))/J$ is *not* a valuation ring: there is a non-zero element $x$ of its fraction field such that neither $x$ nor $x^{-1}$ belongs to $K((\mathbf{R}^{\leq 0}))/J$, for instance $x = (b+J)/(c+J)$ where $b := \sum_n t^{-1/n}$ and $c := \sum_n t^{-1/n^2}$."

**A36. Corollary 9.8, Corollary 9.9 (named consequences).**
(Cor. 9.8, p. 572, l. 594): "*$J$ is a prime ideal of $K((\mathbf{R}^{\leq 0}))$.*"
(Cor. 9.9, l. 598): "*Let $b, c \in K((\mathbf{R}^{\leq 0}))$. Then $ot(bc) = ot(b) \odot ot(c)$ provided there are ordinals $\beta$ and $\xi$ with $ot(b) = \omega^{\beta}$ and $ot(c) = \omega^{\xi}$.*" Also quoted in §1.6 (l. 126) with the same wording.
- Prose gloss (l. 124): "the order type of the product is "roughly" the product of the order types".
- (l. 130): "The fact that the theorem holds only for order types of the form $\omega^{\alpha}$ is not very restrictive, due to the fact that every ordinal has a final segment of type $\omega^{\alpha}$".
- The word "cancellations" (l. 132–134): "there cannot be "cancellations" in the product"; "we need to prove that there are "few cancellations" in the product of two elements of $K((\mathbf{G}^{\leq 0}))$ (this is false in the field $K((\mathbf{G}))$: take $c = b^{-1}$)."

### A.VI Truncations, germs at a point, principal/residual values (§6)

**A37. $b_{|\gamma}$ — "truncation of $b$ at $\gamma$"; $b^{|\gamma}$ — "germ of $b$ at $\gamma$".**
(Def. 6.1, p. 565, l. 352–358): "Given $b = \sum_{\beta} b_{\beta} t^{\beta} \in K((\mathbf{G}))$ and $\gamma \in \mathbf{G}$, we define: 1. $b_{|\gamma} = \sum_{\beta \leq \gamma} b_{\beta} t^{\beta}$. 2. $b^{|\gamma} = t^{-\gamma} b_{|\gamma}$. We call $b_{|\gamma}$ the **truncation of $b$ at $\gamma$** and we call the equivalence class of $b^{|\gamma}$ modulo $J$ the **germ of $b$ at $\gamma$**."
(l. 360): "The supports of $b_{|\gamma}$ and $b^{|\gamma}$ differ only by a translation. The supremum of the support of $b_{|\gamma}$ is $\leq \gamma$. The supremum of the support of $b^{|\gamma}$ is $\leq 0$. So in particular $b^{|\gamma} \in K((\mathbf{G}^{\leq 0}))$."
- Informal introduction (§2, l. 184): "we will define (Definition 6.1) a new series $b^{|\gamma} \in K((\mathbf{G}^{\leq 0}))$ in such a way that $b^{|\gamma} \equiv c^{|\gamma} \bmod J$ iff $b, c$ coincide near $\gamma$ (in the sense that if $\delta$ is sufficiently close to $\gamma$ then the coefficients of $t^{\delta}$ in $b, c$ coincide). The series $b^{|\gamma}$ is obtained by truncating $b$ at $\gamma$ and multiplying the resulting series by the normalization factor $t^{-\gamma}$. We call $b^{|\gamma} + J$ the **germ at** $\gamma$ of $b$."
- Convention: the truncation is **non-strict** ($\beta \leq \gamma$), includes the term at $\gamma$. Contrast with the truncations used in "truncation closed" (A19), which are strict $\beta < \alpha$.
- Convention: subscript bar for truncation ($b_{|\gamma}$), superscript bar for the normalised truncation ($b^{|\gamma}$). Rendering of the bar `|` before $\gamma$ is the transcriber's LaTeX; unverifiable whether printed as $b_{\restriction\gamma}$, $b_{|\gamma}$ or similar. The paper is loose about "germ": strictly the germ is the class mod $J$, but $b^{|\gamma}$ itself is often treated as "the germ" ("these germs at $\gamma$ behave like generalized coefficients", l. 184).
- Also "$a^{|\alpha}$" (Rem. 7.6) and "$b^{|x}$" with a real variable $x$ (§10). Note the paper extends the definition to $b \in K((\mathbf{G}))$ (not just $K((\mathbf{G}^{\leq 0}))$).
- "truncation"/"truncating" 6 occurrences total.

**A38. Remarks 6.2, 6.3.**
(l. 362): "$b^{|\gamma} \equiv c^{|\gamma} \bmod J$ iff for every $\delta$ sufficiently close to $\gamma$ the coefficients of $t^{\delta}$ in $b$ and $c$ coincide."
(l. 364): "$b^{|\gamma} \notin J$ if and only if $\gamma$ is in the topological closure of the support of $b$ with respect to the order topology of $\mathbf{G}$. So in particular $b^{|\gamma} \notin J$ only for $\gamma$ ranging through a well ordered set."

**A39. $v_J^p(b)$ — "principal value"; $v_J^r(b)$ — "residual value".**
(Def. 6.4, pp. 565–566, l. 369–377): "Given $b \in K((\mathbf{G}^{\leq 0}))$ with $v_J(b) > 1$, we know that $v_J(b)$ has the form $\omega^{\beta}$ for some ordinal $\beta > 0$. From the Cantor normal form of $\beta$ it follows that $v_J(b)$ can be written uniquely as a product $\rho_1 \rho_2 \ldots \rho_n$, where $\rho_1 \geq \rho_2 \geq \ldots \geq \rho_n > 1$ are multiplicative principal ordinals. We define: 1. $v_J^p(b) = \rho_n$ = the **principal value** of $b$, 2. $v_J^r(b) = \rho_1 \rho_2 \ldots \rho_{n-1}$ = the **residual value** of $b$, with the convention that the residual value is 1 if $v_J(b) \in \mathbf{MP}$ (i.e. if $n = 1$)."
(l. 379): "So if $v_J(b) = \omega^3$, then $v_J^p(b) = \omega$ and $v_J^r(b) = \omega^2$."
(Remark 6.5, l. 381): "The product $\rho_1 \rho_2 \ldots \rho_n$ coincides with the natural product $\rho_1 \odot \rho_2 \odot \ldots \odot \rho_n$. More generally if $\rho \in \mathbf{MP}, \alpha \in \mathbf{H}$ and $\rho \geq \alpha$, then $\rho\alpha = \rho \odot \alpha$."
(eq. (4), l. 383–387): "For every $b \in K((\mathbf{G}^{\leq 0}))$ of value $> 1$ we have the decomposition: $$v_J(b) = v_J^r(b) v_J^p(b) \tag{4}$$ with $v_J^r(b) \in \mathbf{H}$ and $v_J^p(b) \in \mathbf{MP}$."
- Convention: the principal value is the *smallest* multiplicative-principal factor ($\rho_n$), placed on the right in the ordinal product; parallels "principal part" = smallest CNF term (A23).
- Counts: "principal value" 7 (also in quotes as "principal value" in §2, l. 206, 216: "we can assume that $b$ has "**principal value**" (Definition 6.4) smaller than or equal to that of $c$"); "residual value" 2. Section title: "6. Principal and residual ordinal-values".
- Phrasing: "$b$ was assumed to have "smaller or equal principal value"" (l. 216); "of minimal principal value" (Def. 9.3).
- Motivating prose (l. 367): "the idea is that any series can be thought of as a series of multiplicative principal ordinal value, provided we allow the coefficients themselves to be series. For instance, a series of ordinal value $\omega^3$ (which is not multiplicative principal) can be also understood as a series of ordinal value $\omega$ (which is multiplicative principal) whose coefficients are series of ordinal value $\omega^2$."

**A40. $X(b)$; "hyper-series".**
(Def. 6.6, p. 566, l. 389–391): "Given $b \in K((\mathbf{G}^{\leq 0}))$ with $v_J(b) > 1$, define $$X(b) = \{\gamma < 0 \mid v_J(b^{|\gamma}) = v_J^r(b)\}.$$"
(l. 393): "Informally we think of $b$ as a "hyper-series" of ordinal value $v_J^p(b)$ whose coefficients are series of ordinal value $v_J^r(b)$. The support of this hyper-series is $X(b)$. It may be challenging to find the correct algebraic framework for these hyper-series."
(l. 395): "Note that if $v_J(b)$ is multiplicative principal, then $X(b)$ is the set of all $\gamma < 0$ with $v_J(b^{|\gamma}) = 1$, namely the set of all isolated points of the support of $b$."
(Remark 6.7, l. 397): "If $\gamma \in X(b)$, then either $v_J(b^{|\gamma}) = 1$ or $v_J^p(b^{|\gamma}) = \rho_{n-1} \geq v_J^p(b)$."
- $X(b)$: 19 occurrences; never named in words other than "a set $X(b)$ depending on $b$" (l. 194). "hyper-series" 3 (always in quotes at first use).
- Standard hypothesis phrase: "for every $\gamma \in X(b)$ sufficiently close to zero" (Lemma 6.9, 8.2, 9.5).

**A41. Lemmas 6.8, 6.9 (where $\mathbf{G} = \mathbf{R}$ is first used).**
(l. 399): "For the following result we specialize to the case $\mathbf{G} = (\mathbf{R}, +, 0, \leq)$."
(Lemma 6.8, l. 400): "*Let $b \in K((\mathbf{R}^{\leq 0}))$. If $v_J(b) > 1$, then every sufficiently small non-empty final segment of $X(b)$ has order type equal to $v_J^p(b)$ and supremum $= 0$.*" Proof invokes "Using the completeness of $\mathbf{R}$" (l. 403).
(Lemma 6.9, l. 409): "*Let $b, c \in K((\mathbf{R}^{\leq 0}))$. If $\rho \in \mathbf{H}$ and $v_J(c^{|\gamma}) \geq \rho$ for every $\gamma \in X(b)$ sufficiently close to zero, then $v_J(c) \geq \rho v_J^p(b)$.*"

### A.VII Convolution formula (§7)

**A42. Convolution formula; the lines $L_\gamma$; Iverson bracket $[\phi]$.**
(§2, l. 184–188): "we will prove (Lemma 7.5) the following **convolution formula** which shows that these germs at $\gamma$ behave like generalized coefficients: $$(bc)^{|\gamma} \equiv \sum_{\beta + \xi = \gamma} b^{|\beta} c^{|\xi} \bmod J \tag{1}$$ Equation (1) holds for more general groups $\mathbf{G}$, but we will not need this fact."
(Lemma 7.5, p. 568, l. 443–447): "*Let $b, c \in K((\mathbf{R}^{\leq 0}))$ and $\gamma \in \mathbf{R}^{\leq 0}$.* 1. *There are only finitely many pairs $(\beta, \xi) \in \mathbf{R}^{\leq 0} \times \mathbf{R}^{\leq 0}$ with $\beta + \xi = \gamma$ and $b^{|\beta} c^{|\xi} \not\equiv 0 \bmod J$.* 2. $(bc)^{|\gamma} \equiv \sum_{\beta + \xi = \gamma} b^{|\beta} c^{|\xi} \bmod J$ *(**convolution formula**).*"
- Section title "7. Convolution product"; "convolution formula" 5; "convolution product" 2 (once for the ordinary multiplication of series, l. 23, once as section title).
- (l. 423): "the intersection of the straight line $L_{\gamma} = \{(x, y) \mid x + y = \gamma\}$ with the set of points $B \times C \subseteq \mathbf{R}^2$ is finite."
- (l. 453): "Let $[\phi] = 0$ if $\phi = $ **false**, $[\phi] = 1$ if $\phi = $ **true**." (Iverson bracket, not so named.)
- Lemma 7.1 (l. 419): "*If $B, C$ are well ordered subsets of $\mathbf{R}$, then $\overline{B + C} = \overline{B} + \overline{C}$.*" Remarks 7.2/7.3 (l. 427–429): "The lemma does not hold without the assumption that $B, C$ are well ordered." / "The lemma fails if $\mathbf{R}$ is replaced by the rationals $\mathbf{Q}$."
- Remark 7.6 (l. 474): "By induction one can extend the lemma to more than two factors. For instance, $(abc)^{|\gamma} \equiv \sum_{\alpha, \beta, \xi} [\alpha + \beta + \xi = \gamma] a^{|\alpha} b^{|\beta} c^{|\xi} \bmod J$"

**A43. "terms of value $<$ …" / "terms of small value"; Lemma 7.7 (the derivation-like formula).**
(Lemma 7.7, l. 476–478): "*Let $b, c \in K((\mathbf{R}^{\leq 0}))$ be such that $v_J^p(b) \leq v_J^p(c)$. Let $\equiv$ be the congruence relation modulo $J$. Then for $\gamma \in \mathbf{R}^{<0}$ sufficiently close to zero:* $$(bc)^{|\gamma} \equiv b^{|\gamma} c + b c^{|\gamma} + \text{ terms of value } < v_J^r(b) \odot v_J(c)$$"
- §2 gloss (l. 190–194): "$$(bc)^{|\gamma} \equiv b^{|\gamma} c + b c^{|\gamma} + \text{terms of small value} \tag{2}$$ where "small" means smaller than the "expected" ordinal-value of $b^{|\gamma} c$, namely $v_J(b^{|\gamma}) \odot v_J(c)$. Of course until we have proved the multiplicative property of $v_J$ we do not know whether the *expected* ordinal-value coincides with the *actual* ordinal-value. Equation (2) says that in some sense $b \mapsto b^{|\gamma}$ behaves like a derivation."
- Convention: "$+ \text{ terms of value } < \alpha$" is the paper's idiom for an error term of ordinal-value below $\alpha$ modulo $J$; "expected ordinal-value" = natural product of the values of the factors.

### A.VIII Main lemma and induction (§8–9)

**A44. Lemma 8.2 ("The main lemma"); "the crucial idea".**
(Lemma 8.2, l. 488–492): "*Let $b, c \in K((\mathbf{R}^{\leq 0}))$ be such that $v_J^p(b) \leq v_J^p(c)$ and let $k > 0$. Suppose that for every $\gamma \in X(b)$ sufficiently close to zero we have* $$v_J(b^{|\gamma} b^{k-1} c^2) = \overset{k-1}{\bigodot} v_J(b) \odot v_J(b^{|\gamma}) \odot v_J(c) \odot v_J(c)$$ *Then:* $$v_J(b^k c) = \overset{k}{\bigodot} v_J(b) \odot v_J(c)$$"
- Section title: "8. The main lemma". (l. 498): "The crucial idea is to multiply the above equation by $c$"; §2 (l. 206): "The crucial idea of the whole proof is to multiply both sides of equation (2) by $c$".

**A45. Formal expression; selected factor; selected exponent; relevant factor; complexity.**
(Def. 9.1, p. 570, l. 550): "A **formal expression** is an element of the free commutative monoid generated by $\{x \in K((\mathbf{R}^{\leq 0})) \mid v_J(x) > 1\}$."
(Def. 9.3, l. 554–558): "Let $\prec$ be a fixed well ordering on $K((\mathbf{R}^{\leq 0}))$ (actually a linear ordering suffices). Given a formal expression $w = b_0^{k_0} \cdot \ldots \cdot b_n^{k_n}$ with all the $b_j$'s distinct, let $Y$ be the set of all the elements of $\{b_0, \ldots, b_n\}$ of minimal principal value and let $Z \subseteq Y$ be the set of all the elements of $Y$ of maximal ordinal-value. If $b_i$ is the $\prec$-least element of $Z$, then $b_i$ will be called the **selected factor** of $w$ and the integer $k_i$ will be called the **selected exponent**. We then say that $b_j$ ($j \in \{0, \ldots, n\}$) is a **relevant factor** if its ordinal-value is bigger than or equal to the ordinal-value of the selected factor. The **complexity** of the formal expression $w$ is defined as the ordinal $$\omega[\alpha_0, \ldots, \alpha_m] + k$$ where $k$ is the selected exponent and $\alpha_0, \ldots, \alpha_m$ ($m \leq n$) is the sequence of the ordinal-values of the relevant factors."
(l. 562): "Any formal expression can be reduced to a formal expression in which the $b_j$'s are distinct by replacing $b^{k_1} b^{k_2}$ with $b^{k_1 + k_2}$. The definition of complexity thus extends to all the formal expressions."
- Counts: "formal expression" 10, "complexity" 16, "selected factor" 7, "selected exponent" 2, "relevant factor" 3.
- Convention: formal products written $b_0^{k_0} \cdot \ldots \cdot b_n^{k_n}$ with explicit dots; "we may consider the product … either as an element of $K((\mathbf{R}^{\leq 0}))$ or as a formal expression" (l. 550).
- Lemma 9.6 (l. 580): "*Given elements $b_0, \ldots, b_n \in K((\mathbf{R}^{\leq 0}))$, we have:* $$v_J(b_0^{k_0} \cdot \ldots \cdot b_n^{k_n}) = \overset{k_0}{\bigodot} v_J(b_0) \odot \ldots \odot \overset{k_n}{\bigodot} v_J(b_n).$$"

### A.IX Irreducibility (§10–12)

**A46. Critical point.**
(Lemma 10.1, p. 572, l. 604): "*Given $0 \neq b \in K((\mathbf{R}^{\leq 0}))$, the set of ordinals $\{v_J(b^{|x}) \mid x \in \mathbf{R}^{\leq 0}\}$ has a maximum.*"
(Def. 10.2, l. 608): "Given $0 \neq b \in K((\mathbf{R}^{\leq 0}))$, let $\alpha = \max\{v_J(b^{|x}) \mid x \in \mathbf{R}^{\leq 0}\}$. We say that $x \in \mathbf{R}^{\leq 0}$ is the **critical point** of $b$ if $x$ is the smallest real number such that $v_J(b^{|x}) = \alpha$. This is well defined by the previous lemma and the fact that $\{y \mid v_J(b^{|y}) \neq 0\}$ is well ordered (is included in the closure of the support of $b$)."
(Remark 10.3, l. 610): "If $x$ is the critical point of $b$, $v_J(b^{|x}) \geq v_J(b)$."
(Lemma 10.4, l. 612): "*Let $b, c$ be non-zero elements of $K((\mathbf{R}^{\leq 0}))$ with critical points $x, y$ respectively. Then $v_J((bc)^{|x+y}) = v_J(b^{|x}) \odot v_J(c^{|y})$.*"
- 5 occurrences; phrasing "with critical points $x, y$ respectively", "Let $x, y \in \mathbf{R}^{\leq 0}$ be the critical points of $b, c$ respectively" (l. 618).

**A47. Theorem 10.5 — the irreducibility criterion.**
(l. 616): "*Suppose that $a \in K((\mathbf{R}^{\leq 0}))$ is not divisible by any monomial $t^{\gamma}$ with $\gamma < 0$. If the order type of the support of $a$ is either $\omega$ or of the form $\omega^{\omega^{\beta}}$, then both $a$ and $a + 1$ are irreducible in $K((\mathbf{R}^{\leq 0}))$.*"
- Referred to as "the following criterion for irreducibility which depends only on the order type of the support" (l. 96), "our criterion for irreducibility" (l. 694), "the following test for irreducibility based only on the order type of the support of the series" (abstract).
- (l. 622): "As already remarked in the introduction, $\mathbf{R}$ can be replaced by $\mathbf{G}$ provided $\mathbf{G}$ is archimedean (since then $\mathbf{G}$ embeds in $\mathbf{R}$)."
- Proof's key step phrasing (l. 618): "Since $v_J(a) \in \mathbf{MP}$, either $v_J(b)$ or $v_J(c)$ must be 1."; "the support of $b$ contains 0 as an isolated point."

**A48. Theorem 11.2.**
(l. 628): "*Let $a$ be an irreducible element of $K[\mathbf{R}^{\leq 0}]$. Then $a$ is irreducible in $K((\mathbf{R}^{\leq 0}))$.*" (l. 632): "By Biljacović's work this implies that $t^{-\sqrt{2}} + t^{-1} + 1$ is irreducible in $K((\mathbf{R}^{\leq 0}))$, as well as any other series with finite support whose exponents are not linearly dependent over $\mathbf{Q}$." (l. 104: "We have not checked whether the above theorem holds for a general $\mathbf{G}$ instead of $\mathbf{R}$.")

**A49. Theorem 12.1 and its apparatus: $Q$, $Fin$, $\mu$, $H$, $F = K((\mu))$, $M(\xi)$.**
(Thm. 12.1, p. 573, l. 642–646): "1. *The series $\sum_n t^{-1/n} + 1$ is irreducible in $K((\mathbf{G}^{\leq 0}))$.* 2. *More generally, let $Q$ be an archimedean subgroup of $\mathbf{G}$ and suppose that $a \in K((Q^{<0})) \subset K((\mathbf{G}^{\leq 0}))$ has support of order type $\omega$ or $\omega^{\omega^{\alpha}}$ ($\alpha$ an ordinal) and $a$ is not divisible by any monomial $t^{\gamma}$ with $\gamma \in Q^{<0}$. Then $a + 1$ is irreducible in $K((\mathbf{G}^{\leq 0}))$.*"
- (l. 650): "Fix a positive element of $Q$ and call it 1. Let $Fin \subseteq \mathbf{G}$ be the intersection of all convex subgroups of $\mathbf{G}$ containing 1 (hence containing $Q$)."
- (l. 654): "Let $\mu \subseteq Fin$ be the union of all the convex subgroups of $\mathbf{G}$ not containing 1 (hence $Q \cap \mu = \{0\}$). Then $Q$ is contained in the set-theoretic difference $Fin \setminus \mu$. The quotient $Fin/\mu$ is archimedean, because it contains no non-trivial convex subgroups. Since $\mu$ is convex $Fin/\mu$ has a natural induced order. In a divisible abelian group every subgroup is a direct factor. Thus we have: $$Fin = H \oplus \mu$$ where $H \simeq Fin/\mu$ is archimedean and it can be chosen so that $Q \subseteq H$ because $Q \cap \mu = \{0\}$ and $\mathbf{G}$ is divisible. (See [Baer 40] or [Fuchs 70, vol. 1, Theorem 21.2].) The ordering on $H \oplus \mu$ (induced by $\mathbf{G}$) is lexicographic: $h + m < h' + m'$ if and only if either $h < h'$ or $h = h'$ and $m < m'$ in $\mu$."
- (l. 660–668): "$$Fin^{\leq 0} = (H^{<0} \oplus \mu) \cup \mu^{\leq 0}$$ This induces a canonical identification $$K((Fin^{\leq 0})) = K((\mu))((H^{<0})) \oplus K((\mu^{\leq 0})) \subset K((\mu))((H^{\leq 0}))$$ Indeed, a series $\sum_{\beta} b_{\beta} t^{\beta} \in K((Fin^{\leq 0}))$ can be also thought of as a series $\sum_{\xi \in H} c_{\xi} t^{\xi}$ where $c_{\xi} \in K((\mu))$ is given by $\sum_{\beta \in M(\xi)} b_{\beta} t^{\beta - \xi}$ with $M(\xi) := \{\beta \mid \beta - \xi \in \mu\}$."
- (l. 670): "Since $\mu$ is a subgroup of $\mathbf{G}$, $F := K((\mu))$ is a field and we have $$K((Q^{\leq 0})) \subseteq F((H^{\leq 0}))$$"
- Convention: $Fin$ and $\mu$ are written as multi-letter italic identifiers (not $\mathrm{Fin}$ in the transcription); $Fin$ for the convex hull of $Q$ ("finite" elements relative to 1), $\mu$ for the "infinitesimal" convex subgroup. Iterated series field written $K((\mu))((H^{\leq 0}))$ — nested double parentheses.
- (Remark 12.2, l. 684): "In the above theorem $\mathbf{G}$ can be allowed to be a proper class. So Conway's series $\sum_n t^{-1/n} + 1$ is irreducible even in the ring of omnific integers."

**A50. Conway's series; Gonshor's series.**
(l. 68–72): "[Conway 76] contains the following candidate for an irreducible element of $\mathbf{R}((\mathbf{G}^{\leq 0}))$ … $$\sum_n t^{-1/n} + 1$$ where $n$ ranges over the positive integers. (Conway did not have the minus sign in the exponents because of the change of variables $x = t^{-1}$, but then one has to consider anti-well-ordered supports.)"
(l. 74–76): "Gonshor's book contains the following quite different candidate for an irreducible series: $$t^{-\sqrt{2}} + t^{-1} + 1$$ which was also considered in Conway's lectures."
- Referred to as "Conway's series" (l. 102, 106, 684: "So Conway's series is irreducible even in the ring of omnific integers"). Convention: **negative exponents**, variable $t$, and the explicit "+1" ("in the non-archimedean case we do need to add 1, as otherwise the series is divisible by a monomial", l. 102).

**A51. Archimedean class.**
(l. 640, attributed to Gonshor): "the elements of its support—excluding zero—must belong to the same **archimedean class**, i.e. given two non-zero elements of the support, say $\beta$ and $\xi$, there is a natural number $n$ with $n|\beta| > |\xi|$ and $n|\xi| > |\beta|$." Also (l. 42): "$\mathbf{G}$ is the group of archimedean classes of $F$". "archimedean" 19 occurrences (always lower-case "archimedean", "non-archimedean"). Phrasing: "Let $Q$ be an archimedean subgroup of $\mathbf{G}$"; "If $\mathbf{G}$ is archimedean, then it can be embedded in $\mathbf{R}$" (l. 98).

### A.X Conventions collected

**A52. Hypotheses on $K$ and $\mathbf{G}$.**
- (l. 90): "We prove that if $K$ is a field of characteristic zero (not even assumed to be orderable, e.g. the complex numbers) and $\mathbf{G}$ is an ordered abelian divisible group, then: $K((\mathbf{G}^{\leq 0}))$ *does have irreducible elements.*" (l. 94): "So it is important to work with a general $K$ and not only with $K = \mathbf{R}$."
- (l. 140): "As usual let $\mathbf{G}$ be an ordered divisible abelian group."
- (l. 638): "$K$ is any field of characteristic zero (not assumed to be orderable) and $\mathbf{G} = (\mathbf{G}, +, 0, \leq)$ is any abelian divisible ordered group".
- Word order for the group varies freely: "ordered abelian divisible group" (3), "divisible ordered abelian group" (1), "abelian divisible ordered group" (1), "ordered divisible abelian group" (1), "ordered abelian group" (3), "abelian ordered group" (1). No form dominates decisively; "ordered abelian divisible group" is the abstract's and §1.5's.
- Divisibility is used via "(hence a $\mathbf{Q}$-vector space)" (l. 48) and "by divisibility of $\mathbf{G}$" (l. 64); "In a divisible abelian group every subgroup is a direct factor." (l. 654).
- Characteristic zero is needed (implicitly) because the coefficient $k$ appears in $k b^{k-1} b^{|\gamma} c$ in Lemma 8.2; the paper does not say where it is used.

**A53. "Specialize to the case $\mathbf{G} = \mathbf{R}$."**
The move to the reals is announced each time: "For the following result we specialize to the case $\mathbf{G} = (\mathbf{R}, +, 0, \leq)$." (l. 399); "For simplicity, in this section we specialize to the case $\mathbf{G} = (\mathbf{R}, +, 0, \leq)$, although the arguments go through under more general hypothesis." (l. 417); "(later we specialize to $\mathbf{G} = \mathbf{R}$)" (l. 184); "to prove that it has good algebraic properties we specialize to the case $\mathbf{G} = \mathbf{R}$" (l. 148). Final accounting (l. 692): "In our proofs the assumption $\mathbf{G} = \mathbf{R}$ was only used in two places: in the results of section 7—namely the proof of the "convolution formula"—and in Lemma 6.8."

**A54. "sufficiently close to zero" / "sufficiently small".**
The paper's standard quantifier for "for all $\gamma$ in some final segment of $(-\infty,0)$": "for every $\gamma \leq 0$ sufficiently close to zero" (l. 314); "for $\gamma \in \mathbf{R}^{<0}$ sufficiently close to zero" (l. 476); "every sufficiently small non-empty final segment" (l. 400); "every sufficiently small final segment of a non-zero ordinal" (l. 240); "if $\gamma$ is sufficiently small" (l. 216, 508). Counts: "sufficiently close to zero" 10, "sufficiently close to 0" 1, "sufficiently small" 6. Also "$\delta \leq \gamma$ sufficiently close to $\gamma$" (Lemma 7.4).

**A55. Proper-class $\mathbf{G}$.**
(l. 106): "We can allow $\mathbf{G}$ to be a proper class, but restricting to series whose support is a set." (l. 68): "Conway's group $\mathbf{G}$ is a proper class because he works inside the huge ring of "**omnific integers**", which is an integer part of the real closed field of "**surreal numbers**"".

**A56. Numbering and labelling conventions of the text.**
Results are labelled Definition / Lemma / Theorem / Corollary / Remark / Fact, numbered by section (Def. 5.2, Lemma 7.5, …). "Fact" is reserved for results quoted from the literature without proof (Facts 3.2, 3.3, 3.7, 3.8). Equations are numbered (1)–(6). Proofs end with $\square$. Statement text is italicised. Displayed key theorems in the introduction are set as block quotes prefixed by "(Theorem 10.5)", etc.

---

## Part B. What the paper reuses (attributed terms, symbols, results)

Each entry: what is taken, from whom (the paper's own citation key), the attributing sentence verbatim, and whether it is used unchanged, renamed, re-symbolled, or generalised.

**B1. Generalized power series / Hahn fields — [Hahn 07, MacLane 39, Kaplansky 42, Fuchs 63, Ribenboim 68, Ribenboim 92].**
(l. 17): "Generalized power series with exponents in an arbitrary abelian ordered group are a classical tool in the study of valued fields and ordered fields [Hahn 07, MacLane 39, Kaplansky 42, Fuchs 63, Ribenboim 68, Ribenboim 92]." The paper never uses the phrase "Hahn field" or "Hahn series"; the object is always "generalized power series" (12 occurrences of the full phrase; "power series" 20; "series" 78). Unchanged from the literature as a notion; the paper supplies its own statement of the definition (A1).
(l. 32): "It can be shown that every non-zero series has an inverse and therefore $K((\mathbf{G}))$ is a field [Hahn 07] (see [Neumann 49] for the case of division rings)."

**B2. Real closedness of $K((\mathbf{G}))$ — "classical result", no citation.**
(l. 42): "It is a classical result that if $K$ is real closed and $\mathbf{G}$ is divisible then $K((\mathbf{G}))$ is also real closed."

**B3. Power series representation of ordered fields — [Gleyzal 37], [Krull 32], [Kaplansky 42].**
(l. 42): "Moreover any ordered field, hence any real closed field $F$, admits a power series representation with real coefficients [Gleyzal 37]. More precisely, $F$ can be embedded as an ordered field in $\mathbf{R}((\mathbf{G}))$, where $\mathbf{R}$ is the ordered field of real numbers and $\mathbf{G}$ is the group of archimedean classes of $F$. Indeed, [Krull 32] shows that $F$ possesses a "maximal" extension, and [Kaplansky 42, Theorem 6, Theorem 8] proves that the maximal extension is necessarily a power series field."

**B4. Integer part — [Mourgues-Ressayre 93], [Boughattas 93], [Ressayre 93, 95], [Shepherdson 64].**
(l. 44): "Using generalized power series, [Mourgues-Ressayre 93] proved that every real closed field $F$ has an integer part. [Boughattas 93] showed that real closeness is necessary." (l. 46): "Integer parts of real closed fields happen to coincide with the models of the axiom system known as **open induction** [Shepherdson 64]". The term "integer part" is used unchanged (the paper gives the definition, A17). "Truncation closed" is attributed by context to "the work of Ressayre and his collaborators" (l. 60). "exponential integer part (in the sense of Ressayre)" (l. 694).

**B5. Open induction and its literature — [Wilkie 78, Dries 80-1, Dries 80-2, Otero 90, Otero 93-1], [Macintyre-Marker 89, Berarducci - Otero 96, Moniri 94, Biljacovic 96], [Otero 93-2].**
(l. 46): "a lot of work has been done to study the properties of these discrete rings, focusing in particular on the solution of diophantine equations (see [Wilkie 78, Dries 80-1, Dries 80-2, Otero 90, Otero 93-1]) and on the behavior of primes [Macintyre-Marker 89, Berarducci - Otero 96, Moniri 94, Biljacovic 96]. Generalized power series were exploited in [Otero 93-2] to prove the joint embedding property for normal models of open induction."
(l. 86): "[Macintyre-Marker 89] asked: *Is there a recursive model of open induction with infinite primes?*" (l. 88): "Unlike the models constructed by Moniri and Biljacović, the one of Berarducci and Otero is based on an effective version of a theorem of [Wilkie 78] and has the further property of being "normal" (integrally closed in its fraction field)."

**B6. Conway's candidate series; omnific integers; surreal numbers — [Conway 76].**
(l. 68): "However [Conway 76] contains the following candidate for an irreducible element of $\mathbf{R}((\mathbf{G}^{\leq 0}))$ (Conway's group $\mathbf{G}$ is a proper class because he works inside the huge ring of "**omnific integers**", which is an integer part of the real closed field of "**surreal numbers**"): $$\sum_n t^{-1/n} + 1$$". **Re-symbolled**: the paper changes Conway's variable and sign convention, and says so: "(Conway did not have the minus sign in the exponents because of the change of variables $x = t^{-1}$, but then one has to consider anti-well-ordered supports.)" (l. 72). Also (l. 160): "the larger real closed field of **surreal numbers** [Conway 76, Note on page 28]" for the fact that $(OR, \oplus, \odot, \leq)$ embeds in an ordered field. (l. 688): "Conway's book asks whether in $K((\mathbf{G}^{\leq 0}))$ (actually in the ring of omnific integers) any two factorizations have a common refinement."

**B7. Gonshor's partial results, his candidate, his reduction idea — [Gonshor 86].**
(l. 74): "[Gonshor 86] obtains several partial results, some against the existence of irreducibles in $\mathbf{R}((\mathbf{G}^{\leq 0}))$, and some in favor. He points out the importance of the special case $\mathbf{G} = (\mathbf{R}, +, 0, \leq)$ and shows how to reduce to it, in some cases, at the expense of expanding the field of coefficients $\mathbf{R}$. Gonshor's book contains the following quite different candidate for an irreducible series: $$t^{-\sqrt{2}} + t^{-1} + 1$$ which was also considered in Conway's lectures."
(l. 640): "In his book Gonshor sketches an argument to reduce the general case to the case $\mathbf{G} = \mathbf{R}$. He first proves that in order for a series to be irreducible, the elements of its support—excluding zero—must belong to the same **archimedean class** … He then argues from this fact that the interesting case is $\mathbf{G} = \mathbf{R}$." **Generalised/completed**: the appendix "turn[s] Gonshor's idea into a complete proof" (l. 640) using Mourgues's suggestion (B8). Abstract: "To handle the general case we use a suggestion of M.-H. Mourgues, based on an idea of Gonshor, which allows us to reduce to the special case $\mathbf{G} = \mathbf{R}$."

**B8. Mourgues's suggestion (personal communication) — convex subgroups $\mu \subset Fin$.**
(l. 640): "I had the opportunity to speak with M.-H. Mourgues, who explained me how to turn Gonshor's idea into a complete proof using the fact that every element of $\mathbf{G}$ lies in the set-theoretic difference of two convex subgroups $\mu \subset Fin$ of $\mathbf{G}$ with archimedean quotient $Fin/\mu$. The argument which follows is a result of that conversation." Section title: "12. Appendix: reduction to the case $\mathbf{G} = \mathbf{R}$ (based on ideas of Gonshor and Mourgues)".

**B9. Irreducibility of $t^{-\sqrt 2}+t^{-1}+1$ in the finite-support ring — [Biljacovic 96], [Moniri 94].**
(l. 84): "[Biljacovic 96] showed that $t^{-\sqrt{2}} + t^{-1} + 1$ is irreducible in the subring $K[\mathbf{G}^{\leq 0}]$ of $K((\mathbf{G}^{\leq 0}))$ consisting of all series with finite support. His results were preceded by a related result of [Moniri 94] which showed its irreducibility in a smaller ring." (l. 116): "Combined with Biljacović's work, this shows that $t^{-\sqrt{2}} + t^{-1} + 1$ is irreducible in $K((\mathbf{R}^{\leq 0}))$." Note the two spellings "Biljacovic" (citation key) and "Biljaković" (prose).

**B10. Wilkie's observation on Puiseux series (personal communication, unpublished).**
(l. 64): "Alex Wilkie noted that the Puiseux series with real coefficients form a real closed subfield of $\mathbf{R}((\mathbf{Q}))$ which has a standard part (and also an integer part) without irreducible elements."

**B11. Natural sum / natural product ("Hessemberg's product") — [Hausdorff 27, p. 68], [Pohlers 80].**
(l. 124): "a commutative variant of it known as "**natural product**" or "Hessemberg's product" [Hausdorff 27], which we write as $\odot$." (l. 242): "(see [Hausdorff 27, p. 68] or [Pohlers 80])". **Re-symbolled**: the paper fixes its own symbols $\oplus$, $\odot$ ("which we write as $\odot$"); the name "natural sum/product" is adopted; "Hessemberg's product" is mentioned as an alias once and never used again. The transcription's "Hessemberg" is probably "Hessenberg" (unverifiable).

**B12. Facts about additive/multiplicative principal ordinals — [Pohlers 80].**
(l. 260): "For the following results see [Pohlers 80]." (Facts 3.7, 3.8). The terminology "additive principal", "multiplicative principal" is not explicitly attributed but sits under this citation; the paper's abbreviations $\mathbf{H}$ and $\mathbf{MP}$ are its own (the letter $\mathbf{H}$ presumably for "Hauptzahl", not stated).

**B13. Ordered field containing $(OR, \oplus, \odot, \leq)$ — [Sikorski 48], [Conway 76].**
(l. 160): "$(OR, \oplus, \odot, \leq)$ is contained in an ordered field, for instance the one defined in [Sikorski 48], or the larger real closed field of **surreal numbers** [Conway 76, Note on page 28]."

**B14. Krull valuation — [Endler 72].**
(Remark 1.1, l. 162): "We can obtain a Krull valuation [Endler 72] by reversing the order."

**B15. Direct-summand theorem for divisible groups — [Baer 40], [Fuchs 70, vol. 1, Theorem 21.2].**
(l. 654): "In a divisible abelian group every subgroup is a direct factor. … (See [Baer 40] or [Fuchs 70, vol. 1, Theorem 21.2].)"

**B16. Wilkie's theorem / exponentiation — [Ressayre 93, Ressayre 95], [Dries et al. 94], Kuhlmann papers.**
(l. 44): "Ressayre has exploited integer parts to give a new proof of Wilkie's theorem on the model completeness of the reals with exponentiation, and to give a complete axiomatization of the elementary properties of the exponential function [Ressayre 93, Ressayre 95]. (See [Dries et al. 94] for a related proof not using integer parts.)" (l. 694): "A general discussion of real closed exponential fields can be found in the papers of Ressayre and in the papers of S. Kuhlmann and F.-V. Kuhlmann cited in the bibliography." ([Dries et al.] 1997 and [Mourgues 93] appear in the reference list but are not cited in the text as transcribed.)

**B17. Problems inherited and restated in §13.**
- From Conway (l. 688): "whether in $K((\mathbf{G}^{\leq 0}))$ (actually in the ring of omnific integers) any two factorizations have a common refinement. This would guarantee that factorizations are unique when they exist."
- From conversation with the Kuhlmanns (l. 690): "A related question, which arose during a conversation with Franz-Victor and Salma Kuhlmann, is whether $K((\mathbf{G}^{\leq 0}))/J$ is a unique factorization domain. The existence of the ordinal value map $v_J$ immediately ensures that there are no infinite ascending chains of principal ideals, so every element is a product of irreducible elements."
- From Ressayre (l. 695): "it would be interesting to axiomatize—as already observed by Ressayre—the class of all exponential integer parts of real closed fields."
- From [Otero 93-2] (l. 698): "(By the work of [Otero 93-2] the theory open induction plus the normality axiom scheme does.)"

**B18. Acknowledged origin of the problem (not a citation).**
(l. 706): "I thank Angus Macintyre and Dave Marker for having called to my attention, in the summer of 1995, the problem of the existence of irreducible generalized power series". Also: "whether the series $\sum_n t^{-1/n}$ is irreducible in $\mathbf{R}((\mathbf{R}^{\leq 0}))$" — the original question, **without** the $+1$ and over $\mathbf{R}$.

---

## Part C. What the paper assumes you have read (field notions used without definition or citation)

For each: the term, how it is used, a representative quote, and a note that the meaning attached is inference.

**C1. "order type" of a well-ordered set; $ot(B)$ for sets.**
Used from Lemma 4.1 on without definition ("$ot(B \cup C) \leq ot(B) \oplus ot(C)$", l. 270). Inferred meaning: the unique ordinal order-isomorphic to $B$. The paper defines $ot$ only for series (Def. 5.2), by reference to the order type of the support. Not defined for sets.

**C2. Well-ordered; initial segment; final segment; proper initial segment; limit order type.**
Used freely: "every proper initial segment of $B \cup C$ has order type $< \rho$" (l. 283); "$H_{\beta}$ be the initial segment of $B \cup C$ of order type $\beta$" (l. 274); "every non-empty final segment of $B_i$" (l. 304); "If $B$ has limit order type" (l. 278). The paper glosses "well ordered" once ("i.e. it contains no infinite descending chain", l. 23) but defines none of the segment vocabulary. Inferred: standard order-theoretic meanings; "final segment" = upward-closed subset.

**C3. Real closed field; ordered field; archimedean; non-archimedean; infinitesimal; finite/infinite elements; convex subring/subgroup.**
"if $F$ is non-archimedean it can have non-isomorphic integer parts" (l. 44); "contains an isomorphic copy of the integers $\mathbf{Z}$ as a convex subring" (l. 44); "The set of all infinitesimal elements of $\mathbf{R}((\mathbf{G}))$ is easily seen to be $\mathbf{R}((\mathbf{G}^{>0}))$" (l. 58); "the intersection of all convex subgroups of $\mathbf{G}$ containing 1" (l. 650). None defined. Inferred: standard ordered-field / ordered-group senses; "archimedean" for a group means any two non-zero elements are comparable up to integer multiples (as the paper itself says under the heading "archimedean class", A51, attributed to Gonshor).

**C4. Discrete ring; "normal" model; "models of open induction"; "joint embedding property"; "recursive model"; "elementarily equivalent".**
"Any integer part is a discrete ring" (l. 58); "has the further property of being "normal" (integrally closed in its fraction field)" (l. 88 — this one is glossed); "the joint embedding property for normal models of open induction" (l. 46); "or even not elementarily equivalent ones" (l. 44). Logic/arithmetic background taken as read. Inferred: "discrete ordered ring" = ordered ring with 1 the least positive element.

**C5. Valuation, absolute value, valuation ring, fraction field, domain.**
"Thus $v_J$ is an **non-archimedean absolute value** on $K((\mathbf{R}^{\leq 0}))/J$ except for the fact that usually absolute values are defined on fields, and $K((\mathbf{R}^{\leq 0}))/J$ is only a domain." (l. 160); "$K((\mathbf{R}^{\leq 0}))/J$ is *not* a valuation ring" (l. 164). Only "Krull valuation" receives a citation. Inferred: standard valuation-theoretic senses; the paper's "valuation" for $v_J$ is self-consciously non-standard ("a new kind of valuation", "surreal valuations", l. 693).

**C6. Puiseux series.**
"the Puiseux series with real coefficients form a real closed subfield of $\mathbf{R}((\mathbf{Q}))$" (l. 64); "the real closed field of the Puiseux series with real coefficients has an integer part without infinite irreducible elements" (l. 694). Not defined. Inferred: series in $t^{1/n}$ for some fixed $n$, i.e. $\bigcup_n \mathbf{R}((t^{1/n}))$.

**C7. Irreducible, unit, prime, prime ideal, maximal ideal, noetherian, unique factorization domain, ascending chain of principal ideals.**
"Since this ring is not noetherian the answer is not immediate." (l. 64); "The primes of $\mathbf{Z}$ remain prime in $\mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{Z}$" (l. 62); "$J$ is a prime ideal" (Cor. 9.8); "whether the irreducible elements of $K((\mathbf{G}^{\leq 0}))$ generate prime ideals" (l. 686). Standard commutative algebra; "irreducible" is glossed by the sentence in A9 but never set out as a definition. Note the paper uses "prime" for elements of $\mathbf{Z}$ and "infinite primes" for irreducibles in models of open induction (following Macintyre–Marker, l. 86), while in its own ring it says "irreducible", never "prime element".

**C8. Germ (the topological/analytic notion behind "germs of power series").**
"The elements of $K((\mathbf{G}^{\leq 0}))/J$ can be thought of as **germs of power series**." (l. 144). The analogy with germs of functions is assumed; the paper's definition (A12) is its own.

**C9. Order topology; topological closure; isolated point.**
"$\gamma$ is in the topological closure of the support of $b$ with respect to the order topology of $\mathbf{G}$" (l. 364); "the set of all isolated points of the support of $b$" (l. 395). Standard.

**C10. Lexicographic ordering; direct sum; $\mathbf{Q}$-vector space; linearly independent over $\mathbf{Q}$.**
"The ordering on $H \oplus \mu$ (induced by $\mathbf{G}$) is lexicographic" (l. 654); "its exponents must be linearly independent over $\mathbf{Q}$, as otherwise a change of variables will transform the series into an ordinary polynomial of degree $> 2$ over the reals" (l. 78). Standard.

**C11. Change of variables in the exponent group.**
"as otherwise a change of variables will transform the series into an ordinary polynomial" (l. 78); "because of the change of variables $x = t^{-1}$" (l. 72). The notion of substituting $t^{\gamma} \mapsto$ powers of a new variable is taken as understood.

---

## Part D. Generic machinery presupposed (standard mathematics outside the field)

- **Ordinal arithmetic** (sum, product, exponentiation, Cantor normal form, limit/successor ordinals, cofinality of $\omega$-sequences, countable ordinals). Choices fixed: recursion "on their second argument", continuity "in their second argument" (l. 228); CNF written with repeated exponents (A23); 0 counted as additive principal (A22); $1 \in \mathbf{MP}$ (A26); "$\omega_1$" used for the first uncountable ordinal (l. 238).
- **Transfinite induction** on ordinals and on a custom ordinal-valued "complexity" (§9): "This is proved by induction on a suitable notion of complexity of the formal expressions" (l. 170); "By induction on $ot(B) \odot ot(C)$" (l. 288); "We proceed by induction on $ot(B \cup C)$" (l. 272).
- **Well-ordering principle / choice**: "Let $\prec$ be a fixed well ordering on $K((\mathbf{R}^{\leq 0}))$ (actually a linear ordering suffices)." (l. 554).
- **Completeness of $\mathbf{R}$**: "Using the completeness of $\mathbf{R}$" (l. 403); sequences, subsequences, suprema: "by taking a subsequence we can assume $\beta_n \leq \beta_{n+1}$" (l. 421).
- **Free commutative monoid** (Def. 9.1).
- **Iverson bracket** notation $[\phi]$, introduced ad hoc (l. 453).
- **Classes vs sets**: "$OR$ the class of all ordinals", "proper class" (l. 68, 106, 684).
- **Basic commutative algebra**: ideals, quotient rings, prime/maximal ideals, units, domains, fraction fields, noetherian.
- **Elementary plane geometry** for Lemma 7.4: lines $L_\gamma$ of slope $-1$ in $\mathbf{R}^2$, Figure 1.

---

## Part E. How the paper talks (native phrasing, by object)

Representative sentences, grouped by the object they are about. These are the models for wording.

**E1. Stating where a series lives / its shape.**
- "Suppose that $a \in K((\mathbf{R}^{\leq 0}))$ is not divisible by any monomial $t^{\gamma}$ with $\gamma < 0$." (l. 616)
- "suppose that $a \in K((Q^{<0})) \subset K((\mathbf{G}^{\leq 0}))$ has support of order type $\omega$ or $\omega^{\omega^{\alpha}}$ ($\alpha$ an ordinal)" (l. 100)
- "Let $b, c$ be non-zero elements of $K((\mathbf{R}^{\leq 0}))$ with critical points $x, y$ respectively." (l. 612)
- "Given $0 \neq b \in K((\mathbf{R}^{\leq 0}))$" (l. 604)
- "a series $a \in \mathbf{R}((\mathbf{G}^{\leq 0}))$"; "the series $b^{|\gamma}$"; "a series of ordinal value $\omega^3$"; "series with positive coefficients" (l. 132); "series whose support is a set" (l. 106).
- "the coefficients of $t^{\delta}$ in $b$ and $c$ coincide" (l. 362); "the coefficient of $t^{\delta}$ in $d$ is zero" (l. 458); "0 is in the support of $b$" (l. 324); "the support of $b$ contains 0 as an isolated point" (l. 618).

**E2. Irreducibility and factorization.**
- "$K((\mathbf{G}^{\leq 0}))$ *does have irreducible elements.*" (l. 92)
- "then both $a$ and $a + 1$ are irreducible in $K((\mathbf{R}^{\leq 0}))$" (l. 616)
- "Suppose $a = bc$ with $b, c$ not invertible in $K((\mathbf{R}^{\leq 0}))$." (l. 618)
- "Suppose $a = bc$ is a non-trivial factorization in $K((\mathbf{R}^{\leq 0}))$." (l. 630)
- "if we have a non-trivial factorization $a + 1 = bc$ in $K(\mathbf{G}^{\leq 0})$" (l. 650) [sic, single parentheses]
- "which do not admit a factorization $a = bc$ with $b, c \notin \mathbf{R}$" (l. 64)
- "so all the elements of $J$ are trivially reducible" (l. 140)
- "Any irreducible element of $K[\mathbf{R}^{\leq 0}]$ remains irreducible in $K((\mathbf{R}^{\leq 0}))$." (l. 114)
- "the problem of the existence of irreducibles in $K((\mathbf{G}^{\leq 0}))$ remained open" (l. 86)
- "we could for instance exclude a factorization with two factors, one of order type $\leq \omega$ and the other of order type $\leq \omega^n$" (l. 706)
- "puts restrictions on the order types of the possible factors" (l. 130)
- "any two factorizations have a common refinement" (l. 688); "factorizations are unique when they exist" (l. 688); "every element is a product of irreducible elements" (l. 690).

**E3. Ordinal-value statements.**
- "$b$ has ordinal value $\rho$" / "$b^{|\gamma_{\alpha}}$ has ordinal value $\rho$, namely $\gamma_{\alpha} \in X(b)$" (l. 403)
- "for every $b \in K((\mathbf{G}^{\leq 0}))$ of value $> 1$" (l. 383); "If some $b_i$ have value 1 we can delete it from both sides." (l. 586)
- "$v_J(bc)$ is as big as possible" (l. 190); "showing that $v_J((bc)^{|\gamma})$ is "big" for "many" values of $\gamma$" (l. 190); "has its expected ordinal-value" (l. 200)
- "$+ \text{ terms of value } < v_J^r(b) \odot v_J(c)$" (l. 478); "terms of small value" (l. 192)
- "it is reasonable to consider the term $b^{|\gamma}$ simpler than $b$, because it has smaller ordinal value provided $\gamma$ is sufficiently small" (l. 216)
- "the terms of small value of the above equation include also $b^k c c^{|\gamma}$" (l. 506)
- "By the submultiplicative property, we can now divide by $c$ and conclude that" (l. 539)

**E4. Order types and supports.**
- "the order type of the product is "roughly" the product of the order types" (l. 124)
- "there is no way of predicting the order type of a product $bc$ given the order types of $b$ and $c$ (e.g. take $c = b^{-1}$)" (l. 124)
- "every sufficiently small final segment of a non-zero ordinal $\alpha$ has order type equal to the principal part of $\alpha$" (l. 240)
- "the support of $b + c$ is included in the union $S_b \cup S_c$ of the respective supports, and the support of $bc$ is contained in $S_b + S_c$" (l. 328)
- "$(-\varepsilon, 0) \cap X(b)$ has limit order type $\lambda$" (l. 405)
- "Since the $x_n$ range over a well-ordered set (the closure of the support of $b$)" (l. 606)
- "any well-ordered subset of $\mathbf{R}$ is countable" (l. 606); "the order types of the well-ordered subsets of $\mathbf{G}$ are exactly the countable ordinals" (l. 268)
- "$ot$ has image contained in the countable ordinals" (l. 124)

**E5. Germs, truncations, congruences.**
- "Two series (both not in $J$) have the same germ if they have a common final part." (l. 144)
- "$b, c$ coincide near $\gamma$" (l. 184)
- "The series $b^{|\gamma}$ is obtained by truncating $b$ at $\gamma$ and multiplying the resulting series by the normalization factor $t^{-\gamma}$." (l. 184)
- "Since $b \equiv c \mod J$ implies $v_J(b) = v_J(c)$, we can pass to the quotient and obtain a map" (l. 156)
- "By Lemma 7.1 and Remark 6.3 we can assume $\gamma \in \overline{B} + \overline{C}$; otherwise both sides are $\equiv 0 \bmod J$." (l. 453)
- "The convolution formula says that $\gamma$ is not in the closure of the support of $d = \ldots$" (l. 455)
- "these germs at $\gamma$ behave like generalized coefficients" (l. 184); "$b \mapsto b^{|\gamma}$ behaves like a derivation" (l. 194); "$w_J$ … behaves like a polynomial degree" (l. 162).

**E6. The ideal $J$ and the quotient.**
- "An element is in $J$ iff it is divisible by a monomial" (l. 140)
- "$J$ consists of all the series with negative support bounded away from zero" (l. 314)
- "It implies in particular that the ideal $J$ is prime." (l. 152)
- "$J$ is the set of all $x$ with $v_J(x) = 0$." (l. 596)
- "$K((\mathbf{R}^{\leq 0}))/J$ is only a domain" (l. 160)

**E7. Rings and their units.**
- "The units of $\mathbf{R}((\mathbf{G}^{\leq 0}))$ are the elements of $\mathbf{R}$" (l. 64); "the units of the two rings are different" (l. 670); "because $b$ is not a unit" (l. 618)
- "$\mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{Z}$ is an integer part of $\mathbf{R}((\mathbf{G}))$" (l. 54)
- "contains a subring isomorphic to $\mathbf{R}[\mathbf{Q}^{\leq 0}]$ (by divisibility of $\mathbf{G}$)" (l. 64)
- "Since $\mu$ is a subgroup of $\mathbf{G}$, $F := K((\mu))$ is a field" (l. 670)

**E8. Reductions and specialisations.**
- "which allows us to reduce to the special case $\mathbf{G} = \mathbf{R}$ at the expense of enlarging the field of coefficients $K$" (l. 94)
- "After multiplying by suitable monomials we can reduce to the case $b, c \notin J$." (l. 600)
- "The problem has been reduced to showing that $a + 1$ is irreducible in $K((Fin^{\leq 0}))$." (l. 654)
- "We will be done if we show that $a + 1$ is irreducible in $K((Fin^{\leq 0}))$." (l. 650)
- "So both assumptions on $a$ remain true if we see $a$ as an element of $F((H^{\leq 0}))$." (l. 670)
- "(This is a technical assumption that can always be ensured by interchanging the roles of $b, c$.)" (l. 206)
- "we introduce an asymmetry between $b$ and $c$" (l. 194); "$b$ and $c$ do not play a symmetrical role in our arguments" (l. 216)

**E9. Proof connectives and stock phrases (with rough counts).**
"iff" 27 vs "if and only if" 3 (so "iff" dominates, even in statements of lemmas); "namely" 9; "provided" 8 ("provided $\gamma \neq 0$", "provided there are ordinals $\beta$ and $\xi$ with…"); "as otherwise" 5; "Without loss of generality" 4; "Suppose for a contradiction" 2 / "For a contradiction suppose" 1; "we are done" 4 ("and we are done. $\square$"); "The desired result follows." 2; "Clearly" 3; "Note that" 6; "It is easy to show"/"it is easy to see" 3; "easily seen" 3; "Hence" 16; "Thus" 15; "Therefore" 9; "It follows that" 5; "Reasoning as in Lemma 7.7 we have" (l. 496); "Putting everything together, we find that" (l. 586); "Immediate from the previous lemma." (l. 590); "In the remaining cases the proof is trivial." (l. 340); "there is nothing to prove" (l. 272, 350); "To finish the proof it suffices to show the opposite inequality." (l. 407); "The non-trivial inclusion is $\subseteq$." (l. 421); "Point 1 follows from the fact that" (l. 451); "The claim is thus proved" (l. 525).

**E10. Hedged / informal register (the paper flags informality with quotation marks).**
Words set in scare quotes: "roughly", "few cancellations", "cancellations", "big", "many", "small", "expected", "simpler", "simplification", "hyper-series", "principal value" (at first mention in §2), "maximal" extension, "normal", "natural product", "natural sum", "omnific integers", "surreal numbers", "surreal valuations", "convolution formula" (in §13). The paper also uses first-person singular in places: "I recommend to the reader to make this simplifying assumption on a first reading." (l. 367); "To be quite honest, this simple idea does not actually work so neatly" (l. 367); "I gave a talk" (l. 640).

---

## Part F. Named results and constructions the paper refers to by name

| Name as used | Where stated | How referred to later |
|---|---|---|
| "multiplicative property" (of $v_J$) | l. 152 (list item 3), Thm. 9.7 | "the proof of the multiplicative property", "the multiplicative property says that $v_J(bc)$ is as big as possible" (l. 190) |
| "submultiplicative property" | Lemma 5.5.2 | "By the submultiplicative property" (l. 480, 539, 549) |
| "convolution formula" | eq. (1) l. 186; Lemma 7.5.2 | "We try to use the convolution formula to compute $(bc)^{|\gamma}$" (l. 190); "the proof of the "convolution formula"" (l. 692) |
| "the main lemma" | §8 title (Lemma 8.2) | not referred to by that name elsewhere |
| "criterion for irreducibility" / "test for irreducibility" | Thm. 10.5 | "our criterion for irreducibility" (l. 694); "The criterion does not apply to the series $t^{-\sqrt{2}} + t^{-1} + 1$" (l. 110) |
| "Cantor normal form" | Fact 3.3 | "From the Cantor normal form of $\beta$ it follows that" (l. 369) |
| "principal part" | Fact 3.3 | "the principal part (see Fact 3.3) of $\rho(\alpha+1)$ is $\rho$" (l. 403) |
| "stable interval" | Def. 5.2 | "let $(-\varepsilon, 0) \cap S_b$ be a stable interval for $b$" (l. 401) |
| "the crucial idea" | §2 V, Lemma 8.2 proof | "The crucial idea is to multiply the above equation by $c$" (l. 498) |
| "complexity" | Def. 9.3 | "by induction on the complexity" (l. 220); "the complexity of $w_2$ is of the form…" (l. 572) |
| "Conway's series" | l. 70 | "So Conway's series is irreducible even in the ring of omnific integers." (l. 684) |
| "natural valuation" $v$ | l. 34 | "($v$ is the natural valuation into $\mathbf{G}$, not the ordinal value)" (l. 650) |
| "ordinal value map" | §13 | "The existence of the ordinal value map $v_J$ immediately ensures…" (l. 690) |
| "surreal valuations" | §13 | "a general theory of "surreal valuations" (valuations inside the field of surreal numbers)" (l. 693) |

---

## Part G. Where the paper says it disagrees with, corrects, or departs from another paper's usage

Collected verbatim; this is every passage of that kind found.

**G1. Conway's sign/variable convention is reversed.**
(l. 72): "(Conway did not have the minus sign in the exponents because of the change of variables $x = t^{-1}$, but then one has to consider anti-well-ordered supports.)" The paper adopts negative exponents and well-ordered supports, and writes Conway's candidate as $\sum_n t^{-1/n} + 1$.

**G2. The alternative notation $K((t))^{\mathbf{G}}$ is noted and not adopted.**
(l. 23): "Another notation for $K((\mathbf{G}))$ is $K((t))^{\mathbf{G}}$, where the formal variable $t$ is displayed. We always use $t$ for the formal variable."

**G3. The problem is recast from $\mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{Z}$ (Conway/Gonshor's integer part) to $\mathbf{R}((\mathbf{G}^{\leq 0}))$.**
(l. 62–64): "it is a natural question whether $\mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{Z}$ contains irreducible elements not in $\mathbf{Z}$. This is easily seen to be equivalent to the question of whether the ring $\mathbf{R}((\mathbf{G}^{\leq 0})) := \mathbf{R}((\mathbf{G}^{<0})) \oplus \mathbf{R}$ has any irreducible element, and we will consider the problem in this latter form."

**G4. Coefficients generalised from $\mathbf{R}$ (Conway, Gonshor) to an arbitrary field of characteristic zero.**
(l. 90–94): "We prove that if $K$ is a field of characteristic zero (not even assumed to be orderable, e.g. the complex numbers) … So it is important to work with a general $K$ and not only with $K = \mathbf{R}$." And the abstract's framing "The field of generalized power series with real coefficients".

**G5. "Valuation" / "absolute value" used in a non-standard sense, acknowledged.**
(l. 160): "Thus $v_J$ is an **non-archimedean absolute value** on $K((\mathbf{R}^{\leq 0}))/J$ except for the fact that usually absolute values are defined on fields, and $K((\mathbf{R}^{\leq 0}))/J$ is only a domain." And (l. 162): "We can obtain a Krull valuation [Endler 72] by reversing the order." — i.e. $v_J$ is multiplicative with respect to $\odot$ and *increases* with size, the reverse of the usual valuation convention; $w_J$ is the "degree-like" version.

**G6. Natural product preferred over ordinal product, with the reason.**
(l. 124): "we need to consider not the usual product of ordinals but a commutative variant of it known as "**natural product**" or "Hessemberg's product" [Hausdorff 27], which we write as $\odot$."

**G7. Open interval chosen over the half-open one in the geometric definition of $v_J$.**
(l. 324): "Note that we consider the open interval $(-\varepsilon, 0)$ rather than the half-open one $(-\varepsilon, 0]$ which would seem more natural. This ensures the validity of the following remark and corresponds to the fact that in clause 3 we work modulo $J + K$ rather than modulo $J$."

**G8. Gonshor's reduction is described as a sketch and completed.**
(l. 640): "In his book Gonshor sketches an argument to reduce the general case to the case $\mathbf{G} = \mathbf{R}$. … He then argues from this fact that the interesting case is $\mathbf{G} = \mathbf{R}$. … M.-H. Mourgues, who explained me how to turn Gonshor's idea into a complete proof". (l. 74): Gonshor "shows how to reduce to it, in some cases, at the expense of expanding the field of coefficients $\mathbf{R}$."

**G9. Distinction from the Macintyre–Marker question.**
(l. 86): "The emphasis here was on the recursiveness of the model (which implies countability), so the question is not the same as the one we consider in this paper (i.e. the existence of irreducible elements in the uncountable ring $K((\mathbf{G}^{\leq 0}))$)." (l. 88): "The resulting ring is a recursive integer part of the field of Puiseux series which is *not* truncation closed, so in this respect behaves differently from the rings considered in this paper."

**G10. Conway's original series needs "+1" in the non-archimedean case.**
(l. 102): "In particular Conway's series $\sum_n t^{-1/n} + 1$ is irreducible (in the non-archimedean case we do need to add 1, as otherwise the series is divisible by a monomial)." Contrast with the acknowledgments (l. 706), where the question originally posed was for $\sum_n t^{-1/n}$ without the 1, in $\mathbf{R}((\mathbf{R}^{\leq 0}))$.

**G11. Self-correction on scope: Theorem 11.2 and the multiplicative property for general $\mathbf{G}$ are left open.**
(l. 116): "We have not checked whether the above theorem holds for a general $\mathbf{G}$ instead of $\mathbf{R}$." (l. 692): "it is still of interest to determine whether the ordinal-value map $v_J \colon K((\mathbf{G}^{\leq 0})) \to (OR, \odot)$ has the multiplicative property even in the case when $\mathbf{G}$ is an arbitrary ordered abelian divisible group. This would imply in particular that the ideal $J \subseteq K((\mathbf{G}^{\leq 0}))$ is prime."

---

## Closing note on the source

This record was made from the Markdown transcription alone; no PDF of Ber00 is in the reference library, so nothing here has been checked against the published rendering. Entries whose content depends on rendering and therefore rest on the transcriber's LaTeX: A1 (bold $\mathbf{G}$ vs other), A15 ("G-polynomials"), A21 ($OR$, $LIM$ upright vs italic), A25 ($\overset{k}{\bigodot}$), A37 (the bar in $b_{|\gamma}$, $b^{|\gamma}$), A49 ($Fin$, $\mu$ as identifiers). Apparent errors listed at the top (Hessemberg; "iff and only if"; "$\odot (C)$"; "Lemma 4.4" for 4.5; index $\gamma$ for $\xi$ at l. 458; single-paren $K(\mathbf{G}^{\leq 0})$ at l. 650; "interger") may be either the article's or the transcriber's. One mathematical inconsistency in the source as transcribed: Def. 3.6 admits $\alpha = 2$ as multiplicative principal while Fact 3.8 excludes it (A26). Entry count: Part A 56, Part B 18, Part C 11, Part D 9 bullets, Part E 10 groups, Part F 14 rows, Part G 11.

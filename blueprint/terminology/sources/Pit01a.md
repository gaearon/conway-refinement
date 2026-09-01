# Pit01a — Pitteloud, "Algebraic properties of rings of generalized power series" (2001): terminology record

## Source and how to read locations

- Source read: the Markdown transcription of the SSRN PDF at
  `blueprint/references/pitteloud_2001_algebraic_properties_generalized_power_series.md`. The
  transcriber records that the PDF contains the 30-page paper twice and transcribes it once. The
  local library has no PDF, so doubtful typography or readings are flagged `[UNVERIFIED]` or
  `[GARBLED?]`.
- Locations: `p.N` = page marker in the transcription (SSRN page numbering 1–30); the paper's own numbering (§, Definition/Lemma/Theorem); `L.n` = line number in the transcription file, computed mechanically by matching the quoted text (check with `sed -n 'n p'`). Where a quoted phrase occurs on several lines, all lines are listed.
- Quotes are verbatim from the transcription, including its LaTeX. The transcription writes open intervals with French brackets `]x, y[`; I reproduce that.
- Sections: §0 Introduction (0.1 Generalized power series, 0.2 Results, 0.3–0.7 theorems), §1 Some recalls about ordinals, §2 The completion $(\tilde G,+,0,\le)$, §3 The convolution formula, §4 The subring $Re$ of real series, §5 A lower bound of $v_0(bc)$, §6 Main results, §7 The failure of the multiplicative property, References. All read in full.
- Global standing assumptions the paper fixes and then relies on silently: (i) p.1 L.34 "From now on, $K$ will always denote a field of characteristic 0 and $G$ an ordered additive abelian group." (ii) p.9 L.342 "Unless otherwise specified, $G$ will always denote a dense ordered group, $\tilde{G}$ is the order-completion of $G$ and $G' \subseteq \tilde{G}$ is the Cauchy-completion of $G$." (iii) p.18 §5.9 L.801 "From now on until the end of this §, - $b, c, d$ denote elements of $K((G^{\leq 0}))$."

Entry kinds: **[DEF]** the paper's own term/notation/convention; **[REUSE]** taken from another paper with attribution; **[ASSUMED]** used as shared field background, not defined or cited; **[GENERIC]** standard mathematics from outside the field.

---

## Part A — What the paper defines (own terms, notation, conventions)

### A1. The objects $K((G))$, $K((G^{\le 0}))$ and their parts

**1. $K((G))$ — "the set of all formal series … having well-ordered support"** [DEF, with reuse of Hahn]
- p.1 §0.1 L.24–L.28: "If $K$ is a field and $G$ any ordered additive abelian group, $K((G))$ is the set of all formal series $$a = \sum_{\gamma \in G} a_\gamma x^\gamma \ , \ \text{ where } a_\gamma \in K \ \ \forall \gamma \in G,$$ having well-ordered support $S_a := \{\gamma \in G : a_\gamma \neq 0\}$."
- L.29: "With obvious operations $+$ and $\cdot$ , $K((G))$ is a field (Hahn 1907, see [Ha])."
- Name, L.31: "$K((G))$ is called the field of generalized power series with coefficients in $K$ and exponents in $G$."
- Phrasing: "formal series" once (L.24); "generalized power series" 8 times in the file (title, abstract, §0.1 heading, the naming sentence, keywords, L.39, and two cited titles); "transfinite series" only inside cited titles ([Pi1], [R1]). Elements are called "series" throughout ("series with non-positive exponents", abstract; "each of these terms $b_{\beta'} c_{\xi'}$ appears in one and only one series $b_{|\beta_i} c_{|\xi_i}$", L.498).
- Conventions: indeterminate $x$, exponents as superscripts $x^\gamma$; coefficients subscripted by exponent ($a_\gamma$, $b_\delta$, $b_{\beta'}$, $c_{\xi'}$). Series are lettered $a, b, c, d$ (never $f, g$). Exponents are Greek ($\gamma, \delta, \beta, \xi, \eta, \theta, \mu$); $\varepsilon$ is a positive element of $G$. The ring of interest is series with **non-positive** exponents; "the monomials with negative exponents" generate $J$; the important direction is "close to 0" from below.

**2. $S_a$ — support** [DEF]
- L.28: "having well-ordered support $S_a := \{\gamma \in G : a_\gamma \neq 0\}$."
- Used as $S_b$, $S_c$, $S_{bc}$, $S_{cd}$, $S_{b^k c}$. Phrasing: "taking supports on both sides" (L.515); "$b^L := \sup(S_b)$" (L.378); "$v_0(b)$ is the order type of a small final segment of the support of $b$" (L.62). "support" appears 7 times in the file.

**3. Ordering of $K((G))$** [DEF]
- L.29: "If $K$ is an ordered field, so is $K((G))$ : We simply put $a = \sum_{\gamma \in G} a_\gamma x^\gamma > 0$ iff $a_\delta > 0$, where $\delta := \min S_a$."
- Convention: positivity decided by the coefficient of the **minimal** exponent. This is the only place the order on $K((G))$ is used.

**4. $K((G^{\le 0}))$ and $G^{\le 0}$** [DEF]
- L.32: "$K((G^{\leq 0}))$ denotes the subring of $K((G))$ whose series have their support included in $G^{\leq 0} := \{\gamma \in G : \gamma \leq 0\}$."
- Abstract: "The subrings $K((G^{\leq 0}))$ consisting of series with non-positive exponents". No proper name beyond "the ring $K((G^{\leq 0}))$" (L.43).
- Cognate notation used without separate definition: $G^{<0}$ (L.44), $G^{>0}$ (L.251), $\tilde G^{<0}$ (L.370), $(G')^{<0}$ (L.568), $\tilde G^{<\mu}$ (L.1250). The general rule is Notation 2) of §3 (entry 28).

**5. $x^\gamma$, "monomial"** [ASSUMED; used, not defined]
- Abstract: "the ideal $J \subseteq K((G^{\leq 0}))$ generated by the monomials with negative exponents"; L.44: "generated by the set of monomials $\{x^\gamma, \gamma \in G^{<0}\}$"; L.373: "which is generated by the set of monomials with negative exponents." "monomial" is not defined; it means $x^\gamma$ with coefficient 1.

**6. Standing hypotheses on $K$ and $G$** [DEF, convention]
- L.34: "From now on, $K$ will always denote a field of characteristic 0 and $G$ an ordered additive abelian group."
- Restated at the main theorem, L.627: "Let $K$ be a field of characteristic 0 and $G$ a dense abelian ordered group."
- Word order varies: "additive abelian ordered group" (abstract), "ordered additive abelian group" (L.24, L.34), "dense abelian ordered group" (L.627), "dense ordered group" (20 occurrences, dominant from §2 on). Characteristic 0 is used only tacitly (the coefficient $k$ in "$kb^{|\gamma}b^{k-1}c$", and "$s_b(kb^{|\gamma}b^{k-1}c) = s_b(b^{|\gamma}b^{k-1}c)$ by Lemma 5.10", L.1068).
- Convention: the real case is written "$G = (\mathbb{R},+)$ is the additive group of the reals" (L.11, L.44), and the ring $K((\mathbb{R}^{\leq 0}))$.

### A2. Ordinal machinery the paper fixes (§1)

**7. $OR$ — the class of all ordinals** [DEF, notation]
- L.116: "We denote by $OR$ the class of all ordinals."
- Used as target of the value map: "$v_0 : K((G^{\leq 0})) \longrightarrow (OR, \odot)$" (L.50); "$Cpl : M \longrightarrow OR$" (L.608); "$OR^{<\omega}$" (L.779).

**8. Ordinal arithmetic conventions** [GENERIC, choice fixed]
- L.117–L.121: "Addition, product and exponentiation in $OR$ are defined by induction on their second argument and are continuous in their second argument: For instance, $\alpha + 0 = \alpha$, $\alpha + (\beta + 1) = (\alpha + \beta) + 1$, $\alpha + \beta = \sup\{\alpha + \xi, \xi < \beta\}$ if $\beta$ is limit."
- Convention: ordinal product by juxtaposition $\alpha\beta$ (L.173); in Cantor normal form the integer is on the **right**, $\omega^\alpha n$. Reference for all of §1: "you can find them for instance in Pohlers [Po]" (L.115).

**9. $ot(E)$ — order type; also "o.t" and "$ot(b)$"** [DEF, notation; two spellings]
- L.130 (bracketed, after Lemma 1.1): "[ If $E$ is a well-ordered set , $ot(E)$ is the order type of $E$ ]."
- L.348, Notation 4): "ot abbreviates order type".
- Applied to a series without definition: Lemma 3.2 b) L.394 "$ot(bc) \leq ot(b) \odot ot(c)$"; L.580 "$ot(b) = v_0(b) = \omega^2$"; Theorem 7.1 L.1221 "$v_0(b) = ot(b) = \omega^{\theta+1}$". Meaning (my inference): $ot(b) = ot(S_b)$; the paper does not say so.
- Variant spelling "o.t" in Definition 5.4 (L.710, L.720). Counts in file: `ot(` 13, `o.t(` 2. **Dominant: $ot$.** [UNVERIFIED whether "o.t" is a transcription artefact.]

**10. Lemma 1.1 (properties of $\omega^\alpha$)** [GENERIC, quoted because used by name]
- L.128–L.129: "a) $\omega^\alpha < \omega^\beta$ if $\alpha < \beta$ and $\beta, \gamma < \omega^\alpha \ \Rightarrow \ \beta + \gamma < \omega^\alpha$ b) If $ot(X) = \omega^\alpha$ and $Y \subseteq X$ , then $ot(Y) = \omega^\alpha$ or $ot(X \setminus Y) = \omega^\alpha$".
- The paper never says "additively indecomposable" or "additive principal"; just "the ordinals $\omega^\alpha$" (L.124).

**11. Cantor normal form; abbreviation "C.n.f."** [GENERIC, notation fixed]
- Theorem 1.2, L.133–L.137: "Let $\alpha \neq 0, \alpha \in OR$. There exists a finite sequence of ordinals $\alpha_1 > \alpha_2 > \ldots > \alpha_k \geq 0$ and a finite sequence of non-zero integers $n_1, n_2, \ldots, n_k \in \mathbb{N}^*$ such that $$\alpha = \omega^{\alpha_1} n_1 + \omega^{\alpha_2} n_2 + \ldots + \omega^{\alpha_k} n_k.$$ Moreover, these two finite sequences are uniquely determined."
- L.349, Notation 5): "C.n.f. abbreviates Cantor normal form."
- "Equality in Cantor normal form" is written $\overset{C.n.f.}{=}$ (L.361, L.556, L.878, L.884; also `\stackrel{C.n.f.}{=}` at L.1135). Phrasing when invoked: "Using the Cantor normal form we write" (L.628); "we can write (using the Cantor normal form)" (L.161).
- Convention: $\mathbb{N}^*$ = non-zero integers (L.133; also L.133, L.590, L.1236); $\mathbb{N}$ allows 0 (Def. 1.4, L.150); $\omega$ also stands for the natural numbers ("$n \in \omega$" L.708; "$\forall k \in \omega$" L.763; "$r \in \omega$" L.1135).

**12. $E^+$ — successor points of a well-ordered set** [DEF]
- Definition 1.3, L.142–L.144: "Let $E$ be a well-ordered set. $E^+ := \{\, x \in E : x \text{ is successor in } E$ , i.e. $\exists y \in E$ such that $y < x$ and $]\, y, x \,[ = \emptyset \,\}$. It is easily checked that if $ot(E) = \omega^\alpha$, $ot(E^+) = ot(E) = \omega^\alpha$."
- Used as $S_b^+$, $(S_b^+)^{<0}$ (L.656 "Let $\gamma \in (S_b^+)^{<0}$ be fixed, sufficiently close to 0 (see 1.3 for the definition of $E^+$)"), $Y_b^i(c)^+$ (L.1007), $X_*^{i-1}(b)^+$ (L.1064).

**13. $\oplus$ — (natural sum; the paper does not name it)** [DEF]
- Definition 1.4, L.149–L.153: "Let $\alpha, \beta \in OR$, and write $\alpha = \omega^{\gamma_1} n_1 + \omega^{\gamma_2} n_2 + \ldots + \omega^{\gamma_k} n_k$ , where $\gamma_1 \geq \gamma_2 \geq \ldots \geq \gamma_k \geq 0$ and $n_i \in \mathbb{N} \ \ \forall \, i$ , $\beta = \omega^{\gamma_1} m_1 + \omega^{\gamma_2} m_2 + \ldots + \omega^{\gamma_k} m_k$ , where $m_i \in \mathbb{N} \ \ \forall \, i$. $$\alpha \oplus \beta := \omega^{\gamma_1}(n_1 + m_1) + \omega^{\gamma_2}(n_2 + m_2) + \ldots + \omega^{\gamma_k}(n_k + m_k).$$"
- Introduced by L.146: "Finally we define the operations $\oplus$ and $\odot$ on $OR$, which are commutative variants of $+$ and $\cdot$, and which play a crucial role in the product formula in $[B]$."
- Example L.156: "$(\omega^2 + 1) + \omega = \omega^2 + \omega, \ \ (\omega^2 + 1) \oplus \omega = \omega^2 + \omega + 1, \ \ \omega + (\omega^2 + 1) = \omega^2 + 1.$"
- The phrase "natural sum" never occurs; only "natural product" for $\odot$. $\oplus$ is also used inside exponents: "$\omega^{\alpha_i \oplus \beta_j}$" (L.164), "$\omega^{\theta \oplus \theta' + 2}$" (L.1223), "$\delta' \oplus \omega^\alpha(kn - t)$" (L.1163), "$\oplus\varepsilon_1\oplus...\oplus\varepsilon_{k-l}$" (L.1122).

**14. $\odot$ — "the natural product"** [DEF]
- L.50: "if $\odot$ denotes the natural product of ordinals (see §1)".
- Definition 1.5, L.160–L.164: "i) $0 \odot \gamma = 0 = \gamma \odot 0$ ii) If $\alpha \neq 0 \neq \beta$ , then we can write (using the Cantor normal form) $\alpha = \omega^{\alpha_1} n_1 + \omega^{\alpha_2} n_2 + \ldots + \omega^{\alpha_k} n_k$ and $\beta = \omega^{\beta_1} m_1 + \omega^{\beta_2} m_2 + \ldots + \omega^{\beta_l} m_l$. $$\alpha \odot \beta := \underset{i,j}{\oplus}\, \omega^{\alpha_i \oplus \beta_j}(n_i m_j).$$"
- Properties L.167–L.174: "a) $\alpha \oplus \beta$ and $\alpha \odot \beta$ are well-defined. b) $(OR, \oplus, \odot, <)$ is an ordered semi-ring. c) $\beta < \gamma \Rightarrow \ \alpha \oplus \beta < \alpha \oplus \gamma$ and $(\alpha < \beta, \gamma \neq 0) \Rightarrow \ \alpha \odot \gamma < \beta \odot \gamma$ d) $\alpha + \beta \leq \alpha \oplus \beta$ and $\alpha\beta \leq \alpha \odot \beta$ e) $\beta, \gamma < \omega^\alpha \ \Rightarrow \ \beta \oplus \gamma < \omega^\alpha$ and $\beta, \gamma < \omega^{\omega^\alpha} \ \Rightarrow \ \beta \odot \gamma < \omega^{\omega^\alpha}$."
- Iterated product L.594: "$[\ (\overset{k-1}{\odot} v_0(b)) := v_0(b) \odot \ldots \odot v_0(b) \ \ (k-1)-\text{times}\ ]$".
- **Convention**: the paper writes "$= \ldots \odot \ldots = \ldots\,\ldots$" to flag that the natural product coincides with the ordinary product in the case at hand: "We always have $v_\gamma(b) = v_\gamma^r(b) \odot v_\gamma^p(b) = v_\gamma^r(b) v_\gamma^p(b)$" (L.562); "$v_0(X) = v^B(X) \odot v^S(X) = v^B(X) v^S(X)$" (L.708); "$s_b(c) \odot s(b)^k = s_b(c) s(b)^k$" (L.765). Componentwise: "i) $\odot$ denotes the componentwise product [$s_b(c)$ and $s(b)$ always have the same length ]." (L.768).

**15. Ordered semi-ring** [GENERIC, named in passing] L.168: "b) $(OR, \oplus, \odot, <)$ is an ordered semi-ring." Not defined.

### A3. The completion $\tilde G$ (§2)

**16. Dense ordered group** [DEF]
- L.182: "Let $(\,G, +, 0, \leq\,)$ be a dense ordered group, i.e. $\forall\, \gamma_1, \gamma_2 \in G$, $\exists \gamma \in G$ such that $\gamma_1 < \gamma < \gamma_2$." (As transcribed; presumably "$\gamma_1 < \gamma_2$" is intended in the hypothesis. [GARBLED?] minor.)
- Dominant hypothesis phrase from §3 on: "Let $G$ be a dense ordered group." (L.424, L.437, L.467, L.506, L.524, L.535, L.547, L.589, L.599, L.1190, L.1200, L.1219, L.1235, L.1245). The paper never uses "divisible" as its own hypothesis (it only reports it of [B] and [Ri]).

**17. Dense ordered semi-group with left-continuous addition** [DEF]
- Definition 2.2, L.188–L.193: "$(\,G, +, 0, \leq\,)$ is a dense ordered semi-group with left-continuous addition iff $\forall\, x, y, z \in G$, 1) $x + y = y + x$, $x + 0 = x$, $x + (y + z) = (x + y) + z$ 2) $(\,G, \leq\,)$ is a linear ordered set 3) $x < y \Rightarrow \ \exists z \in G$ such that $x < z < y$ 4) $x \leq y \Rightarrow \ x + z \leq y + z$ 5) If $z < x + y$, $\exists x' < x \ \exists y' < y$ such that $x' + y' \geq z$."
- Remarks L.200–L.201: "a) Condition 5) says that $+ : \ G \times G \longrightarrow G$ is left-continuous (for the order topology on $G$ ). b) If $G$ is a dense ordered group, Condition 5) automatically holds."
- Motivation L.185: "The definition of $\tilde{G}$ doesn't require $G$ to be a dense ordered group, but only $G$ to be a dense ordered semi-group with left-continuous addition. So we will consider this more general setting."

**18. Order topology** [GENERIC, choice fixed]
- Definition 2.3, L.196: "If $(X, <)$ is a total ordering, by the order topology on $X$ we mean the one whose open sets are the unions of open intervals $]\,x, y\,[ := \{z \in X; x < z \wedge z < y\}, \ x, y \in X$."
- L.198: "If $(\,G, +, 0, \leq\,)$ is as above, we always consider $G$ as a topological space with the order topology."
- Convention: open interval $]x,y[$, half-open $]\mu,\gamma]$ (French style).

**19. $\tilde G$ — "the completion" / "order-completion"** [DEF]
- Definition 2.4, L.206: "$$\tilde{G} := \{ \text{ initial segments of } G \text{ without largest element } \}.$$"
- L.208: "We have a canonical inclusion $G \overset{i}{\longrightarrow} \tilde{G}$ given by $\gamma \mapsto I_\gamma := \{\ \gamma' \in G \mid \gamma' < \gamma\}$." L.209: "If $I, J \in \tilde{G}$, we put $I \leq J$ iff $I \subseteq J$." L.223: "If $I, J \in \tilde{G}$, we put $I + J := \{\gamma + \gamma'; \, \gamma \in I, \gamma' \in J\}$."
- Names: section title "§2: The completion $(\,\tilde{G}, +, 0, \leq\,)$" (L.176); "the order completion of an ordered group" (L.90); "order-completion" (L.249, L.332, L.342). **Dominant in running text: "order-completion" (hyphenated).** Letters $I, J, K$ denote elements of $\tilde G$ in §2 — the paper tolerates the clash with the ideal $J$ and the field $K$.
- Properties as stated: L.184: "The main properties of $\tilde{G}$ are completeness (i.e. each subset of $\tilde{G}$ has a supremum) and left-continuity of $+ : \ \tilde{G} \times \tilde{G} \longrightarrow \tilde{G}$." Lemma 2.5 b) L.216: "$G$ is dense in $\tilde{G}$, i.e. $\forall I < J \in \tilde{G}$, there exists $\gamma \in G$ such that $I < I_\gamma < J$." Lemma 2.6 b) L.229: "$I + 0 = I + I_0 = I, \ \ I + \infty = \infty$ if $I \neq -\infty$, $\ I + (-\infty) = -\infty$, $\ I + J < \infty$ if $I, J < \infty$, $I + J > -\infty$ if $I, J > -\infty$." Remark L.236: "it may happen that $I < J$ and $I + K = J + K$."
- "complete": Lemma 2.8 L.268: "assume that $H$ is complete (i.e. every subset of $H$ has a supremum)". Uniqueness via universal property, L.265: "The uniqueness of $(\,\tilde{G}, +, 0, \leq\,)$ follows at once from the following lemma"; Lemma 2.8 L.270: "Then there is one and only one morphism $f : \tilde{G} \longrightarrow H$ such that $f \circ i = j$."

**20. $-\infty$, $\infty$** [DEF] L.212: "$\emptyset$ and $G$ ( denoted by $-\infty$ and $\infty$ ) are respectively the smallest and the largest elements of $\tilde{G}$." Arithmetic, L.244: "$x + \infty = \infty$, $x + (-\infty) = -\infty$, $\infty + \infty = \infty$, $\infty + (-\infty) = (-\infty) + (-\infty) = -\infty$".

**21. Worked examples of $\tilde G$** [DEF, illustrative] L.240: "**1)** $G = \mathbb{Q}$ with the usual order. $\tilde{G} = \mathbb{R} \cup \{-\infty, \infty\}$." L.242: "It is easy to prove that $\tilde{G} = \mathbb{R}^2 \cup \{(x, \pm\infty) \mid x \in \mathbb{R}\} \cup \{-\infty, \infty\}$". L.249: "In the same manner we can describe the order-completion of $G = \mathbb{R}^\alpha$ with the lexicographic order ($\alpha$ ordinal)." L.251–L.253: "**3)** Let $G$ be a non archimedean group, i.e. $\exists x, y \in G^{>0}$ such that $nx < y \ \forall n \in \mathbb{N}$. Let $G_0$ be a proper convex subgroup of $G$. Let $\gamma := \sup G_0$. If $\gamma_1 < \gamma_2 < \gamma$, then $\gamma_1 + \gamma = \gamma_2 + \gamma = \gamma$." Notation $\tilde{\mathbb{R}^2}$ / $\widetilde{\mathbb{R}^\alpha}$ (L.247, L.263, L.327; L.1226). Example after Lemma 2.11, L.326–L.327: "$G = \mathbb{R} \times \mathbb{Q}$ with the lexicographic order. $G' = \mathbb{R} \times \mathbb{R} = \mathbb{R}^2$ and $\tilde{G} = \tilde{\mathbb{R}^2}$ we saw previously."

**22. Left-continuous / right-continuous** [DEF-ish; standard word, choice fixed]
- Lemma 2.7 L.258: "The addition $+ : \ \tilde{G} \times \tilde{G} \longrightarrow \tilde{G}$ is left-continuous (for the order topology on $\tilde{G}$)." Remark L.263: "The addition is not right-continuous. ( Take $G = \mathbb{R}^2$, and consider the point $((x, \infty); (y, -\infty)) \in \tilde{\mathbb{R}^2} \times \tilde{\mathbb{R}^2}$ )."
- As a proof move: "by left-continuity of $+$" (L.301); "by left-continuity of the addition we get" (L.485).

**23. Cauchy-sequence, Cauchy-complete, Cauchy-completion $G'$** [DEF]
- Definition 2.9, L.277–L.279: "a) A Cauchy-sequence in $G$ is a $\theta$-sequence $\{x_\alpha\}_{\alpha < \theta}$ in $G$ for some limit ordinal $\theta$, such that for every positive $\varepsilon \in G$ there exists some $\beta < \theta$ such that $|x_\alpha - x_{\alpha'}| < \varepsilon$ for all $\alpha, \alpha' > \beta$. b) $G$ is called Cauchy-complete if every Cauchy-sequence in $G$ converges in $G$. c) $G'$ is the Cauchy-completion of $G$ if $G'$ is a Cauchy-complete dense ordered group such that $G$ is isomorphic to a dense subgroup of $G'$. [ It is well-known that the Cauchy-completion of $G$ exists and is unique up to a canonical isomorphism ]."
- Always hyphenated ("Cauchy-complet" 20 occurrences, "Cauchy-sequence" 4; never "Cauchy complete"). Standard hypothesis phrase "Let $G$ be a dense ordered group which is Cauchy-complete ( i.e. $G = G'$ )." / "(i.e. $G = G'$)" (L.424, L.467, L.506, L.589, L.599, L.1219, L.1235, L.1245).
- Reduction phrase L.549: "We first remark that it is sufficient to prove Theorem 4.3 for $G$ Cauchy-complete: [ The canonical embedding $i \ : \ G \ \rightarrow \ G'$ induces a ring-homomorphism $j \ : \ K((G^{\leq 0})) \longrightarrow K(((G')^{\leq 0}))$ which commutes with $v_0$, i.e. $v_0(b) = v_0(j(b)) \ \forall\, b \in K((G^{\leq 0}))\,$]." and L.639: "As for the proof of Theorem 4.3, we can assume that $G$ is Cauchy-complete."
- The prime: $G'$ = Cauchy-completion; $\tilde G$ = order-completion. L.275: "An important fact is that $\tilde{G}$ contains the Cauchy-completion of $G$ as subgroup. We precise this below:".

**24. $\tilde G^i$ irregular points, $G'$ regular points; $|x|$** [DEF]
- Definition 2.10, L.282–L.284: "$\tilde{G} = \tilde{G}^i \cup G' \cup \{-\infty, \infty\}$ where $\tilde{G}^i := \{\, \mu \in \tilde{G} \setminus \{-\infty, \infty\} \mid$ there exists $x \in \tilde{G} \setminus \{0\}$ with $\mu + x = \mu \} =$ {irregular points} $G' := \tilde{G} \setminus (\tilde{G}^i \cup \{-\infty, \infty\}) =$ {regular points } $\supseteq G$."
- Lemma 2.11 a) fixes "$[\, |x| := \max\,(x, -x)\ ]$" (L.287). Lemma 2.11 c)–e) (L.289–L.291): "$(G'$ , $+$ , $0$, $\leq$ $)$ is an ordered group."; "If $x \in \tilde{G}$, then $x \in G'$ iff $x$ has an inverse in $\tilde{G}$"; "$G'$ is the Cauchy-completion of $G$."
- Corollary 2.12 L.332: "$G$ and $G'$ have the same order-completion $\tilde{G}$."

**25. Morphism (of such objects)** [GENERIC, named in passing] Lemma 2.8 L.269: "Let $j : G \longrightarrow H$ be a morphism (of such objects) and $i : G \longrightarrow \tilde{G}$ the canonical inclusion." Not further defined.

### A4. Notation block at the head of §3 (p.9)

**26. Comparison of sets: $X \le Y$, $X \le \gamma$** [DEF] L.345: "1) $X \leq Y$ iff $x \leq y \ \ \forall x \in X \ \forall y \in Y, \ \ \ X \leq \gamma$ iff $X \leq \{\gamma\}$. Likewise for $X < Y$, $X \geq Y$ etc". Context L.344: "Let $X, Y \subseteq \ \tilde{G}$ and $\gamma \in \tilde{G}$."

**27. Square-bracket asides** [DEF, convention of presentation] Recalls, justifications and side-definitions are put in square brackets inside running text: "[ If $E$ is a well-ordered set , $ot(E)$ is the order type of $E$ ]" (L.130); "[ It is well-known that the Cauchy-completion of $G$ exists …]" (L.279); "[ Recall that $\overline{\overline{S_b}}$ is the closure of $S_b$ as subset of $\tilde{G}$ ]" (L.537); "[ We have $b^kc = c \bmod (J)$ and $s(b) = (1)$ ]" (L.993). Dozens of occurrences; this is the paper's standard way of fixing a small notation in passing.

**28. Cut-off notation $X^{\le \gamma}$, $X^{<\gamma}$** [DEF] L.346: "2) $X^{\leq \gamma} := \{\delta \in X : \delta \leq \gamma\}$. Likewise for $X^{<\gamma}, X^{\geq \gamma}$ etc". This is the rule behind $G^{\le 0}$, $G^{<0}$, $\tilde G^{<0}$, $(S_b^+)^{<0}$, $X^j(b)^{<0}$, etc.

**29. Minkowski sum $X + Y$, $\gamma + X$** [DEF] L.347: "3) $X + Y := \{x + y : x \in X, y \in Y\}, \ \ \gamma + X = X + \gamma = \{\gamma\} + X$."

**30. Abbreviations** [DEF] L.348–L.349: "4) ot abbreviates order type 5) C.n.f. abbreviates Cantor normal form."

### A5. Truncations, ordinal value, the ideal $J$ (§3.1, p.9)

**31. Truncation $E_{|\gamma}$, $b_{|\gamma}$ — "the truncation of $b$ at $\gamma$"** [DEF]
- §3.1 1), L.353–L.355: "Let $E \subseteq G$ be well-ordered, $\gamma \in \tilde{G}$ and $b \in K((G))$. Write $b = \sum_{\delta \in G} b_\delta x^\delta$. **1)** $E_{|\gamma} := E^{\leq \gamma}$ and $b_{|\gamma} := \sum_{\delta \leq \gamma} b_\delta x^\delta$ is the truncation of $b$ at $\gamma$."
- Conventions: (i) inclusive ($\delta \le \gamma$); (ii) $\gamma$ may lie in $\tilde G$; (iii) subscript with a vertical bar before $\gamma$: $b_{|\gamma}$. "truncation" 4 times; "the truncated product $(bc)_{|\gamma}$" once (L.1230). In the introduction the word is in scare quotes: "compute the "truncations" mod $(J)$ of a product $bc$" (L.88); "be able to compute the "truncations" $(bc)^{|\gamma}$" (L.384).

**32. Shifted truncation $E^{|\gamma}$, $b^{|\gamma}$** [DEF]
- L.356: "If $\gamma \in G$, we put $E^{|\gamma} := -\gamma + E_{|\gamma}$ and $b^{|\gamma} := x^{-\gamma} b_{|\gamma}$."
- Convention: superscript bar = truncate at $\gamma$ and translate $\gamma$ to $0$; requires $\gamma \in G$. No name is given. This is the form used in the convolution formula and throughout §5 ("$(bc)^{|\gamma}$", "$b^{|\gamma} c$", "$X^{|\gamma}$", "$Y_b^j(c)^{|\gamma}$"); also applied to sets with $\gamma \in \overline X$ ("$v_0(X^{|\gamma}) \geq v^B(X)$", L.711}).

**33. $v_\gamma(E)$ — "the ordinal value of $E$ relatively to $\gamma$"** [DEF]
- §3.1 2) a), L.358–L.361: "The ordinal value of $E$ relatively to $\gamma$ , denoted by $v_\gamma(E)$ , is defined by: i) $v_\gamma(E) := 0$ if $\exists \mu < \gamma$ such that $E \cap ]\,\mu, \gamma\,] = \emptyset$ ii) $v_\gamma(E) := 1$ if $\exists \mu < \gamma$ such that $E \cap ]\,\mu, \gamma\,] = \{\gamma\}$ iii) $v_\gamma(E) := \omega^\delta$ otherwise, where $\delta$ is defined by $ot(E \cap ]\,\mu, \gamma\,[\,) \overset{C.n.f.}{=} \omega^\delta$, for $\mu < \gamma$ sufficiently close to $\gamma$."
- Note "relatively to" (not "relative to"/"at"). Defined for $E \subseteq G$ well-ordered, $\gamma \in \tilde G$; used for $E \subseteq \tilde G$ too (Lemma 3.3 "Let $X \subseteq \tilde{G}^{<0}$ be such that $v_0(X) = \omega^\beta$", L.413; Prop. 7.3 "$v_\mu(E) < v_0^p(b)$", L.1250).

**34. $v_\gamma(b)$ — "the ordinal value of $b$ relatively to $\gamma$"** [DEF]
- L.363: "b) The ordinal value of $b$ relatively to $\gamma$, denoted by $v_\gamma(b)$, is defined by $v_\gamma(b) := v_\gamma(S_b)$."
- Remarks L.369–L.370: "i) If $v_\gamma(b) \neq 0$, $v_\gamma(b) = \omega^\delta$ for some $\delta$. ii) If $b \in K((G^{\leq 0}))$ and $b \neq 0$, $v_\gamma(b) < v_0(b)$ for all $\gamma \in \tilde{G}^{<0}$ sufficiently close to 0."
- Names for $v_0$: "a new kind of valuation taking ordinal numbers as values" (L.50, of [B]); "an "ordinal valuation"" (L.63, scare quotes); "the ordinal value" (Def. 3.1); in running text just "$v_0(b)$" or "value": "a term of value $v_\gamma < \ldots$" (L.592, L.1238, L.1249). Description L.62: "Except in some trivial cases, $v_0(b)$ is the order type of a small final segment of the support of $b$."
- Symbol $v_0$ (subscript = base point $0$); "$v_0 : K((G^{\leq 0})) \longrightarrow (OR, \odot)$" (L.50), "$v_0 : K((G^{\leq 0})) \longrightarrow OR$ induces a map $v_0 : K((G^{\leq 0}))/J \longrightarrow OR$" (L.1204) — same letter reused on the quotient.
- Comparison idiom: "$v_0(bc)$ is big (i.e. close to $v_0(b) \odot v_0(c)$)" (L.643); "if $v_\gamma(bc)$ is big for many $\gamma$, so is $v_0(bc)$" (L.417). "big"/"small" is the paper's informal vocabulary throughout §4–5.

**35. $J$ — the ideal** [DEF (re-defined), REUSE from [B]]
- §3.1 3), L.372–L.373: "$J := \{\, b \in K((G^{\leq 0})); \ \exists \gamma < 0$ such that $S_b \leq \gamma \}$. $J$ is easily seen to be an ideal of $K((G^{\leq 0}))$, which is generated by the set of monomials with negative exponents. The main result of this paper is to prove that $J$ is prime (see §6)."
- Introduction (attributed), L.44: "In his proof Berarducci introduces the ideal $J \subseteq K((G^{\leq 0}))$ generated by the set of monomials $\{x^\gamma, \gamma \in G^{<0}\}$". Abstract: "the ideal $J \subseteq K((G^{\leq 0}))$ generated by the monomials with negative exponents".
- Convention: same letter $J$ as in [B]; written "$J \subseteq K((G^{\leq 0}))$" when first mentioned in a statement (L.48, L.1191). Working criterion "$b \notin J$ iff $v_0(b) \geq 1$" (L.1194). Quotient "$K((G^{\leq 0}))/J$", "the quotient ring" (abstract; L.616).
- $J' := J \cap Re$, Cor. 4.8 L.615–L.616: "i) The ideal $J' := J \cap Re$ is prime in $Re$. ii) In the quotient ring $Re/J$, every element is a product of irreducibles." (ii) writes $Re/J$, not $Re/J'$, as transcribed. [UNVERIFIED])

**36. "$b = c$ mod $(J)$" and "$X = Y$ mod $(J)$"** [DEF]
- Notations L.376–L.377: "i) If $b, c \in K((G^{\leq 0}))$, we put $b = c$ mod $(J)$ iff $b - c \in J$ ( iff $v_0(b-c) = 0$). ii) If $X, Y \subseteq G^{\leq 0}$, we put $X = Y$ mod $(J)$ iff $v_0(X \setminus Y \,\cup\, Y \setminus X) = 0$."
- Convention: modulus in parentheses, "mod $(J)$" (transcribed also as "$\bmod (J)$" in §5.18–5.19). Inclusion mod $J$ is used without definition: "$Y_b^{k+1}(c) \subseteq Y_b^{k+1}(c + d) \bmod (J)$" (L.966). The sign $\equiv$ is never used; the paper writes $=$ and puts "mod $(J)$" at the end of the displayed formula.

**37. $b^L := \sup(S_b)$** [DEF]
- L.378: "iii) If $b \in K((G^{\leq 0}))$, $b^L := \sup(S_b) \in \tilde{G}$."
- Hypothesis form "$b^L = c^L = 0$" (L.590, L.600, L.1236) and "$\mu := c^L \in \tilde{G} \setminus G$" (L.1246). No name; the superscript $L$ is unexplained. Note $b^L \in \tilde G$.

**38. Multiplicative property; the formula $(B)$** [DEF of a label; REUSE of result from [B]]
- L.57: "2) If $G = (\mathbb{R},+)$ , **the multiplicative property holds:** $$v_0(bc) = v_0(b) \odot v_0(c) \ \ \forall \ b,c \in K((\mathbb{R}^{\leq 0})).$$"
- L.385–L.387: "Berarducci proved in [B] that $$v_0(bc) \overset{(B)}{=} v_0(b) \odot v_0(c) \ \ \ \forall \ b,c \in K((\mathbb{R}^{\leq 0})).$$"
- Thereafter "$(B)$" (L.389, L.410, L.531, L.606, L.1100, L.1216) and "the multiplicative property" (L.57, L.65, L.70, L.75, L.107, L.380, L.1214). Section title "§7: The failure of the multiplicative property".

**39. Convention: closures $\overline X$ (in $G'$) and $\overline{\overline X}$ (in $\tilde G$)** [DEF]
- L.421: "**Convention:** From now on, if $X \subseteq G$, $\overline{X}$ denotes the closure of $X$ as subset of the topological space $G'$ and $\overline{\overline{X}}$ denotes the closure of $X$ as subset of the topological space $\tilde{G}$."
- Recalled L.703: "[ Recall that if $X \subseteq G$, then $\overline{X}$ denotes the closure of $X$ in the topological space $G' = G\,$]." and at Def. 4.1 (L.537): "[ Recall that $\overline{\overline{S_b}}$ is the closure of $S_b$ as subset of $\tilde{G}$ ]."
- Used in Prop. 3.4, Cor. 3.9 ("$\overline{\overline{(B+C)}} = \overline{\overline{B}} + \overline{\overline{C}}$ and $\overline{B+C} = \overline{B} + \overline{C}$", L.525), Def. 4.1, Def. 5.4, §5.6 ("$X^0(b) = \overline{S_b}$").

**40. The convolution formula (Proposition 3.4)** [DEF — this paper's extension; REUSE of the formula from [B]]
- L.423–L.429: "**Proposition 3.4:** (the convolution formula) Let $G$ be a dense ordered group which is Cauchy-complete ( i.e. $G = G'$ ). Let $b,c \in K((G))$ and $\gamma \in G$ be given. Then $$(bc)^{|\gamma} = b^{|\beta_1} c^{|\xi_1} + b^{|\beta_2} c^{|\xi_2} + \ldots + b^{|\beta_n} c^{|\xi_n} \text{ mod } (J), \ \ \text{where}$$ $(\beta_1, \xi_1), (\beta_2, \xi_2), \ldots, (\beta_n, \xi_n)$ are all the pairs of $\overline{S_b} \times \overline{S_c}$ such that $\beta_i + \xi_i = \gamma$."
- Name "the convolution formula" (14 occurrences: L.88, L.89, L.97, L.103, L.336, L.338, L.380, L.423, L.505, L.586, L.644, L.652, L.1007, L.1047). Once "the product formula in $[B]$" (L.146) — about [B]'s formula. **Dominant: "the convolution formula".**
- Attribution/generalisation L.89: "The convolution formula was proved in [B] only for $G = (\mathbb{R},+)$ and it is here extended to any Cauchy-complete group." Proof opening L.434: "The proof is almost the same as those given in [B] when $G = (\mathbb{R},+)$. However, it may happen that $G$ is not of cofinality $\omega$ (e.g. $G = \mathbb{R}^{\omega_1}$ with the lexicographic order), which requires some additional lemmas."
- Finiteness L.492: "[ There are only finitely many such pairs because $\overline{S_b}$ and $\overline{S_c}$ are well-ordered ]."
- Specialised form for $b,c \in K((G^{\le 0}))$, L.652–L.654: "As $b,c \in K((G^{\leq 0}))$, using the convolution formula we get $$(bc)^{|\gamma} = b^{|\gamma} c + b c^{|\gamma} + \sum_{\xi + \eta = \gamma;\, \xi, \eta < 0} b^{|\xi} c^{|\eta} \ \text{mod } (J), \ \ \text{for all } \gamma \in G^{<0}.$$" The $k$-th power form (L.1009, L.1049): "$(b^kc)^{|\gamma} = kb^{|\gamma}b^{k-1}c + b^kc^{|\gamma} \;+ \sum_{\ldots} b^lb^{|\theta_1}...b^{|\theta_{k-l}}c \;\;+ \sum_{\ldots} b^lb^{|\theta_1}...b^{|\theta_{k-l}}c^{|\theta} \mod (J)$".

**41. Convolution formula for sets (Corollary 3.8)** [DEF]
- L.505–L.511: "**Corollary 3.8:** (the convolution formula for sets) Let $G$ be a dense ordered group which is Cauchy-complete (i.e. $G = G'$), and $\gamma \in G$. Let $E, F$ be well-ordered subsets of $G$. Then $$(E + F)^{|\gamma} = \bigcup_{1 \leq i \leq n} (E^{|\beta_i} + F^{|\xi_i}) \ \text{mod } (J), \ \ \text{where}$$ $(\beta_1, \xi_1), (\beta_2, \xi_2), \ldots, (\beta_n, \xi_n)$ are all pairs of $\overline{E} \times \overline{F}$ such that $\beta_i + \xi_i = \gamma$."
- Proof device L.514–L.515: "Let $b, c \in K((G))$ be such that $S_b = E$ , $S_c = F$ , $b_\beta = 1 \ \forall \ \beta \in S_b$ and $c_\xi = 1 \ \forall \ \xi \in S_c$. Applying Proposition 3.4 to $b, c$ and taking supports on both sides, we get the result." (The all-ones series is not named.)
- Pattern "also works for sets", L.400: "The proof of Lemma 3.2 also works for sets. Hence we have: **Lemma 3.2 bis:**" — suffix "bis" for the set version.

**42. Lemma 3.3 (from local to global value)** [DEF]
- L.413: "Let $d \in K((G^{\leq 0}))$ and $\theta \in OR$. Let $X \subseteq \tilde{G}^{<0}$ be such that $v_0(X) = \omega^\beta$ for some $\beta \in OR$. Then if $v_\gamma(d) \geq \omega^\theta \ \ \forall\, \gamma \in X$, $v_0(d) \geq \omega^{\theta + \beta}$."
- Gloss L.417–L.418: "Putting $d = bc$ in the lemma above, we see that if $v_\gamma(bc)$ is big for many $\gamma$, so is $v_0(bc)$. Hence we are led to estimate $v_\gamma(bc)$ as precisely as possible." Recalled L.551: "Recall (see 3.3) that in order to prove that $v_0(bc)$ is big, it is sufficient to see that $v_\gamma(bc)$ is big for many $\gamma \in G$."
- The conclusion uses ordinary ordinal product with the local value on the left: "$v_0(bc) \geq v_0(c) v_0(b)$" (L.666).

**43. Lemma 3.5 (fundamental system of neighbourhoods indexed by a regular cardinal)** [DEF]
- L.438: "Let $G$ be a dense ordered group. There is a regular cardinal $\kappa$ such that $\forall\, \gamma \in G$, there exists a fundamental system of neighborhoods $\{U_\alpha\}_{\alpha < \kappa}$ of $\gamma$, which satisfies $U_\beta \subseteq \ U_\alpha \ \ \forall\, \alpha < \beta < \kappa$."
- Proof fixes "[ cf($\alpha$) denotes the cofinality of $\alpha$ ]" (L.445). Spelling "neighborhoods" (US).

**44. Lemma 3.6 "(extraction lemma)"** [DEF]
- L.449–L.451: "**Lemma 3.6:** (extraction lemma) Let $\kappa$ be a regular cardinal and $E$ a well-ordered set. Let $f : \kappa \rightarrow \ E$ be any map. Then there exists $X \subseteq \ \kappa$ such that $X$ is of cardinality $\kappa$ and $f|_X$ is increasing, i.e. $f(\gamma_1) \leq f(\gamma_2) \ \ \forall\, \gamma_1 \leq \gamma_2 \in X$."
- Convention: "increasing" = weakly increasing.

**45. Lemma 3.7 (lifting of decompositions to a nearby point)** [DEF] L.468: "Let $B, C \subseteq \ G$ be well-ordered and closed (in $G$). Let $\gamma \in G$ and $\delta < \gamma$, $\delta \in G$ sufficiently close to $\gamma$. Then for each $(\beta', \xi') \in B \times C$ such that $\beta' + \xi' = \delta$, there exists a unique pair $(\beta, \xi) \in B \times C$ such that $\beta + \xi = \gamma$, $\beta' \leq \beta$ and $\xi' \leq \xi$."

**46. Corollary 3.9 (closure of a sum)** [DEF] L.525: "Let $G$ be a dense ordered group. Let $B, C \subseteq G$ be well-ordered. Then $\overline{\overline{(B+C)}} = \overline{\overline{B}} + \overline{\overline{C}}$ and $\overline{B+C} = \overline{B} + \overline{C}$."

### A6. Real series (§4)

**47. $Re$ — "the subring … of real series"** [DEF]
- Definition 4.1, L.537: "$$Re := \{\, b \in K((G^{\leq 0})) : \overline{\overline{S_b}} \subseteq G'\ \}. \ \ [\text{ Recall that } \overline{\overline{S_b}} \text{ is the closure of } S_b \text{ as subset of } \tilde{G}\ ].$$" then L.539: "[ Observe that if $G = (\mathbb{R},+)$, then $Re = K((\mathbb{R}^{\leq 0}))$]."
- Names: "the subring $Re \subseteq K((G^{\leq 0}))$ of "real" series" (L.70, scare quotes at first mention); "§4: The subring $Re \subseteq K((G^{\leq 0}))$ of real series" (L.104, L.529, L.531). The symbol is the two-letter "$Re$" (transcribed in math italics; [UNVERIFIED] whether upright in print).
- Lemma 4.2 L.542: "$Re$ is a subring of $K((G^{\leq 0}))$." Theorem 4.3 L.547: "Let $G$ be a dense ordered group. Then $v_0(bc) = v_0(b) \odot v_0(c) \ \forall \ b,c \in Re$."

**48. $v_\gamma^r(b)$ — "the residual value of $b$ at $\gamma$"; $v_\gamma^p(b)$ — "the principal value of $b$ at $\gamma$"** [DEF]
- Definitions 4.4 1), L.555–L.558: "Let $b \in K((G^{\leq 0}))$ and $\gamma \in \tilde{G}^{<0}$. Assume that $v_\gamma(b) > 1$. Then $v_\gamma(b) = \omega^\delta \overset{C.n.f.}{=} \omega^{\omega^{\delta_1} m_1 + \ldots + \omega^{\delta_{n-1}} m_{n-1} + \omega^{\delta_n} m_n}$. We put $v_\gamma^r(b) := \omega^{\omega^{\delta_1} m_1 + \ldots + \omega^{\delta_{n-1}} m_{n-1} + \omega^{\delta_n}(m_n - 1)}$, $v_\gamma^r(b)$ is the residual value of $b$ at $\gamma$. $v_\gamma^p(b) := \omega^{\omega^{\delta_n}}$ , $v_\gamma^p(b)$ is the principal value of $b$ at $\gamma$."
- Convention L.560: "Convention: If $v_\gamma(b) = \omega^{\omega^\alpha}$ (i.e. if $n = m_1 = 1$ ) , we set $v_\gamma^r(b) = 1$."
- Remark L.562: "We always have $v_\gamma(b) = v_\gamma^r(b) \odot v_\gamma^p(b) = v_\gamma^r(b) v_\gamma^p(b)$."
- Here the preposition is "at $\gamma$" (contrast "relatively to $\gamma$" for $v_\gamma$). The principal value is the **last** (smallest) factor $\omega^{\omega^{\delta_n}}$.

**49. $Z(b)$ — set of "big points"** [DEF]
- Definitions 4.4 2), L.566: "$$\mathbf{Z(b)} := \{\, \gamma \in \tilde{G}^{<0} : v_\gamma(b) = v_0^r(b)\}.$$" Remark L.568: "If $b \in Re$, then $Z(b) \subseteq (G')^{<0}$."
- Motivation L.552: "The idea is to try to compute $v_\gamma(bc)$ on a set $Z(b)$ of "big points" of $b$, which we now define." Lemma 4.5 L.575: "Let $b \in K((G^{\leq 0}))$. Then $v_0(Z(b)) = v_0^p(b)$."
- Example L.580, L.584: "Let $G = (\mathbb{R},+)$ and $b \in K((\mathbb{R}^{\leq 0}))$ such that $ot(b) = v_0(b) = \omega^2$. … We have $v_0^p(b) = v_0^r(b) = \omega$ and $Z(b) = \{\,\theta_1, \theta_2, \theta_3, \ldots\}$."
- §7 hypothesis "$Z(b) \subseteq \tilde{G} \setminus G$, $Z(c) \subseteq \tilde{G} \setminus G$" (L.1221).

**50. "Main Lemma" (Lemma 4.7) and its phrasing** [DEF]
- L.598–L.602: "**Lemma 4.7:** (Main Lemma) Let $G$ be a dense ordered group which is Cauchy-complete. Let $b,c \in K((G^{\leq 0}))$ be such that $b^L = c^L = 0$ and $v_0^p(b) \leq v_0^p(c)$. If $v_\gamma(b_{|\gamma} b^{k-1} c^2) = (\overset{k-1}{\odot} v_0(b)) \odot v_\gamma(b_{|\gamma}) \odot v_0(c) \odot v_0(c) \ \ \forall\, \gamma \in Z(b)$, then $v_0(b^k c) = (\overset{k}{\odot} v_0(b)) \odot v_0(c)$."
- Lemma 4.6 L.592: "$(b^k c)_{|\gamma} = k b^{k-1} b_{|\gamma} c + b^k c_{|\gamma} + \text{ a term of value } v_\gamma < (\overset{k-1}{\odot} v_0(b)) \odot v_0^r(b) \odot v_0(c)\ ,$ for all $\gamma \in G^{<0}$ sufficiently close to 0." — "a term of value $v_\gamma < \ldots$" recurs in Prop. 7.2, 7.3.
- Complexity sketch L.606–L.608: "The Main Lemma states that if $(B)$ holds for the product $b_{|\gamma} b^{k-1} c^2 \ \ \forall \gamma \in Z(b)$, then it holds for $b^k c$. So we are led to associate a complexity to each product in such a way that the complexity of $b_{|\gamma} b^{k-1} c^2$ is smaller than that of $b^k c$. More precisely: Let $M$ be the free abelian monoid generated by $\{\, d \in Re : v_0(d) > 1\}$. We can build a map $Cpl : M \longrightarrow OR$ such that $Cpl(b_{|\gamma} b^{k-1} c^2) < Cpl(b^k c)$; and we get Theorem 4.3 by induction on the complexity."

### A7. The lower bound and the complexity machinery (§5)

**51. Theorem 5.1 / inequality $(I)$ — "our lower bound"** [DEF]
- L.627–L.634: "Let $K$ be a field of characteristic 0 and $G$ a dense abelian ordered group. Let $b,c \in K((G^{\leq 0}))$ be such that $1 \leq v_0(b) \leq v_0(c)$. Using the Cantor normal form we write $$v_0(b) = \omega^{\omega^{\mu_1} m_1 + \ldots + \omega^{\mu_k} m_k} \ \text{ and } v_0(c) = \omega^{\omega^{\theta_1} n_1 + \ldots + \omega^{\theta_l} n_l}.$$ Let $j$ be the largest integer such that $\theta_j \geq \mu_1$. Then $$v_0(bc) \overset{(I)}{\geq} \omega^{\omega^{\theta_1} n_1 + \ldots + \omega^{\theta_j} n_j + \omega^{\mu_1} m_1}.$$" (Theorem 0.6, L.81, is the same statement with "assume that $v_0(b) \leq v_0(c)$".)
- Referred to as "$(I)$" (L.88, L.645, L.649, L.698, L.774, L.1195, L.1209), and "our lower bound" (L.92, L.338). Section title "§5: A lower bound of $v_0(bc)$". Intent L.624: "We now prove that $v_0(bc)$ is close to $v_0(b) \odot v_0(c)$. Precisely:".

**52. "big point" (informal)** [DEF, explicitly informal]
- L.684: "Let us say (informally) that $\gamma$ is a big point of $d \in K((G^{\leq 0}))$ iff $\gamma \in G^{<0}, \gamma$ is close to 0, and $v_\gamma(d)$ is big (i.e. close to $v_0(d)$)."
- L.685: "The main idea of the proof is to look at the set of big points of a series very closely, and to show that $b^{|\xi} c^{|\eta}$ has "less" big points than $b^{|\gamma} c$ (or $bc^{|\gamma}$ ) for almost all big points $\gamma$ of $b$ (or $c$)". L.691: "$s_b(c)$ takes into account the structure of the "big points of $c$ relatively to $b$"." Always informal; formal counterparts are $Z(b)$ (§4) and $\mathrm{Big}(X)$, $X^n(b)$ (§5).

**53. $X^1(c)$ (special-case set, §5.2)** [DEF, local] L.648: "Suppose furthermore that $v_0(X^1(c)) = 1$, where $X^1(c) := \{\,\gamma \in G^{\leq 0}\, :\ v_\gamma(c) \geq \omega^{\omega^{\theta_1} n_1}\}$." (Same letter as the general $X^n(b)$ of §5.6 but a different definition.)

**54. $v^B(X)$, $v^S(X)$ (unnamed "big"/"small" factors)** [DEF]
- §5.4 a), L.707–L.708: "Let $X, Y \subseteq G^{\leq 0}$ and assume that $v_0(X) > 1$ and $v_0(Y) \geq 1$. **a)** We can write in a unique way $v_0(X) = v^B(X) \odot v^S(X) = v^B(X) v^S(X)$, where $v^B(X)$ has the form $\omega^{\omega^\alpha n}$ for some $\alpha \in OR$ and $n \in \omega$, and $v^S(X) < \omega^{\omega^\alpha}$."
- Not named in words; B/S presumably "big"/"small" (my inference). Example L.723–L.724: "Let $X, Y \subseteq G^{\leq 0}$ be such that $v_0(X) = \omega^{\omega^2 5 + \omega + 1}$ and $v_0(Y) = \omega^{\omega^\omega + \omega^3 4 + \omega^2 + \omega + 3}$. Then $v^B(X) = \omega^{\omega^2 5}$, $v^S(X) = \omega^{\omega + 1}$, $v^B_X(Y) = \omega^{\omega^\omega + \omega^3 4 + \omega^2}$, $v^S_X(Y) = \omega^{\omega + 3}$."
- Applied to supports at L.774: "$v^B_{S_b}(S_{bc}) = v^B_{S_b}(S_c) v^B(S_b)$, which is exacly the statement $(I)$." (sic "exacly").

**55. $\mathrm{Big}(X)$** [DEF]
- L.710–L.711: "$$\mathbf{Big}(X) := \{\gamma \in \overline{X};\ o.t(X \cap ]\gamma - \varepsilon, \gamma]\,) \geq v^B(X) \text{ for all sufficiently small } \varepsilon \in G^{<0}\,\} = \{\gamma \in \overline{X};\ v_0(X^{|\gamma}) \geq v^B(X)\}.$$"
- Transcribed bold ("$\mathbf{Big}$") at the definition, roman ("$\mathrm{Big}$") in Lemma 5.5. [UNVERIFIED.] "$\varepsilon \in G^{<0}$" with "$\gamma - \varepsilon$" as transcribed looks sign-inverted; [GARBLED?] possibly $G^{>0}$ in print.

**56. $v^B_X(Y)$, $v^S_X(Y)$, $\mathrm{Big}_X(Y)$ — relative versions** [DEF]
- §5.4 b), L.713–L.720: "Let $v^B(X) = \omega^{\omega^\alpha n}$ be as above. We can write in a unique way $v_0(Y) = v^B_X(Y) \odot v^S_X(Y) = v^B_X(Y) v^S_X(Y)$, where $v^S_X(Y) <$ $\omega^{\omega^\alpha}$ and is as large as possible. $$\mathbf{Big}_X(Y) \ := \{\gamma \in \overline{Y};\ o.t(Y \cap ]\gamma - \varepsilon, \gamma]\,) \geq v^B_X(Y) \text{ for all sufficiently small } \varepsilon \in G^{<0}\,\} = \{\gamma \in \overline{Y};\ v_0(Y^{|\gamma}) \geq v^B_X(Y)\} \ .$$"
- Lemma 5.5 (L.726–L.731), e.g. "b) - If $\gamma \in \mathrm{Big}(X)$, then $v^B(X^{|\gamma}) = v^B(X)$ and $\mathrm{Big}(X^{|\gamma}) = \mathrm{Big}(X)^{|\gamma}$ - If $\gamma \notin \mathrm{Big}(X)$, then $v^B(X^{|\gamma}) \leq v_0(X^{|\gamma}) < v^B(X)$."

**57. $X^n(b)$ and $Y^n_b(c)$** [DEF]
- §5.6, L.744–L.745: "Let $b,c \in K((G^{\leq 0}))$. We put 1) $X^0(b) = \overline{S_b}$ and $X^{n+1}(b) = \mathrm{Big}(X^n(b))$ for all $n \geq 0$. 2) $Y_b^0(c) = \overline{S_c}$ and $Y_b^{n+1}(c) = \mathrm{Big}_{X^n(b)}(Y_b^n(c))$ for all $n \geq 0$."
- Remarks L.747–L.749: "$X^{n+1}(b) \subseteq X^n(b)$ and $Y_b^{n+1}(c) \subseteq Y_b^n(c)$ for all $n \geq 0$. - $X^j(b) = Y_b^j(b)$ for all $j \geq 0$. - If $v_0(X^n(b)) > 1$, then $v^B(X^{n+1}(b)) < v^B(X^n(b))$ and $v_0(X^{n+1}(b)) < v_0(X^n(b))$."
- Variant "$X_0(b)$" at L.835 — subscript instead of superscript; [GARBLED?] likely a typo for $X^0(b)$.
- $X_*^{i-1}(b)$, L.1061: "Let $X_*^{i-1}(b) := \{\, \gamma \in X^{i-1}(b) : \; \omega^{\omega^\alpha(n-t)} \leq v_0(X^{i-1}(b)^{|\gamma}) < \omega^{\omega^\alpha(n-t+1)} \,\}$." with $t$ from L.1056: "Write $v^B(X^{i-1}(b)) = \omega^{\omega^\alpha n}$ and let $t \geq 1$ be the smallest integer such that $$v_0(\{\, \gamma \in X^{i-1}(b) : \; v_0(X^{i-1}(b)^{|\gamma}) \geq \omega^{\omega^\alpha(n-t)} \,\}) \geq \omega^{\omega^\alpha t}.$$"

**58. $s(b)$, $s_b(c)$ — "two finite sequences of ordinals"** [DEF]
- §5.7, L.753–L.755: "Let $b,c \in K((G^{\leq 0}))$ and let $i$ be the least integer such that $v_0(X^i(b)) = 1$. We put 1) $s(b) = (v^B(X^0(b)),\ v^B(X^1(b)),\ \ldots,\ v^B(X^{i-1}(b)),\ 1)$ 2) $s_b(c) = (v^B_{X^0(b)}(Y_b^0(c)),\ v^B_{X^1(b)}(Y_b^1(c)),\ \ldots,\ v^B_{X^{i-1}(b)}(Y_b^{i-1}(c)),\ v_0(Y_b^i(c)))$."
- Standing notation L.757: "We will write $s(b) = (\beta_0, \beta_1, \ldots, \beta_{i-1}, 1)$ and $s_b(c) = (\gamma_0, \gamma_1, \ldots, \gamma_{i-1}, \gamma_i)$." Conventions L.759: "Conventions: If $v_0(b) = 0$ we put $s(b) = (1)$, and if $v_0(c) = 0$ we put $s_b(c) = (1, 1, \ldots, 1)$. $\ [i{+}1 \ 1's]$".
- Motivation L.689: "we will be led to associate to each pair $(b,c) \in K((G^{\leq 0})) \times K((G^{\leq 0}))$ two finite sequences of ordinals $s(b)\,,\ s_b(c) \in OR^{<\omega}$ such that: - $s(b)$ takes into account the structure of the big points of $b$ - $s_b(c)$ takes into account the structure of the "big points of $c$ relatively to $b$"."
- Componentwise operations L.768–L.769: "i) $\odot$ denotes the componentwise product [$s_b(c)$ and $s(b)$ always have the same length ]. ii) Likewise $s(b)^k$ denotes the sequence whose $j^{th}$ component is $s(b)_j^k$. $\ $ [$s(b)_j$ denotes the $j^{th}$ component of $s(b)$]."
- Target identity $(*)$, L.763–L.765: "Our goal is to prove that $\forall\, b,c \in K((G^{\leq 0}))$ such that $v_0(b) \geq 1$, $v_0(c) \geq 1$, and $\forall k \in \omega$ $$(*) \ \ \ s_b(b^k c) = s_b(c) \odot s(b)^k = s_b(c) s(b)^k$$"; boxed at L.983.

**59. $OR^{<\omega}$, $D(OR^{<\omega})$ and their orders $<$, $<_d$** [DEF]
- L.779–L.780: "By $OR^{<\omega}$ we mean the class of all finite sequences of ordinals , and $D(OR^{<\omega}) := \{\, s \in OR^{<\omega}\, :\ s_i > s_{i+1} \ \forall i\,\}$ is the subclass of all finite decreasing sequences of ordinals."
- L.781–L.783: "We order $OR^{<\omega}$ by: $\ \ \ s = (\,s_0, \ldots, s_{n-1}) < t = (\,t_0, \ldots, t_{m-1})$ iff $$n < m \text{ or } (n = m \text{ and } \exists j \text{ such that } s_j < t_j \text{ and } s_k = t_k \ \forall k < j).$$"
- L.785–L.787: "We order $D(OR^{<\omega})$ by : $s = (\,s_0, \ldots, s_{n-1}) <_d t = (\,t_0, \ldots, t_{m-1})$ iff $$(n < m \text{ and } s_i = t_i \, \forall i < n) \ \ \text{or} \ \ (\ \exists j \text{ such that } s_j < t_j \text{ and } s_k = t_k \ \forall k < j).$$"
- L.789: "It is easy to see that $(OR^{<\omega}, <)$ and $(D(OR^{<\omega}), <_d)$ are well-ordered".
- Convention: sequences are 0-indexed; "decreasing" = strictly.

**60. $Cpl$ — "the complexity map"** [DEF]
- §5.8, L.789–L.795: "the complexity map is defined by $$Cpl : K((G^{\leq 0}))^2 \times \omega \ \longrightarrow \ D(OR^{<\omega}) \times OR^{<\omega} \times \omega \ \ \ ,$$ $$(\ b\,,\ c\,,\ k\,) \ \mapsto \ (\ s(b)\,,\ s_b(c)\,,\ k\,)$$ where $D(OR^{<\omega}) \times OR^{<\omega} \times \omega$ is ordered lexicographically (hence well-ordered)."
- Earlier informal version L.692: "We then define a complexity map $$Cpl : K((G^{\leq 0}))^2 \times \omega \ \longrightarrow \ OR^{<\omega} \times OR^{<\omega} \times \omega \ \ \ ,$$ … and proves by induction on this complexity a statement which is somewhat stronger than $(I)$." (sic "proves"). §4 version: entry 50. Phrases: "proceed by induction on the "complexity" of $(b,c,k)$" (L.775); "Assume that $(*)$ holds for all $(b_0, c_0, k_0)$ such that … $Cpl(b_0, c_0, k_0) < Cpl(b, c, k)$" (L.997). "complexity" occurs 10 times.

**61. Proposition 5.20 "(the induction step)"** [DEF] L.996–L.998: "**Proposition 5.20:** (the induction step) Let $(b, c, k) \in K((G^{\leq 0}))^2 \times \omega$ be fixed, and suppose that $(b, c, k)$ doesn't satisfy i), ii) and iii) above. Assume that $(*)$ holds for all $(b_0, c_0, k_0)$ such that $v_0(b_0) \geq 1$, $v_0(c_0) \geq 1$ and $Cpl(b_0, c_0, k_0) < Cpl(b, c, k)$. Then $(*)$ holds for $(b, c, k)$." Base cases L.992–L.994: "i) If $k = 0$. ii) If $v_0(b) = 1$. [ We have $b^kc = c \bmod (J)$ and $s(b) = (1)$ ]. iii) If $k = 1$ and $v_0(c) = 1$. [ We have $S_{b^kc} = S_b \bmod (J)$ and $s_b(c) = (1, 1, ..., 1)$ ]."

**62. $E$, $E_l$, $(E_l)_{t_1,\ldots,t_{k-l}}$, $F_j$, $E'$, $E'_l$, $Z$ (exceptional sets in Case 2)** [DEF, local] L.1089: "$E := \{\, \theta_1 + ... + \theta_{k-l} : \; 0 \leq l \leq k-2,\ \theta_1, ..., \theta_{k-l} \in G^{<0}$ and $s_b(b^lb^{|\theta_1}...b^{|\theta_{k-l}}c) \geq s_b(kb^{|\gamma}b^{k-1}c)\}$"; L.1116: "$F_j := \{\, \theta_j \in G^{<0} : \; \omega^{\omega^\alpha(n-t_j)} \leq v_0(X^{i-1}(b)^{|\theta_j}) < \omega^{\omega^\alpha(n-t_j+1)} \,\}$"; L.1149: "Let $Z := X_*^{i-1}(b)^+ \setminus (E \cup E')$, where $E, E'$ are as in 2) and 3) respectively." ($Z$ here is unrelated to $Z(b)$ of §4.)

**63. "Berarducci's trick"** [REUSE, named device]
- L.687: "If we succeed in doing this, we will get $(bc)^{|\gamma} \approx b^{|\gamma} c + bc^{|\gamma}$ for many $\gamma$ and will be able to conclude using Berarducci's trick (see [B])."
- L.1171: "Multiplying $kb^{|\gamma}b^{k-1}c + b^kc^{|\gamma}$ by $b$ (Berarducci's trick), and using Lemma 5.17, we get". The "trick": multiply the two-term truncation expression by $b$ again and compare with the induction hypothesis for $k+1$. No other name is given.

### A8. Main results and failure (§6–§7)

**64. Theorem 6.1 (primality of $J$)** [DEF, main result] L.1191–L.1195: "Let $G$ be a dense ordered group. Then $J \subseteq K((G^{\leq 0}))$ is a prime ideal. **Proof:** $b \notin J$ iff $v_0(b) \geq 1$. So we have to show that if $v_0(b) \geq 1$ and $v_0(c) \geq 1$, then $v_0(bc) \geq 1$. This is immediate from $(I)$." Introduction's form L.48: "**0.3 Main Theorem:** *$J \subseteq K((G^{\leq 0}))$ is prime for all $G$.*" (0.3 says "for all $G$"; 6.1 says "dense ordered group" — the standing assumption since §3.)

**65. Theorem 6.2 (existence of factorizations in the quotient)** [DEF, main result] L.1199–L.1210: "Let $G$ be a dense ordered group. Each element of $K((G^{\leq 0}))/J$ (not in $K$) admits at least one factorization into irreducibles. **Proof:** We first observe that $v_0 : K((G^{\leq 0})) \longrightarrow OR$ induces a map $v_0 : K((G^{\leq 0}))/J \longrightarrow OR$. The proof is by induction on $v_0(b)$, $b \in K((G^{\leq 0}))/J$. - If b is irreducible, we are done. - If not, we can write $b = cd$ where $c, d$ satisfy $v_0(c) \geq 1$ and $v_0(d) \geq 1$. $(I)$ trivially implies that $v_0(b) = v_0(cd) > \max(v_0(c), v_0(d))$. Hence by induction $c, d$ are products of irreducibles, and so is $b = cd$." Phrasing elsewhere: "admits at least one factorization into irreducibles" (L.12, L.95, L.1201); "every element is a product of irreducibles" (L.616); "is a factorial domain" (L.92, of [B]'s question).

**66. Theorem 7.1 (failure of $(B)$)** [DEF] L.1220–L.1223: "Let $G$ be a dense ordered group which is Cauchy-complete. Let $\theta, \theta'$ be limit ordinals and assume that there exist $b, c \in K((G^{\leq 0}))$ such that $v_0(b) = ot(b) = \omega^{\theta+1}$, $v_0(c) = ot(c) = \omega^{\theta'+1}$, $Z(b) \subseteq \tilde{G} \setminus G$, $Z(c) \subseteq \tilde{G} \setminus G$. Then $$v_0(bc) < v_0(b) \odot v_0(c) = \omega^{\theta \oplus \theta' + 2}.$$" Remark L.1226: "It is easy to show, using the explicit description of $\widetilde{\mathbb{R}^\alpha}$ (see the examples following 2.6) that these hypotheses can be fulfilled if $G = \mathbb{R}^\alpha$ with $\alpha$ of cofinality $\omega$." Introduction's form, Theorem 0.4 L.68: "For many $G$, $\exists b,c \in K((G^{\leq 0}))$ such that $v_0(bc) < v_0(b) \odot v_0(c)$." Proof deferred L.1216: "We mention here without proof that $(B)$ may fail for many groups $G$. For the details, see [Pi1]." Sufficiency remark L.1229: "In order to prove that $v_0(bc) \leq \omega^{\theta \oplus \theta' + 1}$, it is sufficient (and necessary) to show that $v_\gamma(bc) \leq \omega^{\theta \oplus \theta'}$ for all $\gamma \in \tilde{G}^{<0}$ close to 0."

**67. Propositions 7.2, 7.3 (two-term estimates)** [DEF] Prop. 7.2 L.1238: "Let $b, c \in K((G^{\leq 0}))$ be such that $b^L = c^L = 0$ and $v_0^p(b) \leq v_0^p(c)$, and let $k \in \mathbb{N}^*$. Then $$(bc)_{|\gamma} = bc_{|\gamma} + b_{|\gamma}c + \text{ a term of value } v_\gamma < v_0^r(b) \odot v_0(c)\ ,$$ for all $\gamma \in \tilde{G}^{<0}$ sufficiently close to 0." ("$k \in \mathbb{N}^*$" is unused in 7.2 as transcribed — [GARBLED?] possibly carried over from Lemma 4.6.) Prop. 7.3 L.1246–L.1250: "Let $b, c \in K((G))$ be such that $b^L = 0$ and $\mu := c^L \in \tilde{G} \setminus G$. Write $v_0(b) = \omega^\theta$ and assume that $\omega^\theta \leq ot(b) \leq \omega^\theta + 1$. Suppose that $v_0^p(b) \leq v_\mu^p(c)$. Then $(bc)_{|\gamma} = bc_{|\gamma}+$ a term of value $v_\gamma < v_0^r(b) \odot v_\mu(c)$ for all $\gamma \in \tilde{G}^{<\mu} \setminus E$ sufficiently close to $\mu$, where $E$ is some fixed subset of $\tilde{G}^{<\mu}$ such that $v_\mu(E) < v_0^p(b)$."

### A9. Labels and cross-reference conventions

**68. Equation labels over the relation sign** [DEF, convention] Key relations are tagged **over** the relation symbol, not at the margin: "$\overset{(I)}{\geq}$" (L.86, L.634), "$\overset{(B)}{=}$" (L.387), "$\stackrel{(*)}{=}$" (L.983), "$\overset{(+)}{\geq}$" (L.881), justification tags "$\overset{a)}{=}$" (L.826), "$\stackrel{ind}{\geq}$" (L.945), "$\stackrel{i)}{\leq}$" (L.923). Local tags "(+)", "(++)", "(+++)", "(A)", "(B)", "(C)" are used within proofs (p.24–27). [UNVERIFIED: tag placement is as transcribed.]

**69. Numbering and naming of statements** [DEF, convention] Statements are numbered by section ("Lemma 3.2", "Lemma 3.2 bis", "Proposition 3.4", "Corollary 3.8", "Definitions 4.4", "Lemma 4.7: (Main Lemma)"); definitions share the counter; informal subsections are numbered too ("5.2 The ideas of the proof", "5.19 The induction step"). Parenthetical nicknames follow the number: "(Cantor normal form)", "(the convolution formula)", "(extraction lemma)", "(the convolution formula for sets)", "(Main Lemma)", "(the induction step)". Proofs end with "□"; the end of §5 has "□□" (L.1183). Items are "a) b) c)", "i) ii) iii)" or "1) 2)".

**70. "sufficiently close to 0" / "close to 0" / "arbitrarily close to 0"** [DEF, convention of quantification]
- The paper's standard way of saying "for all $\gamma$ in some final segment of $G^{<0}$": "for all $\gamma \in G^{<0}$ sufficiently close to 0" (L.594), "for $\mu < \gamma$ sufficiently close to $\gamma$" (L.361), "Let $\gamma \in (S_b^+)^{<0}$ be fixed, sufficiently close to 0" (L.656), "Let $\gamma \in Y_b^i(c)^+$ be fixed, sufficiently close (and different) to 0" (L.1011), "if $\gamma \in Z$ is close to 0" (L.1150), "for $\gamma \in Z$ arbitrarily close to 0" (L.1167). File counts: "sufficiently close" 16, "close to 0" 24. Never formalised (no "eventually", no "cofinally").
- Also "a small final segment of the support" (L.62), "$X =$ small final segment of $Y_b^i(c)^+$" (L.1042).

---

## Part B — What the paper reuses (with attribution quoted)

**B1. $K((G))$ is a field — Hahn [Ha]** (unchanged) L.29: "With obvious operations $+$ and $\cdot$ , $K((G))$ is a field (Hahn 1907, see [Ha])." Bibliography L.1277: "[Ha] H. Hahn *Uber die nichtarchimedischen Grossensysteme* . S.B. Akad. Wiss. Wien. IIa, 116 (1907), 601-655."

**B2. Real closure of $K((G))$ — [Ri]** L.35: "The fields $K((G))$ play an important role in the theory of real closed fields because if $K$ is real closed and $G$ is divisible, then $K((G))$ is still real closed (see e.g. [Ri])."

**B3. Embedding of real closed fields into $\mathbb{R}((G))$ — [Ka]** (same line): "Moreover, it is a classical fact that if $F$ is a real closed field, then $F$ embeds in some $\mathbb{R}((G))$, see [Ka]."

**B4. Context literature — van den Dries–Macintyre–Marker, Ecalle, van der Hoeven, Ressayre** L.39: "Generalized power series and some variants have been studied by van den Dries, Ecalle, van der Hoeven, Macintyre, Marker, Ressayre and others, in connection with the study of asymptotic functions and o-minimal structures (see e.g. [vdD,Ma,Mar1] , [vdD,Ma,Mar2] , [vdD,Ma,Mar3], [E] , [vdH] , [Re1] , [Re2])." The text cites "[Re1], [Re2]" while the bibliography lists "[R1]", "[R2]" (L.1301, L.1304) — inconsistent keys as transcribed. [M-R] and [Co] are in the bibliography but never cited in the text.

**B5. Irreducibles exist in $K((G^{\le 0}))$ — Berarducci [B], answering Conway–Gonshor** L.43: "In the paper [B] Berarducci considers the ring $K((G^{\leq 0}))$ and proves that $K((G^{\leq 0}))$ does have irreducible elements for all divisible $G$, hence answering a question of Conway-Gonshor." (Gonshor is not in the bibliography; Conway is [Co], uncited in text.)

**B6. The ideal $J$ and its primality for $\mathbb{R}$ — [B]** (symbol $J$ unchanged) L.44: "In his proof Berarducci introduces the ideal $J \subseteq K((G^{\leq 0}))$ generated by the set of monomials $\{x^\gamma, \gamma \in G^{<0}\}$, and shows that $J$ is a prime ideal when $G = (\mathbb{R},+)$ is the additive group of the reals. He asks whether $J$ is prime for all $G$. We prove that this is the case (see §6)". The paper's own equivalent definition (entry 35) — "$\exists \gamma < 0$ such that $S_b \leq \gamma$" — is Pitteloud's phrasing; the ideal is Berarducci's.

**B7. The ordinal-valued map $v_0$ and its properties — [B]** (symbol $v_0$ unchanged; re-defined here as "ordinal value") L.50–L.55: "The results of [B] are based on a new kind of valuation taking ordinal numbers as values. More precisely if $\odot$ denotes the natural product of ordinals (see §1), Berarducci shows that $K((G^{\leq 0}))$ admits a map $v_0 : K((G^{\leq 0})) \longrightarrow (OR, \odot)$ (see §3) with good algebraic properties: 1) For any $G$ we have a) $v_0(b) = v_0(c)$ iff $b - c \in J$ b) $v_0(b+c) \leq \max(v_0(b), v_0(c))$ and we have equality if $v_0(b) \neq v_0(c)$ c) $v_0(bc) \leq v_0(b) \odot v_0(c)$." Remark L.63: "By 1) and 2) above, $v_0$ induces an "ordinal valuation" $v_0 : K((\mathbb{R}^{\leq 0}))/J \longrightarrow (OR, \odot)$." Lemma 3.2 attributed L.389: "In order to prove $(B)$, he first shows that (see [B]):". Whether [B] uses the words "ordinal value"/"relatively to" is not stated.

**B8. The multiplicative property $(B)$ for $G = \mathbb{R}$ — [B]** Entry 38; L.385: "Berarducci proved in [B] that". Questions attributed to [B]: L.65: "It is asked in [B] whether the multiplicative property holds for any $G$. We show that this is not the case (see §7)"; L.92: "Another question asked in [B] is whether $K((G^{\leq 0}))/J$ is a factorial domain."

**B9. $\oplus$, $\odot$ and "the product formula in [B]"** L.146: "Finally we define the operations $\oplus$ and $\odot$ on $OR$, which are commutative variants of $+$ and $\cdot$, and which play a crucial role in the product formula in $[B]$." The symbols are presented as the paper's own definitions (Def. 1.4, 1.5), with the standard name "natural product" for $\odot$; no attribution for the symbols.

**B10. The convolution formula — proved in [B] for $\mathbb{R}$, "here extended"** (generalised) L.89: "The convolution formula was proved in [B] only for $G = (\mathbb{R},+)$ and it is here extended to any Cauchy-complete group." L.434: "The proof is almost the same as those given in [B] when $G = (\mathbb{R},+)$. However, it may happen that $G$ is not of cofinality $\omega$ (e.g. $G = \mathbb{R}^{\omega_1}$ with the lexicographic order), which requires some additional lemmas."

**B11. Results of §4 (real series, Main Lemma, complexity induction) — [B]** L.532: "The proof is an induction on ordinals which is a bit complicated. Instead of giving it, we will just recall the statements and the main idea of the proof. For the details, see [B]." Blanket statement L.97: "Except for the convolution formula (see §3), all the results in §1-4 are proved in [B] or [Pi1]. So we will often sketch (or skip) these proofs."

**B12. "Berarducci's trick"** — entry 63; attributed "(see [B])" at L.687.

**B13. The order-completion $\tilde G$ — [Pi1] (author's thesis)** L.178: "All results of this § are known or easy, so we skip most of the proofs. For details, see [Pi1]." Bibliography L.1292: "[Pi1] D. Pitteloud *Le produit dans les corps de series transfinies.* Thèse de doctorat, Paris 7, 1998."

**B14. The failure of $(B)$ (Theorem 7.1, Props 7.2–7.3) — proofs in [Pi1]** L.1216: "We mention here without proof that $(B)$ may fail for many groups $G$. For the details, see [Pi1]."

**B15. Prime elements — [Pi2], declared independent** L.111: "In our paper [Pi2], we solved affirmatively another question of [B] by proving that $K((G^{\leq 0}))$ does have prime elements if $G = (\mathbb{R},+)$ or more generally if $G$ admits a maximal proper convex subgroup. The results of this paper and [Pi2] are independent." Bibliography L.1295: "[Pi2] D. Pitteloud *Existence of prime elements in rings of generalized power series* . To appear in the Journal of Symbolic Logic."

**B16. Ordinal facts — Pohlers [Po]** L.115: "All results of this § are well-known; you can find them for instance in Pohlers [Po]."

**B17. Existence/uniqueness of the Cauchy-completion — "well-known", uncited** L.279: "[ It is well-known that the Cauchy-completion of $G$ exists and is unique up to a canonical isomorphism ]."

**B18. Acknowledged discussions** L.1255: "I sincerely thank A.Berarducci and J.P. Ressayre for their encouragement on this project and for many helpful discussions. I am also very grateful to the referee for suggestions and comments which improved both content and form of this paper."

---

## Part C — What the paper assumes you have read (field background used without definition or citation)

For each: the term, how used, a quote, and a plain flag that the paper does not define it. Meanings are my inference, not the paper's testimony.

**C1. "real closed field"** — motivating context. Abstract: "play an important role in the study of real closed fields"; L.35: "if $K$ is real closed and $G$ is divisible, then $K((G))$ is still real closed". Not defined.

**C2. "divisible" (group)** — L.35; L.43: "for all divisible $G$". Not defined.

**C3. "ordered additive abelian group" / "ordered group"** — L.24, L.34; group-order notions "positive $\varepsilon \in G$" (L.277), "$G^{>0}$", "$|x_\alpha - x_{\alpha'}|$" used in $G$ before $|x|$ is defined (only in $\tilde G$, L.287). Not defined; the paper defines only the extra adjective "dense" (L.182) and the semi-group axioms (Def. 2.2).

**C4. "convex subgroup", "proper convex subgroup", "maximal proper convex subgroup"** — L.252: "Let $G_0$ be a proper convex subgroup of $G$"; L.111: "if $G$ admits a maximal proper convex subgroup". Not defined.

**C5. "non archimedean group"** — defined inline in an example only, L.251: "Let $G$ be a non archimedean group, i.e. $\exists x, y \in G^{>0}$ such that $nx < y \ \forall n \in \mathbb{N}$." Spelling "non archimedean" (no hyphen, lowercase). "archimedean" itself not discussed.

**C6. "irreducible", "prime" (element), "prime ideal", "factorial domain", "factorization into irreducibles", "product of irreducibles"** — ring vocabulary used without definition: "does have irreducible elements" (L.43); "$J$ is a prime ideal" (L.44); "whether $K((G^{\leq 0}))/J$ is a factorial domain" (L.92); "admits at least one factorization into irreducibles" (L.12, L.95, L.1201); "does have prime elements" (L.111); "every element is a product of irreducibles" (L.616); "If b is irreducible, we are done." (L.1206). Convention: "(not in $K$)" is the paper's way of excluding constants/units (L.12, L.95, L.1201). Never "unit", "UFD", "atomic". Not defined.

**C7. "models of weak axioms for arithmetic"** — abstract: "The subrings $K((G^{\leq 0}))$ consisting of series with non-positive exponents find applications in the study of models of weak axioms for arithmetic." Not defined or cited in text (bibliography has [M-R], [R2] on integer parts).

**C8. "asymptotic functions", "o-minimal structures"** — L.39, context only. Not defined.

**C9. "question of Conway-Gonshor"** — L.43; no citation for Gonshor. Not explained.

**C10. "valuation" (ordinary sense)** — invoked by contrast: "a new kind of valuation taking ordinal numbers as values" (L.50); ""ordinal valuation"" in scare quotes (L.63). The classical min-support valuation on $K((G))$ is never named; it appears only implicitly in the ordering ("$\delta := \min S_a$", L.29). Not defined.

**C11. Cauchy-completion existence/uniqueness** — defined (Def. 2.9) but existence/uniqueness is "well-known" (L.279) — background.

**C12. "$\mathbb{R}^\alpha$ with the lexicographic order", "$\mathbb{R}^{\omega_1}$", "$\mathbb{R}^2$ with the lexicographic order"** — L.249, L.434, L.1226, L.241: ordinal-indexed lexicographic products used as standard examples; never defined (full product vs. finite support not stated). Not defined.

**C13. "$\omega$-blocks"** — appears only in the transcriber's figure description (L.582), not in the paper's text; not testimony.

---

## Part D — Generic machinery presupposed (outside the field), with any choice fixed

**D1. Ordinals, ordinal arithmetic, Cantor normal form, cofinality, regular cardinals.** Choices fixed: recursion/continuity "in their second argument" (L.121); integer coefficients on the right, $\omega^\alpha n$; "$\mathbb{N}^*$" for non-zero integers; $\omega$ doubles as $\mathbb{N}$; "cf($\alpha$) denotes the cofinality of $\alpha$" (L.445); "regular cardinal $\kappa$" (L.438) undefined; "limit ordinal" (L.277) undefined; "$\theta$-sequence $\{x_\alpha\}_{\alpha < \theta}$" (same line) for a transfinite sequence; "$\omega_1$" (L.434).

**D2. Well-orders and order types.** "well-ordered" (13 occurrences, always hyphenated), "$ot$" (entry 9), "initial segment" (L.206; L.443: "we set $X \leq Y$ iff $X$ is an initial segment of $Y$"), "final segment" (L.62, L.1042), "successor" (L.143), "linear ordered set" (L.190), "total ordering" (L.196), "dense" (L.182; "dense in $\tilde{G}$" L.216; "dense subgroup" L.279).

**D3. Order topology, closure, neighbourhoods, convergence.** Def. 2.3 (entry 18); closure bars (entry 39); "fundamental system of neighborhoods" (L.438); "converges in $G$" (L.278), "converges to $x$" (L.310); "$\gamma_\alpha \rightarrow \gamma$ as $\alpha \rightarrow \ \kappa$" (L.479); "is a homeomorphism of $G$" (L.441); "Let $U \subseteq \tilde{G}$ be open such that $x \in U$" (L.311); "closed (in $G$)" (L.468).

**D4. Zorn's lemma / inductive orders.** L.444: "It is easy to check that $(Z, \leq)$ is inductive, so by Zorn's lemma there exists a maximal element $B$ of $Z$."

**D5. Ring theory.** "subring", "ideal", "generated by", "prime ideal", "quotient ring", "ring-homomorphism" (L.550), "free abelian monoid generated by" (L.607), "ordered semi-ring" (L.168), "ordered field" (L.29), "characteristic 0" (L.34). No choices fixed beyond "(not in $K$)" (C6).

**D6. Lexicographic order.** "$\mathbb{R}^2$ with the lexicographic order" (L.241); "is ordered lexicographically (hence well-ordered)" (L.795). The orders on $OR^{<\omega}$ and $D(OR^{<\omega})$ are **not** plain lexicographic — length-first for $OR^{<\omega}$, prefix-is-smaller for $D(OR^{<\omega})$ (entry 59).

**D7. Sup/inf, limsup-style construction.** L.309: "We put $y_\alpha := \ \sup\{x_\beta : \beta \geq \alpha\}$ for $\alpha < \theta$, and $x := \ \inf\{y_\alpha : \alpha < \theta\}$."

**D8. Interval and set-builder notation.** French intervals $]x,y[$, $]\mu,\gamma]$, $]\gamma-\varepsilon,\gamma]$. Set-builder uses both ":" and ";" ("$\{\gamma \in G : \gamma \leq 0\}$" L.32; "$\{z \in X; x < z \wedge z < y\}$" L.196; "$\{\, b \in K((G^{\leq 0})); \ \exists \gamma < 0$ …$\}$" L.372); "$\wedge$" for "and" once; "$\nexists$" once (L.481).

---

## Part E — How the paper talks: verbs, phrases, statement shapes

**E1. Introducing a definition.** Dominant verbs: "we put"/"We put" (22 occurrences in the file; e.g. "we put $b = c$ mod $(J)$ iff", L.376; "We put $y_\alpha := \ldots$", L.309; "We put 1) $X^0(b) = \overline{S_b}$", L.743), "denotes"/"We denote by" (L.116; L.421), "is called" (L.31; L.278), "by … we mean" (L.196; L.779), "we set" (L.560; L.1116), "Let … be such that" and ":=" (≈70 uses of ":="). Blocks headed "Notations:" / "Notation:" / "Convention:" / "Conventions:" (L.343, L.375, L.756; L.420, L.560; L.759).

**E2. Stating a result.** Hypotheses first, each in its own sentence, then "Then": "Let $G$ be a dense ordered group which is Cauchy-complete ( i.e. $G = G'$ ). Let $b,c \in K((G))$ and $\gamma \in G$ be given. Then …" (L.425). "Let $b,c \in K((G^{\leq 0}))$ be such that $b^L = c^L = 0$ and $v_0^p(b) \leq v_0^p(c)$, and let $k \in \mathbb{N}^*$. Then" (L.590). "Assume that … Then" (Lemma 5.10, L.806). "$\forall\, b,c \in K((G^{\leq 0}))$, a) … b) … c) …" (L.392). Quantifiers often trail: "$\ \forall \ b,c \in Re$" (L.547).

**E3. Proof connectives.** "Hence" (39 in file), "Whence" (12 — characteristic; e.g. L.306), "So" ("So we have to show that", L.1194; "So it suffices to prove", L.915), "Therefore" (L.945), "as was to be shown" (L.668, L.1123, L.1180), "This completes the proof of Proposition 3.4." (L.499), "This completes the proof of Proposition 5.20 and Theorem 5.1." (L.1181), "we are done" (L.914, L.1206), "a contradiction" / "a contradition" (sic, L.486), "By contradiction assume that" (L.479), "suppose by contradiction that" (L.319).

**E4. Claims of ease (pervasive).** "It is easily checked that" (L.144, L.461, L.476), "It is easily seen" (L.483), "It is easy to prove that" (L.242), "It is easy to check that" (L.444), "It is easy to see that" (L.789), "It is easy to show" (L.1226), "It is easy to find" (L.572), "is easily seen to be" (L.373), "trivially" ("we trivially get" L.539; "trivially implies" L.771, L.1209; "We trivially prove by induction" L.814; "We trivially have" L.1094), "Clearly" (L.224), "obviously" (L.1060), "Easy." (L.294), "Immediate from the definitions" (L.926, L.975), "Obviously" (L.951), "is obvious from the definitions" (L.927), "the inequality is obvious" (L.909, L.928).

**E5. Applying a construction / invoking a result.** "using the convolution formula we get" (L.652), "Using the convolution formula, we easily get" (L.586), "Using Corollary 3.9, we trivially get" (L.539), "Applying Proposition 3.4 to $b, c$ and taking supports on both sides, we get the result." (L.515), "Applying Corollary 5.16 (with $j = i$, $\delta = 0$, and $X =$ small final segment of $Y_b^i(c)^+$), we get" (L.1042), "By Lemma 3.2 we get" (L.663), "By Lemma 3.6 we can assume that" (L.482), "using Lemma 3.3 we obtain" (L.664), trailing "(see Lemmas 5.10 and 5.17)" (L.1023), "Coming back to the definitions we get the result." (L.847), "Coming back to $(B)$, in view of Lemma 3.2c the problem is to see whether" (L.410), "we get by induction" (L.1069, L.1075), "So by induction" (L.1016), "Multiplying … by $b$ (Berarducci's trick), and using Lemma 5.17, we get" (L.1171), "Putting $(+), (++), (+++)$ together, we get" (L.1077), "Putting (A), (B) and (C) together, we get" (L.1104).

**E6. Reductions and "it suffices".** "We first remark that it is sufficient to prove Theorem 4.3 for $G$ Cauchy-complete" (L.549), "we can assume that $G$ is Cauchy-complete" (L.639), "It suffices to consider the point $\gamma = 0$, because the map $\gamma_1 \mapsto \ \gamma_1 + \gamma$ is a homeomorphism of $G$." (L.441), "it is sufficient (and necessary) to show that" (L.1229), "it is enough to show that $v_\gamma(bc)$ is big for many $\gamma \in \tilde{G}^{<0}$ (see Lemma 3.3)" (L.643), "So it is sufficient to prove that $s_b(b^kc) \geq s_b(c) \odot s(b)^k$." (L.990), "We can assume that $v_0(c) \geq 1$ and $v_0(d) \geq 1$. [ Otherwise the inequality is obvious ]." (L.909), "it suffices to show that $v_0(E_l) < \omega^{\omega^\alpha t}$" (L.1094).

**E7. Describing the value map in words.** "$v_0(b)$ is the order type of a small final segment of the support of $b$" (L.62); "$v_0$ induces an "ordinal valuation"" (L.63); "$v_0(bc)$ is big (i.e. close to $v_0(b) \odot v_0(c)$)" (L.643); "if $v_\gamma(bc)$ is big for many $\gamma$, so is $v_0(bc)$" (L.417); "estimate $v_\gamma(bc)$ as precisely as possible" (L.418); "a term of value $v_\gamma < \ldots$" (L.592, L.1238, L.1249); "$b \notin J$ iff $v_0(b) \geq 1$" (L.1194); "compute the "truncations" mod $(J)$ of a product $bc$" (L.88); "an estimation for the truncated product $(bc)_{|\gamma}$" (L.1230); "Computation of $s_b(b^kc^{|\gamma})$" (L.1013) / "Estimation of $s_b(kb^{|\gamma}b^{k-1}c)$" (L.1021).

**E8. "mod (J)" phrasing.** A trailing qualifier on an equation: "$\ldots \text{ mod } (J)$" in displays (L.427, L.495, L.509, L.654, L.806), "mod $(J)$" inline (L.88, L.376, L.377, L.806, L.814), "$\bmod (J)$" (L.964, L.966, L.970, L.973, L.993, L.994); inclusion "$\subseteq \ldots \bmod (J)$" (L.966). Never "$\equiv$", never "modulo $J$" in words, never "in $K((G^{\le 0}))/J$" for congruence.

**E9. "Recall"/"Observe"/"Precisely".** "Recall (see 3.3) that" (L.551), "[ Recall that …]" (L.537, L.703), "We now recall" (L.124), "we recall the multiplicative property when $G = (\mathbb{R},+)$" (L.380). "Observe that:" (L.410), "[ Observe that if …]" (L.539), "Observe that $(*)$ trivially implies Theorem 5.1" (L.771). "Precisely:" / "More precisely" as cue that a formal statement follows (L.503, L.572, L.624). "We precise this below:" (L.275, Gallicism).

**E10. Hedged / informal register.** Scare quotes for informal words: "real" series (L.70), "ordinal valuation" (L.63), "truncations" (L.88, L.384), "big points" (L.552), ""less" big points" (L.685), ""big points of $c$ relatively to $b$"" (L.691), "complexity" (L.775). "Let us say (informally) that" (L.684). "$\approx$" (L.687). "a bit complicated" (L.532), "which is the most difficult result of this paper" (L.75), "the general case is much more difficult because" (L.678), "So it is not clear that there exists" (L.682), "To overcome this difficulty we will consider an appropriate subset" (L.1054), "The idea here is to compute" (L.1047), "The idea is to try to compute" (L.552), "The main idea of the proof is to look at the set of big points of a series very closely" (L.685), "We are going to compute" (L.1007), "we are led to" (L.418, L.606), "we will be led to" (L.689).

**E11. Section-opening signposts.** "We begin with some basic definitions." (L.22); "We first give some basic definitions." (L.338); "All results of this § are well-known" (L.115); "All results of this § are known or easy, so we skip most of the proofs." (L.178); "The purpose in this § is to show that" (L.531); "All this section will be concerned with the proof of Theorem 5.1." (L.638); "We mention here without proof that" (L.1216). "§" is used as a noun ("this §").

**E12. Case analysis.** "We have to consider two cases." (L.1004, L.1154); "**Case 1:** $\gamma_i > 1$" (L.1006) / "**Case 2:** $\gamma_i = 1$" (L.1046); "a) … b) …" inside cases; "• $j = k$ :" / "• $j \to j - 1$ :" for induction steps (L.940, L.942); "by $\searrow$ induction on $j \leq k$" (L.939, downward arrow for descending induction — [UNVERIFIED symbol]).

**E13. Talking about $G$ and $\tilde G$.** "$G$ is dense in $\tilde{G}$" (L.216); "$\tilde{G}$ contains the Cauchy-completion of $G$ as subgroup" (L.275); "$G$ and $G'$ have the same order-completion $\tilde{G}$" (L.332); "which naturally extends" (L.183); "canonical inclusion" (L.208, L.269); "The canonical embedding $i : G \rightarrow G'$ induces a ring-homomorphism … which commutes with $v_0$" (L.550); "of cofinality $\omega$" (L.434, L.1226); "explicit description of $\widetilde{\mathbb{R}^\alpha}$" (L.1226).

**E14. Talking about the ring and its elements.** "the ring $K((G^{\leq 0}))$" (L.43); "the subring $Re \subseteq K((G^{\leq 0}))$" (L.70); "the quotient ring $K((G^{\leq 0}))/J$" (abstract), "the quotient ring $Re/J$" (L.616); "$J$ is prime" / "$J$ is a prime ideal" / "is prime in $Re$"; emphatic "does have irreducible elements" / "does have prime elements" (L.43; L.111); "each element … admits at least one factorization into irreducibles"; "series" for elements; "the product $bc$", "the product $b_{|\gamma} b^{k-1} c^2$" (L.606); "The coefficient of $x^\delta$ in $(bc)_{|\gamma}$ is a finite sum of the form $\sum_{\beta' + \xi' = \delta} b_{\beta'} c_{\xi'}$" (L.498).

---

## Part F — Where the paper says it disagrees with, corrects, or departs from another paper

**F1. Answers [B]'s question on primality of $J$ affirmatively (extension, not correction).** L.44: "He asks whether $J$ is prime for all $G$. We prove that this is the case (see §6)".

**F2. Answers [B]'s question on the multiplicative property negatively.** L.65: "It is asked in [B] whether the multiplicative property holds for any $G$. We show that this is not the case (see §7):" followed by Theorem 0.4 (L.68). §7: "We mention here without proof that $(B)$ may fail for many groups $G$." (L.1216).

**F3. Replaces the multiplicative property by a weaker lower bound.** L.75: "In order to show our main theorem (i.e. $J$ is prime for all $G$), we use a weakening of the multiplicative property given by a lower bound of $v_0(bc)$, which is the most difficult result of this paper (see §5):".

**F4. Extends [B]'s convolution formula beyond $\mathbb{R}$, and says why [B]'s proof does not suffice.** L.89: "The convolution formula was proved in [B] only for $G = (\mathbb{R},+)$ and it is here extended to any Cauchy-complete group." L.434: "The proof is almost the same as those given in [B] when $G = (\mathbb{R},+)$. However, it may happen that $G$ is not of cofinality $\omega$ (e.g. $G = \mathbb{R}^{\omega_1}$ with the lexicographic order), which requires some additional lemmas."

**F5. Generalises the setting of the completion beyond groups.** L.185: "The definition of $\tilde{G}$ doesn't require $G$ to be a dense ordered group, but only $G$ to be a dense ordered semi-group with left-continuous addition. So we will consider this more general setting."

**F6. Restricts [B]'s multiplicative property to the subring $Re$.** L.70: "However we are able to prove that the multiplicative property holds on the subring $Re \subseteq K((G^{\leq 0}))$ of "real" series (see §4):". L.539: "[ Observe that if $G = (\mathbb{R},+)$, then $Re = K((\mathbb{R}^{\leq 0}))$]".

**F7. Partial answer to [B]'s factoriality question.** L.92: "Another question asked in [B] is whether $K((G^{\leq 0}))/J$ is a factorial domain. As another application of our lower bound, we are able to show (see §6):" followed by Theorem 0.7 (existence of factorizations only; uniqueness not claimed).

**F8. Declares independence from [Pi2].** L.111: "The results of this paper and [Pi2] are independent."

No passage was found in which the paper rejects or renames another paper's terminology or notation; every inherited symbol ($J$, $v_0$, $\odot$, $K((G))$, $K((G^{\le 0}))$) is kept unchanged.

---

## Closing note on the source

- Transcription only; no PDF in the library. Items flagged [UNVERIFIED]/[GARBLED?]: entry 9 ("o.t" vs "ot"), entry 16 (dense-group definition's quantifier), entry 35 ("$Re/J$" vs "$Re/J'$"), entry 47 (typeface of $Re$), entry 55 ("$\varepsilon \in G^{<0}$" with "$\gamma - \varepsilon$"; bold vs roman "Big"), entry 57 ("$X_0(b)$"), entry 67 (stray "$k \in \mathbb{N}^*$" in Prop. 7.2), entry 68 (tag placement), E12 ("$\searrow$"), B4 (citation keys [Re1]/[Re2] vs [R1]/[R2]). Typos reproduced verbatim from the transcription: "exacly" (L.774), "contradition" (L.486), "beeing be able" (L.797), "Kaplanski" (L.1286), "Lectures Notes" (L.1299), "Integers parts" (L.1305), "proves by induction" (L.698).
- The transcriber's figure descriptions (L.247, L.313, L.366, L.582) are not the paper's text and were not used as testimony.
- Line numbers in this record were produced mechanically by matching each quoted phrase against the transcription file; a range "L.a–L.b" means the quote spans those lines.

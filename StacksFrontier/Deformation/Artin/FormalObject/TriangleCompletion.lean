module

public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveSystem
public import StacksFrontier.RingTheory.AdicCompletion.MaximalIdealsOfCompletion
public import StacksFrontier.RingTheory.Ideal.IsDomainOfLocalizationMaximal
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing

/-!
# The limit of the thickenings of the triangle

Let `K` be a field and `f = xy(x + y - 1) ∈ K[x, y]`. The inverse system of thickenings
`K[x, y] ⧸ (f) ^ (n + 1)` of the triangle of three lines (`Deformation.Artin.powQuotientDiagram`)
has limit the `f`-adic completion `R = K[x, y]^∧` of the polynomial ring, and this ring is a two
dimensional regular Noetherian domain. These are the properties of the limit used in the
discussion before Stacks 0CXX, where the first cohomology of an abelian variety over `Spec R` is
shown to be torsion by Stacks 0AF9 and 0AFA.

The maximal ideals of `R` are `𝔪R` for the maximal ideals `𝔪 ∋ f` of `K[x, y]`, and the local
rings there have the same completions as the local rings of `K[x, y]`, which are regular of
dimension two (Stacks 00OQ); so `R` is regular of dimension two by Stacks 07NY and 07NV. It is a
domain because it is locally a domain and has no idempotents besides `0` and `1`: idempotents of
`R` are detected in `K[x, y] ⧸ (f)`, and there the three lines `x = 0`, `y = 0`, `x + y = 1` meet
pairwise, so an idempotent vanishing on one of them vanishes on all, hence is nilpotent.

## Main definitions

* `Deformation.Artin.adicCompletionCone`: the cone over `powQuotientDiagram k I` with vertex
  `AdicCompletion I A`.
* `Deformation.Artin.triangleCompletion`: the `f`-adic completion of `K[x, y]`.

## Main results

* `Deformation.Artin.isLimitAdicCompletionCone`: **the adic completion is the limit of the
  system of powers**, in `k`-algebras.
* `Deformation.Artin.eq_zero_or_eq_one_of_isIdempotentElem_triangle`: the triangle
  `K[x, y] ⧸ (f)` is connected.
* `Deformation.Artin.isRegularRing_triangleCompletion`,
  `Deformation.Artin.ringKrullDim_triangleCompletion`,
  `Deformation.Artin.isDomain_triangleCompletion`: `R` is a regular domain of dimension two.

## References

* [Stacks Project, Tag 0CXX](https://stacks.math.columbia.edu/tag/0CXX)
* [Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)
* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial

universe u

namespace Deformation.Artin

section Limit

variable {A : Type u} [CommRing A] (k : Type u) [CommRing k] [Algebra k A] (I : Ideal A)

/-- The cone over the system of powers `n ↦ A ⧸ I ^ (n + 1)` with vertex the adic completion,
whose leg at `n` is evaluation at level `n + 1`. -/
def adicCompletionCone : Cone (powQuotientDiagram k I) where
  pt := CommAlgCat.of k (AdicCompletion I A)
  π :=
    { app n := CommAlgCat.ofHom ((AdicCompletion.evalₐ I (n.unop + 1)).restrictScalars k)
      naturality m n g := by
        apply CommAlgCat.hom_ext
        ext x
        exact (AdicCompletion.factor_evalₐ I
          (Nat.succ_le_succ (leOfHom g.unop)) x).symm }

/-- The leg of `adicCompletionCone` at `n`, on an element. -/
theorem adicCompletionCone_π_app (n : ℕᵒᵖ) (x : AdicCompletion I A) :
    ((adicCompletionCone k I).π.app n).hom x = AdicCompletion.evalₐ I (n.unop + 1) x :=
  rfl

/-- The level-`0` quotient `A ⧸ I ^ 0` is the zero ring. -/
theorem subsingleton_quotient_pow_zero : Subsingleton (A ⧸ I ^ 0) :=
  Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])

/-- Two quotient maps between quotients of `A` compose to the quotient map. -/
theorem factorₐ_factorₐ_apply {J₁ J₂ J₃ : Ideal A} (h₁ : J₁ ≤ J₂) (h₂ : J₂ ≤ J₃) (y : A ⧸ J₁) :
    Ideal.Quotient.factorₐ k h₂ (Ideal.Quotient.factorₐ k h₁ y) =
      Ideal.Quotient.factorₐ k (h₁.trans h₂) y := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

/-- The components `s.pt → A ⧸ I ^ (n + 1) → A ⧸ I ^ n` of a cone over the system of powers
are compatible with the quotient maps. -/
theorem factorₐ_comp_coneLegs (s : Cone (powQuotientDiagram k I)) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hle)).comp
        ((Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
          (s.π.app (op n)).hom) =
      (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (Nat.le_succ m))).comp
        (s.π.app (op m)).hom := by
  ext x
  rw [← s.w (homOfLE hle).op]
  simp only [AlgHom.comp_apply, CommAlgCat.hom_comp, powQuotientDiagram,
    CommAlgCat.hom_ofHom]
  rw [factorₐ_factorₐ_apply, factorₐ_factorₐ_apply]

/-- The map from the vertex of a cone over the system of powers to the adic completion: its
component at level `n` is the leg at `n` followed by `A ⧸ I ^ (n + 1) → A ⧸ I ^ n`. -/
def adicCompletionConeLift (s : Cone (powQuotientDiagram k I)) : s.pt →ₐ[k] AdicCompletion I A :=
  AdicCompletion.liftAlgHom I
    (fun n => (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
      (s.π.app (op n)).hom)
    (fun hle => factorₐ_comp_coneLegs k I s hle)

/-- The level-`n + 1` component of `adicCompletionConeLift` is the leg of the cone at `n`. -/
theorem evalₐ_adicCompletionConeLift (s : Cone (powQuotientDiagram k I)) (n : ℕ) (x : s.pt) :
    AdicCompletion.evalₐ I (n + 1) (adicCompletionConeLift k I s x) = (s.π.app (op n)).hom x := by
  rw [adicCompletionConeLift, AdicCompletion.evalₐ_liftAlgHom I _
    (fun hle => factorₐ_comp_coneLegs k I s hle), ← s.w (homOfLE (Nat.le_succ n)).op]
  rfl

/-- **The adic completion is the limit of the system of powers** `n ↦ A ⧸ I ^ (n + 1)`, as a
`k`-algebra. -/
def isLimitAdicCompletionCone : IsLimit (adicCompletionCone k I) where
  lift s := CommAlgCat.ofHom (adicCompletionConeLift k I s)
  fac s n := by
    obtain ⟨n⟩ := n
    apply CommAlgCat.hom_ext
    ext x
    exact evalₐ_adicCompletionConeLift k I s n x
  uniq s g hg := by
    apply CommAlgCat.hom_ext
    ext x
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
      have := subsingleton_quotient_pow_zero I
      exact Subsingleton.elim _ _
    | succ n =>
      exact (congrArg (fun φ => φ.hom x) (hg (op n))).trans
        (evalₐ_adicCompletionConeLift k I s n x).symm

end Limit

section Triangle

variable (K : Type u) [Field K]

/-- An element of a principal ideal vanishes at every point where the generator does. -/
theorem eval_eq_zero_of_mem_span_singleton {p g : MvPolynomial (Fin 2) K} (v : Fin 2 → K)
    (hp : eval v p = 0) (hg : g ∈ Ideal.span {p}) : eval v g = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hg
  simp [hp]

/-- The affine change of coordinates `x ↦ x + y - 1`, `y ↦ y` of `K[x, y]`. -/
def triangleShear : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (aeval ![X 0 + X 1 - 1, X 1]) (aeval ![X 0 - X 1 + 1, X 1])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · simp
        ring
      · simp)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · simp
        ring
      · simp)

/-- The three lines of the triangle are prime ideals of `K[x, y]`. -/
theorem isPrime_span_triangleLines :
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) K)}).IsPrime ∧
      (Ideal.span {(X 1 : MvPolynomial (Fin 2) K)}).IsPrime ∧
      (Ideal.span {(X 0 + X 1 - 1 : MvPolynomial (Fin 2) K)}).IsPrime := by
  have hX : ∀ i : Fin 2, Prime (X i : MvPolynomial (Fin 2) K) := fun _ => MvPolynomial.X_prime
  have h3 : Prime (X 0 + X 1 - 1 : MvPolynomial (Fin 2) K) := by
    have := (MulEquiv.prime_iff (triangleShear K).toMulEquiv (p := X 0)).2 (hX 0)
    simpa [triangleShear] using this
  exact ⟨(Ideal.span_singleton_prime (hX 0).ne_zero).2 (hX 0),
    (Ideal.span_singleton_prime (hX 1).ne_zero).2 (hX 1),
    (Ideal.span_singleton_prime h3.ne_zero).2 h3⟩

/-- A lift of an idempotent of `K[x, y] ⧸ (f)` lies, on each line, in its ideal or differs from
`1` by an element of it. -/
theorem mem_or_one_sub_mem_of_isIdempotentElem {g p : MvPolynomial (Fin 2) K}
    (he : IsIdempotentElem (Ideal.Quotient.mk (triangleIdeal K) g))
    (hp : (Ideal.span {p}).IsPrime) (hf : trianglePolynomial K ∈ Ideal.span {p}) :
    g ∈ Ideal.span {p} ∨ 1 - g ∈ Ideal.span {p} := by
  refine hp.mem_or_mem ((Ideal.span_singleton_le_iff_mem _).2 hf ?_)
  refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [map_mul, map_sub, map_one, mul_sub, mul_one]
  exact sub_eq_zero.2 he.eq.symm

/-- An idempotent of `K[x, y] ⧸ (f)` vanishing on the three lines is zero: every prime of the
quotient contains one of the lines, so the idempotent is nilpotent. -/
theorem eq_zero_of_isIdempotentElem_of_mem_triangleLines {g : MvPolynomial (Fin 2) K}
    (he : IsIdempotentElem (Ideal.Quotient.mk (triangleIdeal K) g))
    (h1 : g ∈ Ideal.span {X 0}) (h2 : g ∈ Ideal.span {X 1})
    (h3 : g ∈ Ideal.span {X 0 + X 1 - 1}) :
    Ideal.Quotient.mk (triangleIdeal K) g = 0 := by
  refine he.eq_zero_of_isNilpotent ?_
  rw [← mem_nilradical, nilradical_eq_sInf]
  refine Submodule.mem_sInf.2 fun (q : Ideal (MvPolynomial (Fin 2) K ⧸ triangleIdeal K)) hq => ?_
  have hq : q.IsPrime := hq
  have hQ : (q.comap (Ideal.Quotient.mk (triangleIdeal K))).IsPrime := Ideal.comap_isPrime _ _
  have hfq : trianglePolynomial K ∈ q.comap (Ideal.Quotient.mk (triangleIdeal K)) := by
    have h0 : Ideal.Quotient.mk (triangleIdeal K) (trianglePolynomial K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [Ideal.mem_comap, h0]
    exact q.zero_mem
  rw [trianglePolynomial] at hfq
  have key : ∀ p : MvPolynomial (Fin 2) K, g ∈ Ideal.span {p} →
      p ∈ q.comap (Ideal.Quotient.mk (triangleIdeal K)) →
      Ideal.Quotient.mk (triangleIdeal K) g ∈ q := fun p hg hp =>
    (Ideal.span_singleton_le_iff_mem _).2 hp hg
  rcases hQ.mem_or_mem hfq with h12 | h
  · rcases hQ.mem_or_mem h12 with h | h
    · exact key _ h1 h
    · exact key _ h2 h
  · exact key _ h3 h

/-- An idempotent of `K[x, y] ⧸ (f)` vanishing on the line `x = 0` is zero: it cannot be `1` on
`y = 0` or on `x + y = 1`, which meet `x = 0` at `(0, 0)` and `(0, 1)`. -/
theorem eq_zero_of_isIdempotentElem_of_mem_span_X_zero {g : MvPolynomial (Fin 2) K}
    (he : IsIdempotentElem (Ideal.Quotient.mk (triangleIdeal K) g))
    (h1 : g ∈ Ideal.span {X 0}) : Ideal.Quotient.mk (triangleIdeal K) g = 0 := by
  obtain ⟨-, hP2, hP3⟩ := isPrime_span_triangleLines K
  have hf2 : trianglePolynomial K ∈ Ideal.span {(X 1 : MvPolynomial (Fin 2) K)} :=
    Ideal.mem_span_singleton.2 ⟨X 0 * (X 0 + X 1 - 1), by rw [trianglePolynomial]; ring⟩
  have hf3 : trianglePolynomial K ∈ Ideal.span {(X 0 + X 1 - 1 : MvPolynomial (Fin 2) K)} :=
    Ideal.mem_span_singleton.2 ⟨X 0 * X 1, by rw [trianglePolynomial]; ring⟩
  refine eq_zero_of_isIdempotentElem_of_mem_triangleLines K he h1 ?_ ?_
  · rcases mem_or_one_sub_mem_of_isIdempotentElem K he hP2 hf2 with h | h
    · exact h
    · have ha := eval_eq_zero_of_mem_span_singleton K ![0, 0] (by simp) h1
      have hb := eval_eq_zero_of_mem_span_singleton K ![0, 0] (by simp) h
      rw [map_sub, map_one, ha, sub_zero] at hb
      exact absurd hb one_ne_zero
  · rcases mem_or_one_sub_mem_of_isIdempotentElem K he hP3 hf3 with h | h
    · exact h
    · have ha := eval_eq_zero_of_mem_span_singleton K ![0, 1] (by simp) h1
      have hb := eval_eq_zero_of_mem_span_singleton K ![0, 1] (by simp) h
      rw [map_sub, map_one, ha, sub_zero] at hb
      exact absurd hb one_ne_zero

/-- **The triangle is connected**: `0` and `1` are the only idempotents of
`K[x, y] ⧸ (xy(x + y - 1))`. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem_triangle
    (e : MvPolynomial (Fin 2) K ⧸ triangleIdeal K) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective e
  obtain ⟨hP1, -, -⟩ := isPrime_span_triangleLines K
  have hf1 : trianglePolynomial K ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) K)} :=
    Ideal.mem_span_singleton.2 ⟨X 1 * (X 0 + X 1 - 1), by rw [trianglePolynomial]; ring⟩
  rcases mem_or_one_sub_mem_of_isIdempotentElem K he hP1 hf1 with h | h
  · exact Or.inl (eq_zero_of_isIdempotentElem_of_mem_span_X_zero K he h)
  · have he' : IsIdempotentElem (Ideal.Quotient.mk (triangleIdeal K) (1 - g)) := by
      rw [map_sub, map_one]
      exact he.one_sub
    have := eq_zero_of_isIdempotentElem_of_mem_span_X_zero K he' h
    rw [map_sub, map_one, sub_eq_zero] at this
    exact Or.inr this.symm

/-- The localizations of `K[x, y]` at its maximal ideals are regular local rings of dimension
two (Stacks 00OQ). -/
theorem isRegularLocalRing_localization_mvPolynomial (m : Ideal (MvPolynomial (Fin 2) K))
    [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) ∧
      ringKrullDim (Localization.AtPrime m) = 2 := by
  obtain ⟨h1, h2⟩ :=
    (MvPolynomial.isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization
      K (Fin 2)).2.2 m (Localization.AtPrime m)
  exact ⟨h1, by rw [h2]; simp⟩

/-- The `xy(x + y - 1)`-adic completion of `K[x, y]`, the limit of the thickenings of the
triangle (`Deformation.Artin.isLimitAdicCompletionCone`). -/
abbrev triangleCompletion : Type u :=
  AdicCompletion (triangleIdeal K) (MvPolynomial (Fin 2) K)

/-- **The completion of `K[x, y]` along the triangle is a regular ring.** -/
instance isRegularRing_triangleCompletion : IsRegularRing (triangleCompletion K) :=
  AdicCompletion.isRegularRing_of_isRegularLocalRing _ fun m _ _ =>
    (isRegularLocalRing_localization_mvPolynomial K m).1

/-- **The completion of `K[x, y]` along the triangle has dimension two.** -/
theorem ringKrullDim_triangleCompletion : ringKrullDim (triangleCompletion K) = 2 := by
  have := AdicCompletion.ringKrullDim_eq_of_ringKrullDim_localization (triangleIdeal K)
    (triangleIdeal_ne_top K) 2 fun m _ _ => by
      rw [(isRegularLocalRing_localization_mvPolynomial K m).2]
      rfl
  exact this

/-- **The completion of `K[x, y]` along the triangle is a domain**: it is locally a regular local
ring, hence locally a domain, and connected because the triangle is. -/
instance isDomain_triangleCompletion : IsDomain (triangleCompletion K) := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ (triangleIdeal_ne_top K)
  have hM := AdicCompletion.map_isMaximal (triangleIdeal K) m hIm
  have : Nontrivial (triangleCompletion K) :=
    nontrivial_of_ne 0 1 fun h => hM.ne_top ((Ideal.eq_top_iff_one _).2 (h ▸ Ideal.zero_mem _))
  refine Ideal.isDomain_of_isDomain_localization_of_isIdempotentElem (fun M _ => ?_)
    (AdicCompletion.eq_zero_or_eq_one_of_isIdempotentElem _
      (eq_zero_or_eq_one_of_isIdempotentElem_triangle K))
  have := IsRegularRing.isRegularLocalRing_localization (R := triangleCompletion K) M
  exact IsRegularLocalRing.isDomain _

end Triangle

end Deformation.Artin

end

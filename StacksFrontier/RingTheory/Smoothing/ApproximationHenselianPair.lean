module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Etale.LiftSmoothMap
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Smoothing.ProductOfFilteredColimits

/-!
# Approximation of solutions over a Noetherian henselian pair

Let `(A, I)` be a henselian pair with `A` Noetherian and let `A^∧` be the `I`-adic completion of
`A`. A system of polynomial equations over `A` which has a solution in `A^∧` has, for every
`N ≥ 1`, a solution in `A` congruent to the given one modulo `I ^ N`.

The source deduces this from Popescu's theorem (Tag 07GC), which is used only to present
`A → A^∧` as a filtered colimit of smooth ring maps; that presentation is carried here as the
hypothesis `Stacks.Smoothing.IsIndSmoothAdicCompletion`, because 07GC is proved downstream of
this file. Each of the source's three alternative hypotheses — that `A → A^∧` is regular, that
`A` is a Noetherian G-ring, or that `(A, I)` is the henselization of a pair over a Noetherian
G-ring — yields it through 07GC, the last two by way of Lemmas 0AH3
(`isGRing_henselization`) and 0AH2 (`isRegularRingHom_algebraMap_adicCompletion`). That is done
in `StacksFrontier/RingTheory/Smoothing/ApproximationHenselianGRing.lean`, which states the lemma
once under each of them.

## Main definitions

* `Stacks.Smoothing.IsIndSmoothAdicCompletion`: the `I`-adic completion of `A` is a filtered
  colimit of smooth `A`-algebras.

## Main results

* `Stacks.Smoothing.exists_smooth_factorization_of_isIndSmoothAdicCompletion`: an ind-smooth
  completion factors every map into it from a finitely presented `A`-algebra through a smooth one.
* `Stacks.Smoothing.isIndSmoothAdicCompletion_of_isAdicComplete`: an `I`-adically complete ring
  has ind-smooth completion.
* `Stacks.Smoothing.exists_solution_of_henselianPair`: Lemma 0AH5, with the hypothesis above in
  place of its appeal to 07GC. The statements registered for Tag 0AH5, one for each of the
  source's three alternative hypotheses, are in
  `StacksFrontier/RingTheory/Smoothing/ApproximationHenselianGRing.lean`.

## Implementation notes

"`A^∧` is a filtered colimit of smooth `A`-algebras" is spelled as
`CategoryTheory.ObjectProperty.ind.{u}` of `UnderSmooth (CommRingCat.of A)` on the category
`Under (CommRingCat.of A)`, the spelling already used by Lemma 0BJ7
(`Stacks.Smoothing.ind_underSmooth_of_ramificationIdx_one`) and by the left-hand side of Lemma
07C3 (`CommRingCat.ind_under_iff_exists_factorization`), which is the only way the hypothesis is
consumed.

The system of equations is a family `f : Fin m → MvPolynomial (Fin n) A`, and the finitely
presented algebra fed to the factorization criterion is its universal solution algebra
`MvPolynomial (Fin n) A ⧸ (f)`; this is what makes the relations `f j = 0` hold in the smooth
algebra `B`, which they need not do if the polynomial ring is used instead, since the map
`B → A^∧` is not assumed injective.

The congruence `\hat a_i - a_i ∈ I ^ N` of the source is read in `A^∧`, where the ideal meant is
the extension of `I ^ N`; `a i` is pushed into `A^∧` along its algebra map. What the argument
produces directly is the weaker statement that the difference dies in `A ⧸ I ^ N`, and
`mem_map_pow_of_evalₐ_eq_zero` upgrades it using that `I` is finitely generated — the one place
where `A` being Noetherian is used.

The instance of `IsIndSmoothAdicCompletion` available already in this file is the degenerate one
in which `A → A^∧` is an isomorphism, by
`Stacks.Smoothing.isIndSmoothAdicCompletion_of_isAdicComplete`. The ones with content are those
07GC supplies, and they are supplied downstream: see
`Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing`.

## References

* [Stacks Project, Tag 0AH5](https://stacks.math.columbia.edu/tag/0AH5)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Smoothing

/-- The `I`-adic completion of `A` is a filtered colimit of smooth `A`-algebras: the conclusion of
Popescu's theorem (Tag 07GC) for the completion map of `A` at `I`. -/
public def IsIndSmoothAdicCompletion (A : Type u) [CommRing A] (I : Ideal A) : Prop :=
  ObjectProperty.ind.{u} (UnderSmooth (CommRingCat.of A))
    (Under.mk (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))))

/-- A smooth algebra is of finite presentation, which is what the factorization criterion of
Lemma 07C3 requires of the family it is applied to. -/
private theorem underSmooth_le_finitePresentation {A : Type u} [CommRing A] :
    (UnderSmooth (CommRingCat.of A) : ObjectProperty (Under (CommRingCat.of A))) ≤
      fun X : Under (CommRingCat.of A) => X.hom.hom.FinitePresentation := by
  intro X hX
  let : Algebra A X.right := X.hom.hom.toAlgebra
  change Algebra.Smooth A X.right at hX
  change Algebra.FinitePresentation A X.right
  exact hX.finitePresentation

/-- Every map to an ind-smooth `I`-adic completion from a finitely presented `A`-algebra factors
through a smooth `A`-algebra. -/
public theorem exists_smooth_factorization_of_isIndSmoothAdicCompletion
    {A : Type u} [CommRing A] {I : Ideal A} (h : IsIndSmoothAdicCompletion A I)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FinitePresentation A C]
    (ψ : C →ₐ[A] AdicCompletion I A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Smooth A B ∧
      ∃ (p : C →ₐ[A] B) (q : B →ₐ[A] AdicCompletion I A), q.comp p = ψ := by
  obtain ⟨E, g, hq, hgq, hEsm⟩ :=
    (CommRingCat.ind_under_iff_exists_factorization _ underSmooth_le_finitePresentation).1 h
      (Under.mk (CommRingCat.ofHom (algebraMap A C)))
      (show (algebraMap A C).FinitePresentation from
        RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by ext x; exact ψ.commutes x))
  let : Algebra A E.right := E.hom.hom.toAlgebra
  refine ⟨E.right, inferInstance, inferInstance, hEsm,
    ⟨g.right.hom, fun x => congr($(Under.w g).hom x)⟩,
    ⟨hq.right.hom, fun x => congr($(Under.w hq).hom x)⟩, ?_⟩
  refine AlgHom.ext fun x => ?_
  exact congr($(congrArg Under.Hom.right hgq).hom x)

/-- An `I`-adically complete ring has ind-smooth `I`-adic completion, the completion map being an
isomorphism onto a ring smooth over `A`. -/
public theorem isIndSmoothAdicCompletion_of_isAdicComplete {A : Type u} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] : IsIndSmoothAdicCompletion A I := by
  have hbij : Function.Bijective (algebraMap A (AdicCompletion I A)) :=
    AdicCompletion.of_bijective_iff.2 ‹IsAdicComplete I A›
  have e : A ≃ₐ[A] AdicCompletion I A := AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  refine ObjectProperty.le_ind _ _ ?_
  dsimp [UnderSmooth]
  exact Algebra.Smooth.of_equiv e

/-- An element of the `I`-adic completion killed by the projection to `A ⧸ I ^ n` lies in the
extension of `I ^ n`, provided `I` is finitely generated. -/
private theorem mem_map_pow_of_evalₐ_eq_zero {A : Type u} [CommRing A] {I : Ideal A} (hI : I.FG)
    {n : ℕ} {x : AdicCompletion I A} (hx : AdicCompletion.evalₐ I n x = 0) :
    x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  have h1 : AdicCompletion.eval I A n x = 0 := by
    have h := AdicCompletion.factor_evalₐ_eq_eval (I := I) (n := n) x (by simp)
    rw [hx, map_zero] at h
    exact h.symm
  have h2 : x ∈ (I ^ n) • (⊤ : Submodule A (AdicCompletion I A)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact h1
  rw [Ideal.smul_top_eq_map] at h2
  exact h2

/-- **Stacks 0AH5 (approximation for henselian pairs).** Let `(A, I)` be a henselian pair with `A`
Noetherian whose `I`-adic completion is a filtered colimit of smooth `A`-algebras. A system of
polynomial equations over `A` with a solution in the completion has, for every `N ≥ 1`, a solution
in `A` congruent to it modulo `I ^ N`.

This is the engine of the lemma: the hypothesis `hind` stands for the source's appeal to
Popescu's Theorem 07GC, which is proved — but only downstream of this file, so the lemma itself
is stated in `StacksFrontier/RingTheory/Smoothing/ApproximationHenselianGRing.lean`, once under
each of the source's three alternative hypotheses, and those three statements are what carry Tag
0AH5. This one is left public and untagged because
`Stacks.Smoothing.exists_etale_neighbourhood_algHom_approximation`
(`StacksFrontier/RingTheory/Smoothing/ApproximationOfCompletionMaps.lean`) and
`Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth'`
(`StacksFrontier/RingTheory/Rig/Algebraization/RigSmoothAlgebraizationOfGRing.lean`) consume it with
a presentation of their own, so it cannot be made `private`. -/
public theorem exists_solution_of_henselianPair
    {A : Type u} [CommRing A] {I : Ideal A} [IsNoetherianRing A]
    (hAI : HenselianPair A I) (hind : IsIndSmoothAdicCompletion A I)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (â : Fin n → AdicCompletion I A) (hâ : ∀ j, MvPolynomial.aeval â (f j) = 0)
    {N : ℕ} (hN : N ≠ 0) :
    ∃ a : Fin n → A,
      (∀ i, â i - algebraMap A (AdicCompletion I A) (a i) ∈
        (I ^ N).map (algebraMap A (AdicCompletion I A))) ∧
      ∀ j, MvPolynomial.aeval a (f j) = 0 := by
  classical
  -- The universal solution algebra `C = A[x]/(f)`, finitely presented over `A`.
  set J : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range f) with hJdef
  have hJfg : J.FG := Submodule.fg_span (Set.finite_range f)
  have : Algebra.FinitePresentation A (MvPolynomial (Fin n) A ⧸ J) :=
    Algebra.FinitePresentation.quotient hJfg
  have hJle : ∀ x ∈ J, MvPolynomial.aeval â x = 0 := by
    intro x hx
    have : J ≤ RingHom.ker (MvPolynomial.aeval â : MvPolynomial (Fin n) A →ₐ[A] _) := by
      rw [hJdef, Ideal.span_le]
      rintro y ⟨j, rfl⟩
      simpa using hâ j
    simpa using this hx
  set ψ : (MvPolynomial (Fin n) A ⧸ J) →ₐ[A] AdicCompletion I A :=
    Ideal.Quotient.liftₐ J (MvPolynomial.aeval â) hJle with hψdef
  -- Popescu's input: factor `ψ` through a smooth `A`-algebra `B`.
  obtain ⟨B, _, _, hBsm, p, q, hpq⟩ :=
    exists_smooth_factorization_of_isIndSmoothAdicCompletion hind _ ψ
  have : Algebra.Smooth A B := hBsm
  set π : MvPolynomial (Fin n) A →ₐ[A] B := p.comp (Ideal.Quotient.mkₐ A J) with hπdef
  set b : Fin n → B := fun i => π (MvPolynomial.X i) with hbdef
  have hψcomp : ψ.comp (Ideal.Quotient.mkₐ A J) = MvPolynomial.aeval â := by
    rw [hψdef]; exact Ideal.Quotient.liftₐ_comp J (MvPolynomial.aeval â) hJle
  have hqb : ∀ i, q (b i) = â i := by
    intro i
    have h1 : q (b i) = (ψ.comp (Ideal.Quotient.mkₐ A J)) (MvPolynomial.X i) := by
      rw [hbdef, hπdef]
      exact AlgHom.congr_fun hpq _
    rw [h1, hψcomp, MvPolynomial.aeval_X]
  have hfb : ∀ j, MvPolynomial.aeval b (f j) = 0 := by
    intro j
    have h1 : MvPolynomial.aeval b (f j) = π (f j) :=
      (AlgHom.congr_fun (MvPolynomial.aeval_unique π) (f j)).symm
    have hmem : f j ∈ J := by rw [hJdef]; exact Ideal.subset_span ⟨j, rfl⟩
    rw [h1, hπdef]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hmem]
  -- Lift `B → A ⧸ I^N` along an étale extension (Tag 07M7).
  set σ : B →ₐ[A] A ⧸ I ^ N := (AdicCompletion.evalₐ I N).comp q with hσdef
  obtain ⟨A', _, _, hA'et, hbij, στ, hστ⟩ := exists_etale_lift_of_smooth (I ^ N) σ
  have : Algebra.Etale A A' := hA'et
  set J' : Ideal A' := (I ^ N).map (algebraMap A A') with hJ'def
  set qm : (A ⧸ I ^ N) →+* (A' ⧸ J') :=
    Ideal.quotientMap J' (algebraMap A A') Ideal.le_comap_map with hqmdef
  set e : (A ⧸ I ^ N) ≃+* (A' ⧸ J') := RingEquiv.ofBijective qm hbij with hedef
  have hqme : ∀ x, e x = qm x := fun _ => rfl
  -- A section `A' → A` exists because `(A, I)` is henselian (Tag 09XI).
  have hIN : I ^ N ≤ I := Ideal.pow_le_self hN
  set ρ : A' →ₐ[A] A ⧸ I :=
    ⟨(Ideal.Quotient.factor hIN).comp (e.symm.toRingHom.comp (Ideal.Quotient.mk J')), by
      intro r
      change (Ideal.Quotient.factor hIN) (e.symm (Ideal.Quotient.mk J' (algebraMap A A' r))) = _
      rw [show Ideal.Quotient.mk J' (algebraMap A A' r) = qm (Ideal.Quotient.mk (I ^ N) r) from
        (Ideal.quotientMap_mk).symm, ← hqme, e.symm_apply_apply, Ideal.Quotient.factor_mk]
      rfl⟩ with hρdef
  have hsec : ∀ (A'' : Type u) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''],
      ∀ σ' : A'' →ₐ[A] A ⧸ I, ∃ τ : A'' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ' :=
    ((henselianPair_tfae.{u, u} A I).out 1 2).mp hAI
  obtain ⟨χ, -⟩ := hsec A' ρ
  -- `χ` is an `A`-algebra map, hence a retraction, hence inverse to `qm` modulo `I^N`.
  have hχJ : ∀ y ∈ J', χ y ∈ I ^ N := by
    intro y hy
    have hle : J' ≤ Ideal.comap χ.toRingHom (I ^ N) := by
      rw [hJ'def]
      refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
      have hc : χ (algebraMap A A' x) = x := by simp
      simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hc]
      exact hx
    exact hle hy
  set χbar : (A' ⧸ J') →+* A ⧸ I ^ N :=
    Ideal.Quotient.lift J' ((Ideal.Quotient.mk (I ^ N)).comp χ.toRingHom)
      (fun y hy => Ideal.Quotient.eq_zero_iff_mem.2 (hχJ y hy)) with hχbardef
  have hχbar : ∀ y : A', χbar (Ideal.Quotient.mk J' y) = Ideal.Quotient.mk (I ^ N) (χ y) :=
    fun y => rfl
  have hχqm : ∀ x : A ⧸ I ^ N, χbar (qm x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hqmdef, Ideal.quotientMap_mk, hχbar]
    congr 1
    simp
  have hinv : ∀ y : A', Ideal.Quotient.mk (I ^ N) (χ y) = e.symm (Ideal.Quotient.mk J' y) := by
    intro y
    have h := hχqm (e.symm (Ideal.Quotient.mk J' y))
    rw [← hqme, e.apply_symm_apply, hχbar] at h
    exact h
  have hlift : ∀ x : B, qm (σ x) = Ideal.Quotient.mk J' (στ x) := fun x =>
    RingHom.congr_fun hστ x
  have hcong : ∀ i, AdicCompletion.evalₐ I N (â i) =
      Ideal.Quotient.mk (I ^ N) (χ (στ (b i))) := by
    intro i
    rw [hinv (στ (b i)), ← hlift (b i), ← hqme, e.symm_apply_apply, hσdef]
    simp [hqb i]
  refine ⟨fun i => χ (στ (b i)), fun i => ?_, fun j => ?_⟩
  · refine mem_map_pow_of_evalₐ_eq_zero (IsNoetherian.noetherian I) ?_
    rw [map_sub, hcong i, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    simp
  · exact (MvPolynomial.comp_aeval_apply (f := b) (χ.comp στ) (f j)).symm.trans
      (by rw [hfb j, map_zero])

end Stacks.Smoothing

end

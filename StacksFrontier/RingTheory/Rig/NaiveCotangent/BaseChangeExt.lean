module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeTensor
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ExtAnnihilation

/-!
# Stacks 0GAL: annihilation of `Ext¹` of the completed cotangent complex after base change

Let `(A₁, I₁) → (A₂, I₂)` be as in Stacks Remark 0AL5 with `A₁` and `A₂` Noetherian, let `B₁`
be adically of finite type over `(A₁, I₁)` and let `B₂` be its completed base change
`(B₁ ⊗_{A₁} A₂)^∧_{I₂}`.  Stacks 0GAL says that if `f₁ ∈ B₁` annihilates
`Ext¹_{B₁}(NL^∧_{B₁/A₁}, N₁)` for every `B₁`-module `N₁`, then its image annihilates
`Ext¹_{B₂}(NL^∧_{B₂/A₂}, N₂)` for every `B₂`-module `N₂`.

Its proof is the comparison map of Stacks 0GAG, which is complete: the square of
`StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChange`, the `H⁻¹`-surjectivity of
`StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeCotangent`, and the limit computation of
`StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeTensor`.

What this file supplies is the **one-sided** form of that transport.  Annihilation of `Ext¹` is
weaker than `f • 𝟙 = 0` in the derived category: by Stacks 0G9F it is the existence of a map
`σ : ⨁ i, B dxᵢ → J / J²` with `σ ∘ d = f • id` on `J / J²` *only*, while `f • 𝟙 = 0` also
demands `d ∘ σ = f • id` on `⨁ i, B dxᵢ`.  The existing transport
`Rig.exists_section_of_spanning_comparison` consumes and produces both identities, and the
first of its two conclusions in fact uses only the first of its two hypotheses — the second is
the one that needs the commuting square, the first the spanning.  So this file splits it, and
with the split the Stacks proof of 0GAL goes through on the Ext hypothesis alone.

## Main results

* `Rig.exists_generating_family` — an object of `Rig.AdicFiniteTypeAlgebra A I` admits a finite
  family of elements whose reductions generate `B / I B` over `A / I`.
* `Rig.exists_section_left_of_spanning_comparison` — the one-sided transport, at module level.
* `Rig.exists_differential_section_left_of_smul_ext_one` and
  `Rig.smul_ext_one_of_differential_section_left` — the two directions of Stacks 0G9F for the
  completed naive cotangent complex, read on the conormal module rather than on the lifted
  cochain complex.
* `Rig.le_span_range_sup_adicIdeal_of_completedBaseChange` — the hypothesis `hspan` of
  `Rig.aeval_surjective_baseChange`, for any realization of the completed base change.
* `Rig.smul_ext_one_of_completedBaseChange` — 0GAL for any realization of the base change,
  the identification taken as data.
* `Rig.smul_ext_one_of_completedBaseChangeFunctor` — 0GAL for any
  `Rig.CompletedBaseChange` functor.
* `Rig.smul_ext_one_completedBaseChangeOfIsNoetherianRing` — **Stacks 0GAL**, for the
  completed base change `(B₁ ⊗_{A₁} A₂)^∧` of Remark 0AL5 itself,
  `Rig.completedBaseChangeOfIsNoetherianRing`.

## References

* [Stacks Project, Tag 0GAL](https://stacks.math.columbia.edu/tag/0GAL)
* [Stacks Project, Tag 0GAG](https://stacks.math.columbia.edu/tag/0GAG)
* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
* [The Stacks Project, Lemma 15.85.6 (0G9F)](https://stacks.math.columbia.edu/tag/0G9F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Rig

universe u v w u₁ u₂

open AdicFiniteTypeAlgebra CompletedPolynomialPresentation CompletedNaiveCotangentComplex

attribute [local instance] HasDerivedCategory.standard

section Generators

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **An object of `Rig.AdicFiniteTypeAlgebra A I` has a finite generating family modulo
`I`.**  Its reduction `B / I B` is of finite type over `A / I`, so finitely many of its
elements generate it; lifting those along `B → B / I B` gives the family. -/
public theorem exists_generating_family (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    ∃ (r : ℕ) (g : Fin r → B.carrier), Function.Surjective
      (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk B.adicIdeal (g i)) :
        MvPolynomial (Fin r) (A ⧸ I) →ₐ[A ⧸ I] B.reduction) := by
  classical
  obtain ⟨r, ⟨G⟩⟩ := (Algebra.FiniteType.iff_exists_generators
    (R := A ⧸ I) (S := B.reduction)).mp B.finiteTypeReduction
  refine ⟨r, fun i ↦ Classical.choose
    (Ideal.Quotient.mk_surjective (I := B.adicIdeal) (G.val i)), ?_⟩
  have hg : (fun i ↦ Ideal.Quotient.mk B.adicIdeal (Classical.choose
      (Ideal.Quotient.mk_surjective (I := B.adicIdeal) (G.val i)))) = G.val :=
    funext fun i ↦ Classical.choose_spec
      (Ideal.Quotient.mk_surjective (I := B.adicIdeal) (G.val i))
  rw [hg]
  exact fun s ↦ ⟨G.σ' s, G.aeval_val_σ' s⟩

end Generators

section Transport

/-- **The one-sided transport of a section along a spanning comparison map.**  Let `ι : R₁ → R₂`
be a ring map, let `d₁ : M₁ → R₁ ^ r` and `d₂ : M₂ → R₂ ^ r` be linear maps, and let
`θ : M₁ → M₂` be `R₁`-linear with `d₂ ∘ θ = ι ∘ d₁` coefficientwise and with `R₂`-spanning
image.  A section `σ₁` of `d₁` realizing `f₁ • id` on `M₁` transports to a section of `d₂`
realizing `ι f₁ • id` on `M₂`.

This is the first half of `Rig.exists_section_of_spanning_comparison`, which is exactly the
half that uses only the first of that lemma's two hypotheses.  It is what annihilation of
`Ext¹` gives, the second identity being strictly more. -/
public theorem exists_section_left_of_spanning_comparison
    {R₁ : Type*} [CommRing R₁] {R₂ : Type*} [CommRing R₂] [Algebra R₁ R₂]
    {M₁ : Type*} [AddCommGroup M₁] [Module R₁ M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R₂ M₂] [Module R₁ M₂] [IsScalarTower R₁ R₂ M₂]
    (r : ℕ) (d₁ : M₁ →ₗ[R₁] (Fin r → R₁)) (d₂ : M₂ →ₗ[R₂] (Fin r → R₂)) (θ : M₁ →ₗ[R₁] M₂)
    (hθd : ∀ x : M₁, d₂ (θ x) = fun i ↦ algebraMap R₁ R₂ (d₁ x i))
    (hθspan : Submodule.span R₂ (Set.range θ) = ⊤)
    (f₁ : R₁) (σ₁ : (Fin r → R₁) →ₗ[R₁] M₁)
    (hneg₁ : ∀ y : M₁, σ₁ (d₁ y) = f₁ • y) :
    ∃ σ₂ : (Fin r → R₂) →ₗ[R₂] M₂,
      ∀ y : M₂, σ₂ (d₂ y) = algebraMap R₁ R₂ f₁ • y := by
  classical
  have hθsmul : ∀ (b : R₁) (x : M₁), θ (b • x) = algebraMap R₁ R₂ b • θ x :=
    fun b x ↦ (map_smul θ b x).trans (algebraMap_smul R₂ b (θ x)).symm
  have hsingle : ∀ v : Fin r → R₁, ∑ i : Fin r, v i • Pi.single i (1 : R₁) = v := by
    intro v
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂ : (Fin r → R₂) →ₗ[R₂] M₂,
      σ₂ = ∑ i : Fin r, LinearMap.smulRight
        (LinearMap.proj i : (Fin r → R₂) →ₗ[R₂] R₂) (θ (σ₁ (Pi.single i 1))) := ⟨_, rfl⟩
  have hσ₂apply : ∀ x : Fin r → R₂,
      σ₂ x = ∑ i : Fin r, x i • θ (σ₁ (Pi.single i 1)) := by
    intro x
    rw [hσ₂]
    simp
  have hσ₂comp : ∀ v : Fin r → R₁,
      σ₂ (fun i ↦ algebraMap R₁ R₂ (v i)) = θ (σ₁ v) := by
    intro v
    rw [hσ₂apply]
    calc ∑ i : Fin r, algebraMap R₁ R₂ (v i) • θ (σ₁ (Pi.single i 1))
        = ∑ i : Fin r, θ (σ₁ (v i • Pi.single i (1 : R₁))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_smul, hθsmul]
      _ = θ (σ₁ (∑ i : Fin r, v i • Pi.single i (1 : R₁))) := by rw [map_sum, map_sum]
      _ = θ (σ₁ v) := by rw [hsingle]
  refine ⟨σ₂, fun y ↦ ?_⟩
  have hkey : σ₂.comp d₂ = algebraMap R₁ R₂ f₁ • LinearMap.id := by
    refine LinearMap.ext_on hθspan ?_
    rintro z ⟨x, rfl⟩
    change σ₂ (d₂ (θ x)) = algebraMap R₁ R₂ f₁ • θ x
    rw [hθd, hσ₂comp (d₁ x), hneg₁, hθsmul]
  simpa using LinearMap.congr_fun hkey y

end Transport

section Criterion

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
  (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)

/-- **Stacks 0G9F for the completed naive cotangent complex, read on the conormal module.**  If
`f` annihilates `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`, then multiplication by `f` on
the conormal module `J / J²` factors through the differential by a `B`-linear map
`σ : (Fin r → B) → J / J²`.

This is `Rig.smul_ext_one_derived_iff_exists_factorization` with the universe lifts and the term
isomorphisms `Rig.CompletedNaiveCotangentComplex.degreeZeroIso`, `.degreeNegOneIso` taken out,
in the shape a module-level transport can consume. -/
public theorem exists_differential_section_left_of_smul_ext_one (f : B.carrier)
    (h : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B P)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      f • ξ = 0) :
    ∃ σ : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent,
      ∀ y : P.extension.Cotangent,
        σ ((completedNaiveCotangentComplex B P).differential y) = f • y := by
  set K := completedNaiveCotangentComplex B P with hKdef
  obtain ⟨s, hneg⟩ := (smul_ext_one_derived_iff_exists_factorization B P f).mp h
  rw [K.cochainComplex_d] at hneg
  obtain ⟨t, htdef⟩ :
      ∃ t : ModuleCat.of B.carrier (LiftedDifferentials (P := P)) ⟶
        ModuleCat.of B.carrier (LiftedCotangent (P := P)),
        t = K.degreeZeroIso.inv ≫ s ≫ K.degreeNegOneIso.hom := ⟨_, rfl⟩
  have keyneg : ModuleCat.ofHom K.liftedDifferential ≫ t =
      f • 𝟙 (ModuleCat.of B.carrier (LiftedCotangent (P := P))) := by
    refine (cancel_epi K.degreeNegOneIso.hom).mp ?_
    calc K.degreeNegOneIso.hom ≫ ModuleCat.ofHom K.liftedDifferential ≫ t
        = ((K.degreeNegOneIso.hom ≫ ModuleCat.ofHom K.liftedDifferential ≫
            K.degreeZeroIso.inv) ≫ s) ≫ K.degreeNegOneIso.hom := by
          rw [htdef]; simp only [Category.assoc]
      _ = (f • 𝟙 (K.cochainComplex.X (-1))) ≫ K.degreeNegOneIso.hom := by rw [hneg]
      _ = K.degreeNegOneIso.hom ≫
            (f • 𝟙 (ModuleCat.of B.carrier (LiftedCotangent (P := P)))) := by simp
  refine ⟨ULift.moduleEquiv.toLinearMap.comp
    (t.hom.comp ULift.moduleEquiv.symm.toLinearMap), fun y ↦ ?_⟩
  have hap : (ModuleCat.Hom.hom (ModuleCat.ofHom K.liftedDifferential ≫ t)) (ULift.up y) =
      (ModuleCat.Hom.hom
        (f • 𝟙 (ModuleCat.of B.carrier (LiftedCotangent (P := P))))) (ULift.up y) := by
    rw [keyneg]
  simpa using congrArg ULift.down hap

/-- **The converse half of Stacks 0G9F, read on the conormal module.**  A `B`-linear map
`σ : (Fin r → B) → J / J²` realizing multiplication by `f` against the differential makes `f`
annihilate `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`.

This direction says nothing about the degree-zero term, so it is the one that consumes
transported data. -/
public theorem smul_ext_one_of_differential_section_left (f : B.carrier)
    (σ : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent)
    (hneg : ∀ y : P.extension.Cotangent,
      σ ((completedNaiveCotangentComplex B P).differential y) = f • y) :
    ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B P)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      f • ξ = 0 := by
  set K := completedNaiveCotangentComplex B P with hKdef
  have hcompneg : ModuleCat.ofHom K.liftedDifferential ≫
      ModuleCat.ofHom (liftedSection B P σ) =
      f • 𝟙 (ModuleCat.of B.carrier (LiftedCotangent (P := P))) :=
    ModuleCat.hom_ext (LinearMap.ext fun y ↦ congrArg ULift.up (hneg y.down))
  refine (smul_ext_one_derived_iff_exists_factorization B P f).mpr
    ⟨K.degreeZeroIso.hom ≫ ModuleCat.ofHom (liftedSection B P σ) ≫
      K.degreeNegOneIso.inv, ?_⟩
  rw [K.cochainComplex_d]
  have step : ModuleCat.ofHom K.liftedDifferential ≫
      ModuleCat.ofHom (liftedSection B P σ) ≫ K.degreeNegOneIso.inv =
      f • K.degreeNegOneIso.inv := by
    rw [← Category.assoc, hcompneg, Linear.smul_comp, Category.id_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, step, Linear.comp_smul, Iso.hom_inv_id]

end Criterion

section BaseChange

/-- The canonical map into the adic completion of a ring is its structure map. -/
private theorem adicCompletion_of_eq_algebraMap {R : Type*} [CommRing R] (I : Ideal R) (t : R) :
    AdicCompletion.of I R t = algebraMap R (AdicCompletion I R) t := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂} {c : ℕ}
  {B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁} {B₂ : AdicFiniteTypeAlgebra.{u₂, w} A₂ I₂}
  [Algebra B₁.carrier B₂.carrier]

omit [IsNoetherianRing A₁] [IsNoetherianRing A₂] [Algebra B₁.carrier B₂.carrier] in
/-- Under an identification of `B₂` with `(B₁ ⊗_{A₁} A₂)^∧_{I₂}` carrying the structural map of
`A₂` to the canonical one, the ideal of definition of `B₂` corresponds to the ideal generated by
`I₂` in the completion of the tensor product. -/
public theorem map_adicIdeal_completedBaseChange
    (e : B₂.carrier ≃+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
    (heA : ∀ a : A₂, e (algebraMap A₂ B₂.carrier a) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedRight A₂ B₁ a)) :
    Ideal.map (e : B₂.carrier →+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
        B₂.adicIdeal =
      Ideal.map (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁))
        (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁) := by
  change Ideal.map (e : B₂.carrier →+* _) (Ideal.map (algebraMap A₂ B₂.carrier) I₂) =
    Ideal.map (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁))
      (Ideal.map (baseChangedRight A₂ B₁).toRingHom I₂)
  rw [Ideal.map_map, Ideal.map_map]
  exact congrArg (Ideal.map · I₂) (RingHom.ext heA)

omit [IsNoetherianRing A₁] [IsNoetherianRing A₂] in
/-- **The hypothesis `hspan` of `Rig.aeval_surjective_baseChange`, for any realization of the
completed base change.**  Every element of `B₂` differs, modulo its ideal of definition, from an
`A₂`-linear combination of elements of the image of `B₁`.

Indeed `B₁ ⊗_{A₁} A₂` is spanned over `A₂` by the image of `B₁`, since `b ⊗ a = a · (b ⊗ 1)`,
and the completion maps onto its reduction modulo `I₂`. -/
public theorem le_span_range_sup_adicIdeal_of_completedBaseChange (hI₂ : I₂.FG)
    (e : B₂.carrier ≃+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
    (heA : ∀ a : A₂, e (algebraMap A₂ B₂.carrier a) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedRight A₂ B₁ a))
    (heB : ∀ b : B₁.carrier, e (algebraMap B₁.carrier B₂.carrier b) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedLeft A₂ B₁ b)) :
    (⊤ : Submodule A₂ B₂.carrier) ≤
      Submodule.span A₂ (Set.range (algebraMap B₁.carrier B₂.carrier)) ⊔
        Submodule.restrictScalars A₂ B₂.adicIdeal := by
  intro x _
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalOneₐ (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁) (e x))
  -- the approximation, pulled back through `e`
  have hspan : ∀ t : baseChangedAlgebra (A₂ := A₂) B₁,
      e.symm (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) t) ∈
        Submodule.span A₂ (Set.range (algebraMap B₁.carrier B₂.carrier)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul b a =>
        have hprod : (b ⊗ₜ[A₁] a : baseChangedAlgebra (A₂ := A₂) B₁) =
            baseChangedLeft A₂ B₁ b * baseChangedRight A₂ B₁ a := by
          change _ = (b ⊗ₜ[A₁] (1 : A₂)) * ((1 : B₁.carrier) ⊗ₜ[A₁] a)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have hval : e.symm (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
            (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
            (b ⊗ₜ[A₁] a)) =
            a • algebraMap B₁.carrier B₂.carrier b := by
          rw [hprod, map_mul, ← heA a, ← heB b, ← map_mul, e.symm_apply_apply,
            Algebra.smul_def, mul_comm]
        rw [hval]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    | add t₁ t₂ h₁ h₂ => simpa [map_add] using Submodule.add_mem _ h₁ h₂
  -- the difference lies in the ideal of definition
  have hdiff : x - e.symm (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
      (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) s) ∈ B₂.adicIdeal := by
    have hT : e x - algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) s ∈
        Ideal.map (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
            (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁))
          (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁) := by
      rw [← AdicCompletion.ker_evalOneₐ_eq_map (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁)
        (baseChangedIdeal_fg B₁ hI₂), RingHom.mem_ker, map_sub]
      have h2 : AdicCompletion.evalOneₐ (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁)
          (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
            (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) s) =
          Ideal.Quotient.mk (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁) s := by
        rw [← adicCompletion_of_eq_algebraMap, AdicCompletion.evalOneₐ_of]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h2, hs, sub_self]
    rw [← map_adicIdeal_completedBaseChange e heA] at hT
    have hker : RingHom.ker
        (e : B₂.carrier →+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) = ⊥ := by
      ext z
      simp
    have hmem : x - e.symm (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) s) ∈
        Ideal.comap (e : B₂.carrier →+*
            completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
          (Ideal.map (e : B₂.carrier →+*
            completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) B₂.adicIdeal) := by
      rw [Ideal.mem_comap, map_sub]
      simp only [RingHom.coe_coe, RingEquiv.apply_symm_apply]
      exact hT
    rwa [Ideal.comap_map_of_surjective
      (e : B₂.carrier →+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
      (fun y ↦ ⟨e.symm y, e.apply_symm_apply y⟩), ← RingHom.ker_eq_comap_bot, hker,
      sup_bot_eq] at hmem
  rw [show x = e.symm (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
      (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) s) +
      (x - e.symm (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) s)) by ring]
  exact Submodule.add_mem_sup (hspan s) ((Submodule.restrictScalars_mem A₂ _ _).mpr hdiff)

variable [Algebra A₁ B₂.carrier] [IsScalarTower A₁ A₂ B₂.carrier]
  [IsScalarTower A₁ B₁.carrier B₂.carrier]

/-- **The one-sided transport of Stacks 0GAG.**  A section `σ₁` of the differential of
`NL^∧_{B₁/A₁}` realizing `f₁ • id` on the conormal module gives one for the compatible
presentation of `B₂`, realizing the image of `f₁`.

This is `Rig.exists_section_left_of_spanning_comparison` fed the comparison square
`Rig.baseChange_differential` and the spanning
`Rig.span_range_baseChangeCotangentMap_eq_top`; unlike
`Rig.exists_differential_section_baseChange` it needs only the identity on the conormal
module, which is what annihilation of `Ext¹` supplies. -/
public theorem exists_differential_section_left_baseChange (hI₁ : I₁.FG) (hI₂ : I₂.FG)
    (hc : 0 < c) (hmap : (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂)
    (hspan : (⊤ : Submodule A₂ B₂.carrier) ≤
      Submodule.span A₂ (Set.range (algebraMap B₁.carrier B₂.carrier)) ⊔
        Submodule.restrictScalars A₂ B₂.adicIdeal)
    (r : ℕ) (g : Fin r → B₁.carrier)
    (hgen : Function.Surjective (MvPolynomial.aeval
      (fun i ↦ Ideal.Quotient.mk B₁.adicIdeal (g i)) :
        MvPolynomial (Fin r) (A₁ ⧸ I₁) →ₐ[A₁ ⧸ I₁] B₁.reduction))
    (hker : (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen).extension.ker ≤
      Ideal.map (baseChangeExtensionHom hI₁ hI₂ hc hmap hspan r g hgen).toRingHom
        (ofGenerators B₁ r g hI₁ hgen).extension.ker)
    (f₁ : B₁.carrier)
    (σ₁ : (Fin r → B₁.carrier) →ₗ[B₁.carrier]
      (ofGenerators B₁ r g hI₁ hgen).extension.Cotangent)
    (hneg₁ : ∀ y : (ofGenerators B₁ r g hI₁ hgen).extension.Cotangent,
      σ₁ ((completedNaiveCotangentComplex B₁ (ofGenerators B₁ r g hI₁ hgen)).differential y) =
        f₁ • y) :
    ∃ σ₂ : (Fin r → B₂.carrier) →ₗ[B₂.carrier]
        (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen).extension.Cotangent,
      ∀ y : (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen).extension.Cotangent,
        σ₂ ((completedNaiveCotangentComplex B₂
            (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen)).differential y) =
          algebraMap B₁.carrier B₂.carrier f₁ • y :=
  exists_section_left_of_spanning_comparison r
    (completedNaiveCotangentComplex B₁ (ofGenerators B₁ r g hI₁ hgen)).differential
    (completedNaiveCotangentComplex B₂
      (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen)).differential
    (baseChangeCotangentMap hI₁ hI₂ hc hmap hspan r g hgen)
    (baseChange_differential hI₁ hI₂ hc hmap hspan r g hgen
      (completedNaiveCotangentComplex B₁ (ofGenerators B₁ r g hI₁ hgen))
      (completedNaiveCotangentComplex B₂
        (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen)))
    (span_range_baseChangeCotangentMap_eq_top hI₁ hI₂ hc hmap hspan r g hgen hker)
    f₁ σ₁ hneg₁

/-- **Stacks 0GAL.**  Let `(A₁, I₁) → (A₂, I₂)` be as in Stacks Remark 0AL5 — a map of
Noetherian pairs carrying a positive power of `I₁` into `I₂` — let `B₁` be adically of finite
type over `(A₁, I₁)`, and let `B₂` be its completed base change `(B₁ ⊗_{A₁} A₂)^∧_{I₂}`.  If
`f₁ ∈ B₁` annihilates `Ext¹_{B₁}(NL^∧_{B₁/A₁}, N₁)` for every `B₁`-module `N₁`, then its image
in `B₂` annihilates `Ext¹_{B₂}(NL^∧_{B₂/A₂}, N₂)` for every `B₂`-module `N₂`.

The proof is Stacks': choose a generating family of `B₁` modulo `I₁`, present both algebras on
those variables, and transport along the comparison map of Stacks 0GAG, whose `H⁻¹`-surjectivity
is `Rig.span_range_baseChangeCotangentMap_eq_top` and whose remaining input is
`Rig.ker_le_map_ker_of_completedBaseChange`.  Both ends are moved to the given presentations by
presentation-independence, Stacks 0GAE.

The tag sits on `Rig.smul_ext_one_completedBaseChangeOfIsNoetherianRing`, which is the form Stacks
states — `B₂` *is* the base change — while this one is the general engine, taking the
identification as data. -/
public theorem smul_ext_one_of_completedBaseChange (hc : 0 < c)
    (hmap : (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂)
    (e : B₂.carrier ≃+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
    (heA : ∀ a : A₂, e (algebraMap A₂ B₂.carrier a) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedRight A₂ B₁ a))
    (heB : ∀ b : B₁.carrier, e (algebraMap B₁.carrier B₂.carrier b) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedLeft A₂ B₁ b))
    (P₁ : CompletedPolynomialPresentation I₁ B₁)
    (P₂ : CompletedPolynomialPresentation I₂ B₂) (f₁ : B₁.carrier)
    (h : ∀ (N : ModuleCat.{max u₁ v} B₁.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B₁ P₁)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ v} B₁.carrier) 0).obj N) 1),
      f₁ • ξ = 0) :
    ∀ (N : ModuleCat.{max u₂ w} B₂.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B₂ P₂)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ w} B₂.carrier) 0).obj N) 1),
      algebraMap B₁.carrier B₂.carrier f₁ • ξ = 0 := by
  have hI₁ : I₁.FG := Ideal.fg_of_isNoetherianRing I₁
  have hI₂ : I₂.FG := Ideal.fg_of_isNoetherianRing I₂
  have hspan := le_span_range_sup_adicIdeal_of_completedBaseChange hI₂ e heA heB
  obtain ⟨r, g, hgen⟩ := exists_generating_family B₁
  have hsurj := completedAeval_surjective B₁ r g hI₁ hgen
  have hker : (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen).extension.ker ≤
      Ideal.map (baseChangeExtensionHom hI₁ hI₂ hc hmap hspan r g hgen).toRingHom
        (ofGenerators B₁ r g hI₁ hgen).extension.ker := by
    rw [ker_extension_baseChangePresentation hI₂ hc hmap hspan r g hgen,
      ker_extension_ofGenerators hI₁ r g hgen]
    exact ker_le_map_ker_of_completedBaseChange hI₂ hmap r g hsurj e heA heB
  have h₁ := smul_ext_one_derived_congr_presentation B₁ P₁
    (ofGenerators B₁ r g hI₁ hgen) f₁ h
  obtain ⟨σ₁, hneg₁⟩ := exists_differential_section_left_of_smul_ext_one B₁
    (ofGenerators B₁ r g hI₁ hgen) f₁ h₁
  obtain ⟨σ₂, hneg₂⟩ := exists_differential_section_left_baseChange hI₁ hI₂ hc hmap hspan
    r g hgen hker f₁ σ₁ hneg₁
  exact smul_ext_one_derived_congr_presentation B₂
    (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen) P₂
    (algebraMap B₁.carrier B₂.carrier f₁)
    (smul_ext_one_of_differential_section_left B₂
      (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen)
      (algebraMap B₁.carrier B₂.carrier f₁) σ₂ hneg₂)

end BaseChange

section Functor

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂} {c : ℕ}

/-- **Stacks 0GAL, for any completed base-change functor.**  With `(A₁, I₁) → (A₂, I₂)` as in
Stacks Remark 0AL5 — witnessed by `hc` and `hmap` — annihilation of all first Ext groups of
`NL^∧_{B₁/A₁}` by `f₁ ∈ B₁` gives annihilation of all first Ext groups of `NL^∧_{B₂/A₂}` by the
image of `f₁` in the base change `B₂ = C.functor.obj B₁`, for any completed polynomial
presentations of the two algebras.

The functor's identification of `B₂` with `(B₁ ⊗_{A₁} A₂)^∧_{I₂}` supplies exactly the data
`Rig.smul_ext_one_of_completedBaseChange` asks for; the algebra structure of `B₂` over `B₁` is
the one whose structural map is `Rig.CompletedBaseChange.scalar`.  Stacks 0GAL itself, for the
constructed base change, is `Rig.smul_ext_one_completedBaseChangeOfIsNoetherianRing`. -/
public theorem smul_ext_one_of_completedBaseChangeFunctor
    (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
    (hc : 0 < c) (hmap : (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂)
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
    (P₁ : CompletedPolynomialPresentation I₁ B₁)
    (P₂ : CompletedPolynomialPresentation I₂ (C.functor.obj B₁)) (f₁ : B₁.carrier)
    (h : ∀ (N : ModuleCat.{max u₁ v} B₁.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B₁ P₁)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ v} B₁.carrier) 0).obj N) 1),
      f₁ • ξ = 0) :
    ∀ (N : ModuleCat.{max u₂ v} (C.functor.obj B₁).carrier)
      (ξ : DerivedCategory.Ext
        (derivedCompletedNaiveCotangentComplex (C.functor.obj B₁) P₂)
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max u₂ v} (C.functor.obj B₁).carrier) 0).obj N) 1),
      C.scalar B₁ f₁ • ξ = 0 := by
  let instB : Algebra B₁.carrier (C.functor.obj B₁).carrier :=
    ((C.completedTensorProductEquiv B₁).symm.toRingHom.comp
      ((algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)).comp
        (baseChangedLeft A₂ B₁).toRingHom)).toAlgebra
  have halg : (algebraMap B₁.carrier (C.functor.obj B₁).carrier) =
      (C.completedTensorProductEquiv B₁).symm.toRingHom.comp
        ((algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
            (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)).comp
          (baseChangedLeft A₂ B₁).toRingHom) :=
    RingHom.algebraMap_toAlgebra _
  have halgb : ∀ b : B₁.carrier,
      algebraMap B₁.carrier (C.functor.obj B₁).carrier b =
        (C.completedTensorProductEquiv B₁).symm
          (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
            (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
            (baseChangedLeft A₂ B₁ b)) := fun b ↦ by
    rw [halg]
    rfl
  have hscalar : ∀ b : B₁.carrier,
      algebraMap B₁.carrier (C.functor.obj B₁).carrier b = C.scalar B₁ b := fun b ↦ by
    rw [halgb b, ← adicCompletion_of_eq_algebraMap]
  have heB : ∀ b : B₁.carrier,
      C.completedTensorProductEquiv B₁
          (algebraMap B₁.carrier (C.functor.obj B₁).carrier b) =
        algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
          (baseChangedLeft A₂ B₁ b) := fun b ↦ by
    rw [halgb b, RingEquiv.apply_symm_apply]
  have heA : ∀ a : A₂,
      C.completedTensorProductEquiv B₁
          (algebraMap A₂ (C.functor.obj B₁).carrier a) =
        algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
          (baseChangedRight A₂ B₁ a) := fun a ↦ by
    rw [C.algebraMap_completedTensorProductEquiv B₁ a,
      adicCompletion_of_eq_algebraMap]
  let instA : Algebra A₁ (C.functor.obj B₁).carrier :=
    ((algebraMap A₂ (C.functor.obj B₁).carrier).comp (algebraMap A₁ A₂)).toAlgebra
  have hA₁ : (algebraMap A₁ (C.functor.obj B₁).carrier) =
      (algebraMap A₂ (C.functor.obj B₁).carrier).comp (algebraMap A₁ A₂) :=
    RingHom.algebraMap_toAlgebra _
  have towerA : IsScalarTower A₁ A₂ (C.functor.obj B₁).carrier :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by rw [hA₁]; rfl
  have towerB : IsScalarTower A₁ B₁.carrier (C.functor.obj B₁).carrier := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    have hleft : baseChangedLeft A₂ B₁ (algebraMap A₁ B₁.carrier x) =
        baseChangedRight A₂ B₁ (algebraMap A₁ A₂ x) := by
      simp only [baseChangedLeft, baseChangedRight, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one (R := A₁) (A := B₁.carrier),
        Algebra.algebraMap_eq_smul_one (R := A₁) (A := A₂), TensorProduct.smul_tmul]
    refine (C.completedTensorProductEquiv B₁).injective ?_
    rw [heB (algebraMap A₁ B₁.carrier x), hleft, ← heA (algebraMap A₁ A₂ x), hA₁]
    rfl
  rw [← hscalar f₁]
  exact smul_ext_one_of_completedBaseChange hc hmap (C.completedTensorProductEquiv B₁)
    heA heB P₁ P₂ f₁ h

/-- **Stacks Project, Tag 0GAL.**  Let `(A₁, I₁) → (A₂, I₂)` be as in Stacks Remark 0AL5 — a
ring map `A₁ → A₂` of Noetherian rings with ideals `I₁ ⊆ A₁`, `I₂ ⊆ A₂` such that `I₁ ^ c`
maps into `I₂` for some `c ≥ 1` — let `B₁` be adically of finite type over `(A₁, I₁)` (Stacks
0AL4), let `B₂ = (B₁ ⊗_{A₁} A₂)^∧` be its base change, the value at `B₁` of the completed
base-change functor `Rig.completedBaseChangeOfIsNoetherianRing` of Remark 0AL5, and let
`f₂ ∈ B₂` be the image of `f₁ ∈ B₁`, that is of `f₁ ⊗ 1` (`Rig.CompletedBaseChange.scalar`).
If `f₁` annihilates `Ext¹_{B₁}(NL^∧_{B₁/A₁}, N₁)` for
every `B₁`-module `N₁`, then `f₂` annihilates `Ext¹_{B₂}(NL^∧_{B₂/A₂}, N₂)` for every
`B₂`-module `N₂`.

The completed cotangent complexes are computed from arbitrary completed polynomial
presentations `P₁` and `P₂`, on which they do not depend (Stacks 0GAE). -/
@[stacks 0GAL]
public theorem smul_ext_one_completedBaseChangeOfIsNoetherianRing
    (hpow : ∃ c : ℕ, 0 < c ∧ (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂)
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
    (P₁ : CompletedPolynomialPresentation I₁ B₁)
    (P₂ : CompletedPolynomialPresentation I₂
      ((completedBaseChangeOfIsNoetherianRing hpow).functor.obj B₁))
    (f₁ : B₁.carrier)
    (h : ∀ (N : ModuleCat.{max u₁ v} B₁.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B₁ P₁)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ v} B₁.carrier) 0).obj N) 1),
      f₁ • ξ = 0) :
    ∀ (N : ModuleCat.{max u₂ v}
        ((completedBaseChangeOfIsNoetherianRing hpow).functor.obj B₁).carrier)
      (ξ : DerivedCategory.Ext
        (derivedCompletedNaiveCotangentComplex
          ((completedBaseChangeOfIsNoetherianRing hpow).functor.obj B₁) P₂)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ v}
          ((completedBaseChangeOfIsNoetherianRing hpow).functor.obj B₁).carrier) 0).obj N) 1),
      (completedBaseChangeOfIsNoetherianRing hpow).scalar B₁ f₁ • ξ = 0 :=
  smul_ext_one_of_completedBaseChangeFunctor (completedBaseChangeOfIsNoetherianRing hpow)
    hpow.choose_spec.1 hpow.choose_spec.2 B₁ P₁ P₂ f₁ h

end Functor

end Rig

end

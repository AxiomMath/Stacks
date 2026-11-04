module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.Deformation.Completed.SmoothModel
public import StacksFrontier.Deformation.Formal.VersalObject.DerivationOrbitCriterion
public import StacksFrontier.Deformation.Schlessinger.MinimalVersalOrbits
public import StacksFrontier.Deformation.Smooth.Unobstructed
public import StacksFrontier.Deformation.VersalObject.MinimalVersalOrbitBijection
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# The base category as a deformation category over itself

The base category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field `k` is a category
cofibered in groupoids over itself, through the identity functor. As such it is a
predeformation category, it satisfies Schlessinger's conditions (S1) and (S2), and its tangent
space vanishes; so it satisfies condition (3) of Stacks 06IX and therefore carries a minimal
versal formal object.

A formal object of `𝒞_Λ` over itself with base `R` is the family of adic truncations
`R/𝔪_R^{n+1}`. It is versal exactly when `Λ → R` is formally smooth in the `𝔪_R`-adic topology,
and a *minimal* versal object exactly when, in addition, every `Λ`-derivation `R → k` is the
composite of the augmentation `R → k` with a `Λ`-derivation of `k`. The complete local algebra
`Deformation.smoothModel` of Stacks 06SM satisfies both conditions, and the base of any minimal
versal formal object of `𝒞_Λ` over itself is isomorphic to it, with `H₁(L_{k/Λ}) = 𝔪/𝔪²` and
`Ω_{−/Λ} ⊗ k = Ω_{k/Λ}`.

## Main definitions

* `Deformation.selfFormalObject`: the tautological formal object of `𝒞_Λ` over itself with a
  prescribed complete local algebra as base.
* `Deformation.ResidueDerivationSurjective`: the condition that the injection
  `Der_Λ(k, k) → Der_Λ(R, k)` be surjective.

## Main results

* `Deformation.isPredeformationCategory_id`, `Deformation.schlessingerConditionS1_id`,
  `Deformation.schlessingerConditionS2_id`,
  `Deformation.unique_predeformationTangentSpace_id`: `𝒞_Λ` over itself is a predeformation
  category satisfying (S1) and (S2) with vanishing tangent space.
* `Deformation.satisfiesRS_id` and `Deformation.isDeformationCategory_id`: `𝒞_Λ` over itself
  satisfies the Rim–Schlessinger condition, hence is a deformation category over itself.
* `Deformation.isMinimalVersal_selfFormalObject_smoothModel`: the object of Stacks 06SM carries
  a minimal versal formal object.
* `Deformation.isMinimalVersal_id_base_properties`: the base of any minimal versal formal object
  of `𝒞_Λ` over itself is formally smooth over `Λ`, carries the two cotangent identifications,
  and is isomorphic to the object of Stacks 06SM.
* `Deformation.isVersal_selfFormalObject_iff_formallySmoothNAdic` and
  `Deformation.isMinimalVersal_selfFormalObject_iff`: the tautological formal object over `R` is
  versal exactly when `Λ → R` is formally smooth, and minimal versal exactly when moreover every
  `Λ`-derivation `R → k` comes from a `Λ`-derivation of `k`.
* `Deformation.bijective_mapBaseChange_iff_forall_exists_derivation`: `Ω_{R/Λ} ⊗_R k → Ω_{k/Λ}`
  is bijective exactly when `Der_Λ(k, k) → Der_Λ(R, k)` is surjective.

## References

* [Stacks Project, Tag 06T9](https://stacks.math.columbia.edu/tag/06T9)
* [Stacks Project, Tag 06SM](https://stacks.math.columbia.edu/tag/06SM)
* [Stacks Project, Tag 06IR](https://stacks.math.columbia.edu/tag/06IR)
* [Stacks Project, Tag 06IX](https://stacks.math.columbia.edu/tag/06IX)
* [Stacks Project, Tag 06T5](https://stacks.math.columbia.edu/tag/06T5)
* [Stacks Project, Tag 06T6](https://stacks.math.columbia.edu/tag/06T6)
* [Stacks Project, Tag 06T8](https://stacks.math.columbia.edu/tag/06T8)
* [Stacks Project, Tag 0DYL](https://stacks.math.columbia.edu/tag/0DYL)
-/

@[expose] public section

open CategoryTheory
open IsLocalRing

namespace Deformation

universe u v w

variable (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The identity functor -/

section Identity

variable {C : Type*} [Category C]

/-- The identity functor is cofibered in groupoids. -/
public theorem isCofiberedInGroupoids_id : IsCofiberedInGroupoids (𝟭 C) :=
  Functor.isFiberedInGroupoids_id

/-- Every fibre of the identity functor has exactly one morphism between any two objects:
a morphism of the fibre over `A` is forced to be the canonical identification. -/
public theorem unique_hom_fiber_id (A : C) (x y : (𝟭 C).Fiber A) :
    Nonempty (Unique (x ⟶ y)) := by
  have hφ : (𝟭 C).IsHomLift (𝟙 A) (eqToHom x.2 ≫ eqToHom y.2.symm) :=
    IsHomLift.of_fac' (𝟭 C) (𝟙 A) _ x.2 y.2 (by simp)
  refine ⟨{ default := ⟨_, hφ⟩, uniq := fun ψ ↦ Subtype.ext ?_ }⟩
  have := ψ.2
  have h := IsHomLift.fac' (𝟭 C) (𝟙 A) ψ.1
  change ψ.1 = _ at h
  simp [h]

/-- The fibres of the identity functor are connected: any two objects of a fibre are
isomorphic. -/
public theorem nonempty_iso_fiber_id (A : C) (x y : (𝟭 C).Fiber A) : Nonempty (x ≅ y) := by
  obtain ⟨hxy⟩ := unique_hom_fiber_id A x y
  obtain ⟨hyx⟩ := unique_hom_fiber_id A y x
  obtain ⟨hxx⟩ := unique_hom_fiber_id A x x
  obtain ⟨hyy⟩ := unique_hom_fiber_id A y y
  exact ⟨⟨hxy.default, hyx.default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

end Identity

/-! ### `𝒞_Λ` over itself -/

section Self

/-- The base category `𝒞_Λ`, regarded through the identity functor as a category cofibered in
groupoids over itself, is a predeformation category. -/
@[stacks 06T9 "predeformation category"]
public theorem isPredeformationCategory_id :
    IsPredeformationCategory.{u, v, w} (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) where
  cofibered := isCofiberedInGroupoids_id
  specialFiber := (CategoryTheory.equiv_punit_iff_unique _).2
    ⟨⟨Functor.Fiber.mk rfl⟩, unique_hom_fiber_id _⟩

/-- `𝒞_Λ` over itself satisfies Schlessinger's condition (S1). -/
@[stacks 06T9 "condition (S1)"]
public theorem schlessingerConditionS1_id :
    SchlessingerConditionS1 (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) where
  completion := by
    intro x₁ x₂ x f₁ f₂ _ A₁₂ g₁ g₂ hPB
    exact ⟨{ apex := A₁₂, apex_eq := rfl, toFirst := g₁, toSecond := g₂
             comm := by simpa using hPB.w
             map_toFirst := by simp
             map_toSecond := by simp }⟩

/-- `𝒞_Λ` over itself satisfies Schlessinger's condition (S2). -/
@[stacks 06T9 "condition (S2)"]
public theorem schlessingerConditionS2_id :
    SchlessingerConditionS2 (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) where
  completion := by
    intro x xε x₀ d e _ Aε g gε hPB
    exact ⟨{ apex := Aε, apex_eq := rfl, toFirst := g, toSecond := gε
             comm := by simpa using hPB.w
             map_toFirst := by simp
             map_toSecond := by simp }⟩
  comparison := by
    intro x xε x₀ d e _ Aε g gε _ P Q
    refine ⟨eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm, ?_, rfl⟩
    have hP : P.toFirst = eqToHom P.apex_eq ≫ g := P.map_toFirst
    have hQ : Q.toFirst = eqToHom Q.apex_eq ≫ g := Q.map_toFirst
    simp [hP, hQ]

/-- `𝒞_Λ` over itself satisfies the Rim–Schlessinger condition. -/
public theorem satisfiesRS_id :
    SatisfiesRS (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k)) := by
  refine ⟨isCofiberedInGroupoids_id, ?_⟩
  intro A₁ A₂ A f₁ f₂ hsurj
  obtain ⟨hc, -⟩ := ArtinianLocalAlgCat.hasPullback_of_surjective f₁ f₂ (Or.inr hsurj)
  exact ⟨Limits.PullbackCone.mk hc.fst hc.snd hc.isPullback.w,
    ⟨hc.isPullback.isLimit⟩, ⟨hc.isPullback.isLimit⟩⟩

/-- The base category `𝒞_Λ`, regarded through the identity functor as a category cofibered in
groupoids over itself, is a deformation category. -/
public theorem isDeformationCategory_id :
    IsDeformationCategory.{u, v, w} (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) where
  predeformation := isPredeformationCategory_id.{u, v, w} Λ k
  satisfiesRS := satisfiesRS_id Λ k

/-- Every fibre of the identity functor has exactly one isomorphism class. -/
public theorem subsingleton_isomorphismClasses_id {C : Type*} [Category C] (A : C) :
    Subsingleton ((isomorphismClasses (BasedCategory.ofFunctor (𝟭 C))
      isCofiberedInGroupoids_id).obj A) := by
  have h := isomorphismClasses_obj (BasedCategory.ofFunctor (𝟭 C))
    isCofiberedInGroupoids_id A
  have key : ∀ x y : Quotient (isIsomorphicSetoid
      (Functor.Fiber (BasedCategory.ofFunctor (𝟭 C)).p A)), x = y := by
    intro x y
    induction x using Quotient.ind with | _ x =>
    induction y using Quotient.ind with | _ y =>
    exact Quotient.sound (nonempty_iso_fiber_id A x y)
  exact ⟨fun a b ↦ (Equiv.cast h).injective (key _ _)⟩

/-- Every fibre of the identity functor has at least one isomorphism class, namely the class of
the object of the base over which the fibre is taken. -/
public theorem nonempty_isomorphismClasses_id {C : Type*} [Category C] (A : C) :
    Nonempty ((isomorphismClasses (BasedCategory.ofFunctor (𝟭 C))
      isCofiberedInGroupoids_id).obj A) :=
  ⟨classOf (BasedCategory.ofFunctor (𝟭 C)) isCofiberedInGroupoids_id (Functor.Fiber.mk rfl)⟩

/-- The tangent space of `𝒞_Λ` over itself has at most one element. -/
public theorem subsingleton_predeformationTangentSpace_id :
    Subsingleton (predeformationTangentSpace.{u, v, w}
      (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) (isPredeformationCategory_id Λ k)) :=
  subsingleton_isomorphismClasses_id _

/-- The tangent space of `𝒞_Λ` over itself vanishes: it has exactly one element. -/
@[stacks 06T9 "vanishing of the tangent space"]
public theorem unique_predeformationTangentSpace_id :
    Nonempty (Unique (predeformationTangentSpace.{u, v, w}
      (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) (isPredeformationCategory_id Λ k))) := by
  have := subsingleton_predeformationTangentSpace_id.{u, v, w} Λ k
  obtain ⟨x⟩ := nonempty_isomorphismClasses_id
    (C := ArtinianLocalAlgCat.{u, max v w, w} Λ k) (artinianDualNumbers.{u, w, v} Λ k)
  exact ⟨uniqueOfSubsingleton x⟩

end Self

/-! ### Formal objects of `𝒞_Λ` over itself -/

section FormalObjects

variable {Λ k}

/-- The tautological formal object of `𝒞_Λ` over itself with a prescribed complete local
algebra `R` as base: its level-`n` object is the truncation `R/𝔪_R^{n+1}` and its transition
maps are the quotient projections. -/
public noncomputable def selfFormalObject (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    FormalObject (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) where
  base := R
  level n := (AdicTruncation.functor n).obj R
  level_eq _ := rfl
  transition n := (AdicTruncation.transitionNat n).app R
  transition_lift _ := IsHomLift.map (p := 𝟭 _) _

/-- The base of `selfFormalObject R` is `R`. -/
@[simp]
public theorem selfFormalObject_base (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    (selfFormalObject.{u, v, w} R).base = R := rfl

/-- The morphism associated to the tautological formal object over `R` is the structure
functor of the restricted representable category of `R`. -/
private theorem associatedMorphism_selfFormalObject
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (P : ChosenPushforwards (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k))) :
    (associatedMorphism isCofiberedInGroupoids_id (selfFormalObject.{u, v, w} R) P).toBasedFunctor
      = restrictedCoyonedaProjection R :=
  BasedCategory.BasedFunctor.ext' (associatedMorphism isCofiberedInGroupoids_id
    (selfFormalObject.{u, v, w} R) P).toBasedFunctor.w

/-- The tautological formal object over `R` is versal exactly when the restricted
representable category of `R` is smooth over `𝒞_Λ`. -/
public theorem isVersal_selfFormalObject_iff (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    IsVersal isCofiberedInGroupoids_id (selfFormalObject.{u, v, w} R) ↔
      IsSmooth (restrictedCoyonedaProjection R) := by
  refine ⟨fun h ↦ ?_, fun h P ↦ by rwa [associatedMorphism_selfFormalObject R P]⟩
  rw [← associatedMorphism_selfFormalObject R
    (chosenPushforwardsOfCofibered _ isCofiberedInGroupoids_id)]
  exact h _

variable [IsNoetherianRing Λ] [Module.Finite Λ k]

/-- **The versality criterion for `𝒞_Λ` over itself.** The tautological formal object over `R`
is versal if and only if `Λ → R` is formally smooth in the `𝔪_R`-adic topology. -/
public theorem isVersal_selfFormalObject_iff_formallySmoothNAdic
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    IsVersal isCofiberedInGroupoids_id (selfFormalObject.{u, v, w} R) ↔
      RingHom.FormallySmoothNAdic.{max u (max v w)} (algebraMap Λ R) (maximalIdeal R) :=
  (isVersal_selfFormalObject_iff R).trans
    ((smooth_formallySmooth_flat_specialFibre_tfae R).out 1 2)

end FormalObjects

/-! ### Derivations and the base-changed module of differentials -/

section Duality

open scoped TensorProduct

variable {Λ : Type*} {R : Type*} {K : Type*} [CommRing Λ] [CommRing R] [Field K]
variable [Algebra Λ R] [Algebra Λ K] [Algebra R K] [IsScalarTower Λ R K]

/-- Two `K`-linear functionals on `K ⊗_R Ω_{R/Λ}` which agree on the elements `1 ⊗ dr`
are equal. -/
private theorem tensorFunctional_ext (F G : (K ⊗[R] Ω[R⁄Λ]) →ₗ[K] K)
    (h : ∀ r : R, F (1 ⊗ₜ[R] KaehlerDifferential.D Λ R r) =
      G (1 ⊗ₜ[R] KaehlerDifferential.D Λ R r)) : F = G := by
  refine (LinearMap.liftBaseChangeEquiv K (R := R) (M := Ω[R⁄Λ]) (N := K)).symm.injective ?_
  refine (KaehlerDifferential.linearMapEquivDerivation Λ R).injective (Derivation.ext ?_)
  intro r
  simpa only [KaehlerDifferential.linearMapEquivDerivation_apply_apply,
    LinearMap.liftBaseChangeEquiv_symm_apply] using h r

/-- The `K`-linear functional on `K ⊗_R Ω_{R/Λ}` attached to a `Λ`-derivation `R → K`. -/
private noncomputable def derivationFunctional (D : Derivation Λ R K) :
    (K ⊗[R] Ω[R⁄Λ]) →ₗ[K] K :=
  LinearMap.liftBaseChange K D.liftKaehlerDifferential

private theorem derivationFunctional_apply (D : Derivation Λ R K) (r : R) :
    derivationFunctional D (1 ⊗ₜ[R] KaehlerDifferential.D Λ R r) = D r := by
  rw [derivationFunctional, LinearMap.liftBaseChange_one_tmul,
    Derivation.liftKaehlerDifferential_comp_D]

/-- The base-change map sends `1 ⊗ dr` to the differential of the image of `r`. -/
private theorem mapBaseChange_one_tmul_D (r : R) :
    KaehlerDifferential.mapBaseChange Λ R K (1 ⊗ₜ[R] KaehlerDifferential.D Λ R r) =
      KaehlerDifferential.D Λ K (algebraMap R K r) := by
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]

/-- **Duality between derivations and differentials.** For a `Λ`-algebra `R` with a surjective
map to a field `K`, the canonical base-change map `K ⊗_R Ω_{R/Λ} → Ω_{K/Λ}` is bijective
precisely when every `Λ`-derivation `R → K` is the restriction of a `Λ`-derivation of `K`. -/
public theorem bijective_mapBaseChange_iff_forall_exists_derivation
    (hsurj : Function.Surjective (algebraMap R K)) :
    Function.Bijective (KaehlerDifferential.mapBaseChange Λ R K) ↔
      ∀ D : Derivation Λ R K, ∃ δ : Derivation Λ K K,
        ∀ r : R, D r = δ (algebraMap R K r) := by
  constructor
  · intro hbij D
    let e := LinearEquiv.ofBijective (KaehlerDifferential.mapBaseChange Λ R K) hbij
    refine ⟨KaehlerDifferential.linearMapEquivDerivation Λ K
      ((derivationFunctional D).comp (e.symm : Ω[K⁄Λ] →ₗ[K] K ⊗[R] Ω[R⁄Λ])), fun r ↦ ?_⟩
    have hpre : e.symm (KaehlerDifferential.D Λ K (algebraMap R K r)) =
        1 ⊗ₜ[R] KaehlerDifferential.D Λ R r :=
      e.injective ((e.apply_symm_apply _).trans (mapBaseChange_one_tmul_D r).symm)
    rw [KaehlerDifferential.linearMapEquivDerivation_apply_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, hpre, derivationFunctional_apply]
  · intro hD
    have hker : ∀ z : K ⊗[R] Ω[R⁄Λ],
        KaehlerDifferential.mapBaseChange Λ R K z = 0 → z = 0 := by
      intro z hz
      by_contra hne
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hne
      obtain ⟨δ, hδ⟩ := hD (KaehlerDifferential.linearMapEquivDerivation Λ R
        ((φ.restrictScalars R).comp (TensorProduct.mk R K Ω[R⁄Λ] 1)))
      have hcomp : φ = (δ.liftKaehlerDifferential).comp
          (KaehlerDifferential.mapBaseChange Λ R K) := by
        refine tensorFunctional_ext _ _ fun r ↦ ?_
        rw [LinearMap.comp_apply, mapBaseChange_one_tmul_D,
          Derivation.liftKaehlerDifferential_comp_D]
        simpa only [KaehlerDifferential.linearMapEquivDerivation_apply_apply,
          LinearMap.restrictScalars_apply, LinearMap.comp_apply, TensorProduct.mk_apply]
          using hδ r
      exact hφ (by rw [hcomp, LinearMap.comp_apply, hz, map_zero])
    refine ⟨fun x y hxy ↦ ?_, KaehlerDifferential.mapBaseChange_surjective Λ R K hsurj⟩
    exact sub_eq_zero.mp (hker (x - y) (by rw [map_sub, hxy, sub_self]))

end Duality

/-! ### Minimal versal formal objects of `𝒞_Λ` over itself -/

section Minimal

variable {Λ k}

/-- The condition that the injection `Der_Λ(k, k) → Der_Λ(R, k)`, given by composing with the
augmentation `q : R → k`, is surjective: every `Λ`-derivation of `R` with values in `k`
vanishes on the maximal ideal. -/
public def ResidueDerivationSurjective (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) : Prop :=
  letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
  ∀ D : Derivation Λ R k, ∃ δ : Derivation Λ k k, ∀ r : R, D r = δ (residueHom R r)

/-- The differential of a versal formal object of `𝒞_Λ` over itself is bijective on
`Der_Λ(k, k)`-orbits exactly when every `Λ`-derivation of its base with values in `k` comes from
a `Λ`-derivation of `k`. -/
public theorem hasBijectiveDifferentialOnDerivationOrbits_id_iff
    (ξ : FormalObject (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)))
    (hξ : IsVersal isCofiberedInGroupoids_id ξ) :
    HasBijectiveDifferentialOnDerivationOrbits.{u, v, w}
        (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) (isPredeformationCategory_id Λ k) ξ ↔
      ResidueDerivationSurjective.{u, v, w} ξ.base := by
  have := subsingleton_predeformationTangentSpace_id.{u, v, w} Λ k
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  constructor
  · intro h D
    obtain ⟨y, hy, -⟩ := h.1 (standardToDerivation ξ 0)
    obtain ⟨z, hz, -⟩ := h.1 (standardToDerivation ξ D)
    obtain ⟨δ, hδ⟩ :=
      (h.2.2.2 (standardToDerivation ξ 0) (standardToDerivation ξ D) y z hy hz).mp
      ⟨0, by
        rw [(derivationAction.{u, v, w} _ (isPredeformationCategory_id Λ k)).zero_action]
        exact Subsingleton.elim z y⟩
    refine ⟨δ, fun r ↦ ?_⟩
    simpa [standardToDerivation_apply ξ D r, standardToDerivation_apply ξ 0 r] using hδ r
  · intro hD
    dsimp only [HasBijectiveDifferentialOnDerivationOrbits]
    refine ⟨existsUnique_derivationDifferentialGraph _ ξ,
      fun y ↦ exists_derivationDifferentialGraph_of_versal _ _ (schlessingerConditionS1_id Λ k)
        (schlessingerConditionS2_id Λ k) ξ hξ y,
      fun D δ y hy ↦ exists_derivationDifferentialGraph_derivationAction _ _ ξ D δ y hy, ?_⟩
    intro D E y z hy hz
    refine ⟨fun _ ↦ ?_,
      fun h ↦ exists_derivationAction_eq_of_sub_residueCompDerivation _ _ ξ D E y z hy hz h⟩
    obtain ⟨δD, hδD⟩ := hD (derivationToStandard ξ D)
    obtain ⟨δE, hδE⟩ := hD (derivationToStandard ξ E)
    refine ⟨δE - δD, fun r ↦ ?_⟩
    rw [(derivationToStandard_apply ξ D r).symm.trans (hδD r),
      (derivationToStandard_apply ξ E r).symm.trans (hδE r), Derivation.sub_apply]
    abel

/-- The structure functor of `𝒞_Λ` over itself is smooth: `𝒞_Λ` is unobstructed. -/
public theorem isSmooth_baseProjection_id :
    IsSmooth (baseProjection (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k))) := by
  intro B A f _ y x g hg
  have hy : (BasedCategory.ofFunctor
      (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k))).p.obj y = B := by cases hg; rfl
  exact ⟨y, g, 𝟙 y, hg, IsHomLift.id hy, (Category.id_comp g).symm⟩

/-- The augmentation of a complete local algebra onto its chosen residue field, read as the
structure map of the induced algebra structure, is surjective. -/
private theorem algebraMap_residueHom_surjective
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
    Function.Surjective (algebraMap R k) := by
  let : Algebra R k := (residueHom R).toRingHom.toAlgebra
  exact residueAlgHom_surjective R

variable [IsNoetherianRing Λ] [Module.Finite Λ k]

/-- Every `Λ`-derivation of the base of a minimal versal formal object of `𝒞_Λ` over itself with
values in `k` comes from a `Λ`-derivation of `k`. -/
private theorem residueDerivationSurjective_of_isMinimalVersal
    (ξ : FormalObject (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k)))
    (hξ : IsMinimalVersal isCofiberedInGroupoids_id ξ) :
    ResidueDerivationSurjective.{u, v, w} ξ.base :=
  (hasBijectiveDifferentialOnDerivationOrbits_id_iff ξ hξ.1).mp
    (minimalVersal_hasBijectiveDifferentialOnDerivationOrbits _
      (isPredeformationCategory_id Λ k) (schlessingerConditionS2_id Λ k) ξ hξ)

/-- **The miniversality criterion for `𝒞_Λ` over itself.** The tautological formal object over
`R` is a minimal versal formal object if and only if `Λ → R` is formally smooth in the
`𝔪_R`-adic topology and every `Λ`-derivation `R → k` comes from a `Λ`-derivation of `k`. -/
public theorem isMinimalVersal_selfFormalObject_iff
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    IsMinimalVersal isCofiberedInGroupoids_id (selfFormalObject.{u, v, w} R) ↔
      RingHom.FormallySmoothNAdic.{max u (max v w)} (algebraMap Λ R) (maximalIdeal R) ∧
        ResidueDerivationSurjective.{u, v, w} R := by
  constructor
  · intro h
    exact ⟨(isVersal_selfFormalObject_iff_formallySmoothNAdic R).mp h.1,
      residueDerivationSurjective_of_isMinimalVersal _ h⟩
  · rintro ⟨hfs, hds⟩
    have hv := (isVersal_selfFormalObject_iff_formallySmoothNAdic R).mpr hfs
    exact isMinimalVersal_of_hasBijectiveDifferentialOnDerivationOrbits
      (isPredeformationCategory_id Λ k) _ hv
      ((hasBijectiveDifferentialOnDerivationOrbits_id_iff _ hv).mpr hds)

/-- Every `Λ`-derivation of the smooth model of Stacks 06SM with values in `k` comes from a
`Λ`-derivation of `k`. -/
public theorem residueDerivationSurjective_smoothModel :
    ResidueDerivationSurjective.{u, u, w} (smoothModel.{u, w} (Λ := Λ) (k := k)) := by
  let : Algebra (smoothModel.{u, w} (Λ := Λ) (k := k)) k :=
    (residueHom (smoothModel.{u, w} (Λ := Λ) (k := k))).toRingHom.toAlgebra
  let : IsScalarTower Λ (smoothModel.{u, w} (Λ := Λ) (k := k)) k :=
    IsScalarTower.of_algebraMap_eq'
      (residueHom (smoothModel.{u, w} (Λ := Λ) (k := k))).comp_algebraMap.symm
  exact (bijective_mapBaseChange_iff_forall_exists_derivation
    (algebraMap_residueHom_surjective.{u, u, w} _)).mp smoothModel_mapBaseChange_bijective.{u, w}

/-- The object `R` constructed in Stacks 06SM carries a minimal versal formal object of `𝒞_Λ`
regarded as cofibered in groupoids over itself. -/
@[stacks 06T9 "the smooth model of Stacks 06SM carries a minimal versal formal object"]
public theorem isMinimalVersal_selfFormalObject_smoothModel :
    IsMinimalVersal isCofiberedInGroupoids_id
      (selfFormalObject.{u, u, w} (smoothModel.{u, w} (Λ := Λ) (k := k))) :=
  (isMinimalVersal_selfFormalObject_iff.{u, u, w} _).mpr
    ⟨smoothModel_formallySmooth.{u, w}, residueDerivationSurjective_smoothModel⟩

/-- The complete local algebra `S` underlying any minimal versal formal object of `𝒞_Λ` over
itself is formally smooth over `Λ` in the `𝔪_S`-adic topology, its module of differentials
satisfies `Ω_{S/Λ} ⊗_S k = Ω_{k/Λ}`, its conormal module satisfies `H₁(L_{k/Λ}) = 𝔪_S/𝔪_S²`, and
it is isomorphic to the object constructed in Stacks 06SM. -/
@[stacks 06T9 "the cotangent identifications and the comparison with Stacks 06SM"]
public theorem isMinimalVersal_id_base_properties
    (ξ : FormalObject (𝟭 (ArtinianLocalAlgCat.{u, max u w, w} Λ k)))
    (hξ : IsMinimalVersal isCofiberedInGroupoids_id ξ) :
    letI : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
    letI : IsScalarTower Λ ξ.base k :=
      IsScalarTower.of_algebraMap_eq' (residueHom ξ.base).comp_algebraMap.symm
    RingHom.FormallySmoothNAdic.{max u w} (algebraMap Λ ξ.base) (maximalIdeal ξ.base) ∧
      Function.Bijective (KaehlerDifferential.mapBaseChange Λ ξ.base k) ∧
        Function.Bijective (Algebra.H1Cotangent.map Λ ξ.base k k) ∧
          Nonempty (ξ.base ≅ smoothModel.{u, w} (Λ := Λ) (k := k)) := by
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  let : IsScalarTower Λ ξ.base k :=
    IsScalarTower.of_algebraMap_eq' (residueHom ξ.base).comp_algebraMap.symm
  have hfs : RingHom.FormallySmoothNAdic.{max u w}
      (algebraMap Λ ξ.base) (maximalIdeal ξ.base) :=
    (isSmooth_baseProjection_iff_formallySmoothNAdic
      (isPredeformationCategory_id Λ k) ξ hξ.1).mp isSmooth_baseProjection_id.{u, u, w}
  have hds : ResidueDerivationSurjective.{u, u, w} ξ.base :=
    residueDerivationSurjective_of_isMinimalVersal ξ hξ
  have hmbc : Function.Bijective (KaehlerDifferential.mapBaseChange Λ ξ.base k) :=
    (bijective_mapBaseChange_iff_forall_exists_derivation
      (algebraMap_residueHom_surjective ξ.base)).mpr hds
  have hkill : ∃ n : ℕ, 1 ≤ n ∧
      (maximalIdeal ξ.base) ^ n ≤ RingHom.ker (algebraMap ξ.base k) := by
    refine ⟨1, le_rfl, fun z hz ↦ RingHom.mem_ker.mpr ?_⟩
    have hker : z ∈ RingHom.ker (residueAlgHom ξ.base).toRingHom := by
      rwa [residueAlgHom_ker, ← pow_one (maximalIdeal ξ.base)]
    rw [show algebraMap ξ.base k z = residueHom ξ.base z from rfl,
      ← DFunLike.congr_fun (residueAlgHom_eq_residueHom ξ.base) z]
    exact hker
  exact ⟨hfs, hmbc, h1Cotangent_map_bijective_of_formallySmoothNAdic
    (maximalIdeal ξ.base) hfs hkill hmbc,
    (isomorphic_of_isMinimalVersal (isPredeformationCategory_id Λ k) ξ
      (selfFormalObject.{u, u, w} (smoothModel.{u, w} (Λ := Λ) (k := k))) hξ
      isMinimalVersal_selfFormalObject_smoothModel).map FormalObject.projection.mapIso⟩

end Minimal

end Deformation

end

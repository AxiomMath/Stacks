module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRankIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.RingTheory.Ext.DerivedHomFiniteness
public import StacksFrontier.Homology.DerivedLinear

/-!
# Finiteness of cohomology over a Noetherian base: the dévissage conditions

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`Γ(Y) = Γ(Y, 𝒪_Y)` be the ring of global regular functions on `Y`.  For an `𝒪_X`-module `F`
consider the property

> `HasFiniteGlobalCohomologyOver f F`: every cohomology module `H^n(X, F)`, read as a
> `Γ(Y)`-module along the ring map `Γ(Y) ⟶ Γ(X)` of Stacks 0732, is finite.

When `Γ(Y)` is Noetherian, this property satisfies the two-out-of-three condition and the
direct-summand condition of the dévissage of [Stacks, Tag 08AN], so on a Noetherian algebraic
space it holds for every coherent module as soon as every reduced closed subspace with
irreducible point set is the scheme-theoretic support of a coherent module with the property.

## Main definitions

* `AlgebraicGeometry.Space.HasFiniteGlobalCohomologyOver`: the property above.

## Main results

* `AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_twoOutOfThree`: condition (1) of
  [Stacks, Tag 08AN].
* `AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_directSumDescent`: condition (2).
* `AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_of_isZero`: the zero module has the
  property.
* `AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_of_witness`: **the dévissage**: on a
  Noetherian algebraic space, if every reduced closed subspace with irreducible point set carries
  a coherent module with the property and with that scheme-theoretic support (condition (3)), then
  every coherent module has the property.

## References

* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Finiteness of cohomology over the global functions of the target.**  For `f : X ⟶ Y` and
an `𝒪_X`-module `F`: every cohomology module `H^n(X, F)`, read as a `Γ(Y, 𝒪_Y)`-module along the
ring map of Stacks 0732, is finite. -/
def HasFiniteGlobalCohomologyOver (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  ∀ n : ℕ, Module.Finite
    (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
    ((globalSectionsRestrictScalars B S hS f).obj
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).obj F))

/-- Over a Noetherian ring of global functions of the target, the middle term of an exact
sequence of modules over the global functions of the source is finite over the target when its
outer terms are. -/
private theorem moduleFinite_restrictScalars_of_exact (f : X ⟶ Y)
    [IsNoetherianRing
      (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)]
    (E : ShortComplex (ModuleCat.{u + 1}
      (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)))
    (hE : E.Exact)
    (h₁ : Module.Finite
      (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
      ((globalSectionsRestrictScalars B S hS f).obj E.X₁))
    (h₃ : Module.Finite
      (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
      ((globalSectionsRestrictScalars B S hS f).obj E.X₃)) :
    Module.Finite (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
      ((globalSectionsRestrictScalars B S hS f).obj E.X₂) := by
  rw [ShortComplex.moduleCat_exact_iff] at hE
  exact StacksDraft.DerivedHomFiniteness.module_finite_of_exact
    ((globalSectionsRestrictScalars B S hS f).map E.f).hom
    ((globalSectionsRestrictScalars B S hS f).map E.g).hom hE

/-- **Condition (1) of Stacks 08AN** for finiteness of cohomology over a Noetherian ring of
global functions of the target: for a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of
coherent modules, if two of the `Fᵢ` have finite cohomology then so does the third. -/
theorem hasFiniteGlobalCohomologyOver_twoOutOfThree (f : X ⟶ Y)
    [IsNoetherianRing
      (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)] :
    TwoOutOfThreeCoherent B S hS X (HasFiniteGlobalCohomologyOver B S hS f) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have : EnoughInjectives (Modules.{u, u} B S hS X.1 X.2) :=
    enoughInjectives_modules B S hS X.1 X.2
  intro E hE _ _ _
  obtain ⟨delta, hmono, hwin⟩ :=
    Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅ hE
      (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  refine ⟨fun H₁ H₃ n ↦ ?_, fun H₂ H₃ n ↦ ?_, fun H₁ H₂ n ↦ ?_⟩
  · exact moduleFinite_restrictScalars_of_exact B S hS f _ ((hwin n).exact 0) (H₁ n) (H₃ n)
  · cases n with
    | zero =>
      have hm : Mono (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map E.f) := hmono
      have hinj := (ModuleCat.mono_iff_injective _).1 hm
      have := H₂ 0
      exact Module.Finite.of_injective
        ((globalSectionsRestrictScalars B S hS f).map
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map E.f)).hom
        hinj
    | succ n =>
      exact moduleFinite_restrictScalars_of_exact B S hS f _ ((hwin n).exact 2) (H₃ n)
        (H₂ (n + 1))
  · exact moduleFinite_restrictScalars_of_exact B S hS f _ ((hwin n).exact 1) (H₂ n) (H₁ (n + 1))

/-- **A retract of a module with finite cohomology has finite cohomology.** -/
theorem hasFiniteGlobalCohomologyOver_of_retract (f : X ⟶ Y) {F C : Modules.{u, u} B S hS X.1 X.2}
    (i : F ⟶ C) (p : C ⟶ F) (hip : i ≫ p = 𝟙 F) (hC : HasFiniteGlobalCohomologyOver B S hS f C) :
    HasFiniteGlobalCohomologyOver B S hS f F := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  unfold HasFiniteGlobalCohomologyOver at hC ⊢
  intro _ n
  let H := (globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n ⋙
      globalSectionsRestrictScalars B S hS f
  have hsplit : H.map i ≫ H.map p = 𝟙 _ := by rw [← H.map_comp, hip, H.map_id]
  have hsurj : Function.Surjective (H.map p).hom := fun x =>
    ⟨(H.map i).hom x, by simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 hsplit) x⟩
  exact Module.Finite.of_surjective (hM := hC n) (H.map p).hom hsurj

/-- **Condition (2) of Stacks 08AN** for finiteness of cohomology over the global functions of
the target: if the direct sum of `r ≥ 1` copies of a module has finite cohomology, so does the
module. -/
theorem hasFiniteGlobalCohomologyOver_directSumDescent (f : X ⟶ Y) :
    ClosedUnderDirectSumDescent B S hS X (HasFiniteGlobalCohomologyOver B S hS f) := by
  intro F r hr hP
  exact hasFiniteGlobalCohomologyOver_of_retract B S hS f
    (biproduct.ι (fun _ : Fin r => F) ⟨0, hr⟩) (biproduct.π (fun _ : Fin r => F) ⟨0, hr⟩)
    (biproduct.ι_π_self _ _) hP

/-- The zero module has finite cohomology over any base. -/
theorem hasFiniteGlobalCohomologyOver_of_isZero (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : IsZero M) : HasFiniteGlobalCohomologyOver B S hS f M := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  unfold HasFiniteGlobalCohomologyOver
  intro _ n
  have := Stacks.DerivedLinear.rightDerived_additive (globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) n
  have hz := ((globalSectionsRestrictScalars B S hS f).map_isZero
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).map_isZero hM))
  have : Subsingleton ((globalSectionsRestrictScalars B S hS f).obj
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).obj M)) :=
    ModuleCat.subsingleton_of_isZero hz
  infer_instance

/-- **The dévissage of Stacks 08AN for finiteness of cohomology.**  Let `X` be a Noetherian
algebraic space, `f : X ⟶ Y` a morphism with `Γ(Y, 𝒪_Y)` Noetherian, and suppose that every
reduced closed subspace of `X` with irreducible point set is the scheme-theoretic support of a
coherent `𝒪_X`-module whose cohomology is finite over `Γ(Y, 𝒪_Y)`.  Then every coherent
`𝒪_X`-module has cohomology finite over `Γ(Y, 𝒪_Y)`. -/
theorem hasFiniteGlobalCohomologyOver_of_witness (f : X ⟶ Y)
    [IsNoetherianRing
      (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)]
    (hZtop : B.Contains (⊤_ Scheme.{u})) (hX : IsNoetherian B S hS hZtop X.1)
    (hwit : HasCoherentWitnessOnIntegralSubspaces B S hS X (HasFiniteGlobalCohomologyOver B S hS f))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) :
    HasFiniteGlobalCohomologyOver B S hS f M :=
  property_of_integralWitness_and_twoOutOfThree' B S hS hZtop X hX
    (fun N hN => hasIdealDevissage_of_isCoherent B S hS hZtop X hX N hN)
    (HasFiniteGlobalCohomologyOver B S hS f) (hasFiniteGlobalCohomologyOver_of_isZero B S hS f)
    (hasFiniteGlobalCohomologyOver_twoOutOfThree B S hS f)
    (hasFiniteGlobalCohomologyOver_directSumDescent B S hS f) hwit M hM

end AlgebraicGeometry.Space

end

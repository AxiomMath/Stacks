module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpec
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DirectImageInDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.BoundedDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the punctured cone over a projective spectrum

Let `A` be a nonnegatively graded ring, `P = Proj A`, `Z = Spec A₀`, and let `L = Proj B` be the
cone over `P` attached to cone data `B` for `A`, with cone projection `π : L ⟶ P`. The punctured
cone `U ⊆ L`, the part of `L` lying over `X ∖ V(A₊)`, is affine over `P`, and its direct-image
algebra is the algebra of all integral twists, so that `U = Spec_P(⨁_{m ∈ Z} 𝒪_P(m))`. For a
quasi-coherent `𝒪_P`-module `𝓕` with pullback `𝓕_U = (π|_U)^*𝓕` this gives

  `RΓ(U, 𝓕_U) = ⨁_{m ∈ Z} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`,

the decomposition of the derived global sections of `𝓕_U` over the grading.

The argument is the one of the source. The restricted projection `π|_U` is affine, so its derived
direct image collapses, `R(π|_U)_*(𝓕_U[0]) = ((π|_U)_*𝓕_U)[0]`; the composition formula for
derived direct image replaces `RΓ(U, -)` by `RΓ(P, R(π|_U)_*(-))`; and the identification of
`(π|_U)_*𝓕_U` with `⨁_{m ∈ Z} 𝓕 ⊗ 𝒪_P(m)` turns the result into the derived direct image of a
direct sum, through which the direct sum passes because derived direct image along a
quasi-compact quasi-separated morphism commutes with direct sums of a family concentrated in a
single degree.

## Main results

* `Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_int_singleFunctor`:
  placing a module in a fixed degree of the derived category preserves `ℤ`-indexed direct sums.
* `Stacks.Duality.DerivedPushforward.sigmaIntSingleFunctorIso`: `Rf_*` commutes with a
  `ℤ`-indexed direct sum of modules placed in one degree, for `f` quasi-compact and
  quasi-separated.
* `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIso`: **the displayed
  decomposition**, granted the identification of `(π|_U)_*𝓕_U` with `⨁_{m ∈ Z} 𝓕 ⊗ 𝒪_P(m)`.

## Implementation notes

*Derived global sections are read as derived direct image to the affine base.* `RΓ(U, 𝓕_U)` is
`R(π|_U ≫ P → Z)_*(𝓕_U[0])` and `RΓ(P, 𝓕 ⊗ 𝒪_P(m))` is `R(P → Z)_*((𝓕 ⊗ 𝒪_P(m))[0])`, both
objects of `D(𝒪_Z)`. These correspond to the complexes of `A₀`-modules the source writes under
the equivalence `D(A₀) ≃ D_QCoh(𝒪_Z)` for the affine scheme `Z`; that equivalence is not applied
here, because the composition formula for derived direct image and the direct-sum statement used
below are available at the locally small model of the derived categories, while the comparison of
derived global sections over a base ring with derived direct image is not.

*Which direct-sum statement.* The family `m ↦ 𝓕 ⊗ 𝒪_P(m)` is concentrated in degree zero, so the
base case of the dévissage behind [Stacks, Tag 08DZ] suffices:
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_singleFunctor_obj` asks only that the
morphism be quasi-compact and quasi-separated, needs no quasi-coherence, and fixes no model of
the derived categories. The uniform cohomological bound that the full tag adds, for an arbitrary
family, is not needed and is available only at the standard model, where the composition formula
is not.

*The index universe.* The derived category of `𝒪_X`-modules has direct sums indexed by types of
the scheme universe, whereas the grading of the twists is indexed by `ℤ`, which lives in
`Type 0`. The two statements below move between `ℤ` and `ULift ℤ`: the shape `Discrete ℤ` is
equivalent to `Discrete (ULift ℤ)`, which gives the direct sums and the preservation statement,
and `CategoryTheory.Limits.Sigma.whiskerEquiv` reindexes the direct sums themselves.

*What is assumed here.* The identification `(π|_U)_*𝓕_U = ⨁_{m ∈ Z} 𝓕 ⊗ 𝒪_P(m)` is a hypothesis
of the declaration below. It is the module-sheaf form, tensored with `𝓕`, of the presentation
`U = Spec_P(⨁_{m ∈ Z} 𝒪_P(m))` of [Stacks, Tag 0EKG]. It is discharged in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecPuncturedConeProjectionFormula`, by the
projection formula along `π|_U` out of
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso`; that
module is where [Stacks, Tag 0EKH] is stated with nothing assumed and where its `stacks`
attribute sits.

## References

* [Stacks Project, Tag 0EKH](https://stacks.math.columbia.edu/tag/0EKH)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Duality (derivedPushforward derivedPushforwardCompIso)

universe u

namespace Stacks.Duality.DerivedPushforward

/-- `D(𝒪_X)` has `ℤ`-indexed direct sums: the shape `Discrete ℤ` is equivalent to the shape
`Discrete (ULift ℤ)`, whose index type lives in the scheme universe. -/
instance hasColimitsOfShape_discrete_int_derivedCategory (X : Scheme.{u}) :
    HasColimitsOfShape (Discrete ℤ) (DerivedCategory X.Modules) :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℤ)))

/-- **Placing a module in a fixed degree of the derived category preserves `ℤ`-indexed direct
sums.** This is
`Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_singleFunctor` at the index
type `ULift ℤ`, transported along the equivalence `Discrete (ULift ℤ) ≌ Discrete ℤ`. -/
theorem preservesColimitsOfShape_discrete_int_singleFunctor (X : Scheme.{u}) (a : ℤ) :
    PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.singleFunctor X.Modules a) :=
  have := preservesColimitsOfShape_discrete_singleFunctor (X := X) a (ULift.{u, 0} ℤ)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℤ))) _

/-- **`Rf_*` commutes with a `ℤ`-indexed direct sum of modules placed in a single degree**, for
`f` quasi-compact and quasi-separated. The comparison morphism is invertible at such a family
indexed by a type of the scheme universe
(`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_singleFunctor_obj`), and the two direct
sums are reindexed between `ℤ` and `ULift ℤ`. -/
def sigmaIntSingleFunctorIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (a : ℤ) (M : ℤ → X.Modules) :
    (∐ fun m : ℤ => (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj (M m))) ≅
      (derivedPushforward f).obj
        (∐ fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m)) :=
  have := isIso_sigmaComparison_singleFunctor_obj f a (fun k : ULift.{u, 0} ℤ => M k.down)
  Limits.Sigma.whiskerEquiv (Equiv.ulift.{u, 0} (α := ℤ)).symm
      (g := fun k : ULift.{u, 0} ℤ => (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj (M k.down)))
      (fun _ => Iso.refl _) ≪≫
    asIso (sigmaComparison (derivedPushforward f)
      (fun k : ULift.{u, 0} ℤ =>
        (DerivedCategory.singleFunctor X.Modules a).obj (M k.down))) ≪≫
    (derivedPushforward f).mapIso
      (Limits.Sigma.whiskerEquiv (Equiv.ulift.{u, 0} (α := ℤ))
        (g := fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m))
        (fun _ => Iso.refl _))

end Stacks.Duality.DerivedPushforward

namespace Stacks.AlgebraicGeometry.ProjAndSpec

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (c : ConeData 𝒜 ℬ)

/-- **The cone projection restricted to the punctured cone**, `π|_U : U ⟶ P`. It is affine, by
`Stacks.AlgebraicGeometry.ProjAndSpec.isAffineHom_pi_restrict`. -/
abbrev puncturedConeProj : (openUInL c).toScheme ⟶ AlgebraicGeometry.Proj 𝒜 :=
  (openUInL c).ι ≫ pi c

/-- **The pullback of a module sheaf to the punctured cone**, `𝓕_U = (π|_U)^*𝓕`. -/
abbrev puncturedConePullback (F : (AlgebraicGeometry.Proj 𝒜).Modules) :
    (openUInL c).toScheme.Modules :=
  (Scheme.Modules.pullback (puncturedConeProj c)).obj F

/-- **`RΓ(U, 𝓕_U) = ⨁_{m ∈ Z} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`.** Derived global sections of the
pullback of a quasi-coherent `𝒪_P`-module `𝓕` to the punctured cone decompose as the direct sum,
over all integers `m`, of the derived global sections of the `m`-th twist of `𝓕`; both sides are
read as derived direct images to `Z = Spec A₀`.

The hypothesis `hcone` is the identification `(π|_U)_*𝓕_U = ⨁_{m ∈ Z} 𝓕 ⊗ 𝒪_P(m)` coming from
the presentation `U = Spec_P(⨁_{m ∈ Z} 𝒪_P(m))` of [Stacks, Tag 0EKG]. Given it, the proof is:
the composition formula for derived direct image, the collapse of `R(π|_U)_*` on a quasi-coherent
module along the affine morphism `π|_U` ([Stacks, Tag 01XC]), and the passage of a `ℤ`-indexed
direct sum concentrated in one degree through `R(P → Z)_*`, which is quasi-compact because `P`
is and quasi-separated because `P` is separated over `Z`.

`hcone` is discharged by
`Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConePushforwardPullbackCoproductIso`, and
`Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoTruncation` — which is
where the `stacks` attribute for [Stacks, Tag 0EKH] sits — is this isomorphism for the cone of
the truncation algebra, with nothing assumed. -/
def derivedPushforwardPuncturedConeIso [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent]
    (hcone : (Scheme.Modules.pushforward (puncturedConeProj c)).obj
        (puncturedConePullback c F) ≅ ∐ fun m : ℤ => twistSheafOfModules 𝒜 F m) :
    (derivedPushforward (puncturedConeProj c ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (puncturedConePullback c F)) ≅
      ∐ fun m : ℤ => (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistSheafOfModules 𝒜 F m)) :=
  have : IsAffineHom (puncturedConeProj c) := isAffineHom_pi_restrict c
  have : PreservesColimitsOfShape (Discrete ℤ)
      (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0) :=
    Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_int_singleFunctor _ 0
  have : IsIso (sigmaComparison
      (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0)
      (fun m : ℤ => twistSheafOfModules 𝒜 F m)) :=
    isIso_sigmaComparison_of_preservesColimit _ _ inferInstance
  ((derivedPushforwardCompIso (puncturedConeProj c)
      (AlgebraicGeometry.Proj.toSpecZero 𝒜)).app _).symm ≪≫
    (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).mapIso
      ((Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardSingleIso
          (puncturedConeProj c) (puncturedConePullback c F)).symm ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso hcone ≪≫
        (asIso (sigmaComparison
          (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0)
          (fun m : ℤ => twistSheafOfModules 𝒜 F m))).symm) ≪≫
    (Stacks.Duality.DerivedPushforward.sigmaIntSingleFunctorIso
      (AlgebraicGeometry.Proj.toSpecZero 𝒜) 0 (fun m : ℤ => twistSheafOfModules 𝒜 F m)).symm

end Stacks.AlgebraicGeometry.ProjAndSpec

end

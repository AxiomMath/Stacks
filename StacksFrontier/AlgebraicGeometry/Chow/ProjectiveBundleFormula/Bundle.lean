module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.Properness
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TautologicalMap

/-!
# The projective bundle of a finite locally free module, for intersection theory

Let `X` be a scheme and `ℰ` a finite locally free `𝒪_X`-module. The projective bundle
`π : 𝐏(ℰ) = Proj_X(Sym(ℰ)) ⟶ X` of [Stacks, Tag 02TV] with its twist `𝒪_{𝐏(ℰ)}(1)` is
`Stacks.SymGraded.schemeProjectiveBundle` with
`Stacks.ProjectiveBundleSplitting.tautologicalTwist`. This file defines the bundle, its
projection, its twist, and — over a base situation of chapter 42 — the first Chern class cap
operator `c₁(𝒪(1)) ∩ -` on its Chow groups, whose factoring through rational equivalence is
[Stacks, Tag 02TI], `Stacks.Chow.firstChernCapFactorsEverywhere`.

## Main definitions

* `Stacks.Chow.bundle` — the scheme `𝐏(ℰ)`.
* `Stacks.Chow.bundleProj` — its projection `π : 𝐏(ℰ) ⟶ X`.
* `Stacks.Chow.bundleTwist` — the twist `𝒪_{𝐏(ℰ)}(1)`.
* `Stacks.Chow.bundleTwistCap` — the cap operator `c₁(𝒪_{𝐏(ℰ)}(1)) ∩ -`.

## References

* [Stacks Project, Tag 02TV](https://stacks.math.columbia.edu/tag/02TV)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open Stacks.SymGraded

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The homogeneous pieces of the symmetric algebra of a finite locally free module are
quasi-coherent. -/
alias bundlePieces := Stacks.ProjectiveBundleSplitting.isQuasicoherentPieces_of_isFiniteLocallyFree

/-- **The projective bundle `𝐏(ℰ) = Proj_X(Sym(ℰ))`** of a finite locally free module. -/
def bundle : Scheme.{u} :=
  (schemeProjectiveBundle E (bundlePieces E)).scheme

/-- **The projection `π : 𝐏(ℰ) ⟶ X`.** -/
def bundleProj : bundle E ⟶ X :=
  schemeProjectiveBundleToBase E (bundlePieces E)

/-- **The twist `𝒪_{𝐏(ℰ)}(1)`**, normalized so that `π_*𝒪(1) = ℰ`; it receives the
tautological surjection `π^*ℰ ⟶ 𝒪(1)`. -/
def bundleTwist : (bundle E).Modules :=
  Stacks.ProjectiveBundleSplitting.tautologicalTwist E (bundlePieces E)

/-- The projection of the projective bundle is proper. -/
instance isProper_bundleProj : IsProper (bundleProj E) :=
  haveI : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  Stacks.ProjectiveBundleSplitting.isProper_schemeProjectiveBundleToBase E (bundlePieces E)

/-- The twist is invertible. -/
instance isInvertible_bundleTwist :
    AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).sheaf.obj
      (bundle E).ringCatSheaf.property (bundleTwist E) :=
  haveI : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E (bundlePieces E)

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The composite of the projection `π : 𝐏(ℰ) ⟶ X` with a morphism `X ⟶ S` locally of finite
type is locally of finite type. -/
instance locallyOfFiniteType_bundleProj_comp :
    LocallyOfFiniteType (bundleProj E ≫ sX) :=
  haveI : LocallyOfFiniteType (bundleProj E) := inferInstance
  inferInstance

/-- **The cap operator `c₁(𝒪_{𝐏(ℰ)}(1)) ∩ -`** on the Chow groups of the projective bundle, over
a base situation of chapter 42. Its component rule is the one of [Stacks, Tag 02SO] of the
twist, and its factoring through rational equivalence is [Stacks, Tag 02TI]. -/
def bundleTwistCap : ChernCapOperator C (bundleProj E ≫ sX) :=
  invertibleChernCapOperator C (bundleProj E ≫ sX) (bundleTwist E)
    (fun k => firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k
      (bundleProj E ≫ sX) (bundleTwist E))

end Stacks.Chow

end

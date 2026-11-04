module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula

/-!
# The projective bundle of a module of constant rank as a bundle datum, and its Segre pushforward

For `ℰ` finite locally free of rank `n + 1` on `X` locally of finite type over the base of chapter
42, the projection `π : 𝐏(ℰ) ⟶ X` of `Stacks.Chow.bundle` is flat, proper, locally of finite type
and of relative dimension `n` (Stacks 02TX, `Stacks.Chow.flat_bundleProj` and its siblings), and
the twist `𝒪(1)` gives the cap operator `Stacks.Chow.bundleTwistCap`. This file packages these as
the inputs of the parametric relation `Stacks.Chow.ProjectiveBundleChernRelation` and of
`Stacks.Chow.IsChernCapFamily`, and defines the
operation

  `Stacks.Chow.GenuineChern.segre ℰ : CH_k(X) ⟶ CH_{k-1}(X)`,  `α ↦ π_*(c₁(𝒪(1))^{n+1} ∩ π^*α)`,

which by `Stacks.Chow.chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily` is the
first Chern class `c₁(ℰ) ∩ α` of [Stacks, Tag 02U0] and [Stacks, Tag 02U6], granted the top half of
[Stacks, Tag 02TW]. `Stacks.Chow.GenuineChern.firstChern` extends it by zero to rank zero.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable {X : Scheme.{u}} (E : X.Modules)

/-- A module of rank `r` is finite locally free. -/
theorem isFiniteLocallyFree_of_rank (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r

section

variable (n : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

include n

/-- `Stacks.Chow.flat_bundleProj`, with the finite local freeness of `ℰ` an instance. -/
theorem flat_bundleProj : Flat (bundleProj E) :=
  Stacks.Chow.flat_bundleProj E n

/-- `Stacks.Chow.locallyOfFiniteType_bundleProj`, with the finite local freeness of `ℰ` an
instance. -/
theorem locallyOfFiniteType_bundleProj : LocallyOfFiniteType (bundleProj E) :=
  Stacks.Chow.locallyOfFiniteType_bundleProj E n

/-- `Stacks.Chow.relativeDimension_bundleProj`, in the form `r - 1` for the rank `r = n + 1` that
the relation of Stacks 02U6 is indexed by. -/
theorem relativeDimension_bundleProj :
    haveI := locallyOfFiniteType_bundleProj E n
    AlgebraicGeometry.RelativeDimension (bundleProj E) (n + 1 - 1) :=
  Stacks.Chow.relativeDimension_bundleProj E n

omit n

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The Segre pushforward** `α ↦ π_*(c₁(𝒪(1))^{n+1} ∩ π^*α)` of the projective bundle of a module
of rank `n + 1`, as an operation `CH_k(X) ⟶ CH_{k-1}(X)`. -/
def segre (k : ℤ) : chowGroup C sX k →+ chowGroup C sX (k - 1) :=
  haveI := flat_bundleProj E n
  haveI := locallyOfFiniteType_bundleProj E n
  (chowGroupCast C sX (by omega)).toAddMonoidHom.comp
    (projectiveBundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
      (relativeDimension_bundleProj E n)
      (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap E C sX) (n + 1) k)

end

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The first Chern class `c₁(ℰ) ∩ -`** of a finite locally free module of constant rank `r`, as
an operation `CH_k(X) ⟶ CH_{k-1}(X)`: the Segre pushforward of its projective bundle in positive
rank, and zero in rank zero. -/
def firstChern : (r : ℕ) →
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] →
    (k : ℤ) → chowGroup C sX k →+ chowGroup C sX (k - 1)
  | 0, _, _ => 0
  | n + 1, _, k =>
    haveI := isFiniteLocallyFree_of_rank E (n + 1)
    segre E n C sX k

/-- The first Chern class operation of a module of rank `0` is the zero map. -/
theorem firstChern_zero [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0]
    (k : ℤ) : firstChern E C sX 0 k = 0 := rfl

/-- The first Chern class operation of a module of rank `n + 1` is the Segre pushforward of its
projective bundle. -/
theorem firstChern_succ (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (k : ℤ) :
    firstChern E C sX (n + 1) k = segre E n C sX k := rfl

end Stacks.Chow.GenuineChern

end

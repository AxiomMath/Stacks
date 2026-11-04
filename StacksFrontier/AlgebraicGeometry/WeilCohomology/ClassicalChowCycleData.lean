module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Classical Weil cohomology theories on the Chow groups of Chapter 42

`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` (Stacks 0FGV) is stated for an arbitrary
`Stacks.WeilCohomology.ChowCycleData`: a family of groups with an intersection product, Gysin
pullbacks, proper pushforwards and fundamental classes obeying no laws. This file supplies the
instance the source means, the Chow groups of Chapter 42 with their actual operations, and names
the classical Weil cohomology theories over it.

The operations are those of the codimension-graded Chow groups `CH^i(X) = ∏_d CH_{d-i}(X_d)` of a
smooth scheme over `k`: the intersection product of Stacks 0FC0
(`Stacks.Chow.codimensionIntersectionProduct`), the Gysin map of Stacks 0FF3
(`Stacks.Chow.codimensionGysin`), proper pushforward between equidimensional schemes
(`Stacks.WeilCohomology.equidimensionalPushforward`) and the fundamental class
(`Stacks.WeilCohomology.fundamentalClass`). They are defined on the category
`Stacks.WeilCohomology.SmoothProjectiveScheme` of all smooth projective schemes over `k`, of
which the smooth projective varieties form a full subcategory, and they are transported along
the inclusion `Stacks.WeilCohomology.SmoothProjective.toSchemeCat`.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjective.toSchemeCat`: the inclusion of smooth projective
  varieties into smooth projective schemes over `k`.
* `Stacks.WeilCohomology.chowCycleData`: the Chow groups of Chapter 42 of smooth projective
  varieties, graded by codimension, with their intersection product, Gysin maps, proper
  pushforwards and fundamental classes.
* `Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory`: a classical Weil cohomology theory
  whose cycle class maps are defined on these Chow groups.

## Implementation notes

The proper pushforward of a `ChowCycleData` takes the dimensions `d` and `e` of the two
varieties together with proofs that they are the topological dimensions; a smooth projective
variety is irreducible, hence equidimensional, so the pushforward of the part of dimension `d`
is the whole pushforward, and `equidimensionalPushforward` at `d` and `e` is it.

## References

* [Stacks Project, Tag 0FGV](https://stacks.math.columbia.edu/tag/0FGV)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u v w

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

namespace SmoothProjective

/-- A smooth projective variety over `k` is a smooth projective scheme over `k`. -/
theorem le_smoothProjectiveScheme : SmoothProjective k ≤ SmoothProjectiveScheme k :=
  fun _ hX ↦ ⟨hX.1.toSmooth, (isProjective_iff_isProjectiveMorphism_of_isAffine _).2 hX.2⟩

/-- The inclusion of the smooth projective varieties over `k` into the smooth projective schemes
over `k`. -/
abbrev toSchemeCat :
    (SmoothProjective k).FullSubcategory ⥤ (SmoothProjectiveScheme k).FullSubcategory :=
  ObjectProperty.ιOfLE (le_smoothProjectiveScheme k)

end SmoothProjective

/-- **The Chow groups of Chapter 42** of smooth projective varieties over `k`, graded by
codimension, `CH^r(X) = ∏_d CH_{d-r}(X_d)`, with the intersection product of Stacks 0FC0, the
Gysin map of Stacks 0FF3, proper pushforward and the fundamental class `[X]`. -/
@[sga "6 XIV 4.1" "special case"]
def chowCycleData : ChowCycleData.{u, u} k where
  group X r := codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj X).obj.hom r
  mul r s α β := codimensionIntersectionProduct k _ r s α β
  gysin f r := codimensionGysin _ _ (Over.w ((SmoothProjective.toSchemeCat k).map f).hom) r
  pushforward f d e _ _ r :=
    equidimensionalPushforward ((SmoothProjective.toSchemeCat k).map f) d e r _ rfl
  fundamental X := fundamentalClass ((SmoothProjective.toSchemeCat k).obj X)

variable {k}

/-- The product of `chowCycleData` is the intersection product of Chow groups. -/
@[simp]
theorem chowCycleData_mul {X : (SmoothProjective k).FullSubcategory} (r s : ℤ)
    (α : (chowCycleData k).group X r) (β : (chowCycleData k).group X s) :
    (chowCycleData k).mul r s α β = codimensionIntersectionProduct k _ r s α β :=
  rfl

/-- The Gysin map of `chowCycleData` along `f` is the Gysin map `codimensionGysin` of `f`. -/
theorem chowCycleData_gysin {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
    (β : (chowCycleData k).group Y r) :
    (chowCycleData k).gysin f r β =
      codimensionGysin _ _ (Over.w ((SmoothProjective.toSchemeCat k).map f).hom) r β :=
  rfl

/-- The pushforward of `chowCycleData` along `f` is the proper pushforward
`equidimensionalPushforward` of `f` at the dimensions `d` and `e`. -/
theorem chowCycleData_pushforward {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y)
    (d e : ℕ) (hd : topologicalKrullDim X.obj.left = (d : WithBot ℕ∞))
    (he : topologicalKrullDim Y.obj.left = (e : WithBot ℕ∞)) (r : ℤ)
    (α : (chowCycleData k).group X r) :
    (chowCycleData k).pushforward f d e hd he r α =
      equidimensionalPushforward ((SmoothProjective.toSchemeCat k).map f) d e r _ rfl α :=
  rfl

/-- The fundamental class of `X` in `chowCycleData` is its fundamental class `[X]`. -/
theorem chowCycleData_fundamental (X : (SmoothProjective k).FullSubcategory) :
    (chowCycleData k).fundamental X = fundamentalClass ((SmoothProjective.toSchemeCat k).obj X) :=
  rfl

variable (k) in
/-- **A classical Weil cohomology theory** (Stacks 0FGV) over an algebraically closed field `k`
with coefficients in a field `F` of characteristic zero, whose cycle class maps
`γ : CH^r(X) → H^{2r}(X)` are defined on the Chow groups of Chapter 42 and whose axioms `(C)`
are stated for their actual intersection product, Gysin maps, proper pushforwards and
fundamental classes. -/
abbrev ChowClassicalWeilCohomologyTheory [IsAlgClosed k] (F : Type v) [Field F] [CharZero F] :=
  ClassicalWeilCohomologyTheory.{u, v, w, u} k F (chowCycleData k)

end Stacks.WeilCohomology

end

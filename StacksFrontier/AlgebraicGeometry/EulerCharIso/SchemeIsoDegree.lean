module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a finite locally free sheaf is invariant under an isomorphism of schemes

Let `f : X ⟶ Y` be an isomorphism of schemes over a field `k`, with `g : Y ⟶ Spec k` the
structure morphism of the target. The degree of a finite locally free sheaf of constant rank on
`Y` equals the degree of its pullback on `X`, and the degree of a sheaf on `X` equals the degree
of its direct image on `Y`.

This is the companion, across an isomorphism of *schemes*, of
`AlgebraicGeometry.curveDegree_eq_of_iso`, which is invariance across an isomorphism of
*modules* on one fixed scheme. The two together are what the base cases of the component formula
of Stacks Tag 0AYW need.

## Main definitions

* `AlgebraicGeometry.pushforwardUnitIso`: the direct image of the structure sheaf along an
  isomorphism of schemes is the structure sheaf of the target.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_unit_pushforward` and
  `AlgebraicGeometry.finrank_cohomologyOverField_pullback`: the two forms of
  `AlgebraicGeometry.finrank_cohomologyOverField_pushforward` the degree needs — at the
  structure sheaf, and at a pullback.
* `AlgebraicGeometry.curveDegree_pushforward` and `AlgebraicGeometry.curveDegree_pullback`:
  `deg(ℰ) = deg(f_* ℰ)` and `deg(f^* ℰ) = deg(ℰ)`.

## Implementation notes

`AlgebraicGeometry.curveDegree` is the alternating sum of the dimensions of the cohomology of the
sheaf, minus the rank times the same sum for the structure sheaf, so each of the two statements
needs the cohomology comparison twice: once at the sheaf and once at the structure sheaf.

At the structure sheaf the comparison is `AlgebraicGeometry.pushforwardUnitIso`, that `f_* 𝒪_X`
is `𝒪_Y`. It is **not** constructed here: Mathlib's `SheafOfModules.unitToPushforwardObjUnit` is
the canonical map, and `Stacks.StacksTag0E62.isIso_c_iff_isIso_unitToPushforwardObjUnit` already
says it is invertible exactly when the comparison `f.c` of sheaves of rings is, which for an
isomorphism of schemes it is, one open at a time.

At a pullback the comparison is the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, which is invertible because
pullback along an isomorphism is fully faithful; no new instance is needed, Mathlib's
`CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful` fires.

The local-freeness class does not transport along either comparison, so where a statement
mentions both a sheaf and its image, local freeness of both is an instance hypothesis. This is
why `curveDegree_pullback` is proved directly from the cohomology comparison rather than from
`curveDegree_pushforward`: routing it through the direct image would need local freeness of
`f_*(f^* ℰ)`, which is not available from local freeness of `ℰ`.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The direct image of the structure sheaf along an isomorphism of schemes is the structure
sheaf.** -/
def pushforwardUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  have : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit f).1
      ((Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_app f).2 fun _ =>
        inferInstance)
  (asIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).symm

/-- The cohomology of the structure sheaf is unchanged by an isomorphism of schemes over the
base. -/
theorem finrank_cohomologyOverField_unit_pushforward (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Spec (.of k)) (n : ℕ) :
    Module.finrank k
        (cohomologyOverField k (f ≫ g) (SheafOfModules.unit X.ringCatSheaf) n) =
      Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) n) :=
  (finrank_cohomologyOverField_pushforward k f g (SheafOfModules.unit X.ringCatSheaf) n).trans
    (finrank_cohomologyOverField_eq_of_iso k g (pushforwardUnitIso f) n)

/-- The cohomology of a pullback along an isomorphism of schemes has the dimension of the
cohomology of the original sheaf. -/
theorem finrank_cohomologyOverField_pullback (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Spec (.of k)) (E : Y.Modules) (n : ℕ) :
    Module.finrank k
        (cohomologyOverField k (f ≫ g) ((Scheme.Modules.pullback f).obj E) n) =
      Module.finrank k (cohomologyOverField k g E n) :=
  (finrank_cohomologyOverField_pushforward k f g _ n).trans
    (finrank_cohomologyOverField_eq_of_iso k g
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E)).symm n)

/-- The degree across an isomorphism of schemes depends only on the dimensions of the cohomology
of the sheaf and of the structure sheaf. -/
private theorem curveDegree_eq_of_finrank_eq (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Spec (.of k)) [IsProper (f ≫ g)] [IsProper g]
    (hX : topologicalKrullDim X ≤ 1) (hY : topologicalKrullDim Y ≤ 1)
    (E : X.Modules) (E' : Y.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' rank]
    (h : ∀ n, Module.finrank k (cohomologyOverField k (f ≫ g) E n) =
      Module.finrank k (cohomologyOverField k g E' n)) :
    curveDegree k (f ≫ g) hX E rank = curveDegree k g hY E' rank := by
  unfold curveDegree
  simp only [h, finrank_cohomologyOverField_unit_pushforward k f g]

/-- **The degree of a finite locally free sheaf equals the degree of its direct image along an
isomorphism of schemes over the base.** -/
theorem curveDegree_pushforward (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Spec (.of k)) [IsProper (f ≫ g)] [IsProper g]
    (hX : topologicalKrullDim X ≤ 1) (hY : topologicalKrullDim Y ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj E) rank] :
    curveDegree k (f ≫ g) hX E rank =
      curveDegree k g hY ((Scheme.Modules.pushforward f).obj E) rank :=
  curveDegree_eq_of_finrank_eq k f g hX hY E _ rank
    (finrank_cohomologyOverField_pushforward k f g E)

/-- **The degree of the pullback of a finite locally free sheaf along an isomorphism of schemes
over the base is its degree.** -/
theorem curveDegree_pullback (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Spec (.of k)) [IsProper (f ≫ g)] [IsProper g]
    (hX : topologicalKrullDim X ≤ 1) (hY : topologicalKrullDim Y ≤ 1)
    (E : Y.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) rank] :
    curveDegree k (f ≫ g) hX ((Scheme.Modules.pullback f).obj E) rank =
      curveDegree k g hY E rank :=
  curveDegree_eq_of_finrank_eq k f g hX hY _ E rank
    (finrank_cohomologyOverField_pullback k f g E)

end AlgebraicGeometry

end

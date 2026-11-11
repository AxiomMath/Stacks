module

public import StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible

/-!
# The invertible sheaf of an effective Cartier divisor has a nonzero section

Let `D ⊆ X` be an effective Cartier divisor on a nonempty algebraic space.  Multiplication by the
canonical section `1_D` of `𝒪_X(D)` is a nonzero morphism `𝒪_X ⟶ 𝒪_X(D)`.

## The argument

Multiplication by `1_D` is a monomorphism (Stacks 0847, part (1),
`AlgebraicGeometry.Space.canonicalSection_isRegular`).  A zero monomorphism out of `𝒪_X` forces
`𝒪_X ≅ 0`, so every geometric stalk of `𝒪_X` vanishes.  But the stalk of `𝒪_X` at a geometric
point is a local ring, which is not zero, and a nonempty algebraic space has a geometric point
(`AlgebraicGeometry.Space.exists_geometricRepresentative`).

## Main results

* `AlgebraicGeometry.Space.not_isZero_unit_of_nonempty_points`: the structure sheaf of a nonempty
  algebraic space is not zero.
* `AlgebraicGeometry.Space.exists_unit_hom_associatedInvertibleSheaf_ne_zero`: **`𝒪_X(D)` has a
  nonzero section `𝒪_X ⟶ 𝒪_X(D)`.**

## References

* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structure sheaf of a nonempty algebraic space is not zero.**  The stalk of `𝒪_X` at a
geometric point is a local ring, which is nontrivial, whereas the stalks of a zero module are
zero. -/
theorem not_isZero_unit_of_nonempty_points (X : AlgebraicSpaces B S hS)
    (hne : Nonempty (points B S hS X.1)) :
    ¬ IsZero (SheafOfModules.unit (structureRingSheaf B S hS X)) := by
  intro hz
  obtain ⟨y⟩ := hne
  obtain ⟨x, -⟩ := exists_geometricRepresentative B S hS X.1 y
  let O : Modules.{u, u} B S hS X.1 X.2 := SheafOfModules.unit (structureRingSheaf B S hS X)
  have hO : IsInvertibleModule X O := Stacks.SheafOfModules.isInvertible_unit _ _
  have hz' : IsZero O := hz
  have h0 : Subsingleton ((moduleStalkSetFunctor B S hS X x).obj
      (0 : Modules.{u, u} B S hS X.1 X.2)) :=
    subsingleton_moduleStalkSetFunctor_obj_zero B S hS X x
  have hst : Subsingleton ((moduleStalkSetFunctor B S hS X x).obj O) :=
    ((moduleStalkSetFunctor B S hS X x).mapIso hz'.isoZero).toEquiv.subsingleton
  have hlarge := subsingleton_moduleStalkLarge_of_subsingleton_stalkSet B S hS X x
    (smallEtaleRingedTopos B S hS X).O O hst
  let : IsLocalRing ↥(etaleLocalRing B S hS X.1 x) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  let : IsLocalRing ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X x).symm.isLocalRing
  obtain ⟨g⟩ := nonempty_linearEquiv_moduleStalkLarge_of_isInvertibleModule B S hS X x O hO
  have : Subsingleton ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :=
    g.toEquiv.symm.subsingleton
  exact not_subsingleton _ this

/-- **The invertible sheaf `𝒪_X(D)` of an effective Cartier divisor has a nonzero section**, as
soon as `X` is nonempty: multiplication by the canonical section `1_D` is a monomorphism
`𝒪_X ⟶ 𝒪_X(D)` (Stacks 0847, part (1)), and a zero monomorphism out of `𝒪_X` would make `𝒪_X`
zero (`AlgebraicGeometry.Space.not_isZero_unit_of_nonempty_points`). -/
theorem exists_unit_hom_associatedInvertibleSheaf_ne_zero (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
    (hne : Nonempty (points B S hS X.1)) :
    ∃ s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
        associatedInvertibleSheaf B S hS X D hD, s ≠ 0 := by
  refine ⟨canonicalSectionHom B S hS X D hD, fun h0 => ?_⟩
  have hm : Mono (canonicalSectionHom B S hS X D hD) := canonicalSection_isRegular B S hS X D hD
  rw [h0] at hm
  refine not_isZero_unit_of_nonempty_points B S hS X hne ((IsZero.iff_id_eq_zero _).mpr ?_)
  rw [← cancel_mono (0 : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
    associatedInvertibleSheaf B S hS X D hD), zero_comp, comp_zero]

end AlgebraicGeometry.Space

end

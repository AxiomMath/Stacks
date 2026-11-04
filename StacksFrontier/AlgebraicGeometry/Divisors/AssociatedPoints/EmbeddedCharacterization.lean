module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Embedded associated points and the generic points of the support

For a coherent module on a locally Noetherian scheme, the generic points of the irreducible
components of its support are associated to it, and an associated point is embedded precisely
when it is not one of those generic points. The same description specializes to the embedded
points of a scheme.

## Main results

* `AlgebraicGeometry.mem_associatedPoints_of_isGenericPoint_irreducibleComponent_supp`: the
  generic points of the irreducible components of the support are associated.
* `AlgebraicGeometry.isEmbeddedAssociatedPoint_iff_not_genericPoint`: the embedded associated
  points are exactly the non-generic associated points.
* `AlgebraicGeometry.isEmbeddedPoint_iff_not_genericPoint`: the corresponding characterization
  for the embedded points of a scheme.

## Implementation notes

An irreducible component of the support is a component of `SheafOfModules.supp F` with its
subspace topology; its image in `X` is used to express the generic-point condition in the
ambient scheme. The support of a coherent module is closed by `SheafOfModules.isClosed_supp`,
so that subspace is quasi-sober and its components do have generic points.

The last result is stated as an equivalence, so that it also characterizes the schemes without
embedded points.

## References

* [Stacks Project, Tag 05AL](https://stacks.math.columbia.edu/tag/05AL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The support of a coherent module on a locally Noetherian scheme is closed. -/
private theorem support_isClosed (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] : IsClosed (SheafOfModules.supp F) := by
  have : F.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).2
  exact SheafOfModules.isClosed_supp F

/-- In a quasi-sober space every point specializes from the generic point of some irreducible
component. -/
private theorem exists_generic_component_specializes {Y : Type u} [TopologicalSpace Y]
    [QuasiSober Y] (x : Y) :
    ∃ Z ∈ irreducibleComponents Y, ∃ y : Y, IsGenericPoint y Z ∧ y ⤳ x := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set Y)) isIrreducible_singleton.closure
  have hy := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  exact ⟨Z, hZ, _, hy, hy.specializes (hxZ (subset_closure rfl))⟩

/-- A point of the support specializing to the generic point of an irreducible component of the
support is that generic point. -/
private theorem generic_support_component_minimal (X : Scheme.{u}) (F : X.Modules)
    {Z : Set (↥(SheafOfModules.supp F))}
    (hZ : Z ∈ irreducibleComponents (↥(SheafOfModules.supp F))) {x : X}
    (hxgen : IsGenericPoint x (Subtype.val '' Z)) {y : X}
    (hymem : y ∈ SheafOfModules.supp F) (hspec : y ⤳ x) : y = x := by
  let yY : ↥(SheafOfModules.supp F) := ⟨y, hymem⟩
  have hsub : Z ⊆ closure ({yY} : Set ↥(SheafOfModules.supp F)) := fun z hz =>
    specializes_iff_mem_closure.mp <| Topology.IsInducing.subtypeVal.specializes_iff.mp <|
      hspec.trans (hxgen.specializes ⟨z, hz, rfl⟩)
  have hyZ : yY ∈ Z := hZ.2 isIrreducible_singleton.closure hsub (subset_closure rfl)
  exact ((hxgen.specializes ⟨yY, hyZ, rfl⟩).antisymm hspec).eq.symm

/-- **Stacks 05AL, part (1).** The generic point of an irreducible component of the support of a
coherent sheaf is associated to that sheaf. -/
@[stacks 05AL "part (1)", ega "IV 3.1.3" "special case"]
theorem mem_associatedPoints_of_isGenericPoint_irreducibleComponent_supp (X : Scheme.{u})
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    {Z : Set (↥(SheafOfModules.supp F))}
    (hZ : Z ∈ irreducibleComponents (↥(SheafOfModules.supp F))) {x : X}
    (hx : IsGenericPoint x (Subtype.val '' Z)) :
    x ∈ Stacks.Divisors.associatedPoints F := by
  obtain ⟨z, -, rfl⟩ := hx.mem
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  exact mem_associatedPoints_of_mem_supp_of_specialization X F _ z.2
    fun y hym hspec => generic_support_component_minimal X F hZ hx hym hspec

/-- **Stacks 05AL, part (2).** An associated point of a coherent sheaf is embedded exactly when
it is not generic in any irreducible component of its support. -/
@[stacks 05AL "part (2)"]
theorem isEmbeddedAssociatedPoint_iff_not_genericPoint (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : X) :
    IsEmbeddedAssociatedPoint F x ↔
      x ∈ Stacks.Divisors.associatedPoints F ∧
        ¬ ∃ Z ∈ irreducibleComponents (↥(SheafOfModules.supp F)),
          IsGenericPoint x (Subtype.val '' Z) := by
  constructor
  · rintro ⟨hxass, y, hyass, hspec, hne⟩
    exact ⟨hxass, fun ⟨Z, hZ, hxgen⟩ => hne (generic_support_component_minimal X F hZ hxgen
      (associatedPoints_subset_support F hyass) hspec)⟩
  · rintro ⟨hxass, hngen⟩
    have hxmem : x ∈ SheafOfModules.supp F := associatedPoints_subset_support F hxass
    have hemb := (support_isClosed X F).isClosedEmbedding_subtypeVal
    have := hemb.quasiSober
    obtain ⟨Z, hZ, y, hygen, hspec⟩ :=
      exists_generic_component_specializes (⟨x, hxmem⟩ : ↥(SheafOfModules.supp F))
    have hygen' : IsGenericPoint (y : X) (Subtype.val '' Z) := by
      show closure ({(y : X)} : Set X) = Subtype.val '' Z
      simpa [Set.image_singleton, hygen.def] using
        (hemb.closure_image_eq ({y} : Set ↥(SheafOfModules.supp F)))
    exact ⟨hxass, y,
      mem_associatedPoints_of_isGenericPoint_irreducibleComponent_supp X F hZ hygen',
      hspec.map continuous_subtype_val, fun hyx => hngen ⟨Z, hZ, hyx ▸ hygen'⟩⟩

/-- **Stacks 05AL, concluding assertion.** The embedded points of a locally Noetherian scheme
are precisely its non-generic associated points. -/
@[stacks 05AL "embedded points of the scheme"]
theorem isEmbeddedPoint_iff_not_genericPoint (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    IsEmbeddedPoint X x ↔
      x ∈ Stacks.Divisors.schemeAssociatedPoints X ∧
        ¬ ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z := by
  constructor
  · rintro ⟨hxass, y, hyass, hspec, hne⟩
    exact ⟨hxass, fun ⟨Z, hZ, hxgen⟩ =>
      hne (Topology.eq_of_specializes_isGenericPoint hZ hxgen hspec)⟩
  · rintro ⟨hxass, hngen⟩
    obtain ⟨Z, hZ, y, hygen, hspec⟩ := exists_generic_component_specializes x
    exact ⟨hxass, y,
      (Stacks.Divisors.mem_schemeAssociatedPoints_iff X y).mp
        (mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X hZ hygen),
      hspec, fun hyx => hngen ⟨Z, hZ, hyx ▸ hygen⟩⟩

end AlgebraicGeometry

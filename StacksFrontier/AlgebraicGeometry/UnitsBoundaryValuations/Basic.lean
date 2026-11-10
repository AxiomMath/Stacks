module

public import StacksFrontier.AlgebraicGeometry.UnitsBoundaryValuations.Finiteness
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.GlobalSections
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Japanese

/-!
# Units of an open subscheme of a normal proper variety, modulo the constants

Let `k` be an algebraically closed field, let `Y` be a *normal* proper variety over `k`, and let
`V ⊆ Y` be a nonempty open subscheme. This file proves that the group of units of `Γ(Y, V)`,
modulo the constants coming from `k`, is finitely generated: this is [Stacks, Tag 04L4] for a
normal proper variety.

A unit `u` on `V` is a nonzero element of the function field of `Y`, with an order of vanishing
at each point of `Y` of codimension one; that order is zero at every point of `V`, and the
family of orders at the finitely many boundary points of codimension one has kernel exactly the
constants, so the quotient embeds in a free abelian group of finite rank.

## Main definitions

* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.boundaryPoints`: the points of codimension one
  outside the open subscheme.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.boundaryOrd`: the family of orders of
  vanishing of a unit at those points.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.structMapOpen`: the constants of `k` as
  sections over the open subscheme.

## Main results

* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.structMapOpen_eq_structMapLE`: these
  constants are given by the structural map
  `Stacks.AlgebraicGeometry.UnitsNormalProper.structMapLE` of the open subscheme.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.boundaryOrd_eq_zero_iff`: the kernel of the
  family of boundary orders is exactly the subgroup of constants.
* `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.units_quotient_fg_of_isNormal`: the units
  modulo the constants form a finitely generated group.

## References

* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Order Set TopologicalSpace Topology

universe u

namespace Stacks.AlgebraicGeometry.UnitsBoundaryValuations

open Stacks.AlgebraicGeometry.UnitsNormalProper

/-- The boundary points of codimension one of an open subscheme `V` of `Y`: the points of `Y`
whose local ring has dimension one and which do not lie in `V`. -/
def boundaryPoints {Y : Scheme.{u}} (V : Y.Opens) : Set Y :=
  {y : Y | coheight y = 1 ∧ y ∉ (V : Set Y)}

/-- The family of orders of vanishing, at the boundary points of codimension one, of a unit of
the sections over `V` read as an element of the function field. -/
noncomputable def boundaryOrd {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (V : Y.Opens) [Nonempty V] (u : Γ(Y, V)ˣ) (b : boundaryPoints V) : ℤ :=
  Scheme.ord (Y.germToFunctionField V u.1) b.1

/-- The constants of `k` as sections over an open subscheme `V` of a scheme over `Spec k`: the
structural ring map `k →+* Γ(Y, ⊤)` followed by restriction to `V`. -/
noncomputable def structMapOpen (k : Type u) [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (V : Y.Opens) : k →+* Γ(Y, V) :=
  (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp (structMap k g)

section Basic

variable {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens) [Nonempty V]

/-- A unit of the sections over a nonempty open has invertible image in the function field. -/
theorem isUnit_germToFunctionField (u : Γ(Y, V)ˣ) : IsUnit (Y.germToFunctionField V u.1) := by
  refine IsUnit.of_mul_eq_one (Y.germToFunctionField V (u⁻¹ : Γ(Y, V)ˣ).1) ?_
  rw [← map_mul, Units.mul_inv, map_one]

/-- A unit of the sections over a nonempty open has nonzero image in the function field. -/
theorem germToFunctionField_ne_zero (u : Γ(Y, V)ˣ) : Y.germToFunctionField V u.1 ≠ 0 :=
  (isUnit_germToFunctionField V u).ne_zero

variable [IsLocallyNoetherian Y]

/-- The boundary orders are additive in the unit. -/
theorem boundaryOrd_mul (u v : Γ(Y, V)ˣ) :
    boundaryOrd V (u * v) = boundaryOrd V u + boundaryOrd V v := by
  funext b
  simp only [boundaryOrd, Units.val_mul, map_mul, Pi.add_apply]
  exact Scheme.ord_mul (germToFunctionField_ne_zero V u) (germToFunctionField_ne_zero V v)

/-- The boundary orders of the unit `1` all vanish. -/
theorem boundaryOrd_one : boundaryOrd V (1 : Γ(Y, V)ˣ) = 0 := by
  funext b
  simp only [boundaryOrd, Units.val_one, map_one, Pi.zero_apply]
  exact (Scheme.ord_eq_iff b.2.1 one_ne_zero).mpr (by simp)

/-- The boundary orders of an inverse are the negatives of the boundary orders. -/
theorem boundaryOrd_inv (u : Γ(Y, V)ˣ) : boundaryOrd V u⁻¹ = -boundaryOrd V u := by
  have h := boundaryOrd_mul V u u⁻¹
  rw [mul_inv_cancel, boundaryOrd_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- A unit whose boundary orders all vanish has order of vanishing zero at *every* point of
codimension one. -/
theorem ord_eq_zero_of_boundaryOrd_eq_zero {u : Γ(Y, V)ˣ} (hu : boundaryOrd V u = 0) (y : Y)
    (hy : coheight y = 1) : Scheme.ord (Y.germToFunctionField V u.1) y = 0 := by
  by_cases hyV : y ∈ (V : Set Y)
  · exact Scheme.ord_of_isUnit u.isUnit hyV
  · exact congrFun hu ⟨y, hy, hyV⟩

end Basic

section Proper

variable (k : Type u) [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))

/-- The constants over `V` are the restrictions of the constants over `Y`. -/
theorem structMapOpen_apply (V : Y.Opens) (c : k) :
    structMapOpen k g V c =
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (structMap k g c) := rfl

/-- Restricting the constants to `V` gives the structural map `structMapLE g V` of the open
subscheme. -/
theorem structMapOpen_eq_structMapLE (V : Y.Opens) :
    structMapOpen k g V = structMapLE g V := by
  refine RingHom.ext fun c => ?_
  simp only [structMapOpen, structMapLE, structMap, Scheme.Hom.appLE, Scheme.Hom.appTop,
    RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp]
  congr 1

variable [IsAlgClosed k] [AlgebraicGeometry.IsProperVariety k g] [AlgebraicGeometry.IsNormal Y]

/-- On a normal proper variety over an algebraically closed field, a unit of the sections over a
nonempty open subscheme has all its boundary orders zero exactly when it is a constant. -/
theorem boundaryOrd_eq_zero_iff [IsLocallyNoetherian Y] (V : Y.Opens) [Nonempty V]
    (u : Γ(Y, V)ˣ) :
    boundaryOrd V u = 0 ↔ u ∈ (Units.map (structMapOpen k g V).toMonoidHom).range := by
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : IsDomain Γ(Y, ⊤) := isDomain_globalSections (X := Y)
  have hgen : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hres : ∀ a : Γ(Y, ⊤),
      Y.germToFunctionField V (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a) =
        Y.presheaf.germ ⊤ (genericPoint Y) trivial a := fun a =>
    Y.presheaf.germ_res_apply (homOfLE (le_top : V ≤ ⊤)) (genericPoint Y) hgen a
  constructor
  · intro hu
    obtain ⟨a, ha⟩ := exists_globalSection_of_forall_ord_eq_zero
      (germToFunctionField_ne_zero V u) (ord_eq_zero_of_boundaryOrd_eq_zero V hu)
    obtain ⟨b, hb⟩ := exists_globalSection_of_forall_ord_eq_zero
      (germToFunctionField_ne_zero V u⁻¹)
      (ord_eq_zero_of_boundaryOrd_eq_zero V (by rw [boundaryOrd_inv, hu, neg_zero]))
    have hab : a * b = 1 := by
      refine germ_injective_of_isIntegral (X := Y) (U := ⊤) (genericPoint Y) trivial ?_
      rw [map_mul, ha, hb, map_one, ← map_mul, Units.mul_inv, map_one]
    obtain ⟨c, hc⟩ := (bijective_structMap k g).2 a
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact (IsUnit.of_mul_eq_one b hab).ne_zero hc.symm
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    change structMapOpen k g V c = u.1
    rw [structMapOpen_apply, hc]
    exact Y.germToFunctionField_injective V (by rw [hres, ha])
  · rintro ⟨c, rfl⟩
    funext b
    change Scheme.ord (Y.germToFunctionField V (structMapOpen k g V (c : k))) b.1 = 0
    rw [structMapOpen_apply, hres]
    exact Scheme.ord_of_isUnit (U := ⊤) (c.isUnit.map (structMap k g)) trivial

/-- **Stacks Project, Tag 04L4** for a normal proper variety. Let `k` be an algebraically closed
field, let `Y` be a normal proper variety over `k`, and let `V` be a nonempty open subscheme of
`Y`. Then the group of units of `Γ(Y, V)` modulo the constants coming from `k` is finitely
generated. -/
theorem units_quotient_fg_of_isNormal (V : Y.Opens) [Nonempty V] :
    Group.FG (Γ(Y, V)ˣ ⧸ (Units.map (structMapOpen k g V).toMonoidHom).range) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : AlgebraicGeometry.IsNoetherian Y := AlgebraicGeometry.IsNoetherian.mk
  have hgen : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have : Finite (boundaryPoints V) :=
    (finite_coheight_one_notMem (fun _ _ => Scheme.le_iff_specializes) V.isOpen hgen).to_subtype
  exact group_fg_quotient_of_intCounting _ (boundaryOrd V) (boundaryOrd_mul V)
    (boundaryOrd_eq_zero_iff k g V)

end Proper

end Stacks.AlgebraicGeometry.UnitsBoundaryValuations

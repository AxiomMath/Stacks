module

public import StacksFrontier.AlgebraicGeometry.Ample.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The nonvanishing locus of a section of the structure sheaf

The nonvanishing locus `X_s` of Tag 01CY is defined for a global section of an arbitrary
invertible sheaf of modules, as the set of points where the germ of the section escapes
`𝔪_x L_x`. For the structure sheaf itself, viewed as a module over itself, that set is the
locus where the germ of the section is a *unit*, which is exactly Mathlib's
`AlgebraicGeometry.RingedSpace.basicOpen`. This file proves that identification, together with
the transport of nonvanishing loci along an isomorphism of module sheaves, and draws the first
consequence for ampleness: on an affine scheme the structure sheaf is an ample invertible
sheaf.

## Main definitions

* `Stacks.SheafOfModules.unitSections`: the unit section `1 ∈ Γ(X, O_X)`, as a global section of
  the structure sheaf viewed as a module over itself.

## Main results

* `Stacks.SheafOfModules.mem_nonvanishingLocus_unit_iff`: a point lies in the nonvanishing locus
  of a section of the structure sheaf exactly when the germ of the section there is a unit.
* `Stacks.SheafOfModules.nonvanishingLocus_unit_eq_basicOpen`: consequently that locus is
  `RingedSpace.basicOpen` of the section.
* `Stacks.SheafOfModules.nonvanishingLocus_sectionsMap`: an isomorphism of sheaves of modules
  carries a global section to one with the same nonvanishing locus.
* `Stacks.SheafOfModules.nonvanishingLocus_unitSections`: the unit section vanishes nowhere.
* `AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_unit`: on an affine scheme the
  nonvanishing locus of a section of the structure sheaf is affine. This is the case
  `L = O_X` of Tag 01PV.
* `AlgebraicGeometry.Scheme.Modules.isAmple_unit`: the structure sheaf of an affine scheme is
  ample.
* `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_isAffine`: an affine scheme carries an
  ample invertible sheaf.

## Implementation notes

The membership criterion is proved against the local-algebra description of the stalk rather
than against the pairing criterion `Stacks.SheafOfModules.mem_nonvanishingLocus_iff`: for the
structure sheaf the stalk is free of rank one on the germ of the unit section
(`Stacks.SheafOfModules.unitStalkLinearEquiv`), so membership in `𝔪_x (O_X)_x` reduces along
that equivalence to membership in `𝔪_x`, with no trivialization to choose. The two directions
are `Stacks.SheafOfModules.map_mem_smul_top`, which says a linear map carries `I • ⊤` into
`I • ⊤`, and `Stacks.SheafOfModules.ideal_smul_top_le`, which says `I • ⊤ ≤ I` for the module
`R` itself.

`nonvanishingLocus` takes no invertibility hypothesis, and `nonvanishingOpen` is
`nonvanishingLocus` paired with its openness proof, so the results about loci are stated for
`nonvanishingLocus` and transfer to `nonvanishingOpen` without having to produce an
invertibility instance. The one place an instance is needed is the ampleness statement, whose
definition in `StacksFrontier/AlgebraicGeometry/Ample/Defs.lean` quantifies over invertible
sheaves; `AlgebraicGeometry.Scheme.Modules.isInvertible_unit` supplies it from
`Stacks.SheafOfModules.isInvertible_unit`.

Ampleness of `O_X` on an affine scheme uses exponent `n = 1`, and the first tensor power is
identified with `O_X` by `Stacks.SheafOfModules.Invertible.tensorPowerOneIso`; it is the
transport lemma `nonvanishingLocus_sectionsMap` that lets the unit section be pushed across
that identification without losing its nonvanishing locus.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpGerm)

universe u

namespace Stacks.SheafOfModules

section LocalAlgebra

variable {R : Type u} [CommRing R]

/-- A linear map carries `I • ⊤` into `I • ⊤`. -/
theorem map_mem_smul_top {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (I : Ideal R) (f : P →ₗ[R] Q) {p : P}
    (hp : p ∈ I • (⊤ : Submodule R P)) : f p ∈ I • (⊤ : Submodule R Q) := by
  refine Submodule.smul_induction_on hp ?_ ?_
  · intro a ha y _
    rw [map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- A linear equivalence identifies the submodules `I • ⊤` on either side. -/
theorem mem_smul_top_iff_of_linearEquiv {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (I : Ideal R) (f : P ≃ₗ[R] Q) (p : P) :
    f p ∈ I • (⊤ : Submodule R Q) ↔ p ∈ I • (⊤ : Submodule R P) := by
  refine ⟨fun h => ?_, fun h => map_mem_smul_top I f.toLinearMap h⟩
  simpa using map_mem_smul_top I f.symm.toLinearMap h

/-- For the module `R` itself, `I • ⊤` is contained in `I`. -/
theorem ideal_smul_top_le (I : Ideal R) : I • (⊤ : Submodule R R) ≤ I :=
  Submodule.smul_le.2 fun _ ha r _ => Ideal.mul_mem_right r _ ha

end LocalAlgebra

section Unit

variable (X : RingedSpace.{u, u})

/-- The unit section `1 ∈ Γ(X, O_X)`, as a global section of the structure sheaf viewed as a
module over itself. -/
@[ega "0 4.1.1"]
noncomputable def unitSections : (SheafOfModules.unit (structureSheafRing X)).sections :=
  PresheafOfModules.sectionsMk (fun W => unitSection X W.unop)
    (fun {_ _} f => map_one ((structureSheafRing X).obj.map f).hom)

/-- The unit section evaluates on each open `W` to the unit section `1 ∈ Γ(W, O_X)`. -/
@[simp]
theorem unitSections_eval (W : (Opens X.carrier)ᵒᵖ) :
    (unitSections X).eval W = unitSection X W.unop := rfl

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- A point lies in the nonvanishing locus of a global section of the structure sheaf, viewed as
a module over itself, exactly when the germ of that section is a unit. The stalk is free of rank
one on the germ of the unit section, so `𝔪_x (O_X)_x` corresponds to `𝔪_x` under that
identification. -/
theorem mem_nonvanishingLocus_unit_iff
    (s : (SheafOfModules.unit (structureSheafRing X)).sections) (x : X.carrier) :
    x ∈ nonvanishingLocus (SheafOfModules.unit (structureSheafRing X)) s ↔
      IsUnit (ringGerm X x ⊤ (Opens.mem_top x) (s.eval (op ⊤))) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  show (grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x ⊤ (Opens.mem_top x)
      (s.eval (op ⊤)) ∉ _) ↔ _
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := map_mem_smul_top (IsLocalRing.maximalIdeal (ringStalk X x))
      (unitStalkLinearEquiv X x).symm.toLinearMap h
    simp only [LinearEquiv.coe_coe, unitStalkLinearEquiv_symm_grpGerm] at h2
    exact ideal_smul_top_le _ h2
  · rw [← ringGerm_smul_unitGerm X x ⊤ (Opens.mem_top x)]
    exact Submodule.smul_mem_smul h Submodule.mem_top

/-- The nonvanishing locus of a global section of the structure sheaf is the basic open of that
section. -/
@[ega "0 5.5.2" "special case"]
theorem nonvanishingLocus_unit_eq_basicOpen
    (s : (SheafOfModules.unit (structureSheafRing X)).sections) :
    nonvanishingLocus (SheafOfModules.unit (structureSheafRing X)) s
      = (X.basicOpen (U := ⊤) (s.eval (op ⊤)) : Set X.carrier) := by
  ext x
  exact Iff.trans (mem_nonvanishingLocus_unit_iff X s x)
    (X.mem_basicOpen (U := ⊤) (s.eval (op ⊤)) x (Opens.mem_top x)).symm

/-- The unit section of the structure sheaf vanishes nowhere. -/
theorem nonvanishingLocus_unitSections :
    nonvanishingLocus (SheafOfModules.unit (structureSheafRing X)) (unitSections X)
      = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  rw [mem_nonvanishingLocus_unit_iff]
  exact (map_one (ringGerm X x ⊤ (Opens.mem_top x))) ▸ isUnit_one

/-- An isomorphism of sheaves of modules preserves nonvanishing loci: the image of a global
section under the isomorphism has the same nonvanishing locus as the section itself. -/
theorem nonvanishingLocus_sectionsMap {L M : SheafOfModules.{u} (structureSheafRing X)}
    (e : L ≅ M) (s : L.sections) :
    nonvanishingLocus M (SheafOfModules.sectionsMap e.hom s) = nonvanishingLocus L s := by
  ext x
  show (grpGerm X M.val x ⊤ (Opens.mem_top x)
      ((SheafOfModules.sectionsMap e.hom s).eval (op ⊤)) ∉ _) ↔ (_ ∉ _)
  refine not_congr ?_
  rw [show (SheafOfModules.sectionsMap e.hom s).eval (op ⊤)
      = (e.hom.val.app (op ⊤)).hom (s.eval (op ⊤)) from rfl,
    ← stalkLinearEquiv_germ X e x ⊤ (Opens.mem_top x) (s.eval (op ⊤))]
  exact mem_smul_top_iff_of_linearEquiv _ (stalkLinearEquiv X e x) _

end Unit

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

variable (Y : Scheme.{u})

/-- The structure sheaf of a scheme, viewed as a module over itself, is invertible. -/
instance isInvertible_unit :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- The nonvanishing locus of a global section of the structure sheaf of a scheme is its basic
open, as an open subset. -/
@[ega "0 5.5.2" "special case"]
theorem nonvanishingOpen_unit_eq_basicOpen
    [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))]
    (s : (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).sections) :
    nonvanishingOpen (X := Y.toRingedSpace)
        (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) s
      = Y.basicOpen (U := ⊤) (s.eval (op ⊤)) :=
  TopologicalSpace.Opens.ext (nonvanishingLocus_unit_eq_basicOpen Y.toRingedSpace s)

/-- On an affine scheme the nonvanishing locus of a global section of the structure sheaf is
affine. This is the case `L = O_X` of **Stacks Project, Tag 01PV**; the general case, for an
arbitrary invertible sheaf, is not proved here. -/
theorem isAffineOpen_nonvanishingOpen_unit [IsAffine Y]
    [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))]
    (s : (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).sections) :
    IsAffineOpen (nonvanishingOpen (X := Y.toRingedSpace)
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) s) := by
  rw [nonvanishingOpen_unit_eq_basicOpen]
  exact (isAffineOpen_top Y).basicOpen _

/-- The structure sheaf of an affine scheme is ample: the unit section already has nonvanishing
locus all of `X`, which is affine. -/
theorem isAmple_unit [IsAffine Y] :
    IsAmple Y (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) := by
  refine ⟨inferInstance, fun x => ⟨1, le_refl 1, ?_⟩⟩
  have e := tensorPowerOneIso Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
  have h := (nonvanishingLocus_sectionsMap Y.toRingedSpace e.symm
    (unitSections Y.toRingedSpace)).trans (nonvanishingLocus_unitSections Y.toRingedSpace)
  refine ⟨SheafOfModules.sectionsMap e.symm.hom (unitSections Y.toRingedSpace),
    h.ge (Set.mem_univ x), ?_⟩
  convert isAffineOpen_top Y using 1
  exact TopologicalSpace.Opens.ext h

/-- An affine scheme carries an ample invertible sheaf, namely its structure sheaf. -/
theorem exists_isAmple_of_isAffine [IsAffine Y] :
    ∃ (L : Y.Modules) (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
        Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property L),
      @IsAmple Y L hL :=
  ⟨SheafOfModules.unit (structureSheafRing Y.toRingedSpace), inferInstance, isAmple_unit Y⟩

end AlgebraicGeometry.Scheme.Modules

end

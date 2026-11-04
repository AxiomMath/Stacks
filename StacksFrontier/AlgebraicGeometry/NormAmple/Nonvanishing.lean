module
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Coefficient
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf

/-!
# The nonvanishing locus of a global section, read in a local frame

Let `(X, 𝒪_X)` be a ringed space with local stalks and let `L` be an invertible sheaf of
`𝒪_X`-modules. Over an open `U` carrying a generator `t` of `L` a global section `s` is a unique
multiple `a · t`, and this file proves that `s` is nonvanishing at a point of `U` exactly when
`a` is: the nonvanishing locus of Tag 01CY is computed by the frame calculus of
[Stacks, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ).

That identification is what connects the two ways this repository records "vanishing at a
point". `Stacks.SheafOfModules.nonvanishingLocus` is about a *global section* of an invertible
module and is what ampleness (Tag 01PS) is defined with; `Stacks.SheafOfModules.zeroAt` is about
a *map* of invertible modules and is what the norm of a map (Tag 0BCZ) is characterized by. For
a map `φ` out of a module carrying a nowhere-vanishing global section `g`, the last result below
says the two agree: the nonvanishing locus of `φ(g)` is the complement of the vanishing locus of
`φ`. Taking `g` to be the unit section of the structure sheaf turns a global section of `L` into
a map `𝒪_X ⟶ L` with the same locus, which is how Tag 0BD0 feeds a section into Tag 0BCZ.

## Main definitions

* `Stacks.SheafOfModules.generatorSectionsOfNonvanishing`: a global section vanishing nowhere,
  read as a generator over an arbitrary open.

## Main results

* `Stacks.SheafOfModules.exists_smul_grpGerm_eq_of_generator`: a local generator generates every
  stalk over its open.
* `Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_generator`: **the germ of a local
  generator lies outside `𝔪_x L_x`**, that is, a generator is nonvanishing.
* `Stacks.SheafOfModules.mem_nonvanishingLocus_iff_isUnit_ringGerm`: **the nonvanishing locus of
  a global section, read off a local frame.**
* `Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_generator`: a generator over `⊤` is a
  global section vanishing nowhere.
* `Stacks.SheafOfModules.sectionsMap_unitHomEquiv_symm_unitSections`: the map out of the
  structure sheaf attached to a section carries the unit section back to it.
* `Stacks.SheafOfModules.nonvanishingLocus_sectionsMap_eq_setOf_not_zeroAt`: **for a map `φ` and
  a nowhere-vanishing section `g`, the nonvanishing locus of `φ(g)` is where `φ` does not
  vanish.**

## Implementation notes

The germ of a generator is shown to be a unit under *some* identification `L_x ≃ₗ 𝒪_{X,x}`
rather than by exhibiting a basis: the stalk of an invertible module over a local ring is free
of rank one (`Stacks.SheafOfModules.Invertible.nonempty_linearEquiv_of_module_invertible`,
through `Stacks.SheafOfModules.stalkPairing`), and a cyclic generator of a free rank-one module
has unit image. No finiteness of the stalk is used, which is the same route as the converse half
of Tag 0B8M in `StacksFrontier/AlgebraicGeometry/InvertibleTrivialization/Basic.lean`.

The frame-independence of the answer is not reproved here: both sides of the last result are
computed in *one* frame, chosen at the point, and the two existing frame-independence
statements — `Stacks.SheafOfModules.zeroAt_iff_evaluation_eq_zero` for a map and the frame
calculus behind it — do the rest.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpStalk grpGerm)

universe u

namespace Stacks.SheafOfModules

section RingedSpace

variable {X : RingedSpace.{u, u}}

/-- A local generator generates the stalk at every point of its open. -/
theorem exists_smul_grpGerm_eq_of_generator
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    {U : Opens X.carrier} (t : GeneratorSections X L U) (x : X.carrier) (hx : x ∈ U)
    (m : grpStalk X L.val x) :
    ∃ c : ringStalk X x, c • grpGerm X L.val x U hx t.val = m := by
  obtain ⟨V, hxV, mV, hmV⟩ := exists_grpGerm_eq X L.val x m
  have hxW : x ∈ V ⊓ U := ⟨hxV, hx⟩
  obtain ⟨c, hc⟩ := (t.property (V ⊓ U) inf_le_right).2
    (L.val.restrictₛₗ (homOfLE (inf_le_left : V ⊓ U ≤ V)).op mV)
  refine ⟨ringGerm X x (V ⊓ U) hxW c, ?_⟩
  have h2 : grpGerm X L.val x (V ⊓ U) hxW
      (L.val.restrictₛₗ (homOfLE (inf_le_right : V ⊓ U ≤ U)).op t.val)
      = grpGerm X L.val x U hx t.val :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE (inf_le_right : V ⊓ U ≤ U)) x hxW t.val
  have h1 : grpGerm X L.val x (V ⊓ U) hxW
      (L.val.restrictₛₗ (homOfLE (inf_le_left : V ⊓ U ≤ V)).op mV) = m :=
    (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE (inf_le_left : V ⊓ U ≤ V)) x hxW mV).trans hmV
  refine Eq.trans ?_ h1
  rw [← hc, ← h2]
  exact (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X L.val x (V ⊓ U) hxW c
    (L.val.restrictₛₗ (homOfLE (inf_le_right : V ⊓ U ≤ U)).op t.val)).symm

/-- The section corresponding to a map out of the structure sheaf is the image of the unit
section. -/
theorem sectionsMap_unitHomEquiv_symm_unitSections
    (L : _root_.SheafOfModules.{u} (structureSheafRing X)) (s : L.sections) :
    _root_.SheafOfModules.sectionsMap ((_root_.SheafOfModules.unitHomEquiv L).symm s)
      (unitSections X) = s := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  have h := _root_.SheafOfModules.unitHomEquiv_apply_coe L
    ((_root_.SheafOfModules.unitHomEquiv L).symm s) U
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **The germ of a local generator is nonvanishing.** -/
theorem notMem_maximalIdeal_smul_top_of_generator
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : GeneratorSections X L U) (x : X.carrier) (hx : x ∈ U) :
    grpGerm X L.val x U hx t.val ∉
      maximalIdeal (ringStalk X x) • (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  have : Module.Invertible (ringStalk X x) (grpStalk X L.val x) := .left (stalkPairing ψ x)
  obtain ⟨e⟩ := Invertible.nonempty_linearEquiv_of_module_invertible
    (ringStalk X x) (grpStalk X L.val x)
  rw [Invertible.mem_maximalIdeal_smul_top_iff e]
  refine notMem_maximalIdeal.2 ?_
  obtain ⟨c, hc⟩ := exists_smul_grpGerm_eq_of_generator L t x hx (e.symm 1)
  refine IsUnit.of_mul_eq_one c ?_
  have h := congrArg e hc
  rw [map_smul, e.apply_symm_apply] at h
  simpa [mul_comm] using h

/-- **The nonvanishing locus read off a local frame.** -/
theorem mem_nonvanishingLocus_iff_isUnit_ringGerm
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    (s : L.sections) {U : Opens X.carrier} (t : GeneratorSections X L U)
    (a : (structureSheafRing X).obj.obj (op U))
    (ha : s.eval (op U) =
      @SMul.smul ((structureSheafRing X).obj.obj (op U)) (L.val.obj (op U)) _ a t.val)
    (x : X.carrier) (hx : x ∈ U) :
    x ∈ nonvanishingLocus L s ↔ IsUnit (ringGerm X x U hx a) := by
  have hres : L.val.map (homOfLE (le_top : U ≤ ⊤)).op (s.eval (op ⊤)) = s.eval (op U) :=
    PresheafOfModules.sections_property s (homOfLE (le_top : U ≤ ⊤)).op
  have key : grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))
      = ringGerm X x U hx a • grpGerm X L.val x U hx t.val := by
    refine Eq.trans ?_ (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X L.val x
      U hx a t.val)
    refine Eq.trans ?_ (congrArg (grpGerm X L.val x U hx) (hres.trans ha))
    exact (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE (le_top : U ≤ ⊤)) x hx (s.eval (op ⊤))).symm
  rw [show (x ∈ nonvanishingLocus L s) ↔
      grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) ∉
        maximalIdeal (ringStalk X x) •
          (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) from Iff.rfl,
    key, smul_notMem_maximalIdeal_smul_top_iff]
  exact and_iff_left (notMem_maximalIdeal_smul_top_of_generator L t x hx)

/-- A global section that vanishes nowhere generates over every open. -/
noncomputable def generatorSectionsOfNonvanishing
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    (s : L.sections) (hs : ∀ x : X.carrier, x ∈ nonvanishingLocus L s)
    (U : Opens X.carrier) : GeneratorSections X L U :=
  ⟨s.eval (op U), fun V h => (PresheafOfModules.sections_property s (homOfLE h).op) ▸
    bijective_smul_of_subset_nonvanishingLocus L s V fun y _ => hs y⟩

/-- A generator over the whole space is a global section vanishing nowhere. -/
theorem nonvanishingLocus_sectionsOfTop_generator
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    (t : GeneratorSections X L ⊤) :
    nonvanishingLocus L (sectionsOfTop L t.val) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  refine (mem_nonvanishingLocus_iff_isUnit_ringGerm L (sectionsOfTop L t.val) t 1 ?_ x
    (Opens.mem_top x)).2 ?_
  · exact (sectionsOfTop_eval_top L t.val).trans (one_smul _ _).symm
  · rw [map_one]
    exact isUnit_one

end RingedSpace

section Scheme

variable {X : Scheme.{u}}

/-- **The nonvanishing locus of the image of a nowhere-vanishing section is exactly the locus
where the map does not vanish.** -/
theorem nonvanishingLocus_sectionsMap_eq_setOf_not_zeroAt
    (M M' : X.Modules)
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property M]
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property M']
    (φ : M ⟶ M') (g : M.sections)
    (hg : ∀ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace) M g) :
    nonvanishingLocus (X := X.toRingedSpace) M' (_root_.SheafOfModules.sectionsMap φ g)
      = {x : X | ¬ zeroAt M M' φ x} := by
  ext x
  obtain ⟨W, hxW, b, hb⟩ :=
    exists_bijective_smul_of_isInvertible (X := X.toRingedSpace) M' x
  have ha := generatorCoefficient_spec (X := X.toRingedSpace) M M' φ W
    (generatorSectionsOfNonvanishing M g hg W) ⟨b, hb⟩
  have h1 := mem_nonvanishingLocus_iff_isUnit_ringGerm (X := X.toRingedSpace) M'
    (_root_.SheafOfModules.sectionsMap φ g) (⟨b, hb⟩ : GeneratorSections X.toRingedSpace M' W)
    (generatorCoefficient (X := X.toRingedSpace) M M' φ W
      (generatorSectionsOfNonvanishing M g hg W) ⟨b, hb⟩) ha x hxW
  have h2 := zeroAt_iff_evaluation_eq_zero M M' φ W x hxW
    (generatorSectionsOfNonvanishing M g hg W) ⟨b, hb⟩ _ ha
  have h3 := isUnit_ringGerm_iff_mem_basicOpen (X := X.toRingedSpace)
    (generatorCoefficient (X := X.toRingedSpace) M M' φ W
      (generatorSectionsOfNonvanishing M g hg W) ⟨b, hb⟩) x hxW
  have h4 := X.evaluation_ne_zero_iff_mem_basicOpen x hxW
    (generatorCoefficient (X := X.toRingedSpace) M M' φ W
      (generatorSectionsOfNonvanishing M g hg W) ⟨b, hb⟩)
  exact h1.trans (h3.trans (h4.symm.trans (not_congr h2).symm))

end Scheme

end Stacks.SheafOfModules

end

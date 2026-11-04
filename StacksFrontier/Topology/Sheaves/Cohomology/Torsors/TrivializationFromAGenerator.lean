module

public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule

/-!
# A generator trivializes a module

A section of a sheaf of modules `L` on a ringed space which trivializes `L` over an open `U`
is the same thing as an isomorphism `𝒪_U ≅ L|_U`: multiplication by the section is the
isomorphism, and the image of `1` is the section.  This file records the translation, in the
two cases needed for the classification of invertible modules by first cohomology: over an
arbitrary open, and over the whole space.

## Main definitions

* `Stacks.Cohomology.Generators.generatorSectionsUnitIso`: the trivialization of `L` over `U`
  determined by a generator over `U`.
* `Stacks.Cohomology.Generators.moduleIsoOfGenerator`: the trivialization of `L` over the whole
  space determined by a global generator.
* `Stacks.Cohomology.Generators.generatorSections_unit`: the unit section of the structure
  sheaf is a global generator of it.

## Main results

* `Stacks.Cohomology.Generators.generatorSectionsUnitIso_apply_one`: the trivialization carries
  the unit section to the generator it was built from.

## Implementation notes

The morphism `𝒪_U ⟶ L|_U` is `SheafOfModules.unitHomEquiv.symm` applied to the section of
`L|_U` whose value over `V ≤ U` is the restriction of the generator.  Its component over `V` is
multiplication by that restriction, so the generating hypothesis says exactly that every
component is bijective, and `Stacks.SheafOfModules.isIso_of_isIso_val_app` turns that into an
isomorphism of sheaves of modules.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Generators

/-- The section of `L|_U` whose value over each `V ≤ U` is the restriction of a generator. -/
def generatorOverSections (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) (U : Opens X)
    (s : GeneratorSections X L U) : (L.over U).sections :=
  (L.over U).val.sectionsMk (fun V => L.val.map V.unop.hom.op s.val) (by
    intro V W f
    change L.val.map f.unop.left.op (L.val.map V.unop.hom.op s.val) =
      L.val.map W.unop.hom.op s.val
    rw [← L.val.map_comp_apply]
    have hh : V.unop.hom.op ≫ f.unop.left.op = W.unop.hom.op := Subsingleton.elim _ _
    rw [hh])

/-- Multiplication by a generator of `L` over `U` is an isomorphism `𝒪_U ≅ L|_U`: a trivializing
section is the same datum as a trivialization. -/
def generatorSectionsUnitIso (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) (U : Opens X)
    (s : GeneratorSections X L U) :
    SheafOfModules.unit ((structureSheaf X.sheaf).over U) ≅ L.over U := by
  let f := (L.over U).unitHomEquiv.symm (generatorOverSections X L U s)
  have hf : IsIso f := by
    refine Stacks.SheafOfModules.isIso_of_isIso_val_app f fun V => ?_
    have hbij : Function.Bijective (f.val.app V) := by
      let W := V.unop.left
      let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op W)) :=
        inferInstanceAs (CommRing (X.presheaf.obj (op W)))
      change Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op W) =>
        @SMul.smul _ _ _ r (L.val.map V.unop.hom.op s.val))
      exact s.property W V.unop.hom.le
    exact (ConcreteCategory.isIso_iff_bijective (f.val.app V)).2 hbij
  exact asIso f

/-- The trivialization determined by a generator carries the unit section to that generator. -/
theorem generatorSectionsUnitIso_apply_one (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) (U : Opens X)
    (s : GeneratorSections X L U) :
    (((generatorSectionsUnitIso X L U s).hom.val.app (op (Over.mk (𝟙 U)))).hom)
        (1 : ((structureSheaf X.sheaf).over U).obj.obj (op (Over.mk (𝟙 U)))) = s.val := by
  let top : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let R := (structureSheaf X.sheaf).over U
  let _ : CommRing (R.obj.obj top) := inferInstanceAs (CommRing (X.presheaf.obj (op U)))
  let M := L.over U
  let t : M.sections := generatorOverSections X L U s
  have hval := congrArg (fun q : M.sections => q.val top) (M.unitHomEquiv.apply_symm_apply t)
  rw [SheafOfModules.unitHomEquiv_apply_coe] at hval
  show ((M.unitHomEquiv.symm t).val.app top).hom (1 : R.obj.obj top) = s.val
  rw [hval]
  show (L.val.map (𝟙 (op U))).hom s.val = s.val
  exact congrArg (fun g => g.hom s.val) (L.val.map_id (op U))

/-- The unit section of the structure sheaf trivializes it over the whole space. -/
def generatorSections_unit (X : RingedSpace.{u, u}) :
    GeneratorSections X (SheafOfModules.unit (structureSheaf X.sheaf)) ⊤ := by
  let R := structureSheaf X.sheaf
  let L := SheafOfModules.unit R
  refine ⟨(1 : R.obj.obj (op ⊤)), ?_⟩
  intro V h
  have hfun : (fun r : R.obj.obj (op V) =>
      r • L.val.restrictₛₗ (homOfLE h).op (1 : R.obj.obj (op ⊤))) =
      fun r : R.obj.obj (op V) => r := by
    funext r
    have hres : L.val.restrictₛₗ (homOfLE h).op (1 : R.obj.obj (op ⊤)) =
        (1 : R.obj.obj (op V)) :=
      PresheafOfModules.unit_map_one (R := R.obj) (homOfLE h).op
    rw [hres]
    change r * 1 = r
    exact mul_one r
  rw [hfun]
  exact Function.bijective_id

/-- A global generator of `L` trivializes it: multiplication by it is an isomorphism
`𝒪_X ≅ L`. -/
def moduleIsoOfGenerator (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (s : GeneratorSections X L ⊤) :
    SheafOfModules.unit (structureSheaf X.sheaf) ≅ L := by
  let R := structureSheaf X.sheaf
  let t : L.sections := L.val.sectionsMk
    (fun V => L.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op s.val) (by
      intro V W f
      change L.val.map (homOfLE f.unop.down.down).op
          (L.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op s.val) =
        L.val.map (homOfLE (le_top : W.unop ≤ ⊤)).op s.val
      rw [← L.val.map_comp_apply]
      have hh : (homOfLE (le_top : V.unop ≤ ⊤)).op ≫ (homOfLE f.unop.down.down).op =
          (homOfLE (le_top : W.unop ≤ ⊤)).op := Subsingleton.elim _ _
      rw [hh])
  let f := L.unitHomEquiv.symm t
  have hf : IsIso f := by
    refine Stacks.SheafOfModules.isIso_of_isIso_val_app f fun V => ?_
    have hbij : Function.Bijective (f.val.app V) := by
      let W := V.unop
      let _ : CommRing (R.obj.obj (op W)) := inferInstanceAs (CommRing (X.presheaf.obj (op W)))
      change Function.Bijective (fun r : R.obj.obj (op W) =>
        @SMul.smul _ _ _ r (L.val.map (homOfLE (le_top : W ≤ ⊤)).op s.val))
      exact s.property W le_top
    exact (ConcreteCategory.isIso_iff_bijective (f.val.app V)).2 hbij
  exact asIso f

end Stacks.Cohomology.Generators

end

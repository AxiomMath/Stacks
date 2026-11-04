module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonGlobalSection
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonNatural

/-!
# The canonical map of Tag 0EX3 (b) at the structure sheaf of the base

The invertibility half of conclusion (b) of [Stacks, Tag 0EX3] is run, following the source,
against the value of the canonical map at `G = 𝒪_Y`.  This file computes that value: it is the
right unitor of `TensorComparisonUnitor.lean` followed by the `n`-th higher direct image of
`x ↦ x ⊗ η`, where `η` is the global section of `f^* 𝒪_Y` that the unit of `f^* ⊣ f_*` attaches
to the unit section of `𝒪_Y`.

What makes the computation short is that the bilinear family of conclusion (b) is linear in the
section of `G` (`tensorTopSection_smul`), and over `𝒪_Y` every section is a multiple of the unit
section.  So the value of the canonical map on a local pure tensor `a ⊗ t` is `t` times its value
on `a ⊗ 1`, and the whole map is pinned down by its value at the unit section, where it is the
higher direct image of a morphism on `X` itself — which is what
`TensorComparisonGlobalSection.lean` supplies.

Nothing is assumed: `f` is an arbitrary morphism of schemes, `F` an arbitrary sheaf of modules
on `X` and `n` an arbitrary degree.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.unitGlobalSection`: the global section of `f^* G`
  attached by the unit of `f^* ⊣ f_*` to a global section of `G`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.unitValueMap`: the morphism
  `R^n f_* F ⟶ R^n f_*(F ⊗ f^* 𝒪_Y)` whose sections the value of the canonical map at `𝒪_Y` is.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `unitGlobalSection_restrict`: the unit carries the restriction of a global section to the
  restriction of `unitGlobalSection`.
* `higherDirectImageTensorSection_globalRestrict`: **the bilinear family at the restriction of a
  global section is the restriction of one morphism of sheaves on `Y`**, namely the `n`-th higher
  direct image of `x ↦ x ⊗ η`.
* `tensorTopSection_globalRestrict` and `tensorTopSection_unitModule`: the same, read on
  sections, and at the structure sheaf of the base where every section is a multiple of the unit
  section.
* `higherDirectImageTensorMap_structureModule`: **the canonical map of conclusion (b) at
  `G = 𝒪_Y` is the right unitor followed by the higher direct image of `x ↦ x ⊗ η`.**

## Implementation notes

`higherDirectImageTensorSection_globalRestrict` is an instance of `conjugateRestrict_naturality`
at the identity morphism upstairs: the bilinear family is a conjugate of
`(R^n (f ∣_ V)_*)` applied to a local morphism, and taking that local morphism to be the
restriction of a global one is exactly what the naturality statement of
`TensorComparisonNatural.lean` turns into a restriction of the global higher direct image.  So
no new transport along the comparison of [Stacks, Tag 01E5] is written here.

The discipline of this directory is kept: the statements below are in the
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling of a restriction, and no declaration
pairs two spellings of one right-derived-functor object twice.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (n : ℕ)

/-! ### The unit of `f^* ⊣ f_*` on a global section -/

/-- **The global section of `f^* G` attached by the unit of `f^* ⊣ f_*` to a global section of
`G`.** -/
def unitGlobalSection (s : Γ(G, ⊤)) : Γ((Scheme.Modules.pullback f).obj G, ⊤) :=
  Scheme.Modules.Hom.app
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ⊤ s

/-- **The unit carries the restriction of a global section to the restriction of
`unitGlobalSection`.** This is the naturality of the unit, which is a morphism of sheaves on
`Y`, together with the uniqueness of an inclusion of opens. -/
theorem unitGlobalSection_restrict (s : Γ(G, ⊤)) (V : Y.Opens) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) V
        (globalRestrict G s V) =
      globalRestrict ((Scheme.Modules.pullback f).obj G) (unitGlobalSection f G s) (f ⁻¹ᵁ V) := by
  refine (ModuleLimits.Hom_app_presheaf_map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G)
    (le_top : V ≤ ⊤) s).symm.trans ?_
  exact congrArg (fun j : (op (⊤ : X.Opens) ⟶ op (f ⁻¹ᵁ V)) =>
      ((Scheme.Modules.pullback f).obj G).presheaf.map j (unitGlobalSection f G s))
    (Subsingleton.elim _ _)

/-! ### The bilinear family at the restriction of a global section -/

/-- **The bilinear family of conclusion (b) at the restriction of a global section is the
restriction of one morphism of sheaves on `Y`**: the `n`-th higher direct image of
`x ↦ x ⊗ η`. -/
theorem higherDirectImageTensorSection_globalRestrict (s : Γ(G, ⊤)) (V : Y.Opens) :
    higherDirectImageTensorSection f F G n V (globalRestrict G s V) =
      (Scheme.Modules.restrictFunctor V.ι).map
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
          (tensorGlobalSection F ((Scheme.Modules.pullback f).obj G)
            (unitGlobalSection f G s))) := by
  have hloc : tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) V
        (globalRestrict G s V)) =
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map
        (tensorGlobalSection F ((Scheme.Modules.pullback f).obj G)
          (unitGlobalSection f G s)) := by
    rw [unitGlobalSection_restrict f G s V,
      tensorGlobalSection_restrictFunctor F ((Scheme.Modules.pullback f).obj G)
        (unitGlobalSection f G s) (f ⁻¹ᵁ V)]
  have key := conjugateRestrict_naturality f F n V F
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback f).obj G)))
    (tensorGlobalSection F ((Scheme.Modules.pullback f).obj G) (unitGlobalSection f G s))
    (𝟙 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map
      (tensorGlobalSection F ((Scheme.Modules.pullback f).obj G)
        (unitGlobalSection f G s)))
    (Category.id_comp _)
  rw [higherDirectImageTensorSection_eq f F G n V (globalRestrict G s V), hloc, ← key,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.id_comp]

/-- **The candidate value on sections at the restriction of a global section** is the higher
direct image of `x ↦ x ⊗ η`, read on sections over `V`. -/
theorem tensorTopSection_globalRestrict (s : Γ(G, ⊤)) (V : Y.Opens)
    (a : Γ(topDirectImage f F n, V)) :
    tensorTopSection f F G n V (globalRestrict G s V) a =
      Scheme.Modules.Hom.app
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
          (tensorGlobalSection F ((Scheme.Modules.pullback f).obj G)
            (unitGlobalSection f G s))) V a := by
  rw [tensorTopSection, higherDirectImageTensorSection_globalRestrict f F G n s V,
    topReading_restrictFunctor_map]

/-! ### The canonical map at the structure sheaf of the base -/

/-- Every section of the structure sheaf is its own multiple of the unit section. -/
theorem smul_globalRestrict_one (U : Y.Opens) (t : Γ(Scheme.unitModule Y, U)) :
    unitRingSection (op U) t • globalRestrict (Scheme.unitModule Y)
        (1 : ↑(Y.presheaf.obj (op ⊤))) U = t := by
  rw [show globalRestrict (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤))) U =
      (1 : ↑(Y.presheaf.obj (op U))) from
    PresheafOfModules.unit_map_one Y.ringCatSheaf.obj
      (homOfLE (le_top : U ≤ ⊤)).op]
  exact mul_one (unitRingSection (op U) t)

/-- Abbreviation for the morphism `R^n f_* F ⟶ R^n f_*(F ⊗ f^* 𝒪_Y)` whose sections the value of
the canonical map at the structure sheaf is. -/
abbrev unitValueMap : topDirectImage f F n ⟶ topDirectImageTensor f F (Scheme.unitModule Y) n :=
  ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
    (tensorGlobalSection F ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y))
      (unitGlobalSection f (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤)))))

/-- **The candidate value on sections at the structure sheaf of the base.**  Every section of
`𝒪_Y` over `U` is its own multiple of the unit section, and the family is linear in the section
of `G`, so the value at `t` is `t` times the value at the unit section. -/
theorem tensorTopSection_unitModule (U : Y.Opens) (t : Γ(Scheme.unitModule Y, U))
    (a : Γ(topDirectImage f F n, U)) :
    tensorTopSection f F (Scheme.unitModule Y) n U t a =
      unitRingSection (op U) t • Scheme.Modules.Hom.app (unitValueMap f F n) U a := by
  conv_lhs => rw [← smul_globalRestrict_one U t]
  rw [tensorTopSection_smul f U F (Scheme.unitModule Y) n (unitRingSection (op U) t) _ a,
    tensorTopSection_globalRestrict f F (Scheme.unitModule Y) n
      (1 : ↑(Y.presheaf.obj (op ⊤))) U a]

/-- **The canonical map of conclusion (b) of [Stacks, Tag 0EX3] at `G = 𝒪_Y`** is the right
unitor `R^n f_* F ⊗ 𝒪_Y ≅ R^n f_* F` followed by the `n`-th higher direct image of
`x ↦ x ⊗ η`.

Two morphisms out of a tensor sheaf agree as soon as they agree on the local pure tensors
(`hom_ext_of_tensorSection`), and there both sides are `t` times their value at the unit
section: on the left by `tensorTopSection_unitModule`, on the right because the unitor sends
`a ⊗ t` to `t • a` and a morphism of modules acts linearly on sections. -/
theorem higherDirectImageTensorMap_structureModule :
    higherDirectImageTensorMap f F (Scheme.unitModule Y) n =
      tensorUnitHom (topDirectImage f F n) ≫ unitValueMap f F n := by
  refine hom_ext_of_tensorSection fun W a t => ?_
  have hL : Scheme.Modules.Hom.app
      (higherDirectImageTensorMap f F (Scheme.unitModule Y) n) W.unop
      (toTensorSheafSection Y.toRingedSpace (topDirectImage f F n) (Scheme.unitModule Y)
        (op W.unop) (a ⊗ₜ[Y.presheaf.obj (op W.unop)] t)) =
      unitRingSection (op W.unop) t •
        Scheme.Modules.Hom.app (unitValueMap f F n) W.unop a := by
    rw [higherDirectImageTensorMap_tmul f F (Scheme.unitModule Y) n W.unop a t]
    exact tensorTopSection_unitModule f F n W.unop t a
  have hR : ((tensorUnitHom (topDirectImage f F n) ≫ unitValueMap f F n).val.app
        (op W.unop)).hom
      (toTensorSheafSection Y.toRingedSpace (topDirectImage f F n) (Scheme.unitModule Y)
        (op W.unop) (a ⊗ₜ[Y.presheaf.obj (op W.unop)] t)) =
      unitRingSection (op W.unop) t •
        Scheme.Modules.Hom.app (unitValueMap f F n) W.unop a := by
    show Scheme.Modules.Hom.app (unitValueMap f F n) W.unop
        (((tensorUnitHom (topDirectImage f F n)).val.app (op W.unop)).hom
          (toTensorSheafSection Y.toRingedSpace (topDirectImage f F n) (Scheme.unitModule Y)
            (op W.unop) (a ⊗ₜ[Y.presheaf.obj (op W.unop)] t))) = _
    rw [tensorUnitHom_toTensorSheafSection (topDirectImage f F n) (op W.unop) a t]
    exact Scheme.Modules.Hom.app_smul _ (unitRingSection (op W.unop) t) a
  exact hL.trans hR.symm

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

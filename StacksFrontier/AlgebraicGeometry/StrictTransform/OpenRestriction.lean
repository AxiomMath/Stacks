module

public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSectionsRestrict
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent

/-!
# The strict transform is computed on an open of the base change

Let `f : X ⟶ S`, `b : S' ⟶ S` and `E : S'.IdealSheafData` be data for a strict transform, and let
`f₂ : Y ⟶ T`, `b₂ : T' ⟶ T` and `E₂` be a second such package together with an open immersion
`j : Y ×_T T' ⟶ X ×_S S'` of the two ambient base changes which identifies the two exceptional
preimages. Then the defining ideal of the strict transform of `X` restricts along `j` to the
defining ideal of the strict transform of `Y`, and — given the matching identification of the
pulled-back modules — the strict transform of a module restricts to the strict transform of its
restriction.

This is what makes a strict transform local on the base: for `T` an open of `S` and `T'` the
corresponding open of `S'`, the hypotheses hold and the conclusions say that the strict transform
over that open is the restriction of the strict transform.

## Main results

* `Stacks.StrictTransform.ideal_comap_of_isOpenImmersion`: the inverse image of the defining ideal
  of a strict transform is the defining ideal of the strict transform.
* `Stacks.StrictTransform.schemeRestrictIso`: the strict transform of `Y` is the base change of
  the strict transform of `X` along `j`.
* `Stacks.StrictTransform.sheafRestrictIso`: the strict transform of a module restricts to the
  strict transform of the restricted module, on the ambient base change.
* `Stacks.StrictTransform.moduleRestrictIso`: the same, for the module carried by the strict
  transform itself.

## Implementation notes

The ideal statement is read off from the description of the defining ideal on affine opens,
`Stacks.StrictTransform.ideal_eq`, which needs the two exceptional complements to have
quasi-compact inclusion — for a blowup this is
`Stacks.Blowup.quasiCompact_ι_exceptionalPullbackCompl` and costs nothing. The comparison of the
two modules of supported sections is
`AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_restrict_iff`.

A near-miss worth recording:
`Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsRestrictIso` is the same
restriction statement for `Stacks.SheafOfModules.SupportedSections.supportedSectionsSheaf` and an
open subscheme of the ambient. It is not usable here, because the strict transform is built
from `AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule` and the open immersion `j` is
not the inclusion of an open subscheme; bridging the two spellings is a separate job.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The pullback of a module along a commuting square.** For a square `g ≫ i = i' ≫ h` and a
module `F` on the target of `i` whose pullback along `h` is identified with a module `F'`, the
pullback of `F'` along `i'` is the pullback along `g` of the pullback of `F` along `i`. -/
public def pullbackModuleIsoOfSquare {X Y X' Y' : Scheme.{u}} (i : X ⟶ Y) (i' : X' ⟶ Y')
    (g : X' ⟶ X) (h : Y' ⟶ Y) (w : g ≫ i = i' ≫ h) (F : Y.Modules) (F' : Y'.Modules)
    (e : F' ≅ (Scheme.Modules.pullback h).obj F) :
    (Scheme.Modules.pullback i').obj F' ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj F) :=
  (Scheme.Modules.pullback i').mapIso e ≪≫ (Scheme.Modules.pullbackComp i' h).app F ≪≫
    (Scheme.Modules.pullbackCongr w.symm).app F ≪≫
    ((Scheme.Modules.pullbackComp g i).app F).symm

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.StrictTransform

open AlgebraicGeometry.Scheme.Modules hiding pullback

variable {X S S' Y T T' : Scheme.{u}} (f : X ⟶ S) (b : S' ⟶ S) (E : S'.IdealSheafData)
  (f₂ : Y ⟶ T) (b₂ : T' ⟶ T) (E₂ : T'.IdealSheafData)

/-- **The defining ideal of a strict transform is computed on an open of the base change.** -/
public theorem ideal_comap_of_isOpenImmersion [QuasiCompact (exceptionalComplement f b E).ι]
    [QuasiCompact (exceptionalComplement f₂ b₂ E₂).ι]
    (j : baseChange f₂ b₂ ⟶ baseChange f b) [IsOpenImmersion j]
    (hZ : exceptionalPreimage f₂ b₂ E₂ = j.base ⁻¹' exceptionalPreimage f b E) :
    (ideal f b E).comap j = ideal f₂ b₂ E₂ := by
  refine Scheme.IdealSheafData.ext (funext fun U ↦ ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, ideal_eq, ideal_eq]
  refine Ideal.ext fun s ↦ Ideal.mem_comap.trans ?_
  exact (mem_supportedSectionsSubmodule_restrict_iff' j (exceptionalPreimage f b E)
      (exceptionalPreimage f₂ b₂ E₂) hZ (SheafOfModules.unit (baseChange f b).ringCatSheaf) U.1
      ((restrictUnitIso j).inv.app U.1 s)).symm.trans
    (mem_supportedSectionsSubmodule_iso_iff (exceptionalPreimage f₂ b₂ E₂)
      (restrictUnitIso j).symm U.1 s)

/-- **The strict transform of `Y` is the base change along `j` of the strict transform of
`X`.** -/
public def schemeRestrictIso [QuasiCompact (exceptionalComplement f b E).ι]
    [QuasiCompact (exceptionalComplement f₂ b₂ E₂).ι]
    (j : baseChange f₂ b₂ ⟶ baseChange f b) [IsOpenImmersion j]
    (hZ : exceptionalPreimage f₂ b₂ E₂ = j.base ⁻¹' exceptionalPreimage f b E) :
    scheme f₂ b₂ E₂ ≅ Limits.pullback (ideal f b E).subschemeι j :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (ideal_comap_of_isOpenImmersion f b E f₂ b₂ E₂ j hZ)).symm ≪≫
    (ideal f b E).comapIso j ≪≫ pullbackSymmetry j (ideal f b E).subschemeι

/-- The isomorphism `schemeRestrictIso`, followed by the second projection of the pullback, is
the closed immersion of the strict transform of `Y`. -/
@[reassoc]
public lemma schemeRestrictIso_hom_snd [QuasiCompact (exceptionalComplement f b E).ι]
    [QuasiCompact (exceptionalComplement f₂ b₂ E₂).ι]
    (j : baseChange f₂ b₂ ⟶ baseChange f b) [IsOpenImmersion j]
    (hZ : exceptionalPreimage f₂ b₂ E₂ = j.base ⁻¹' exceptionalPreimage f b E) :
    (schemeRestrictIso f b E f₂ b₂ E₂ j hZ).hom ≫
        pullback.snd (ideal f b E).subschemeι j =
      (ideal f₂ b₂ E₂).subschemeι := by
  rw [schemeRestrictIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    pullbackSymmetry_hom_comp_snd, Scheme.IdealSheafData.comapIso_hom_fst, eqToIso.hom]
  exact AlgebraicGeometry.eqToHom_subscheme_comp_subschemeι _ _
    (ideal_comap_of_isOpenImmersion f b E f₂ b₂ E₂ j hZ).symm

/-- **The strict transform of a module is computed on an open of the base change.** -/
public def sheafRestrictIso [QuasiCompact (exceptionalComplement f b E).ι]
    [QuasiCompact (exceptionalComplement f₂ b₂ E₂).ι]
    (j : baseChange f₂ b₂ ⟶ baseChange f b) [IsOpenImmersion j]
    (hZ : exceptionalPreimage f₂ b₂ E₂ = j.base ⁻¹' exceptionalPreimage f b E)
    (F : X.Modules) (F₂ : Y.Modules)
    (eF : (Scheme.Modules.pullback (pullback.fst f₂ b₂)).obj F₂ ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (pullback.fst f b)).obj F)) :
    sheaf f₂ b₂ E₂ F₂ ≅ (Scheme.Modules.pullback j).obj (sheaf f b E F) :=
  supportedQuotientRestrictIso j (exceptionalPreimage f b E) (exceptionalPreimage f₂ b₂ E₂) hZ
    ((Scheme.Modules.pullback (pullback.fst f b)).obj F)
    ((Scheme.Modules.pullback (pullback.fst f₂ b₂)).obj F₂) eF

/-- **The strict transform of a module, as a module on the strict transform itself, is computed on
an open of the base change.** -/
public def moduleRestrictIso [QuasiCompact (exceptionalComplement f b E).ι]
    [QuasiCompact (exceptionalComplement f₂ b₂ E₂).ι]
    (j : baseChange f₂ b₂ ⟶ baseChange f b) [IsOpenImmersion j]
    (hZ : exceptionalPreimage f₂ b₂ E₂ = j.base ⁻¹' exceptionalPreimage f b E)
    (F : X.Modules) (F₂ : Y.Modules)
    (eF : (Scheme.Modules.pullback (pullback.fst f₂ b₂)).obj F₂ ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (pullback.fst f b)).obj F)) :
    (Scheme.Modules.pullback (ideal f₂ b₂ E₂).subschemeι).obj (sheaf f₂ b₂ E₂ F₂) ≅
      (Scheme.Modules.pullback (schemeRestrictIso f b E f₂ b₂ E₂ j hZ).hom).obj
        ((Scheme.Modules.pullback
            (pullback.fst (ideal f b E).subschemeι j)).obj
          ((Scheme.Modules.pullback (ideal f b E).subschemeι).obj (sheaf f b E F))) := by
  set i := (ideal f b E).subschemeι with hi
  set i₂ := (ideal f₂ b₂ E₂).subschemeι with hi₂
  set eX := schemeRestrictIso f b E f₂ b₂ E₂ j hZ with heX
  have hleft : eX.hom ≫ pullback.snd i j = i₂ :=
    schemeRestrictIso_hom_snd f b E f₂ b₂ E₂ j hZ
  have hw : (eX.hom ≫ pullback.fst i j) ≫ i = i₂ ≫ j := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hleft]
  refine Scheme.Modules.pullbackModuleIsoOfSquare i i₂ (eX.hom ≫ pullback.fst i j) j hw
      (sheaf f b E F) (sheaf f₂ b₂ E₂ F₂)
      (sheafRestrictIso f b E f₂ b₂ E₂ j hZ F F₂ eF) ≪≫ ?_
  exact ((Scheme.Modules.pullbackComp eX.hom (pullback.fst i j)).app
    ((Scheme.Modules.pullback i).obj (sheaf f b E F))).symm

end Stacks.StrictTransform

end

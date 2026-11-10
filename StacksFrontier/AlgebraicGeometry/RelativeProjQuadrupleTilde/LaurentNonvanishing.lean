module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Laurent
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality

/-!
# A section nonvanishing everywhere names an isomorphism out of the structure sheaf

Let `M` be an invertible module on a scheme `X` and `s` a global section of `M` whose
nonvanishing open is all of `X`. Then the morphism `𝒪_X ⟶ M`, `1 ↦ s`, named by `s` is an
isomorphism: on the sections over every open `W` it is `a ↦ a • s|_W`, which is bijective because
`W` lies in the nonvanishing open of `s` (`Stacks.NonvanishingSpelling.bijective_smul`).

The morphism named by a section is natural in the module, so the same holds for the image of `s`
under any isomorphism of modules; this is how a nonvanishing section of `L` gives an isomorphism
`𝒪_X ⟶ L^{⊗ 1}` onto the degree-one piece of the Laurent algebra.

## Main results

* `LaurentSections.isIso_secHom_of_nonvanishingOpen_eq_top`: **the morphism named by an
  everywhere nonvanishing section is an isomorphism.**
* `LaurentSections.secHom_comp`: the morphism named by a section followed by a morphism of modules
  is the morphism named by the image section.
* `LaurentSections.isIso_secHom_of_isIso`: the morphism named by the image of a section under an
  isomorphism is an isomorphism when the one named by the section is.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MonoidalCategory
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

variable {X : Scheme.{u}}

/-- **The morphism `𝒪_X ⟶ M` named by an everywhere nonvanishing global section of an invertible
module is an isomorphism.** -/
theorem isIso_secHom_of_nonvanishingOpen_eq_top
    (M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    [Stacks.Ample.IsInvertibleModule X M] (s : M.val.obj (op ⊤))
    (h : Stacks.NonvanishingOpen.nonvanishingOpen X M s = ⊤) : IsIso (secHom M s) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun W => ?_
  have hb := Stacks.NonvanishingSpelling.bijective_smul X M s (W := W.unop) (h ▸ le_top)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

/-- **The morphism named by a section, followed by a morphism of modules**, is the morphism named
by the image section. -/
theorem secHom_comp {F G : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (e : F ⟶ G)
    (x : F.val.obj (op ⊤)) : secHom F x ≫ e = secHom G (e.val.app (op ⊤) x) := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  change e.val.app V ((secHom F x).val.app V r) = (secHom G (e.val.app (op ⊤) x)).val.app V r
  rw [secHom_app F x V r, secHom_app G _ V r]
  have hn : (e.val.app V).hom (F.val.restrictₛₗ (topRes X V) x) =
      G.val.restrictₛₗ (topRes X V) (e.val.app (op ⊤) x) :=
    PresheafOfModules.naturality_apply e.val (topRes X V) x
  refine ((e.val.app V).hom.map_smul _ _).trans ?_
  rw [hn]

/-- The morphism named by the image of a section under an isomorphism of modules is an
isomorphism when the morphism named by the section is. -/
theorem isIso_secHom_of_isIso {F G : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)}
    (e : F ⟶ G) [IsIso e] (x : F.val.obj (op ⊤)) [IsIso (secHom F x)] :
    IsIso (secHom G (e.val.app (op ⊤) x)) := by
  rw [← secHom_comp]
  infer_instance

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

end

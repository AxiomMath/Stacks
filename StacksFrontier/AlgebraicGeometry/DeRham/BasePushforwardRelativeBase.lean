module

public import StacksFrontier.AlgebraicGeometry.DeRham.BasePushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence

/-!
# The two direct images over the base rings agree

For morphisms of schemes `g : Y ⟶ X` and `f : X ⟶ S`, two constructions of the direct image of
sheaves of `(g ≫ f)^{-1}𝒪_S`-modules on `Y` to sheaves of `f^{-1}𝒪_S`-modules on `X` occur in the
library: `AlgebraicGeometry.Scheme.Hom.basePushforward g f`, the pushforward along the comparison
of base rings `AlgebraicGeometry.Scheme.Hom.baseRingCompHom g f`, and the pushforward of modules
along the morphism of ringed spaces `Stacks.DeRhamSmooth.relativeBase g f`. This file proves that
they are equal: the two comparisons `f^{-1}𝒪_S ⟶ g_*(g ≫ f)^{-1}𝒪_S` of base rings are the same
morphism, both being adjoint to the unit of the inverse image along `g ≫ f`.

## Main results

* `TopCat.Sheaf.pullbackPushforwardAdjunction_homEquiv_symm_unit_comp`: the adjoint of the unit
  of the inverse image along a composite.
* `AlgebraicGeometry.Scheme.Hom.baseRingCompHom_eq_relativeBase_c`: the two comparisons of base
  rings agree.
* `AlgebraicGeometry.Scheme.Hom.basePushforward_eq_modulePushforward`: the two direct images
  agree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace TopCat.Sheaf

/-- **The adjoint of the unit of the inverse image along a composite.** For continuous maps
`i : Z ⟶ W` and `j : W ⟶ X` and a sheaf of rings `𝒪` on `X`, the map
`j^{-1}𝒪 ⟶ i_*(i ≫ j)^{-1}𝒪` adjoint to the unit `𝒪 ⟶ (i ≫ j)_*(i ≫ j)^{-1}𝒪` is the unit of
`i` at `j^{-1}𝒪` followed by the comparison `i^{-1}j^{-1} ≅ (i ≫ j)^{-1}`. -/
theorem pullbackPushforwardAdjunction_homEquiv_symm_unit_comp {Z W X : TopCat.{u}} (i : Z ⟶ W)
    (j : W ⟶ X) (𝒪 : TopCat.Sheaf CommRingCat.{u} X) :
    ((pullbackPushforwardAdjunction CommRingCat.{u} j).homEquiv 𝒪
        ((pushforward CommRingCat.{u} i).obj ((pullback CommRingCat.{u} (i ≫ j)).obj 𝒪))).symm
        ((pullbackPushforwardAdjunction CommRingCat.{u} (i ≫ j)).unit.app 𝒪) =
      (pullbackPushforwardAdjunction CommRingCat.{u} i).unit.app
          ((pullback CommRingCat.{u} j).obj 𝒪) ≫
        (pushforward CommRingCat.{u} i).map
          ((sheafPullbackCompIso i j CommRingCat.{u}).inv.app 𝒪) := by
  apply ((pullbackPushforwardAdjunction CommRingCat.{u} j).homEquiv _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  rw [Adjunction.homEquiv_unit]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (pullbackPushforwardAdjunction CommRingCat.{u} (i ≫ j))
    (((pullbackPushforwardAdjunction CommRingCat.{u} j).comp
      (pullbackPushforwardAdjunction CommRingCat.{u} i)).ofNatIsoRight
        (sheafPushforwardCompIso i j CommRingCat.{u}).symm) 𝒪
  rw [← sheafPullbackCompIso_compat] at h
  have h' : (pullbackPushforwardAdjunction CommRingCat.{u} (i ≫ j)).unit.app 𝒪 =
      (((pullbackPushforwardAdjunction CommRingCat.{u} j).comp
        (pullbackPushforwardAdjunction CommRingCat.{u} i)).ofNatIsoRight
          (sheafPushforwardCompIso i j CommRingCat.{u}).symm).unit.app 𝒪 ≫
        (pushforward CommRingCat.{u} (i ≫ j)).map
          ((sheafPullbackCompIso i j CommRingCat.{u}).inv.app 𝒪) := by
    rw [← h, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  rw [h']
  simp [Adjunction.comp_unit_app, sheafPushforwardCompIso]
  rfl

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Hom

variable {Y X S : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ S)

/-- **The two comparisons of base rings agree**: `baseRingCompHom g f` is the structure map of the
morphism of ringed spaces `Stacks.DeRhamSmooth.relativeBase g f`. -/
theorem baseRingCompHom_eq_relativeBase_c :
    (baseRingCompHom g f).hom = (Stacks.DeRhamSmooth.relativeBase g f).hom.c := by
  have h := TopCat.Sheaf.pullbackPushforwardAdjunction_homEquiv_symm_unit_comp g.base f.base
    S.sheaf
  exact (congrArg (fun φ => φ.hom) h).symm

/-- **The two direct images over the base rings agree.** -/
theorem basePushforward_eq_modulePushforward :
    basePushforward g f = modulePushforward (Stacks.DeRhamSmooth.relativeBase g f) := by
  have h : baseRingCompRingHom g f = structureSheafHom (Stacks.DeRhamSmooth.relativeBase g f) :=
    ObjectProperty.hom_ext _
      (congrArg (fun φ => Functor.whiskerRight φ (forget₂ CommRingCat RingCat))
        (baseRingCompHom_eq_relativeBase_c g f))
  exact congrArg SheafOfModules.pushforward h

end AlgebraicGeometry.Scheme.Hom

end

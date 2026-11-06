module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension

/-!
# Coextension of scalars commutes with restriction to a localized site

Let `φ : O ⟶ O'` be a morphism of sheaves of rings on a site `(C, J)` and let `U` be an object
of `C`. Restricting the coextension of scalars `SheafHom_O(O', B)` of Stacks Tag 0932 to the
localized site `C/U` gives the coextension of scalars along the restricted morphism
`φ|_U : O|_U ⟶ O'|_U`,

`SheafHom_O(O', B)|_U ≅ SheafHom_{O|_U}(O'|_U, B|_U)`,

as sheaves of `O'|_U`-modules.

This is the statement that makes Tag 0932 usable on the slice sites, and therefore usable on
the internal Hom complex `Stacks.SheafOfModules.sheafHomComplex`, whose interface is its
sections over each slice. It is the coextension-of-scalars companion of
`Stacks.SheafOfModules.InternalHom.internalHomOverIso`, Tag 0E8H, which is the same statement
for the internal Hom of two sheaves of modules over one fixed sheaf of rings; what is new here
is that the comparison is linear for the right-multiplication `O'`-action, which Tag 0E8H does
not see.

## Main definitions

* `Stacks.SheafOfModules.CoextendScalars.coextOverHom`: the comparison morphism.
* `Stacks.SheafOfModules.CoextendScalars.sheafCoextOverIso`: **the isomorphism above.**
* `Stacks.SheafOfModules.CoextendScalars.sheafCoextendScalarsOverIso`: the same isomorphism,
  as an isomorphism of functors.

## Main results

* `Stacks.SheafOfModules.CoextendScalars.coextOverHom_app_apply`: on a section of
  `SheafHom_O(O', B)` over `V ⟶ U`, the comparison is restriction of that local morphism along
  the iterated-slice functor `(C/U)/V ⥤ C/V`. This pins the comparison down rather than
  merely asserting that some isomorphism exists.
* `Stacks.SheafOfModules.CoextendScalars.coextOverHom_naturality`: the comparison is natural
  in the sheaf of `O`-modules.

## Implementation notes

The comparison morphism is not written out by hand. Restriction of scalars commutes with
restriction to `C/U` on the nose — `restrictScalars_over` is `rfl` — so the counit
`SheafHom_O(O', B)_O ⟶ B` of Tag 0932, restricted to `C/U`, is already a morphism
`(SheafHom_O(O', B)|_U)_{O|_U} ⟶ B|_U`, and `coextOverHom` is its transpose under Tag 0932 on
`C/U`. Naturality in the object of `C/U` therefore costs nothing; writing the comparison out
sectionwise instead puts an `eqToHom`-laden naturality square in the way, since the restriction
maps of `SheafHom_O(O', B)` are conjugated by the coherence isomorphisms
`Stacks.PresheafOfModules.CoextendScalars.overRestrictIso`.

Bijectivity is checked on sections, where the comparison is restriction of a local morphism
along the iterated-slice equivalence `(C/U)/V ≌ C/V`: that equivalence identifies the sheaves
of modules on the two slices (`sliceModulesEquiv`), and the forgetful functor from sheaves of
modules to presheaves of modules is fully faithful, so the two sets of local morphisms agree.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.PresheafOfModules.CoextendScalars

namespace Stacks.SheafOfModules.CoextendScalars

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O O' : Sheaf J RingCat.{u}}

/-- A morphism of sheaves of rings on `C`, restricted to the localized site `C/U`. -/
abbrev sliceHom (φ : O ⟶ O') (U : C) : O.over U ⟶ O'.over U :=
  (J.overPullback RingCat.{u} U).map φ

/-- Restriction of scalars along `φ` commutes with restriction to the localized site `C/U`:
the two functors `SheafOfModules O' ⥤ SheafOfModules (O|_U)` are equal. -/
theorem restrictScalars_over (φ : O ⟶ O') (U : C) (G : _root_.SheafOfModules.{u} O') :
    ((_root_.SheafOfModules.restrictScalars φ).obj G).over U =
      (_root_.SheafOfModules.restrictScalars (sliceHom φ U)).obj (G.over U) :=
  rfl

/-- Sheaves of modules on the localized site `C/V.left` and on the iterated slice `(C/U)/V`
agree, along the iterated-slice equivalence `(C/U)/V ≌ C/V.left`. -/
def sliceModulesEquiv (O : Sheaf J RingCat.{u}) (U : C) (V : Over U) :
    _root_.SheafOfModules.{u} (O.over V.left) ≌
      _root_.SheafOfModules.{u} ((O.over U).over V) := by
  let E := Over.iteratedSliceEquiv V
  let S := (O.over U).over V
  let R := O.over V.left
  let φ : S ⟶ (E.functor.sheafPushforwardContinuous RingCat _ _).obj R := 𝟙 _
  let ψ : R ⟶ (E.inverse.sheafPushforwardContinuous RingCat _ _).obj S := 𝟙 _
  exact _root_.SheafOfModules.pushforwardPushforwardEquivalence E φ ψ
    (by ext : 2; exact O.1.map_id _)
    (by ext : 2; exact O.1.map_id _)

/-- `O'`, viewed as a sheaf of `O`-modules along `φ`. -/
abbrev unitAsModule (φ : O ⟶ O') : _root_.SheafOfModules.{u} O :=
  (_root_.SheafOfModules.restrictScalars φ).obj (.unit O')

/-- A section of `SheafHom_O(O', B)` over `V.left`, that is an `O|_{V.left}`-linear morphism
`O'|_{V.left} ⟶ B|_{V.left}`, read as a section of `SheafHom_{O|_U}(O'|_U, B|_U)` over `V`,
that is an `(O|_U)|_V`-linear morphism on the iterated slice `(C/U)/V`. -/
def coextOverSection (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O) (V : Over U)
    (α : coextSec φ.hom B.val (op V.left)) :
    coextSec (sliceHom φ U).hom (B.over U).val (op V) := by
  let e := sliceModulesEquiv O U V
  let α₁ : (unitAsModule φ).over V.left ⟶ B.over V.left :=
    (_root_.SheafOfModules.fullyFaithfulForget _).preimage α
  exact (_root_.SheafOfModules.forget _).map (e.functor.map α₁)

/-- The comparison on sections over `V ⟶ U` is a bijection: the iterated-slice equivalence is
fully faithful, and so is the forgetful functor from sheaves of modules. -/
def coextOverSectionEquiv (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O) (V : Over U) :
    coextSec φ.hom B.val (op V.left) ≃ coextSec (sliceHom φ U).hom (B.over U).val (op V) := by
  let e := sliceModulesEquiv O U V
  let A := (unitAsModule φ).over V.left
  let Bo := B.over V.left
  let hA := _root_.SheafOfModules.fullyFaithfulForget (O.over V.left)
  let hA' := _root_.SheafOfModules.fullyFaithfulForget ((O.over U).over V)
  exact (hA.homEquiv (X := A) (Y := Bo)).symm.trans
    ((e.fullyFaithfulFunctor.homEquiv (X := A) (Y := Bo)).trans
      (hA'.homEquiv (X := e.functor.obj A) (Y := e.functor.obj Bo)))

/-- The forward map of `coextOverSectionEquiv` is `coextOverSection`. -/
theorem coextOverSectionEquiv_toFun (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O)
    (V : Over U) :
    (coextOverSectionEquiv φ U B V).toFun = coextOverSection φ U B V := by
  rfl

/-- On sections, the comparison is restriction of a local morphism along the iterated-slice
functor `(C/U)/V ⥤ C/V.left`. -/
theorem coextOverSection_app (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O)
    (V : Over U) (α : coextSec φ.hom B.val (op V.left)) (W : (Over V)ᵒᵖ)
    (x : (restrictToOver V (O'asOModule (sliceHom φ U).hom)).obj W) :
    ((coextOverSection φ U B V α).app W).hom x =
      (α.app ((Over.iteratedSliceForward V).op.obj W)).hom x :=
  rfl

/-- **The comparison `SheafHom_O(O', B)|_U ⟶ SheafHom_{O|_U}(O'|_U, B|_U)`**: the transpose,
under Tag 0932 on the localized site `C/U`, of the restriction to `C/U` of the counit
`SheafHom_O(O', B)_O ⟶ B` of Tag 0932 on `C`. -/
def coextOverHom (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O) :
    ((coextendScalars φ).obj B).over U ⟶
      (coextendScalars (sliceHom φ U)).obj (B.over U) :=
  coextendScalarsSheafHomEquiv (sliceHom φ U) (((coextendScalars φ).obj B).over U) (B.over U)
    ((_root_.SheafOfModules.overFunctor O U).map
      ((restrictScalars_coextendScalars_adjunction φ).counit.app B))

/-- **The comparison, on a section.** A section of `SheafHom_O(O', B)` over `V ⟶ U` is a local
morphism `O'|_{V.left} ⟶ B|_{V.left}`, and the comparison restricts it along the
iterated-slice functor: its value on `W ⟶ V` at `a' ∈ O'(W.left.left)` is the value of the
original at the composite `W.left.left ⟶ V.left`. -/
theorem coextOverHom_app_apply (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O)
    (V : (Over U)ᵒᵖ) (α : coextSec φ.hom B.val (op V.unop.left)) (W : (Over V.unop)ᵒᵖ)
    (a' : (O'.obj.obj (op W.unop.left.left) : Type u)) :
    ((((coextOverHom φ U B).val.app V).hom α).app W).hom a' =
      (α.app (op (Over.mk W.unop.hom.left))).hom a' :=
  (invSecVal_smul φ.hom B.val (op W.unop.left.left) a'
      (coextRestrFun φ.hom B.val (W.unop.hom.left).op α)).trans
    (coextRestrFun_app_apply φ.hom B.val (W.unop.hom.left).op α
      (𝟙 W.unop.left.left) W.unop.hom.left (Category.id_comp _) a')

/-- On sections over `V ⟶ U`, the comparison `coextOverHom` is `coextOverSection`. -/
theorem coextOverHom_val_app (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O)
    (V : (Over U)ᵒᵖ) (α : coextSec φ.hom B.val (op V.unop.left)) :
    ((coextOverHom φ U B).val.app V).hom α = coextOverSection φ U B V.unop α := by
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun a' => ?_)
  exact (coextOverHom_app_apply φ U B V α W a').trans
    (coextOverSection_app φ U B V.unop α W a').symm

/-- The comparison `coextOverHom` is an isomorphism on sections over each `V ⟶ U`. -/
instance isIso_coextOverHom_val_app (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O)
    (V : (Over U)ᵒᵖ) : IsIso ((coextOverHom φ U B).val.app V) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have he : (fun α => ((coextOverHom φ U B).val.app V).hom α) =
      (coextOverSectionEquiv φ U B V.unop).toFun := by
    rw [coextOverSectionEquiv_toFun]
    funext α
    exact coextOverHom_val_app φ U B V α
  rw [show ⇑((coextOverHom φ U B).val.app V) = (coextOverSectionEquiv φ U B V.unop).toFun from he]
  exact (coextOverSectionEquiv φ U B V.unop).bijective

/-- The underlying morphism of presheaves of modules of `coextOverHom` is an isomorphism. -/
instance isIso_coextOverHom_val (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O) :
    IsIso (coextOverHom φ U B).val :=
  (PresheafOfModules.isoMk (fun V => asIso ((coextOverHom φ U B).val.app V))
    (fun _ _ f => (coextOverHom φ U B).val.naturality f)).isIso_hom

/-- The comparison `coextOverHom` is an isomorphism of sheaves of `O'|_U`-modules. -/
instance isIso_coextOverHom (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O) :
    IsIso (coextOverHom φ U B) := by
  have h : IsIso ((_root_.SheafOfModules.forget (O'.over U)).map (coextOverHom φ U B)) :=
    inferInstanceAs (IsIso (coextOverHom φ U B).val)
  exact isIso_of_reflects_iso (coextOverHom φ U B) (_root_.SheafOfModules.forget (O'.over U))

/-- **Coextension of scalars commutes with restriction to a localized site.** For a morphism
`φ : O ⟶ O'` of sheaves of rings on `(C, J)`, an object `U` of `C` and a sheaf of `O`-modules
`B`, restricting `SheafHom_O(O', B)` to `C/U` gives `SheafHom_{O|_U}(O'|_U, B|_U)`. On sections
the isomorphism is restriction of a local morphism along the iterated-slice functor, by
`coextOverHom_app_apply`. -/
def sheafCoextOverIso (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O) :
    ((coextendScalars φ).obj B).over U ≅
      (coextendScalars (sliceHom φ U)).obj (B.over U) :=
  asIso (coextOverHom φ U B)

/-- The Hom-bijection of the adjunction of Tag 0932 is the explicit one,
`coextendScalarsSheafHomEquiv`. -/
theorem adj_homEquiv_apply (φ : O ⟶ O') (G : _root_.SheafOfModules.{u} O')
    (F : _root_.SheafOfModules.{u} O)
    (g : (_root_.SheafOfModules.restrictScalars φ).obj G ⟶ F) :
    (restrictScalars_coextendScalars_adjunction φ).homEquiv G F g =
      coextendScalarsSheafHomEquiv φ G F g := by
  simp only [restrictScalars_coextendScalars_adjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- Restriction of scalars commutes with restriction to `C/U` on morphisms as well. -/
theorem restrictScalars_overFunctor_map (φ : O ⟶ O') (U : C)
    {G G' : _root_.SheafOfModules.{u} O'} (f : G ⟶ G') :
    (_root_.SheafOfModules.restrictScalars (sliceHom φ U)).map
        ((_root_.SheafOfModules.overFunctor O' U).map f) =
      (_root_.SheafOfModules.overFunctor O U).map
        ((_root_.SheafOfModules.restrictScalars φ).map f) :=
  rfl

/-- The transpose of `coextOverHom` under Tag 0932 on `C/U` is the restriction to `C/U` of the
counit `SheafHom_O(O', B)_O ⟶ B`, which is what `coextOverHom` was built from. -/
theorem homEquiv_symm_coextOverHom (φ : O ⟶ O') (U : C) (B : _root_.SheafOfModules.{u} O) :
    ((restrictScalars_coextendScalars_adjunction (sliceHom φ U)).homEquiv
        (((coextendScalars φ).obj B).over U) (B.over U)).symm (coextOverHom φ U B) =
      (_root_.SheafOfModules.overFunctor O U).map
        ((restrictScalars_coextendScalars_adjunction φ).counit.app B) :=
  (congrArg (((restrictScalars_coextendScalars_adjunction (sliceHom φ U)).homEquiv
      (((coextendScalars φ).obj B).over U) (B.over U)).symm)
    (adj_homEquiv_apply (sliceHom φ U) (((coextendScalars φ).obj B).over U) (B.over U)
      ((_root_.SheafOfModules.overFunctor O U).map
        ((restrictScalars_coextendScalars_adjunction φ).counit.app B))).symm).trans
    (Equiv.symm_apply_apply _ _)

/-- The comparison `coextOverHom` is natural in the sheaf of `O`-modules. Both transposes are
the restriction to `C/U` of the counit of Tag 0932, composed with the morphism; so the square
commutes because the counit is natural. -/
theorem coextOverHom_naturality (φ : O ⟶ O') (U : C) {B B' : _root_.SheafOfModules.{u} O}
    (f : B ⟶ B') :
    (_root_.SheafOfModules.overFunctor O' U).map ((coextendScalars φ).map f) ≫
        coextOverHom φ U B' =
      coextOverHom φ U B ≫ (coextendScalars (sliceHom φ U)).map
        ((_root_.SheafOfModules.overFunctor O U).map f) := by
  refine ((restrictScalars_coextendScalars_adjunction (sliceHom φ U)).homEquiv
    (((coextendScalars φ).obj B).over U) (B'.over U)).symm.injective ?_
  rw [Adjunction.homEquiv_naturality_left_symm
      (restrictScalars_coextendScalars_adjunction (sliceHom φ U))
      ((_root_.SheafOfModules.overFunctor O' U).map ((coextendScalars φ).map f))
      (coextOverHom φ U B'),
    Adjunction.homEquiv_naturality_right_symm
      (restrictScalars_coextendScalars_adjunction (sliceHom φ U))
      (coextOverHom φ U B) ((_root_.SheafOfModules.overFunctor O U).map f),
    homEquiv_symm_coextOverHom, homEquiv_symm_coextOverHom]
  exact ((_root_.SheafOfModules.overFunctor O U).map_comp
      ((_root_.SheafOfModules.restrictScalars φ).map ((coextendScalars φ).map f))
      ((restrictScalars_coextendScalars_adjunction φ).counit.app B')).symm.trans
    ((congrArg (_root_.SheafOfModules.overFunctor O U).map
        ((restrictScalars_coextendScalars_adjunction φ).counit.naturality f)).trans
      ((_root_.SheafOfModules.overFunctor O U).map_comp
        ((restrictScalars_coextendScalars_adjunction φ).counit.app B) f))

/-- **Coextension of scalars commutes with restriction to a localized site, as functors.** -/
def sheafCoextendScalarsOverIso (φ : O ⟶ O') (U : C) :
    coextendScalars.{u} φ ⋙ _root_.SheafOfModules.overFunctor O' U ≅
      _root_.SheafOfModules.overFunctor O U ⋙ coextendScalars.{u} (sliceHom φ U) :=
  NatIso.ofComponents (fun B => sheafCoextOverIso φ U B)
    (fun f => coextOverHom_naturality φ U f)

end Stacks.SheafOfModules.CoextendScalars

end

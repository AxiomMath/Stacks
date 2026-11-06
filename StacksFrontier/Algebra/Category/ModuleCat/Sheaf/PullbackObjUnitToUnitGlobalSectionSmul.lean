module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul

/-!
# Inverse image and multiplication by a global section

Let `φ : S ⟶ F_* R` be the structure map of a morphism of ringed sites, and let `t` be a
compatible family of local sections of `S` whose image under `φ` is a compatible family `s` of
local sections of `R`. The direct image along `φ` intertwines multiplication by `s` with
multiplication by `t`, which is `Stacks.SheafOfModules.map_globalSectionToEnd`. This file
transposes that statement across the adjunction `φ^* ⊣ φ_*`: the canonical comparison
`φ^*(S) ⟶ R` of `SheafOfModules.pullbackObjUnitToUnit` intertwines the inverse image of
multiplication by `t` with multiplication by `s`.

## Main results

* `Stacks.SheafOfModules.pullbackObjUnitToUnit_comp_globalSectionToEnd`: the comparison square
  `φ^*(t · -) ≫ ν = ν ≫ (s · -)` on the structure sheaf.

## Implementation notes

Both sides are morphisms out of `φ^*(S)`, so they are equal as soon as their transposes under
`φ^* ⊣ φ_*` agree. The transpose of the comparison is the map `S ⟶ φ_* R` induced by `φ`
(`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`), the two
transposes are computed by `CategoryTheory.Adjunction.homEquiv_naturality_left` and
`…_right`, and what is left is the naturality of multiplication by `t` — an endomorphism of the
identity functor — at that map, together with
`Stacks.SheafOfModules.map_globalSectionToEnd` on the target.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v₁ u₁ v₂ u₂ w

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  [∀ U, IsMulCommutative (R.obj.obj U)] [∀ U, IsMulCommutative (S.obj.obj U)]

open scoped IsMulCommutative

/-- **Direct image intertwines multiplication by compatible families of local sections.** If
`φ` carries the family `t` of sections of `S` to the family `s` of sections of `R`, then the
direct image along `φ` carries multiplication by `s` to multiplication by `t`. -/
theorem pushforward_map_globalSectionToEnd
    (s : (R.obj ⋙ forget RingCat).sections) (t : (S.obj ⋙ forget RingCat).sections)
    (h : ∀ U : Cᵒᵖ, φ.hom.app U (t.val U) = s.val (op (F.obj U.unop)))
    (M : _root_.SheafOfModules.{w} R) :
    (_root_.SheafOfModules.pushforward.{w} φ).map ((globalSectionToEnd R s).asHom.app M) =
      (globalSectionToEnd S t).asHom.app ((_root_.SheafOfModules.pushforward.{w} φ).obj M) := by
  ext U x
  let y : M.val.obj (op (F.obj (unop U))) := x
  show s.val (op (F.obj (unop U))) • y = _
  rw [← h U]
  rfl

variable [(_root_.SheafOfModules.pushforward.{w} φ).IsRightAdjoint]

/-- **The comparison `φ^*(S) ⟶ R` intertwines the inverse image of multiplication by `t` with
multiplication by `s`.** Here `t` is a compatible family of local sections of `S` and `s` one of
`R`, corresponding under the structure map `φ`.

Transposing both sides under `φ^* ⊣ φ_*` turns the left hand side into
`(t · -) ≫ (S ⟶ φ_* R)` and the right hand side into `(S ⟶ φ_* R) ≫ φ_*(s · -)`; the latter is
`(S ⟶ φ_* R) ≫ (t · -)` by `pushforward_map_globalSectionToEnd_unit`, and the two agree because
multiplication by `t` is an endomorphism of the identity functor and so natural at
`S ⟶ φ_* R`. -/
theorem pullbackObjUnitToUnit_comp_globalSectionToEnd
    (s : (R.obj ⋙ forget RingCat).sections) (t : (S.obj ⋙ forget RingCat).sections)
    (h : ∀ U : Cᵒᵖ, φ.hom.app U (t.val U) = s.val (op (F.obj U.unop))) :
    (_root_.SheafOfModules.pullback.{w} φ).map
          ((globalSectionToEnd S t).asHom.app (_root_.SheafOfModules.unit S)) ≫
        _root_.SheafOfModules.pullbackObjUnitToUnit φ =
      _root_.SheafOfModules.pullbackObjUnitToUnit φ ≫
        (globalSectionToEnd R s).asHom.app (_root_.SheafOfModules.unit R) := by
  set adj := _root_.SheafOfModules.pullbackPushforwardAdjunction.{w} φ with hadj
  set ν := _root_.SheafOfModules.pullbackObjUnitToUnit φ with hν
  set a : _root_.SheafOfModules.unit S ⟶ _root_.SheafOfModules.unit S :=
    (globalSectionToEnd S t).asHom.app (_root_.SheafOfModules.unit S) with ha
  set b : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R :=
    (globalSectionToEnd R s).asHom.app (_root_.SheafOfModules.unit R) with hb
  refine (adj.homEquiv (_root_.SheafOfModules.unit S)
    (_root_.SheafOfModules.unit R)).injective ?_
  have hL : adj.homEquiv (_root_.SheafOfModules.unit S) (_root_.SheafOfModules.unit R)
      ((_root_.SheafOfModules.pullback.{w} φ).map a ≫ ν) =
      a ≫ adj.homEquiv (_root_.SheafOfModules.unit S) (_root_.SheafOfModules.unit R) ν :=
    Adjunction.homEquiv_naturality_left adj a ν
  have hR : adj.homEquiv (_root_.SheafOfModules.unit S) (_root_.SheafOfModules.unit R)
      (ν ≫ b) =
      adj.homEquiv (_root_.SheafOfModules.unit S) (_root_.SheafOfModules.unit R) ν ≫
        (_root_.SheafOfModules.pushforward.{w} φ).map b :=
    Adjunction.homEquiv_naturality_right adj ν b
  have hnat := ((globalSectionToEnd S t).asHom.naturality
    (_root_.SheafOfModules.unitToPushforwardObjUnit φ)).symm
  dsimp only [Functor.id_obj, Functor.id_map] at hnat
  rw [hL, hR, hadj, hν,
    _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit, hb,
    pushforward_map_globalSectionToEnd φ s t h, ha]
  exact hnat

end Stacks.SheafOfModules

end

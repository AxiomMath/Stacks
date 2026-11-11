module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulatedLeft
public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift

/-!
# The derived functor on the localization of a right or left derivable functor

Let `F : 𝒞 ⥤ ℋ` be an exact functor of pre-triangulated categories and let `W` be a saturated
multiplicative system in `𝒞` compatible with the triangulated structure (Situation 05S8). If `F`
is *right derivable* (Tag 05SV, `Functor.IsRightDerivable`), i.e. for every `X` the ind-object
`X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` is essentially constant (Tag 05S9), then one obtains a right
derived functor
$$ RF : W^{-1}𝒞 ⟶ ℋ $$
(equation (05SW), via Proposition 05SE); dually, a left derivable `F` gives
`LF : W⁻¹𝒞 ⟶ ℋ`.

The functor is Mathlib's total derived functor, `Functor.totalRightDerived L W`, resp.
`Functor.totalLeftDerived L W`, along any localization functor `L : 𝒞 ⥤ 𝒟` for `W`. This file
proves that it exists under the source's hypothesis and that it is the source's `RF`:

* it exists: `Functor.hasRightDerivedFunctor_of_isRightDerivable`;
* it extends the pointwise `RF`: its value at `L(X)` is a value of `RF` at `X` in the sense of
  Tag 05S9, with coprojections `F(X') ⟶ RF(L(X')) ≅ RF(L(X))`, and its action on `L(f)` is the
  morphism of Tag 05SA, the unique morphism compatible with the coprojections;
* it is exact (Tag 05SE);
* conversely, any functor on the localization whose values extend the pointwise `RF` in this
  way is a right derived functor in Mathlib's sense, hence isomorphic to the total one.

## Main results

* `CategoryTheory.Functor.hasRightDerivedFunctor_of_isRightDerivable`,
  `CategoryTheory.Functor.hasLeftDerivedFunctor_of_isLeftDerivable`: a right (resp. left)
  derivable functor has a total right (resp. left) derived functor.
* `CategoryTheory.Functor.totalRightDerived_isTriangulated_and_isRightDerivedValueAt`,
  `CategoryTheory.Functor.totalLeftDerived_isTriangulated_and_isLeftDerivedValueAt`: Tag 05SW.
* `CategoryTheory.Functor.totalRightDerivedObjIso`, `CategoryTheory.Functor.totalLeftDerivedObjIso`:
  any value of `RF` (resp. `LF`) at `X` is canonically isomorphic to the total derived functor at
  `L(X)`, compatibly with the coprojections (resp. projections).
* `CategoryTheory.Functor.isRightDerivedFunctor_of_forall_isRightDerivedValueAt`,
  `CategoryTheory.Functor.isLeftDerivedFunctor_of_forall_isLeftDerivedValueAt`: the converse
  bridge.

## Implementation notes

The localization `W⁻¹𝒞` is represented by an arbitrary localization functor `L : 𝒞 ⥤ 𝒟` with an
arbitrary pre-triangulated structure on `𝒟` for which `L` is exact; the structure of Tag 05R6,
`Triangulated.Localization.pretriangulated`, is one of these. The left derived functor commutes
with the shift through `StacksDraft.PseudoCoherence.leftDerivedCommShift`, Mathlib providing the
shift only on the right derived functor.

## References

* [Stacks, Tag 05SW](https://stacks.math.columbia.edu/tag/05SW); derivability is Tag 05SV, being
  defined at an object Tag 05S9, the morphisms Tag 05SA, and exactness Tag 05SE.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

section General

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]
  (F : C ⥤ H) (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]

/-- **Stacks 05SW**, existence of `RF`: a functor that is right derivable (Tag 05SV) relative to a
class of morphisms with a left calculus of fractions has a total right derived functor
`RF : W⁻¹𝒞 ⥤ ℋ`. -/
@[stacks 05SW "existence of `RF : S⁻¹𝒟 ⥤ 𝒟'` for a right derivable `F`"]
theorem hasRightDerivedFunctor_of_isRightDerivable [W.HasLeftCalculusOfFractions]
    (h : F.IsRightDerivable W) : F.HasRightDerivedFunctor W :=
  have := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable W h
  inferInstance

/-- **Stacks 05SW**, existence of `LF`: a functor that is left derivable (Tag 05SV) relative to a
class of morphisms with a right calculus of fractions has a total left derived functor
`LF : W⁻¹𝒞 ⥤ ℋ`. -/
@[stacks 05SW "existence of `LF : S⁻¹𝒟 ⥤ 𝒟'` for a left derivable `F`"]
theorem hasLeftDerivedFunctor_of_isLeftDerivable [W.HasRightCalculusOfFractions]
    (h : F.IsLeftDerivable W) : F.HasLeftDerivedFunctor W :=
  have := F.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable W h
  inferInstance

/-- The value of `RF` at `X` (Tag 05S9), for any value cocone `c`, is the total right derived
functor at `L(X)`: the canonical isomorphism of the two colimit cocones. -/
noncomputable def totalRightDerivedObjIso [W.HasLeftCalculusOfFractions]
    (h : F.IsRightDerivable W) {X : C}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) :
    haveI := F.hasRightDerivedFunctor_of_isRightDerivable W h
    c.pt ≅ (F.totalRightDerived L W).obj (L.obj X) :=
  haveI := F.hasRightDerivedFunctor_of_isRightDerivable W h
  haveI := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable W h
  hc.isColimit.coconePointUniqueUpToIso
    (isColimitDerivedUnitCocone F W L (F.totalRightDerived L W) (F.totalRightDerivedUnit L W) X)

/-- The isomorphism `CategoryTheory.Functor.totalRightDerivedObjIso` is compatible with the
coprojections: it carries the coprojection of `c` at `(s : X ⟶ X')` to
`F(X') ⟶ RF(L(X')) ≅ RF(L(X))`. -/
@[reassoc]
lemma ι_app_totalRightDerivedObjIso_hom [W.HasLeftCalculusOfFractions]
    (h : F.IsRightDerivable W) {X : C}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) (s : W.Under ⊤ X) :
    haveI := F.hasRightDerivedFunctor_of_isRightDerivable W h
    c.ι.app s ≫ (F.totalRightDerivedObjIso W L h hc).hom =
      (F.totalRightDerivedUnit L W).app s.right ≫
        (F.totalRightDerived L W).map (W.underIso L X s).inv :=
  haveI := F.hasRightDerivedFunctor_of_isRightDerivable W h
  haveI := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable W h
  hc.isColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitDerivedUnitCocone F W L (F.totalRightDerived L W) (F.totalRightDerivedUnit L W) X) s

/-- The value of `LF` at `X` (Tag 05S9), for any value cone `c`, is the total left derived
functor at `L(X)`: the canonical isomorphism of the two limit cones. -/
noncomputable def totalLeftDerivedObjIso [W.HasRightCalculusOfFractions]
    (h : F.IsLeftDerivable W) {X : C}
    {c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)}
    (hc : F.IsLeftDerivedValueAt W X c) :
    haveI := F.hasLeftDerivedFunctor_of_isLeftDerivable W h
    c.pt ≅ (F.totalLeftDerived L W).obj (L.obj X) :=
  haveI := F.hasLeftDerivedFunctor_of_isLeftDerivable W h
  haveI := F.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable W h
  hc.isLimit.conePointUniqueUpToIso
    (isLimitDerivedCounitCone F W L (F.totalLeftDerived L W) (F.totalLeftDerivedCounit L W) X)

/-- The isomorphism `CategoryTheory.Functor.totalLeftDerivedObjIso` is compatible with the
projections: it carries the projection of `c` at `(s : X' ⟶ X)` to
`LF(L(X)) ≅ LF(L(X')) ⟶ F(X')`. -/
@[reassoc]
lemma totalLeftDerivedObjIso_inv_π_app [W.HasRightCalculusOfFractions]
    (h : F.IsLeftDerivable W) {X : C}
    {c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)}
    (hc : F.IsLeftDerivedValueAt W X c) (s : W.Over ⊤ X) :
    haveI := F.hasLeftDerivedFunctor_of_isLeftDerivable W h
    (F.totalLeftDerivedObjIso W L h hc).inv ≫ c.π.app s =
      (F.totalLeftDerived L W).map (W.overIso L X s).inv ≫
        (F.totalLeftDerivedCounit L W).app s.left :=
  haveI := F.hasLeftDerivedFunctor_of_isLeftDerivable W h
  haveI := F.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable W h
  hc.isLimit.conePointUniqueUpToIso_inv_comp
    (isLimitDerivedCounitCone F W L (F.totalLeftDerived L W) (F.totalLeftDerivedCounit L W) X) s

/-- **A functor on the localization extending the pointwise `RF` is a right derived functor.**
If `RF : W⁻¹𝒞 ⥤ ℋ` and `α : F ⟶ L ⋙ RF` are such that, for every `X`, `RF(L(X))` with the
coprojections `F(X') ⟶ RF(L(X')) ≅ RF(L(X))` is a value of `RF` at `X` (Tag 05S9), then `RF` is a
right derived functor of `F` in Mathlib's sense (a left Kan extension of `F` along `L`), hence
isomorphic to `F.totalRightDerived L W`. -/
theorem isRightDerivedFunctor_of_forall_isRightDerivedValueAt [W.HasLeftCalculusOfFractions]
    (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hv : ∀ X, F.IsRightDerivedValueAt W X (derivedUnitCocone F W L RF α X)) :
    RF.IsRightDerivedFunctor α W := by
  have := Localization.essSurj L W
  have hpt : (LeftExtension.mk RF α).IsPointwiseLeftKanExtension := fun Y =>
    letI := W.final_underToCostructuredArrow L (L.objPreimage Y)
    (LeftExtension.mk RF α).isPointwiseLeftKanExtensionAtEquivOfIso' (L.objObjPreimageIso Y)
      ((Functor.Final.isColimitWhiskerEquiv (W.underToCostructuredArrow L (L.objPreimage Y))
        _) (hv (L.objPreimage Y)).isColimit)
  exact ⟨hpt.isLeftKanExtension⟩

/-- **A functor on the localization extending the pointwise `LF` is a left derived functor.**
If `LF : W⁻¹𝒞 ⥤ ℋ` and `α : L ⋙ LF ⟶ F` are such that, for every `X`, `LF(L(X))` with the
projections `LF(L(X)) ≅ LF(L(X')) ⟶ F(X')` is a value of `LF` at `X` (Tag 05S9), then `LF` is a
left derived functor of `F` in Mathlib's sense, hence isomorphic to `F.totalLeftDerived L W`. -/
theorem isLeftDerivedFunctor_of_forall_isLeftDerivedValueAt [W.HasRightCalculusOfFractions]
    (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hv : ∀ X, F.IsLeftDerivedValueAt W X (derivedCounitCone F W L LF α X)) :
    LF.IsLeftDerivedFunctor α W := by
  have := Localization.essSurj L W
  have hpt : (RightExtension.mk LF α).IsPointwiseRightKanExtension := fun Y =>
    letI := W.initial_overToStructuredArrow L (L.objPreimage Y)
    (RightExtension.mk LF α).isPointwiseRightKanExtensionAtEquivOfIso' (L.objObjPreimageIso Y)
      ((Functor.Initial.isLimitWhiskerEquiv (W.overToStructuredArrow L (L.objPreimage Y))
        _) (hv (L.objPreimage Y)).isLimit)
  exact ⟨hpt.isRightKanExtension⟩

end General

section Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {H : Type u₃} [Category.{v₃} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- **Stacks 05SW**, right derived functor. In Situation 05S8 — `F : 𝒞 ⥤ ℋ` an exact functor of
pre-triangulated categories, `W` a saturated multiplicative system compatible with the
triangulated structure — let `L : 𝒞 ⥤ 𝒟` be a localization functor for `W`, exact for a
pre-triangulated structure on `𝒟` (e.g. that of Tag 05R6). If `F` is right derivable
(Tag 05SV), the total right derived functor `RF = F.totalRightDerived L W : W⁻¹𝒞 ⥤ ℋ`, with
comparison `α = F.totalRightDerivedUnit L W : F ⟶ L ⋙ RF`, exists
(`Functor.hasRightDerivedFunctor_of_isRightDerivable`) and

1. `RF` is exact (Tag 05SE);
2. `RF` extends the pointwise `RF` of Tag 05S9 on objects: for every `X`, `RF(L(X))`, with the
   coprojections `F(X') ⟶ RF(L(X')) ≅ RF(L(X))` at `(s : X ⟶ X')`, is a value of `RF` at `X`;
3. `RF` extends it on morphisms: `RF(L(f))` is the morphism of Tag 05SA, i.e. a morphism
   `RF(L(X)) ⟶ RF(L(Y))` is compatible with the coprojections along every square
   `f ≫ t = s ≫ g` with `s`, `t` in `W` if and only if it is `RF(L(f))`. -/
@[stacks 05SW "right derived functor `RF : S⁻¹𝒟 ⥤ 𝒟'`: exact, value at `X` the essentially
constant ind-object, `RF(f)` the map of 05SA"]
theorem totalRightDerived_isTriangulated_and_isRightDerivedValueAt
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (h : F.IsRightDerivable W) :
    haveI := hW.hasLeftCalculusOfFractions
    haveI := F.hasRightDerivedFunctor_of_isRightDerivable W h
    (F.totalRightDerived L W).IsTriangulated ∧
      (∀ X : C, F.IsRightDerivedValueAt W X
        (derivedUnitCocone F W L (F.totalRightDerived L W) (F.totalRightDerivedUnit L W) X)) ∧
      ∀ {X Y : C} (f : X ⟶ Y)
        (u : (F.totalRightDerived L W).obj (L.obj X) ⟶ (F.totalRightDerived L W).obj (L.obj Y)),
        (∀ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (g : s.right ⟶ t.right),
          f ≫ t.hom = s.hom ≫ g →
            (derivedUnitCocone F W L (F.totalRightDerived L W)
                (F.totalRightDerivedUnit L W) X).ι.app s ≫ u =
              F.map g ≫ (derivedUnitCocone F W L (F.totalRightDerived L W)
                (F.totalRightDerivedUnit L W) Y).ι.app t) ↔
          u = (L ⋙ F.totalRightDerived L W).map f := by
  have := hW.hasLeftCalculusOfFractions
  have := F.hasRightDerivedFunctor_of_isRightDerivable W h
  have := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable W h
  refine ⟨isTriangulated_of_isRightDerivable F W L (F.totalRightDerived L W)
      (F.totalRightDerivedUnit L W) hW h,
    isRightDerivedValueAt_derivedUnitCocone F W L (F.totalRightDerived L W)
      (F.totalRightDerivedUnit L W) h, fun {X Y} f u => ⟨fun hu => ?_, ?_⟩⟩
  · refine (isColimitDerivedUnitCocone F W L (F.totalRightDerived L W)
      (F.totalRightDerivedUnit L W) X).hom_ext fun c => ?_
    obtain ⟨ψ, hψ⟩ := MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction
      (MorphismProperty.RightFraction.mk (W := W) (X := c.right) (Y := Y)
        (show X ⟶ c.right from c.hom) c.prop f)
    exact (hu c (MorphismProperty.Under.mk ⊤ ψ.s ψ.hs) ψ.f hψ).trans
      (unit_comp_map_eq F W L _ _ f _ c.prop _ ψ.hs ψ.f hψ).symm
  · rintro rfl s t g hsq
    exact unit_comp_map_eq F W L _ _ f _ s.prop _ t.prop g hsq

/-- **Stacks 05SW**, left derived functor. In Situation 05S8, with `L : 𝒞 ⥤ 𝒟` an exact
localization functor for `W`, if `F` is left derivable (Tag 05SV), the total left derived functor
`LF = F.totalLeftDerived L W : W⁻¹𝒞 ⥤ ℋ`, with comparison
`α = F.totalLeftDerivedCounit L W : L ⋙ LF ⟶ F`, exists
(`Functor.hasLeftDerivedFunctor_of_isLeftDerivable`) and, for the commutation with the shift of
`StacksDraft.PseudoCoherence.leftDerivedCommShift`,

1. `LF` is exact (Tag 05SE);
2. `LF` extends the pointwise `LF` of Tag 05S9 on objects: for every `X`, `LF(L(X))`, with the
   projections `LF(L(X)) ≅ LF(L(X')) ⟶ F(X')` at `(s : X' ⟶ X)`, is a value of `LF` at `X`;
3. `LF` extends it on morphisms: a morphism `LF(L(X)) ⟶ LF(L(Y))` is compatible with the
   projections along every square `s ≫ f = g ≫ t` with `s`, `t` in `W` if and only if it is
   `LF(L(f))` (Tag 05SA). -/
@[stacks 05SW "left derived functor `LF : S⁻¹𝒟 ⥤ 𝒟'`: exact, value at `X` the essentially
constant pro-object, `LF(f)` the map of 05SA"]
theorem totalLeftDerived_isTriangulated_and_isLeftDerivedValueAt
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (h : F.IsLeftDerivable W) :
    haveI := hW.hasRightCalculusOfFractions
    haveI := F.hasLeftDerivedFunctor_of_isLeftDerivable W h
    letI := StacksDraft.PseudoCoherence.leftDerivedCommShift (F.totalLeftDerived L W)
      (F.totalLeftDerivedCounit L W) W ℤ
    (F.totalLeftDerived L W).IsTriangulated ∧
      (∀ X : C, F.IsLeftDerivedValueAt W X
        (derivedCounitCone F W L (F.totalLeftDerived L W) (F.totalLeftDerivedCounit L W) X)) ∧
      ∀ {X Y : C} (f : X ⟶ Y)
        (u : (F.totalLeftDerived L W).obj (L.obj X) ⟶ (F.totalLeftDerived L W).obj (L.obj Y)),
        (∀ (s : W.Over ⊤ X) (t : W.Over ⊤ Y) (g : s.left ⟶ t.left),
          s.hom ≫ f = g ≫ t.hom →
            u ≫ (derivedCounitCone F W L (F.totalLeftDerived L W)
                (F.totalLeftDerivedCounit L W) Y).π.app t =
              (derivedCounitCone F W L (F.totalLeftDerived L W)
                (F.totalLeftDerivedCounit L W) X).π.app s ≫ F.map g) ↔
          u = (L ⋙ F.totalLeftDerived L W).map f := by
  have := hW.hasRightCalculusOfFractions
  have := F.hasLeftDerivedFunctor_of_isLeftDerivable W h
  have := F.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable W h
  let := StacksDraft.PseudoCoherence.leftDerivedCommShift (F.totalLeftDerived L W)
    (F.totalLeftDerivedCounit L W) W ℤ
  have := IsLeftDerivedFunctor.natTrans_commShift (F.totalLeftDerived L W)
    (F.totalLeftDerivedCounit L W) W ℤ
  refine ⟨isTriangulated_of_isLeftDerivable F W L (F.totalLeftDerived L W)
      (F.totalLeftDerivedCounit L W) hW h,
    isLeftDerivedValueAt_derivedCounitCone F W L (F.totalLeftDerived L W)
      (F.totalLeftDerivedCounit L W) h, fun {X Y} f u => ⟨fun hu => ?_, ?_⟩⟩
  · refine (isLimitDerivedCounitCone F W L (F.totalLeftDerived L W)
      (F.totalLeftDerivedCounit L W) Y).hom_ext fun c => ?_
    obtain ⟨ψ, hψ⟩ := MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
      (MorphismProperty.LeftFraction.mk (W := W) (X := X) (Y := c.left) f
        (show c.left ⟶ Y from c.hom) c.prop)
    exact (hu (MorphismProperty.Over.mk ⊤ ψ.s ψ.hs) c ψ.f hψ).trans
      (map_comp_counit_eq F W L _ _ f _ ψ.hs _ c.prop ψ.f hψ).symm
  · rintro rfl s t g hsq
    exact map_comp_counit_eq F W L _ _ f _ s.prop _ t.prop g hsq

end Triangulated

end CategoryTheory.Functor

end

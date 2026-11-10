module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.StalkSequence

/-!
# The fibre-regular family of an open subscheme

Let `i : Y ⟶ X` be an open immersion and `f : X ⟶ S` a morphism.  For `y : Y` the local rings of
`X` at `i y` and of `Y` at `y` agree, and so do the local rings of the fibres of `f` and of
`i ≫ f`.  Consequently a family of elements of `𝒪_{X, i y}` which is a regular sequence in the
local ring of the fibre of `f` transports to a family of elements of `𝒪_{Y, y}` which is a
regular sequence in the local ring of the fibre of `i ≫ f`.

We also show that the germ on the fibre of the restriction of a global section is the image of
its germ on the total space, and that a fibre of a morphism locally of finite type is locally
Noetherian.

## Main results

* `Stacks.AlgebraicGeometry.isRegular_fiber_comp_of_isOpenImmersion`: transport of the fibre
  regularity along an open immersion.
* `Stacks.AlgebraicGeometry.germ_fiberι_appTop_apply`: the germ on the fibre of the restriction
  of a global section is the image of its germ.
* `Stacks.AlgebraicGeometry.isLocallyNoetherian_fiber`: a fibre of a morphism locally of finite
  type is locally Noetherian.

## References

* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry RingTheory.Sequence

namespace Stacks.AlgebraicGeometry

universe u

/-- Regularity of a sequence transports along a ring isomorphism. -/
theorem RingEquiv.isRegular_map {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (l : List A) (hl : IsRegular A l) : IsRegular B (l.map e) :=
  (e.toAddEquiv.isRegular_congr (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun a _ b => e.map_mul a b))).mp hl

variable {X S : Scheme.{u}}

/-- Composing the map on global sections with the germ at `x` is the germ at the image of `x`
followed by the stalk map. -/
theorem appTop_comp_germ_top {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    g.appTop ≫ X.presheaf.germ ⊤ x trivial =
      Y.presheaf.germ ⊤ (g x) trivial ≫ g.stalkMap x :=
  (Scheme.Hom.germ_stalkMap g ⊤ x trivial).symm

/-- Transport of a germ of a global section along an equality of points. -/
theorem cast_germ_top {x y : X} (hxy : x = y) (a : Γ(X, ⊤)) :
    hxy ▸ X.presheaf.germ ⊤ x trivial a = X.presheaf.germ ⊤ y trivial a := by
  subst hxy; rfl

/-- For `a : Γ(X, ⊤)` the germ at the point of the fibre through `x` of the restriction of `a` is
the image of the germ of `a` at `x`. -/
theorem germ_fiberι_appTop_apply (f : X ⟶ S) (x : X) (a : Γ(X, ⊤)) :
    ((f.fiberι (f x)).appTop ≫
        (f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) trivial).hom a =
      ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((f.fiberι_asFiber x).symm ▸ X.presheaf.germ ⊤ x trivial a) := by
  rw [appTop_comp_germ_top, cast_germ_top]
  rfl

/-- Let `i : Y ⟶ X` be an open immersion, `f : X ⟶ S` a morphism and `y : Y`. A family of
elements of `𝒪_{X, i y}` whose image in the local ring of the fibre of `f` through `i y` is a
regular sequence has an image in `𝒪_{Y, y}` whose image in the local ring of the fibre of `i ≫ f`
through `y` is again a regular sequence. -/
theorem isRegular_fiber_comp_of_isOpenImmersion {Y : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] (f : X ⟶ S) (y : Y) {r : ℕ} (h : Fin r → X.presheaf.stalk (i y))
    (hr : IsRegular ((f.fiber (f (i y))).presheaf.stalk (f.asFiber (i y)))
      (List.ofFn fun j => ((f.fiberι (f (i y))).stalkMap (f.asFiber (i y))).hom
        ((f.fiberι_asFiber (i y)).symm ▸ h j))) :
    IsRegular (((i ≫ f).fiber ((i ≫ f) y)).presheaf.stalk ((i ≫ f).asFiber y))
      (List.ofFn fun j => (((i ≫ f).fiberι ((i ≫ f) y)).stalkMap ((i ≫ f).asFiber y)).hom
        (((i ≫ f).fiberι_asFiber y).symm ▸ (i.stalkMap y).hom (h j))) := by
  set I : Ideal (X.presheaf.stalk (i y)) := Ideal.map (f.stalkMap (i y)).hom
    (IsLocalRing.maximalIdeal (S.presheaf.stalk (f (i y)))) with hI
  set J : Ideal (Y.presheaf.stalk y) := Ideal.map ((i ≫ f).stalkMap y).hom
    (IsLocalRing.maximalIdeal (S.presheaf.stalk ((i ≫ f) y))) with hJ
  set e : X.presheaf.stalk (i y) ≃+* Y.presheaf.stalk y :=
    (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv with he
  have hJI : J = Ideal.map e.toRingHom I := by
    rw [hJ, hI, Ideal.map_map, Scheme.Hom.stalkMap_comp]
    rfl
  set q := I.quotientEquiv J e hJI with hq
  have hrq := isRegular_quotient_stalk_of_isRegular_fiber f (i y) h hr
  have hrF := RingEquiv.isRegular_map (quotientStalkEquivFiberStalk (i ≫ f) y) _
    (RingEquiv.isRegular_map q _ hrq)
  convert hrF using 1
  rw [List.map_map, List.map_ofFn]
  refine congrArg List.ofFn (funext fun j => ?_)
  change _ = (quotientStalkEquivFiberStalk (i ≫ f) y)
    (Ideal.Quotient.mk J ((i.stalkMap y).hom (h j)))
  rw [quotientStalkEquivFiberStalk_mk, stalkCongr_hom_apply_eq_cast]

/-- A fibre of a morphism locally of finite type is locally Noetherian. -/
theorem isLocallyNoetherian_fiber (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    IsLocallyNoetherian (f.fiber s) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    have : MorphismProperty.IsStableUnderBaseChangeAlong
        (P := @LocallyOfFiniteType) (S.fromSpecResidueField s) :=
      ⟨fun pb h => locallyOfFiniteType_isStableUnderBaseChange.of_isPullback pb h⟩
    exact MorphismProperty.pullback_snd f (S.fromSpecResidueField s) inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)

end Stacks.AlgebraicGeometry

end

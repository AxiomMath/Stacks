module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# A scheme flat over a thickening-and-affine pushout is the scheme pushout of its base changes

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism
and `E = Y ⨿_X X'` a pushout of algebraic spaces.  Let `W` be a scheme with a flat morphism
`W ⟶ E` (for instance an étale chart of `E`), and let `W_{X'} = W ×_E X'`, `W_Y = W ×_E Y` and
`W_X = W_Y ×_Y X = W_{X'} ×_{X'} X` be schemes carrying its base changes.  Then the square of
schemes
```
W_X  ⟶ W_{X'}
 ↓        ↓
W_Y  ⟶  W
```
is a pushout in the category of schemes.

## Main results

* `AlgebraicGeometry.Space.isPushout_toScheme_of_isFlat`: the square of schemes above is a
  pushout.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A scheme flat over a thickening-and-affine pushout is the scheme pushout of its base
changes**: for a pushout `E = Y ⨿_X X'` of a thickening `i` and an affine morphism `f`, a flat
morphism `w : W ⟶ E` from a scheme and schemes `W_{X'}`, `W_Y`, `W_X` carrying its base changes,
the square of schemes `W_X ⟶ W_{X'}`, `W_Y ⟶ W` is a pushout. -/
theorem isPushout_toScheme_of_isFlat (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y E : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {a : X' ⟶ E} {b : Y ⟶ E} (hE : IsPushout i f a b)
    {W WX' WY WX : BigFppfOver B S hS} {cX' : WX' ⟶ W} {cY : WY ⟶ W} {jX' : WX ⟶ WX'}
    {jY : WX ⟶ WY} {w : schemeSpace W ⟶ E} {pX' : schemeSpace WX' ⟶ X'}
    {pY : schemeSpace WY ⟶ Y} {pX : schemeSpace WX ⟶ X} (hw : IsFlat B S hS w.hom)
    (hX'sq : IsPullback (schemeSpaceMap cX') pX' w a)
    (hYsq : IsPullback (schemeSpaceMap cY) pY w b)
    (hjYsq : IsPullback (schemeSpaceMap jY) pX pY f)
    (hjX'sq : IsPullback (schemeSpaceMap jX') pX pX' i)
    (hsides : jY ≫ cY = jX' ≫ cX') :
    IsPushout ((BigFppfOver.toScheme B S hS).map jX') ((BigFppfOver.toScheme B S hS).map jY)
      ((BigFppfOver.toScheme B S hS).map cX') ((BigFppfOver.toScheme B S hS).map cY) := by
  obtain ⟨A⟩ := hatlas i f hi hf
  obtain ⟨Epo, aY, bY, qm, hpush, hqm, hqmS, hqmE, haX', hbYc⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  let eE := hpush.isoIsPushout _ _ hE
  let eP : Epo.1 ≅ E.1 :=
    { hom := eE.hom.hom
      inv := eE.inv.hom
      hom_inv_id := congrArg (fun φ => φ.hom) eE.hom_inv_id
      inv_hom_id := congrArg (fun φ => φ.hom) eE.inv_hom_id }
  have hinl : aY.hom ≫ eP.hom = a.hom :=
    congrArg (fun φ => φ.hom) (hpush.inl_isoIsPushout_hom _ _ hE)
  have hinr : bY.hom ≫ eP.hom = b.hom :=
    congrArg (fun φ => φ.hom) (hpush.inr_isoIsPushout_hom _ _ hE)
  have hqm' : IsPullback (yoneda.map A.s) (yoneda.map A.t) (qm ≫ eP.hom) (qm ≫ eP.hom) :=
    hqm.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simp)
  have haX'' : IsPullback (yoneda.map A.a) A.p' (qm ≫ eP.hom) a.hom :=
    haX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (hinl.trans (Category.id_comp _).symm)
  have hbY'' : IsPullback (yoneda.map A.b) A.q (qm ≫ eP.hom) b.hom :=
    hbYc.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (hinr.trans (Category.id_comp _).symm)
  have hback : i.hom ≫ a.hom = f.hom ≫ b.hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using congrArg (fun φ => φ.hom) hE.w
  have hsides' : (schemeSpaceMap jY).hom ≫ (schemeSpaceMap cY).hom =
      (schemeSpaceMap jX').hom ≫ (schemeSpaceMap cX').hom := by
    show yoneda.map jY ≫ yoneda.map cY = yoneda.map jX' ≫ yoneda.map cX'
    rw [← Functor.map_comp, ← Functor.map_comp, hsides]
  have hWpush : IsPushout (schemeSpaceMap jX') (schemeSpaceMap jY) (schemeSpaceMap cX')
      (schemeSpaceMap cY) :=
    isPushout_of_isFlat_of_thickeningAffineAtlas B S hS A hqm'
      (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS)
      (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE) haX'' hbY'' hback hw
      (AlgebraicSpaces.isPullback_hom B S hS hX'sq) (AlgebraicSpaces.isPullback_hom B S hS hYsq)
      (AlgebraicSpaces.isPullback_hom B S hS hjYsq)
      (by simpa only [ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun φ => φ.hom) hjX'sq.w) hsides'
  have hjT : IsThickeningHom B S hS (schemeSpaceMap jX') :=
    isThickeningHom_of_isPullback B S hS hjX'sq.flip hi
  have hjs : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map jX') :=
    ⟨(presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u})
        inferInstance jX').mp hjT.isClosedImmersion,
      surjective_of_isSurjective_yonedaMap B S hS jX' hjT.surjective_pointsMap⟩
  have hjYA : IsAffineHom B S hS (yoneda.map jY) :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS hjYsq).flip hf
  have key := (isAffineHom_tfae_of_isAlgebraicSpace B S hS (yoneda.map jY)
    (schemeSpace WX).property (schemeSpace WY).property).out 2 1
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map jY) :=
    (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsAffineHom.{u})
      inferInstance jY).mp (key.mp hjYA).2
  obtain ⟨P, a₀, b₀, hP⟩ := exists_isPushout_site B S hS jX' jY hjs
  have hPsp : IsPushout (schemeSpaceMap jX') (schemeSpaceMap jY) (schemeSpaceMap a₀)
      (schemeSpaceMap b₀) :=
    isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS jX' jY a₀ b₀ hjs hP
  let e := hPsp.isoIsPushout _ _ hWpush
  let φ : yoneda.obj P ⟶ yoneda.obj W := e.hom.hom
  let ψ : yoneda.obj W ⟶ yoneda.obj P := e.inv.hom
  let e₀ : P ≅ W :=
    { hom := yoneda.preimage φ
      inv := yoneda.preimage ψ
      hom_inv_id := yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage,
          CategoryTheory.Functor.map_id]
        exact congrArg (fun φ => φ.hom) e.hom_inv_id)
      inv_hom_id := yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage,
          CategoryTheory.Functor.map_id]
        exact congrArg (fun φ => φ.hom) e.inv_hom_id) }
  have ha₀ : a₀ ≫ e₀.hom = cX' := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage]
    exact congrArg (fun φ => φ.hom) (hPsp.inl_isoIsPushout_hom _ _ hWpush))
  have hb₀ : b₀ ≫ e₀.hom = cY := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage]
    exact congrArg (fun φ => φ.hom) (hPsp.inr_isoIsPushout_hom _ _ hWpush))
  refine hP.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((BigFppfOver.toScheme B S hS).mapIso e₀) (by simp) (by simp) ?_ ?_
  · rw [Functor.mapIso_hom, ← Functor.map_comp, ha₀, Iso.refl_hom, Category.id_comp]
  · rw [Functor.mapIso_hom, ← Functor.map_comp, hb₀, Iso.refl_hom, Category.id_comp]

/-- **The structure sheaf of a thickening-and-affine pushout on a flat scheme over it.**  In the
situation of `AlgebraicGeometry.Space.isPushout_toScheme_of_isFlat`, the ring of functions on
`W` is the fibre product of the rings of functions on `W_Y` and on `W_{X'}` over the ring of
functions on `W_X`.  Of the square `W_X ⟶ W_{X'} ⟶ X'` only commutativity is assumed. -/
theorem isPullback_globalSections_of_isFlat (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y E : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {a : X' ⟶ E} {b : Y ⟶ E} (hE : IsPushout i f a b)
    {W WX' WY WX : BigFppfOver B S hS} {cX' : WX' ⟶ W} {cY : WY ⟶ W} {jX' : WX ⟶ WX'}
    {jY : WX ⟶ WY} {w : schemeSpace W ⟶ E} {pX' : schemeSpace WX' ⟶ X'}
    {pY : schemeSpace WY ⟶ Y} {pX : schemeSpace WX ⟶ X} (hw : IsFlat B S hS w.hom)
    (hX'sq : IsPullback (schemeSpaceMap cX') pX' w a)
    (hYsq : IsPullback (schemeSpaceMap cY) pY w b)
    (hjYsq : IsPullback (schemeSpaceMap jY) pX pY f)
    (hjX'w : schemeSpaceMap jX' ≫ pX' = pX ≫ i)
    (hsides : jY ≫ cY = jX' ≫ cX') :
    IsPullback (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map cY).op)
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map cX').op)
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map jY).op)
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map jX').op) := by
  have hcomp : ∀ {U V Z : BigFppfOver B S hS} (k : U ⟶ V) (l : V ⟶ Z),
      schemeSpaceMap (k ≫ l) = schemeSpaceMap k ≫ schemeSpaceMap l := fun k l =>
    ObjectProperty.hom_ext _ (yoneda.map_comp k l)
  have hbig : IsPullback (schemeSpaceMap jX' ≫ schemeSpaceMap cX') pX w (i ≫ a) := by
    have h := hjYsq.paste_horiz hYsq
    rwa [← hcomp, hsides, hcomp, ← hE.w] at h
  have hjX'sq : IsPullback (schemeSpaceMap jX') pX pX' i := IsPullback.of_right hbig hjX'w hX'sq
  exact (isPushout_toScheme_of_isFlat hatlas hi hf hE hw hX'sq hYsq hjYsq hjX'sq
    hsides).op.map Scheme.Γ

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.AffineChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Regular functions on an affine closed subspace lift to the chart of a nilpotent thickening

Let `i : G ⟶ X` be a thickening of algebraic spaces over `S` whose source is isomorphic to the
presheaf represented by an affine object `T` of the site, let `w' : U' ⟶ X` be an affine
surjective étale chart with affine kernel pair `R' ⇉ U'`, and let `U ⟶ U'` be the base change of
`i` along `w'`, assumed to have nilpotent ideal. This file proves that every regular function on
`T`, pulled back to `U`, is the restriction of a regular function on `U'` whose two pullbacks to
`R'` agree.

It is the translation of `AlgebraicGeometry.C1573.exists_appTop_eq_of_isNilpotent_ker` from
cartesian squares of affine schemes to the geometry of algebraic spaces: the double and triple
overlaps of the chart and their base changes along `i` are formed, and the cartesian squares the
scheme-level statement asks for are obtained by pasting.

## Main results

* `AlgebraicGeometry.Space.C1573.exists_isPullback_baseChange`: base change along a fixed morphism
  of presheaves is functorial on representable charts, with cartesian comparison squares.
* `AlgebraicGeometry.Space.C1573.exists_appTop_eq_of_isThickeningHom_chart`: the lifting statement.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Base change of representable charts is functorial.** Let `i : G ⟶ X` be a morphism of
presheaves, and let `V₀ ⟶ V` and `V'₀ ⟶ V'` be base changes of `i` along charts `v` and `v'`
with `v = q ≫ v'`. Then the comparison `V₀ ⟶ V'₀` over `q` exists and the comparison square is
cartesian. -/
theorem C1573.exists_isPullback_baseChange {X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : G ⟶ X)
    {V₀ V V'₀ V' : BigFppfOver B S hS} {jV : V₀ ⟶ V} {ηV : yoneda.obj V₀ ⟶ G}
    {v : yoneda.obj V ⟶ X} {jV' : V'₀ ⟶ V'} {ηV' : yoneda.obj V'₀ ⟶ G}
    {v' : yoneda.obj V' ⟶ X}
    (h : IsPullback ηV (yoneda.map jV) i v) (h' : IsPullback ηV' (yoneda.map jV') i v')
    (q : V ⟶ V') (hv : v = yoneda.map q ≫ v') :
    ∃ q₀ : V₀ ⟶ V'₀, yoneda.map q₀ ≫ ηV' = ηV ∧
      IsPullback (yoneda.map q₀) (yoneda.map jV) (yoneda.map jV') (yoneda.map q) := by
  have hw : ηV ≫ i = (yoneda.map jV ≫ yoneda.map q) ≫ v' := by
    rw [h.w, hv, Category.assoc]
  refine ⟨yoneda.preimage (h'.lift ηV (yoneda.map jV ≫ yoneda.map q) hw), ?_, ?_⟩
  · simpa only [Functor.map_preimage] using h'.lift_fst _ _ hw
  · refine IsPullback.of_right ?_ ?_ h'
    · rw [Functor.map_preimage, h'.lift_fst _ _ hw, ← hv]
      exact h
    · simpa only [Functor.map_preimage] using h'.lift_snd _ _ hw

/-- A property of schemes stable under base change and isomorphism passes from a chart `w'` to the
base change `k` of `i` along `w'`, read through `G ≅ T`. -/
private theorem map_of_isPullback_of_presheaf {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : G ⟶ X}
    {T W W' : BigFppfOver B S hS} {w' : yoneda.obj W' ⟶ X} {j : W ⟶ W'} {η : yoneda.obj W ⟶ G}
    (hW : IsPullback η (yoneda.map j) i w') (e : G ≅ yoneda.obj T) {k : W ⟶ T}
    (hk : yoneda.map k = η ≫ e.hom)
    (hw' : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf w') :
    P ((BigFppfOver.toScheme B S hS).map k) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange _
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1 ?_
  rw [hk]
  exact MorphismProperty.RespectsIso.postcomp _ e.hom η
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hW.flip hw')

/-- **Lifting a regular function on an affine closed subspace to a chart.** Let `i : G ⟶ X` be a
thickening of algebraic spaces over `S` with `G ≅ T` for an affine object `T` of the site, let
`w' : U' ⟶ X` be a surjective étale chart from an affine object with affine kernel pair
`q₁, q₂ : R' ⟶ U'`, and let `j : U ⟶ U'` be the base change of `i` along `w'`, with nilpotent
kernel on global sections and `k : U ⟶ T` its projection read through `G ≅ T`. Then every
regular function `z` on `T` has a lift `y` on `U'` with `q₁^* y = q₂^* y` and `j^* y = k^* z`. -/
theorem C1573.exists_appTop_eq_of_isThickeningHom_chart
    {X G : AlgebraicSpaces B S hS} (i : G ⟶ X) (hi : IsThickeningHom B S hS i)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (e : G.1 ≅ yoneda.obj T)
    {W' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W')]
    (w' : yoneda.obj W' ⟶ X.1)
    (hw'e : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w')
    (hw's : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w')
    {R' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj R')]
    (q₁ q₂ : R' ⟶ W') (hR' : IsPullback (yoneda.map q₁) (yoneda.map q₂) w' w')
    {W : BigFppfOver B S hS} (j : W ⟶ W') (η : yoneda.obj W ⟶ G.1)
    (hW : IsPullback η (yoneda.map j) i.hom w')
    (hJ : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map j).appTop.hom))
    (k : W ⟶ T) (hk : yoneda.map k = η ≫ e.hom)
    (z : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    ∃ y : Γ((BigFppfOver.toScheme B S hS).obj W', ⊤),
      ((BigFppfOver.toScheme B S hS).map q₁).appTop y =
          ((BigFppfOver.toScheme B S hS).map q₂).appTop y ∧
        ((BigFppfOver.toScheme B S hS).map j).appTop y =
          ((BigFppfOver.toScheme B S hS).map k).appTop z := by
  let F := BigFppfOver.toScheme B S hS
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hci := hi.isClosedImmersion
  -- The chart and its overlaps.
  have hq₁e : Etale (F.map q₁) := hw'e.2 w' (yoneda.map q₂) q₁ hR'.flip
  have hjci : _root_.AlgebraicGeometry.IsClosedImmersion (F.map j) := hci.property w' η j hW
  have : IsAffine (F.obj W) := isAffine_of_isAffineHom (F.map j)
  -- `k` is étale and surjective.
  have hke : Etale (F.map k) := map_of_isPullback_of_presheaf hW e hk hw'e
  have hks : Surjective (F.map k) := map_of_isPullback_of_presheaf hW e hk hw's
  -- The base change of the double overlap.
  set r' : yoneda.obj R' ⟶ X.1 := yoneda.map q₁ ≫ w'
  have hR₀ := hci.rep.isPullback r'
  set ρ₀ := hci.rep.snd r'
  have hρ₀ci : _root_.AlgebraicGeometry.IsClosedImmersion (F.map ρ₀) := hci.property r' _ ρ₀ hR₀
  have : IsAffine (F.obj (hci.rep.pullback r')) := isAffine_of_isAffineHom (F.map ρ₀)
  obtain ⟨r₁, hr₁η, hP₁⟩ := exists_isPullback_baseChange i.hom hR₀ hW q₁ rfl
  obtain ⟨r₂, hr₂η, hP₂⟩ := exists_isPullback_baseChange i.hom hR₀ hW q₂ hR'.w
  -- The base change of the double overlap is `U ×_T U`.
  have hQ : IsPullback (yoneda.map r₂) (yoneda.map r₁) η η := by
    refine IsPullback.of_bot ?_ (by rw [hr₁η, hr₂η]) hW
    have := hP₂.paste_vert hR'.flip
    rwa [← hP₁.w, ← hW.w] at this
  have hRT : IsPullback (yoneda.map r₁) (yoneda.map r₂) (yoneda.map k) (yoneda.map k) := by
    rw [hk]
    exact hQ.flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) (by simp)
      (by simp)
  -- The triple overlap.
  set c₀₁ := pullback.fst q₂ q₁
  set c₁₂ := pullback.snd q₂ q₁
  have hR''site : IsPullback c₀₁ c₁₂ q₂ q₁ := IsPullback.of_hasPullback q₂ q₁
  have : IsAffine (F.obj (pullback q₂ q₁)) := IsAffine.of_isPullback (hR''site.map F)
  have hc : (yoneda.map (c₀₁ ≫ q₁)) ≫ w' = (yoneda.map (c₁₂ ≫ q₂)) ≫ w' := by
    simp only [Functor.map_comp, Category.assoc, hR'.w]
    rw [← Category.assoc, ← Functor.map_comp, hR''site.w, Functor.map_comp, Category.assoc,
      ← hR'.w]
  set c₀₂ : pullback q₂ q₁ ⟶ R' := yoneda.preimage (hR'.lift _ _ hc)
  have h₀₂₀ : c₀₂ ≫ q₁ = c₀₁ ≫ q₁ :=
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hR'.lift_fst])
  have h₀₂₁ : c₀₂ ≫ q₂ = c₁₂ ≫ q₂ :=
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hR'.lift_snd])
  -- Site-level forms of the squares over the base change of the double overlap.
  have hP₁site : IsPullback r₁ ρ₀ j q₁ := IsPullback.of_map_of_faithful yoneda hP₁
  have hw₂ : r₂ ≫ j = ρ₀ ≫ q₂ := yoneda.map_injective (by simpa using hP₂.w)
  -- The base change of the triple overlap.
  set e₁₂ := pullback.fst r₁ r₂
  set e₀₁ := pullback.snd r₁ r₂
  have hL : IsPullback e₁₂ e₀₁ r₁ r₂ := IsPullback.of_hasPullback r₁ r₂
  have : IsAffine (F.obj (pullback r₁ r₂)) := IsAffine.of_isPullback (hL.map F)
  have hr₂w : (e₀₁ ≫ ρ₀) ≫ q₂ = (e₁₂ ≫ ρ₀) ≫ q₁ := by
    rw [Category.assoc, ← hw₂, ← Category.assoc, ← hL.w, Category.assoc, hP₁site.w,
      Category.assoc]
  set ρ₂ : pullback r₁ r₂ ⟶ pullback q₂ q₁ := pullback.lift _ _ hr₂w
  have hρ₂₀₁ : ρ₂ ≫ c₀₁ = e₀₁ ≫ ρ₀ := pullback.lift_fst _ _ _
  have hρ₂₁₂ : ρ₂ ≫ c₁₂ = e₁₂ ≫ ρ₀ := pullback.lift_snd _ _ _
  have he₀₂w : (e₀₁ ≫ r₁) ≫ j = (ρ₂ ≫ c₀₂) ≫ q₁ := by
    simp only [Category.assoc, h₀₂₀]
    rw [← Category.assoc ρ₂, hρ₂₀₁, Category.assoc, hP₁site.w]
  set e₀₂ : pullback r₁ r₂ ⟶ hci.rep.pullback r' := hP₁site.lift _ _ he₀₂w
  have he₀₂ : e₀₂ ≫ ρ₀ = ρ₂ ≫ c₀₂ := hP₁site.lift_snd _ _ _
  have hR₂ : IsPullback ρ₂ e₀₁ c₀₁ ρ₀ := by
    refine (IsPullback.of_bot ?_ hρ₂₀₁.symm hR''site).flip
    rw [hρ₂₁₂, ← hw₂]
    exact hL.flip.paste_vert hP₁site
  have hR₂T : IsPullback (e₁₂ ≫ r₂) e₀₁ k (r₁ ≫ k) := by
    have h := hL.paste_horiz (IsPullback.of_map_of_faithful yoneda hRT).flip
    rwa [show r₂ ≫ k = r₁ ≫ k from
      yoneda.map_injective (by simpa using hRT.w.symm)] at h
  -- The scheme-level statement.
  exact exists_appTop_eq_of_isNilpotent_ker (F.map j) (F.map q₁) (F.map q₂) (F.map ρ₀)
    (F.map r₁) (F.map r₂) (hP₁site.flip.map F) (by rw [← F.map_comp, ← F.map_comp, hw₂])
    (F.map k) (isPullback_toScheme_of_isPullback_yoneda B S hS hRT) (F.map c₀₁) (F.map c₀₂)
    (F.map c₁₂) (hR''site.map F) (by rw [← F.map_comp, ← F.map_comp, h₀₂₀])
    (by rw [← F.map_comp, ← F.map_comp, h₀₂₁]) (F.map ρ₂) (F.map e₀₁) (F.map e₀₂) (F.map e₁₂)
    (hR₂.map F) (by rw [← F.map_comp, ← F.map_comp, he₀₂])
    (by rw [← F.map_comp, ← F.map_comp, hρ₂₁₂])
    (by simpa only [F.map_comp] using hR₂T.map F) hJ z

end AlgebraicGeometry.Space

end

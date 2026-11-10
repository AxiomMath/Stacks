module

public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffinePushoutDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineAtlasCartesianCharts

/-!
# A scheme étale over a pushout of algebraic spaces is the pushout of its restrictions

Let `Y'` be the pushout of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` of
algebraic spaces over `S`, built in Stacks 07VX as the quotient of a pushout of scheme charts
`P = U' ⨿_U V`. For a scheme `W` étale over `Y'` with base changes `W₁ = W ×_{Y'} X'`,
`W₂ = W ×_{Y'} Y` and `W₀ = W ×_{Y'} X`, the square of schemes `W₀ ⟶ W₁`, `W₀ ⟶ W₂`, `W₁ ⟶ W`,
`W₂ ⟶ W` is a pushout.

The base change `W' = W ×_{Y'} P` is étale over the scheme pushout `P`, so it is the pushout of
its restrictions to `U'` and `V` (Stacks 07RX,
`Stacks.Pushout.C1573.isPushout_of_etale_of_isPullback`);
those restrictions are the base changes of `W₁` and `W₂` along `W' ⟶ W`, because the chart squares
are cartesian; and being such a pushout descends along the étale surjection `W' ⟶ W`
(`Stacks.Pushout.isPushout_of_isPushout_of_etale_surjective`).

This is the étale-local form of the pushout that the structure-sheaf assertion of Stacks 07VX and
the gluing statements of Stacks 07W0 and 07W3 reduce to.

## Main results

* `AlgebraicGeometry.Space.isPushout_toScheme_of_etale_of_charts`.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfOver.hasSheafify_type
attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- If a square over `h` with corner `U ⟶ P` is cartesian and so is its composite with a square
along `π : E' ⟶ P`, then the induced map `E ⟶ U` exists and makes the square along `π` cartesian. -/
private theorem exists_isPullback_of_isPullback_paste {C : Type*} [Category C]
    {T Z : Cᵒᵖ ⥤ Type _} {U P E' E : C} {a : U ⟶ P} {p' : yoneda.obj U ⟶ T}
    {m : yoneda.obj P ⟶ Z} {h : T ⟶ Z} (hc : IsPullback (yoneda.map a) p' m h) (π : E' ⟶ P)
    (x : E ⟶ E') (y : yoneda.obj E ⟶ T) (hbig : IsPullback (yoneda.map x) y (yoneda.map π ≫ m) h) :
    ∃ ℓ : E ⟶ U, yoneda.map ℓ ≫ yoneda.map a = yoneda.map (x ≫ π) ∧ yoneda.map ℓ ≫ p' = y ∧
      IsPullback (yoneda.map x) (yoneda.map ℓ) (yoneda.map π) (yoneda.map a) := by
  obtain ⟨ℓ, hℓ⟩ := yoneda.map_surjective (hc.lift (yoneda.map (x ≫ π)) y
    (by rw [Functor.map_comp, Category.assoc]; exact hbig.w))
  have hℓa : yoneda.map ℓ ≫ yoneda.map a = yoneda.map (x ≫ π) := hℓ ▸ hc.lift_fst _ _ _
  have hℓp : yoneda.map ℓ ≫ p' = y := hℓ ▸ hc.lift_snd _ _ _
  refine ⟨ℓ, hℓa, hℓp, IsPullback.of_bot ?_ (by rw [← Functor.map_comp, ← hℓa]) hc⟩
  rw [hℓp]
  exact hbig

/-- **A scheme étale over the pushout of Stacks 07VX is the pushout of its restrictions.** Let
`A` be a compatible pair of charts for a thickening `i` and an affine `f`, and `E` the pushout of
algebraic spaces with chart `qm : P ⟶ E` whose two chart squares are cartesian. For a scheme `W`
étale over `E` and cartesian squares exhibiting `W₁`, `W₂`, `W₀` as its base changes to `X'`, `Y`
and `X`, the square of schemes `W₀ ⟶ W₁ ⟶ W ⟵ W₂ ⟵ W₀` is a pushout. -/
theorem isPushout_toScheme_of_etale_of_charts
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (A : ThickeningAffineAtlas B S hS i f) {E : AlgebraicSpaces B S hS} {a : X' ⟶ E}
    {b : Y ⟶ E} (hpush : IsPushout i f a b) {qm : yoneda.obj A.P ⟶ E.1}
    (hqmS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hca : IsPullback (yoneda.map A.a) A.p' qm a.hom)
    (hcb : IsPullback (yoneda.map A.b) A.q qm b.hom)
    {W W₁ W₂ W₀ : BigFppfOver B S hS} (w : yoneda.obj W ⟶ E.1)
    (hwE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) w)
    {u₁ : W₁ ⟶ W} {p₁ : yoneda.obj W₁ ⟶ X'.1} (h₁ : IsPullback (yoneda.map u₁) p₁ w a.hom)
    {u₂ : W₂ ⟶ W} {p₂ : yoneda.obj W₂ ⟶ Y.1} (h₂ : IsPullback (yoneda.map u₂) p₂ w b.hom)
    {iW : W₀ ⟶ W₁} {fW : W₀ ⟶ W₂} {p₀ : yoneda.obj W₀ ⟶ X.1}
    (h₀₁ : IsPullback (yoneda.map iW) p₀ p₁ i.hom) (h₀₂ : IsPullback (yoneda.map fW) p₀ p₂ f.hom)
    (hw₀ : iW ≫ u₁ = fW ≫ u₂) :
    IsPushout ((BigFppfOver.toScheme B S hS).map iW) ((BigFppfOver.toScheme B S hS).map fW)
      ((BigFppfOver.toScheme B S hS).map u₁) ((BigFppfOver.toScheme B S hS).map u₂) := by
  set Φ := BigFppfOver.toScheme B S hS
  have := A.isAffineHom_g
  -- the thickening and the affine morphism of the square, and the thickening `W₂ ⟶ W`
  have hiW : Stacks.Thickenings.IsThickening (Φ.map iW) :=
    ⟨hi.isClosedImmersion.property p₁ p₀ iW h₀₁.flip,
      (hi.surjective.property p₁ p₀ iW h₀₁.flip).surj⟩
  have hfW : _root_.AlgebraicGeometry.IsAffineHom (Φ.map fW) :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.property Y.property
      hf).2.property p₂ p₀ fW h₀₂.flip
  have hb : IsThickeningHom B S hS b := by
    have : HasPushout i f := hpush.hasPushout
    have hg := C1573.pushout_inr_isThickening_of_thickeningAffineAtlas B S hS A
    set e := hpush.isoPushout.symm with he
    have hbe : pushout.inr i f ≫ e.hom = b := by
      rw [he, Iso.symm_hom, IsPushout.inr_isoPushout_inv]
    have : IsIso e.hom.hom := ⟨⟨e.inv.hom, congrArg (fun φ => φ.hom) e.hom_inv_id,
      congrArg (fun φ => φ.hom) e.inv_hom_id⟩⟩
    rw [← hbe]
    refine (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).mpr ⟨?_, ?_⟩
    · exact MorphismProperty.RespectsIso.postcomp (MorphismProperty.presheaf
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) e.hom.hom _ hg.isClosedImmersion
    · intro z
      obtain ⟨y, hy⟩ := pointsMap_surjective_of_isIso B S hS e.hom.hom z
      obtain ⟨x, hx⟩ := hg.surjective_pointsMap y
      refine ⟨x, ?_⟩
      change pointsMap B S hS Y.1 ((pushout.inr i f).hom ≫ e.hom.hom) x = z
      rw [pointsMap_comp]
      simp only [Function.comp_apply]
      rw [hx]
      exact hy
  have hu₂ : Stacks.Thickenings.IsThickening (Φ.map u₂) :=
    ⟨hb.isClosedImmersion.property w p₂ u₂ h₂.flip, (hb.surjective.property w p₂ u₂ h₂.flip).surj⟩
  -- the étale surjective cover `W' = W ×_E P` and its étale map to `P`
  set W' := hqmE.rep.pullback w
  set ρ : W' ⟶ W := hqmE.rep.snd w
  set π : W' ⟶ A.P := hqmE.rep.fst' w
  have hW' : IsPullback (yoneda.map π) (yoneda.map ρ) qm w := hqmE.rep.isPullback' w
  have : Etale (Φ.map ρ) := hqmE.property w (yoneda.map π) ρ hW'
  have : Surjective (Φ.map ρ) := hqmS.property w (yoneda.map π) ρ hW'
  have : Etale (Φ.map π) := hwE.property qm (yoneda.map ρ) π hW'.flip
  -- the three base changes of the cover, in the site
  set E₁ := pullback ρ u₁ with hE₁
  set E₂ := pullback ρ u₂ with hE₂
  set E₀ := pullback (pullback.snd ρ u₁) iW
  set v₁ := pullback.fst ρ u₁
  set q₁ := pullback.snd ρ u₁
  set v₂ := pullback.fst ρ u₂
  set q₂ := pullback.snd ρ u₂
  set kE := pullback.fst q₁ iW
  set q₀ := pullback.snd q₁ iW
  have hc₁ : IsPullback kE q₀ q₁ iW := IsPullback.of_hasPullback _ _
  have hE₁pb : IsPullback v₁ q₁ ρ u₁ := IsPullback.of_hasPullback _ _
  have hE₂pb : IsPullback v₂ q₂ ρ u₂ := IsPullback.of_hasPullback _ _
  have hlift : (kE ≫ v₁) ≫ ρ = (q₀ ≫ fW) ≫ u₂ := by
    rw [Category.assoc, hE₁pb.w, ← Category.assoc, hc₁.w, Category.assoc, hw₀, Category.assoc]
  set gE : E₀ ⟶ E₂ := pullback.lift (kE ≫ v₁) (q₀ ≫ fW) hlift with hgE
  have hgEv : gE ≫ v₂ = kE ≫ v₁ := pullback.lift_fst _ _ _
  have hgEq : gE ≫ q₂ = q₀ ≫ fW := pullback.lift_snd _ _ _
  have hc₂ : IsPullback gE q₀ q₂ fW := by
    refine IsPullback.of_right ?_ hgEq hE₂pb
    rw [hgEv, ← hw₀]
    exact hc₁.paste_horiz hE₁pb
  -- `E₁` and `E₂` are the base changes of the charts `U'` and `V` of `P`
  obtain ⟨ℓ₁, hℓ₁a, hℓ₁p, hp₁⟩ := exists_isPullback_of_isPullback_paste hca π v₁
    (yoneda.map q₁ ≫ p₁) (by
      rw [hW'.w]; exact ((IsPullback.of_hasPullback ρ u₁).map yoneda).paste_vert h₁)
  obtain ⟨ℓ₂, hℓ₂b, hℓ₂q, hp₂⟩ := exists_isPullback_of_isPullback_paste hcb π v₂
    (yoneda.map q₂ ≫ p₂) (by
      rw [hW'.w]; exact ((IsPullback.of_hasPullback ρ u₂).map yoneda).paste_vert h₂)
  -- `E₀` is the base change of the chart `U` of `X`
  obtain ⟨ℓ₀, hℓ₀k, hℓ₀p, hk₀⟩ := exists_isPullback_of_isPullback_paste A.isPullback_thickening ℓ₁
    kE (yoneda.map q₀ ≫ p₀) (by rw [hℓ₁p]; exact (hc₁.map yoneda).paste_vert h₀₁)
  -- the compatibilities, read in the site
  have eℓ₁ : ℓ₁ ≫ A.a = v₁ ≫ π := yoneda.map_injective (by rw [Functor.map_comp, hℓ₁a])
  have eℓ₂ : ℓ₂ ≫ A.b = v₂ ≫ π := yoneda.map_injective (by rw [Functor.map_comp, hℓ₂b])
  have eℓ₀ : ℓ₀ ≫ A.k = kE ≫ ℓ₁ := yoneda.map_injective (by rw [Functor.map_comp, hℓ₀k])
  have hkgab : A.k ≫ A.a = A.g ≫ A.b :=
    Φ.map_injective (by rw [Φ.map_comp, Φ.map_comp]; exact A.isPushout_chart.w)
  have hg₀ : ℓ₀ ≫ A.g = gE ≫ ℓ₂ := by
    apply yoneda.map_injective
    apply hcb.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, ← hkgab,
        ← Category.assoc, eℓ₀, eℓ₂, Category.assoc, eℓ₁, ← Category.assoc gE, hgEv,
        Category.assoc]
    · have hw1 : yoneda.map A.g ≫ A.q = A.p ≫ f.hom := A.isPullback_affine.w.symm
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hw1, hℓ₂q,
        ← Category.assoc (yoneda.map ℓ₀), hℓ₀p, ← Category.assoc (yoneda.map gE),
        ← Functor.map_comp, hgEq, Functor.map_comp, Category.assoc, Category.assoc, h₀₂.w]
  have hgℓ : IsPullback (yoneda.map gE) (yoneda.map ℓ₀) (yoneda.map ℓ₂) (yoneda.map A.g) := by
    refine IsPullback.of_bot ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, hg₀])
      A.isPullback_affine.flip
    have hbig : IsPullback (yoneda.map gE) (yoneda.map q₀ ≫ p₀) (yoneda.map q₂ ≫ p₂) f.hom :=
      (hc₂.map yoneda).paste_vert h₀₂
    rw [hℓ₀p, hℓ₂q]
    exact hbig
  -- the scheme-level squares
  have hP₁s := (IsPullback.of_map_of_faithful yoneda hp₁).map Φ
  have hP₂s := (IsPullback.of_map_of_faithful yoneda hp₂).map Φ
  have hcart₁ := (IsPullback.of_map_of_faithful yoneda hk₀).map Φ
  have hcart₂ := (IsPullback.of_map_of_faithful yoneda hgℓ).map Φ
  have hwE : Φ.map kE ≫ Φ.map v₁ = Φ.map gE ≫ Φ.map v₂ := by
    rw [← Φ.map_comp, ← Φ.map_comp, hgEv]
  have hE : IsPushout (Φ.map kE) (Φ.map gE) (Φ.map v₁) (Φ.map v₂) :=
    Stacks.Pushout.C1573.isPushout_of_etale_of_isPullback A.isThickening_k A.isPushout_chart
      (Φ.map π) hP₁s hP₂s hcart₁ hcart₂ hwE
  exact Stacks.Pushout.isPushout_of_isPushout_of_etale_surjective hiW hu₂
    (by rw [← Φ.map_comp, ← Φ.map_comp, hw₀]) (Φ.map ρ) (hE₁pb.map Φ) (hE₂pb.map Φ)
    (hc₁.map Φ) (hc₂.map Φ) hE

/-- **The structure sheaf of the pushout of Stacks 07VX, section by section.** In the situation of
`AlgebraicGeometry.Space.isPushout_toScheme_of_etale_of_charts`, for every scheme `W` étale over
the pushout `Y'`, the ring of functions on `W` is the fibre product of the rings of functions on
its base changes to `Y` and to `X'` over that on its base change to `X`:
`Γ(W, 𝒪) = Γ(W ×_{Y'} Y, 𝒪) ×_{Γ(W ×_{Y'} X, 𝒪)} Γ(W ×_{Y'} X', 𝒪)`.

These are the sections over `W` of `𝒪_{Y'}`, `𝒪_Y`, `f_*𝒪_X` and `f'_*𝒪_{X'}` read on the small
étale site of `Y'`, so this is the equality `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}` of the source,
evaluated on every object of that site. -/
theorem isPullback_appTop_of_etale_of_charts
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (A : ThickeningAffineAtlas B S hS i f) {E : AlgebraicSpaces B S hS} {a : X' ⟶ E}
    {b : Y ⟶ E} (hpush : IsPushout i f a b) {qm : yoneda.obj A.P ⟶ E.1}
    (hqmS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hca : IsPullback (yoneda.map A.a) A.p' qm a.hom)
    (hcb : IsPullback (yoneda.map A.b) A.q qm b.hom)
    {W W₁ W₂ W₀ : BigFppfOver B S hS} (w : yoneda.obj W ⟶ E.1)
    (hwE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) w)
    {u₁ : W₁ ⟶ W} {p₁ : yoneda.obj W₁ ⟶ X'.1} (h₁ : IsPullback (yoneda.map u₁) p₁ w a.hom)
    {u₂ : W₂ ⟶ W} {p₂ : yoneda.obj W₂ ⟶ Y.1} (h₂ : IsPullback (yoneda.map u₂) p₂ w b.hom)
    {iW : W₀ ⟶ W₁} {fW : W₀ ⟶ W₂} {p₀ : yoneda.obj W₀ ⟶ X.1}
    (h₀₁ : IsPullback (yoneda.map iW) p₀ p₁ i.hom) (h₀₂ : IsPullback (yoneda.map fW) p₀ p₂ f.hom)
    (hw₀ : iW ≫ u₁ = fW ≫ u₂) :
    let Φ := BigFppfOver.toScheme B S hS
    IsPullback ((Φ.map u₂).app ⊤) ((Φ.map u₁).app ⊤) ((Φ.map fW).app ((Φ.map u₂) ⁻¹ᵁ ⊤))
      ((Φ.map iW).app ((Φ.map u₁) ⁻¹ᵁ ⊤) ≫ eqToHom (congrArg (fun O ↦ Γ(Φ.obj W₀, O))
        (congrArg (fun k : Φ.obj W₀ ⟶ Φ.obj W ↦ k ⁻¹ᵁ ⊤)
          (show Φ.map iW ≫ Φ.map u₁ = Φ.map fW ≫ Φ.map u₂ by
            rw [← Φ.map_comp, ← Φ.map_comp, hw₀])))) := by
  intro Φ
  have hpo := isPushout_toScheme_of_etale_of_charts B S hS hi hf A hpush hqmS hqmE hca hcb w hwE
    h₁ h₂ h₀₁ h₀₂ hw₀
  have hiW : Stacks.Thickenings.IsThickening (Φ.map iW) :=
    ⟨hi.isClosedImmersion.property p₁ p₀ iW h₀₁.flip,
      (hi.surjective.property p₁ p₀ iW h₀₁.flip).surj⟩
  have : _root_.AlgebraicGeometry.IsAffineHom (Φ.map fW) :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.property Y.property
      hf).2.property p₂ p₀ fW h₀₂.flip
  exact ThickeningAffinePushoutSituation.sections_isPullback_of_isPushout hiW hpo ⊤

end AlgebraicGeometry.Space

module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFormalOfStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoverOfEtalePointLifts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineSetCondition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningPushforward
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningSubfunctorDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace

/-!
# Sheaves representable over an affine formal algebraic space

Let `Y` be an affine formal algebraic space over `S` and let `f : X ⟶ Y` be a morphism of fppf
sheaves which is representable by algebraic spaces. Then `X` is a formal algebraic space over
`S`: this is **Stacks 0AJH**. The étale case is proved separately, with a shorter proof of the
affineness of the stages, because it is what several consumers use.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_iso_of_isRepresentableEtale_of_isThickening`: a
  sheaf representable étale over an affine object of the site whose base change to a
  thickening of that object is affine is itself affine.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_isAffineFormal`:
  **Stacks 0AJH**.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableEtale_over_affineFormal`:
  **Stacks 0AJH** for a morphism which is representable by algebraic spaces and étale, and
  `AlgebraicGeometry.FormalSpace.representableEtaleOverAffineIsFormal`, the same statement as
  the proposition `AlgebraicGeometry.FormalSpace.RepresentableEtaleOverAffineIsFormal`.

## Implementation notes

The proof is the source's, with the chart transport of Stacks 0AIU done at once over `X`.
Write `Y = colim Yλ` along thickenings of affine schemes and fix a stage `Y₀`. The base change
`X₀ = Y₀ ×_Y X` is an algebraic space, so it has an étale atlas by affine schemes `Uₖ`. Each
chart `Uₖ ⟶ X₀` is transported along the thickening `X₀ ⟶ X` to a morphism `Wₖ ⟶ X`,
representable by objects of the site and étale
(`AlgebraicGeometry.FormalSpace.exists_etale_isPullback_of_isRepresentableThickeningULift`).
The base changes `Wₖ ×_Y Yλ` for `λ` above the fixed stage form a directed system along
thickenings whose colimit is `Wₖ`, colimits of sheaves being universal; each of them is an
algebraic space over the affine `Yλ` whose base change to `Y₀` is `Uₖ`, hence affine by the
thickening case of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedSubspace_of_isSurjective_terminal` (in the
étale case already by
`AlgebraicGeometry.Space.isAffineSpace_of_isEtale_of_isThickening_of_isAffineSpace_pullback`).
So each `Wₖ` is an affine formal algebraic space, and the `Wₖ` cover `X` because the `Uₖ` cover
`X₀` and `Wₖ ×_X T` is homeomorphic to `Uₖ ×_{X₀} T₀` for every point `T ⟶ X`.

## References

* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf representable by algebraic spaces over an object of the site descends to an
algebraic space valued in the value universe of the site. -/
private theorem exists_descent_of_isRepresentableByAlgebraicSpacesULift
    {T : BigFppfOver B S hS} {Z : FppfSheaf B S hS}
    (z : Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T)
    (hz : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS z.hom) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS V)
      (p : V ⟶ yoneda.obj T) (eV : (uliftPresheaf B S hS).obj V ≅ Z.obj),
      (uliftPresheaf B S hS).map p =
        eV.hom ≫ z.hom ≫ ((sheafifiedYonedaCompForgetIso B S hS).app T).hom := by
  classical
  let ξ := ((sheafifiedYonedaCompForgetIso B S hS).app T).inv
  have hsnd : IsIso (pullback.snd ξ z.hom) :=
    (IsPullback.of_hasPullback ξ z.hom).isIso_snd_of_isIso
  have hZalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS (asIso (pullback.snd ξ z.hom)) (hz T ξ)
  have _ := Space.small_of_isAlgebraicSpaceULift B S hS hZalg
  let eV : (uliftPresheaf B S hS).obj (FunctorToTypes.shrink.{u} Z.obj) ≅ Z.obj :=
    Space.shrinkCompUliftFunctorIso Z.obj
  exact ⟨FunctorToTypes.shrink.{u} Z.obj,
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS eV.symm hZalg),
    (uliftPresheaf B S hS).preimage
      (eV.hom ≫ z.hom ≫ ((sheafifiedYonedaCompForgetIso B S hS).app T).hom),
    eV, (uliftPresheaf B S hS).map_preimage _⟩

/-- The descent of a sheaf over an affine object of the site to the value universe of the
site, with the affineness of the descended algebraic space over a thickening as an input: let
`z : Z ⟶ h_T` be representable by algebraic spaces and let its base change along the thickening
`h_i` be affine. Then `Z` is affine as soon as the descended morphism `p : V ⟶ h_T` of
algebraic spaces valued in `Type u` is affine whenever its base change along `h_i` is. -/
private theorem exists_affine_iso_of_isThickening_of_descent {T₀ T : BigFppfOver B S hS}
    (i : T₀ ⟶ T)
    {Z : FppfSheaf B S hS} (z : Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T)
    (hz : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS z.hom)
    (hlem : ∀ {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS V →
      ∀ (p : V ⟶ yoneda.obj T) (eV : (uliftPresheaf B S hS).obj V ≅ Z.obj),
      (uliftPresheaf B S hS).map p =
        eV.hom ≫ z.hom ≫ ((sheafifiedYonedaCompForgetIso B S hS).app T).hom →
      Space.IsAffineSpace B S hS (pullback p (yoneda.map i)) → Space.IsAffineSpace B S hS V)
    {U₀ : BigFppfOver B S hS}
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (e₀ : pullback z ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i) ≅
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U₀) :
    ∃ T' : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T') ∧
      Nonempty (Z ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T') := by
  classical
  -- descend `Z` to the value universe of the site
  obtain ⟨V, hV, p, eV, hHp⟩ :=
    exists_descent_of_isRepresentableByAlgebraicSpacesULift B S hS z hz
  let J := BigFppfOver.topology B S hS
  let Fy := Sheaf.sheafifiedYoneda J
  let Pr := sheafToPresheaf J (Type (u + 1))
  let y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let H := uliftPresheaf B S hS
  let ee := sheafifiedYonedaCompForgetIso B S hS
  -- `z` read in presheaves, with target the universe-lifted Yoneda presheaf
  let z' : Z.obj ⟶ y.obj T := z.hom ≫ (ee.app T).hom
  replace hHp : H.map p = eV.hom ≫ z' := hHp
  -- the base change of `p` along `h_i`, read in presheaves
  have hQ0 : IsPullback (e₀.inv ≫ pullback.fst z (Fy.map i)) (e₀.inv ≫ pullback.snd z (Fy.map i))
      z (Fy.map i) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩
      e₀.symm rfl rfl
  have Q₁ : IsPullback (Pr.map (e₀.inv ≫ pullback.fst z (Fy.map i)))
      (Pr.map (e₀.inv ≫ pullback.snd z (Fy.map i)) ≫ (ee.app T₀).hom) z' (y.map i) :=
    (hQ0.map Pr).of_iso (Iso.refl _) (Iso.refl _) (ee.app T₀) (ee.app T) (by simp) (by simp)
      rfl (ee.hom.naturality i)
  let snd'' : y.obj U₀ ⟶ y.obj T₀ := (ee.app U₀).inv ≫
    Pr.map (e₀.inv ≫ pullback.snd z (Fy.map i)) ≫ (ee.app T₀).hom
  let β : U₀ ⟶ T₀ := (ULiftYoneda.fullyFaithful.{u + 1} (C := BigFppfOver B S hS)).preimage snd''
  have hβ : y.map β = snd'' := Functor.FullyFaithful.map_preimage _ _
  let fst'' : y.obj U₀ ⟶ Z.obj := (ee.app U₀).inv ≫ Pr.map (e₀.inv ≫ pullback.fst z (Fy.map i))
  have Q₂ : IsPullback (fst'' ≫ eV.inv) (y.map β) (eV.hom ≫ z') (y.map i) :=
    Q₁.of_iso (ee.app U₀) eV.symm (Iso.refl _) (Iso.refl _)
      (by
        dsimp only [fst'']
        rw [Category.assoc, ← Category.assoc (ee.app U₀).hom, Iso.hom_inv_id, Category.id_comp]
        rfl)
      (by
        rw [hβ]
        dsimp only [snd'']
        rw [← Category.assoc (ee.app U₀).hom, Iso.hom_inv_id, Category.id_comp, Iso.refl_hom,
          Category.comp_id])
      (by simp) (by simp)
  let a' : yoneda.obj U₀ ⟶ V := H.preimage (fst'' ≫ eV.inv)
  have hHa' : H.map a' = fst'' ≫ eV.inv := H.map_preimage _
  have sq : IsPullback a' (yoneda.map β) p (yoneda.map i) := by
    refine IsPullback.of_map H (H.map_injective ?_) ?_
    · rw [H.map_comp, H.map_comp, hHa', hHp]
      exact Q₂.w
    · rwa [hHa', hHp]
  obtain ⟨T', hT', ⟨eT'⟩⟩ := hlem hV p eV hHp ⟨U₀, hU₀, ⟨sq.isoPullback.symm⟩⟩
  exact ⟨T', hT', ⟨(fullyFaithfulSheafToPresheaf J _).preimageIso
    (eV.symm ≪≫ H.mapIso eT' ≪≫ (ee.app T').symm)⟩⟩

/-- **A sheaf representable étale over an affine object of the site, affine over a thickening
of it, is affine.** Let `i : T₀ ⟶ T` be a morphism of the site whose underlying morphism of
schemes is a thickening and let `z : Z ⟶ h_T` be representable by algebraic spaces and étale.
If the base change of `z` along `h_i` is represented by an affine object of the site, then so
is `Z`.

This is
`AlgebraicGeometry.Space.isAffineSpace_of_isEtale_of_isThickening_of_isAffineSpace_pullback`, which
is stated for presheaves valued in `Type u`, read for sheaves valued in `Type (u + 1)` through the
universe lift, which is fully faithful on the algebraic spaces. -/
theorem exists_affine_iso_of_isRepresentableEtale_of_isThickening {T₀ T : BigFppfOver B S hS}
    (i : T₀ ⟶ T) (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    {Z : FppfSheaf B S hS} (z : Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T)
    (hz : IsRepresentableEtale B S hS z) {U₀ : BigFppfOver B S hS}
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (e₀ : pullback z ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i) ≅
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U₀) :
    ∃ T' : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T') ∧
      Nonempty (Z ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T') := by
  refine exists_affine_iso_of_isThickening_of_descent B S hS i z hz.1
    (fun {V} hV p eV hHp h₀ ↦ ?_) hU₀ e₀
  let ee := sheafifiedYonedaCompForgetIso B S hS
  let ξ := (ee.app T).inv
  have hsnd : IsIso (pullback.snd ξ z.hom) :=
    (IsPullback.of_hasPullback ξ z.hom).isIso_snd_of_isIso
  have hfst : pullback.fst ξ z.hom = pullback.snd ξ z.hom ≫ z.hom ≫ (ee.app T).hom := by
    rw [← cancel_mono (ee.app T).inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    exact pullback.condition
  have hz'et : Space.IsEtaleULift.{u + 1} B S hS (z.hom ≫ (ee.app T).hom) := by
    have h₁ : Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ z.hom) := hz.2 T ξ
    rw [hfst] at h₁
    simpa using isEtaleULift_precomp_iso B S hS (asIso (pullback.snd ξ z.hom)).symm _ h₁
  have hp : Space.IsEtale B S hS p := by
    refine (Space.isEtaleULift_whiskerRight_iff.{u + 1} B S hS p).mp ?_
    change Space.IsEtaleULift.{u + 1} B S hS ((uliftPresheaf B S hS).map p)
    rw [hHp]
    exact isEtaleULift_precomp_iso B S hS eV _ hz'et
  exact Space.isAffineSpace_of_isEtale_of_isThickening_of_isAffineSpace_pullback B S hS hV i hi p
    hp h₀

/-! ### The affineness of a space over a thickening of its base -/

/-- **An algebraic space over an object of the site, affine over a thickening of it, is affine.**
Let `i : T₀ ⟶ T` be a morphism of the site whose underlying morphism of schemes is a thickening
and let `p : V ⟶ h_T` be a morphism from an algebraic space. If the base change of `p` along
`h_i` is affine, then so is `V`: that base change is a closed subspace of `V` with all its
points. -/
private theorem isAffineSpace_of_isThickening_of_isAffineSpace_pullback'
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    {T₀ T : BigFppfOver B S hS} (i : T₀ ⟶ T)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    (p : V ⟶ yoneda.obj T) (h₀ : Space.IsAffineSpace B S hS (pullback p (yoneda.map i))) :
    Space.IsAffineSpace B S hS V := by
  let q := pullback.fst p (yoneda.map i)
  have hsq : IsPullback q (pullback.snd p (yoneda.map i)) p (yoneda.map i) :=
    IsPullback.of_hasPullback _ _
  have hcl : Space.IsClosedImmersion B S hS q :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip
      (MorphismProperty.relative_map (F := yoneda) hi.1)
  have hsurj₀ : Function.Surjective
      (Space.pointsMap B S hS (yoneda.obj T₀) (yoneda.map i)) :=
    Space.isSurjective_of_presheafSurjective B S hS (yoneda.map i)
      (MorphismProperty.relative_map (F := yoneda) (P := MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) ⟨hi.2⟩)
  exact Space.isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS q h₀.isAlgebraicSpace hV
    hcl (Space.surjective_pointsMap_of_isPullback B S hS hsq.flip hsurj₀) h₀

/-! ### Transporting the charts of a stage -/

/-- The stage maps of a directed presentation of an affine formal algebraic space by affine
objects along thickenings are representable thickenings of presheaves. -/
theorem isRepresentableThickeningULift_colimitι_comp_inv {I : Type (u + 1)} [Preorder I]
    [Nonempty I] [IsDirected I (· ≤ ·)] (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    {Y : FppfSheaf B S hS} (e : Y ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) (i : I) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv).hom := by
  let J := BigFppfOver.topology B S hS
  let Fy := Sheaf.sheafifiedYoneda J
  let Pr := sheafToPresheaf J (Type (u + 1))
  let ee := sheafifiedYonedaCompForgetIso B S hS
  have h := isThickening_colimitι B S hS D hD Y e.symm i
  refine MorphismProperty.relative.of_exists fun a g ↦ ?_
  let g' : Fy.obj a ⟶ Y := ⟨(ee.app a).hom ≫ g⟩
  obtain ⟨b, snd, fst, sq⟩ := h.rep g'
  refine ⟨b, (ee.app b).inv ≫ fst.hom, snd, ?_, h.property g' fst snd sq⟩
  exact (sq.map Pr).of_iso (ee.app b) (Iso.refl _) (ee.app a) (Iso.refl _)
    (by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Iso.refl_hom, Category.comp_id]
      rfl)
    (ee.hom.naturality snd)
    (by
      simp
      rfl)
    rfl

/-- The base change of a morphism representable by algebraic spaces along a morphism from a
represented sheaf is an algebraic space. -/
theorem isAlgebraicSpaceULift_pullback_of_isRepresentableByAlgebraicSpacesULift
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    {T : BigFppfOver B S hS}
    (v : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback v f).obj := by
  let ee := sheafifiedYonedaCompForgetIso B S hS
  let ξ : uliftYoneda.{u + 1}.obj T ⟶ Y.obj := (ee.inv.app T) ≫ v.hom
  have h0 : IsPullback (pullback.fst v f).hom (pullback.snd v f).hom v.hom f.hom :=
    (IsPullback.of_hasPullback v f).map (sheafToPresheaf _ (Type (u + 1)))
  have hbot : IsPullback v.hom (ee.hom.app T) (𝟙 Y.obj) ξ :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Iso.hom_inv_id_app_assoc]⟩
  have hv := h0.flip.paste_vert hbot
  rw [Category.comp_id] at hv
  exact Space.isAlgebraicSpaceULift_of_iso B S hS hv.flip.isoPullback.symm (hf T ξ)

/-- **The transported charts cover.** Let `ι : X₀ ⟶ X` be a representable thickening, `a` a
surjective atlas of `X₀` by an object `U` of the site, and `πₖ : Wₖ ⟶ X` étale morphisms whose
base changes along `ι` are the restrictions of `a` to the affine opens of `U`; then the `Wₖ`
cover `X`. -/
theorem isLocallySurjective_sigmaDesc_of_isPullback_affineOpens
    {X₀ X : FppfSheaf B S hS} (ι : X₀ ⟶ X)
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom)
    {U : BigFppfOver B S hS} (a : uliftYoneda.{u + 1}.obj U ⟶ X₀.obj)
    (ha : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} a)
    {Uk : ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).affineOpens → BigFppfOver B S hS}
    (uk : ∀ k, Uk k ⟶ U)
    (huk : ∀ k, Set.range ((BigFppfOver.toScheme B S hS).map (uk k)) = (k.down.1 : Set _))
    (c : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (Uk k) ⟶ X₀)
    (hc : ∀ k, (c k).hom = ((sheafifiedYonedaCompForgetIso B S hS).app (Uk k)).hom ≫
      uliftYoneda.{u + 1}.map (uk k) ≫ a)
    {W : ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).affineOpens → FppfSheaf B S hS}
    (π : ∀ k, W k ⟶ X)
    (j : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (Uk k) ⟶ W k)
    (hπ : ∀ k, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (π k).hom)
    (hsq : ∀ k, IsPullback (j k) (c k) (π k) ι) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc π) := by
  refine isLocallySurjective_sigmaDesc_of_forall_mem_range B S hS π fun T ξ x ↦ ?_
  let y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let ee := sheafifiedYonedaCompForgetIso B S hS
  let F := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan F :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨T₀, i₀, fst₀, hsq₀⟩ := hι.rep ξ
  obtain ⟨x₀, rfl⟩ := (hι.property ξ fst₀ i₀ hsq₀).2 x
  obtain ⟨A₀, q, g₁, hsq₁⟩ := ha.rep fst₀
  obtain ⟨x₁, rfl⟩ := (ha.property fst₀ g₁ q hsq₁).surj x₀
  let g₁' : A₀ ⟶ U := (ULiftYoneda.fullyFaithful.{u + 1} (C := BigFppfOver B S hS)).preimage g₁
  have hg₁' : y.map g₁' = g₁ := Functor.FullyFaithful.map_preimage _ _
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (F.obj U).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (F.map g₁' x₁))
      isOpen_univ
  let k : ULift.{u + 1} (F.obj U).affineOpens := ⟨⟨V, hV⟩⟩
  obtain ⟨v, hv⟩ : F.map g₁' x₁ ∈ Set.range (F.map (uk k)) := by rwa [huk k]
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x₁ v hv.symm
  let A₁ := pullback g₁' (uk k)
  let x₂ := (PreservesPullback.iso F g₁' (uk k)).inv z
  have hx₂ : F.map (pullback.fst g₁' (uk k)) x₂ = x₁ := by
    rw [← hz₁, ← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst]
  let t : A₁ ⟶ T := pullback.fst g₁' (uk k) ≫ q ≫ i₀
  let h : y.obj A₁ ⟶ (W k).obj :=
    y.map (pullback.snd g₁' (uk k)) ≫ (ee.app (Uk k)).inv ≫ (j k).hom
  have hh : h ≫ (π k).hom = y.map t ≫ ξ := by
    have h₁ : (j k).hom ≫ (π k).hom = (c k).hom ≫ ι.hom :=
      congrArg (fun φ ↦ φ.hom) (hsq k).w
    have h₄ : pullback.snd g₁' (uk k) ≫ uk k = pullback.fst g₁' (uk k) ≫ g₁' :=
      pullback.condition.symm
    have hck : (c k).hom = (ee.app (Uk k)).hom ≫ y.map (uk k) ≫ a := hc k
    simp only [h, t, Category.assoc, h₁, hck, Iso.inv_hom_id_assoc, Functor.map_comp]
    rw [← Functor.map_comp_assoc, h₄, Functor.map_comp_assoc, hg₁', reassoc_of% hsq₁.w, hsq₀.w]
  obtain ⟨P, p, r, hsqP⟩ := (hπ k).rep ξ
  let m : A₁ ⟶ P := (ULiftYoneda.fullyFaithful.{u + 1} (C := BigFppfOver B S hS)).preimage
    (hsqP.lift h (y.map t) hh)
  have hm : m ≫ p = t :=
    (ULiftYoneda.fullyFaithful.{u + 1} (C := BigFppfOver B S hS)).map_injective (by
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage]
      exact hsqP.lift_snd _ _ _)
  refine ⟨k, P, p, r, hsqP.w, (hπ k).property ξ r p hsqP, F.map m x₂, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← F.map_comp, hm]
  simp only [t, F.map_comp, Scheme.Hom.comp_apply, hx₂]
  rfl

/-- **Affine étale charts transported along a representable thickening.** If `ι : X₀ ⟶ X` is a
representable thickening from an algebraic space, then `X` is covered by étale morphisms
`πₖ : Wₖ ⟶ X`, representable by objects of the site, whose base changes along `ι` are
represented by affine objects of the site. -/
theorem exists_etale_cover_of_isRepresentableThickeningULift
    {X₀ X : FppfSheaf B S hS} (ι : X₀ ⟶ X)
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom)
    (hX₀ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X₀.obj) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (K : Type (u + 1)) (U : K → BigFppfOver B S hS) (W : K → FppfSheaf B S hS)
      (π : ∀ k, W k ⟶ X)
      (j : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (U k) ⟶ W k)
      (c : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (U k) ⟶ X₀),
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (U k))) ∧
      (∀ k, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (π k).hom) ∧
      (∀ k, IsPullback (j k) (c k) (π k) ι) ∧ Sheaf.IsLocallySurjective (Sigma.desc π) := by
  let y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let ee := sheafifiedYonedaCompForgetIso B S hS
  obtain ⟨U, a, ha_surj, ha_et⟩ := hX₀.exists_atlas
  let Kx := ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).affineOpens
  choose Uk uk huk_open huk_range huk_aff using
    fun k : Kx ↦ BigFppfOver.exists_affineOpen_restrict B S hS U k.down
  let Pet := MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let c : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (Uk k) ⟶ X₀ :=
    fun k ↦ ⟨(ee.app (Uk k)).hom ≫ y.map (uk k) ≫ a⟩
  have hc : ∀ k, Pet.relative y (c k).hom := fun k ↦ by
    have h₁ : Pet.relative y (y.map (uk k)) :=
      MorphismProperty.relative_map (F := y) (P := Pet) (by
        have := huk_open k
        change Etale ((BigFppfOver.toScheme B S hS).map (uk k))
        infer_instance)
    exact MorphismProperty.RespectsIso.precomp _ (ee.app (Uk k)).hom _
      (MorphismProperty.comp_mem _ _ _ h₁ ha_et)
  choose W π j hπ hsq using fun k ↦
    exists_etale_isPullback_of_isRepresentableThickeningULift B S hS ι (c k) hι (hc k)
  exact ⟨Kx, Uk, W, π, j, c, huk_aff, hπ, hsq,
    isLocallySurjective_sigmaDesc_of_isPullback_affineOpens B S hS ι hι a ha_surj uk huk_range c
      (fun _ ↦ rfl) π j hπ hsq⟩

/-! ### The stages of a transported chart -/

/-- The indices above a fixed one in a directed preorder form a directed preorder. -/
theorem isDirected_subtype_le {Λ : Type*} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (l₀ : Λ) :
    IsDirected {μ : Λ // l₀ ≤ μ} (· ≤ ·) :=
  ⟨fun a b ↦ by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, le_trans a.2 hac⟩, hac, hbc⟩⟩

/-- The restriction of a colimit cocone of fppf sheaves over a directed preorder to the indices
above a fixed one is a universal colimit. -/
theorem isUniversalColimit_whisker_subtype_le {Λ : Type (u + 1)} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] {G : Λ ⥤ FppfSheaf B S hS} {t : Cocone G} (ht : IsColimit t)
    (l₀ : Λ) :
    IsUniversalColimit (t.whisker (Subtype.mono_coe (fun x : Λ ↦ l₀ ≤ x)).functor) := by
  let incl : {μ : Λ // l₀ ≤ μ} ⥤ Λ := (Subtype.mono_coe (fun x : Λ ↦ l₀ ≤ x)).functor
  have : Nonempty {μ : Λ // l₀ ≤ μ} := ⟨⟨l₀, le_refl l₀⟩⟩
  have := isDirected_subtype_le l₀
  have : incl.Final := by
    refine Functor.final_of_exists_of_isFiltered incl (fun d ↦ ?_) (fun {_ c} s s' ↦ ?_)
    · obtain ⟨c, hdc, hlc⟩ := exists_ge_ge d l₀
      exact ⟨⟨c, hlc⟩, ⟨homOfLE hdc⟩⟩
    · exact ⟨c, 𝟙 c, by subsingleton⟩
  exact (sheaf_filteredColimit_isUniversalColimit (BigFppfOver.topology B S hS) (incl ⋙ G)).of_iso
    ((colimit.isColimit (incl ⋙ G)).uniqueUpToIso
      ((Functor.Final.isColimitWhiskerEquiv incl t).symm ht))

/-- A sheaf representable by algebraic spaces over the point of a universal directed colimit of
fppf sheaves along representable thickenings, whose base changes to the stages are represented
by affine objects of the site, is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_of_isUniversalColimit_of_stages {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {E : I ⥤ FppfSheaf B S hS} {c : Cocone E}
    (hc : IsUniversalColimit c)
    (hE : ∀ ⦃i j : I⦄ (h : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map h).hom)
    (hY : IsAffineFormalAlgebraicSpace B S hS c.pt) {W : FppfSheaf B S hS} (g : W ⟶ c.pt)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hstage : ∀ i, ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty ((c.pullbackDiagram g).obj i ≅
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T)) :
    IsAffineFormalAlgebraicSpace B S hS W :=
  isAffineFormalAlgebraicSpace_of_isColimit_of_isAffine_stages B S hS I (c.pullbackDiagram g)
    hstage
    (fun _ _ h ↦ (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      ((c.isPullback_pullbackDiagram_map g h).flip.map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) (hE h))
    (c.pullbackCocone g) (IsUniversalColimit.nonempty_isColimit_pullbackCocone hc g).some
    (satisfiesSetTheoreticCondition_of_representable_over_affineFormal B S hS g hY hg)

private theorem isAffineFormalAlgebraicSpace_of_isPullback_stage
    (Q : ∀ {Z : FppfSheaf B S hS} {T : BigFppfOver B S hS},
      (Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T) → Prop)
    (haffine : ∀ {T₀ T : BigFppfOver B S hS} (i : T₀ ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      ∀ {Z : FppfSheaf B S hS}
        (z : Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T),
      Q z → ∀ {U₀ : BigFppfOver B S hS}, IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) →
      (pullback z ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i) ≅
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U₀) →
      ∃ T' : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T') ∧
        Nonempty (Z ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T'))
    {Λ : Type (u + 1)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ BigAffineFppf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (eY : Y ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) (l₀ : Λ)
    {W : FppfSheaf B S hS} (π : W ⟶ X) (hπ : IsRepresentableEtale B S hS π)
    (hQ : ∀ {T : BigFppfOver B S hS}
      (v : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y),
      Q (pullback.fst v (π ≫ f)))
    {U₀ : BigFppfOver B S hS} (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (j : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U₀ ⟶ W)
    (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U₀ ⟶
      pullback (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) l₀ ≫ eY.inv) f)
    (hsq : IsPullback j c π (pullback.snd (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) l₀ ≫ eY.inv) f)) :
    IsAffineFormalAlgebraicSpace B S hS W := by
  let K := BigAffineFppf.inclusion B S hS
  let G : Λ ⥤ FppfSheaf B S hS := D ⋙ K ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let gi (μ : Λ) : G.obj μ ⟶ Y := colimit.ι G μ ≫ eY.inv
  have hgi {μ ν : Λ} (g : μ ⟶ ν) : G.map g ≫ gi ν = gi μ := colimit.w_assoc G g eY.inv
  let Λ' := {μ : Λ // l₀ ≤ μ}
  have : Nonempty Λ' := ⟨⟨l₀, le_refl l₀⟩⟩
  have : IsDirected Λ' (· ≤ ·) := isDirected_subtype_le l₀
  let incl : Λ' ⥤ Λ := (Subtype.mono_coe (fun x : Λ ↦ l₀ ≤ x)).functor
  let cY₀ : Cocone G :=
    { pt := Y, ι := { app := gi, naturality := fun μ ν g ↦ by simpa using hgi g } }
  have hcY₀ : IsColimit cY₀ :=
    IsColimit.ofIsoColimit (colimit.isColimit G) (Cocone.ext eY.symm (fun _ ↦ rfl))
  let g := π ≫ f
  refine isAffineFormalAlgebraicSpace_of_isUniversalColimit_of_stages B S hS
    (isUniversalColimit_whisker_subtype_le B S hS hcY₀ l₀)
    (fun _ _ h ↦ isRepresentableThickeningULift_sheafifiedYoneda_map B S hS
      (K.map (D.map (incl.map h))) (hthick _)) hY g
    (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS π.hom f.hom hπ.1 hf) fun μ ↦ ?_
  let h : l₀ ⟶ μ.1 := homOfLE μ.2
  let fst₀ := pullback.fst (gi l₀) f
  have S₁₂ : IsPullback j (c ≫ fst₀) g (gi l₀) :=
    hsq.paste_vert (IsPullback.of_hasPullback (gi l₀) f).flip
  have hw : ((c ≫ fst₀) ≫ G.map h) ≫ gi μ.1 = j ≫ g := by
    rw [Category.assoc, hgi h, ← S₁₂.w]
  let ℓ := pullback.lift ((c ≫ fst₀) ≫ G.map h) j hw
  have hout : IsPullback (c ≫ fst₀) (ℓ ≫ pullback.snd (gi μ.1) g) (G.map h ≫ gi μ.1) g := by
    rw [pullback.lift_snd, hgi h]
    exact S₁₂.flip
  have htop := IsPullback.of_bot hout (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback (gi μ.1) g)
  exact haffine (K.map (D.map h)) (D.obj μ.1).property (hthick h) (pullback.fst (gi μ.1) g)
    (hQ (gi μ.1)) hU₀ htop.flip.isoPullback.symm

/-- The proof of Stacks 0AJH, with the affineness of the stages of the transported charts as
an input: for a morphism `f : X ⟶ Y` to an affine formal algebraic space, representable by
algebraic spaces, `X` is a formal algebraic space as soon as a sheaf over an affine object of
the site, of the kind `Q` that the base changes of the transported charts are, is affine when
its base change to a thickening is. -/
private theorem isFormalAlgebraicSpace_of_affine_stages
    (Q : ∀ {Z : FppfSheaf B S hS} {T : BigFppfOver B S hS},
      (Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T) → Prop)
    (haffine : ∀ {T₀ T : BigFppfOver B S hS} (i : T₀ ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      ∀ {Z : FppfSheaf B S hS}
        (z : Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T),
      Q z → ∀ {U₀ : BigFppfOver B S hS}, IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) →
      (pullback z ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i) ≅
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U₀) →
      ∃ T' : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T') ∧
        Nonempty (Z ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T'))
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hQ : ∀ {W : FppfSheaf B S hS} (π : W ⟶ X), IsRepresentableEtale B S hS π →
      ∀ {T : BigFppfOver B S hS}
        (v : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Y),
      Q (pullback.fst v (π ≫ f))) :
    IsFormalAlgebraicSpace B S hS X := by
  classical
  obtain ⟨-, Λ, pre, hne, hdir, D, hthick, ⟨eY⟩⟩ := id hY
  let : Preorder Λ := pre
  have : IsDirected Λ (· ≤ ·) := hdir
  have : Nonempty Λ := hne
  obtain ⟨l₀⟩ := hne
  let J := BigFppfOver.topology B S hS
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let K := BigAffineFppf.inclusion B S hS
  let G : Λ ⥤ FppfSheaf B S hS := D ⋙ K ⋙ Sheaf.sheafifiedYoneda J
  let gi (μ : Λ) : G.obj μ ⟶ Y := colimit.ι G μ ≫ eY.inv
  -- the thickening `X₀ ⟶ X` over the stage `l₀`
  let ι : pullback (gi l₀) f ⟶ X := pullback.snd (gi l₀) f
  have hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      ((IsPullback.of_hasPullback (gi l₀) f).map (sheafToPresheaf J (Type (u + 1))))
      (isRepresentableThickeningULift_colimitι_comp_inv B S hS D hthick eY l₀)
  obtain ⟨Kx, Uk, W, π, j, c, hUk, hπ, hsq, hcov⟩ :=
    exists_etale_cover_of_isRepresentableThickeningULift B S hS ι hι
      (isAlgebraicSpaceULift_pullback_of_isRepresentableByAlgebraicSpacesULift B S hS f hf
        (T := K.obj (D.obj l₀)) (gi l₀))
  have hπ' : ∀ k, IsRepresentableEtale B S hS (π k) :=
    fun k ↦ isRepresentableEtale_of_relative_etale B S hS (π k) (hπ k)
  exact ⟨satisfiesSetTheoreticCondition_of_representable_over_affineFormal B S hS f hY hf, Kx, W,
    π, fun k ↦ isAffineFormalAlgebraicSpace_of_isPullback_stage B S hS Q haffine D hthick f hY hf
      eY l₀ (π k) (hπ' k) (hQ (π k) (hπ' k)) (hUk k) (j k) (c k) (hsq k), hπ', hcov⟩

/-- **Stacks 0AJH for an étale morphism.** Let `Y` be an affine formal algebraic space over `S`
and let `f : X ⟶ Y` be a morphism of fppf sheaves which is representable by algebraic spaces
and étale. Then `X` is a formal algebraic space over `S`. -/
theorem isFormalAlgebraicSpace_of_isRepresentableEtale_over_affineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : IsRepresentableEtale B S hS f) : IsFormalAlgebraicSpace B S hS X :=
  isFormalAlgebraicSpace_of_affine_stages B S hS (fun z ↦ IsRepresentableEtale B S hS z)
    (fun i _ hi _ z hz _ hU₀ e₀ ↦
      exists_affine_iso_of_isRepresentableEtale_of_isThickening B S hS i hi z hz hU₀ e₀)
    f hY hf.1 (fun _ hπ _ v ↦
      isRepresentableEtale_pullback_fst B S hS v _ (IsRepresentableEtale.comp B S hS hπ hf))

/-- **Stacks 0AJH.** Let `S` be a scheme, let `Y` be an affine formal algebraic space over `S`,
and let `f : X ⟶ Y` be a morphism of sheaves on the big fppf site of `S` which is representable
by algebraic spaces. Then `X` is a formal algebraic space over `S`.

The affine étale charts of one stage `X₀ = Y₀ ×_Y X` are transported to `X` along the
representable thickening `X₀ ⟶ X`; the stages of a transported chart over the stages `Y_μ` of
`Y` are algebraic spaces over the affine `Y_μ` whose base change to `Y₀` is affine, hence affine
by the thickening case of Stacks 07VT
(`AlgebraicGeometry.Space.isAffineSpace_of_isClosedSubspace_of_isSurjective_terminal`), so each
transported chart is an affine formal algebraic space, and the charts cover `X`. -/
@[stacks 0AJH "the full statement, with no hypothesis beyond the source's: the set-theoretic \
condition of Stacks 0AIS on the source is proved, not assumed"]
theorem isFormalAlgebraicSpace_of_representable_over_isAffineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsFormalAlgebraicSpace B S hS X :=
  isFormalAlgebraicSpace_of_affine_stages B S hS
    (fun z ↦ Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS z.hom)
    (fun i _ hi _ z hz _ hU₀ e₀ ↦ exists_affine_iso_of_isThickening_of_descent B S hS i z hz
      (fun hV p _ _ h₀ ↦ isAffineSpace_of_isThickening_of_isAffineSpace_pullback' B S hS hV i hi p
        h₀) hU₀ e₀)
    f hY hf (fun π hπ _ v ↦
      Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
        (pullback.snd v (π ≫ f)).hom (pullback.fst v (π ≫ f)).hom (π ≫ f).hom v.hom
        ((IsPullback.of_hasPullback v (π ≫ f)).flip.map
          (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))))
        (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS π.hom f.hom hπ.1 hf))

/-- **Stacks 0AJH for an étale morphism**, as the proposition
`AlgebraicGeometry.FormalSpace.RepresentableEtaleOverAffineIsFormal`. -/
theorem representableEtaleOverAffineIsFormal : RepresentableEtaleOverAffineIsFormal B S hS :=
  isFormalAlgebraicSpace_of_isRepresentableEtale_over_affineFormal B S hS

end AlgebraicGeometry.FormalSpace

end

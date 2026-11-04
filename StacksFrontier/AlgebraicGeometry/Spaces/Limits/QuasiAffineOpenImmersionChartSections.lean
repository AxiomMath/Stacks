module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineOpenImmersionSubring
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineOpenImmersionAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward

/-!
# Finitely many local sections make a quasi-affine morphism open in a space affine over the base

Let `f : Y ⟶ X` be a quasi-affine morphism of algebraic spaces which is locally of finite type,
with `X` quasi-compact.  This file proves that there are an affine surjective étale chart `U` of
`X` and finitely many sections `s` of `f_* 𝒪_Y` over `U` with the following property: for every
algebraic space `P` affine over `X` and every morphism `g : Y ⟶ P` over `X` whose map on
direct-image algebras `P_* 𝒪_P ⟶ f_* 𝒪_Y` is injective on the sections over `U` with image
containing `s`, the morphism `g` is an open immersion.

## Main results

* `AlgebraicGeometry.Space.exists_finset_isOpenImmersion_of_pushforwardRingMap_app`: the
  statement above.
* `AlgebraicGeometry.Space.exists_finset_isImmersion_of_pushforwardRingMap_app`: with no
  injectivity, `g` is an immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-compact algebraic space has an affine surjective étale chart in its small étale site. -/
private theorem exists_smallEtale_affine_surjective_etale {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ U : SmallEtale B S hS X.1, IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) U.1.hom ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) U.1.hom := by
  obtain ⟨U₀, u, hUaff, husurj, huet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).mp hXqc
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 U₀)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U₀)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have huet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u := by
    have h := huet U₀ (yoneda.map (𝟙 U₀)) hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact ⟨⟨CostructuredArrow.mk u, huet'⟩, hUaff, husurj, huet'⟩

/-- If `u : U₀ ⟶ X` is a surjective étale chart, `Y ⟶ P` is the base change of a scheme
morphism `m` (in `Q`) along a chart pullback of `P`, then the pulled-back chart is surjective
étale and the base change of `Y ⟶ P` along it is in `Q`. -/
private theorem presheaf_surjective_etale_and_snd_of_isPullback
    (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
    {Y P X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V₀ V₁ V₂ : BigFppfOver B S hS}
    {u : yoneda.obj V₀ ⟶ X} {p : P ⟶ X} {a : yoneda.obj V₂ ⟶ P} {b : V₂ ⟶ V₀}
    {g : Y ⟶ P} {c : yoneda.obj V₁ ⟶ Y} {m : V₁ ⟶ V₂}
    (hq : IsPullback a (yoneda.map b) p u)
    (husurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) u)
    (huet : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) u)
    (hsq : IsPullback c (yoneda.map m) g a)
    (hm : Q ((BigFppfOver.toScheme B S hS).map m)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS))) (pullback.snd g a) := by
  have key : ∀ (R : MorphismProperty Scheme.{u}) [R.IsStableUnderBaseChange],
      (MorphismProperty.presheaf (MorphismProperty.inverseImage R
        (BigFppfOver.toScheme B S hS))) u →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage R
        (BigFppfOver.toScheme B S hS))) a := fun R _ hu ↦ by
    have := inverseImage_isStableUnderBaseChange B S hS (P := R) inferInstance
    have := MorphismProperty.relative_isStableUnderBaseChange
      (F := yoneda) (MorphismProperty.inverseImage R (BigFppfOver.toScheme B S hS))
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hq.flip hu
  refine ⟨key _ husurj, key _ huet, ?_⟩
  have := inverseImage_isStableUnderBaseChange B S hS (P := Q) inferInstance
  rw [← hsq.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp _ hsq.isoPullback.inv _
    (MorphismProperty.relative_map hm)

/-- If `σY.inv` maps `s` into the range of `ρ` and `σZ.inv ≫ ρ ≫ σY.hom = φ`, then `s` lies in the
range of `φ`. -/
private theorem subset_range_of_image_inv_subset_range {R₁ R₂ R₃ R₄ : CommRingCat.{u}}
    [DecidableEq R₁] (σY : R₁ ≅ R₂) (σZ : R₃ ≅ R₄) (ρ : R₃ ⟶ R₁) (φ : R₄ ⟶ R₂)
    (heq : σZ.inv ≫ ρ ≫ σY.hom = φ) {s : Finset R₂}
    (hrange : (s.image σY.inv : Set R₁) ⊆ Set.range ρ) : (s : Set R₂) ⊆ Set.range φ := by
  intro t ht
  obtain ⟨a, ha⟩ := hrange (Finset.mem_coe.2 (Finset.mem_image_of_mem σY.inv ht))
  refine ⟨σZ.hom a, ?_⟩
  rw [← heq]
  change σY.hom (ρ (σZ.inv (σZ.hom a))) = t
  rw [Iso.hom_inv_id_apply, ha, Iso.inv_hom_id_apply]

/-- Let `f : Y ⟶ X` be quasi-affine and locally of finite type, `X` quasi-compact.  There are an
étale chart `U` of `X` and a finite set `s` of sections of `f_* 𝒪_Y` over `U` such that every
morphism `g : Y ⟶ P` over `X` into an algebraic space `P` affine over `X`, whose map of
direct-image rings at `U` is injective with image containing `s`, is an open immersion. -/
theorem exists_finset_isOpenImmersion_of_pushforwardRingMap_app {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hfqa : IsQuasiAffineHom B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f.hom) (hXqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ (U : SmallEtale B S hS X.1)
      (s : Finset ((pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op U))),
      ∀ (P : AffineOver B S hS X) (g : Over.mk f ⟶ P.obj),
        Function.Injective ((pushforwardRingMap B S hS g).hom.app (op U)) →
        (s : Set _) ⊆ Set.range ((pushforwardRingMap B S hS g).hom.app (op U)) →
        IsOpenImmersion B S hS g.left.hom := by
  classical
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, hUaff, husurj, huet'⟩ := exists_smallEtale_affine_surjective_etale B S hS hXqc
  have hfpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f.hom :=
    ((isQuasiAffineHom_tfae_of_isAlgebraicSpace Y.2 X.2 f.hom).out 2 1).mp hfqa
  have hY : yoneda.relativelyRepresentable (Over.mk f).hom.hom := hfpre.rep
  have hftpre := (holdsOnEveryEtaleChart_iff_relative B S hS
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget Y.2 X.2 f.hom hY).1 hft
  let π := T.map (hY.snd U.1.hom)
  have : IsAffine (T.obj U.1.left) := hUaff
  have hπqa : _root_.AlgebraicGeometry.IsQuasiAffineHom π :=
    hfpre.property U.1.hom (hY.fst U.1.hom) (hY.snd U.1.hom) (hY.isPullback U.1.hom)
  have : (T.obj (hY.pullback U.1.hom)).IsQuasiAffine :=
    (isQuasiAffineHom_iff_isQuasiAffine π).1 hπqa
  have : LocallyOfFiniteType π :=
    hftpre.property U.1.hom (hY.fst U.1.hom) (hY.snd U.1.hom) (hY.isPullback U.1.hom)
  obtain ⟨s₀, hs₀⟩ := exists_finset_isOpenImmersion_of_injective_appTop π
  let σY := pushforwardAlgebraSectionsIso B S hS (Over.mk f) hY U
  refine ⟨U, s₀.image σY.inv, fun P g hinj hrange => ?_⟩
  have hfac : g.left.hom ≫ P.obj.hom.hom = f.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Y ⟶ X => m.hom) (Over.w g)
  have hpaff := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS P.obj.hom.hom
    P.obj.left.2 X.2).out 2 1).mp P.property
  have hZ : yoneda.relativelyRepresentable P.obj.hom.hom := hpaff.2.rep
  let σZ := pushforwardAlgebraSectionsIso B S hS P.obj hZ U
  let m := smallBaseChangeOverMap B S hS g hY hZ U
  have heq := pushforwardRingMap_app_eq B S hS g hY hZ U
  have hqaff : _root_.AlgebraicGeometry.IsAffineHom (T.map (hZ.snd U.1.hom)) :=
    hpaff.2.property U.1.hom (hZ.fst U.1.hom) (hZ.snd U.1.hom) (hZ.isPullback U.1.hom)
  have hPUaff : IsAffine (T.obj (hZ.pullback U.1.hom)) :=
    @isAffine_of_isAffineHom _ _ (T.map (hZ.snd U.1.hom)) hqaff hUaff
  set ρ := (pushforwardRingMap B S hS g).hom.app (op U)
  have hinj' : Function.Injective (T.map m).appTop := by
    intro a b hab
    rw [← heq] at hab
    simp only [CommRingCat.comp_apply] at hab
    exact (ConcreteCategory.bijective_of_isIso σZ.inv).1
      (hinj ((ConcreteCategory.bijective_of_isIso σY.hom).1 hab))
  have hrange' : (s₀ : Set _) ⊆ Set.range (T.map m).appTop :=
    subset_range_of_image_inv_subset_range σY σZ _ _ heq hrange
  have hm : _root_.AlgebraicGeometry.IsOpenImmersion (T.map m) :=
    hs₀ (T.map (hZ.snd U.1.hom)) (T.map m)
      (by rw [← Functor.map_comp, smallBaseChangeOverMap_snd]) hinj' hrange'
  have hsq : IsPullback (hY.fst U.1.hom) (yoneda.map m) g.left.hom (hZ.fst U.1.hom) := by
    refine IsPullback.of_bot ?_ (yoneda_map_smallBaseChangeOverMap_fst B S hS g hY hZ U).symm
      (hZ.isPullback U.1.hom)
    rw [← Functor.map_comp, smallBaseChangeOverMap_snd, hfac]
    exact hY.isPullback U.1.hom
  apply ((isOpenImmersion_tfae_of_isAlgebraicSpace Y.2
    P.obj.left.2 g.left.hom).out 4 1).mp
  exact ⟨hZ.pullback U.1.hom, hZ.fst U.1.hom,
    presheaf_surjective_etale_and_snd_of_isPullback B S hS _ (hZ.isPullback U.1.hom) husurj huet'
      hsq hm⟩

/-- Let `f : Y ⟶ X` be quasi-affine and locally of finite type, `X` quasi-compact.  There are an
étale chart `U` of `X` and a finite set `s` of sections of `f_* 𝒪_Y` over `U` such that every
morphism `g : Y ⟶ P` over `X` into an algebraic space `P` affine over `X`, whose map of
direct-image rings at `U` has image containing `s`, is an immersion. -/
theorem exists_finset_isImmersion_of_pushforwardRingMap_app {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hfqa : IsQuasiAffineHom B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f.hom) (hXqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ (U : SmallEtale B S hS X.1), IsAffine (chartScheme U) ∧
      ∃ (s : Finset ((pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op U))),
      ∀ (P : AffineOver B S hS X) (g : Over.mk f ⟶ P.obj),
        (s : Set _) ⊆ Set.range ((pushforwardRingMap B S hS g).hom.app (op U)) →
        IsImmersion B S hS g.left.hom := by
  classical
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, hUaff, husurj, huet'⟩ := exists_smallEtale_affine_surjective_etale B S hS hXqc
  have hfpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f.hom :=
    ((isQuasiAffineHom_tfae_of_isAlgebraicSpace Y.2 X.2 f.hom).out 2 1).mp hfqa
  have hY : yoneda.relativelyRepresentable (Over.mk f).hom.hom := hfpre.rep
  have hftpre := (holdsOnEveryEtaleChart_iff_relative B S hS
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget Y.2 X.2 f.hom hY).1 hft
  let π := T.map (hY.snd U.1.hom)
  have : IsAffine (T.obj U.1.left) := hUaff
  have hπqa : _root_.AlgebraicGeometry.IsQuasiAffineHom π :=
    hfpre.property U.1.hom (hY.fst U.1.hom) (hY.snd U.1.hom) (hY.isPullback U.1.hom)
  have : (T.obj (hY.pullback U.1.hom)).IsQuasiAffine :=
    (isQuasiAffineHom_iff_isQuasiAffine π).1 hπqa
  have : LocallyOfFiniteType π :=
    hftpre.property U.1.hom (hY.fst U.1.hom) (hY.snd U.1.hom) (hY.isPullback U.1.hom)
  obtain ⟨s₀, hs₀⟩ := exists_finset_isImmersion_of_range_appTop π
  let σY := pushforwardAlgebraSectionsIso B S hS (Over.mk f) hY U
  refine ⟨U, hUaff, s₀.image σY.inv, fun P g hrange => ?_⟩
  have hfac : g.left.hom ≫ P.obj.hom.hom = f.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Y ⟶ X => m.hom) (Over.w g)
  have hpaff := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS P.obj.hom.hom
    P.obj.left.2 X.2).out 2 1).mp P.property
  have hZ : yoneda.relativelyRepresentable P.obj.hom.hom := hpaff.2.rep
  let σZ := pushforwardAlgebraSectionsIso B S hS P.obj hZ U
  let m := smallBaseChangeOverMap B S hS g hY hZ U
  have heq := pushforwardRingMap_app_eq B S hS g hY hZ U
  have hqaff : _root_.AlgebraicGeometry.IsAffineHom (T.map (hZ.snd U.1.hom)) :=
    hpaff.2.property U.1.hom (hZ.fst U.1.hom) (hZ.snd U.1.hom) (hZ.isPullback U.1.hom)
  have hPUaff : IsAffine (T.obj (hZ.pullback U.1.hom)) :=
    @isAffine_of_isAffineHom _ _ (T.map (hZ.snd U.1.hom)) hqaff hUaff
  set ρ := (pushforwardRingMap B S hS g).hom.app (op U)
  have hrange' : (s₀ : Set _) ⊆ Set.range (T.map m).appTop :=
    subset_range_of_image_inv_subset_range σY σZ _ _ heq hrange
  have hm : _root_.AlgebraicGeometry.IsImmersion (T.map m) :=
    hs₀ (T.map (hZ.snd U.1.hom)) (T.map m)
      (by rw [← Functor.map_comp, smallBaseChangeOverMap_snd]) hrange'
  have hsq : IsPullback (hY.fst U.1.hom) (yoneda.map m) g.left.hom (hZ.fst U.1.hom) := by
    refine IsPullback.of_bot ?_ (yoneda_map_smallBaseChangeOverMap_fst B S hS g hY hZ U).symm
      (hZ.isPullback U.1.hom)
    rw [← Functor.map_comp, smallBaseChangeOverMap_snd, hfac]
    exact hY.isPullback U.1.hom
  apply ((isImmersion_tfae_of_isAlgebraicSpace Y.2
    P.obj.left.2 g.left.hom).out 4 1).mp
  exact ⟨hZ.pullback U.1.hom, hZ.fst U.1.hom,
    presheaf_surjective_etale_and_snd_of_isPullback B S hS _ (hZ.isPullback U.1.hom) husurj huet'
      hsq hm⟩

end AlgebraicGeometry.Space

end

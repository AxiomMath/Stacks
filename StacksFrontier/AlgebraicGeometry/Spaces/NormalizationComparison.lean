module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Comparing the normalization of an algebraic space with that of a scheme

Let `F` be an algebraic space over `S` equipped with normalization data
`AlgebraicGeometry.Space.NormalizationData`, that is, with a morphism `ν : F^ν ⟶ F` of
algebraic spaces whose base change along every surjective étale scheme chart of `F` is the
normalization of that chart. When `F` is representable, `F^ν` is representable and `ν` is the
normalization morphism of the representing scheme. Over an arbitrary surjective étale chart the
base change of `ν` is an integral morphism of algebraic spaces, and for a representable `F` the
morphism `ν` itself is integral.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.exists_iso_yoneda_normalizationScheme`: for a
  representable algebraic space the normalization is represented by the normalization scheme
  of the representing scheme, compatibly with the two normalization morphisms.
* `AlgebraicGeometry.Space.NormalizationData.isIntegralHom_pullback_snd`: the base change of
  the normalization morphism along a surjective étale scheme chart is an integral morphism of
  algebraic spaces.
* `AlgebraicGeometry.Space.NormalizationData.isIntegralHom_of_representable`: for a
  representable algebraic space the normalization morphism itself is integral.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

namespace NormalizationData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphisms of the big fppf site of `S` whose underlying morphism of schemes is integral. -/
private abbrev integralOnSite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is integral is
representable with integral represented base changes, as a morphism of the presheaves it
represents. -/
private theorem relative_integralOnSite_yoneda_map
    {Xν X : BigFppfOver B S hS} (p : Xν ⟶ X)
    (hp : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map p)) :
    (integralOnSite B S hS).relative yoneda (yoneda.map p) := by
  let _ : (integralOnSite B S hS).IsStableUnderBaseChange := ⟨by
    intro A C C' Z a b a' b' hsq hb
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsIntegralHom)
      (hsq.map (BigFppfOver.toScheme B S hS)) hb⟩
  exact MorphismProperty.relative_map hp

/-- A morphism of algebraic spaces over `S` whose represented base changes are integral on the
underlying schemes is an integral morphism of algebraic spaces. -/
private theorem isIntegralHom_of_relative_integralOnSite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : (integralOnSite B S hS).relative yoneda f) :
    IsIntegralHom B S hS f :=
  (isIntegralHom_iff_representable B S hS f hX hY).2 ⟨hf.1, hf⟩

/-- If a square over the identity of `yoneda.obj X` is a pullback with `g` an isomorphism, then
its right-hand map `h` is `inv g ≫ yoneda.map p`. -/
private theorem eq_inv_comp_of_isPullback_id {X Xν : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : F ⟶ yoneda.obj X) (p : Xν ⟶ X)
    (g : yoneda.obj Xν ⟶ F) [IsIso g]
    (hpb : IsPullback g (yoneda.map p) h (𝟙 (yoneda.obj X))) :
    h = inv g ≫ yoneda.map p := by
  rw [← cancel_epi g, IsIso.hom_inv_id_assoc]
  simpa only [Category.comp_id] using hpb.w

/-- Let `X` be an object of the big fppf site of `S` every
quasi-compact open of whose underlying scheme has finitely many irreducible components, and let
`D` be normalization data for the algebraic space it represents. Then `D.space` is represented
by an object `Xν` of the site whose underlying scheme is the normalization scheme of the
underlying scheme of `X`, and under that identification `D.hom` is the normalization
morphism. -/
@[stacks 07U4 "part (2): the normalization of a scheme as an algebraic space"]
theorem exists_iso_yoneda_normalizationScheme {X : BigFppfOver B S hS}
    (D : NormalizationData B S hS (yoneda.obj X))
    (hX : ∀ V : ((BigFppfOver.toScheme B S hS).obj X).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj X)) →
        (irreducibleComponents V).Finite) :
    ∃ (Xν : BigFppfOver B S hS) (p : Xν ⟶ X)
      (e : ((BigFppfOver.toScheme B S hS).obj Xν) ≅
        Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj X) hX)
      (φ : D.space ≅ yoneda.obj Xν),
      (BigFppfOver.toScheme B S hS).map p =
          e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj X) hX ∧
        φ.hom ≫ yoneda.map p = D.hom := by
  obtain ⟨hU, Xν, p, g, e, hp, hpb⟩ := D.chart_self
  have : IsIso g := hpb.isIso_fst_of_isIso
  exact ⟨Xν, p, e, (asIso g).symm, hp, (eq_inv_comp_of_isPullback_id D.hom p g hpb).symm⟩

/-- The base change of the normalization morphism of an algebraic space along a surjective
étale scheme chart is an integral morphism of algebraic spaces. -/
theorem isIntegralHom_pullback_snd {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : IsSurjective B S hS f) (hfe : IsEtale B S hS f) :
    IsIntegralHom B S hS (pullback.snd D.hom f) := by
  obtain ⟨hU, Uν, p, g, e, hp, hpb⟩ := D.chart U f hf hfe
  have hUspace : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hrelp := relative_integralOnSite_yoneda_map p (by rw [hp]; infer_instance)
  have hrelq : (integralOnSite B S hS).relative yoneda (pullback.snd D.hom f) := by
    refine (((integralOnSite B S hS).relative yoneda).cancel_left_of_respectsIso
      hpb.isoPullback.hom (pullback.snd D.hom f)).mp ?_
    rwa [hpb.isoPullback_hom_snd]
  exact isIntegralHom_of_relative_integralOnSite (pullback.snd D.hom f)
    (isAlgebraicSpace_pullback B S hS D.hom f D.isAlgebraicSpace hUspace hF) hUspace hrelq

/-- The normalization morphism of the algebraic space represented by an object of the big fppf
site of `S` is an integral morphism of algebraic spaces. -/
theorem isIntegralHom_of_representable {X : BigFppfOver B S hS}
    (D : NormalizationData B S hS (yoneda.obj X)) :
    IsIntegralHom B S hS D.hom := by
  obtain ⟨hU, Xν, p, g, e, hp, hpb⟩ := D.chart_self
  have hg : IsIso g := hpb.isIso_fst_of_isIso
  have hrelp := relative_integralOnSite_yoneda_map p (by rw [hp]; infer_instance)
  have hrel := (((integralOnSite B S hS).relative yoneda).cancel_left_of_respectsIso
    (inv g) (yoneda.map p)).mpr hrelp
  rw [eq_inv_comp_of_isPullback_id D.hom p g hpb]
  exact isIntegralHom_of_relative_integralOnSite _ D.isAlgebraicSpace
    (isAlgebraicSpace_yoneda B S hS X) hrel

end NormalizationData

end AlgebraicGeometry.Space

end

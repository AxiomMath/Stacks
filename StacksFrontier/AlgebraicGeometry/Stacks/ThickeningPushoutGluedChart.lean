module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Pushouts.ThickeningAffineAtlasOfChartLift

/-!
# Gluing scheme charts over a thickening-and-affine pushout inside the big fppf site

Let `X ⟶ X'` be a thickening and `X ⟶ Y` an affine morphism of objects of the big fppf site of
`S`, with pushout `Y'` (Stacks 07RT). Given schemes `V₁ ⟶ Y` and `U'₁ ⟶ X'` of the site whose
base changes to `X` agree, the pushout `P = V₁ ⨿_{U₁} U'₁` is again an object of the site, it
maps to `Y'`, its base changes to `Y` and to `X'` are `V₁` and `U'₁` (Stacks 07RV), and it is
smooth over `Y'` when both pieces are smooth (Stacks 07RX) and surjective over `Y'` when `V₁ ⟶ Y`
is.

This is the chart-level step of the essential surjectivity of Stacks 07WN.

## Main results

* `AlgebraicGeometry.Stack.ThickeningPushout.exists_gluedChart`: the glued chart and its
  properties.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack.ThickeningPushout

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Gluing two scheme charts over a thickening-and-affine pushout, inside the site.** Let
`i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of objects of the big fppf site
of `S` with pushout `Y'` (in schemes), and let `t : V₁ ⟶ Y` and `t' : U'₁ ⟶ X'` have a common
base change `U₁` to `X`. Then the pushout `P` of `U₁ ⟶ U'₁` and `U₁ ⟶ V₁` is an object of the site
with a morphism `q : P ⟶ Y'` restricting to `t` and `t'`, both comparison squares are cartesian,
`q` is smooth as soon as `t` and `t'` are, and surjective as soon as `t` is. -/
theorem exists_gluedChart {X X' Y Y' : BigFppfOver B S hS}
    {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    {V₁ U'₁ U₁ : BigFppfOver B S hS} {t : V₁ ⟶ Y} {t' : U'₁ ⟶ X'} {r : U₁ ⟶ X}
    {k : U₁ ⟶ U'₁} {g : U₁ ⟶ V₁}
    (hk : IsPullback ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map t') ((BigFppfOver.toScheme B S hS).map i))
    (hg : IsPullback ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map f)) :
    ∃ (P : BigFppfOver B S hS) (u₁ : U'₁ ⟶ P) (u₂ : V₁ ⟶ P) (q : P ⟶ Y'),
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map u₁) ((BigFppfOver.toScheme B S hS).map u₂) ∧
      u₁ ≫ q = t' ≫ a ∧ u₂ ≫ q = t ≫ b ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map u₁) ((BigFppfOver.toScheme B S hS).map t')
        ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map a) ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map u₂) ((BigFppfOver.toScheme B S hS).map t)
        ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map b) ∧
      (Smooth ((BigFppfOver.toScheme B S hS).map t) →
        Smooth ((BigFppfOver.toScheme B S hS).map t') →
          Smooth ((BigFppfOver.toScheme B S hS).map q)) ∧
      (Flat ((BigFppfOver.toScheme B S hS).map t) →
        Flat ((BigFppfOver.toScheme B S hS).map t') →
          Flat ((BigFppfOver.toScheme B S hS).map q)) ∧
      (Function.Surjective ((BigFppfOver.toScheme B S hS).map t) →
        Function.Surjective ((BigFppfOver.toScheme B S hS).map q)) := by
  set Φ := BigFppfOver.toScheme B S hS
  have : IsAffineHom (Φ.map g) := MorphismProperty.of_isPullback hg.flip inferInstance
  obtain ⟨P, u₁, u₂, hP⟩ := Space.C1573.exists_isPushout_toScheme_of_isThickening B S hS k g
    (Stacks.Thickenings.isThickening_of_isPullback hk hi)
  have hw : Φ.map k ≫ (Φ.map t' ≫ Φ.map a) = Φ.map g ≫ (Φ.map t ≫ Φ.map b) := by
    rw [← Category.assoc, ← Category.assoc, hk.w, hg.w, Category.assoc, Category.assoc, hpo.w]
  set φ : Φ.obj P ⟶ Φ.obj Y' := hP.desc (Φ.map t' ≫ Φ.map a) (Φ.map t ≫ Φ.map b) hw with hφ
  have hover : ∀ {A C : BigFppfOver B S hS} (x : A ⟶ C),
      B.inclusion.map x.left ≫ B.inclusion.map C.hom = B.inclusion.map A.hom := fun x ↦ by
    rw [← Functor.map_comp, Over.w x]
  have hφS : φ ≫ B.inclusion.map Y'.hom = B.inclusion.map P.hom := by
    refine hP.hom_ext ?_ ?_
    · rw [← Category.assoc, hP.inl_desc]
      exact (hover (t' ≫ a)).trans (hover u₁).symm
    · rw [← Category.assoc, hP.inr_desc]
      exact (hover (t ≫ b)).trans (hover u₂).symm
  let q : P ⟶ Y' := Over.homMk (B.inclusion.preimage φ) <|
    B.inclusion.map_injective <| by rwa [Functor.map_comp, B.inclusion.map_preimage]
  have hqΦ : Φ.map q = φ := B.inclusion.map_preimage φ
  have hq₁' : Φ.map u₁ ≫ Φ.map q = Φ.map t' ≫ Φ.map a := by rw [hqΦ, hφ, hP.inl_desc]
  have hq₂' : Φ.map u₂ ≫ Φ.map q = Φ.map t ≫ Φ.map b := by rw [hqΦ, hφ, hP.inr_desc]
  have hq₁ : u₁ ≫ q = t' ≫ a := Φ.map_injective (by rwa [Φ.map_comp, Φ.map_comp])
  have hq₂ : u₂ ≫ q = t ≫ b := Φ.map_injective (by rwa [Φ.map_comp, Φ.map_comp])
  obtain ⟨hpb₁, hpb₂, -⟩ :=
    Stacks.Pushout.C1573.isPullback_of_isPushout_of_isPullback hi hpo hk hg hP hq₁' hq₂'
  refine ⟨P, u₁, u₂, q, hP, hq₁, hq₂, hpb₁, hpb₂,
    fun ht ht' ↦ (ThickeningAffineGluing.smooth_induced_iff_of_isPushout hi hpo hP hk hg hq₁'
      hq₂').2 ⟨ht, ht'⟩,
    fun ht ht' ↦ (ThickeningAffineGluing.flat_induced_iff_of_isPushout hi hpo hP hk hg hq₁'
      hq₂').2 ⟨ht, ht'⟩, fun ht y ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (Stacks.Pushout.isThickening_of_isPushout_of_isThickening hpo hi).2 y
  obtain ⟨v, rfl⟩ := ht z
  exact ⟨Φ.map u₂ v, by rw [← Scheme.Hom.comp_apply, hq₂', Scheme.Hom.comp_apply]⟩

end AlgebraicGeometry.Stack.ThickeningPushout

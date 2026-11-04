module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineEtaleChart
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite

/-!
# An affine chart of a first-order thickening of an affine algebraic space

Let `G ⊂ F` be a first-order thickening of algebraic spaces over a scheme `S`, with `G` affine,
say `G ≅ h_{T₀}` for an object `T₀` of the big fppf site of `S` with affine underlying scheme.
The direct proof of [Stacks Project, Tag 05ZR] for finite order thickenings reduces to this case
and then computes with an affine étale chart of `F`. This file produces that chart and the
fibre-product squares the computation reads off it.

## Main results

* `CategoryTheory.IsPullback.exists_kernelPair_restrict`: the pasting argument, in an arbitrary
  category. Let `U₀ = U ×_X T` along `c : U ⟶ X` and `ι : T ⟶ X`, let `(t, s)` be a kernel pair
  of `c`, and let `R₀ = R ×_{t, U} U₀`. Then `R₀` maps to `U₀` a second time, over `s`, and with
  its two maps to `U₀` it is `U₀ ×_T U₀`. It is also `R ×_{s, U} U₀`.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isThickening_of_isAffineSpace`: the ambient
  space of a thickening of an affine algebraic space is quasi-compact.
* `AlgebraicGeometry.Space.exists_affineChart_of_isFirstOrderThickening_of_isAffineSpace`: an
  affine étale chart `c : h_U ⟶ F`, surjective on points, together with the square-zero closed
  immersion `k : U₀ ⟶ U` that restricts the thickening to it and a morphism `u₀ : U₀ ⟶ T₀` of
  the site exhibiting `h_{U₀}` as `h_U ×_F h_{T₀}`.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

/-! ### The pasting argument -/

namespace CategoryTheory.IsPullback

variable {C : Type u} [Category.{v} C]

/-- **Restricting a kernel pair along a base change.** Let `U₀` be the fibre product
`U ×_X T` of `c : U ⟶ X` and `ι : T ⟶ X`, with projections `k` and `u`, let `t, s : R ⟶ U` be a
kernel pair of `c`, and let `R₀` be the fibre product `R ×_{t, U} U₀`, with projections `p₁` and
`p₂`. Then `R₀` has a second morphism `p₂'` to `U₀`, lying over `s`. With its two morphisms to
`U₀` it is the fibre product `U₀ ×_T U₀`, and it is the fibre product `R ×_{s, U} U₀` as well. -/
theorem exists_kernelPair_restrict {X T U U₀ R R₀ : C} {c : U ⟶ X} {ι : T ⟶ X} {k : U₀ ⟶ U}
    {u : U₀ ⟶ T} {t s : R ⟶ U} {p₁ : R₀ ⟶ R} {p₂ : R₀ ⟶ U₀} (h₀ : IsPullback k u c ι)
    (hR : IsPullback t s c c) (h₁ : IsPullback p₁ p₂ t k) :
    ∃ p₂' : R₀ ⟶ U₀, p₂' ≫ k = p₁ ≫ s ∧ p₂' ≫ u = p₂ ≫ u ∧ IsPullback p₂ p₂' u u ∧
      IsPullback p₁ p₂' s k := by
  have hw : (p₁ ≫ s) ≫ c = (p₂ ≫ u) ≫ ι := by
    rw [Category.assoc, ← hR.w, ← Category.assoc, h₁.w, Category.assoc, h₀.w, Category.assoc]
  refine ⟨h₀.lift (p₁ ≫ s) (p₂ ≫ u) hw, h₀.lift_fst _ _ _, h₀.lift_snd _ _ _, ?_, ?_⟩
  · -- `R₀` is `U₀ ×_U R ×_U U₀`, read off by pasting with the square of `U₀`
    have houter : IsPullback (h₀.lift (p₁ ≫ s) (p₂ ≫ u) hw ≫ k) p₂ c (u ≫ ι) := by
      rw [h₀.lift_fst, ← h₀.w]
      exact h₁.paste_horiz hR.flip
    exact (IsPullback.of_right houter
      (by rw [h₀.lift_snd]) h₀).flip
  · have houter : IsPullback (h₀.lift (p₁ ≫ s) (p₂ ≫ u) hw ≫ u) p₁ ι (s ≫ c) := by
      rw [h₀.lift_snd, ← hR.w]
      exact h₁.flip.paste_horiz h₀.flip
    exact (IsPullback.of_right houter (by rw [h₀.lift_fst]) h₀.flip).flip

/-- **The restricted pair of composable arrows.** Let `R₀ = R ×_{t, U} U₀ = R ×_{s, U} U₀`
along `(j, b)` and `(j, a)`, and let `R₂ = R ×_{s, U, t} R` and `R₂₀ = R₀ ×_{a, U₀, b} R₀`. The
morphism `R₂₀ ⟶ R₂` induced by `j` on both factors exhibits `R₂₀` as `R₂ ×_{e₀, R, j} R₀`,
`e₀` being the first projection. -/
theorem pullback_lift_fst_restrict [Limits.HasPullbacks C] {U U₀ R R₀ : C} {t s : R ⟶ U}
    {k : U₀ ⟶ U} {j : R₀ ⟶ R} {b a : R₀ ⟶ U₀} (h₁ : IsPullback j b t k)
    (h₂ : IsPullback j a s k) :
    ∃ w, IsPullback (Limits.pullback.lift (Limits.pullback.fst a b ≫ j)
        (Limits.pullback.snd a b ≫ j) w) (Limits.pullback.fst a b) (Limits.pullback.fst s t) j := by
  have w : (Limits.pullback.fst a b ≫ j) ≫ s = (Limits.pullback.snd a b ≫ j) ≫ t := by
    rw [Category.assoc, h₂.w, ← Category.assoc, Limits.pullback.condition, Category.assoc,
      ← h₁.w, Category.assoc]
  refine ⟨w, IsPullback.of_right ?_ (Limits.pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback s t).flip⟩
  rw [Limits.pullback.lift_snd, h₂.w]
  exact (IsPullback.of_hasPullback a b).flip.paste_horiz h₁

/-- The second projection of the restricted pair of composable arrows: in the situation of
`CategoryTheory.IsPullback.pullback_lift_fst_restrict`, the same morphism `R₂₀ ⟶ R₂` exhibits
`R₂₀` as `R₂ ×_{e₂, R, j} R₀`, `e₂` being the second projection. -/
theorem pullback_lift_snd_restrict [Limits.HasPullbacks C] {U U₀ R R₀ : C} {t s : R ⟶ U}
    {k : U₀ ⟶ U} {j : R₀ ⟶ R} {b a : R₀ ⟶ U₀} (h₁ : IsPullback j b t k)
    (h₂ : IsPullback j a s k) (w : (Limits.pullback.fst a b ≫ j) ≫ s =
      (Limits.pullback.snd a b ≫ j) ≫ t) :
    IsPullback (Limits.pullback.lift (Limits.pullback.fst a b ≫ j)
        (Limits.pullback.snd a b ≫ j) w) (Limits.pullback.snd a b) (Limits.pullback.snd s t) j := by
  refine IsPullback.of_right ?_ (Limits.pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s t)
  rw [Limits.pullback.lift_fst, h₁.w]
  exact (IsPullback.of_hasPullback a b).paste_horiz h₂

/-- **The restricted composition.** In the situation of
`CategoryTheory.IsPullback.pullback_lift_fst_restrict`, let `m : R₂ ⟶ R` satisfy
`m ≫ t = e₀ ≫ t`. Then there is `m₀ : R₂₀ ⟶ R₀` with `ρ ≫ m = m₀ ≫ j` exhibiting `R₂₀` as
`R₂ ×_{m, R, j} R₀`, `ρ : R₂₀ ⟶ R₂` being the comparison morphism. -/
theorem exists_restrict_of_comp_eq [Limits.HasPullbacks C] {U U₀ R R₀ : C} {t s : R ⟶ U}
    {k : U₀ ⟶ U} {j : R₀ ⟶ R} {b a : R₀ ⟶ U₀} (h₁ : IsPullback j b t k)
    (w : (Limits.pullback.fst a b ≫ j) ≫ s = (Limits.pullback.snd a b ≫ j) ≫ t)
    (h₀ : IsPullback (Limits.pullback.lift (Limits.pullback.fst a b ≫ j)
        (Limits.pullback.snd a b ≫ j) w) (Limits.pullback.fst a b) (Limits.pullback.fst s t) j)
    (m : Limits.pullback s t ⟶ R) (hmt : m ≫ t = Limits.pullback.fst s t ≫ t) :
    ∃ m₀ : Limits.pullback a b ⟶ R₀,
      Limits.pullback.lift (Limits.pullback.fst a b ≫ j) (Limits.pullback.snd a b ≫ j) w ≫ m =
        m₀ ≫ j ∧
      IsPullback (Limits.pullback.lift (Limits.pullback.fst a b ≫ j)
        (Limits.pullback.snd a b ≫ j) w) m₀ m j := by
  set ρ := Limits.pullback.lift (Limits.pullback.fst a b ≫ j) (Limits.pullback.snd a b ≫ j) w
  have hw : (ρ ≫ m) ≫ t = (Limits.pullback.fst a b ≫ b) ≫ k := by
    rw [Category.assoc, hmt, ← Category.assoc, h₀.w, Category.assoc, h₁.w, Category.assoc]
  refine ⟨h₁.lift (ρ ≫ m) (Limits.pullback.fst a b ≫ b) hw, (h₁.lift_fst _ _ _).symm, ?_⟩
  refine IsPullback.of_bot ?_ (h₁.lift_fst _ _ _).symm h₁
  rw [h₁.lift_snd, hmt]
  exact h₀.paste_vert h₁

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness, and the chart -/

/-- **The ambient space of a thickening of an affine algebraic space is quasi-compact.** The
inclusion of a thickening is surjective on points, and an affine algebraic space is
quasi-compact, so this is Stacks 040W, part (1). -/
theorem isQuasiCompactSpace_of_isThickening_of_isAffineSpace {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
    (hGaff : IsAffineSpace B S hS G.toFunctor) : IsQuasiCompactSpace B S hS X.1 := by
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hGaff
  have hGalg : IsAlgebraicSpace B S hS G.toFunctor :=
    isAlgebraicSpace_of_iso B S hS e.symm (isAlgebraicSpace_yoneda B S hS T₀)
  exact IsQuasiCompactSpace.of_isSurjective B S hS hGalg X.2
    (isSurjective_ι_of_isThickening B S hS hG)
    (IsQuasiCompactSpace.of_iso B S hS (isQuasiCompactSpace_yoneda_of_isAffine B S hS T₀ hT₀)
      e.symm)

/-- **An affine chart of a first-order thickening of an affine algebraic space.** Let `G ⊂ F`
be a first-order thickening with `e : G ≅ h_{T₀}`, `T₀` affine. There is an affine object `U`
of the site with an étale morphism `c : h_U ⟶ F` which is surjective, an affine object `U₀`
with a square-zero closed immersion `k : U₀ ⟶ U`, and a morphism `u₀ : U₀ ⟶ T₀` of the site
such that `h_{U₀}` is the fibre product of `c` and of the inclusion `h_{T₀} ≅ G ⊆ F`. -/
theorem exists_affineChart_of_isFirstOrderThickening_of_isAffineSpace
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsFirstOrderThickening B S hS X G)
    {T₀ : BigFppfOver B S hS} (e : G.toFunctor ≅ yoneda.obj T₀)
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ∃ (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ X.1) (U₀ : BigFppfOver B S hS)
      (k : U₀ ⟶ U) (u₀ : U₀ ⟶ T₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c ∧
      IsEtale B S hS c ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) ∧
      IsSquareZeroClosedImmersion B S hS k ∧
      IsEtale B S hS (yoneda.map u₀) ∧
      IsPullback (yoneda.map k) (yoneda.map u₀) c (e.inv ≫ G.ι) := by
  obtain ⟨U, c, hU, hcs, hce⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).mp
      (isQuasiCompactSpace_of_isThickening_of_isAffineSpace B S hS hG.1 ⟨T₀, hT₀, ⟨e⟩⟩)
  obtain ⟨U₀, k, u, hpb, hU₀, hue, hk⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening B S hS hG U c hce hU
  refine ⟨U, c, U₀, k, yoneda.preimage (u ≫ e.hom), hU, hcs, hce, hU₀, hk, ?_, ?_⟩
  · rw [Functor.map_preimage]
    exact isEtale_comp B S hS hue (isEtale_of_isIso B S hS e.hom)
  · rw [Functor.map_preimage]
    refine IsPullback.of_iso hpb (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_ <;>
      simp

/-! ### The kernel pair of the chart, restricted to the thickening -/

section KernelPair

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U U₀ T₀ R : BigFppfOver B S hS}
  {c : yoneda.obj U ⟶ X} {ι : yoneda.obj T₀ ⟶ X} {k : U₀ ⟶ U} {u₀ : U₀ ⟶ T₀} {t s : R ⟶ U}

/-- **The kernel pair of the chart, restricted to the closed subspace.** If `h_{U₀}` is the
fibre product of `c : h_U ⟶ X` and `ι : h_{T₀} ⟶ X` along `k` and `u₀`, and `t, s : R ⟶ U` is a
kernel pair of `c`, then there is an object `R₀` of the site with `j : R₀ ⟶ R` and two morphisms
`b, a : R₀ ⟶ U₀` such that `R₀ = R ×_{t, U} U₀ = R ×_{s, U} U₀` along `(j, b)` and `(j, a)`, and
`R₀ = U₀ ×_{T₀} U₀` along `(b, a)`. -/
theorem exists_restrictedKernelPair (h₀ : IsPullback (yoneda.map k) (yoneda.map u₀) c ι)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) c c) :
    ∃ (R₀ : BigFppfOver B S hS) (j : R₀ ⟶ R) (b a : R₀ ⟶ U₀),
      IsPullback j b t k ∧ IsPullback j a s k ∧ IsPullback b a u₀ u₀ := by
  obtain ⟨a', h1, h2, h3, h4⟩ := IsPullback.exists_kernelPair_restrict h₀ hR
    ((IsPullback.of_hasPullback t k).map yoneda)
  set a : pullback t k ⟶ U₀ := yoneda.preimage a' with ha
  have hya : yoneda.map a = a' := Functor.map_preimage _ _
  rw [← hya] at h3 h4
  exact ⟨pullback t k, pullback.fst t k, pullback.snd t k, a, IsPullback.of_hasPullback t k,
    h4.of_map_of_faithful yoneda, h3.of_map_of_faithful yoneda⟩

/-- **The composition of the kernel pair.** For a kernel pair `t, s : R ⟶ U` of `c` and the
fibre product `R ×_{s, U, t} R` with its two projections `e₀, e₂`, there is a morphism
`m : R ×_{s, U, t} R ⟶ R`, the composition of the groupoid, with `m ≫ t = e₀ ≫ t` and
`m ≫ s = e₂ ≫ s`. -/
theorem exists_kernelPair_comp (hR : IsPullback (yoneda.map t) (yoneda.map s) c c) :
    ∃ m : pullback s t ⟶ R, m ≫ t = pullback.fst s t ≫ t ∧ m ≫ s = pullback.snd s t ≫ s := by
  have hw : yoneda.map (pullback.fst s t ≫ t) ≫ c = yoneda.map (pullback.snd s t ≫ s) ≫ c := by
    simp only [Functor.map_comp, Category.assoc, hR.w]
    rw [← Category.assoc, ← Functor.map_comp, pullback.condition, Functor.map_comp,
      Category.assoc, hR.w]
  refine ⟨yoneda.preimage (hR.lift _ _ hw), ?_, ?_⟩ <;> apply yoneda.map_injective <;>
    simp

end KernelPair

end AlgebraicGeometry.Space

end

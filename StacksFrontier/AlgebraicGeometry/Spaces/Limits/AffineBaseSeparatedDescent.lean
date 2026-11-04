module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineBasePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableAtlasTest
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Separatedness descends to an affine base, with no bound on the index

This file proves the affine-base, size-free form of **Stacks 0851**: separatedness of a morphism
of algebraic spaces descends from the limit of a cofiltered system of affine objects of the big
fppf site to a finite stage, with **no cardinality hypothesis** on the index category and no
`AlgebraicGeometry.Space.ChartsBounded` hypothesis.

The tag 0851 is already registered, in the bounded
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded` form, on its theorem
`MorphismDescentSystemOfChartsBounded.exists_isSeparated_mapAt_of_isSeparated_mapLimit`; the
declarations here are a different, incomparable reading of it (the base system is a system of
affine objects of the site rather than a system of algebraic spaces, but the index category is
unrestricted), so they carry no `@[stacks]` attribute of their own.

## Main definitions

No new definitions are introduced outside of private helpers.

## Main results

* `AlgebraicGeometry.Space.isSeparated_iff_isClosedImmersion_kernelPairLift`: separatedness over
  a representable base tested on the kernel pair of one surjective étale chart of the source.
  This is the **converse the library did not have**: only the forward half,
  `AlgebraicGeometry.Space.exists_closedImmersion_selfPullback_of_isSeparated`, was available,
  and the absolute converse
  `AlgebraicGeometry.Space.isSeparatedOver_of_isClosedImmersion_kernelPairToProd` is stated for
  `diag F` over `S`, with `U ×_S U` in place of `T ×_{Y₀} T`.
* `AlgebraicGeometry.Space.isSeparated_iff_isClosedImmersion_kernelPair`: the same with the
  self-fibre product of the base presented by an arbitrary cartesian square, which is the form
  a client holding a *base change* of that fibre product needs.
* `AlgebraicGeometry.Space.exists_isSeparated_baseChange_of_isSeparated_limit`: the affine-base,
  size-free form of **Stacks 0851**.
* `AlgebraicGeometry.Space.exists_isSeparated_isPullback_of_isSeparated_limit`: the same, stated
  over an arbitrary cartesian square, matching
  `AlgebraicGeometry.Space.exists_isFlat_isPullback_of_isFlat_limit` and
  `AlgebraicGeometry.Space.exists_isProper_isPullback_of_isProper_limit`.

## Implementation notes

**Why no chart engine.** `AlgebraicGeometry.Space.IsSeparated f` is
`AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)`, and
`AlgebraicGeometry.Space.IsClosedImmersion` is a *representable-morphism* property, not one of
the form `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`; closed immersion is not étale local
on the source, so no condition on squares of étale charts detects separatedness. The chart
reduction that gives the flatness and relative-dimension analogues over an affine base in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineBasePropertyDescent.lean` therefore cannot
give this one, and the `ChartSquareOfChartsBounded` engine of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/DescendingMorphismProperties.lean` has no
separatedness statement.

**The route that works.** Closed immersions of algebraic spaces are étale local on the
*target*, unconditionally (`AlgebraicGeometry.Space.isClosedImmersion_tfae`, Stacks 03M4), and
over a representable base an étale surjective chart of `Z ×_{T} Z` is the representable
`h_{V ×_T V}` attached to an étale surjective chart `h_V ⟶ Z`. Stacks 02WZ
(`AlgebraicGeometry.presheaf_inverseImage_iff_atlas_snd`) applied to the relative diagonal along
that chart turns separatedness into the single scheme-level statement that
`V ×_Z V ⟶ V ×_T V` is a closed immersion, the base change of the diagonal along the chart being
the kernel pair by `CategoryTheory.Limits.pullback_map_diagonal_isPullback`. That statement is a
property of a base change of one fixed morphism of schemes over the stage, so the cutoff-free
scheme-level Stacks 01ZP, `AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit`,
descends it.

**Hypotheses.** Quasi-compactness of `Z` produces an affine chart; quasi-separatedness of `z`
makes the kernel pair of that chart quasi-compact, which Stacks 01ZP needs. Both are conjuncts
of `AlgebraicGeometry.Space.IsFinitePresentation`, so both are available in the intended
application. **No finite-type hypothesis on `z` is taken**, unlike in the sibling statements:
the comparison `V ×_Z V ⟶ V ×_T V` is locally of finite type because its composite with the
first projection is the étale `V ×_Z V ⟶ V`.

**Shared chart helpers.** The lift of a chart along a base change
(`AlgebraicGeometry.Space.isPullback_chart_baseChange`) and the base change of a chart over a
representable base (`AlgebraicGeometry.Space.baseChangedChart`, with
`AlgebraicGeometry.Space.isPullback_baseChangedChart` and
`AlgebraicGeometry.Space.baseChangedChart_comp_fst`) are taken from
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/DescendingMorphismProperties.lean`, the lowest
module of this family, which is where they are declared once for every file that needs them.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-! ### Cartesian squares for base changes and kernel pairs -/

section Squares

variable {A : Type*} [Category* A] [HasPullbacks A]

/-- **Base changing a morphism over the target.** Let `v : A₁ ⟶ A₂` be a morphism of objects
over `Y`, with structure morphisms `α` and `β`, and let `t : T ⟶ Y`. The induced morphism of
fibre products `A₁ ×_Y T ⟶ A₂ ×_Y T` is a base change of `v` along the first projection of
`A₂ ×_Y T`.

This is `AlgebraicGeometry.overPullback_isPullback` of
`StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange`, read on the chosen fibre
products of the ambient category rather than on the `CategoryTheory.Over` category, and with the
structure morphism of the source given as data so that it need not be literally `v ≫ β`. -/
private theorem isPullback_pullbackMapId {A₁ A₂ Y T : A} (v : A₁ ⟶ A₂) (β : A₂ ⟶ Y)
    (α : A₁ ⟶ Y) (hα : α = v ≫ β) (t : T ⟶ Y) :
    IsPullback (pullback.fst α t)
      (pullback.map α t β t v (𝟙 T) (𝟙 Y) (by rw [Category.comp_id, hα])
        (by rw [Category.comp_id, Category.id_comp]))
      v (pullback.fst β t) := by
  refine IsPullback.of_bot ?_
    (by simp only [pullback.map, pullback.lift_fst, Category.comp_id])
    (IsPullback.of_hasPullback β t)
  have h : pullback.map α t β t v (𝟙 T) (𝟙 Y) (by rw [Category.comp_id, hα])
      (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd β t = pullback.snd α t := by
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  rw [h, ← hα]
  exact IsPullback.of_hasPullback α t

omit [HasPullbacks A] in
/-- **The kernel pair of a base change is the base change of the kernel pair.** Let `aj` be a
base change of `a` along `g`, let `κ₁, κ₂` be a kernel pair of `a`, and let `ρ₁ : Rj ⟶ Vj` be a
base change of `κ₁` along the comparison `u`. Then together with the morphism `ρ₂` determined by
`ρ₂ ≫ u = σ ≫ κ₂`, it is a kernel pair of `aj`. -/
private theorem isPullback_kernelPair_of_isPullback {Rj Vj V Zj Z R : A}
    {σ : Rj ⟶ R} {ρ₁ ρ₂ : Rj ⟶ Vj} {u : Vj ⟶ V} {aj : Vj ⟶ Zj} {a : V ⟶ Z} {g : Zj ⟶ Z}
    {κ₁ κ₂ : R ⟶ V} (hbc : IsPullback u aj a g) (hst : IsPullback κ₁ κ₂ a a)
    (hA : IsPullback σ ρ₁ κ₁ u) (h2u : ρ₂ ≫ u = σ ≫ κ₂) (h2a : ρ₂ ≫ aj = ρ₁ ≫ aj) :
    IsPullback ρ₁ ρ₂ aj aj := by
  have houter : IsPullback (σ ≫ κ₂) ρ₁ a (u ≫ a) := hA.paste_horiz hst.flip
  rw [← h2u, hbc.w] at houter
  exact (houter.of_right h2a hbc).flip

end Squares

/-! ### Separatedness over a representable base, tested on a kernel pair -/

section KernelPairCriterion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    (f : X ⟶ yoneda.obj Y₀) (φ : yoneda.obj T ⟶ X) (τ : T ⟶ Y₀) (hτ : φ ≫ f = yoneda.map τ)

include hτ in
/-- The self-fibre product of `τ` in the site represents the self-fibre product over the
representable base of the source of a chart. -/
private theorem isPullback_yonedaSelfPullback :
    IsPullback (yoneda.map (pullback.fst τ τ)) (yoneda.map (pullback.snd τ τ))
      (φ ≫ f) (φ ≫ f) := by
  rw [hτ]
  exact (IsPullback.of_hasPullback τ τ).map yoneda

/-- **The chart of `X ×_{h_{Y₀}} X` attached to a chart `φ : h_T ⟶ X`.** Its source is the
representable presheaf of the self-fibre product `T ×_{Y₀} T`, formed in the site. -/
private noncomputable def selfProdChart : yoneda.obj (pullback τ τ) ⟶ pullback f f :=
  pullback.lift (yoneda.map (pullback.fst τ τ) ≫ φ) (yoneda.map (pullback.snd τ τ) ≫ φ)
    (by rw [Category.assoc, Category.assoc, hτ, ← yoneda.map_comp, ← yoneda.map_comp,
      pullback.condition])

/-- The chart of the self-fibre product is, up to the representing isomorphism, the morphism of
fibre products induced by the chart. -/
private theorem selfProdChart_eq :
    selfProdChart B S hS f φ τ hτ =
      (isPullback_yonedaSelfPullback B S hS f φ τ hτ).isoPullback.hom ≫
        pullback.map (φ ≫ f) (φ ≫ f) f f φ φ (𝟙 _) (Category.comp_id _) (Category.comp_id _) := by
  refine pullback.hom_ext ?_ ?_
  · simp only [selfProdChart, pullback.lift_fst, Category.assoc, pullback.map,
      pullback.lift_fst,
      (isPullback_yonedaSelfPullback B S hS f φ τ hτ).isoPullback_hom_fst_assoc]
  · simp only [selfProdChart, pullback.lift_snd, Category.assoc, pullback.map,
      pullback.lift_snd,
      (isPullback_yonedaSelfPullback B S hS f φ τ hτ).isoPullback_hom_snd_assoc]

/-- The chart of the self-fibre product inherits every relative property of the chart whose
tested property of morphisms of schemes is stable under composition. -/
private theorem presheaf_selfProdChart (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderComposition]
    (hφ : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf φ) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (selfProdChart B S hS f φ τ hτ) := by
  let P : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) P
  rw [selfProdChart_eq]
  exact MorphismProperty.RespectsIso.precomp P.presheaf _ _
    (MorphismProperty.pullbackMap (P := P.presheaf) hφ hφ rfl rfl)

variable {Rp : BigFppfOver B S hS} {p q : Rp ⟶ T}

/-- **The kernel pair of a chart is the base change of the relative diagonal along the induced
chart of the self-fibre product.** -/
private theorem isPullback_kernelPairLift_diagonal
    (hpq : IsPullback (yoneda.map p) (yoneda.map q) φ φ) (hc : p ≫ τ = q ≫ τ) :
    IsPullback (yoneda.map p ≫ φ) (yoneda.map (pullback.lift p q hc))
      (pullback.diagonal f) (selfProdChart B S hS f φ τ hτ) := by
  have hsq := isPullback_yonedaSelfPullback B S hS f φ τ hτ
  refine (pullback_map_diagonal_isPullback φ φ f).of_iso hpq.isoPullback.symm (Iso.refl X)
    hsq.isoPullback.symm (Iso.refl (pullback f f)) ?_ ?_ (by simp) ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp,
      hpq.isoPullback_hom_fst_assoc]
  · refine (Iso.comp_inv_eq _).2 (pullback.hom_ext ?_ ?_)
    · simp only [Iso.symm_hom, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id,
        hsq.isoPullback_hom_fst, ← Functor.map_comp, pullback.lift_fst,
        Iso.eq_inv_comp, hpq.isoPullback_hom_fst]
    · simp only [Iso.symm_hom, Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id,
        hsq.isoPullback_hom_snd, ← Functor.map_comp, pullback.lift_snd,
        Iso.eq_inv_comp, hpq.isoPullback_hom_snd]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp,
      ← selfProdChart_eq B S hS f φ τ hτ]

include hτ in
/-- **Separatedness over a representable base, tested on the kernel pair of one surjective
étale chart of the source.** Let `f : X ⟶ h_{Y₀}` be a morphism from an algebraic space to a
representable presheaf, let `φ : h_T ⟶ X` be a surjective étale chart of the source, let
`τ : T ⟶ Y₀` be the morphism of the site underlying `φ ≫ f`, and let `p, q : R ⟶ T` present the
kernel pair of `φ`. Then `f` is separated exactly when the morphism of schemes underlying
`R ⟶ T ×_{Y₀} T` is a closed immersion.

This is the relative form of
`AlgebraicGeometry.Space.isSeparatedOver_iff_isClosedImmersion_kernelPairToProd`, which tests
the *absolute* diagonal on `R ⟶ U ×_S U`. The forward direction strengthens
`AlgebraicGeometry.Space.exists_closedImmersion_selfPullback_of_isSeparated` by producing the
closed immersion on a *given* presentation of the kernel pair rather than on a chosen one, and
the backward direction — the converse the library did not have — is what makes separatedness
readable off a single chart.

The proof is Stacks 02WZ (`AlgebraicGeometry.Space.presheaf_inverseImage_iff_atlas_snd`) applied
to the relative diagonal of `f`, which is representable because `X` is an algebraic space, with
the atlas `h_{T ×_{Y₀} T} ⟶ X ×_{h_{Y₀}} X` induced by `φ`; that atlas is surjective and étale
because `φ` is, and the base change of the diagonal along it is the kernel pair by
`CategoryTheory.Limits.pullback_map_diagonal_isPullback`. -/
theorem isSeparated_iff_isClosedImmersion_kernelPairLift (hX : IsAlgebraicSpace B S hS X)
    (hφS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hφE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hpq : IsPullback (yoneda.map p) (yoneda.map q) φ φ) (hc : p ≫ τ = q ≫ τ) :
    IsSeparated B S hS f ↔
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (pullback.lift p q hc)) := by
  have : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun g₁ g₂ h₁ h₂ ↦ by have := h₁; have := h₂; infer_instance⟩
  have : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have hdiag : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    relativelyRepresentable_pullbackDiagonal B S hS f hX
  set ch := selfProdChart B S hS f φ τ hτ with hch
  rw [show IsSeparated B S hS f = (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) from rfl,
    presheaf_inverseImage_iff_atlas_snd B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (pullback.diagonal f) hdiag
      (pullback τ τ) ch
      (hch ▸ presheaf_selfProdChart B S hS f φ τ hτ _ hφS)
      (hch ▸ presheaf_selfProdChart B S hS f φ τ hτ _ hφE),
    ← BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (hdiag.snd ch),
    ← BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (pullback.lift p q hc)]
  exact CategoryTheory.prop_snd_iff_of_isPullback _ (hdiag.isPullback ch)
    (hch ▸ isPullback_kernelPairLift_diagonal B S hS f φ τ hτ hpq hc)

include hτ in
/-- **Separatedness over a representable base, tested on the kernel pair of one surjective
étale chart of the source, with the self-fibre product of the base presented by any cartesian
square.** This is
`AlgebraicGeometry.Space.isSeparated_iff_isClosedImmersion_kernelPairLift` with `T ×_{Y₀} T`
replaced by an arbitrary object `Pr` of the site carrying a cartesian square over `τ`, and the
comparison morphism `j : R ⟶ Pr` given by its two components; this is the form a client holding
a base change of the self-fibre product needs, since that base change is only isomorphic to, not
literally, the chosen fibre product. -/
theorem isSeparated_iff_isClosedImmersion_kernelPair (hX : IsAlgebraicSpace B S hS X)
    (hφS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hφE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    {Pr : BigFppfOver B S hS} {π₁ π₂ : Pr ⟶ T} (hPr : IsPullback π₁ π₂ τ τ)
    (hpq : IsPullback (yoneda.map p) (yoneda.map q) φ φ)
    {jr : Rp ⟶ Pr} (hj₁ : jr ≫ π₁ = p) (hj₂ : jr ≫ π₂ = q) :
    IsSeparated B S hS f ↔
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map jr) := by
  have hc : p ≫ τ = q ≫ τ := by
    rw [← hj₁, ← hj₂, Category.assoc, Category.assoc, hPr.w]
  have heq : jr ≫ hPr.isoPullback.hom = pullback.lift p q hc := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hPr.isoPullback_hom_fst, hj₁, pullback.lift_fst]
    · rw [Category.assoc, hPr.isoPullback_hom_snd, hj₂, pullback.lift_snd]
  have : IsIso ((BigFppfOver.toScheme B S hS).map hPr.isoPullback.hom) :=
    Functor.map_isIso (BigFppfOver.toScheme B S hS) hPr.isoPullback.hom
  rw [isSeparated_iff_isClosedImmersion_kernelPairLift B S hS f φ τ hτ hX hφS hφE hpq hc,
    ← heq, Functor.map_comp]
  exact MorphismProperty.cancel_right_of_respectsIso
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) ((BigFppfOver.toScheme B S hS).map jr)
    ((BigFppfOver.toScheme B S hS).map hPr.isoPullback.hom)

end KernelPairCriterion

/-! ### Base changing the chart and its kernel pair along a morphism of the site -/

section StageBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Ti Tj Vs Rp : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable (qa : Vs ⟶ Ti) (m : Tj ⟶ Ti)

/-- The first projection of `(V ×_{T_i} V) ×_{T_i} T_j` onto `V ×_{T_i} T_j`. -/
private noncomputable def selfProdProj₁ : pullback (pullback.fst qa qa ≫ qa) m ⟶ pullback qa m :=
  pullback.map (pullback.fst qa qa ≫ qa) m qa m (pullback.fst qa qa) (𝟙 Tj) (𝟙 Ti)
    (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])

/-- The second projection of `(V ×_{T_i} V) ×_{T_i} T_j` onto `V ×_{T_i} T_j`. -/
private noncomputable def selfProdProj₂ : pullback (pullback.fst qa qa ≫ qa) m ⟶ pullback qa m :=
  pullback.map (pullback.fst qa qa ≫ qa) m qa m (pullback.snd qa qa) (𝟙 Tj) (𝟙 Ti)
    (by rw [Category.comp_id]; exact pullback.condition)
    (by rw [Category.comp_id, Category.id_comp])

/-- **`(V ×_{T_i} V) ×_{T_i} T_j` is the self-fibre product of `V ×_{T_i} T_j` over `T_j`.**
This is the identification that lets the kernel pair of the base changed chart be read inside
the base change of the self-fibre product of the chart. -/
private theorem isPullback_selfProdProj :
    IsPullback (selfProdProj₁ qa m) (selfProdProj₂ qa m)
      (pullback.snd qa m) (pullback.snd qa m) := by
  have hS₁ : IsPullback (pullback.fst (pullback.fst qa qa ≫ qa) m) (selfProdProj₂ qa m)
      (pullback.snd qa qa) (pullback.fst qa m) :=
    isPullback_pullbackMapId (pullback.snd qa qa) qa (pullback.fst qa qa ≫ qa)
      pullback.condition m
  have houter := hS₁.paste_horiz (IsPullback.of_hasPullback qa qa)
  rw [show pullback.fst qa m ≫ qa = pullback.snd qa m ≫ m from pullback.condition,
    show pullback.fst (pullback.fst qa qa ≫ qa) m ≫ pullback.fst qa qa =
      selfProdProj₁ qa m ≫ pullback.fst qa m from
      (by simp only [selfProdProj₁, pullback.map, pullback.lift_fst, Category.comp_id])] at houter
  exact houter.of_right
    (by simp only [selfProdProj₁, selfProdProj₂, pullback.map, pullback.lift_snd,
      Category.comp_id]) (IsPullback.of_hasPullback qa m)

variable {κ₁ κ₂ : Rp ⟶ Vs} (hκ : κ₁ ≫ qa = κ₂ ≫ qa)

/-- The first projection of `R ×_{T_i} T_j` onto `V ×_{T_i} T_j`. -/
private noncomputable def stageKernelProj₁ : pullback (κ₁ ≫ qa) m ⟶ pullback qa m :=
  pullback.map (κ₁ ≫ qa) m qa m κ₁ (𝟙 Tj) (𝟙 Ti) (Category.comp_id _)
    (by rw [Category.comp_id, Category.id_comp])

include hκ in
/-- The second projection of `R ×_{T_i} T_j` onto `V ×_{T_i} T_j`. -/
private noncomputable def stageKernelProj₂ : pullback (κ₁ ≫ qa) m ⟶ pullback qa m :=
  pullback.map (κ₁ ≫ qa) m qa m κ₂ (𝟙 Tj) (𝟙 Ti) (by rw [Category.comp_id]; exact hκ)
    (by rw [Category.comp_id, Category.id_comp])

include hκ in
/-- The base change along `m` of the comparison `R ⟶ V ×_{T_i} V` of the kernel pair of the
chart with the self-fibre product of the chart. -/
private noncomputable def stageKernelLift :
    pullback (κ₁ ≫ qa) m ⟶ pullback (pullback.fst qa qa ≫ qa) m :=
  pullback.map (κ₁ ≫ qa) m (pullback.fst qa qa ≫ qa) m (pullback.lift κ₁ κ₂ hκ) (𝟙 Tj) (𝟙 Ti)
    (by rw [Category.comp_id, ← Category.assoc, pullback.lift_fst])
    (by rw [Category.comp_id, Category.id_comp])

include hκ in
/-- The base changed comparison has the two base changed projections as its components. -/
private theorem stageKernelLift_comp :
    stageKernelLift qa m hκ ≫ selfProdProj₁ qa m = stageKernelProj₁ qa m (κ₁ := κ₁) ∧
      stageKernelLift qa m hκ ≫ selfProdProj₂ qa m = stageKernelProj₂ qa m hκ := by
  constructor <;> refine pullback.hom_ext ?_ ?_ <;>
    simp only [stageKernelLift, stageKernelProj₁, stageKernelProj₂, selfProdProj₁, selfProdProj₂,
      pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
      pullback.lift_fst_assoc]

include hκ in
/-- **The kernel pair of the base changed chart is the base change of the kernel pair.** -/
private theorem isPullback_stageKernelProj (z : Z ⟶ yoneda.obj Ti) (a : yoneda.obj Vs ⟶ Z)
    (hqa : yoneda.map qa = a ≫ z)
    (hst : IsPullback (yoneda.map κ₁) (yoneda.map κ₂) a a) :
    IsPullback (yoneda.map (stageKernelProj₁ qa m (κ₁ := κ₁)))
      (yoneda.map (stageKernelProj₂ qa m hκ))
      (baseChangedChart z a qa hqa m) (baseChangedChart z a qa hqa m) := by
  have e₁ : stageKernelProj₁ qa m (κ₁ := κ₁) ≫ pullback.fst qa m =
      pullback.fst (κ₁ ≫ qa) m ≫ κ₁ := by
    simp only [stageKernelProj₁, pullback.map, pullback.lift_fst, Category.comp_id]
  have e₂ : stageKernelProj₂ qa m hκ ≫ pullback.fst qa m =
      pullback.fst (κ₁ ≫ qa) m ≫ κ₂ := by
    simp only [stageKernelProj₂, pullback.map, pullback.lift_fst, Category.comp_id]
  have f₁ : stageKernelProj₁ qa m (κ₁ := κ₁) ≫ pullback.snd qa m =
      pullback.snd (κ₁ ≫ qa) m := by
    simp only [stageKernelProj₁, pullback.map, pullback.lift_snd, Category.comp_id]
  have f₂ : stageKernelProj₂ qa m hκ ≫ pullback.snd qa m = pullback.snd (κ₁ ≫ qa) m := by
    simp only [stageKernelProj₂, pullback.map, pullback.lift_snd, Category.comp_id]
  refine isPullback_kernelPair_of_isPullback (isPullback_baseChangedChart z a qa hqa m) hst
    ((isPullback_pullbackMapId κ₁ qa (κ₁ ≫ qa) rfl m).map yoneda) ?_ ?_
  · rw [← yoneda.map_comp, ← yoneda.map_comp, e₂]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, baseChangedChart_comp_fst, ← yoneda.map_comp,
        ← yoneda.map_comp, f₁, f₂]
    · simp only [baseChangedChart, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, e₁, e₂,
        yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hst.w]

end StageBaseChange

/-! ### Separatedness of a base change, read on the base change of the kernel pair -/

section StageCriterion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Ti Tj Vs Rp : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- **Separatedness of the base change of `z` along `h_m`, read on the base change of the
kernel pair of a chart of `Z`.** Let `z : Z ⟶ h_{T_i}` be an algebraic space over a
representable presheaf, let `a : h_V ⟶ Z` be a surjective étale chart with `h_{qa} = a ≫ z`, and
let `κ₁, κ₂ : R ⟶ V` present the kernel pair of `a`. For every morphism `m : T_j ⟶ T_i` of the
site, the base change of `z` along `h_m` is separated exactly when the base change along `m` of
the comparison `R ⟶ V ×_{T_i} V` is a closed immersion of schemes.

This is the whole geometric content of the descent: the right-hand side is a property of a
*base change of one fixed morphism of schemes over `T_i`*, so the scheme-level descent along a
cofiltered system applies to it directly. -/
private theorem isSeparated_baseChange_iff_isClosedImmersion_stageKernelLift
    (hZalg : IsAlgebraicSpace B S hS Z) (z : Z ⟶ yoneda.obj Ti) (a : yoneda.obj Vs ⟶ Z)
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haEt : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (qa : Vs ⟶ Ti) (hqa : yoneda.map qa = a ≫ z)
    {κ₁ κ₂ : Rp ⟶ Vs} (hst : IsPullback (yoneda.map κ₁) (yoneda.map κ₂) a a)
    (hκ : κ₁ ≫ qa = κ₂ ≫ qa) (m : Tj ⟶ Ti) :
    IsSeparated B S hS (pullback.fst (yoneda.map m) z) ↔
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (stageKernelLift qa m hκ)) := by
  obtain ⟨hl₁, hl₂⟩ := stageKernelLift_comp qa m hκ
  exact isSeparated_iff_isClosedImmersion_kernelPair B S hS _
    (baseChangedChart z a qa hqa m) (pullback.snd qa m) (baseChangedChart_comp_fst z a qa hqa m)
    (isAlgebraicSpace_pullback B S hS (yoneda.map m) z (isAlgebraicSpace_yoneda B S hS _) hZalg
      (isAlgebraicSpace_yoneda B S hS _))
    (MorphismProperty.of_isPullback (isPullback_baseChangedChart z a qa hqa m) haSurj)
    (MorphismProperty.of_isPullback (isPullback_baseChangedChart z a qa hqa m) haEt)
    (isPullback_selfProdProj qa m) (isPullback_stageKernelProj qa m hκ z a hqa hst) hl₁ hl₂

end StageCriterion

/-! ### Comparing the base change in the site with the `Over`-category base change -/

section OverComparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A₁ A₂ Ti Tj : BigFppfOver B S hS}

/-- **The base change in the site of a morphism over `T_i` and its base change in the category
over the underlying scheme of `T_i` carry the same properties.** This is the comparison that lets
the scheme-level descent of Stacks 01ZP, which is stated on
`CategoryTheory.Over ((D ⋙ ...).obj i)`, be read on a morphism of the site.

It generalizes `CategoryTheory.prop_overPullback_map_left_iff_pullback_snd` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties`, which is the case
where the target of the morphism being base changed is the base object itself. -/
private theorem prop_pullbackMapId_iff_overPullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (v : A₁ ⟶ A₂) (β : A₂ ⟶ Ti) (α : A₁ ⟶ Ti) (hα : α = v ≫ β) (m : Tj ⟶ Ti)
    (t : (BigFppfOver.toScheme B S hS).obj Tj ⟶ (BigFppfOver.toScheme B S hS).obj Ti)
    (ht : t = (BigFppfOver.toScheme B S hS).map m) :
    P ((BigFppfOver.toScheme B S hS).map
        (pullback.map α m β m v (𝟙 Tj) (𝟙 Ti) (by rw [Category.comp_id, hα])
          (by rw [Category.comp_id, Category.id_comp]))) ↔
      P ((Over.pullback t).map
        (Over.homMk ((BigFppfOver.toScheme B S hS).map v)
            (by simp only [Over.mk_hom, ← Functor.map_comp, ← hα]) :
          Over.mk ((BigFppfOver.toScheme B S hS).map α) ⟶
            Over.mk ((BigFppfOver.toScheme B S hS).map β))).left := by
  subst ht
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsq := (isPullback_pullbackMapId v β α hα m).map (BigFppfOver.toScheme B S hS)
  set eβ := ((IsPullback.of_hasPullback β m).map (BigFppfOver.toScheme B S hS)).isoPullback
    with heβ
  have h₂ : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst α m))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.map α m β m v (𝟙 Tj) (𝟙 Ti) (by rw [Category.comp_id, hα])
          (by rw [Category.comp_id, Category.id_comp])) ≫ eβ.hom)
      ((BigFppfOver.toScheme B S hS).map v)
      (pullback.fst ((BigFppfOver.toScheme B S hS).map β)
        ((BigFppfOver.toScheme B S hS).map m)) :=
    hsq.of_iso (Iso.refl _) (Iso.refl _) eβ (Iso.refl _) (by simp) (by simp) (by simp)
      (by simpa only [Iso.refl_hom, Category.comp_id, heβ] using
        (((IsPullback.of_hasPullback β m).map
          (BigFppfOver.toScheme B S hS)).isoPullback_hom_fst).symm)
  exact (P.cancel_right_of_respectsIso _ eβ.hom).symm.trans
    (CategoryTheory.prop_snd_iff_of_isPullback P h₂
      (overPullback_isPullback ((BigFppfOver.toScheme B S hS).map m) _ _ _))

end OverComparison

/-! ### Separatedness descends along a cofiltered system of affine objects of the site -/

section AffineBaseDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) {c : Cone D}

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- **The affine-base, size-free form of Stacks 0851.** Let `D` be a cofiltered inverse system
of affine objects of the big fppf site over `S` whose cone `c` has a limiting cone of underlying
schemes, let `i` be a stage, and let `z : Z ⟶ T_i` be a quasi-compact, quasi-separated algebraic
space over the representable presheaf `T_i` attached to `D.obj i`. If the base change of `z`
along the leg of `c` at `i` is separated, then its base change along `D.map g` is separated for
some `g : j ⟶ i`.

There is no cardinality hypothesis on `I` and no `AlgebraicGeometry.Space.ChartsBounded`
hypothesis. This is the input that
`AlgebraicGeometry.Space.exists_isProper_pullback_fst_of_isProper_limit` takes as a hypothesis
at the starting stage, and that Chow's lemma consumes there.

**Hypotheses.** Quasi-compactness of `Z` is what produces an *affine* surjective étale chart
`a : h_V ⟶ Z`; quasi-separatedness of `z` is what makes the kernel pair `V ×_Z V` of that chart
quasi-compact, which the scheme-level descent needs. Both are available in the intended
application, where `z` is a finitely presented, flat and proper family of algebraic spaces over
the affine base. No finite-type hypothesis on `z` is needed: the comparison morphism
`V ×_Z V ⟶ V ×_{T_i} V` is locally of finite type because its composite with the first
projection is the étale `V ×_Z V ⟶ V`.

**The route.** Separatedness is a closed-immersion property of the relative diagonal, which is
*not* of the form `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, so the chart reduction behind
the flatness and relative-dimension analogues over an affine base is unavailable. Instead closed
immersions of algebraic spaces are étale local on the *target* unconditionally (Stacks 03M4,
`AlgebraicGeometry.Space.isClosedImmersion_tfae`), which through Stacks 02WZ makes separatedness
of `z` equivalent to one morphism of schemes `V ×_Z V ⟶ V ×_{T_i} V` being a closed immersion
(`AlgebraicGeometry.Space.isSeparated_iff_isClosedImmersion_kernelPairLift`). That equivalence
is compatible with base change along the system
(`AlgebraicGeometry.Space.isSeparated_baseChange_iff_isClosedImmersion_stageKernelLift`), so the
cutoff-free scheme-level Stacks 01ZP
(`AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit`) descends it. -/
theorem exists_isSeparated_baseChange_of_isSeparated_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZalg : IsAlgebraicSpace B S hS Z) (hqc : IsQuasiCompactSpace B S hS Z)
    (hqs : IsQuasiSeparated B S hS z)
    (hsep : IsSeparated B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) z)) :
    ∃ (j : I) (g : j ⟶ i), IsSeparated B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) := by
  classical
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : EssentiallySmall.{u} I := inferInstance
  -- the affine surjective étale chart of `Z`
  obtain ⟨Vs, a, hVsAff, haSurj, haEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z hZalg).mp hqc
  have ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a :=
    (isEtale_iff_presheaf_of_yoneda B S hS a).mp haEt
  obtain ⟨qa, hqa⟩ : ∃ qa : Vs ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i),
      yoneda.map qa = a ≫ z := ⟨yoneda.preimage (a ≫ z), yoneda.map_preimage _⟩
  -- the kernel pair of the chart and its comparison with the self-fibre product of the base
  have hst : IsPullback (yoneda.map (ha.rep.fst' a)) (yoneda.map (ha.rep.snd a)) a a :=
    ha.rep.isPullback' a
  have hκ : ha.rep.fst' a ≫ qa = ha.rep.snd a ≫ qa := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hqa, ← Category.assoc, ← Category.assoc, hst.w]
  set jR := pullback.lift (ha.rep.fst' a) (ha.rep.snd a) hκ with hjR
  -- affineness of the base, of the chart and of the self-fibre product of the chart
  have hTiAff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) := (D.obj i).property
  have := hVsAff
  have hPAff : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback qa qa)) :=
    IsAffine.of_isIso ((((IsPullback.of_hasPullback qa qa).map
      (BigFppfOver.toScheme B S hS)).isoPullback).hom)
  -- the comparison is locally of finite type, being a mono onto the self-fibre product whose
  -- composite with the first projection is étale
  have hκ₁Et : _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (ha.rep.fst' a)) :=
    ha.property a (yoneda.map (ha.rep.snd a)) (ha.rep.fst' a) hst.flip
  have hcomp : _root_.AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map jR ≫
        (BigFppfOver.toScheme B S hS).map (pullback.fst qa qa)) := by
    rw [← Functor.map_comp, hjR, pullback.lift_fst]
    have := hκ₁Et
    infer_instance
  have hjRft : _root_.AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map jR) :=
    _root_.AlgebraicGeometry.locallyOfFiniteType_of_comp
      ((BigFppfOver.toScheme B S hS).map jR)
      ((BigFppfOver.toScheme B S hS).map (pullback.fst qa qa))
  have hmono : Mono jR := by
    refine ⟨fun {W} x y hxy => ?_⟩
    refine ha.rep.hom_ext' ?_ ?_
    · simpa only [hjR, Category.assoc, pullback.lift_fst] using
        congrArg (fun k => k ≫ pullback.fst qa qa) hxy
    · simpa only [hjR, Category.assoc, pullback.lift_snd] using
        congrArg (fun k => k ≫ pullback.snd qa qa) hxy
  -- the kernel pair is quasi-compact, by quasi-separatedness of `z`
  have hjRqc : _root_.AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map jR) :=
    (diagonalProp_quasiCompact_of_isQuasiSeparated B S hS
      (relativelyRepresentable_pullbackDiagonal B S hS z hZalg) hqs).property
      (selfProdChart B S hS z a qa hqa.symm) _ jR
      (isPullback_kernelPairLift_diagonal B S hS z a qa hqa.symm hst hκ)
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj (pullback qa qa)) :=
    Scheme.compactSpace_of_isAffine _
  have := hjRqc
  have hRcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj (ha.rep.pullback a)) :=
    _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map jR)
  have : Mono ((BigFppfOver.toScheme B S hS).map jR) :=
    preserves_mono_of_preservesLimit (BigFppfOver.toScheme B S hS) jR
  have hRqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (ha.rep.pullback a)) :=
    _root_.AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map jR)
  -- the scheme-level descent problem at the stage
  set Y₀ : Over ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) :=
    Over.mk ((BigFppfOver.toScheme B S hS).map (pullback.fst qa qa ≫ qa)) with hY₀
  set X₀ : Over ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) :=
    Over.mk ((BigFppfOver.toScheme B S hS).map (ha.rep.fst' a ≫ qa)) with hX₀
  set f₀ : X₀ ⟶ Y₀ := Over.homMk ((BigFppfOver.toScheme B S hS).map jR)
    (by
      show (BigFppfOver.toScheme B S hS).map jR ≫
          (BigFppfOver.toScheme B S hS).map (pullback.fst qa qa ≫ qa) =
        (BigFppfOver.toScheme B S hS).map (ha.rep.fst' a ≫ qa)
      rw [← Functor.map_comp, hjR, ← Category.assoc, pullback.lift_fst]) with hf₀
  have hEaff : ∀ k : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj k) := fun k ↦
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj k)
  have : ∀ {k l : I} (g : k ⟶ l),
      _root_.AlgebraicGeometry.IsAffineHom ((D ⋙ BigAffineFppf.toScheme B S hS).map g) := by
    intro k l g
    have := hEaff k
    have := hEaff l
    exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  have : IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) := hEaff i
  have : CompactSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) :=
    Scheme.compactSpace_of_isAffine _
  have : QuasiSeparatedSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) := inferInstance
  have : IsAffine Y₀.left := hPAff
  have : CompactSpace Y₀.left := Scheme.compactSpace_of_isAffine _
  have : QuasiSeparatedSpace Y₀.left := inferInstance
  have : CompactSpace X₀.left := hRcompact
  have : QuasiSeparatedSpace X₀.left := hRqs
  have : _root_.AlgebraicGeometry.LocallyOfFiniteType f₀.left := hjRft
  -- separatedness of a base change, read on the `Over`-category base change of `f₀`
  have key := fun {Tj : BigFppfOver B S hS}
      (m : Tj ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i)) =>
    (isSeparated_baseChange_iff_isClosedImmersion_stageKernelLift B S hS hZalg z a
      haSurj ha qa hqa hst hκ m).trans
      (prop_pullbackMapId_iff_overPullback
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) jR (pullback.fst qa qa ≫ qa)
        (ha.rep.fst' a ≫ qa) (by rw [hjR, ← Category.assoc, pullback.lift_fst]) m _ rfl)
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((Over.pullback (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i)).map f₀).left :=
    (key ((BigAffineFppf.inclusion B S hS).map (c.π.app i))).mp hsep
  obtain ⟨j, g, hj⟩ := _root_.AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit
    (D ⋙ BigAffineFppf.toScheme B S hS) ((BigAffineFppf.toScheme B S hS).mapCone c) hc i
    X₀ Y₀ f₀
  exact ⟨j, g, (key ((BigAffineFppf.inclusion B S hS).map (D.map g))).mpr hj⟩

/-- **The affine-base, size-free form of Stacks 0851, stated over an arbitrary cartesian
square.** The base change of `fi` to the vertex of the cone is presented by any cartesian square
over the cone leg rather than by the canonical fibre product, and the conclusion produces the
stage, the morphism `s : k ⟶ i` of the index category, and a cartesian square over `D.map s`.

This is the shape in which
`AlgebraicGeometry.Space.exists_isFlat_isPullback_of_isFlat_limit`,
`AlgebraicGeometry.Space.exists_hasRelativeDimensionLE_isPullback_of_limit` and
`AlgebraicGeometry.Space.exists_isProper_isPullback_of_isProper_limit` state their
conclusions. -/
theorem exists_isSeparated_isPullback_of_isSeparated_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fi : Zi ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZi : IsAlgebraicSpace B S hS Zi) (hqc : IsQuasiCompactSpace B S hS Zi)
    (hqs : IsQuasiSeparated B S hS fi)
    {ZT : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fT : ZT ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)) (gT : ZT ⟶ Zi)
    (hsq : IsPullback fT gT
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi)
    (hsep : IsSeparated B S hS fT) :
    ∃ (k : I) (s : k ⟶ i) (Zk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fk : Zk ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (hk : Zk ⟶ Zi),
      IsPullback fk hk
          (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) fi ∧
        IsSeparated B S hS fk := by
  have hiso : hsq.isoPullback.inv ≫ fT =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi := by
    rw [Iso.inv_comp_eq]
    exact hsq.isoPullback_hom_fst.symm
  have hlim : IsSeparated B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi) := by
    rw [← hiso]
    exact isSeparated_of_arrowIso B S hS fT (hsq.isoPullback.inv ≫ fT) hsq.isoPullback.hom
      (𝟙 (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)))
      (by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]) hsep
  obtain ⟨k, s, h⟩ := exists_isSeparated_baseChange_of_isSeparated_limit B S hS D hc i fi hZi
    hqc hqs hlim
  exact ⟨k, s, _, _, _, IsPullback.of_hasPullback _ _, h⟩

end AffineBaseDescent

end AlgebraicGeometry.Space

end

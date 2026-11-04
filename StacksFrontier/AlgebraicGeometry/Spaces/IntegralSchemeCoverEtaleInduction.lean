module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverDenseOpenFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverDenseOpenEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenImmersionBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePointwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Operations
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence

/-!
# Stacks 0GUL: the induction tracking the étale locus, and the tag

Stacks 0GUL asserts, for a quasi-compact and quasi-separated algebraic space `X` over a scheme
`S` whose space of points has finitely many irreducible components, that there is a surjective
integral morphism `Y ⟶ X` from a scheme which is finite étale over a quasi-compact dense open
`U ⊆ X`, and that it can be chosen to factor Zariski locally on `Y` through any prescribed
surjective étale `V ⟶ X`. This file proves it, and carries the `@[stacks 0GUL]` attribute.

## Main results

* `AlgebraicGeometry.Space.exists_etaleRefiningCover_of_chart_fibre_le`: **the induction.** For
  a separated surjective étale chart `p : h_U ⟶ X` with quasi-compact source whose field-valued
  fibres have degree at most `d`, there is a surjective integral cover by a scheme, étale at
  every point over an open set containing every generic point of `|X|`, factoring Zariski
  locally through `p`.
* `AlgebraicGeometry.Space.existsIntegralSchemeCoverEtaleRefining_of_isEtale`: the same for an
  arbitrary surjective étale chart by a scheme, through an affine chart refining it
  (`AlgebraicGeometry.Space.exists_affine_chart_through`).
* `AlgebraicGeometry.Space.exists_integralSchemeCover_finiteEtaleOverDenseOpen_and_refining`:
  **Stacks 0GUL**, both clauses, over the hypotheses of the tag and no others.

## Implementation notes

**The source's induction does not go through as written, and is repaired here.** The source
proves both clauses together by induction on a bound `d` for the fibre degree of a *family* of
étale `φ_j : V_j ⟶ X`, and applies the induction hypothesis to `V_j ⨿ W_j ⟶ Y_j`, where `Y_j` is
the normalization of `X` in `V_j`. That morphism need not be surjective: over `X = 𝔸¹` with
`V_1 = (𝔸¹ ∖ 0) ⊔ (𝔸¹ ∖ 0)` and `V_2 = 𝔸¹`, both origins of `Y_1 = 𝔸¹ ⊔ 𝔸¹` are missed. The
induction here runs instead with a *single* chart, as Stacks 09YB does
(`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_chart_fibre_le`), and changes
that step in one place. 09YB covers `Y` by an extension of the cover of the open subspace `V`
glued with the reduced structure on `|Y| ∖ |V|`; over the interior of `|Y| ∖ |V|` that reduced
structure is the reduction of an open subspace, finite but not étale. So `V` is first enlarged
to `V⁺ = V ∪ O'`, where `O'` is a quasi-compact open of `|Y| ∖ closure |V|` containing its generic
points, and the cover of `V⁺` is the cover of `V` glued with the identity of `O'`
(`AlgebraicGeometry.Space.exists_cover_of_openSubspace_cover`). The closed complement of `V⁺`
then contains no generic point of `|Y|`.

**The étale locus is tracked pointwise and through generic points.** The inductive statement asks
for étaleness at every point lying over an open set containing all generic points, rather than
over a dense open subspace. Under the hypothesis on the irreducible components the two agree;
the pointwise form glues along coproducts (`AlgebraicGeometry.Space.exists_coprod_glue`) and
pushes down along the integral `π : Y ⟶ X`
(`AlgebraicGeometry.Space.exists_isOpen_genericPoints_subset_of_isIntegralHom`): a point of `Y`
over a generic point of `|X|` at which `π` is étale has a local ring of dimension `0`
(Stacks 0A4H), so it is itself generic (Stacks 0ADC). That `π` is étale over an open set
containing the generic points of `|X|` comes from Stacks 0BBC, which makes the chart finite over
a dense open subspace, together with the fact that over such an open subspace every point of
the compactification already lies in the chart
(`AlgebraicGeometry.Space.mem_range_of_isFinite_pullback_snd`, Stacks 04NX).

**Where the hypotheses are used.** Quasi-compactness of `X` gives the affine chart through a
prescribed one. Quasi-separatedness makes the chart quasi-compact (Tag 0ABS applies), bounds its
fibre degrees (Stacks 03JX, 07S8), and makes every space in sight decent. Finiteness of the
irreducible components is what lets `O'` be quasi-compact (Stacks 0G2D needs `V⁺ ⟶ Y`
quasi-compact), what makes the generic points of `|Y|` miss the boundary of `V`, and what turns
the generic-point form of the étale locus into a dense open subspace.

## References

* [Stacks Project, Tag 0GUL](https://stacks.math.columbia.edu/tag/0GUL)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 0G2D](https://stacks.math.columbia.edu/tag/0G2D)
* [Stacks Project, Tag 0BBC](https://stacks.math.columbia.edu/tag/0BBC)
* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Open immersions of presheaves on the big fppf site are stable under base change. -/
private theorem isOpenImmersion_snd_of_isPullback
    {F G H P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F}
    {snd : P ⟶ G} (sq : IsPullback fst snd f g) (hf : IsOpenImmersion B S hS f) :
    IsOpenImmersion B S hS snd :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sq hf

/-- Precomposing an integral morphism with an isomorphism gives an integral morphism. -/
private theorem isIntegralHom_comp_of_isIso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ G) [IsIso e] {g : G ⟶ H} (hg : IsIntegralHom B S hS g) :
    IsIntegralHom B S hS (e ≫ g) :=
  isIntegralHom_comp B S hS
    (isIntegralHom_of_isClosedImmersion B S hS _ (isClosedImmersion_of_isIso B S hS e)) hg

/-! ### Étaleness at a point -/

section EtaleAt

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Étaleness at a point can be witnessed by any open immersion.** If `k : W ⟶ X` is an open
immersion from an algebraic space and `k ≫ f` is étale, then `f` is étale at every point of the
image of `k`: the image of `k` is an open subspace isomorphic to `W`. -/
theorem isEtaleAt_of_isOpenImmersion {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (k : W ⟶ X) (hk : IsOpenImmersion B S hS k) (f : X ⟶ Y)
    (hkf : IsEtale B S hS (k ≫ f)) (w : points B S hS W) :
    IsEtaleAt B S hS f (pointsMap B S hS W k w) := by
  have _ : Mono k := mono_of_isOpenImmersion B S hS k hk
  refine ⟨Subfunctor.range k, isOpenSubspace_range_of_isAlgebraicSpace B S hS hW k hk,
    pointsMap B S hS W (Subfunctor.toRange k) w, ?_, ?_⟩
  · rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
  · rw [← inv_toRange_comp k, Category.assoc]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) hkf

/-- An étale morphism is étale at every point. -/
theorem isEtaleAt_of_isEtale (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hf : IsEtale B S hS f) (x : points B S hS X) : IsEtaleAt B S hS f x := by
  have h := isEtaleAt_of_isOpenImmersion B S hS hX (𝟙 X) (isOpenImmersion_of_isIso B S hS _) f
    (by rwa [Category.id_comp]) x
  rwa [pointsMap_id, id_eq] at h

/-- Étaleness at a point is preserved by composing with an étale morphism. -/
theorem IsEtaleAt.comp_isEtale {f : X ⟶ Y} {g : Y ⟶ Z} {x : points B S hS X}
    (hf : IsEtaleAt B S hS f x) (hg : IsEtale B S hS g) : IsEtaleAt B S hS (f ≫ g) x := by
  obtain ⟨U, hU, x', hx', he⟩ := hf
  exact ⟨U, hU, x', hx', by simpa only [Category.assoc] using isEtale_comp B S hS he hg⟩

/-- Étaleness at a point can be cancelled against an étale morphism on the right. -/
theorem IsEtaleAt.of_comp_isEtale (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) {f : X ⟶ Y} {g : Y ⟶ Z} {x : points B S hS X}
    (hfg : IsEtaleAt B S hS (f ≫ g) x) (hg : IsEtale B S hS g) : IsEtaleAt B S hS f x := by
  obtain ⟨U, hU, x', hx', he⟩ := hfg
  exact ⟨U, hU, x', hx', isEtale_of_isEtale_over B S hS hU.1 hY hZ (U.ι ≫ f) _ g he hg
    (Category.assoc _ _ _)⟩

/-- **Étaleness at a point is stable under composition.** -/
theorem IsEtaleAt.comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} {g : Y ⟶ Z} {x : points B S hS X}
    (hf : IsEtaleAt B S hS f x) (hg : IsEtaleAt B S hS g (pointsMap B S hS X f x)) :
    IsEtaleAt B S hS (f ≫ g) x := by
  obtain ⟨U₁, hU₁, x₁, hx₁, he₁⟩ := hf
  obtain ⟨U₂, hU₂, y₂, hy₂, he₂⟩ := hg
  set k : U₁.toFunctor ⟶ Y := U₁.ι ≫ f with hkdef
  set P : Subfunctor U₁.toFunctor := U₂.preimage k with hPdef
  have hP : IsOpenSubspace B S hS P := isOpenSubspace_preimage B S hS k U₂ hY hU₁.1 hU₂
  have hsq := Subfunctor.isPullback_preimage k U₂
  obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS hsq y₂ x₁
    (by rw [hy₂, hkdef, pointsMap_comp_apply, hx₁])
  have hfrom : IsEtale B S hS (U₂.fromPreimage k) :=
    isEtale_of_isEtale_over B S hS hP.1 hU₂.1 hY (U₂.fromPreimage k) (P.ι ≫ k) U₂.ι
      (isEtale_comp B S hS (isEtale_ι_of_isOpenSubspace hP) he₁) (isEtale_ι_of_isOpenSubspace hU₂)
      (Subfunctor.fromPreimage_ι U₂ k)
  have hmain : IsEtale B S hS ((P.ι ≫ U₁.ι) ≫ f ≫ g) := by
    have heq : (P.ι ≫ U₁.ι) ≫ f ≫ g = U₂.fromPreimage k ≫ U₂.ι ≫ g := by
      rw [← Category.assoc, Category.assoc P.ι, ← hkdef, ← Subfunctor.fromPreimage_ι U₂ k,
        Category.assoc]
    rw [heq]
    exact isEtale_comp B S hS hfrom he₂
  have h := isEtaleAt_of_isOpenImmersion B S hS hP.1 (P.ι ≫ U₁.ι)
    (isOpenImmersion_comp B S hS _ _ hP.2 hU₁.2) (f ≫ g) hmain w
  rwa [pointsMap_comp_apply, hw₂, hx₁] at h

/-- **Étaleness over an open subspace of the target, read pointwise.** If `f` is étale at every
point of its source lying over the open subspace `Ω`, then the base change of `f` to `Ω` is
étale. -/
theorem isEtale_pullback_fst_of_forall_isEtaleAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (Ω : Subfunctor X) (hΩ : IsOpenSubspace B S hS Ω)
    (f : Y ⟶ X)
    (h : ∀ y : points B S hS Y, pointsMap B S hS Y f y ∈
      Set.range (pointsMap B S hS Ω.toFunctor Ω.ι) → IsEtaleAt B S hS f y) :
    IsEtale B S hS (pullback.fst Ω.ι f) := by
  have hP : IsAlgebraicSpace B S hS (pullback Ω.ι f) :=
    isAlgebraicSpace_pullback B S hS Ω.ι f hΩ.1 hY hX
  have hsnd : IsOpenImmersion B S hS (pullback.snd Ω.ι f) :=
    isOpenImmersion_snd_of_isPullback B S hS (IsPullback.of_hasPullback Ω.ι f) hΩ.2
  refine isEtale_of_forall_isEtaleAt B S hS hP hΩ.1 _ fun w => ?_
  have hy : pointsMap B S hS Y f (pointsMap B S hS _ (pullback.snd Ω.ι f) w) ∈
      Set.range (pointsMap B S hS Ω.toFunctor Ω.ι) :=
    ⟨pointsMap B S hS _ (pullback.fst Ω.ι f) w, by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, pullback.condition]⟩
  have hcomp : IsEtaleAt B S hS (pullback.snd Ω.ι f ≫ f) w :=
    IsEtaleAt.comp B S hS hP hY (isEtaleAt_of_isEtale B S hS hP _
      (isEtale_of_isOpenImmersion B S hS hsnd) w) (h _ hy)
  rw [← pullback.condition] at hcomp
  exact hcomp.of_comp_isEtale B S hS hΩ.1 hX (isEtale_ι_of_isOpenSubspace hΩ)

/-- The converse: if the base change of `f` to the open subspace `Ω` is étale, then `f` is
étale at every point of its source lying over `Ω`. -/
theorem isEtaleAt_of_isEtale_pullback_fst (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (Ω : Subfunctor X) (hΩ : IsOpenSubspace B S hS Ω)
    (f : Y ⟶ X) (h : IsEtale B S hS (pullback.fst Ω.ι f)) (y : points B S hS Y)
    (hy : pointsMap B S hS Y f y ∈ Set.range (pointsMap B S hS Ω.toFunctor Ω.ι)) :
    IsEtaleAt B S hS f y := by
  have hP : IsAlgebraicSpace B S hS (pullback Ω.ι f) :=
    isAlgebraicSpace_pullback B S hS Ω.ι f hΩ.1 hY hX
  have hsnd : IsOpenImmersion B S hS (pullback.snd Ω.ι f) :=
    isOpenImmersion_snd_of_isPullback B S hS (IsPullback.of_hasPullback Ω.ι f) hΩ.2
  obtain ⟨ω, hω⟩ := hy
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback Ω.ι f) ω y
    hω
  have he : IsEtale B S hS (pullback.snd Ω.ι f ≫ f) := by
    rw [← pullback.condition]
    exact isEtale_comp B S hS h (isEtale_ι_of_isOpenSubspace hΩ)
  have := isEtaleAt_of_isOpenImmersion B S hS hP _ hsnd f he w
  rwa [hw] at this

end EtaleAt

/-! ### Generic points along étale morphisms -/

section GenericPoints

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A morphism étale at a point preserves the dimension of the local ring there**
(Stacks 0A4H, read at a point). -/
theorem IsEtaleAt.localRingDimension_eq (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} {x : points B S hS X}
    (h : IsEtaleAt B S hS f x) :
    localRingDimension B S hS (pointsMap B S hS X f x) = localRingDimension B S hS x := by
  obtain ⟨U, hU, x', rfl, he⟩ := h
  have h1 := localRingDimension_pointsMap_of_etale B S hS hU.1 hY (U.ι ≫ f) he x'
  have h2 := localRingDimension_pointsMap_of_etale B S hS hU.1 hX U.ι
    (isEtale_ι_of_isOpenSubspace hU) x'
  rw [pointsMap_comp_apply] at h1
  rw [h1, h2]

/-- **A point at which a morphism of quasi-separated algebraic spaces is étale is a generic
point exactly when its image is**: both conditions say that the local ring has dimension `0`
(Stacks 0ADC), and étaleness preserves that dimension (Stacks 0A4H). -/
theorem IsEtaleAt.mem_genericPoints_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) {f : X ⟶ Y} {x : points B S hS X}
    (h : IsEtaleAt B S hS f x) :
    pointsMap B S hS X f x ∈ genericPoints (points B S hS Y) ↔
      x ∈ genericPoints (points B S hS X) := by
  rw [← localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated B S hS hZ Y hY hYqs,
    ← localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated B S hS hZ X hX hXqs,
    h.localRingDimension_eq B S hS hX hY]

/-- A point of an open subspace of a quasi-separated space is generic when its image is. -/
private theorem mem_genericPoints_of_isOpenSubspace (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) (G : Subfunctor Y)
    (hG : IsOpenSubspace B S hS G) {x : points B S hS G.toFunctor}
    (hx : pointsMap B S hS G.toFunctor G.ι x ∈ genericPoints (points B S hS Y)) :
    x ∈ genericPoints (points B S hS G.toFunctor) :=
  ((isEtaleAt_of_isEtale B S hS hG.1 G.ι (isEtale_ι_of_isOpenSubspace hG) x).mem_genericPoints_iff
    B S hS hZ hG.1 hY (isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hYqs G hG.1) hYqs).1 hx

/-- **A quasi-compact étale chart of a quasi-separated algebraic space with finitely many
irreducible components has finitely many generic points, and finitely many irreducible
components.** The generic points of the chart lie over generic points of the space, of which
there are finitely many, and each fibre of the chart is finite (Stacks 03IJ). -/
theorem finite_genericPoints_of_isEtale_of_isQuasiCompactSpace (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hfin : (irreducibleComponents (points B S hS X)).Finite)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (hp : IsEtale B S hS p)
    (hpsep : IsSeparated B S hS p) (hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U)) :
    (genericPoints (points B S hS (yoneda.obj U))).Finite ∧
      (irreducibleComponents (points B S hS (yoneda.obj U))).Finite := by
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hXdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  have _ := t0Space_points_of_isDecentSpace B S hS hX hXdec
  have _ := quasiSober_points_of_isDecentSpace B S hS hX hXdec
  have hUdec : IsDecentSpace B S hS (yoneda.obj U) := isDecentSpace_yoneda B S hS U
  have _ := t0Space_points_of_isDecentSpace B S hS hUalg hUdec
  have _ := quasiSober_points_of_isDecentSpace B S hS hUalg hUdec
  have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hUalg hXqs
      (isQuasiSeparated_of_isSeparated B S hS hpsep)
  have hpqc : IsQuasiCompact B S hS p :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hXqs hUqc p
  have hgenX : (genericPoints (points B S hS X)).Finite := genericPoints.finite hfin
  have hsub : genericPoints (points B S hS (yoneda.obj U)) ⊆
      ⋃ η ∈ genericPoints (points B S hS X), pointsMap B S hS (yoneda.obj U) p ⁻¹' {η} := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨pointsMap B S hS (yoneda.obj U) p x, ?_, rfl⟩
    exact ((isEtaleAt_of_isEtale B S hS hUalg p hp x).mem_genericPoints_iff B S hS hZ hUalg hX
      hUqs hXqs).2 hx
  have hgenU : (genericPoints (points B S hS (yoneda.obj U))).Finite :=
    (hgenX.biUnion fun η _ => finite_fiber_pointsMap_of_etale_presentation B S hS X U p hp
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback p p).flip hpqc)
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback p p) hpqc) η).subset hsub
  refine ⟨hgenU, ?_⟩
  have : Finite (genericPoints (points B S hS (yoneda.obj U))) := hgenU.to_subtype
  exact Finite.of_equiv _ (genericPoints.equiv (α := points B S hS (yoneda.obj U)))

/-- **The push-down of an étale locus along an integral morphism (item (e4)).** Let
`π : Y ⟶ X` be an integral morphism of quasi-separated algebraic spaces, étale at every point
lying over an open set `Ω ⊆ |X|` which contains every generic point of `|X|`, and let `D ⊆ |Y|`
be open and contain every generic point of `|Y|`. Then the set of points of `Ω` over which
every point of `Y` lies in `D` is open, contains every generic point of `|X|`, and over it `π`
is étale.

Openness is closedness of `π` (Stacks 0415, 04XU). A point of `Y` over a generic point of `|X|`
lying in `Ω` is a point at which `π` is étale, so it is itself generic (Stacks 0ADC, 0A4H),
hence in `D`. -/
theorem exists_isOpen_genericPoints_subset_of_isIntegralHom (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) (π : Y ⟶ X)
    (hπ : IsIntegralHom B S hS π) (Ω : Set (points B S hS X)) (hΩ : IsOpen Ω)
    (hΩgen : genericPoints (points B S hS X) ⊆ Ω)
    (hπet : ∀ y, pointsMap B S hS Y π y ∈ Ω → IsEtaleAt B S hS π y)
    (D : Set (points B S hS Y)) (hD : IsOpen D)
    (hDgen : genericPoints (points B S hS Y) ⊆ D) :
    IsOpen (Ω ∩ (pointsMap B S hS Y π '' Dᶜ)ᶜ) ∧
      genericPoints (points B S hS X) ⊆ Ω ∩ (pointsMap B S hS Y π '' Dᶜ)ᶜ ∧
      ∀ y, pointsMap B S hS Y π y ∈ Ω ∩ (pointsMap B S hS Y π '' Dᶜ)ᶜ →
        y ∈ D ∧ IsEtaleAt B S hS π y := by
  have hcl : IsClosedMap (pointsMap B S hS Y π) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS π
      (universallyClosed_of_isIntegralHom B S hS hY hX hπ X hX (𝟙 X))
  refine ⟨hΩ.inter (hcl _ hD.isClosed_compl).isOpen_compl, fun η hη => ⟨hΩgen hη, ?_⟩, ?_⟩
  · rintro ⟨y, hyD, rfl⟩
    exact hyD (hDgen (((hπet y (hΩgen hη)).mem_genericPoints_iff B S hS hZ hY hX hYqs hXqs).1
      hη))
  · rintro y ⟨hyΩ, hyD⟩
    refine ⟨?_, hπet y hyΩ⟩
    by_contra hy
    exact hyD ⟨y, hy, rfl⟩

end GenericPoints

/-! ### Covers assembled from pieces -/

section Pieces

variable {X T U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Étaleness at a point descends from an open immersion into the source. -/
theorem isEtaleAt_of_isEtaleAt_isOpenImmersion_comp {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : W ⟶ T) (hk : IsOpenImmersion B S hS k) (f : T ⟶ X) (w : points B S hS W)
    (h : IsEtaleAt B S hS (k ≫ f) w) : IsEtaleAt B S hS f (pointsMap B S hS W k w) := by
  obtain ⟨V, hV, w', rfl, he⟩ := h
  have := isEtaleAt_of_isOpenImmersion B S hS hV.1 (V.ι ≫ k)
    (isOpenImmersion_comp B S hS _ _ hV.2 hk) f (by simpa only [Category.assoc] using he) w'
  rwa [pointsMap_comp_apply] at this

/-- **Zariski-local factorization is local on the source for open immersions.** If every point
of `h_Y` lies in the image of an open immersion `k : h_{Y'} ⟶ h_Y` along which `f` factors
Zariski locally through `q`, then `f` factors Zariski locally through `q`. -/
theorem factorsZariskiLocallyThrough_of_forall_isOpenImmersion (q : U ⟶ X)
    (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X)
    (h : ∀ y : points B S hS (yoneda.obj Y), ∃ (Y' : BigFppfOver B S hS)
      (k : yoneda.obj Y' ⟶ yoneda.obj Y) (y' : points B S hS (yoneda.obj Y')),
      IsOpenImmersion B S hS k ∧ pointsMap B S hS _ k y' = y ∧
        FactorsZariskiLocallyThrough B S hS q Y' (k ≫ f)) :
    FactorsZariskiLocallyThrough B S hS q Y f := by
  intro y
  obtain ⟨Y', k, y', hk, rfl, hfac⟩ := h y
  obtain ⟨W', hW', hW'rep, ⟨w', hw'⟩, g', hg'⟩ := hfac y'
  set m : W'.toFunctor ⟶ yoneda.obj Y := W'.ι ≫ k with hmdef
  have hm : IsOpenImmersion B S hS m := isOpenImmersion_comp B S hS _ _ hW'.2 hk
  have _ : Mono m := mono_of_isOpenImmersion B S hS m hm
  refine ⟨Subfunctor.range m, isOpenSubspace_range_of_isAlgebraicSpace B S hS hW'.1 m hm,
    isRepresentable_of_natIso _ (asIso (Subfunctor.toRange m)), ⟨pointsMap B S hS _
      (Subfunctor.toRange m) w', ?_⟩, inv (Subfunctor.toRange m) ≫ g', ?_⟩
  · rw [← pointsMap_comp_apply, Subfunctor.toRange_ι, hmdef, pointsMap_comp_apply, hw']
  · rw [← inv_toRange_comp m, Category.assoc, Category.assoc]
    exact hg'.symm ▸ rfl

/-- The two summand inclusions of a binary coproduct of the site are open immersions. -/
theorem isOpenImmersion_yoneda_map_coprodPairIncl (Z₁ Z₂ : BigFppfOver B S hS)
    (b : ULift.{u} Bool) :
    IsOpenImmersion B S hS (yoneda.map (coprodPairIncl B S hS Z₁ Z₂ b)) :=
  isOpenImmersion_yoneda_map B S hS _
    (isOpenImmersion_toScheme_map_cofan (isColimit_cofan_coprodPair B S hS Z₁ Z₂) b)

/-- Every point of a binary coproduct of the site comes from one of the two summands. -/
theorem exists_points_coprodPairIncl (Z₁ Z₂ : BigFppfOver B S hS)
    (z : points B S hS (yoneda.obj (Z₁ ⨿ Z₂))) :
    ∃ (b : ULift.{u} Bool) (z' : points B S hS (yoneda.obj (coprodPairObj B S hS Z₁ Z₂ b))),
      pointsMap B S hS _ (yoneda.map (coprodPairIncl B S hS Z₁ Z₂ b)) z' = z := by
  have hcov := iUnion_range_toScheme_map_cofan (isColimit_cofan_coprodPair B S hS Z₁ Z₂)
  obtain ⟨-, ⟨b, rfl⟩, x', hx'⟩ := hcov.symm ▸ Set.mem_univ (pointsToScheme B S hS _ z)
  obtain ⟨z', rfl⟩ := surjective_pointsToScheme B S hS _ x'
  refine ⟨b, z', injective_pointsToScheme B S hS _ ?_⟩
  rw [pointsToScheme_pointsMap_yoneda]
  exact hx'

/-- **The glueing of two covers by a binary coproduct of the site, with what it inherits.**
Morphisms `p₁ : h_{Z₁} ⟶ T` and `p₂ : h_{Z₂} ⟶ T` assemble into `c : h_{Z₁ ⨿ Z₂} ⟶ T`, which
is integral when both are, whose point range is the union of theirs, which is étale at every
point over a set `D` when both are, and which factors Zariski locally through `q : U ⟶ X` after
composing with `π : T ⟶ X` when both do. -/
theorem exists_coprod_glue (hT : IsAlgebraicSpace B S hS T) (Z₁ Z₂ : BigFppfOver B S hS)
    (p₁ : yoneda.obj Z₁ ⟶ T) (p₂ : yoneda.obj Z₂ ⟶ T) :
    ∃ c : yoneda.obj (Z₁ ⨿ Z₂) ⟶ T,
      yoneda.map (coprod.inl : Z₁ ⟶ Z₁ ⨿ Z₂) ≫ c = p₁ ∧
      yoneda.map (coprod.inr : Z₂ ⟶ Z₁ ⨿ Z₂) ≫ c = p₂ ∧
      (IsIntegralHom B S hS p₁ → IsIntegralHom B S hS p₂ → IsIntegralHom B S hS c) ∧
      Set.range (pointsMap B S hS _ c) =
        Set.range (pointsMap B S hS _ p₁) ∪ Set.range (pointsMap B S hS _ p₂) ∧
      (∀ D : Set (points B S hS T),
        (∀ z, pointsMap B S hS _ p₁ z ∈ D → IsEtaleAt B S hS p₁ z) →
        (∀ z, pointsMap B S hS _ p₂ z ∈ D → IsEtaleAt B S hS p₂ z) →
        ∀ z, pointsMap B S hS _ c z ∈ D → IsEtaleAt B S hS c z) ∧
      (∀ (q : U ⟶ X) (π : T ⟶ X),
        FactorsZariskiLocallyThrough B S hS q Z₁ (p₁ ≫ π) →
        FactorsZariskiLocallyThrough B S hS q Z₂ (p₂ ≫ π) →
        FactorsZariskiLocallyThrough B S hS q (Z₁ ⨿ Z₂) (c ≫ π)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let Ts : Sheaf J (Type u) := ⟨T, hT.isSheaf⟩
  have hV : IsColimit (Cofan.mk (Z₁ ⨿ Z₂) (coprodPairIncl B S hS Z₁ Z₂)) :=
    isColimit_cofan_coprodPair B S hS Z₁ Z₂
  have hY : IsColimit (Cofan.mk (J.yoneda.obj (Z₁ ⨿ Z₂))
      fun b => J.yoneda.map (coprodPairIncl B S hS Z₁ Z₂ b)) :=
    BigFppfOver.isColimit_yoneda_cofan B S hS (coprodPairObj B S hS Z₁ Z₂)
      (coprodPairIncl B S hS Z₁ Z₂) hV
  let fam : ∀ b : ULift.{u} Bool, yoneda.obj (coprodPairObj B S hS Z₁ Z₂ b) ⟶ T := fun b =>
    match b with
    | ⟨false⟩ => p₁
    | ⟨true⟩ => p₂
  let tgt : ∀ b, J.yoneda.obj (coprodPairObj B S hS Z₁ Z₂ b) ⟶ Ts := fun b => ⟨fam b⟩
  let h : J.yoneda.obj (Z₁ ⨿ Z₂) ⟶ Ts := Cofan.IsColimit.desc hY tgt
  have hfac : ∀ b, yoneda.map (coprodPairIncl B S hS Z₁ Z₂ b) ≫ h.hom = fam b := fun b =>
    congrArg (fun k : J.yoneda.obj (coprodPairObj B S hS Z₁ Z₂ b) ⟶ Ts => k.hom)
      (Cofan.IsColimit.fac hY tgt b)
  have hfac₁ : yoneda.map (coprod.inl : Z₁ ⟶ Z₁ ⨿ Z₂) ≫ h.hom = p₁ := hfac ⟨false⟩
  have hfac₂ : yoneda.map (coprod.inr : Z₂ ⟶ Z₁ ⨿ Z₂) ≫ h.hom = p₂ := hfac ⟨true⟩
  have hpieces : ∀ z : points B S hS (yoneda.obj (Z₁ ⨿ Z₂)),
      (∃ z₁, pointsMap B S hS _ (yoneda.map (coprod.inl : Z₁ ⟶ Z₁ ⨿ Z₂)) z₁ = z) ∨
        (∃ z₂, pointsMap B S hS _ (yoneda.map (coprod.inr : Z₂ ⟶ Z₁ ⨿ Z₂)) z₂ = z) := by
    intro z
    obtain ⟨b, z', hz'⟩ := exists_points_coprodPairIncl B S hS Z₁ Z₂ z
    rcases b with ⟨_ | _⟩
    · exact Or.inl ⟨z', hz'⟩
    · exact Or.inr ⟨z', hz'⟩
  have hoi₁ : IsOpenImmersion B S hS (yoneda.map (coprod.inl : Z₁ ⟶ Z₁ ⨿ Z₂)) :=
    isOpenImmersion_yoneda_map_coprodPairIncl B S hS Z₁ Z₂ ⟨false⟩
  have hoi₂ : IsOpenImmersion B S hS (yoneda.map (coprod.inr : Z₂ ⟶ Z₁ ⨿ Z₂)) :=
    isOpenImmersion_yoneda_map_coprodPairIncl B S hS Z₁ Z₂ ⟨true⟩
  refine ⟨h.hom, hfac₁, hfac₂, fun h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · refine isIntegralHom_coproduct B S hS
      (fun b => yoneda.obj (coprodPairObj B S hS Z₁ Z₂ b))
      (fun b => isAlgebraicSpace_yoneda B S hS (coprodPairObj B S hS Z₁ Z₂ b)) hT
      (J.yoneda.obj (Z₁ ⨿ Z₂))
      (fun b => J.yoneda.map (coprodPairIncl B S hS Z₁ Z₂ b)) hY fam h.hom hfac ?_
    intro b
    rcases b with ⟨_ | _⟩
    · exact h₁
    · exact h₂
  · refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro _ ⟨z, rfl⟩
      rcases hpieces z with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩
      · exact Or.inl ⟨z₁, by rw [← pointsMap_comp_apply, hfac₁]⟩
      · exact Or.inr ⟨z₂, by rw [← pointsMap_comp_apply, hfac₂]⟩
    · rintro _ (⟨z₁, rfl⟩ | ⟨z₂, rfl⟩)
      · exact ⟨_, by rw [← pointsMap_comp_apply, hfac₁]⟩
      · exact ⟨_, by rw [← pointsMap_comp_apply, hfac₂]⟩
  · intro D hD₁ hD₂ z hz
    rcases hpieces z with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩
    · refine isEtaleAt_of_isEtaleAt_isOpenImmersion_comp B S hS _ hoi₁ _ z₁ ?_
      rw [hfac₁]
      exact hD₁ z₁ (by rwa [← pointsMap_comp_apply, hfac₁] at hz)
    · refine isEtaleAt_of_isEtaleAt_isOpenImmersion_comp B S hS _ hoi₂ _ z₂ ?_
      rw [hfac₂]
      exact hD₂ z₂ (by rwa [← pointsMap_comp_apply, hfac₂] at hz)
  · intro q π hq₁ hq₂
    refine factorsZariskiLocallyThrough_of_forall_isOpenImmersion B S hS q _ _ fun z => ?_
    rcases hpieces z with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩
    · exact ⟨Z₁, _, z₁, hoi₁, rfl, by rwa [← Category.assoc, hfac₁]⟩
    · exact ⟨Z₂, _, z₂, hoi₂, rfl, by rwa [← Category.assoc, hfac₂]⟩

end Pieces

/-! ### Over a dense open where the chart is finite, the compactification adds nothing -/

section FiniteLocus

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Over an open subspace of `X` over which a chart `p = j ≫ π` is finite, every point of `Y`
lies in the image of the dense open immersion `j`.** The base change of `j` over the preimage of
the open subspace is an open immersion with dense point range whose composite with the integral
(hence separated) base change of `π` is the finite base change of `p`, so it is an isomorphism
by Stacks 04NX. -/
theorem mem_range_of_isFinite_pullback_snd (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X)
    (j : yoneda.obj U ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (hjdense : DenseRange (pointsMap B S hS (yoneda.obj U) j)) (π : Y ⟶ X)
    (hπ : IsIntegralHom B S hS π) (hjπ : j ≫ π = p) (X₁ : Subfunctor X)
    (hX₁ : IsOpenSubspace B S hS X₁) (hfin : IsFinite B S hS (pullback.snd p X₁.ι))
    (y : points B S hS Y)
    (hy : pointsMap B S hS Y π y ∈ Set.range (pointsMap B S hS X₁.toFunctor X₁.ι)) :
    y ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) := by
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  set w₁ := pullback.fst π X₁.ι with hw₁def
  set w₂ := pullback.snd π X₁.ι with hw₂def
  have hsqW : IsPullback w₁ w₂ π X₁.ι := IsPullback.of_hasPullback π X₁.ι
  have hWalg : IsAlgebraicSpace B S hS (pullback π X₁.ι) :=
    isAlgebraicSpace_pullback B S hS π X₁.ι hY hX₁.1 hX
  have hw₁ : IsOpenImmersion B S hS w₁ :=
    isOpenImmersion_snd_of_isPullback B S hS hsqW.flip hX₁.2
  set m := pullback.fst w₁ j with hmdef
  set a := pullback.snd w₁ j with hadef
  have hsqA : IsPullback m a w₁ j := IsPullback.of_hasPullback w₁ j
  have hAalg : IsAlgebraicSpace B S hS (pullback w₁ j) :=
    isAlgebraicSpace_pullback B S hS w₁ j hWalg hUalg hY
  have hm : IsOpenImmersion B S hS m := isOpenImmersion_snd_of_isPullback B S hS hsqA.flip hj
  have hmdense : DenseRange (pointsMap B S hS _ m) :=
    denseRange_pointsMap_of_isPullback_of_denseRange B S hS hsqA hw₁ hjdense
  have hpaste : IsPullback a (m ≫ w₂) p X₁.ι := by
    have h := (hsqA.paste_horiz hsqW.flip).flip
    rwa [hjπ] at h
  have hPalg : IsAlgebraicSpace B S hS (pullback p X₁.ι) :=
    isAlgebraicSpace_pullback B S hS p X₁.ι hUalg hX₁.1 hX
  have hclosed : UniversallyClosed B S hS (m ≫ w₂) := by
    rw [← hpaste.isoPullback_hom_snd]
    exact universallyClosed_comp B S hS hPalg hX₁.1 _ _
      (universallyClosed_of_isIso B S hS _)
      (universallyClosed_of_isFinite B S hS hPalg hX₁.1 hfin)
  have hw₂sep : IsSeparated B S hS w₂ :=
    isSeparated_of_isIntegralHom B S hS w₂ hWalg hX₁.1
      (isIntegralHom_of_isPullback B S hS hsqW hπ)
  have _ : IsIso m :=
    isIso_of_isOpenImmersion_of_denseRange_of_universallyClosed B S hS hAalg hWalg hX₁.1 m hm
      w₂ hw₂sep hclosed hmdense
  obtain ⟨x₁, hx₁⟩ := hy
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hsqW y x₁ hx₁.symm
  obtain ⟨z, rfl⟩ := pointsMap_surjective_of_isIso B S hS m w
  refine ⟨pointsMap B S hS _ a z, ?_⟩
  rw [← pointsMap_comp_apply, ← hsqA.w, pointsMap_comp_apply, hw]

end FiniteLocus

/-! ### From an étale locus containing the generic points to the form of `h2` -/

section Conclusion

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {X V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A cover which is étale at every point over an open set containing every generic point
satisfies the first clause of `AlgebraicGeometry.Space.ExistsIntegralSchemeCoverEtaleRefining`.**
The open set is the point set of an open subspace (Stacks 03BZ); it is dense because it contains
every generic point of a decent space (Stacks 0ADC); and étaleness at the points over it is
étaleness of the base change by `AlgebraicGeometry.Space.isEtale_pullback_fst_of_forall_isEtaleAt`.
-/
theorem existsIntegralSchemeCoverEtaleRefining_of_genericPoints_subset
    (hX : IsAlgebraicSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (q : V ⟶ X) (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (hfsurj : IsSurjective B S hS f)
    (hfint : IsIntegralHom B S hS f) (D : Set (points B S hS X)) (hD : IsOpen D)
    (hDgen : genericPoints (points B S hS X) ⊆ D)
    (hfet : ∀ y, pointsMap B S hS _ f y ∈ D → IsEtaleAt B S hS f y)
    (hfac : FactorsZariskiLocallyThrough B S hS q Y f) :
    ExistsIntegralSchemeCoverEtaleRefining B S hS q := by
  have hdec : IsDecentSpace B S hS X := isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  have _ := quasiSober_points_of_isDecentSpace B S hS hX hdec
  have hΩ := isOpenSubspace_openSubspaceOfPoints B S hS hX D hD
  have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS D (F := X)
  refine ⟨Y, f, openSubspaceOfPoints B S hS X D, ⟨hfsurj, hfint, hΩ, ?_, ?_⟩, hfac⟩
  · rw [hrange]
    exact dense_iff_closure_eq.2 (Set.univ_subset_iff.1
      ((genericPoints.closure (α := points B S hS X)) ▸ closure_mono hDgen))
  · refine isEtale_pullback_fst_of_forall_isEtaleAt B S hS hX (isAlgebraicSpace_yoneda B S hS Y)
      _ hΩ f fun y hy => hfet y ?_
    rwa [hrange] at hy

end Conclusion

/-! ### Small lemmas on local factorizations -/

section Factor

variable {X X' U U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism which factors globally through `q` factors through it Zariski locally. -/
theorem factorsZariskiLocallyThrough_of_eq_comp (q : U ⟶ X) (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (s : yoneda.obj Y ⟶ U) (h : f = s ≫ q) :
    FactorsZariskiLocallyThrough B S hS q Y f := by
  intro y
  refine ⟨⊤, isOpenSubspace_top (isAlgebraicSpace_yoneda B S hS Y),
    isRepresentable_of_natIso _ (asIso (⊤ : Subfunctor (yoneda.obj Y)).ι).symm,
    ⟨pointsMap B S hS _ (inv (⊤ : Subfunctor (yoneda.obj Y)).ι) y, ?_⟩,
    (⊤ : Subfunctor (yoneda.obj Y)).ι ≫ s, ?_⟩
  · rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]
  · rw [h, Category.assoc]

/-- A Zariski-local factorization through `q` composes with a commutative square. -/
theorem FactorsZariskiLocallyThrough.comp {q : U ⟶ X} {Y : BigFppfOver B S hS}
    {f : yoneda.obj Y ⟶ X} (h : FactorsZariskiLocallyThrough B S hS q Y f) (r : X ⟶ X')
    (q' : U' ⟶ X') (s : U ⟶ U') (hrs : q ≫ r = s ≫ q') :
    FactorsZariskiLocallyThrough B S hS q' Y (f ≫ r) := by
  intro y
  obtain ⟨W, hW, hWrep, hy, g, hg⟩ := h y
  exact ⟨W, hW, hWrep, hy, g ≫ s, by rw [← Category.assoc, hg, Category.assoc, hrs,
    Category.assoc]⟩

/-- A subfunctor whose point set lies in the image of a representable open immersion `j` factors
through `j`. -/
theorem exists_comp_eq_ι_of_range_subset {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U₀ : BigFppfOver B S hS) (j : yoneda.obj U₀ ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (G : Subfunctor Y)
    (hsub : Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆
      Set.range (pointsMap B S hS (yoneda.obj U₀) j)) :
    ∃ s : G.toFunctor ⟶ yoneda.obj U₀, s ≫ j = G.ι := by
  have _ : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hle : G ≤ Subfunctor.range j :=
    le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_range_of_isOpenImmersion U₀ j hj)
      (by rw [range_pointsMap_ι_range]; exact hsub)
  refine ⟨Subfunctor.homOfLe hle ≫ inv (Subfunctor.toRange j), ?_⟩
  rw [Category.assoc, ← asIso_inv, inv_toRange_comp, Subfunctor.homOfLe_ι]

end Factor

/-! ### The étale locus of the compactification of a chart -/

section ChartLocus

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The compactification `π : Y ⟶ X` of a chart `p = j ≫ π` is étale over an open set of
`|X|` containing every generic point.** Stacks 0BBC makes `p` finite over a dense open subspace;
over it every point of `Y` lies in `j(U)` by
`AlgebraicGeometry.Space.mem_range_of_isFinite_pullback_snd`, and at a point of `j(U)` the
morphism `π` is étale because `j ≫ π = p` is. -/
theorem exists_isOpen_genericPoints_subset_isEtaleAt_of_chart (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hXfin : (irreducibleComponents (points B S hS X)).Finite)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (hpet : IsEtale B S hS p)
    (hpsep : IsSeparated B S hS p) (hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U))
    (hY : IsAlgebraicSpace B S hS Y) (j : yoneda.obj U ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (hjdense : DenseRange (pointsMap B S hS (yoneda.obj U) j)) (π : Y ⟶ X)
    (hπ : IsIntegralHom B S hS π) (hjπ : j ≫ π = p) :
    ∃ Ω : Set (points B S hS X), IsOpen Ω ∧ genericPoints (points B S hS X) ⊆ Ω ∧
      ∀ y, pointsMap B S hS Y π y ∈ Ω → IsEtaleAt B S hS π y := by
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hXdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  have _ := t0Space_points_of_isDecentSpace B S hS hX hXdec
  have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hUalg hXqs
      (isQuasiSeparated_of_isSeparated B S hS hpsep)
  obtain ⟨hUgen, -⟩ := finite_genericPoints_of_isEtale_of_isQuasiCompactSpace B S hS hZ hX hXqs
    hXfin U p hpet hpsep hUqc
  have hzeroX : {x : points B S hS X | localRingDimension B S hS x = 0} =
      genericPoints (points B S hS X) := by
    ext x
    exact localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated B S hS hZ X hX hXqs x
  have hzeroU : {x : points B S hS (yoneda.obj U) | localRingDimension B S hS x = 0} =
      genericPoints (points B S hS (yoneda.obj U)) := by
    ext x
    exact localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated B S hS hZ _ hUalg
      hUqs x
  obtain ⟨X₁, hX₁, hX₁dense, hX₁fin⟩ := exists_isDenseOpenSubspace_isFinite_pullback_snd B S hS
    hUalg hX p (isLocallyOfFiniteType_of_isEtale' B S hS p hpet) hXdec
    (by rw [hzeroU]; exact hUgen) (by rw [hzeroX]; exact genericPoints.finite hXfin)
    (by
      ext u
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [localRingDimension_pointsMap_of_etale B S hS hUalg hX p hpet u])
    (Or.inr hpsep)
  refine ⟨Set.range (pointsMap B S hS X₁.toFunctor X₁.ι),
    isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hX X₁ hX₁, fun η hη =>
      mem_of_mem_genericPoints_of_dense
        (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hX X₁ hX₁) hX₁dense hXfin hη, ?_⟩
  intro y hy
  obtain ⟨u, rfl⟩ := mem_range_of_isFinite_pullback_snd B S hS hX hY U p j hj hjdense π hπ hjπ
    X₁ hX₁ hX₁fin y hy
  exact isEtaleAt_of_isOpenImmersion B S hS hUalg j hj π (by rw [hjπ]; exact hpet) u

end ChartLocus

/-! ### The inductive step on `Y`: the enlargement `V⁺` -/

section Enlargement

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The inductive step of Stacks 0GUL on the compactification, repaired by the enlargement
`V⁺`.** Let `Y` be a quasi-separated algebraic space with finitely many irreducible components,
let `j : h_U ⟶ Y` be an open immersion and `V ⊆ Y` a quasi-compact open subspace with
`j(U) ∪ |V| = |Y|`, and let `c_V : h_{Z_V} ⟶ V` be an integral surjective cover étale over an open
`D_V ⊆ |V|` containing the generic points of `|V|`, which after `V ⟶ Y ⟶ X` factors Zariski
locally through `p = j ≫ π`. Then `Y` has an integral surjective scheme cover, étale over an open
set containing every generic point of `|Y|`, which after `π` factors Zariski locally through `p`.

`O := |Y| ∖ closure |V|` lies in `j(U)` and is a scheme; it is shrunk to a quasi-compact open `O'`
containing its generic points, and `V⁺ := |V| ∪ |O'|` carries the cover `Z_V ⨿ O'`, which is
integral because `V` and `O'` are clopen in `V⁺`. Stacks 0G2D extends that cover to an integral
`ν : C ⟶ Y` with `C ×_Y V⁺ ≅ Z_V ⨿ O'`; `C` is a scheme, being covered by that open and by the
part over `j(U)`. The reduced closed complement of `V⁺` lies in `j(U)` and is a scheme, and
`C ⨿ (|Y| ∖ |V⁺|)_red` is the cover: over `V⁺` it is `Z_V ⨿ O'`, étale over `D_V ∪ |O'|`, and
every generic point of `|Y|` lies in `V` or in `O`, so in `D_V ∪ |O'|`. -/
theorem exists_cover_of_openSubspace_cover (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hYfin : (irreducibleComponents (points B S hS Y)).Finite)
    (U : BigFppfOver B S hS) (j : yoneda.obj U ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (π : Y ⟶ X) (p : yoneda.obj U ⟶ X) (hjπ : j ≫ π = p)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hcov : Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
      Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.univ)
    (ZV : BigFppfOver B S hS) (cV : yoneda.obj ZV ⟶ V.toFunctor)
    (hcVsurj : IsSurjective B S hS cV) (hcVint : IsIntegralHom B S hS cV)
    (DV : Set (points B S hS V.toFunctor)) (hDVopen : IsOpen DV)
    (hDVgen : genericPoints (points B S hS V.toFunctor) ⊆ DV)
    (hcVet : ∀ z, pointsMap B S hS _ cV z ∈ DV → IsEtaleAt B S hS cV z)
    (hcVfac : FactorsZariskiLocallyThrough B S hS p ZV (cV ≫ V.ι ≫ π)) :
    ∃ (C : BigFppfOver B S hS) (F : yoneda.obj C ⟶ Y) (DY : Set (points B S hS Y)),
      IsSurjective B S hS F ∧ IsIntegralHom B S hS F ∧ IsOpen DY ∧
      genericPoints (points B S hS Y) ⊆ DY ∧
      (∀ z, pointsMap B S hS _ F z ∈ DY → IsEtaleAt B S hS F z) ∧
      FactorsZariskiLocallyThrough B S hS p C (F ≫ π) := by
  classical
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hVemb := isOpenEmbedding_pointsMap_ι B S hS hV
  have hVopenPts : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY V hV
  -- the open subspace `O` and the density of `V ∪ O`
  obtain ⟨O, Vp₀, hO, hOrep, hVp₀, -, -, -, hVp₀range, hdisjO, hVp₀dense, -⟩ :=
    exists_denseOpenSubspace_representableComplement_of_cover B S hS hY U j hj V hV hcov
  have hgenVO : ∀ η ∈ genericPoints (points B S hS Y),
      η ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∪
        Set.range (pointsMap B S hS O.toFunctor O.ι) := by
    intro η hη
    have h := mem_of_mem_genericPoints_of_dense
      (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY Vp₀ hVp₀) hVp₀dense hYfin hη
    rwa [hVp₀range] at h
  -- `O'`: a quasi-compact open of `O` containing its generic points
  have hOqs := isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hYqs O hO.1
  have hOemb := isOpenEmbedding_pointsMap_ι B S hS hO
  have hOfin : (irreducibleComponents (points B S hS O.toFunctor)).Finite :=
    finite_irreducibleComponents_of_isOpenEmbedding _ hOemb hYfin
  have htopdense : Dense (Set.range (pointsMap B S hS (⊤ : Subfunctor O.toFunctor).toFunctor
      (⊤ : Subfunctor O.toFunctor).ι)) := by
    rw [(pointsMap_surjective_of_isIso B S hS _).range_eq]
    exact dense_univ
  obtain ⟨O₁, -, hO₁, hO₁qc, hO₁dense, -⟩ :=
    exists_isOpenSubspace_isQuasiCompactSpace_dense_factorization B S hS hZ hO.1 hOqs hOfin ⊤
      (isOpenSubspace_top hO.1) htopdense
  set m₁ : O₁.toFunctor ⟶ Y := O₁.ι ≫ O.ι with hm₁def
  have hm₁ : IsOpenImmersion B S hS m₁ := isOpenImmersion_comp B S hS _ _ hO₁.2 hO.2
  have _ : Mono m₁ := mono_of_isOpenImmersion B S hS m₁ hm₁
  set O' : Subfunctor Y := Subfunctor.range m₁ with hO'def
  have hO' : IsOpenSubspace B S hS O' :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS hO₁.1 m₁ hm₁
  have hO'range : Set.range (pointsMap B S hS O'.toFunctor O'.ι) =
      pointsMap B S hS O.toFunctor O.ι '' Set.range (pointsMap B S hS O₁.toFunctor O₁.ι) := by
    rw [range_pointsMap_ι_range, hm₁def, pointsMap_comp, Set.range_comp]
  have hO'qc : IsQuasiCompactSpace B S hS O'.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (Subfunctor.toRange m₁)) hO₁qc
  have hO₁rep : O₁.toFunctor.IsRepresentable :=
    isRepresentable_of_isOpenSubspace B S hS hOrep O₁ hO₁
  have hO'rep : O'.toFunctor.IsRepresentable :=
    isRepresentable_of_natIso _ (asIso (Subfunctor.toRange m₁))
  have hO'sub : Set.range (pointsMap B S hS O'.toFunctor O'.ι) ⊆
      Set.range (pointsMap B S hS O.toFunctor O.ι) := by
    rw [hO'range]
    exact Set.image_subset_range _ _
  have hdisj' : Disjoint (Set.range (pointsMap B S hS V.toFunctor V.ι))
      (Set.range (pointsMap B S hS O'.toFunctor O'.ι)) := hdisjO.mono_right hO'sub
  have hgen : genericPoints (points B S hS Y) ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι) ∪
      Set.range (pointsMap B S hS O'.toFunctor O'.ι) := by
    intro η hη
    rcases hgenVO η hη with h | ⟨o, rfl⟩
    · exact Or.inl h
    · refine Or.inr ?_
      have ho₁ := mem_of_mem_genericPoints_of_dense
        (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hO.1 O₁ hO₁) hO₁dense hOfin
        (mem_genericPoints_of_isOpenSubspace B S hS hZ hY hYqs O hO hη)
      rw [hO'range]
      exact ⟨o, ho₁, rfl⟩
  have hoffV : ∀ x, x ∉ Set.range (pointsMap B S hS V.toFunctor V.ι) →
      x ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) := by
    intro x hx
    have hmem : x ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
        Set.range (pointsMap B S hS V.toFunctor V.ι) := hcov ▸ Set.mem_univ x
    rcases hmem with h | h
    · exact h
    · exact absurd h hx
  have hO'j : Set.range (pointsMap B S hS O'.toFunctor O'.ι) ⊆
      Set.range (pointsMap B S hS (yoneda.obj U) j) :=
    fun x hx => hoffV x (Set.disjoint_right.1 hdisj' hx)
  -- `V⁺`
  have hO'openPts : IsOpen (Set.range (pointsMap B S hS O'.toFunctor O'.ι)) :=
    isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY O' hO'
  set Tplus : Set (points B S hS Y) := Set.range (pointsMap B S hS V.toFunctor V.ι) ∪
    Set.range (pointsMap B S hS O'.toFunctor O'.ι) with hTplusdef
  set Vp : Subfunctor Y := openSubspaceOfPoints B S hS Y Tplus with hVpdef
  have hVp : IsOpenSubspace B S hS Vp :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY Tplus (hVopenPts.union hO'openPts)
  have hVprange : Set.range (pointsMap B S hS Vp.toFunctor Vp.ι) = Tplus :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Tplus
  have hVle : V ≤ Vp := le_of_range_pointsMap_ι_subset B S hS hVp
    (by rw [hVprange]; exact Set.subset_union_left)
  have hO'le : O' ≤ Vp := le_of_range_pointsMap_ι_subset B S hS hVp
    (by rw [hVprange]; exact Set.subset_union_right)
  have hcompact : ∀ G : Subfunctor Y, IsAlgebraicSpace B S hS G.toFunctor →
      IsQuasiCompactSpace B S hS G.toFunctor →
      IsCompact (Set.range (pointsMap B S hS G.toFunctor G.ι)) := fun G hG hGqc => by
    have _ := (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hG).1 hGqc
    exact isCompact_range (continuous_pointsMap B S hS G.ι)
  have hVpqc : IsQuasiCompactSpace B S hS Vp.toFunctor :=
    isQuasiCompactSpace_of_isCompact_range B S hS hY hVp
      (by rw [hVprange]; exact (hcompact V hV.1 hVqc).union (hcompact O' hO'.1 hO'qc))
  -- the two pieces of `V⁺` are clopen in it
  have hVpinj := pointsMap_injective_of_mono B S hS Vp.ι
  have hhom₁ : IsOpenImmersion B S hS (Subfunctor.homOfLe hVle) :=
    isOpenImmersion_homOfLe B S hS hV.2 hVle
  have hhom₂ : IsOpenImmersion B S hS (Subfunctor.homOfLe hO'le) :=
    isOpenImmersion_homOfLe B S hS hO'.2 hO'le
  have hrangeLe : ∀ {G : Subfunctor Y} (h : G ≤ Vp),
      Set.range (pointsMap B S hS _ (Subfunctor.homOfLe h)) =
        pointsMap B S hS Vp.toFunctor Vp.ι ⁻¹' Set.range (pointsMap B S hS G.toFunctor G.ι) := by
    intro G h
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, by rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, hVpinj (by rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι, hv])⟩
  have hsplit : ∀ x : points B S hS Vp.toFunctor,
      pointsMap B S hS _ Vp.ι x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ↔
        pointsMap B S hS _ Vp.ι x ∉ Set.range (pointsMap B S hS O'.toFunctor O'.ι) := by
    intro x
    have hx : pointsMap B S hS _ Vp.ι x ∈ Tplus := hVprange ▸ ⟨x, rfl⟩
    constructor
    · exact fun h h' => Set.disjoint_left.1 hdisj' h h'
    · intro h
      rcases hx with hx | hx
      · exact hx
      · exact absurd hx h
  have hclosed₁ : IsClosed (Set.range (pointsMap B S hS _ (Subfunctor.homOfLe hVle))) := by
    have heq : Set.range (pointsMap B S hS _ (Subfunctor.homOfLe hVle)) =
        (pointsMap B S hS Vp.toFunctor Vp.ι ⁻¹'
          Set.range (pointsMap B S hS O'.toFunctor O'.ι))ᶜ := by
      rw [hrangeLe hVle]
      ext x
      exact hsplit x
    rw [heq]
    exact (hO'openPts.preimage (continuous_pointsMap B S hS Vp.ι)).isClosed_compl
  have hclosed₂ : IsClosed (Set.range (pointsMap B S hS _ (Subfunctor.homOfLe hO'le))) := by
    have heq : Set.range (pointsMap B S hS _ (Subfunctor.homOfLe hO'le)) =
        (pointsMap B S hS Vp.toFunctor Vp.ι ⁻¹'
          Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ := by
      rw [hrangeLe hO'le]
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      rw [hsplit x, not_not]
    rw [heq]
    exact (hVopenPts.preimage (continuous_pointsMap B S hS Vp.ι)).isClosed_compl
  -- the cover of `V⁺`
  set eA := O'.toFunctor.reprW with heAdef
  set p₁ : yoneda.obj ZV ⟶ Vp.toFunctor := cV ≫ Subfunctor.homOfLe hVle with hp₁def
  set p₂ : yoneda.obj O'.toFunctor.reprX ⟶ Vp.toFunctor :=
    eA.hom ≫ Subfunctor.homOfLe hO'le with hp₂def
  have hint₁ : IsIntegralHom B S hS p₁ :=
    isIntegralHom_comp B S hS hcVint (isIntegralHom_of_isClosedImmersion B S hS _
      (isClosedImmersion_of_isOpenImmersion_of_isClosed_range_pointsMap B S hS _ hhom₁ hclosed₁))
  have hint₂ : IsIntegralHom B S hS p₂ :=
    isIntegralHom_comp_of_isIso B S hS eA.hom
      (isIntegralHom_of_isClosedImmersion B S hS _
        (isClosedImmersion_of_isOpenImmersion_of_isClosed_range_pointsMap B S hS _ hhom₂
          hclosed₂))
  obtain ⟨cp, -, -, hcpint, hcprange, hcpet, hcpfac⟩ :=
    exists_coprod_glue B S hS hVp.1 ZV O'.toFunctor.reprX p₁ p₂
  have hcpint' := hcpint hint₁ hint₂
  have hZpalg : IsAlgebraicSpace B S hS (yoneda.obj (ZV ⨿ O'.toFunctor.reprX)) :=
    isAlgebraicSpace_yoneda B S hS (ZV ⨿ O'.toFunctor.reprX)
  have hcpsurj : ∀ x : points B S hS Vp.toFunctor, x ∈ Set.range (pointsMap B S hS _ cp) := by
    intro x
    rw [hcprange]
    by_cases hx : pointsMap B S hS _ Vp.ι x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)
    · obtain ⟨v, hv⟩ : x ∈ Set.range (pointsMap B S hS _ (Subfunctor.homOfLe hVle)) := by
        rw [hrangeLe hVle]; exact hx
      obtain ⟨z, rfl⟩ := hcVsurj v
      exact Or.inl ⟨z, by rw [hp₁def, pointsMap_comp_apply, hv]⟩
    · obtain ⟨o, ho⟩ : x ∈ Set.range (pointsMap B S hS _ (Subfunctor.homOfLe hO'le)) := by
        rw [hrangeLe hO'le]
        by_contra hO
        exact hx ((hsplit x).2 hO)
      obtain ⟨a, rfl⟩ := pointsMap_surjective_of_isIso B S hS eA.hom o
      exact Or.inr ⟨a, by rw [hp₂def, pointsMap_comp_apply, ho]⟩
  -- the étale locus
  set DY : Set (points B S hS Y) := pointsMap B S hS V.toFunctor V.ι '' DV ∪
    Set.range (pointsMap B S hS O'.toFunctor O'.ι) with hDYdef
  have hDYopen : IsOpen DY := (hVemb.isOpenMap _ hDVopen).union hO'openPts
  have hDYgen : genericPoints (points B S hS Y) ⊆ DY := by
    intro η hη
    rcases hgen hη with ⟨v, rfl⟩ | h
    · exact Or.inl ⟨v, hDVgen
        (mem_genericPoints_of_isOpenSubspace B S hS hZ hY hYqs V hV hη), rfl⟩
    · exact Or.inr h
  have hDYsub : DY ⊆ Tplus := Set.union_subset_union (Set.image_subset_range _ _) subset_rfl
  have hcpet' : ∀ z, pointsMap B S hS _ cp z ∈ pointsMap B S hS Vp.toFunctor Vp.ι ⁻¹' DY →
      IsEtaleAt B S hS cp z := by
    refine hcpet _ (fun z hz => ?_) (fun z _ => ?_)
    · have hz' : pointsMap B S hS _ V.ι (pointsMap B S hS _ cV z) ∈ DY := by
        have := hz
        rw [Set.mem_preimage, hp₁def, ← pointsMap_comp_apply, Category.assoc,
          Subfunctor.homOfLe_ι, pointsMap_comp_apply] at this
        exact this
      rcases hz' with ⟨v, hv, hveq⟩ | hO
      · have hv' : v = pointsMap B S hS _ cV z := pointsMap_injective_of_mono B S hS V.ι hveq
        exact (hcVet z (hv' ▸ hv)).comp_isEtale B S hS (isEtale_of_isOpenImmersion B S hS hhom₁)
      · exact absurd hO (Set.disjoint_left.1 hdisj' ⟨_, rfl⟩)
    · exact isEtaleAt_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS _) _
        (isEtale_comp B S hS (isEtale_of_isIso B S hS _)
          (isEtale_of_isOpenImmersion B S hS hhom₂)) z
  -- the local factorization of the cover of `V⁺`
  have hfac₁ : FactorsZariskiLocallyThrough B S hS p ZV (p₁ ≫ Vp.ι ≫ π) := by
    have heq : p₁ ≫ Vp.ι ≫ π = cV ≫ V.ι ≫ π := by
      rw [hp₁def, Category.assoc, Subfunctor.homOfLe_ι_assoc]
    rw [heq]
    exact hcVfac
  obtain ⟨sO, hsO⟩ := exists_comp_eq_ι_of_range_subset B S hS U j hj O' hO'j
  have hfac₂ : FactorsZariskiLocallyThrough B S hS p O'.toFunctor.reprX (p₂ ≫ Vp.ι ≫ π) :=
    factorsZariskiLocallyThrough_of_eq_comp B S hS p _ _ (eA.hom ≫ sO) (by
      rw [hp₂def, Category.assoc, Subfunctor.homOfLe_ι_assoc, ← hsO, ← hjπ, Category.assoc,
        Category.assoc])
  have hcpfac' := hcpfac p (Vp.ι ≫ π) hfac₁ hfac₂
  -- Stacks 0G2D: extend the cover of `V⁺` over `Y`
  have hVpιqc : IsQuasiCompact B S hS Vp.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hY hYqs hVpqc Vp.ι
  obtain ⟨Y', ν, f', hY', hνint, hsq⟩ :=
    exists_isIntegralHom_isPullback_of_isOpenImmersion hZpalg hVp.1 hY Vp.ι hVp.2 hVpιqc cp
      hcpint'
  have hf'oi : IsOpenImmersion B S hS f' :=
    isOpenImmersion_snd_of_isPullback B S hS hsq.flip hVp.2
  have hPalg : IsAlgebraicSpace B S hS (pullback ν j) :=
    isAlgebraicSpace_pullback B S hS ν j hY' hUalg hY
  have hfstoi : IsOpenImmersion B S hS (pullback.fst ν j) :=
    isOpenImmersion_snd_of_isPullback B S hS (IsPullback.of_hasPullback ν j).flip hj
  have hsndint : IsIntegralHom B S hS (pullback.snd ν j) :=
    isIntegralHom_of_isPullback B S hS (IsPullback.of_hasPullback ν j) hνint
  have hPrep : (pullback ν j).IsRepresentable := by
    obtain ⟨hrep, -⟩ :=
      (isIntegralHom_iff_representable B S hS (pullback.snd ν j) hPalg hUalg).1 hsndint
    exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ hrep
  have _ := hPrep
  set eP : yoneda.obj (pullback ν j).reprX ≅ pullback ν j := (pullback ν j).reprW with hePdef
  have hcovY : Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
      Set.range (pointsMap B S hS Vp.toFunctor Vp.ι) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)
    · exact Or.inr (by rw [hVprange]; exact Or.inl hy)
    · exact Or.inl (hoffV y hy)
  -- `Y'` is a scheme
  set Wfam : ULift.{u} Bool → BigFppfOver B S hS := fun b =>
    match b with
    | ⟨false⟩ => (ZV ⨿ O'.toFunctor.reprX)
    | ⟨true⟩ => (pullback ν j).reprX
  set kfam : ∀ b, yoneda.obj (Wfam b) ⟶ Y' := fun b =>
    match b with
    | ⟨false⟩ => f'
    | ⟨true⟩ => eP.hom ≫ pullback.fst ν j
  have hkoi : ∀ b, IsOpenImmersion B S hS (kfam b) := by
    intro b
    rcases b with ⟨_ | _⟩
    · exact hf'oi
    · exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS eP.hom) hfstoi
  have hcoverY' : ∀ y' : points B S hS Y',
      (∃ w, pointsMap B S hS _ f' w = y') ∨ (∃ w, pointsMap B S hS _ (pullback.fst ν j) w = y')
      := by
    intro y'
    have hmem : pointsMap B S hS Y' ν y' ∈
        Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
          Set.range (pointsMap B S hS Vp.toFunctor Vp.ι) := hcovY ▸ Set.mem_univ _
    rcases hmem with ⟨uu, hu⟩ | ⟨vv, hv⟩
    · obtain ⟨w, hw, -⟩ :=
        exists_points_of_isPullback B S hS (IsPullback.of_hasPullback ν j) y' uu hu.symm
      exact Or.inr ⟨w, hw⟩
    · obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hsq y' vv hv.symm
      exact Or.inl ⟨w, hw⟩
  have hkcov : (⋃ b, Set.range (pointsMap B S hS (yoneda.obj (Wfam b)) (kfam b))) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun y' => ?_
    rcases hcoverY' y' with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact Set.mem_iUnion.2 ⟨⟨false⟩, w, hw⟩
    · refine Set.mem_iUnion.2 ⟨⟨true⟩, pointsMap B S hS (pullback ν j) eP.inv w, ?_⟩
      show pointsMap B S hS (yoneda.obj (pullback ν j).reprX) (eP.hom ≫ pullback.fst ν j)
        (pointsMap B S hS (pullback ν j) eP.inv w) = y'
      rw [← pointsMap_comp_apply, eP.inv_hom_id_assoc]
      exact hw
  have hY'rep : Y'.IsRepresentable := by
    refine isRepresentable_of_isOpenImmersion_cover B S hS hY'.isSheaf
      (ι := ULift.{u} Bool) ((Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff)
      (μ := max ((BigFppfOver.toScheme B S hS).obj (ZV ⨿ O'.toFunctor.reprX)).size
        ((BigFppfOver.toScheme B S hS).obj (pullback ν j).reprX).size)
      (max_lt (ZV ⨿ O'.toFunctor.reprX).left.property (pullback ν j).reprX.left.property)
      (W := Wfam) ?_ kfam hkoi hkcov
    intro b
    rcases b with ⟨_ | _⟩
    · exact le_max_left _ _
    · exact le_max_right _ _
  have _ := hY'rep
  set eY' : yoneda.obj Y'.reprX ≅ Y' := Y'.reprW with heY'def
  -- the reduced closed complement of `V⁺`
  have hTcl : IsClosed (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ :=
    (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY Vp hVp).isClosed_compl
  set T : Subfunctor Y := reducedClosedSubspace B S hS Y hY _ hTcl with hTdef
  have hTrange : Set.range (pointsMap B S hS T.toFunctor T.ι) =
      (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS Y hY _ hTcl
  have hTcs : IsClosedSubspace B S hS T :=
    isClosedSubspace_reducedClosedSubspace' B S hS hY _ hTcl
  have hTj : Set.range (pointsMap B S hS T.toFunctor T.ι) ⊆
      Set.range (pointsMap B S hS (yoneda.obj U) j) := by
    intro y hy
    rw [hTrange, hVprange] at hy
    exact hoffV y fun h => hy (Or.inl h)
  have _ : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hTrep : T.toFunctor.IsRepresentable :=
    isRepresentable_of_le_of_isClosedSubspace B S hS hTcs
      (le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_range_of_isOpenImmersion U j hj)
        (by rw [range_pointsMap_ι_range]; exact hTj))
      (isRepresentable_range_of_isOpenImmersion U j hj)
  have _ := hTrep
  set eT : yoneda.obj T.toFunctor.reprX ≅ T.toFunctor := T.toFunctor.reprW with heTdef
  -- the final glueing
  set q₁ : yoneda.obj Y'.reprX ⟶ Y := eY'.hom ≫ ν with hq₁def
  set q₂ : yoneda.obj T.toFunctor.reprX ⟶ Y := eT.hom ≫ T.ι with hq₂def
  have hqint₁ : IsIntegralHom B S hS q₁ := isIntegralHom_comp_of_isIso B S hS eY'.hom hνint
  have hqint₂ : IsIntegralHom B S hS q₂ :=
    isIntegralHom_comp_of_isIso B S hS eT.hom
      (isIntegralHom_of_isClosedImmersion B S hS _ hTcs.2)
  obtain ⟨Fc, -, -, hFint, hFrange, hFet, hFfac⟩ :=
    exists_coprod_glue B S hS hY Y'.reprX T.toFunctor.reprX q₁ q₂
  refine ⟨Y'.reprX ⨿ T.toFunctor.reprX, Fc, DY, ?_, hFint hqint₁ hqint₂, hDYopen, hDYgen, ?_, ?_⟩
  · -- surjectivity
    intro y
    have hy : y ∈ Set.range (pointsMap B S hS _ Fc) := by
      rw [hFrange]
      by_cases hyV : y ∈ Set.range (pointsMap B S hS Vp.toFunctor Vp.ι)
      · obtain ⟨v, rfl⟩ := hyV
        obtain ⟨z, rfl⟩ := hcpsurj v
        refine Or.inl ⟨pointsMap B S hS _ eY'.inv (pointsMap B S hS _ f' z), ?_⟩
        rw [hq₁def, ← pointsMap_comp_apply, ← pointsMap_comp_apply, Iso.inv_hom_id_assoc,
          hsq.w, pointsMap_comp_apply]
      · refine Or.inr ?_
        obtain ⟨t, ht⟩ : y ∈ Set.range (pointsMap B S hS T.toFunctor T.ι) := by
          rw [hTrange]; exact hyV
        obtain ⟨a, rfl⟩ := pointsMap_surjective_of_isIso B S hS eT.hom t
        exact ⟨a, by rw [hq₂def, pointsMap_comp_apply, ht]⟩
    exact hy
  · -- étaleness over `DY`
    refine hFet DY (fun z hz => ?_) (fun z hz => ?_)
    · have hzV := hDYsub hz
      rw [← hVprange] at hzV
      obtain ⟨v, hv⟩ := hzV
      obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS hsq
        (pointsMap B S hS _ eY'.hom z) v (by rw [hv, hq₁def, pointsMap_comp_apply])
      have hcw : IsEtaleAt B S hS (cp ≫ Vp.ι) w := by
        refine (hcpet' w ?_).comp_isEtale B S hS (isEtale_ι_of_isOpenSubspace hVp)
        rw [Set.mem_preimage, hw₂, hv]
        exact hz
      rw [← hsq.w] at hcw
      have hν := isEtaleAt_of_isEtaleAt_isOpenImmersion_comp B S hS f' hf'oi ν w hcw
      rw [hw₁] at hν
      exact IsEtaleAt.comp B S hS (isAlgebraicSpace_yoneda B S hS _) hY'
        (isEtaleAt_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS _) _
          (isEtale_of_isIso B S hS _) z) hν
    · have hzV := hDYsub hz
      have hzT : pointsMap B S hS _ q₂ z ∈ Set.range (pointsMap B S hS T.toFunctor T.ι) :=
        ⟨_, by rw [hq₂def, pointsMap_comp_apply]⟩
      rw [hTrange, hVprange] at hzT
      exact absurd hzV hzT
  · -- the local factorization
    refine hFfac p π ?_ ?_
    · refine factorsZariskiLocallyThrough_of_forall_isOpenImmersion B S hS p _ _ fun z => ?_
      rcases hcoverY' (pointsMap B S hS _ eY'.hom z) with ⟨w, hw⟩ | ⟨w, hw⟩
      · refine ⟨(ZV ⨿ O'.toFunctor.reprX), f' ≫ eY'.inv, w, isOpenImmersion_comp B S hS _ _ hf'oi
          (isOpenImmersion_of_isIso B S hS _), ?_, ?_⟩
        · rw [pointsMap_comp_apply, hw, ← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id,
            id_eq]
        · have heq : (f' ≫ eY'.inv) ≫ q₁ ≫ π = cp ≫ Vp.ι ≫ π := by
            simp only [hq₁def, Category.assoc, Iso.inv_hom_id_assoc]
            rw [← Category.assoc, hsq.w, Category.assoc]
          rw [heq]
          exact hcpfac'
      · refine ⟨(pullback ν j).reprX, eP.hom ≫ pullback.fst ν j ≫ eY'.inv,
          pointsMap B S hS _ eP.inv w, ?_, ?_, ?_⟩
        · exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
            (isOpenImmersion_comp B S hS _ _ hfstoi (isOpenImmersion_of_isIso B S hS _))
        · rw [← pointsMap_comp_apply, Iso.inv_hom_id_assoc, pointsMap_comp_apply, hw,
            ← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id, id_eq]
        · refine factorsZariskiLocallyThrough_of_eq_comp B S hS p _ _
            (eP.hom ≫ pullback.snd ν j) ?_
          simp only [hq₁def, Category.assoc, Iso.inv_hom_id_assoc]
          rw [pullback.condition_assoc, hjπ]
    · obtain ⟨sT, hsT⟩ := exists_comp_eq_ι_of_range_subset B S hS U j hj T hTj
      exact factorsZariskiLocallyThrough_of_eq_comp B S hS p _ _ (eT.hom ≫ sT) (by
        rw [hq₂def, Category.assoc, ← hsT, ← hjπ, Category.assoc, Category.assoc])

end Enlargement

/-! ### The induction -/

section Induction

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The induction of Stacks 0GUL, tracking the étale locus.** A quasi-separated algebraic space
`X` with finitely many irreducible components, carrying a separated surjective étale chart
`p : h_U ⟶ X` with quasi-compact source all of whose field-valued fibres have degree at most `d`,
has a surjective integral morphism from a scheme, étale at every point over an open set of `|X|`
containing every generic point, which factors Zariski locally through `p`.

The step is that of Stacks 09YB
(`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_chart_fibre_le`): Tag 0ABS and the
dense replacement give `p = j ≫ π`, the fibre-degree drop gives the open subspace `V ⊆ Y` with a
chart of smaller degree, and the induction hypothesis covers `V`. The cover of `V` is then extended
over `Y` by `AlgebraicGeometry.Space.exists_cover_of_openSubspace_cover`, which enlarges `V` to
`V⁺` so that the cover stays étale over the generic points of `|Y|`, and pushed down along `π`,
which is étale over an open set containing the generic points of `|X|`
(`AlgebraicGeometry.Space.exists_isOpen_genericPoints_subset_isEtaleAt_of_chart`), by
`AlgebraicGeometry.Space.exists_isOpen_genericPoints_subset_of_isIntegralHom`. -/
theorem exists_etaleRefiningCover_of_chart_fibre_le (d : ℕ) :
    ∀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS X →
      IsAbsolutelyQuasiSeparated B S hS hZ X →
      (irreducibleComponents (points B S hS X)).Finite →
      ∀ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsEtale B S hS p → IsSurjective B S hS p → IsSeparated B S hS p →
        IsQuasiCompactSpace B S hS (yoneda.obj U) →
        (∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
          (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
          (ζ : yoneda.obj T ⟶ X) (Q : BigFppfOver B S hS) (q : Q ⟶ T)
          (c : yoneda.obj Q ⟶ yoneda.obj U),
          IsPullback c (yoneda.map q) p ζ →
            ∃ r : ℕ, r ≤ d ∧
              Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) →
        ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (D : Set (points B S hS X)),
          IsSurjective B S hS f ∧ IsIntegralHom B S hS f ∧ IsOpen D ∧
          genericPoints (points B S hS X) ⊆ D ∧
          (∀ y, pointsMap B S hS _ f y ∈ D → IsEtaleAt B S hS f y) ∧
          FactorsZariskiLocallyThrough B S hS p Y f := by
  classical
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro X hX hXqs hXfin U p hpet hpsurj hpsep hUqc hd
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hpqc : IsQuasiCompact B S hS p :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hXqs hUqc p
  have hpqf : IsQuasiFinite B S hS p :=
    ⟨isLocallyQuasiFinite_of_isEtale' B S hS hpet, hpqc⟩
  obtain ⟨-, N₀, hfac₀, hj₀, hj₀qc, hπ₀⟩ := zariskiMainTheorem B S hS p hUalg hX hpqf hpsep
  have hY₀ := N₀.isAlgebraicSpace
  obtain ⟨Y, j, π, hY, hj, hjqc, hπ, hfac, -, -, -, hdense⟩ :=
    exists_isSchemeTheoreticallyDense_isIntegralHom_factorization B S hS hUalg hY₀ N₀.toNorm hj₀
      hj₀qc N₀.fromNorm hπ₀
  have hjπ : j ≫ π = p := hfac.trans hfac₀
  obtain ⟨Wc, V, g', φ, hVopen, hg'et, hg'surj, hφint, hgfac, hcov, hdrop⟩ :=
    exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt B S hS hX hY U j π hj hπ
      (by rw [hjπ]; exact hpet) (by rw [hjπ]; exact hpsep) (by rw [hjπ]; exact hpsurj)
      hdense d (by rw [hjπ]; exact hd)
  have hWcalg : IsAlgebraicSpace B S hS (yoneda.obj Wc) := isAlgebraicSpace_yoneda B S hS Wc
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- the base: `V` has no points, so `j` is an isomorphism and `p` is its own cover
    subst hd0
    have hVempty : IsEmpty (points B S hS V.toFunctor) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨pt, -⟩ := Quot.exists_rep x
      have hg'p := (isEtale_iff_presheaf_of_yoneda B S hS g').1 hg'et
      obtain ⟨r, hr, -⟩ := hdrop pt.carrier pt.field pt.siteObject (Iso.refl _)
        (yonedaEquiv.symm pt.value) (hg'p.rep.pullback (yonedaEquiv.symm pt.value))
        (hg'p.rep.snd (yonedaEquiv.symm pt.value))
        (yoneda.map (hg'p.rep.fst' (yonedaEquiv.symm pt.value)))
        (hg'p.rep.isPullback' (yonedaEquiv.symm pt.value))
      exact absurd hr (Nat.not_lt_zero r)
    have hjsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) j) := by
      intro y
      have hmem : y ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
          Set.range (pointsMap B S hS V.toFunctor V.ι) := hcov ▸ Set.mem_univ y
      rcases hmem with h | ⟨v, -⟩
      · exact h
      · exact hVempty.elim v
    have _ : IsIso j := isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS j hj hjsurj
    refine ⟨U, p, Set.univ, hpsurj, ?_, isOpen_univ, Set.subset_univ _,
      fun y _ => isEtaleAt_of_isEtale B S hS hUalg p hpet y,
      factorsZariskiLocallyThrough_of_eq_comp B S hS p U p (𝟙 _) (Category.id_comp _).symm⟩
    rw [← hjπ]
    exact isIntegralHom_comp B S hS
      (isIntegralHom_of_isClosedImmersion B S hS j (isClosedImmersion_of_isIso B S hS j)) hπ
  · -- the step
    have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY hXqs
        (isQuasiSeparated_of_isSeparated B S hS
          (isSeparated_of_isIntegralHom B S hS π hY hX hπ))
    obtain ⟨-, hUfin⟩ := finite_genericPoints_of_isEtale_of_isQuasiCompactSpace B S hS hZ hX
      hXqs hXfin U p hpet hpsep hUqc
    have hYfin : (irreducibleComponents (points B S hS Y)).Finite :=
      finite_irreducibleComponents_of_denseRange (continuous_pointsMap B S hS j) hdense hUfin
    have hVfin : (irreducibleComponents (points B S hS V.toFunctor)).Finite :=
      finite_irreducibleComponents_of_isOpenEmbedding _ (isOpenEmbedding_pointsMap_ι B S hS hVopen)
        hYfin
    have hφqc : IsQuasiCompact B S hS φ :=
      isQuasiCompact_of_isAffineHom' B S hS φ hWcalg hUalg
        (isAffineHom_of_isIntegralHom φ hφint)
    have hWcqc : IsQuasiCompactSpace B S hS (yoneda.obj Wc) :=
      isQuasiCompactSpace_source_of_isQuasiCompact B S hS hUalg hUqc hφqc
    have hVqc : IsQuasiCompactSpace B S hS V.toFunctor :=
      isQuasiCompactSpace_of_isSurjective B S hS hWcalg hVopen.1 g' hg'surj hWcqc
    have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
      isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hYqs V hVopen.1
    have hcomp : g' ≫ V.ι ≫ π = φ ≫ p := by rw [← Category.assoc, hgfac, hjπ]
    have hg'sep : IsSeparated B S hS g' := by
      refine isSeparated_of_comp B S hS g' (V.ι ≫ π) ?_
      rw [hcomp]
      exact isSeparated_comp B S hS φ p
        (isSeparated_of_isIntegralHom B S hS φ hWcalg hUalg hφint) hpsep
    obtain ⟨ZV, cV, DV, hcVsurj, hcVint, hDVopen, hDVgen, hcVet, hcVfac⟩ :=
      ih (d - 1) (by omega) V.toFunctor hVopen.1 hVqs hVfin Wc g' hg'et hg'surj hg'sep hWcqc
        (fun K hK T eT ξ Q q c hsqc => by
          obtain ⟨r, hlt, hrank⟩ := hdrop K hK T eT ξ Q q c hsqc
          exact ⟨r, by omega, hrank⟩)
    obtain ⟨C, F, DY, hFsurj, hFint, hDYopen, hDYgen, hFet, hFfac⟩ :=
      exists_cover_of_openSubspace_cover B S hS hZ hY hYqs hYfin U j hj π p hjπ V hVopen hVqc
        hcov ZV cV hcVsurj hcVint DV hDVopen hDVgen hcVet
        (hcVfac.comp B S hS (V.ι ≫ π) p φ hcomp)
    obtain ⟨Ω, hΩopen, hΩgen, hπet⟩ := exists_isOpen_genericPoints_subset_isEtaleAt_of_chart B S hS
      hZ hX hXqs hXfin U p hpet hpsep hUqc hY j hj hdense π hπ hjπ
    obtain ⟨hDXopen, hDXgen, hDX⟩ := exists_isOpen_genericPoints_subset_of_isIntegralHom B S hS hZ
      hX hY hXqs hYqs π hπ Ω hΩopen hΩgen hπet DY hDYopen hDYgen
    refine ⟨C, F ≫ π, _, ?_, isIntegralHom_comp B S hS hFint hπ, hDXopen, hDXgen, ?_, hFfac⟩
    · intro x
      obtain ⟨u, hu⟩ := hpsurj x
      obtain ⟨z, hz⟩ := hFsurj (pointsMap B S hS _ j u)
      exact ⟨z, by rw [pointsMap_comp_apply, hz, ← pointsMap_comp_apply, hjπ, hu]⟩
    · intro z hz
      rw [pointsMap_comp_apply] at hz
      obtain ⟨hzD, hπz⟩ := hDX _ hz
      exact IsEtaleAt.comp B S hS (isAlgebraicSpace_yoneda B S hS C) hY (hFet z hzD) hπz

end Induction

/-! ### An affine chart through a given chart -/

section AffineChart

/-- **A quasi-compact algebraic space has an affine surjective étale chart factoring through any
given surjective étale chart by a scheme.** Pull the given chart back to an affine chart of the
space (Stacks 03H6); the result is a surjective étale scheme over an affine, hence quasi-compact,
scheme, so finitely many affine opens of it already surject (an étale morphism is open), and
their disjoint union is affine. -/
theorem exists_affine_chart_through {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (V₀ : BigFppfOver B S hS) (q : yoneda.obj V₀ ⟶ X) (hq : IsSurjective B S hS q)
    (hqe : IsEtale B S hS q) :
    ∃ (A : BigFppfOver B S hS) (c : yoneda.obj A ⟶ X) (a : yoneda.obj A ⟶ yoneda.obj V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧ IsSurjective B S hS c ∧
        IsEtale B S hS c ∧ a ≫ q = c := by
  classical
  obtain ⟨A₀, c₀, hA₀aff, hc₀surj, hc₀et⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hXqc
  obtain ⟨W, r, a, hrsurj, hret, hfac⟩ := exists_etale_chart_over B S hS hX
    (isAlgebraicSpace_yoneda B S hS V₀) A₀ c₀ q hq hqe
  let G := BigFppfOver.toScheme B S hS
  let T : Scheme.{u} := G.obj W
  have _ : IsAffine (G.obj A₀) := hA₀aff
  have _ : Etale (G.map r) := hret
  -- finitely many affine opens of `T` whose images cover the affine `G.obj A₀`
  choose O hOaff hOmem using fun t : T =>
    exists_isAffineOpen_mem_and_subset (X := T) (x := t) (U := ⊤)
      (show t ∈ (⊤ : T.Opens) from trivial)
  have hOopen : ∀ t, IsOpen ((G.map r).base '' (O t : Set T)) := fun t =>
    (G.map r).isOpenMap _ (O t).2
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t => (G.map r).base '' (O t : Set T))
    hOopen (fun x _ => by
      obtain ⟨t, rfl⟩ := hrsurj.surj x
      exact Set.mem_iUnion.2 ⟨t, ⟨t, (hOmem t).1, rfl⟩⟩)
  let I := {t // t ∈ s}
  let Yf : I → Scheme.{u} := fun i => (O i.1 : T.Opens).toScheme
  let a' : (∐ Yf) ⟶ T := Sigma.desc fun i => (O i.1 : T.Opens).ι
  have hAsmall : (∐ Yf).size < B.cutoff := by
    apply Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      Cardinal.mk_le_aleph0 Yf
    exact fun i => Scheme.size_lt_of_isOpenImmersion ((O i.1 : T.Opens).ι) W.left.property
  have ha'Etale : Etale a' := by
    have : HasRingHomProperty @Etale RingHom.Etale := inferInstance
    have : IsZariskiLocalAtSource @Etale :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ => inferInstance)
  let V : BigFppfOver B S hS :=
    Over.mk ((B.inclusion.preimage (X := B.obj hAsmall) (Y := W.left)
      (show B.inclusion.obj (B.obj hAsmall) ⟶ B.inclusion.obj W.left from a')) ≫ W.hom)
  let g : V ⟶ W := Over.homMk (B.inclusion.preimage
    (show B.inclusion.obj (B.obj hAsmall) ⟶ B.inclusion.obj W.left from a'))
  have hgmap : G.map g = a' := B.inclusion.map_preimage _
  have hAff : ∀ i, IsAffine (Yf i) := fun i => hOaff i.1
  have _ : IsAffine (∐ Yf) := inferInstance
  have hVaff : IsAffine (G.obj V) := by change IsAffine (∐ Yf); infer_instance
  have hcomp : Etale (G.map (g ≫ r)) := by
    rw [Functor.map_comp, hgmap]
    exact Etale.etale_comp _ _
  have hcompsurj : Surjective (G.map (g ≫ r)) := by
    rw [Functor.map_comp, hgmap]
    refine ⟨fun x => ?_⟩
    obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', rfl⟩ : y ∈ Set.range (O t).ι := by rw [Scheme.Opens.range_ι]; exact hy
    refine ⟨(Sigma.ι Yf ⟨t, ht⟩) y', ?_⟩
    have h1 : ∀ z, a' ((Sigma.ι Yf ⟨t, ht⟩) z) = (O t).ι z := fun z => by
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    rw [Scheme.Hom.comp_apply, h1]
  refine ⟨V, yoneda.map (g ≫ r) ≫ c₀, yoneda.map g ≫ a, hVaff, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := isSurjective_of_presheafSurjective B S hS c₀ hc₀surj x
    obtain ⟨z, rfl⟩ := isSurjective_yoneda_map B S hS (g ≫ r) hcompsurj y
    exact ⟨z, by rw [pointsMap_comp_apply]⟩
  · refine isEtale_comp B S hS ?_ hc₀et
    refine isEtale_of_presheaf_etale' B S hS _ ?_
    exact (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G)).2 hcomp
  · rw [Category.assoc, ← hfac, Functor.map_comp, Category.assoc]

end AffineChart

/-! ### The conclusion for every chart by a scheme -/

section Discharge

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **What the carried hypothesis `h2` of the former registration of Stacks 0GUL asserts, proved.**
For a quasi-compact quasi-separated algebraic space `X` whose point space has finitely many
irreducible components, every surjective étale `q : h_{V₀} ⟶ X` from a scheme admits a surjective
integral `f : h_Y ⟶ X` from a scheme, étale over an open subspace with dense point set, which
factors through `q` Zariski locally on `Y`.

An affine surjective étale chart factoring through `q` exists by
`AlgebraicGeometry.Space.exists_affine_chart_through`; it is separated, and its field-valued
fibres have bounded degree by Stacks 03JX and 07S8; the induction
`AlgebraicGeometry.Space.exists_etaleRefiningCover_of_chart_fibre_le` produces a cover factoring
through it, hence through `q`. -/
theorem existsIntegralSchemeCoverEtaleRefining_of_isEtale
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hcomp : (irreducibleComponents (points B S hS X)).Finite)
    (V₀ : BigFppfOver B S hS) (q : yoneda.obj V₀ ⟶ X) (hq : IsSurjective B S hS q)
    (hqe : IsEtale B S hS q) :
    ExistsIntegralSchemeCoverEtaleRefining B S hS q := by
  classical
  obtain ⟨A, c, a, hAaff, hcsurj, hcet, hac⟩ :=
    exists_affine_chart_through B S hS hX hXqc V₀ q hq hqe
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaff
  have hAalg : IsAlgebraicSpace B S hS (yoneda.obj A) := isAlgebraicSpace_yoneda B S hS A
  rcases isEmpty_or_nonempty (points B S hS X) with hemp | hne
  · -- no points: any integral surjective cover will do, all conditions on points are vacuous
    obtain ⟨Y, f, hfsurj, hfint⟩ :=
      existsIntegralSurjectiveSchemeCover_of_isEmpty_points B S hS hX A c hcet hcsurj hemp
    have hYemp : IsEmpty (points B S hS (yoneda.obj Y)) :=
      ⟨fun y => hemp.elim (pointsMap B S hS _ f y)⟩
    refine existsIntegralSchemeCoverEtaleRefining_of_genericPoints_subset B S hS hZ hX hXqs q Y f
      hfsurj hfint Set.univ isOpen_univ (Set.subset_univ _) (fun y => hYemp.elim y)
      (fun y => hYemp.elim y)
  · have hAsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj A) := inferInstance
    have hcsep : IsSeparated B S hS c :=
      isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX A hAsep c hcet
    have hAqc : IsQuasiCompactSpace B S hS (yoneda.obj A) :=
      isQuasiCompact_yoneda_of_compact B S hS A inferInstance
    have hR : IsReasonableSpace B S hS X :=
      isReasonableSpace_of_isAbsolutelyQuasiSeparated B S hS hZ X hX hXqs
    obtain ⟨d, -, -, -, -, -, hbd⟩ :=
      exists_minimalDegreeOpen_and_fibre_le_degree B S hS X A c hX hR hAaff hcet hcsep hne
    obtain ⟨Y, f, D, hfsurj, hfint, hDopen, hDgen, hfet, hfac⟩ :=
      exists_etaleRefiningCover_of_chart_fibre_le B S hS hZ d X hX hXqs hcomp A c hcet hcsurj
        hcsep hAqc hbd
    refine existsIntegralSchemeCoverEtaleRefining_of_genericPoints_subset B S hS hZ hX hXqs q Y f
      hfsurj hfint D hDopen hDgen hfet ?_
    intro y
    obtain ⟨W, hW, hWrep, hy, g, hg⟩ := hfac y
    exact ⟨W, hW, hWrep, hy, g ≫ a, by rw [hg, Category.assoc, hac]⟩

end Discharge

/-! ### The tag -/

section Tag

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks Project, Tag 0GUL.** Let `X` be a quasi-compact and quasi-separated algebraic
space over a scheme `S` such that `|X|` has finitely many irreducible components. Then

1. there is a surjective integral morphism to `X` from the presheaf represented by an object of
   the big fppf site — a scheme over `S` — which is finite étale over a quasi-compact open
   subspace of `X` with dense point set, and
2. given a surjective étale morphism `p : V ⟶ X` from an algebraic space, such a cover can be
   chosen so that it factors through `p` on a representable open subspace neighbourhood of
   every one of its points.

Clause (2) for a cover `p` is reduced to a chart `c : h_{V₀} ⟶ V`
(`AlgebraicGeometry.Space.existsIntegralSchemeCoverRefining_of_comp_chart`); for the chart
`c ≫ p` the induction gives a cover étale over a dense open
(`AlgebraicGeometry.Space.existsIntegralSchemeCoverEtaleRefining_of_isEtale`), which is upgraded
to one finite étale over a quasi-compact dense open
(`AlgebraicGeometry.Space.existsIntegralSchemeCoverRefining_of_etaleRefining`). Clause (1) is
clause (2) at the identity of `X`. -/
@[stacks 0GUL]
theorem exists_integralSchemeCover_finiteEtaleOverDenseOpen_and_refining
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hcomp : (irreducibleComponents (points B S hS X)).Finite) :
    ExistsIntegralSchemeCoverFiniteEtaleOverDenseOpen B S hS X ∧
      ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS V →
        ∀ p : V ⟶ X, IsSurjective B S hS p → IsEtale B S hS p →
          ExistsIntegralSchemeCoverRefining B S hS p := by
  have H : ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS V →
      ∀ p : V ⟶ X, IsSurjective B S hS p → IsEtale B S hS p →
        ExistsIntegralSchemeCoverRefining B S hS p := by
    intro V hV p hp hpe
    obtain ⟨V₀, c, hcsurj, hcet⟩ := hV.exists_atlas
    have hc : IsSurjective B S hS c := isSurjective_of_presheafSurjective B S hS c hcsurj
    have hce : IsEtale B S hS c := isEtale_of_presheaf_etale B S hS hcet
    have hcp : IsSurjective B S hS (c ≫ p) := by
      show Function.Surjective (pointsMap B S hS (yoneda.obj V₀) (c ≫ p))
      rw [pointsMap_comp B S hS (yoneda.obj V₀) c p]
      exact hp.comp hc
    exact existsIntegralSchemeCoverRefining_of_comp_chart B S hS p V₀ c
      (existsIntegralSchemeCoverRefining_of_etaleRefining B S hS hZ hX hXqs hcomp _
        (existsIntegralSchemeCoverEtaleRefining_of_isEtale B S hS hZ hX hXqc hXqs hcomp V₀
          (c ≫ p) hcp (isEtale_comp B S hS hce hpe)))
  exact ⟨existsIntegralSchemeCoverFiniteEtaleOverDenseOpen_of_refining_id B S hS
    (H X hX (𝟙 X) (isSurjective_id B S hS X) (isEtale_id B S hS X)), H⟩

end Tag

end AlgebraicGeometry.Space

end

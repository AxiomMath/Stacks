module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaRefinement

/-!
# A very reasonable algebraic space is reasonable

Stacks 03JX relates nine conditions on an algebraic space `X` over a scheme `S`. This file
proves the implication `(ε) ⇒ (δ)`: an algebraic space carrying a jointly surjective family of
étale charts by schemes whose self-intersection projections are quasi-compact is reasonable,
that is, every one of its étale charts by an affine scheme has universally bounded fibres in
the sense of Stacks 03JL.

By Stacks 03JT it is enough to produce *one* jointly surjective family of étale charts with
universally bounded fibres, and the family is obtained by refining the given one: for an affine
open `W` of the source `U` of a chart `φ : U ⟶ X`, the fibre product `W ×_X U` is a base change
of the self-intersection projection `U ×_X U ⟶ U` along `W ⟶ U`, hence quasi-compact over the
affine scheme `W`, so it is a quasi-compact scheme. Its projection to `U` is étale, so
Stacks 03JA bounds its fibres, and Stacks 03JO carries that bound to `W ⟶ X` because the image
of `|W| → |X|` lies in the image of `|U| → |X|`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_affineOpen_comp_of_isQuasiCompact`: the
  fibre bound at one affine open of one chart.
* `AlgebraicGeometry.Space.isReasonableSpace_of_isVeryReasonableSpace`: **Stacks 03JX,
  `(ε) ⇒ (δ)`**.
* `AlgebraicGeometry.Space.isReasonable_of_isVeryReasonable`: **Stacks 03M5**, the implication
  from very reasonable to reasonable for a *morphism*, which is the same implication applied to
  each represented base change.

## Implementation notes

The source argument runs through Stacks 03IH, replacing the family of charts by a Zariski
covering with quasi-compact surjective étale charts and using that `W → X` factors through the
member containing it. That step is not needed: Stacks 03JO asks only that the image of the
points of the chart being bounded lie in the image of the points of the chart it is base changed
along, and for `W` an open of `U` that is immediate from the factorization `W → U → X`. So the
argument is carried out at the given family directly, with no appeal to Stacks 03IH and none to
Zariski locality of `(δ)`.

Quasi-compactness of `W ×_X U ⟶ W` is read off the vertical pasting
`CategoryTheory.IsPullback.of_bot'`, which exhibits it as the base change of
`U ×_X U ⟶ U` along `W ⟶ U`; quasi-compactness of a morphism of algebraic spaces is stable
under base change, and for a represented morphism it is quasi-compactness of the underlying
morphism of schemes (Stacks 03HD), which with `W` affine makes `W ×_X U` a quasi-compact
scheme.

The refined family is indexed by the pairs consisting of an index of the given family and a
point of the scheme underlying that chart, the affine open attached to a point being one
containing it. Joint surjectivity of the refinement is
`CategoryTheory.Presheaf.isLocallySurjective_sigmaDesc_refinement`.

## References

* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JO](https://stacks.math.columbia.edu/tag/03JO)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03M5](https://stacks.math.columbia.edu/tag/03M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibre bound at one affine open of one chart.** Let `c : h_A ⟶ X` be an étale chart of
an algebraic space over `S` whose first self-intersection projection is quasi-compact. Then the
composite of the inclusion of an affine open of `A` with `c` has universally bounded fibres in
the sense of Stacks 03JL.

The fibre product of that composite with `c` is a base change of the self-intersection
projection along the inclusion, hence quasi-compact over the affine open, so it is a
quasi-compact scheme; its projection to `A` is étale, so Stacks 03JA bounds its fibres, and
Stacks 03JO carries the bound to the composite. -/
theorem hasUniversallyBoundedFibers_affineOpen_comp_of_isQuasiCompact
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (A : BigFppfOver B S hS) (c : yoneda.obj A ⟶ X)
    (hcEt : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hcqc : IsQuasiCompact B S hS (pullback.fst c c))
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) (hO : IsAffineOpen O) :
    HasUniversallyBoundedFibers B S hS (openObj B S hS A O)
      (yoneda.map (openIncl B S hS A O) ≫ c) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hrep : yoneda.relativelyRepresentable c := hX.diagonal_representable.of_diag c
  have hsq : IsPullback
      (yoneda.map (hrep.snd (yoneda.map (openIncl B S hS A O) ≫ c)))
      (yoneda.map (hrep.fst' (yoneda.map (openIncl B S hS A O) ≫ c)))
      (yoneda.map (openIncl B S hS A O) ≫ c) c :=
    (hrep.isPullback' _).flip
  -- the projection to the chart is étale, being a base change of the open chart
  have hχEt : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (openIncl B S hS A O) ≫ c) :=
    etale_comp_of_scheme B S hS (openIncl B S hS A O) c
      (inferInstanceAs (_root_.AlgebraicGeometry.Etale O.ι)) hcEt
  have hpEt : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hrep.fst' (yoneda.map (openIncl B S hS A O) ≫ c))) :=
    hχEt.property c _ _ hsq
  -- the projection to the affine open is a base change of the self-intersection projection
  have hpaste := (IsPullback.of_bot' hsq (IsPullback.of_hasPullback c c)).flip
  have hqc : IsQuasiCompact B S hS
      (yoneda.map (hrep.snd (yoneda.map (openIncl B S hS A O) ≫ c))) :=
    isQuasiCompact_of_isPullback B S hS hpaste hcqc
  have hqcScheme : _root_.AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map
        (hrep.snd (yoneda.map (openIncl B S hS A O) ≫ c))) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1
      (presheaf_quasiCompact_of_isQuasiCompact B S hS
        (Functor.relativelyRepresentable.map yoneda _) hqc)
  -- so the fibre product is a quasi-compact scheme and Stacks 03JA bounds its fibres
  have hWc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (openObj B S hS A O)) := by
    rw [toScheme_obj_openObj]
    have _ : IsAffine O.toScheme := hO
    infer_instance
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (yoneda.map (openIncl B S hS A O) ≫ c))) :=
    @_root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace _ _ _ hqcScheme hWc
  obtain ⟨hft, hqf⟩ := _root_.AlgebraicGeometry.locallyQuasiFinite_of_etale
    ((BigFppfOver.toScheme B S hS).map
      (hrep.fst' (yoneda.map (openIncl B S hS A O) ≫ c)))
  have _ := hft
  have _ := hqf
  obtain ⟨N, hN⟩ := _root_.AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite
    ((BigFppfOver.toScheme B S hS).map
      (hrep.fst' (yoneda.map (openIncl B S hS A O) ≫ c)))
  -- Stacks 03JO transfers the bound along the chart
  have himage : Set.range (pointsMap B S hS (yoneda.obj (openObj B S hS A O))
        (yoneda.map (openIncl B S hS A O) ≫ c)) ⊆
      Set.range (pointsMap B S hS (yoneda.obj A) c) := by
    rw [pointsMap_comp]
    exact Set.range_comp_subset_range _ _
  exact hasUniversallyBoundedFibers_of_baseChange_of_range_subset B S hS hX
    (isAlgebraicSpace_yoneda B S hS A) c _ himage hsq
    (hasUniversallyBoundedFibers_yoneda_map_of_boundsFiberDegrees B S hS _ N hN)

/-- **Stacks 03JX, `(ε) ⇒ (δ)`.** A very reasonable algebraic space over `S` is reasonable:
every étale chart of it by an affine scheme has universally bounded fibres.

This is also the third implication of Stacks 03M5. The given family of charts is refined by the
affine opens of its sources, which have universally bounded fibres over the space by
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_affineOpen_comp_of_isQuasiCompact`, and
Stacks 03JT turns one such jointly surjective family into reasonableness. -/
@[stacks 03JX "(epsilon) implies (delta)"]
theorem isReasonableSpace_of_isVeryReasonableSpace
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (h : IsVeryReasonableSpace B S hS X) :
    IsReasonableSpace B S hS X := by
  classical
  obtain ⟨I, Ui, φ, hsurj, hprops⟩ := h
  -- an affine open of each chart source around each of its points
  have hcov : ∀ (i : I) (y : (BigFppfOver.toScheme B S hS).obj (Ui i)),
      ∃ O : ((BigFppfOver.toScheme B S hS).obj (Ui i)).Opens, IsAffineOpen O ∧ y ∈ O := by
    intro i y
    obtain ⟨O, hOaff, hyO, -⟩ :=
      _root_.AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
        (X := (BigFppfOver.toScheme B S hS).obj (Ui i)) (x := y) (U := ⊤)
        (show y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj (Ui i)).Opens) from trivial)
    exact ⟨O, hOaff, hyO⟩
  choose O hOaff hyO using hcov
  have hEt : ∀ i, (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (φ i) := fun i ↦
    presheaf_etale_of_isEtale B S hS (hprops i).1
  refine isReasonableSpace_of_boundedEtaleCover B S hS X hX
    (fun k : Σ i : I, (BigFppfOver.toScheme B S hS).obj (Ui i) ↦
      openObj B S hS (Ui k.1) (O k.1 k.2))
    (fun k ↦ yoneda.map (openIncl B S hS (Ui k.1) (O k.1 k.2)) ≫ φ k.1) ?_ (fun k ↦ ?_)
    fun k ↦ ?_
  · refine Presheaf.isLocallySurjective_sigmaDesc_refinement (BigFppfOver.topology B S hS)
      Ui φ (fun i y ↦ openObj B S hS (Ui i) (O i y))
      (fun i y ↦ openIncl B S hS (Ui i) (O i y)) (fun i ↦ ?_) hsurj
    refine generate_ofArrows_mem_topology_of_openCover B S hS _ _ (fun y ↦ ?_) fun y ↦ ?_
    · exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (O i y).ι)
    · exact ⟨y, ⟨y, hyO i y⟩, by rw [toScheme_map_openIncl]; rfl⟩
  · exact etale_comp_of_scheme B S hS (openIncl B S hS (Ui k.1) (O k.1 k.2)) (φ k.1)
      (inferInstanceAs (_root_.AlgebraicGeometry.Etale (O k.1 k.2).ι)) (hEt k.1)
  · exact hasUniversallyBoundedFibers_affineOpen_comp_of_isQuasiCompact B S hS hX (Ui k.1)
      (φ k.1) (hEt k.1) (hprops k.1).2.1 (O k.1 k.2) (hOaff k.1 k.2)

/-- **Stacks 03M5, very reasonable implies reasonable.** A very reasonable morphism of
algebraic spaces over `S` is reasonable.

Both conditions of Stacks 03KZ are conditions on the represented base changes of the morphism,
each of which is an algebraic space, so this is the implication
`AlgebraicGeometry.Space.isReasonableSpace_of_isVeryReasonableSpace` applied base change by
base change. -/
@[stacks 03M5 "very reasonable implies reasonable"]
theorem isReasonable_of_isVeryReasonable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h : IsVeryReasonable B S hS f) : IsReasonable B S hS f := fun T g ↦
  isReasonableSpace_of_isVeryReasonableSpace B S hS _
    (isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY) (h T g)

end AlgebraicGeometry.Space

end

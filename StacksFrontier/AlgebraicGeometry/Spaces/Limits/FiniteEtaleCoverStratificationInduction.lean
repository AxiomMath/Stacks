module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverSpreading
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The induction step of Stacks 0GUP

Let `X` be a quasi-compact and quasi-separated algebraic space and `C ⊆ |X|` a closed set all of
whose proper closed subsets lie in cover-stratified closed subspaces of finite presentation.
Suppose there is a finite morphism of finite presentation `g : T ⟶ X` from a scheme whose image
contains `C` and whose base change to the reduced closed subspace on `C` is étale over a set
open in `|X|` and meeting `C`. Then `C` itself lies in a cover-stratified closed subspace of
finite presentation: the part of `C` off that open set lies in one, `W'`, the cover spreads to a
closed subspace `W ⊇ C` of finite presentation over which it is étale off `W'`
(`AlgebraicGeometry.Space.exists_isFinitePresentation_spread`), and `W` followed by the chain of
`W' ∩ W` is a stratification of `W`.

## Main results

* `AlgebraicGeometry.Space.exists_isCoverStratified_of_spreadCover`: the induction step, `C`
  lies in a cover-stratified closed subspace of finite presentation.
* `AlgebraicGeometry.Space.exists_finiteEtaleCoverStratification_of_isCoverStratified`: a
  cover-stratified closed subspace with all the points of `X` gives the chain of Stacks 0GUP.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

attribute [local instance] pointTopology

/-- **The induction step of Stacks 0GUP.**  Let `C ⊆ |X|` be closed, with every proper closed
subset lying in a cover-stratified closed subspace of finite presentation, and let `g : T ⟶ X` be
finite and of finite presentation, with image containing `C`, whose base change to `C` is étale
over an open set `O` meeting `C`.  Then `C` lies in a cover-stratified closed subspace of finite
presentation. -/
theorem exists_isCoverStratified_of_spreadCover (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) {C₀ : Subfunctor X}
    (hC₀ : IsClosedSubspace B S hS C₀)
    (hsmall : ∀ C' : Set (points B S hS X), IsClosed C' → C' ⊂ subspacePointSet B S hS X C₀ →
      ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
        IsCoverStratified B S hS W ∧ C' ⊆ subspacePointSet B S hS X W)
    {T : BigFppfOver B S hS} {g : yoneda.obj T ⟶ X} (hg : IsFinite B S hS g)
    (hgfp : IsFinitePresentation B S hS g) {O : Set (points B S hS X)} (hO : IsOpen O)
    (hOC : (O ∩ subspacePointSet B S hS X C₀).Nonempty)
    (hrange : subspacePointSet B S hS X C₀ ⊆ Set.range (pointsMap B S hS _ g))
    (hét : ∀ t : points B S hS (pullback C₀.ι g),
      pointsMap B S hS _ (pullback.fst C₀.ι g ≫ C₀.ι) t ∈ O →
        IsEtaleAt B S hS (pullback.fst C₀.ι g) t) :
    ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
      IsCoverStratified B S hS W ∧ subspacePointSet B S hS X C₀ ⊆ subspacePointSet B S hS X W := by
  have hCcl : IsClosed (subspacePointSet B S hS X C₀) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS hX C₀.ι hC₀.2
  obtain ⟨W', hW', hW'fp, hW's, hC'W'⟩ := hsmall (subspacePointSet B S hS X C₀ \ O)
    (hCcl.sdiff hO) ⟨Set.diff_subset, fun h => by
      obtain ⟨x, hxO, hxC⟩ := hOC
      exact (h hxC).2 hxO⟩
  have hét' : ∀ t : points B S hS (pullback C₀.ι g),
      pointsMap B S hS _ (pullback.fst C₀.ι g ≫ C₀.ι) t ∉ subspacePointSet B S hS X W' →
        IsEtaleAt B S hS (pullback.fst C₀.ι g) t := by
    intro t ht
    refine hét t ?_
    by_contra hO'
    refine ht (hC'W' ⟨⟨pointsMap B S hS _ (pullback.fst C₀.ι g) t, ?_⟩, hO'⟩)
    rw [← pointsMap_comp_apply]
  obtain ⟨W, hW, hWfp, hC₀W, hWét, hWsurj⟩ := exists_isFinitePresentation_spread hZ hX hXqc hXqs
    hC₀ hW' hW'fp hg hgfp hét' fun x hx => hrange hx.1
  have hrep := hW.2.1
  let Y := hrep.pullback g
  let f : yoneda.obj Y ⟶ W.toFunctor := hrep.fst g
  have sq : IsPullback f (yoneda.map (hrep.snd g)) W.ι g := hrep.isPullback g
  let e := sq.isoPullback
  have hef : e.hom ≫ pullback.fst W.ι g = f := IsPullback.isoPullback_hom_fst _
  have hY := isAlgebraicSpace_yoneda B S hS Y
  have hcover : IsEtaleCoverOver B S hS W f
      (subspacePointSet B S hS X W \ subspacePointSet B S hS X W') := by
    refine ⟨isFinite_of_isPullback B S hS sq.flip hg,
      IsFinitePresentation.of_isPullback B S hS hY (isAlgebraicSpace_yoneda B S hS T) hW.1 hX
        sq.flip hgfp, fun y hy => ?_⟩
    rw [← hef]
    refine IsEtaleAt.comp B S hS hY (isAlgebraicSpace_pullback B S hS _ _ hW.1
      (isAlgebraicSpace_yoneda B S hS T) hX) (isEtaleAt_of_isEtale B S hS hY _
        (isEtale_of_iso B S hS e) y) (hWét _ ?_)
    rw [← pointsMap_comp_apply, ← Category.assoc, hef]
    exact hy.2
  have hsurj : subspacePointSet B S hS X W \ subspacePointSet B S hS X W' ⊆
      Set.range (pointsMap B S hS _ (f ≫ W.ι)) := by
    rintro _ ⟨⟨w, rfl⟩, hw⟩
    obtain ⟨y, hy⟩ := hWsurj ⟨⟨w, rfl⟩, hw⟩
    obtain ⟨p, hp, -⟩ := exists_points_of_isPullback B S hS sq w y hy.symm
    exact ⟨p, by rw [pointsMap_comp_apply, hp]⟩
  refine ⟨W, hW, hWfp, isCoverStratified_of_isEtaleCoverOver hX hW hWfp hW' hW'fp hW's hcover
    hsurj, ?_⟩
  rintro _ ⟨c, rfl⟩
  exact ⟨pointsMap B S hS _ (Subfunctor.homOfLe hC₀W) c, by
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩

/-- **A cover-stratified closed subspace with all the points of `X` gives the chain of
Stacks 0GUP.** -/
theorem exists_finiteEtaleCoverStratification_of_isCoverStratified
    (hX : IsAlgebraicSpace B S hS X) {W : Subfunctor X} (hW : IsCoverStratified B S hS W)
    (hWpts : subspacePointSet B S hS X W = Set.univ) :
    ∃ (t : ℕ) (Z : ℕ → Subfunctor X),
      (∀ i, IsClosedSubspace B S hS (Z i)) ∧ (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
      (∀ i, Z (i + 1) ≤ Z i) ∧ IsThickening B S hS ⟨X, hX⟩ (Z 0) ∧
      IsEmpty (points B S hS (Z t).toFunctor) ∧
      ∀ i < t, IsFiniteEtaleCoverStep B S hS (Z i) (Z (i + 1)) := by
  obtain ⟨t, Z, hcl, hfp, hdec, -, hpts, hemp, hstep⟩ := hW
  refine ⟨t, Z, hcl, hfp, hdec, ⟨hcl 0, fun x => ?_⟩, ?_, fun i hi => ?_⟩
  · exact (by rw [hpts, hWpts]; trivial : x ∈ subspacePointSet B S hS X (Z 0))
  · refine ⟨fun z => ?_⟩
    have hz : pointsMap B S hS _ (Z t).ι z ∈ subspacePointSet B S hS X (Z t) := ⟨z, rfl⟩
    rwa [hemp] at hz
  · obtain ⟨Y, f, hf, hs⟩ := hstep i hi
    exact isFiniteEtaleCoverStep_of_isEtaleCoverOver hX (hcl i) (hcl (i + 1)) hf hs

end AlgebraicGeometry.Space

end

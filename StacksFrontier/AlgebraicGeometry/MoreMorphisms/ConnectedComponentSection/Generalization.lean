module

public import StacksFrontier.AlgebraicGeometry.Limits.IntegralFamily
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.GeneralizationStableLocus

/-!
# Stability of the locus `X⁰` under generalization at a single fibre

Let `f : X ⟶ Y` be flat and of finite presentation with a specified section `s`, as in
Situation 055L, and let `x` be a point of `X` whose fibre `X_{f(x)}` is geometrically reduced.
If `x` lies in the locus `X⁰` then so does every generalization of `x`.

Geometric reducedness is required of the one fibre through `x` only. This is the form in which
the hypothesis of Stacks Tag 055Q is pointwise: the Stacks statement assumes that `X_y` is
geometrically reduced for the single point `y` under consideration, not that every fibre of `f`
is geometrically reduced.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_over_spec_of_fiber`: the
  case of an affine base.
* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_of_fiber`: the general case.

## Implementation notes

The reduction to a locally Noetherian source is the limit over the finitely generated
`ℤ`-subalgebras of the base ring, whose stages are Noetherian because a finitely generated
`ℤ`-algebra is; the diagram and its colimit cocone are `Algebra.adjoinFinsetDiagram` and
`Algebra.isColimitAdjoinFinsetCocone`. The geometrically reduced fibre is transported to the
stage by `AlgebraicGeometry.geometricallyReduced_fiber_set_eq_preimage_of_isPullback`, which
describes the geometrically reduced locus of a base change as the preimage of the one
downstairs; this is a statement about single fibres and so applies at the one fibre assumed
geometrically reduced here, whereas geometric reducedness of *all* the fibres is not available
at the stage, the projection from the limit not being surjective.

The general case shrinks the base to an affine open containing the image of `x`. The two points
both lie over that open, a generalization of `f x` lying in every open subset containing `f x`,
and both the locus and the geometrically reduced fibre restrict along the resulting open
immersion.

## References

* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
* [Stacks Project, Tag 055M](https://stacks.math.columbia.edu/tag/055M)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

noncomputable section

/-- In a pullback square, the fibre of `f` through `f x` is geometrically reduced iff the fibre of
`f₀` through `f₀ (g' x)` is. -/
private theorem geometricallyReduced_fiber_iff_of_isPullback {X₀ Y₀ X Y : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (g' : X ⟶ X₀) (g : Y ⟶ Y₀) (h : IsPullback g' f f₀ g) (x : X) :
    GeometricallyReduced (f.fiberToSpecResidueField (f x)) ↔
      GeometricallyReduced (f₀.fiberToSpecResidueField (f₀ (g' x))) := by
  have hfib : f₀ (g' x) = g (f x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m x) h.w
  rw [hfib]
  exact Set.ext_iff.mp (geometricallyReduced_fiber_set_eq_preimage_of_isPullback f₀ f g' g h) _

/-- **Stability of `X⁰` under generalization at a single fibre, over an affine base.** For a
flat sectioned morphism of finite presentation over `Spec A` and a point `x` of the source
whose fibre is geometrically reduced, every point specializing to `x` lies in `X⁰` as soon as
`x` does. -/
theorem mem_locus_of_specializes_over_spec_of_fiber {X : Scheme.{u}} (A : CommRingCat.{u})
    (f : X ⟶ Spec A) (s : Spec A ⟶ X) (hsec : s ≫ f = 𝟙 (Spec A))
    (hfp : FinitePresentation f) [Flat f] {x x' : X}
    (hgr : GeometricallyReduced (f.fiberToSpecResidueField (f x)))
    (hx : x ∈ (⟨X, Spec A, f, s, hsec⟩ : ConnectedAlongSection.{u}).locus) (hspec : x' ⤳ x) :
    x' ∈ (⟨X, Spec A, f, s, hsec⟩ : ConnectedAlongSection.{u}).locus := by
  let D : ConnectedAlongSection.{u} := ⟨X, Spec A, f, s, hsec⟩
  let Dg := (Algebra.adjoinFinsetDiagram ℤ A).op ⋙ Scheme.Spec
  let cBase := Scheme.Spec.mapCone (Algebra.adjoinFinsetCocone ℤ A).op
  let c : Cone Dg := { pt := Spec A, π := cBase.π }
  have hc : IsLimit c := by
    change IsLimit cBase
    exact isLimitOfPreserves _ (Algebra.isColimitAdjoinFinsetCocone ℤ A).op
  have : ∀ i, IsAffine (Dg.obj i) := fun i => inferInstanceAs (IsAffine (Spec _))
  obtain ⟨k, X₀, f₀, s₀, g', hfp₀, hflat₀, hs₀, hpb, hsc⟩ :=
    exists_flat_section_model_of_isLimit Dg c hc f s hsec hfp inferInstance
  let D₀ : ConnectedAlongSection.{u} := ⟨X₀, Dg.obj k, f₀, s₀, hs₀⟩
  -- The stage `k` is the spectrum of a finitely generated `ℤ`-algebra, hence Noetherian.
  have hNoeth : IsNoetherian (Dg.obj k) := by
    have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ ((unop k : Finset A) : Set A)) :=
      (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
    have : IsNoetherianRing (Algebra.adjoin ℤ ((unop k : Finset A) : Set A)) :=
      Algebra.FiniteType.isNoetherianRing ℤ _
    change IsNoetherian (Spec (CommRingCat.of (Algebra.adjoin ℤ ((unop k : Finset A) : Set A))))
    exact AlgebraicGeometry.IsNoetherian.mk
  have : LocallyOfFinitePresentation f₀ := hfp₀.1
  have hln : IsLocallyNoetherian D₀.X := LocallyOfFiniteType.isLocallyNoetherian f₀
  have hflat : Flat D₀.f := hflat₀
  -- The locus downstairs pulls back to the locus upstairs.
  have hloc : D.locus = g' ⁻¹' D₀.locus :=
    locus_eq_preimage_of_isPullback D₀ D g' (c.π.app k) hpb hsc
  -- Geometric reducedness of the one relevant fibre passes to the model.
  have hgr₀ : GeometricallyReduced (f₀.fiberToSpecResidueField (D₀.f (g' x))) :=
    (geometricallyReduced_fiber_iff_of_isPullback f₀ f g' (c.π.app k) hpb x).mp hgr
  -- Apply the locally Noetherian case to the model.
  rw [hloc]
  exact mem_locus_of_specializes_of_isLocallyNoetherian D₀ hfp₀ hgr₀ (by rwa [hloc] at hx)
    (hspec.map g'.continuous)

/-- **Stability of `X⁰` under generalization at a single fibre.** For a flat sectioned morphism
of finite presentation and a point `x` of the source whose fibre is geometrically reduced, every
point specializing to `x` lies in the locus `X⁰` of Situation 055L as soon as `x` does. -/
theorem mem_locus_of_specializes_of_fiber (D : ConnectedAlongSection.{u})
    (hfp : FinitePresentation D.f) [Flat D.f] {x x' : D.X}
    (hgr : GeometricallyReduced (D.f.fiberToSpecResidueField (D.f x)))
    (hx : x ∈ D.locus) (hspec : x' ⤳ x) : x' ∈ D.locus := by
  -- Shrink the target to an affine open containing the image of `x`.
  obtain ⟨i, z, hz⟩ := D.Y.affineCover.exists_eq (D.f x)
  let Rᵢ : CommRingCat.{u} := Classical.choose (Classical.choose_spec (D.Y.local_affine i))
  let g : Spec Rᵢ ⟶ D.Y := D.Y.affineCover.f i
  have hoig : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (D.Y.affineCover.f i))
  let prᵢ : pullback D.f g ⟶ D.X := pullback.fst D.f g
  let fᵢ : pullback D.f g ⟶ Spec Rᵢ := pullback.snd D.f g
  let sᵢ : Spec Rᵢ ⟶ pullback D.f g := pullback.lift (g ≫ D.s) (𝟙 _)
    (by rw [Category.assoc, D.section_fac, Category.comp_id, Category.id_comp])
  have hsecᵢ : sᵢ ≫ fᵢ = 𝟙 (Spec Rᵢ) := pullback.lift_snd _ _ _
  let Dᵢ : ConnectedAlongSection.{u} := ⟨pullback D.f g, Spec Rᵢ, fᵢ, sᵢ, hsecᵢ⟩
  have hPB : IsPullback prᵢ fᵢ D.f g := IsPullback.of_hasPullback D.f g
  have hloc : Dᵢ.locus = prᵢ ⁻¹' D.locus :=
    locus_eq_preimage_of_isPullback D Dᵢ prᵢ g hPB (pullback.lift_fst _ _ _)
  have hoipr : IsOpenImmersion prᵢ := MorphismProperty.of_isPullback hPB.flip hoig
  -- The two points lie in the open subscheme over the affine open.
  have hrange : ∀ y : D.X, D.f y ∈ Set.range g → y ∈ Set.range prᵢ := fun y hy => by
    rwa [IsOpenImmersion.range_pullbackFst g D.f]
  have hgx : D.f x ∈ Set.range g := ⟨z, hz⟩
  have hgx' : D.f x' ∈ Set.range g :=
    (hspec.map D.f.continuous).mem_open g.isOpenEmbedding.isOpen_range hgx
  obtain ⟨w, hw⟩ := hrange x hgx
  obtain ⟨w', hw'⟩ := hrange x' hgx'
  have hspecᵢ : w' ⤳ w :=
    (prᵢ.isOpenEmbedding.isEmbedding.isInducing.specializes_iff).mp (by rwa [hw, hw'])
  -- The hypotheses pass to the base change.
  have hfpᵢ : FinitePresentation fᵢ :=
    ⟨MorphismProperty.of_isPullback hPB hfp.1, MorphismProperty.of_isPullback hPB hfp.2.1,
      MorphismProperty.of_isPullback hPB hfp.2.2⟩
  have : Flat fᵢ := MorphismProperty.of_isPullback hPB inferInstance
  -- The one geometrically reduced fibre passes to the base change.
  have hgrᵢ : GeometricallyReduced (fᵢ.fiberToSpecResidueField (fᵢ w)) := by
    have := (geometricallyReduced_fiber_iff_of_isPullback D.f fᵢ prᵢ g hPB w).mpr
    rw [hw] at this
    exact this hgr
  have hxᵢ : w ∈ Dᵢ.locus := by rwa [hloc, Set.mem_preimage, hw]
  have hconcl : w' ∈ Dᵢ.locus :=
    mem_locus_of_specializes_over_spec_of_fiber Rᵢ fᵢ sᵢ hsecᵢ hfpᵢ hgrᵢ hxᵢ hspecᵢ
  rwa [hloc, Set.mem_preimage, hw'] at hconcl

end

end ConnectedAlongSection

end AlgebraicGeometry

end

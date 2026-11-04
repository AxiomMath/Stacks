module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleChartFromCompletion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyBaseChange
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalDescentAlongLimit
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing

/-!
# The Noetherian approximation reduction of Tag 0CBY

The first proof of [Stacks, Tag 0CBY] begins by reducing to a base of finite type over the
integers: the assertion is local on source and target, so the base may be assumed affine, its
coordinate ring is a filtered colimit of finite type `ℤ`-algebras, the family descends to a
finite stage by [Stacks, Tag 01ZM], it is still at-worst-nodal of relative dimension one at a
later stage by [Stacks, Tag 0C5F], the point stays a singular point of its fibre because the
relative singular subscheme commutes with base change ([Stacks, Tag 0C3I]), and the conclusion
for the stage gives the conclusion for the original family by base change.

This file carries out that reduction. The base change step is
`Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_isPullback`, which is not a
consequence of `nonempty_nodalChartNeighbourhood_of_etale`: the morphism from the limit to a
stage is not étale.

## Main results

* `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_resLE` — the chart form is
  local on source and target, which is the step by which the base may be assumed affine.
* `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_isPullback_isAffine` — the
  chart form base-changes along a morphism of affine bases, with the bases merely affine rather
  than literal spectra.
* `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_isLimit` — **the
  Noetherian approximation reduction**: if the chart form holds for every at-worst-nodal morphism
  of relative dimension one over a stage of a cofiltered system of affine schemes with affine
  transition morphisms, at every point of the relative singular subscheme, then it holds for the
  base change of such a morphism to the limit.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C5F](https://stacks.math.columbia.edu/tag/0C5F)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks

universe u

namespace Stacks.NodalEtaleLocalStructure

/-- **The chart form of Tag 0CBY base-changes along a morphism of affine bases.** This is
`nonempty_nodalChartNeighbourhood_of_isPullback` with the two bases merely affine instead of
literal spectra; the two forms differ by the canonical isomorphism of an affine scheme with the
spectrum of its ring of global sections, along which the chart form transfers because an
isomorphism is étale. -/
public theorem nonempty_nodalChartNeighbourhood_of_isPullback_isAffine
    {X₀ X S₀ S : Scheme.{u}} [IsAffine S₀] [IsAffine S]
    {p : X ⟶ X₀} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : S ⟶ S₀}
    (hsq : IsPullback p f f₀ g) {x : X} {x₀ : X₀} (hx : p.base x = x₀)
    (d : NodalChartNeighbourhood f₀ x₀) :
    Nonempty (NodalChartNeighbourhood f x) := by
  obtain ⟨d'⟩ := nonempty_nodalChartNeighbourhood_of_etale (f := f₀ ≫ S₀.isoSpec.hom)
    (x' := x₀) (x := x₀) (𝟙 X₀) S₀.isoSpec.hom (by simp) (by simp) d
  obtain ⟨γ, hγ⟩ := Spec.map_surjective (S.isoSpec.inv ≫ g ≫ S₀.isoSpec.hom)
  have hbot : IsPullback g S.isoSpec.hom S₀.isoSpec.hom (Spec.map γ) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [hγ]
    simp
  obtain ⟨d''⟩ := nonempty_nodalChartNeighbourhood_of_isPullback γ (hsq.paste_vert hbot) hx d'
  exact nonempty_nodalChartNeighbourhood_of_etale (f := f) (x' := x) (x := x) (𝟙 X)
    S.isoSpec.inv (by simp) (by simp) d''

/-- **The chart form of Tag 0CBY is local on source and target.** A chart for the restriction of
`f` to an open `U` of the source mapping into an open `V` of the target, at a point of `U`, is a
chart for `f` at that point: the two inclusions are open immersions, hence étale.

This is the step "the question is local on `X` and `S`, hence we may assume `X` and `S` affine"
of the first proof of Tag 0CBY. -/
public theorem nonempty_nodalChartNeighbourhood_of_resLE
    {X S : Scheme.{u}} {f : X ⟶ S} (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V)
    {x : X} (hx : x ∈ U)
    (d : NodalChartNeighbourhood (f.resLE V U e) ⟨x, hx⟩) :
    Nonempty (NodalChartNeighbourhood f x) :=
  nonempty_nodalChartNeighbourhood_of_etale (f := f) (x' := ⟨x, hx⟩) (x := x) U.ι V.ι
    (Scheme.Hom.resLE_comp_ι f e).symm rfl d

/-! ### Descent of the chart form along a cofiltered limit -/

/-- At-worst-nodality of relative dimension one is invariant under isomorphism. -/
private instance : MorphismProperty.RespectsIso
    (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Nodality of a base change read through `CategoryTheory.Over.pullback`, which is the shape in
which [Stacks, Tag 0C5F] is stated, is nodality of the second projection of the pullback: the two
differ by the isomorphism `pullback (𝟙 S) h ≅ T`. -/
public theorem isAtWorstNodal_overPullback_iff {S T : Scheme.{u}} (h : T ⟶ S) {Y : Scheme.{u}}
    (q : Y ⟶ S) :
    IsAtWorstNodalOfRelativeDimensionOne
        ((Over.pullback h).map (Over.homMk q (by simp) :
          Over.mk q ⟶ Over.mk (𝟙 S))).left ↔
      IsAtWorstNodalOfRelativeDimensionOne (pullback.snd q h) := by
  have hiso : IsIso (pullback.snd (𝟙 S) h) :=
    (MorphismProperty.isomorphisms Scheme.{u}).of_isPullback
      (IsPullback.of_hasPullback (𝟙 S) h) inferInstance
  rw [← MorphismProperty.cancel_right_of_respectsIso
    (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) _
    (pullback.snd (𝟙 S) h)]
  exact Iff.of_eq (congrArg _ (Over.w ((Over.pullback h).map (Over.homMk q (by simp) :
    Over.mk q ⟶ Over.mk (𝟙 S)))))

/-- **The absolute Noetherian approximation reduction of Tag 0CBY.** Let a scheme `c.pt` be the
limit of a cofiltered inverse system of *affine* schemes with affine transition morphisms, let
`f : X ⟶ c.pt` be of finite presentation and at-worst-nodal of relative dimension one, and let
`x` be a point of the relative singular subscheme of `f`. If the étale local chart of Tag 0CBY
exists for every at-worst-nodal morphism of relative dimension one over a stage of the system, at
every point of its relative singular subscheme, then it exists for `f` at `x`.

This is the first step of the first proof of Tag 0CBY: with `c.pt = Spec R` and the stages
`Spec R_i` for a presentation of `R` as a filtered colimit of finite type `ℤ`-algebras, it
reduces the lemma to a base of finite type over the integers. The three inputs are [Stacks,
Tag 01ZM] part (1), which produces a model `Y ⟶ D.obj i` of `f` over a stage; [Stacks, Tag 0C5F],
which makes the model at-worst-nodal of relative dimension one after passing to a later stage;
and [Stacks, Tag 0C3I] at index one, which says that the relative singular subscheme commutes
with base change and therefore carries `x` to a point of the relative singular subscheme of the
model. The conclusion for the model gives the conclusion for `f` by
`nonempty_nodalChartNeighbourhood_of_isPullback_isAffine`. -/
public theorem nonempty_nodalChartNeighbourhood_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c)
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, IsAffine (D.obj i)] [IsAffine c.pt]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    (hfp : FinitePresentation f) (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    {x : X} (hxsing : x ∈ Set.range (relativeSingularIdeal f).subschemeι.base)
    (H : ∀ (i : I) (Z : Scheme.{u}) (r : Z ⟶ D.obj i) (z : Z),
      IsAtWorstNodalOfRelativeDimensionOne r →
      z ∈ Set.range (relativeSingularIdeal r).subschemeι.base →
      Nonempty (NodalChartNeighbourhood r z)) :
    Nonempty (NodalChartNeighbourhood f x) := by
  classical
  -- a model of `f` over a finite stage
  obtain ⟨i, Y, q, g, hqfp, hpb⟩ :=
    AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation D c hc f hfp
  have : QuasiCompact q := hqfp.2.1
  have : QuasiSeparated q := hqfp.2.2
  have : LocallyOfFinitePresentation q := hqfp.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  -- the base change of the model to the limit is nodal, in the shape Tag 0C5F consumes
  have hmodel : IsAtWorstNodalOfRelativeDimensionOne (pullback.snd q (c.π.app i)) := by
    have hsnd : (hpb.isoIsPullback Y c.pt
          (IsPullback.of_hasPullback q (c.π.app i))).hom ≫ pullback.snd q (c.π.app i) = f :=
      hpb.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback q (c.π.app i))
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u})
      (hpb.isoIsPullback Y c.pt (IsPullback.of_hasPullback q (c.π.app i))).hom
      (pullback.snd q (c.π.app i)), hsnd]
    exact hf
  -- Tag 0C5F: the model is nodal after base change to a later stage
  have : CompactSpace (Over.mk q).left := (inferInstance : CompactSpace Y)
  have : QuasiSeparatedSpace (Over.mk q).left := (inferInstance : QuasiSeparatedSpace Y)
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := (inferInstance : CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    (inferInstance : QuasiSeparatedSpace (D.obj i))
  obtain ⟨j, a, hja⟩ :=
    AlgebraicGeometry.exists_isAtWorstNodalOfRelativeDimensionOne_baseChange_of_limitBaseChange
    D c i (Over.mk q) (Over.mk (𝟙 (D.obj i)))
    (Over.homMk q (by simp)) (by simpa using hqfp.1) hc
    ((isAtWorstNodal_overPullback_iff (c.π.app i) q).mpr hmodel)
  rw [isAtWorstNodal_overPullback_iff] at hja
  -- the model over the later stage, and `f` as its base change
  have hA : IsPullback (pullback.fst q (D.map a)) (pullback.snd q (D.map a)) q (D.map a) :=
    IsPullback.of_hasPullback q (D.map a)
  have hw : g ≫ q = (f ≫ c.π.app j) ≫ D.map a := by
    rw [Category.assoc, c.w a]
    exact hpb.w
  set g' : X ⟶ (pullback q (D.map a) : Scheme.{u}) := hA.lift g (f ≫ c.π.app j) hw with hg'
  have hg'fst : g' ≫ pullback.fst q (D.map a) = g := hA.lift_fst _ _ _
  have hg'snd : g' ≫ pullback.snd q (D.map a) = f ≫ c.π.app j := hA.lift_snd _ _ _
  have hB : IsPullback g' f (pullback.snd q (D.map a)) (c.π.app j) := by
    refine IsPullback.of_right ?_ hg'snd hA
    rw [hg'fst, c.w a]
    exact hpb
  -- the point stays a point of the relative singular subscheme
  have : LocallyOfFinitePresentation (pullback.snd q (D.map a)) :=
    AlgebraicGeometry.locallyOfFinitePresentation hja.1.1
  have hcomap : (relativeSingularIdeal (pullback.snd q (D.map a))).comap g' =
      relativeSingularIdeal f :=
    relativeSingularIdeal_comap_of_isPullback g' f (pullback.snd q (D.map a)) (c.π.app j) hB
  have hrange : Set.range (relativeSingularIdeal f).subschemeι.base =
      g'.base ⁻¹' Set.range (relativeSingularIdeal (pullback.snd q (D.map a))).subschemeι.base := by
    rw [← hcomap]
    simp
  rw [hrange] at hxsing
  -- the conclusion at the stage, base changed back to the limit
  obtain ⟨d⟩ := H j (pullback q (D.map a)) (pullback.snd q (D.map a)) (g'.base x) hja hxsing
  exact nonempty_nodalChartNeighbourhood_of_isPullback_isAffine hB rfl d

end Stacks.NodalEtaleLocalStructure

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Descent of the pairs of Stacks 0D3W from the charts of an algebraic space

In Situation 0CZY a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf site
is given, and Stacks 0D3W identifies the morphisms of sheaves from an algebraic space `T` into the
Hilbert functor `Hilb_{X/Y}` with the pairs `(h, Z)` of a morphism `h : T ⟶ Y` and a closed
subspace `Z ⊆ X_T = X ×_{Y, h} T` which is of finite presentation, flat and proper over `T`:

`Mor_{Sh((Sch/S)_fppf)}(T, Hilb_{X/Y}) = {(h, Z) : h : T ⟶ Y, Z ⊆ X_T closed with Z ⟶ T of`
`finite presentation, flat and proper}`.

The bijection `AlgebraicGeometry.Space.morEquivSpaceHilbertFamily` exists for an arbitrary
algebraic space `T` given the descent input `AlgebraicGeometry.Space.IsHilbertLocalOnBase f T`:
that the four conditions on a subfunctor of `X_T` follow from the same conditions on its inverse
images in the charts `V ⟶ T` from the schemes of the site. This file proves that input for every
algebraic space `T`, and so states Stacks 0D3W with no hypothesis beyond Situation 0CZY.

## Main results

* `AlgebraicGeometry.Space.hilbertChartSection_comp`: a morphism to `X_T` from a scheme `V` of the
  site factors through `X_V ⟶ X_T` for the chart `V ⟶ T` it determines.
* `AlgebraicGeometry.Space.isClosedImmersion_ι_of_charts`: a subfunctor of `X_T` whose inverse
  image in every chart is closed is itself closed.
* `AlgebraicGeometry.Space.isHilbertLocalOnBase`: the descent input of Stacks 0D3W, for every
  algebraic space `T`.
* `AlgebraicGeometry.Space.morEquivSpaceHilbertFamilyOfAlgebraicSpace`: Stacks 0D3W, the displayed
  identification as a bijection, for an arbitrary algebraic space `T`.

## Implementation notes

**The descent step.** Stacks proves 0D3W from 0D3V through `Hilb = Quot_{𝒪_X}`
(Stacks 0D00); the descent there is that of quasi-coherent quotients along an étale chart
`U ⟶ T`. For the Hilbert functor the descended object is a subfunctor of `X_T`, and it is already
glued by `AlgebraicGeometry.Space.hilbertMorSubfunctor`; what remains is to descend the four
conditions on it, which is done here directly, without passing through quotient modules.

* *Closedness* needs no covering at all. Being a closed immersion of presheaves is a condition on
  the base changes along morphisms `V ⟶ X_T` from schemes of the site, and each of those factors
  through the chart `V ⟶ T` it determines, where the hypothesis applies. Once `Z ⟶ X_T` is a
  closed immersion it is representable, so `Z` is an algebraic space (Stacks 02WY).
* *Finite presentation, flatness and properness* over `T` are then descended along one surjective
  étale scheme atlas `U ⟶ T` (Stacks 025Y). Such an atlas is a one-member fppf covering of `T`, the
  inverse image of `Z` in `X_U` is the base change of `Z ⟶ T` along it
  (`AlgebraicGeometry.Space.isPullback_preimage_chart`), and the three properties are local on the
  base for the fppf topology: local finite presentation by Stacks 041T, quasi-compactness by
  Stacks 041L, quasi-separatedness by Stacks 041N, flatness by Stacks 041W and properness by
  Stacks 0422.

## References

* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_HilbertFunctorPointsDescent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, at high priority. -/
local instance (priority := high) hasPullback_presheaf_HilbertFunctorPointsDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The section of `X_V` over `V` through which a morphism `g : V ⟶ X_T` from a scheme of the
site factors: its first projection is that of `g` and its second projection is the identity, the
base change being taken along the chart `V ⟶ T` given by the second projection of `g`. -/
def hilbertChartSection (f : X ⟶ Y) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : G ⟶ Y.obj)
    {V : BigFppfOver B S hS} (g : yoneda.obj V ⟶ pullback f.hom c) :
    yoneda.obj V ⟶ pullback f.hom ((g ≫ pullback.snd f.hom c) ≫ c) :=
  pullback.lift (g ≫ pullback.fst f.hom c) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc])

/-- **A morphism to `X_T` from a scheme of the site factors through the chart it determines.** -/
@[reassoc (attr := simp)]
theorem hilbertChartSection_comp (f : X ⟶ Y) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (c : G ⟶ Y.obj) {V : BigFppfOver B S hS} (g : yoneda.obj V ⟶ pullback f.hom c) :
    hilbertChartSection f c g ≫ hilbertChartMap f (g ≫ pullback.snd f.hom c) rfl = g := by
  apply pullback.hom_ext
  · rw [Category.assoc, hilbertChartMap_fst, hilbertChartSection, pullback.lift_fst]
  · rw [Category.assoc, hilbertChartMap_snd, hilbertChartSection, pullback.lift_snd_assoc,
      Category.id_comp]

/-- **Closedness of a subfunctor of `X_T` is detected by the charts of `T`.** If the inverse image
of a subfunctor `Z` of `X_T` along the transition map of every morphism `V ⟶ T` from a scheme of
the big fppf site is a closed immersion, then so is the inclusion of `Z`. -/
theorem isClosedImmersion_ι_of_charts (f : X ⟶ Y) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (c : G ⟶ Y.obj) (Z : Subfunctor (pullback f.hom c))
    (h : ∀ (V : BigFppfOver B S hS) (k : yoneda.obj V ⟶ G),
      IsClosedImmersion B S hS (Z.preimage (hilbertChartMap f k (rfl : k ≫ c = k ≫ c))).ι) :
    IsClosedImmersion B S hS Z.ι := by
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun V g ↦ ?_
  have hk := h V (g ≫ pullback.snd f.hom c)
  obtain ⟨b, snd, fst, hsq⟩ := hk.rep (hilbertChartSection f c g)
  refine ⟨b, fst ≫ Z.fromPreimage _, snd, ?_, hk.property _ fst snd hsq⟩
  have hpaste := hsq.paste_horiz
    (Subfunctor.isPullback_preimage (hilbertChartMap f (g ≫ pullback.snd f.hom c) rfl) Z)
  rwa [hilbertChartSection_comp] at hpaste

/-- **The descent input of Stacks 0D3W holds for every algebraic space.** Being a closed subspace
of `X_T` which is of finite presentation, flat and proper over `T` may be tested in the charts of
`T`, for an arbitrary algebraic space `T` over `S`. -/
theorem isHilbertLocalOnBase (f : X ⟶ Y) (T : AlgebraicSpaces B S hS) :
    IsHilbertLocalOnBase f T := by
  intro h Z hcharts
  have hXT : IsAlgebraicSpace B S hS (pullback f.hom h.hom) :=
    isAlgebraicSpace_pullback B S hS f.hom h.hom X.2 T.2 Y.2
  have hci : IsClosedImmersion B S hS Z.ι :=
    isClosedImmersion_ι_of_charts f h.hom Z fun V k ↦ (hcharts V _ k rfl).1.2
  have hZ : IsClosedSubspace B S hS Z :=
    ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS Z.ι hci.rep hXT, hci⟩
  obtain ⟨U, a, hsurj, het⟩ := T.2.exists_atlas
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hXU : IsAlgebraicSpace B S hS (pullback f.hom (a ≫ h.hom)) :=
    isAlgebraicSpace_pullback B S hS f.hom (a ≫ h.hom) X.2 hU Y.2
  obtain ⟨hpre, hfp, hfl, hpr⟩ := hcharts U (a ≫ h.hom) a rfl
  have hpb := isPullback_preimage_chart f T.2 hU a rfl Z hZ hXT hXU hpre
  have ha : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 het
  have hsurj' : IsSurjective B S hS a :=
    (surjective_iff_surjective_pointsMap B S hS T.obj T.2 U a).1 hsurj
  have hflat := isFlat_atlas B S hS T.2 ha
  have hlfp := isLocallyOfFinitePresentation_atlas B S hS T.2 ha
  have : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => IsFlat B S hS g.hom)
      (Topology.fppf.precoverage.{u, 0} B S hS) :=
    (isFlat_isLocalAtTarget_fpqc B S hS).of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)
  refine ⟨hZ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact prop_of_isPullback_of_fppf.{u, 0} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        IsLocallyOfFinitePresentation B S hS g.hom) hpb hsurj' hflat hlfp hfp.1
  · exact prop_of_isPullback_of_fppf.{u, 0} B S hS (quasiCompactProperty B S hS) hpb hsurj'
      hflat hlfp hfp.2.1
  · exact prop_of_isPullback_of_fppf.{u, 0} B S hS (quasiSeparatedProperty B S hS) hpb hsurj'
      hflat hlfp hfp.2.2
  · exact prop_of_isPullback_of_fppf.{u, 0} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => IsFlat B S hS g.hom) hpb hsurj'
      hflat hlfp hfl
  · exact prop_of_isPullback_of_fppf.{u, 0} B S hS (properProperty B S hS) hpb hsurj'
      hflat hlfp hpr

/-- **The points of the Hilbert functor with values in an algebraic space.** In Situation 0CZY,
for an algebraic space `T` over `S` the morphisms of sheaves on the big fppf site of `S` from `T`
into the Hilbert presheaf `Hilb_{X/Y}` are the pairs `(h, Z)` consisting of a morphism `h : T ⟶ Y`
of algebraic spaces and a closed subspace `Z` of `X_T = X ×_{Y, h} T` which is of finite
presentation, flat and proper over `T`.

The identification is a bijection, given as an `Equiv`; the finite presentation of `f` imposed by
Situation 0CZY is not needed. The sheaf of `T` is lifted to the universe of `Hilb_{X/Y}`, which
adds or loses no morphism. -/
@[stacks 0D3W "the identification as a bijection, for an arbitrary algebraic space, \
  unconditionally"]
def morEquivSpaceHilbertFamilyOfAlgebraicSpace (f : X ⟶ Y) (T : AlgebraicSpaces B S hS) :
    (T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f) ≃ SpaceHilbertFamily f T :=
  morEquivSpaceHilbertFamily f T (isHilbertLocalOnBase f T)

end AlgebraicGeometry.Space

end

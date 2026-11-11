module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedChartTopStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulaySlice
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingRegularSequence

/-!
# Local finite presentation of a chart sliced by a regular sequence (Stacks 06MD)

Let `𝒳` be an algebraic stack over `S`, let `U` be an algebraic space with a 1-morphism
`f : U ⟶ 𝒳` which is flat and locally of finite presentation, let `Spec k ⟶ 𝒳` be a
field-valued point and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`. Let
`f₁, …, f_r ∈ Γ(U, 𝒪_U)` and let `z` be a geometric point of `F` at which the `f_i` map to a
regular sequence in the étale local ring `𝒪_{F, z̄}`. Stacks 06MD asserts that after replacing
`U` by an open subspace containing `p(z)` the zero locus `V(f₁, …, f_r) ⟶ 𝒳` is flat and locally
of finite presentation.

This file supplies the locally-of-finite-presentation step of that conclusion, which holds over
*every* open subspace of `U`. The full statement, both conjuncts at the hypotheses the source
states, is
`exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`
in `StacksFrontier/AlgebraicGeometry/Stacks/ChartSlicingFlatness.lean`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff`: a morphism
  of algebraic spaces over `S` is locally of finite presentation exactly when the 1-morphism of
  algebraic stacks it induces is.
* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_ι_zeroLocusOnOpen`: the closed immersion
  `V(f₁, …, f_r) ∩ V ⟶ V` is locally of finite presentation as soon as `V(f₁, …, f_r) ⟶ U` is,
  the former being a base change of the latter.
* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_zeroLocusOnOpenToStack`: for *every*
  open subspace `V ⊆ U`, the 1-morphism `V(f₁, …, f_r) ∩ V ⟶ 𝒳` is locally of finite
  presentation.
* `AlgebraicGeometry.Stack.exists_openSubspace_isLocallyOfFinitePresentation_zeroLocus`: the same,
  in the shape of the conclusion of Stacks 06MD, with the open subspace containing `p(z)` supplied.

## Implementation notes

The locally-of-finite-presentation conjunct of Stacks 06MD needs neither a chart of `𝒳` nor any
descent: the closed immersion `V(f₁, …, f_r) ⟶ U` is locally of finite presentation, so the
composite with `U ⟶ 𝒳` is, by Stacks 03XQ at the level of algebraic stacks. That is the same
argument `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_vanishingSubfunctor_comp` makes
for a morphism of algebraic spaces, read one level up through the induced 1-morphism of
algebraic stacks, and it is settled before any shrinking of `U`.

The results here take local finite presentation of the closed immersion `V(f₁, …, f_r) ⟶ U` as
the argument `hslice`; the library proves it as
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_ι_vanishingSubfunctor`, and that is how
Stacks 06MD discharges it. Its restriction to an open subspace is a genuine base change:
`V(f₁, …, f_r) ∩ V` is the inverse image of Stacks 083Q, cartesian over `V(f₁, …, f_r)` by
`CategoryTheory.Subfunctor.isPullback_preimage`, and local finite presentation is stable under
base change by Stacks 03XR.

The bridge `isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff` is the local-finite-
presentation companion of
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_algebraicSpaceStackMap_iff` and is proved the same
way: the universal smooth-diagram condition of Stacks 06FS is traded for the existential one and
then read on the representable source and target by Stacks 06FM, through the identity
comparisons of Stacks 04SW. What Stacks 06FM asks of the property is that it be smooth local on
source and target, which for local finite presentation is Stacks 06FC.

## References

* [Stacks Project, Lemma 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06CN](https://stacks.math.columbia.edu/tag/06CN)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Local finite presentation read between algebraic spaces and algebraic stacks -/

/-- **A morphism of algebraic spaces over `S` is locally of finite presentation exactly when the
1-morphism of algebraic stacks it induces is.** The smooth-diagram test of Stacks 06FS is read on
the representable source and target by Stacks 06FM, through the identity comparisons of
Stacks 04SW; what Stacks 06FM asks of the property is that it be smooth local on source and
target, which for local finite presentation is Stacks 06FC. -/
theorem isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsLocallyOfFinitePresentation B S hS g := by
  have hloc := Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  have hTs := isAlgebraicStack_fibredCategory.{u, w} B S hS T hT
  have hGs := isAlgebraicStack_fibredCategory.{u, w} B S hS G hG
  refine Iff.trans (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _ hloc hTs hGs _) ?_
  refine Iff.trans (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _ hloc hTs hGs
    T G hT hG (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _) ?_
  rw [representingMap_associatedMap B S hS T G g]

/-! ### The zero locus on an open subspace -/

variable (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)

variable {r : ℕ}
  (a : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)

/-- **The restriction of the zero locus to an open subspace is locally of finite presentation
over that open subspace**, as soon as the closed immersion `V(f₁, …, f_r) ⟶ U` is locally of
finite presentation over `U`.

`V(f₁, …, f_r) ∩ V` is the inverse image of Stacks 083Q, so it is cartesian over
`V(f₁, …, f_r)` by `CategoryTheory.Subfunctor.isPullback_preimage`, and being locally of finite
presentation is stable under base change by Stacks 03XR. -/
theorem isLocallyOfFinitePresentation_ι_zeroLocusOnOpen
    (hslice : Space.IsLocallyOfFinitePresentation B S hS (chartZeroLocus B S hS U hU a).ι)
    (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V) :
    Space.IsLocallyOfFinitePresentation B S hS (zeroLocusOnOpen B S hS U hU a V).ι := by
  have hZ : IsAlgebraicSpace B S hS (chartZeroLocus B S hS U hU a).toFunctor :=
    (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
  have hP : IsAlgebraicSpace B S hS (zeroLocusOnOpen B S hS U hU a V).toFunctor :=
    (isClosedSubspace_zeroLocusOnOpen B S hS U hU a V hV).1
  have hsq := Subfunctor.isPullback_preimage V.ι (chartZeroLocus B S hS U hU a)
  let U' : AlgebraicSpaces B S hS := ⟨U, hU⟩
  let V' : AlgebraicSpaces B S hS := ⟨V.toFunctor, hV.1⟩
  let Z' : AlgebraicSpaces B S hS := ⟨(chartZeroLocus B S hS U hU a).toFunctor, hZ⟩
  let P' : AlgebraicSpaces B S hS := ⟨(zeroLocusOnOpen B S hS U hU a V).toFunctor, hP⟩
  exact (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (show IsPullback
      (ObjectProperty.homMk ((chartZeroLocus B S hS U hU a).fromPreimage V.ι) : P' ⟶ Z')
      (ObjectProperty.homMk (zeroLocusOnOpen B S hS U hU a V).ι : P' ⟶ V')
      (ObjectProperty.homMk (chartZeroLocus B S hS U hU a).ι : Z' ⟶ U')
      (ObjectProperty.homMk V.ι : V' ⟶ U') from IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) hsq) hslice

/-! ### The locally-of-finite-presentation conjunct of Stacks 06MD -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- **The zero locus on an open subspace is locally of finite presentation over `𝒳`.** The
inclusion `V(f₁, …, f_r) ∩ V ⟶ V` is locally of finite presentation by
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_ι_zeroLocusOnOpen`, the open immersion
`V ⟶ U` is by Stacks 06CN, hence so is the composite `V(f₁, …, f_r) ∩ V ⟶ U` by Stacks 03XQ;
that passes to the induced 1-morphism of algebraic stacks and composes with `f`.

No shrinking of `U` is involved: the statement holds for every open subspace `V ⊆ U`. -/
theorem isLocallyOfFinitePresentation_zeroLocusOnOpenToStack
    (hf : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hslice : Space.IsLocallyOfFinitePresentation B S hS (chartZeroLocus B S hS U hU a).ι)
    (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV) := by
  have hP := (isClosedSubspace_zeroLocusOnOpen B S hS U hU a V hV).1
  refine AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS _ f ?_ hf
  refine (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hP hU _).2 ?_
  exact Space.isLocallyOfFinitePresentation_comp B S hS hP hV.1 hU _ _
    (isLocallyOfFinitePresentation_ι_zeroLocusOnOpen B S hS U hU a hslice V hV)
    (Space.isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hV.2)

variable (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

/-- **The open subspace of Stacks 06MD over which `V(f₁, …, f_r) ⟶ 𝒳` is locally of finite
presentation.** Let `𝒳` be an algebraic stack over `S`, let `U` be an algebraic space with a
1-morphism `f : U ⟶ 𝒳` which is flat and locally of finite presentation, let `Spec k ⟶ 𝒳` be a
field-valued point, and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`. Let
`f₁, …, f_r ∈ Γ(U, 𝒪_U)` and let `z` be a geometric point of `F` at which the `f_i` map to a
regular sequence in `𝒪_{F, z̄}`. Then there is an open subspace of `U` containing `p(z)` over
which `V(f₁, …, f_r) ⟶ 𝒳` is locally of finite presentation; the whole of `U` serves.

The argument `hslice` is local finite presentation of the closed immersion `V(f₁, …, f_r) ⟶ U`,
which `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_ι_vanishingSubfunctor` proves. The
flatness and regular-sequence arguments are not used. Stacks 06MD itself, flatness included, is
`exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`. -/
theorem exists_openSubspace_isLocallyOfFinitePresentation_zeroLocus
    (_hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (z : Space.GeometricPoint B S hS Fsp)
    (_hreg : FibreIsRegularSequenceAt.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z)
    (hslice : Space.IsLocallyOfFinitePresentation B S hS (chartZeroLocus B S hS U hU a).ι) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      Space.pointsMap B S hS Fsp
          (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z.image ∈
        Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV) :=
  ⟨⊤, Space.isOpenSubspace_top hU,
    (Space.range_pointsMap_ι_top B S hS).symm ▸ Set.mem_univ _,
    isLocallyOfFinitePresentation_zeroLocusOnOpenToStack.{u, w} B S hS U hU a 𝒳 f hfp hslice _ _⟩

end AlgebraicGeometry.Stack

end

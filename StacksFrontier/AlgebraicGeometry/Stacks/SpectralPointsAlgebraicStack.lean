module

public import Mathlib.Topology.Spectral.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStackKolmogorov
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsEquivalenceHomeomorph
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBaseQuantifier
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.Topology.Spectral.PrespectralOpenSurjection

/-!
# The topological space of an algebraic stack with quasi-compact diagonal is spectral

Let `𝒳` be an algebraic stack over `S` whose absolute diagonal `Δ : 𝒳 ⟶ 𝒳 ×_{Spec ℤ} 𝒳` is
quasi-compact. This file proves that the topological space of points `|𝒳|` of Stacks 04XL is
spectral when `𝒳` is moreover quasi-compact (**Stacks 0DQN**), in particular when `𝒳` is
quasi-compact and quasi-separated (**Stacks 0DQP**), and that in general `|𝒳|` is covered by
spectral open subspaces and is sober (**Stacks 0DQQ**).

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompact_diagonal`: a 1-morphism from
  the algebraic stack of a quasi-compact scheme to `𝒳` is quasi-compact.
* `AlgebraicGeometry.Stack.isCompact_preimage_image_pointsMap`: for a quasi-compact 1-morphism
  from the algebraic stack of a scheme, the saturation of a quasi-compact open of the source
  point space is quasi-compact.
* `AlgebraicGeometry.Stack.spectralSpace_points_of_isQuasiCompact_diagonal`: **Stacks 0DQN**.
* `AlgebraicGeometry.Stack.spectralSpace_points_of_isAbsolutelyQuasiSeparated`: **Stacks 0DQP**.
* `AlgebraicGeometry.Stack.exists_spectralSpace_cover_and_stacksSober`: **Stacks 0DQQ**.

## Implementation notes

The argument is not the source's. The source shows that `|𝒳|` is sober by passing to a reduced
closed substack and quoting the existence of a dense open substack which is a gerbe (Stacks
06RC). Here instead the whole argument runs on one smooth surjective chart `φ : |U| ⟶ |𝒳|` by an
affine scheme, and the topology is the general statement
`spectralSpace_of_isOpenMap_surjective`: a continuous open surjection from a spectral space onto
a Kolmogorov space whose saturations of quasi-compact opens are quasi-compact has spectral
target. The three inputs are:

* the Kolmogorov property of `|𝒳|`, which is Stacks 0GW7 for the decent algebraic stack `𝒳`,
  decency being Stacks 0GW2 at quasi-compact diagonal;
* openness, continuity and surjectivity of `φ`, which are Stacks 04XL, Stacks 06R7 and the choice
  of the chart;
* quasi-compactness of saturations. The chart `U ⟶ 𝒳` is a quasi-compact 1-morphism, so its base
  change along the algebraic stack of a quasi-compact open subscheme `V ⊆ U` is quasi-compact,
  and by Stacks 04XH the image of that base change in `|U|` is the saturation of `V`.

The quasi-compactness of `U ⟶ 𝒳` is where the *absolute* diagonal is needed: over a base `S`
which is not quasi-separated the structure morphism of an affine scheme is not quasi-compact, so
the cancellation of quasi-compactness along a 1-morphism with quasi-compact relative diagonal is
run over `Spec ℤ`, after Construction A of Stacks 04X5, and its conclusion is carried back to `S`
by the base-independence of the condition of Stacks 04XB. The quasi-compactness of Construction A
of the algebraic stack of `U`, which the cancellation needs, comes from the equivalence
`AlgebraicGeometry.Stack.factorSliceInverse` with the algebraic stack of `U` viewed over
`Spec ℤ`.

The absolute diagonal is read as in Stacks 050D and Stacks 0GW2: the relative diagonal of the
structure morphism of `𝒳` viewed over the terminal scheme, quasi-compact in the sense of
Stacks 050U. The containment of the terminal scheme in the site is
`AlgebraicGeometry.BigFppfSite.contains_terminal` and is not a hypothesis.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 0DQN](https://stacks.math.columbia.edu/tag/0DQN)
* [Stacks Project, Tag 0DQP](https://stacks.math.columbia.edu/tag/0DQP)
* [Stacks Project, Tag 0DQQ](https://stacks.math.columbia.edu/tag/0DQQ)
* [Stacks Project, Tag 0GW2](https://stacks.math.columbia.edu/tag/0GW2)
* [Stacks Project, Tag 0GW7](https://stacks.math.columbia.edu/tag/0GW7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

attribute [local instance] pointTopology reprPointTopology

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Construction A of the algebraic stack of a quasi-compact scheme over `S` is quasi-compact:
its point space is the image of the point space of the algebraic stack of the same scheme over
`S'`, along the equivalence `AlgebraicGeometry.Stack.factorSliceInverse`. -/
theorem isQuasiCompactStack_changeBase_schemeStack (S' : Scheme.{u}) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (U : BigFppfOver B S hS)
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    IsQuasiCompactStack.{u, w} B S' hS'
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g (schemeStack.{u, w} B S hS U)).val
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (schemeStack.{u, w} B S hS U)).property := by
  let := pointTopology B S' hS' (schemeFibredCategory B S' hS' ((Over.map g).obj U))
  have hq := isQuotientMap_pointsMap_of_isEquivalence B S' hS'
    (schemeFibredCategory B S' hS' ((Over.map g).obj U))
    (changeBaseFiberedInGroupoids B S S' hS hS' g (schemeFibredCategory B S hS U))
    (factorSliceInverse B S S' hS hS' g U) (isEquivalence_factorSliceInverse B S S' hS hS' g U)
  have : CompactSpace (points B S' hS' (schemeFibredCategory B S' hS' ((Over.map g).obj U)).val
      (schemeFibredCategory B S' hS' ((Over.map g).obj U)).property) :=
    isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B S' hS' ((Over.map g).obj U) hU
  exact hq.surjective.compactSpace hq.continuous

/-- **A 1-morphism from a quasi-compact scheme into an algebraic stack with quasi-compact absolute
diagonal is quasi-compact.**

Over `Spec ℤ` the structure morphism of the scheme is quasi-compact, `Spec ℤ` being
quasi-separated, so the cancellation of quasi-compactness along a 1-morphism with quasi-compact
relative diagonal applies there; the conclusion is carried back to `S` through the condition of
Stacks 04XB, which does not depend on the base. -/
theorem isQuasiCompactMorphism_of_isQuasiCompact_diagonal (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) B.contains_terminal
        (structureMorphism B (⊤_ Scheme.{u}) B.contains_terminal
          (AlgebraicStacks.viewOverIntegers B S hS B.contains_terminal 𝒳))))
    (U : BigFppfOver B S hS) (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    IsQuasiCompactMorphism.{u, w} B S hS f := by
  let g : B.obj hS ⟶ B.obj B.contains_terminal := ⟨terminal.from S⟩
  let fZ : changeBaseAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS B.contains_terminal g
      (schemeStack.{u, w} B S hS U) ⟶
      AlgebraicStacks.viewOverIntegers B S hS B.contains_terminal 𝒳 :=
    changeBaseHomAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS B.contains_terminal g f
  have hstr := isQuasiCompactMorphism_structureMorphism.{u, w} B (⊤_ Scheme.{u})
    B.contains_terminal inferInstance _
    (isQuasiCompactStack_changeBase_schemeStack.{u, w} B S hS (⊤_ Scheme.{u})
      B.contains_terminal g U hU)
  have hfZ : IsQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal fZ :=
    isQuasiCompactMorphism_of_comp_of_isQuasiCompact_relativeDiagonal B (⊤_ Scheme.{u})
      B.contains_terminal fZ _ (by rw [comp_structureMorphism]; exact hstr)
      ((isQuasiCompactMorphism_relativeDiagonal_iff B (⊤_ Scheme.{u}) B.contains_terminal _).1 hΔ)
  have hrepZ : IsRepresentableByAlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal
      fZ.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B (⊤_ Scheme.{u})
      B.contains_terminal (AlgebraicStacks.viewOverIntegers B S hS B.contains_terminal 𝒳).property
      (isRepresentableByAlgebraicSpace_changeBase_scheme B S (⊤_ Scheme.{u}) hS
        B.contains_terminal g U) fZ.hom
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) f.hom
  exact (isQuasiCompact_iff_baseChange_quasiCompact B S hS f hrep).1
    ((isQuasiCompact_changeBaseHom_iff B S (⊤_ Scheme.{u}) hS B.contains_terminal g f.hom).1
      ((isQuasiCompact_iff_baseChange_quasiCompact B (⊤_ Scheme.{u}) B.contains_terminal fZ
        hrepZ).2 hfZ))

/-- Under the identifications of point spaces with underlying schemes, the map on points induced
by the inclusion of an open subscheme is the open immersion. -/
private theorem pointsMap_openSiteObjectHom_eq (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    AlgebraicStacks.pointsMap B S hS
      (schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U O)) =
      (pointsHomeomorphScheme B S hS U).symm ∘
        (BigFppfOver.toScheme B S hS).map (Space.openSiteObjectHom B S hS U O) ∘
        pointsHomeomorphScheme B S hS (Space.openSiteObject B S hS U O) := by
  funext z
  refine (pointsHomeomorphScheme B S hS U).injective ?_
  rw [Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
  exact pointsHomeomorphScheme_naturality B S hS _ z

/-- **The image of the algebraic stack of an open subscheme.** For an open `O` of the scheme
underlying `U`, the points of the algebraic stack of `U` coming from the algebraic stack of `O`
are those whose underlying scheme point lies in `O`. -/
theorem range_pointsMap_openSiteObjectHom (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Set.range (AlgebraicStacks.pointsMap B S hS
        (schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U O))) =
      pointsHomeomorphScheme B S hS U ⁻¹' (O : Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  rw [pointsMap_openSiteObjectHom_eq, Set.range_comp, Set.range_comp,
    (pointsHomeomorphScheme B S hS _).surjective.range_eq, Set.image_univ,
    Space.map_openSiteObjectHom, Homeomorph.image_symm]
  exact congrArg _ (Scheme.Opens.range_ι O)

/-- **A quasi-compact chart has quasi-compact saturations.** Let `f` be a quasi-compact
1-morphism to `𝒳` from the algebraic stack of a scheme `U`. For a quasi-compact open `V` of the
point space of `U`, the set of points of `U` with the same image in `|𝒳|` as a point of `V` is
quasi-compact: it is the image of the point space of the 2-fibre product of `f` with the algebraic
stack of the open subscheme cut out by `V`, which is quasi-compact because `f` is, and Stacks 04XH
describes that image. -/
theorem isCompact_preimage_image_pointsMap (U : BigFppfOver B S hS)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : IsQuasiCompactMorphism.{u, w} B S hS f)
    (V : Set (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)))
    (hVo : IsOpen V) (hVc : IsCompact V) :
    IsCompact (AlgebraicStacks.pointsMap B S hS f ⁻¹'
      (AlgebraicStacks.pointsMap B S hS f '' V)) := by
  let e := pointsHomeomorphScheme B S hS U
  let O : ((BigFppfOver.toScheme B S hS).obj U).Opens := ⟨e '' V, e.isOpenMap V hVo⟩
  let W := Space.openSiteObject B S hS U O
  let ι := schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U O)
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS ι) = V := by
    rw [range_pointsMap_openSiteObjectHom]
    exact e.preimage_image V
  let P := twoFibreProductSquareAlgebraicStacks B S hS (ι ≫ f) f
  have : CompactSpace (AlgebraicStacks.points B S hS P.pt) := hf (schemeStack.{u, w} B S hS W)
    (ι ≫ f) (isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B S hS W
      (isCompact_iff_compactSpace.mp (hVc.image e.continuous)))
  have himage : AlgebraicStacks.pointsMap B S hS P.snd '' Set.univ =
      AlgebraicStacks.pointsMap B S hS f ⁻¹' (AlgebraicStacks.pointsMap B S hS f '' V) := by
    ext u
    constructor
    · rintro ⟨p, -, rfl⟩
      refine ⟨AlgebraicStacks.pointsMap B S hS ι (AlgebraicStacks.pointsMap B S hS P.fst p),
        hrange ▸ Set.mem_range_self _, ?_⟩
      simpa only [AlgebraicStacks.pointsMap_comp, Function.comp_apply] using
        congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS P.iso.hom) p
    · rintro ⟨v, hv, hfv⟩
      rw [← hrange] at hv
      obtain ⟨o, rfl⟩ := hv
      obtain ⟨p, -, hp⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (ι ≫ f) f) o u
        ((congrFun (AlgebraicStacks.pointsMap_comp B S hS ι f) o).trans hfv)
      exact ⟨p, Set.mem_univ _, hp⟩
  rw [← himage]
  exact isCompact_univ.image (continuous_pointsMap B S hS P.pt.val _ P.snd.hom.hom)

/-- The point space of the algebraic stack of an affine scheme is spectral: it is homeomorphic to
the underlying space of the scheme. -/
theorem spectralSpace_points_schemeStack (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    SpectralSpace (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)) := by
  have : SpectralSpace ((BigFppfOver.toScheme B S hS).obj U) := SpectralSpace.mk
  have : CompactSpace (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)) :=
    (pointsHomeomorphScheme B S hS U).symm.compactSpace
  exact (pointsHomeomorphScheme B S hS U).isOpenEmbedding.spectralSpace

/-- **Stacks 0DQN.** Let `𝒳` be a quasi-compact algebraic stack over `S` whose absolute diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_{Spec ℤ} 𝒳` is quasi-compact. Then the topological space of points `|𝒳|` is
spectral.

The absolute diagonal is read as in Stacks 050D: the relative diagonal of the structure
morphism of `𝒳` viewed over the terminal scheme `Spec ℤ`, quasi-compact in the sense of
Stacks 050U. -/
@[stacks 0DQN]
theorem spectralSpace_points_of_isQuasiCompact_diagonal (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hΔ : IsQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) B.contains_terminal
        (structureMorphism B (⊤_ Scheme.{u}) B.contains_terminal
          (AlgebraicStacks.viewOverIntegers B S hS B.contains_terminal 𝒳)))) :
    SpectralSpace (points B S hS 𝒳.val.val 𝒳.val.property) := by
  obtain ⟨U, hU, f, hfsurj, hfsmooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 hqc
  let f' : schemeStack.{u, w} B S hS U ⟶ 𝒳 := f
  have : SpectralSpace (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)) :=
    spectralSpace_points_schemeStack.{u, w} B S hS U hU
  have : T0Space (points B S hS 𝒳.val.val 𝒳.val.property) :=
    t0Space_points_of_isDecent.{u, w} B S hS 𝒳.val 𝒳.property
      (isDecent_of_isQuasiCompact_diagonal B S hS B.contains_terminal 𝒳 hΔ)
  exact spectralSpace_of_isOpenMap_surjective
    (continuous_pointsMap B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f'.hom.hom)
    (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS f'
      (isSmooth_of_isRelativelySmooth B S hS f' hfsmooth))
    hfsurj (isCompact_preimage_image_pointsMap.{u, w} B S hS U f'
      (isQuasiCompactMorphism_of_isQuasiCompact_diagonal.{u, w} B S hS 𝒳 hΔ U inferInstance f'))

/-- **Stacks 0DQP.** The topological space of points `|𝒳|` of a quasi-compact and
quasi-separated algebraic stack `𝒳` over `S` is spectral.

Quasi-separatedness is absolute quasi-separatedness, part (8) of Stacks 050D; its first half is
quasi-compactness of the absolute diagonal (Stacks 04Z0, part (2)), so this is the special case of
Stacks 0DQN. -/
@[stacks 0DQP]
theorem spectralSpace_points_of_isAbsolutelyQuasiSeparated (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hqs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS B.contains_terminal 𝒳) :
    SpectralSpace (points B S hS 𝒳.val.val 𝒳.val.property) :=
  spectralSpace_points_of_isQuasiCompact_diagonal.{u, w} B S hS 𝒳 hqc
    ((isQuasiSeparated_iff_isQuasiCompactMorphism_diagonals B (⊤_ Scheme.{u}) B.contains_terminal
      (structureMorphism B (⊤_ Scheme.{u}) B.contains_terminal
        (AlgebraicStacks.viewOverIntegers B S hS B.contains_terminal 𝒳))).1 hqs).1

/-- The map on points induced by the inclusion of the algebraic stack of an open subscheme is
open: under the identification of the two point spaces with the underlying schemes it is the open
immersion. -/
theorem isOpenMap_pointsMap_openSiteObjectHom (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    IsOpenMap (AlgebraicStacks.pointsMap B S hS
      (schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U O))) := by
  have hι : IsOpenMap ((BigFppfOver.toScheme B S hS).map
      (Space.openSiteObjectHom B S hS U O)) := by
    rw [Space.map_openSiteObjectHom]
    exact O.ι.isOpenEmbedding.isOpenMap
  rw [pointsMap_openSiteObjectHom_eq]
  exact (pointsHomeomorphScheme B S hS U).symm.isOpenMap.comp
    (hι.comp (pointsHomeomorphScheme B S hS _).isOpenMap)

/-- **The image of an open affine chart is spectral.** Let `𝒳` have quasi-compact absolute
diagonal and let `b` be a 1-morphism to `𝒳` from the algebraic stack of an affine scheme which is
open on points. Then the image of `b` on points, an open subset of `|𝒳|`, is a spectral space. -/
theorem spectralSpace_range_pointsMap (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) B.contains_terminal
        (structureMorphism B (⊤_ Scheme.{u}) B.contains_terminal
          (AlgebraicStacks.viewOverIntegers B S hS B.contains_terminal 𝒳))))
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (b : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (hb : IsOpenMap (AlgebraicStacks.pointsMap B S hS b)) :
    SpectralSpace (Set.range (AlgebraicStacks.pointsMap B S hS b)) := by
  let φ := AlgebraicStacks.pointsMap B S hS b
  have : SpectralSpace (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS V)) :=
    spectralSpace_points_schemeStack.{u, w} B S hS V hV
  have : T0Space (AlgebraicStacks.points B S hS 𝒳) :=
    t0Space_points_of_isDecent.{u, w} B S hS 𝒳.val 𝒳.property
      (isDecent_of_isQuasiCompact_diagonal B S hS B.contains_terminal 𝒳 hΔ)
  have hφ : Continuous φ :=
    continuous_pointsMap B S hS (schemeStack.{u, w} B S hS V).val 𝒳.val b.hom.hom
  have key : ∀ s : Set (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS V)),
      Set.rangeFactorization φ '' s = Subtype.val ⁻¹' (φ '' s) := fun s => by
    ext ⟨y, hy⟩
    simp only [Set.mem_image, Set.mem_preimage, Set.rangeFactorization, Subtype.mk.injEq]
  refine spectralSpace_of_isOpenMap_surjective (f := Set.rangeFactorization φ)
    (hφ.codRestrict _) ?_ Set.rangeFactorization_surjective ?_
  · intro s hs
    rw [key]
    exact (hb s hs).preimage continuous_subtype_val
  · intro s hso hsc
    rw [key, Set.preimage_preimage]
    exact isCompact_preimage_image_pointsMap.{u, w} B S hS V b
      (isQuasiCompactMorphism_of_isQuasiCompact_diagonal.{u, w} B S hS 𝒳 hΔ V inferInstance b)
      s hso hsc

/-- The image on points of the algebraic stack of an open subscheme of a chart. -/
private abbrev chartImage {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Set (AlgebraicStacks.points B S hS 𝒳) :=
  Set.range (AlgebraicStacks.pointsMap B S hS
    (schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U O) ≫ a))

/-- **Stacks 0DQQ.** Let `𝒳` be an algebraic stack over `S` whose absolute diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_{Spec ℤ} 𝒳` is quasi-compact. Then `|𝒳|` has an open covering by spectral
subspaces, and in particular `|𝒳|` is sober.

The covering is by the images of the affine opens of a smooth surjective chart by a scheme. The
absolute diagonal is read as in Stacks 050D, as in
`AlgebraicGeometry.Stack.spectralSpace_points_of_isQuasiCompact_diagonal`. -/
@[stacks 0DQQ]
theorem exists_spectralSpace_cover_and_stacksSober (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) B.contains_terminal
        (structureMorphism B (⊤_ Scheme.{u}) B.contains_terminal
          (AlgebraicStacks.viewOverIntegers B S hS B.contains_terminal 𝒳)))) :
    (∃ 𝒰 : Set (Set (points B S hS 𝒳.val.val 𝒳.val.property)),
      (∀ W ∈ 𝒰, IsOpen W ∧ SpectralSpace W) ∧ ⋃₀ 𝒰 = Set.univ) ∧
      StacksSober (points B S hS 𝒳.val.val 𝒳.val.property) := by
  obtain ⟨U, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  have hbo : ∀ O : ((BigFppfOver.toScheme B S hS).obj U).Opens, IsOpenMap
      (AlgebraicStacks.pointsMap B S hS
        (schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U O) ≫ a)) := by
    intro O
    rw [AlgebraicStacks.pointsMap_comp]
    exact (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS a hasm).comp
      (isOpenMap_pointsMap_openSiteObjectHom.{u, w} B S hS U O)
  let 𝒰 : Set (Set (AlgebraicStacks.points B S hS 𝒳)) :=
    {W | ∃ O, IsAffineOpen O ∧ chartImage B S hS a O = W}
  have h𝒰 : ∀ W ∈ 𝒰, IsOpen W ∧ SpectralSpace W := by
    rintro _ ⟨O, hO, rfl⟩
    exact ⟨by simpa only [Set.image_univ] using hbo O Set.univ isOpen_univ,
      spectralSpace_range_pointsMap.{u, w} B S hS 𝒳 hΔ (Space.openSiteObject B S hS U O) hO
        _ (hbo O)⟩
  have hcover : ⋃₀ 𝒰 = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨u, rfl⟩ := hasurj x
    obtain ⟨O, hO, hu, -⟩ := exists_isAffineOpen_mem_and_subset
      (U := ⊤) (Set.mem_univ (pointsHomeomorphScheme B S hS U u))
    obtain ⟨z, rfl⟩ : u ∈ Set.range (AlgebraicStacks.pointsMap B S hS
        (schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U O))) := by
      rwa [range_pointsMap_openSiteObjectHom]
    exact ⟨_, ⟨O, hO, rfl⟩, z, congrFun (AlgebraicStacks.pointsMap_comp B S hS _ a) z⟩
  refine ⟨⟨𝒰, h𝒰, hcover⟩, stacksSober_iff_t0_and_quasiSober.mpr
    ⟨t0Space_points_of_isDecent.{u, w} B S hS 𝒳.val 𝒳.property
      (isDecent_of_isQuasiCompact_diagonal B S hS B.contains_terminal 𝒳 hΔ), ?_⟩⟩
  have : ∀ W : 𝒰, QuasiSober W := fun W => (h𝒰 W.1 W.2).2.toQuasiSober
  exact quasiSober_of_open_cover 𝒰 (fun W => (h𝒰 W.1 W.2).1) hcover

end AlgebraicGeometry.Stack

end

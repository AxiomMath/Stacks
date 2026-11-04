module

public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromFiniteSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatChartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover

/-!
# Finiteness over a dense open subspace: neighbourhoods of points of codimension zero

This file collects the first steps towards **Stacks 0BBC**, proved in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace`.
For a decent algebraic space `Y` with finitely many points of codimension zero it controls the
generic points of dense open subschemes and the fibres over a point of codimension zero; it shows
that étale morphisms and open immersions preserve and reflect local rings of dimension zero; it
produces open neighbourhoods of a point of codimension zero over which a morphism is finite; and
it glues finitely many open subspaces over which a morphism is finite into a dense one.

## Implementation notes

Density of the open subspace is density of the range of its map on points for the canonical
topology of Stacks 03BX, and the restriction of `f` over an open subspace is the second
projection of the fibre product.

Both branches reduce to a single point of codimension zero of the target. The target is decent
with finitely many points of codimension zero, so Stacks 0BB9 produces a dense open subspace of
`Y` which is a scheme with finitely many irreducible components, and Stacks 0ABV identifies the
points of codimension zero with the generic points of that scheme. Around each such point one
finds a quasi-compact quasi-separated open neighbourhood, and the union of finitely many open
subspaces over which `f` is finite is again such an open subspace, dense because it contains
every point of codimension zero.

Over such a neighbourhood the two hypotheses are used differently. If `f` is quasi-compact
then the base change is of finite type and Stacks 0ACZ applies directly, its condition (3)
being `AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber`.
If `f` is separated then Stacks 0AD0 supplies open subspaces `U ⊂ X` and `V ⊂ Y` with
`f^{-1}(y) ⊂ |U|` over which `f` restricts to a finite morphism; finiteness makes `U` closed as
well as open in `f^{-1}(V)` (Stacks 04NX and Stacks 04NZ), and `U` already contains every point
of codimension zero of `f^{-1}(V)`, so Stacks 0BAR forces the complement to be empty.

## References

* [Stacks Project, Tag 0BBC](https://stacks.math.columbia.edu/tag/0BBC)
* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
* [Stacks Project, Tag 0AAY](https://stacks.math.columbia.edu/tag/0AAY)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0ACZ](https://stacks.math.columbia.edu/tag/0ACZ)
* [Stacks Project, Tag 0AD0](https://stacks.math.columbia.edu/tag/0AD0)
* [Stacks Project, Tag 0BAI](https://stacks.math.columbia.edu/tag/0BAI)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 0BAR](https://stacks.math.columbia.edu/tag/0BAR)
* [Stacks Project, Tag 0BB9](https://stacks.math.columbia.edu/tag/0BB9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology
attribute [local instance] CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange

lemma genericPoints_finite_of_zero_finite
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYdecent : IsDecentSpace B S hS Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0}) :
    letI : TopologicalSpace (points B S hS Y) :=
      pointTopology B S hS Y
    (genericPoints (points B S hS Y)).Finite := by
  let : TopologicalSpace (points B S hS Y) :=
    pointTopology B S hS Y
  have hEq : genericPoints (points B S hS Y) =
      {y : points B S hS Y |
        localRingDimension B S hS y = 0} := by
    ext y
    exact mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hYdecent y
  rw [hEq]
  exact hYzero

lemma exists_open_nhds_unique_generic
    {P : Type*} [TopologicalSpace P] [T0Space P] [QuasiSober P]
    (hfinite : (genericPoints P).Finite) (η : genericPoints P) :
    ∃ V : TopologicalSpace.Opens P, (η : P) ∈ V ∧
      ∀ ξ : genericPoints P, (ξ : P) ∈ V → ξ = η := by
  let : Finite (genericPoints P) := hfinite.to_subtype
  let : Finite (irreducibleComponents P) :=
    Finite.of_equiv _ (genericPoints.equiv)
  have hc : (irreducibleComponents P).Finite := Set.toFinite _
  let s : Set P := ⋃₀ (irreducibleComponents P \ {closure ({(η : P)} : Set P)})
  have hs : IsClosed s := by
    dsimp [s]
    rw [Set.sUnion_eq_biUnion]
    exact hc.sdiff.isClosed_biUnion fun Z hZ =>
      isClosed_of_mem_irreducibleComponents Z hZ.1
  let V : TopologicalSpace.Opens P := ⟨sᶜ, hs.isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · show (η : P) ∉ s
    intro h
    obtain ⟨Z, hZ, hηZ⟩ := h
    have hsub : closure ({(η : P)} : Set P) ⊆ Z :=
      closure_minimal (Set.singleton_subset_iff.mpr hηZ)
        (isClosed_of_mem_irreducibleComponents Z hZ.1)
    have heq : Z = closure ({(η : P)} : Set P) :=
      Set.Subset.antisymm (η.2.2 hZ.1.1 hsub) hsub
    exact hZ.2 (by simp [heq])
  · intro ξ hξ
    have hsub : closure ({(ξ : P)} : Set P) ⊆ closure (V : Set P) :=
      closure_mono (Set.singleton_subset_iff.mpr hξ)
    change closure ({(ξ : P)} : Set P) ⊆ closure sᶜ at hsub
    dsimp [s] at hsub
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton hc _ η.2] at hsub
    have heq : closure ({(ξ : P)} : Set P) = closure ({(η : P)} : Set P) :=
      Set.Subset.antisymm hsub (ξ.2.2 η.2.1 hsub)
    exact genericPoints.component_injective (Subtype.ext heq)

private lemma exists_dense_affineOpen_of_finite_genericPoints
    (T : Scheme.{u}) (hfinite : (genericPoints T).Finite) :
    ∃ V : T.affineOpens, Dense (V.1 : Set T) := by
  classical
  let : Finite (genericPoints T) := hfinite.to_subtype
  have hchoose (η : genericPoints T) :
      ∃ V : T.affineOpens, (η : T) ∈ V.1 ∧
        ∀ ξ : genericPoints T, (ξ : T) ∈ V.1 → ξ = η := by
    obtain ⟨O, hηO, huniq⟩ := exists_open_nhds_unique_generic hfinite η
    obtain ⟨V, hV, hηV, hVO⟩ := exists_isAffineOpen_mem_and_subset hηO
    exact ⟨⟨V, hV⟩, hηV, fun ξ hξ => huniq ξ (hVO hξ)⟩
  choose V hV huniq using hchoose
  have hgen : Dense (genericPoints T) := dense_iff_closure_eq.mpr genericPoints.closure
  have hdisj : Pairwise (Function.onFun Disjoint (fun η => (V η).1)) := by
    intro η ξ hne
    apply disjoint_iff_inf_le.mpr
    intro x hx
    obtain ⟨z, hz, hzgen⟩ := hgen.inter_open_nonempty
      ((V η).1 ∩ (V ξ).1) ((V η).1.isOpen.inter (V ξ).1.isOpen) ⟨x, hx⟩
    exact hne ((huniq η ⟨z, hzgen⟩ hz.1).symm.trans
      (huniq ξ ⟨z, hzgen⟩ hz.2))
  refine ⟨⟨⨆ η, (V η).1, IsAffineOpen.iSup_of_disjoint (fun η => (V η).2) hdisj⟩, ?_⟩
  exact hgen.mono fun η hη => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨η, hη⟩, hV ⟨η, hη⟩⟩

/-- The open subspace corresponding to an open set of points has exactly that set of points. -/
private lemma range_pointsMap_openSubspacesOrderIso_symm
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (O : TopologicalSpace.Opens (points B S hS Y)) :
    Set.range (pointsMap B S hS ((openSubspacesOrderIso B S hS Y hY).symm O).1.toFunctor
      ((openSubspacesOrderIso B S hS Y hY).symm O).1.ι) = (O : Set (points B S hS Y)) := by
  have h := openSubspacesOrderIso_apply B S hS Y hY ((openSubspacesOrderIso B S hS Y hY).symm O)
  rw [OrderIso.apply_symm_apply] at h
  exact h.symm

private lemma exists_open_subspace_isolating_zero_point
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYdecent : IsDecentSpace B S hS Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      ∀ z : points B S hS Y,
        localRingDimension B S hS z = 0 →
        z ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) → z = y := by
  let : TopologicalSpace (points B S hS Y) :=
    pointTopology B S hS Y
  have hgen : (genericPoints (points B S hS Y)).Finite :=
    genericPoints_finite_of_zero_finite B S hS hY hYdecent hYzero
  let : T0Space (points B S hS Y) :=
    t0Space_points_of_isDecentSpace B S hS hY hYdecent
  let : QuasiSober (points B S hS Y) := quasiSober_points_of_isDecentSpace B S hS hY hYdecent
  have hygen : y ∈ genericPoints (points B S hS Y) :=
    (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hYdecent y).mpr hy
  obtain ⟨O, hyO, huniq⟩ := exists_open_nhds_unique_generic hgen ⟨y, hygen⟩
  let e := openSubspacesOrderIso B S hS Y hY
  let Vdata := e.symm O
  let V : Subfunctor Y := Vdata.1
  have hV : IsOpenSubspace B S hS V := Vdata.2
  have hImage : Set.range (pointsMap B S hS V.toFunctor V.ι) =
      (O : Set (points B S hS Y)) := range_pointsMap_openSubspacesOrderIso_symm B S hS hY O
  refine ⟨V, hV, ?_, ?_⟩
  · rw [hImage]
    exact hyO
  · intro z hz hzV
    have hzgen : z ∈ genericPoints (points B S hS Y) :=
      (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hYdecent z).mpr hz
    rw [hImage] at hzV
    exact congrArg Subtype.val (huniq ⟨z, hzgen⟩ hzV)

lemma finite_fiber_over_zero_point
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hpreimage : (pointsMap B S hS X f) ⁻¹'
      {y : points B S hS Y |
        localRingDimension B S hS y = 0} =
      {x : points B S hS X |
        localRingDimension B S hS x = 0}) :
    ∀ y : points B S hS Y,
      localRingDimension B S hS y = 0 →
        Set.Finite {x : points B S hS X |
          pointsMap B S hS X f x = y} := by
  intro y hy
  apply hXzero.subset
  intro x hx
  have hmem : x ∈ (pointsMap B S hS X f) ⁻¹'
      {y : points B S hS Y |
        localRingDimension B S hS y = 0} := by
    show localRingDimension B S hS
      (pointsMap B S hS X f x) = 0
    rw [hx]
    exact hy
  rw [hpreimage] at hmem
  exact hmem

namespace FiniteOverDense

/-- The identity of a presheaf induces the identity on points, with the site and the presheaf
left implicit. Shared by the parts of `AlgebraicGeometry.Space.FiniteOverDenseOpenSubspace`. -/
theorem pointsMap_id'
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    pointsMap B S hS F (𝟙 F) = id :=
  pointsMap_id B S hS F

end FiniteOverDense

open FiniteOverDense

theorem isEtale_of_presheaf
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsEtale B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) := by
    refine ⟨?_⟩
    intro A C D g h hg hh
    let : Etale g := hg
    let : Etale h := hh
    exact Etale.etale_comp g h
  let : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage T
  let : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  intro U a ha
  exact MorphismProperty.comp_mem Q.presheaf a f ha hf

theorem isEtale_of_openImmersion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hf : IsOpenImmersion B S hS f) :
    IsEtale B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have hle : MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T ≤ Q := by
    intro A C g hg
    let : AlgebraicGeometry.IsOpenImmersion (T.map g) := hg
    exact (inferInstance : Etale (T.map g))
  have hf' : Q.presheaf f := MorphismProperty.relative_monotone hle f hf
  exact isEtale_of_presheaf B S hS f hf'

theorem localRingDimension_zero_iff_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsEtale B S hS f)
    (x : points B S hS X) :
    localRingDimension B S hS x = 0 ↔
      localRingDimension B S hS (pointsMap B S hS X f x) = 0 := by
  constructor
  · intro hx
    apply (localRingDimension_eq_iff_hasChartLocalRingDimension
      B S hS hY _ 0).2
    obtain ⟨U, a, u, ha, ⟨q, hqu, hqx⟩, hdim⟩ :=
      (localRingDimension_eq_iff_hasChartLocalRingDimension
        B S hS hX x 0).1 hx
    refine ⟨U, a ≫ f, u, hf U a ha, ⟨q, hqu, ?_⟩, hdim⟩
    simp only [pointsMap_comp, Function.comp_apply, hqx]
  · intro hx
    apply (localRingDimension_eq_zero_iff_all_etale_genericPoints
      B S hS hX x).2
    intro U a z ha hz
    apply (localRingDimension_eq_zero_iff_all_etale_genericPoints
      B S hS hY _).1 hx U (a ≫ f) z
    · intro V b hb
      simpa only [Category.assoc] using hf V (b ≫ a) (ha V b hb)
    · obtain ⟨q, hqz, hqx⟩ := hz
      refine ⟨q, hqz, ?_⟩
      simp only [pointsMap_comp, Function.comp_apply, hqx]

theorem localRingDimension_zero_iff_of_openImmersion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsOpenImmersion B S hS f)
    (x : points B S hS X) :
    localRingDimension B S hS x = 0 ↔
      localRingDimension B S hS (pointsMap B S hS X f x) = 0 :=
  localRingDimension_zero_iff_of_isEtale B S hS hX hY f
    (isEtale_of_openImmersion B S hS f hf) x

lemma localRingDimension_zero_map_of_openSubspace
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G)
    (j : F ⟶ G) (hj : IsOpenImmersion B S hS j)
    (x : points B S hS F)
    (hx : localRingDimension B S hS x = 0) :
    localRingDimension B S hS
      (pointsMap B S hS F j x) = 0 :=
  (localRingDimension_zero_iff_of_openImmersion B S hS hF hG j hj x).1 hx

private lemma exists_finite_open_restriction_at_zero_point
     (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hpreimage : (pointsMap B S hS X f) ⁻¹'
      {y : points B S hS Y |
        localRingDimension B S hS y = 0} =
      {x : points B S hS X |
        localRingDimension B S hS x = 0})
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ (U : Subfunctor X) (V : Subfunctor Y)
      (g : U.toFunctor ⟶ V.toFunctor),
      IsOpenSubspace B S hS U ∧
      IsOpenSubspace B S hS V ∧
      g ≫ V.ι = U.ι ≫ f ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      {x : points B S hS X |
        pointsMap B S hS X f x = y} ⊆
        Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
      IsFinite B S hS g :=
  exists_isOpenSubspace_isFinite_openRestriction_of_finite_setFibre
    B S hS hX hY f hqs hlft hYqs y hy (finite_fiber_over_zero_point B S hS f hXzero hpreimage y hy)

private lemma exists_finite_open_restriction_at_zero_point_of_isSeparated
     (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hsep : IsSeparated B S hS f)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hpreimage : (pointsMap B S hS X f) ⁻¹'
      {y : points B S hS Y |
        localRingDimension B S hS y = 0} =
      {x : points B S hS X |
        localRingDimension B S hS x = 0})
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ (U : Subfunctor X) (V : Subfunctor Y)
      (g : U.toFunctor ⟶ V.toFunctor),
      IsOpenSubspace B S hS U ∧
      IsOpenSubspace B S hS V ∧
      g ≫ V.ι = U.ι ≫ f ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      {x : points B S hS X |
        pointsMap B S hS X f x = y} ⊆
        Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
      IsFinite B S hS g :=
  exists_finite_open_restriction_at_zero_point B S hS hZ hX hY f hlft
    (isQuasiSeparated_of_isSeparated B S hS hsep) hYqs hXzero
    hpreimage y hy

private lemma exists_finite_open_over_zero_point_of_finiteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f)
    (hft : IsFiniteType B S hS f)
    (hYdecent : IsDecentSpace B S hS Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hpreimage : (pointsMap B S hS X f) ⁻¹'
      {y : points B S hS Y |
        localRingDimension B S hS y = 0} =
      {x : points B S hS X |
        localRingDimension B S hS x = 0})
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  have hset : Set.Finite {x : points B S hS X |
      pointsMap B S hS X f x = y} :=
    finite_fiber_over_zero_point B S hS f hXzero hpreimage y hy
  obtain ⟨p, hp, _hmono, _hqc⟩ := hYdecent y
  have hfield : Set.Finite (Set.univ : Set (points B S hS
      (pullback f (yonedaEquiv.symm p.value)))) :=
    (finite_fieldFiber_iff_finite_setFiber_of_decent
      B S hS hX hY f hqs hft hYdecent y p hp).mpr hset
  exact (exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber
    B S hS hX hY f hqs hft y p hp hy) hfield

lemma exists_dense_open_scheme_of_decent_of_zero_finite
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYdecent : IsDecentSpace B S hS Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0}) :
    HasQuasiCompactGenericDenseOpenScheme B S hS Y ∧
      (irreducibleComponents (points B S hS Y)).Finite := by
  let : TopologicalSpace (points B S hS Y) :=
    pointTopology B S hS Y
  have hgen : (genericPoints (points B S hS Y)).Finite :=
    genericPoints_finite_of_zero_finite B S hS hY hYdecent hYzero
  let : T0Space (points B S hS Y) :=
    t0Space_points_of_isDecentSpace B S hS hY hYdecent
  let : QuasiSober (points B S hS Y) := quasiSober_points_of_isDecentSpace B S hS hY hYdecent
  let : Finite (genericPoints (points B S hS Y)) := hgen.to_subtype
  let : Finite (irreducibleComponents (points B S hS Y)) :=
    Finite.of_equiv _ (genericPoints.equiv)
  have hcomp : (irreducibleComponents (points B S hS Y)).Finite :=
    Set.toFinite _
  refine ⟨((isDecentWithFinitelyManyComponents_tfae B S hS hY).out 1 3).mp
    (⟨hYdecent, hcomp⟩ : IsDecentWithFinitelyManyComponents B S hS Y), hcomp⟩

private lemma isFinite_of_zariskiCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (I : Type u) (U : I → Subfunctor Y)
    (hcover : IsZariskiCover B S hS I U)
    (hfinite : ∀ i, IsFinite B S hS
      (pullback.snd f (U i).ι)) :
    IsFinite B S hS f :=
  (isFinite_iff_zariskiCover B S hS (f := f) hX hY).2
    ⟨I, U, hcover, hfinite⟩

lemma isFinite_of_arrowIso
    {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (hcomm : eX.hom ≫ g = f ≫ eY.hom)
    (hf : IsFinite B S hS f) :
    IsFinite B S hS g := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hfinite, hpull⟩ := hf U hU (ξ ≫ eY.inv)
  refine ⟨V, p, i ≫ eX.hom, hV, hfinite, ?_⟩
  apply hpull.of_iso (Iso.refl _) eX (Iso.refl (yoneda.obj U)) eY
  · simp
  · simp
  · exact hcomm.symm
  · simp [Category.assoc]

noncomputable def openPreimageFactorIso
    {C : Type v} [Category.{w} C]
    {X Y V : Cᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (i : V ⟶ Y) [Mono i] (U : Subfunctor X)
    (g : U.toFunctor ⟶ V) (h : g ≫ i = U.ι ≫ f) :
    (U.preimage (pullback.fst f i)).toFunctor ≅ U.toFunctor := by
  let P := pullback f i
  let k : U.toFunctor ⟶ P := pullback.lift U.ι g h.symm
  have hfst : k ≫ pullback.fst f i = U.ι := by
    dsimp [k]
    exact pullback.lift_fst U.ι g h.symm
  have hsnd : k ≫ pullback.snd f i = g := by
    dsimp [k]
    exact pullback.lift_snd U.ι g h.symm
  have hk : Subfunctor.range k ≤ U.preimage (pullback.fst f i) := by
    intro T x hx
    obtain ⟨y, rfl⟩ := hx
    change (pullback.fst f i).app T (k.app T y) ∈ U.obj T
    have heq : (pullback.fst f i).app T (k.app T y) = y.1 := by
      have h := congrFun (congrArg (fun q => q.app T) hfst) y
      change (pullback.fst f i).app T (k.app T y) = y.1 at h
      exact h
    rw [heq]
    exact y.2
  let k' : U.toFunctor ⟶ (U.preimage (pullback.fst f i)).toFunctor :=
    Subfunctor.lift k hk
  refine ⟨U.fromPreimage (pullback.fst f i), k', ?_, ?_⟩
  · apply (cancel_mono (U.preimage (pullback.fst f i)).ι).mp
    apply pullback.hom_ext
    · calc
        U.fromPreimage (pullback.fst f i) ≫ k' ≫
              (U.preimage (pullback.fst f i)).ι ≫ pullback.fst f i =
            U.fromPreimage (pullback.fst f i) ≫ k ≫ pullback.fst f i :=
              congrArg (fun t => U.fromPreimage (pullback.fst f i) ≫
                t ≫ pullback.fst f i) (Subfunctor.lift_ι k hk)
        _ = (U.preimage (pullback.fst f i)).ι ≫ pullback.fst f i := by
              simpa only [hfst] using Subfunctor.fromPreimage_ι U (pullback.fst f i)
    · apply (cancel_mono i).mp
      calc
        U.fromPreimage (pullback.fst f i) ≫ k' ≫
              (U.preimage (pullback.fst f i)).ι ≫ pullback.snd f i ≫ i =
            U.fromPreimage (pullback.fst f i) ≫ k ≫ pullback.snd f i ≫ i :=
              congrArg (fun t => U.fromPreimage (pullback.fst f i) ≫
                t ≫ pullback.snd f i ≫ i) (Subfunctor.lift_ι k hk)
        _ = U.fromPreimage (pullback.fst f i) ≫ g ≫ i :=
              congrArg (fun t => U.fromPreimage (pullback.fst f i) ≫ t ≫ i) hsnd
        _ = U.fromPreimage (pullback.fst f i) ≫ U.ι ≫ f :=
              congrArg (fun t => U.fromPreimage (pullback.fst f i) ≫ t) h
        _ = (U.preimage (pullback.fst f i)).ι ≫ pullback.fst f i ≫ f := by
              simpa only [Category.assoc] using
                congrArg (fun t => t ≫ f) (Subfunctor.fromPreimage_ι U (pullback.fst f i))
        _ = (U.preimage (pullback.fst f i)).ι ≫ pullback.snd f i ≫ i :=
              (congrArg (fun t => (U.preimage (pullback.fst f i)).ι ≫ t)
                pullback.condition)
  · apply (cancel_mono U.ι).mp
    calc
      k' ≫ U.fromPreimage (pullback.fst f i) ≫ U.ι =
          k' ≫ (U.preimage (pullback.fst f i)).ι ≫ pullback.fst f i :=
            congrArg (fun t => k' ≫ t)
              (Subfunctor.fromPreimage_ι U (pullback.fst f i))
      _ = U.ι := by
            rw [← Category.assoc, Subfunctor.lift_ι, hfst]

private lemma isFinite_over_open_restriction
    {X Y V W U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (_hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W)
    (hU : IsAlgebraicSpace B S hS U)
    (f : X ⟶ Y) (v : V ⟶ Y) (w : W ⟶ V) (u : U ⟶ Y)
    (e : W ≅ U) (he : e.hom ≫ u = w ≫ v)
    (hfinite : IsFinite B S hS
      (pullback.snd f u)) :
    IsFinite B S hS
      (pullback.snd (pullback.snd f v) w) := by
  let P : AlgebraicGeometry.AlgebraicSpaces B S hS :=
    ⟨pullback f u, isAlgebraicSpace_pullback B S hS f u hX hU hY⟩
  let U' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨U, hU⟩
  let W' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨W, hW⟩
  let f' : P ⟶ U' := ⟨pullback.snd f u⟩
  let e' : W' ⟶ U' := ⟨e.hom⟩
  have hbase : IsFinite B S hS
      (pullback.snd (pullback.snd f u) e.hom) :=
    isFinite_of_isPullback B S hS
      (IsPullback.of_hasPullback (pullback.snd f u) e.hom) hfinite
  let k₁ := pullbackLeftPullbackSndIso f u e.hom
  have hdirect : IsFinite B S hS
      (pullback.snd f (e.hom ≫ u)) := by
    apply isFinite_of_arrowIso B S hS
      (pullback.snd (pullback.snd f u) e.hom)
      (pullback.snd f (e.hom ≫ u)) k₁ (Iso.refl W) ?_ hbase
    simp [k₁]
  have hdirect' : IsFinite B S hS
      (pullback.snd f (w ≫ v)) := by
    apply isFinite_of_arrowIso B S hS
      (pullback.snd f (e.hom ≫ u))
      (pullback.snd f (w ≫ v)) (pullback.congrHom rfl he) (Iso.refl W) ?_ hdirect
    dsimp [pullback.congrHom]
    rw [pullback.map, pullback.lift_snd]
  let k₂ := pullbackLeftPullbackSndIso f v w
  apply isFinite_of_arrowIso B S hS
    (pullback.snd f (w ≫ v))
    (pullback.snd (pullback.snd f v) w) k₂.symm (Iso.refl W) ?_ hdirect'
  simp [k₂]

private theorem preimageIso_hom_ι
    {C : Type v} [Category.{w} C] {F : Cᵒᵖ ⥤ Type u}
    {U V : Subfunctor F} (h : U ≤ V) :
    (preimageIso_of_le h).hom ≫ U.ι = (U.preimage V.ι).ι ≫ V.ι := by
  show U.fromPreimage V.ι ≫ U.ι = (U.preimage V.ι).ι ≫ V.ι
  exact Subfunctor.fromPreimage_ι U V.ι

lemma exists_dense_open_isFinite_of_finite_open_neighborhoods
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (hnear : ∀ y : points B S hS Y,
      localRingDimension B S hS y = 0 →
        ∃ U : Subfunctor Y,
          IsOpenSubspace B S hS U ∧
          y ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
          IsFinite B S hS (pullback.snd f U.ι)) :
    letI : TopologicalSpace (points B S hS Y) :=
      pointTopology B S hS Y
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
      Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  classical
  let : TopologicalSpace (points B S hS Y) :=
    pointTopology B S hS Y
  let I := {y : points B S hS Y |
    localRingDimension B S hS y = 0}
  let : Fintype I := hYzero.fintype
  let n := Fintype.card I
  let en : I ≃ Fin n := Fintype.equivFin I
  let e := openSubspacesOrderIso B S hS Y hY
  let U (i : Fin n) : Subfunctor Y :=
    (hnear (en.symm i).1 (en.symm i).2).choose
  have hU (i : Fin n) : IsOpenSubspace B S hS (U i) :=
    (hnear (en.symm i).1 (en.symm i).2).choose_spec.1
  have hUpt (i : Fin n) : (en.symm i).1 ∈
      Set.range (pointsMap B S hS (U i).toFunctor (U i).ι) :=
    (hnear (en.symm i).1 (en.symm i).2).choose_spec.2.1
  have hUfin (i : Fin n) : IsFinite B S hS
      (pullback.snd f (U i).ι) :=
    (hnear (en.symm i).1 (en.symm i).2).choose_spec.2.2
  let Udata (i : Fin n) : {W : Subfunctor Y // IsOpenSubspace B S hS W} :=
    ⟨U i, hU i⟩
  let O : TopologicalSpace.Opens (points B S hS Y) := ⨆ i, e (Udata i)
  let Vdata := e.symm O
  let V : Subfunctor Y := Vdata.1
  have hV : IsOpenSubspace B S hS V := Vdata.2
  have hEv : e Vdata = O := e.apply_symm_apply O
  have hVimage : Set.range (pointsMap B S hS V.toFunctor V.ι) =
      (O : Set (points B S hS Y)) := range_pointsMap_openSubspacesOrderIso_symm B S hS hY O
  have hzero : {y : points B S hS Y |
      localRingDimension B S hS y = 0} ⊆
        (O : Set (points B S hS Y)) := by
    intro y hy
    let i : Fin n := en ⟨y, hy⟩
    have hyi : y ∈ (e (Udata i) : Set (points B S hS Y)) := by
      show y ∈ (e (Udata i)).1
      rw [openSubspacesOrderIso_apply
        B S hS Y hY (Udata i)]
      simpa [i] using hUpt i
    exact (le_iSup (fun i : Fin n => e (Udata i)) i) hyi
  have hdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
    rw [hVimage]
    exact (codimensionZeroPoints_dense B S hS hY).mono hzero
  let T (i : Fin n) : Subfunctor V.toFunctor := (U i).preimage V.ι
  have hTV (i : Fin n) : U i ≤ V := by
    show (Udata i).1 ≤ Vdata.1
    apply (e.le_iff_le).mp
    rw [hEv]
    exact le_iSup (fun i : Fin n => e (Udata i)) i
  have hT (i : Fin n) : IsOpenSubspace B S hS (T i) :=
    isOpenSubspace_preimage_of_le B S hS (hTV i) (hU i)
  let eT (i : Fin n) : (T i).toFunctor ≅ (U i).toFunctor :=
    preimageIso_of_le (hTV i)
  have hcoverPoints :
      (⋃ i, Set.range (pointsMap B S hS (T i).toFunctor (T i).ι)) =
        Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      let y := pointsMap B S hS V.toFunctor V.ι z
      have hyO : y ∈ (O : Set (points B S hS Y)) := by
        rw [← hVimage]
        exact ⟨z, rfl⟩
      obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hyO
      have hyU : y ∈ Set.range
          (pointsMap B S hS (U i).toFunctor (U i).ι) := by
        rw [← openSubspacesOrderIso_apply
          B S hS Y hY (Udata i)]
        exact hyi
      obtain ⟨x, hx⟩ := hyU
      let x' := pointsMap B S hS (U i).toFunctor (eT i).inv x
      have hcomp : pointsMap B S hS V.toFunctor V.ι
          (pointsMap B S hS (T i).toFunctor (T i).ι x') = y := by
        calc
          _ = pointsMap B S hS (T i).toFunctor
              ((T i).ι ≫ V.ι) x' :=
                (congrFun (pointsMap_comp B S hS _ (T i).ι V.ι) x').symm
          _ = pointsMap B S hS (T i).toFunctor
              ((eT i).hom ≫ (U i).ι) x' := by rw [preimageIso_hom_ι (hTV i)]
          _ = pointsMap B S hS (U i).toFunctor (U i).ι x := by
                rw [congrFun (pointsMap_comp B S hS _ (eT i).hom (U i).ι) x']
                dsimp [x']
                have hpm : pointsMap B S hS (T i).toFunctor
                    (eT i).hom
                    (pointsMap B S hS (U i).toFunctor (eT i).inv x) =
                    pointsMap B S hS (U i).toFunctor
                      ((eT i).inv ≫ (eT i).hom) x := by
                  simpa only [Function.comp_apply] using
                    (congrFun (pointsMap_comp B S hS _ (eT i).inv (eT i).hom) x).symm
                rw [hpm, (eT i).inv_hom_id]
                simp
          _ = y := hx
      have hinj := pointsMap_injective_of_mono B S hS V.ι
      have hz : pointsMap B S hS (T i).toFunctor (T i).ι x' = z := by
        apply hinj
        simpa [y] using hcomp
      exact Set.mem_iUnion.mpr ⟨i, ⟨x', hz⟩⟩
  let J := ULift.{u} (Fin n)
  let T' (j : J) : Subfunctor V.toFunctor := T j.down
  have hT' (j : J) : IsOpenSubspace B S hS (T' j) := hT j.down
  have hcoverPoints' :
      (⋃ j : J, Set.range
        (pointsMap B S hS (T' j).toFunctor (T' j).ι)) = Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      have hz : z ∈ ⋃ i : Fin n, Set.range
          (pointsMap B S hS (T i).toFunctor (T i).ι) := by
        rw [hcoverPoints]
        simp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨ULift.up i, by simpa [T'] using hi⟩
  have hcover : IsZariskiCover B S hS J T' :=
    (isZariskiCover_iff_iUnion_points B S hS V.toFunctor hV.1 J T' hT').2 hcoverPoints'
  have hXv : IsAlgebraicSpace B S hS (pullback f V.ι) :=
    isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY
  have hfinite : ∀ j : J, IsFinite B S hS
      (pullback.snd (pullback.snd f V.ι) (T' j).ι) := by
    intro j
    let i := j.down
    exact isFinite_over_open_restriction B S hS hX hY hV.1 (hT i).1
      (hU i).1 f V.ι (T i).ι (U i).ι (eT i)
      (preimageIso_hom_ι (hTV i)) (hUfin i)
  refine ⟨V, hV, hdense, ?_⟩
  exact isFinite_of_zariskiCover B S hS hXv hV.1 (pullback.snd f V.ι)
    J T' hcover hfinite

end AlgebraicGeometry.Space

end

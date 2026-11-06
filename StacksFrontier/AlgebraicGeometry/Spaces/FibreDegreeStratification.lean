module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Integral
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FieldFibreDegreeBound
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# Stratifying an algebraic space by the degree of a fibre

Let `W` be a scheme and `X` an algebraic space over a scheme `S`, and let `W ⟶ X` be flat,
locally of finite presentation, separated and locally quasi-finite. Stacks 086T produces a
descending chain of open subspaces
`X = X₀ ⊇ X₁ ⊇ X₂ ⊇ …`
through which a field-valued point `Spec k ⟶ X` factors exactly when the fibre
`W ×_X Spec k` has degree at least the index over `k`. This file proves it.

## Main definitions

* `AlgebraicGeometry.Space.DegreeGe`: a morphism has degree at least `d` when it is not finite
  or is finite locally free of some degree at least `d`.

## Main results

* `AlgebraicGeometry.Space.exists_antitone_isOpenSubspace_iff_fibre_degree_ge`: the descending
  chain of open subspaces `Xᵈ` through which a field-valued point factors exactly when the fibre
  above it has degree at least `d`, and
  `AlgebraicGeometry.Space.exists_antitone_openSubspaces_iff_fibreDegree_ge` is the same
  statement with three further results carried as named hypotheses.
* `AlgebraicGeometry.Space.exists_comp_ι_openSubspaceOfPoints_iff`: a field-valued point factors
  through the subspace cut out by a set of points exactly when its class lies in that set.
* `AlgebraicGeometry.Space.exists_antitone_opens_of_etale_chart`: the chain of opens of an étale
  chart detecting the degree of a fibre, and
  `AlgebraicGeometry.Space.degreeGe_iff_mem_of_etale_chart` reads its chain at the fibre over a
  point of `X`: a field-valued point of the chart lies in the `d`-th open exactly when the fibre
  above the point of `X` it carries has degree at least `d`.
* `AlgebraicGeometry.Space.degreeGe_iff_of_class_eq`: the degree condition at a field-valued
  point depends only on the point of the point space it represents, and
  `AlgebraicGeometry.Space.degreeGe_iff_presheaf` compares it with the relatively representable
  form in which Stacks 086T states it.
* `AlgebraicGeometry.Space.isOpenImmersion_of_comp_mono`: a morphism of presheaves which
  composes with a monomorphism to a relative open immersion is itself one.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_isOpenSubspace`: a
  representable open subspace of an open subspace of `X` is, with the same points, a
  representable open subspace of `X`.
* `AlgebraicGeometry.Space.exists_fieldValuedPoint_degreeGe_iff`: a morphism to `X` from a site
  object whose underlying scheme is merely *isomorphic* to a field spectrum carries a
  field-valued point of `X` with the same fibre degrees. This reconciles the shape in which
  Stacks 03JL speaks of a field-valued point with the shape of Stacks 03BU.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace`: a morphism from a
  represented presheaf to an algebraic space is representable, which is what makes the fibre
  `W ×_X Spec k` a scheme and gives its degree a meaning.
* `AlgebraicGeometry.Space.presheaf_pullback_fst_iff_property_snd`: a property of scheme
  morphisms stable under base change holds on the represented fibre of `W ⟶ X` over a chart
  exactly when it holds, in the relatively representable sense, for the projection of the
  fibre product of presheaves.
* `AlgebraicGeometry.Space.baseChange_properties_of_etale_chart`: the scheme morphism
  representing the base change of a flat, locally finitely presented, separated and locally
  quasi-finite morphism of algebraic spaces along an étale chart has all four properties at the
  level of schemes.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_snd_fieldMorphism`: the fibre of an
  étale chart with quasi-compact source above a quasi-compact field-valued point is finite
  locally free of some degree.
* `AlgebraicGeometry.Space.isFlat_of_presheafEtale`,
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_presheafEtale`,
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_presheafEtale` and
  `AlgebraicGeometry.Space.isSeparated_of_scheme_isSeparated`: the four hypotheses above, for
  an étale chart whose underlying scheme is separated.
* `AlgebraicGeometry.Space.opensObject` and `AlgebraicGeometry.Space.opensObjectι`: a Zariski
  open of an object of the site, as an object of the site.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_etaleImage`: the open subspace swept out by an
  étale chart, together with the induced surjective étale chart of it. This is Stacks 06NF.
* `AlgebraicGeometry.Space.exists_rank_lt_of_degree_ge_zero_of_not_degree_ge`: a fibre whose
  degree is at least `0` and not at least `n` is finite locally free of a rank below `n`.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_rank_lt`: if above every field-valued
  point of an open subspace `X'` of `X` the fibre of a chart `φ` of `X` has degree below `n`,
  then a chart of `X'` by a Zariski open of the chart of `X` has universally bounded fibres in
  the sense of Stacks 03JL.
* `AlgebraicGeometry.exists_rank_le_of_isOpenImmersion_over_field`: an open subscheme of a
  scheme finite locally free over a field is finite locally free of a degree at most that of
  the ambient scheme.
* `AlgebraicGeometry.exists_isAffineOpen_disjoint_or_exists_antitone_isAffineOpen`: either a
  nonempty affine open of a scheme misses some member of a descending family of opens, or there
  is a descending chain of nonempty affine opens inside the family.
* `AlgebraicGeometry.Space.exists_not_fibre_degree_ge_of_isDecentSpace`: on a *decent*
  algebraic space the chain is exhausted at every point — the fibre of an étale chart with
  quasi-compact source above a field-valued point fails to have degree at least `d` for some
  `d`.

## Implementation notes

"Degree at least `d`" is spelled, as in Stacks 086R, as the disjunction of non-finiteness of
the fibre with the existence of a degree `r ≥ d`: a degree is a rank of a finite locally free
morphism, so a fibre which is not finite has no degree, and the source's convention that such
a fibre counts as having infinite degree has to be written out. The statement puts that
disjunction on the *presheaf* fibre product `W ×_X Spec k`, with the two properties in their
relatively representable form, so that it mentions no choice of representing object; that the
two agree with the properties of the representing scheme morphism is
`AlgebraicGeometry.Space.presheaf_pullback_fst_iff_property_snd`.

Decency is `AlgebraicGeometry.Space.IsDecentSpace`, condition (4) of Stacks 03JV.

## References

* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 086R](https://stacks.math.columbia.edu/tag/086R)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-! ### A degree fact at the level of schemes -/

/-- An open subscheme of a scheme finite locally free over a field is itself finite locally free,
of a degree at most that of the ambient scheme. -/
theorem exists_rank_le_of_isOpenImmersion_over_field {k : Type u} [Field k]
    {A C : Scheme.{u}} (i : C ⟶ A) [IsOpenImmersion i] (p : A ⟶ Spec (.of k)) (r : ℕ)
    (hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r) :
    ∃ s : ℕ, s ≤ r ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank (i ≫ p) s := by
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r := hr
  obtain ⟨hfin, hflat, hlfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).1
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p r)
  let : IsFinite p := hfin
  let : Flat p := hflat
  let : LocallyOfFinitePresentation p := hlfp
  let : IsArtinianScheme A :=
    { toIsLocallyArtinian := IsLocallyArtinian.of_locallyQuasiFinite p
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p }
  have hdisc : DiscreteTopology A :=
    (IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mp inferInstance).2
  let : IsClosedImmersion i := .of_isPreimmersion i (isClosed_discrete (Set.range i.base))
  let : IsFinite (i ≫ p) := inferInstance
  let : Flat (i ≫ p) := inferInstance
  let : LocallyOfFinitePresentation (i ≫ p) := inferInstance
  let : LocallyQuasiFinite (i ≫ p) := inferInstance
  let : LocallyOfFiniteType (i ≫ p) := inferInstance
  have hcs : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (i ≫ p)
  obtain ⟨s, hs, -⟩ := existsUnique_rank_of_bounded_fiber (i ≫ p)
    (hasUniversallyBoundedFibers_of_locallyQuasiFinite (i ≫ p)) (default : Spec (.of k))
  have hsrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (i ≫ p) s :=
    rank_of_constant_fiber_rank (i ≫ p) s fun t => by
      rwa [Subsingleton.elim t (default : Spec (.of k))]
  exact ⟨s, finite_open_rank_le_of_field i p r s hr hsrank, hsrank⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_FibreDegreeStratification :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_FibreDegreeStratification
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_FibreDegreeStratification B S hS).has_limit _

/-! ### Representability of a morphism from a scheme -/

/-- A morphism from a represented presheaf to an algebraic space over `S` is representable. -/
theorem relativelyRepresentable_of_isAlgebraicSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} (f : yoneda.obj W ⟶ X) :
    yoneda.relativelyRepresentable f :=
  (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).1
    hX.diagonal_representable f

/-! ### The four hypotheses of Stacks 086T, for an étale chart -/

/-- An étale morphism of presheaves, in the relatively representable sense, has every property
of scheme morphisms which the étale morphisms have. -/
theorem presheaf_of_presheafEtale {P : MorphismProperty Scheme.{u}}
    (hP : (@Etale.{u} : MorphismProperty Scheme.{u}) ≤ P)
    {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {φ : G ⟶ H}
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf φ :=
  MorphismProperty.relative_monotone (F := yoneda)
    (fun _ _ _ hk => hP _ _ _ hk) _ hφ

/-- An étale morphism of algebraic spaces over `S`, in the relatively representable sense, is
flat. -/
theorem isFlat_of_presheafEtale {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {φ : G ⟶ H}
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    IsFlat B S hS φ :=
  presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS (@Flat.{u})
    (fun i p hi hp => by
      have : Etale i := hi
      have : Flat p := hp
      infer_instance) φ
    (presheaf_of_presheafEtale B S hS (fun _ _ k hk => by
      have : Etale k := hk
      infer_instance) hφ)

/-- An étale morphism of algebraic spaces over `S`, in the relatively representable sense, is
locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_of_presheafEtale
    {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {φ : G ⟶ H}
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    IsLocallyOfFinitePresentation B S hS φ :=
  presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS
    (@LocallyOfFinitePresentation.{u})
    (fun i p hi hp => by
      have : Etale i := hi
      have : LocallyOfFinitePresentation p := hp
      infer_instance) φ
    (presheaf_of_presheafEtale B S hS (fun _ _ k hk => by
      have : Etale k := hk
      infer_instance) hφ)

/-- An étale morphism of algebraic spaces over `S`, in the relatively representable sense, is
locally quasi-finite. -/
theorem isLocallyQuasiFinite_of_presheafEtale
    {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {φ : G ⟶ H}
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    IsLocallyQuasiFinite B S hS φ :=
  presheafImpliesHoldsOnEveryEtaleChart_locallyQuasiFinite B S hS φ
    (presheaf_of_presheafEtale B S hS (fun _ _ k hk => by
      have : Etale k := hk
      exact ⟨inferInstance, (locallyQuasiFinite_of_etale k).2⟩) hφ)

/-- A morphism from a represented presheaf whose underlying scheme is separated is a separated
morphism of algebraic spaces over `S`. -/
theorem isSeparated_of_scheme_isSeparated {U : BigFppfOver B S hS}
    (hU : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : yoneda.obj U ⟶ X) :
    IsSeparated B S hS φ :=
  isSeparated_of_isSeparatedOver B S hS (isSeparatedOver_yoneda_obj B S hS U hU) φ

/-! ### Zariski opens of an object of the site -/

/-- A Zariski open of an object of the big fppf category over `S`, as an object of that
category. -/
def opensObject (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Over.mk (Y := ⟨V.toScheme, lt_of_le_of_lt (Scheme.size_coe_opens_le _ V) U.left.property⟩)
    (ObjectProperty.homMk V.ι ≫ U.hom)

/-- The inclusion of a Zariski open of an object of the site into that object. -/
def opensObjectι (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : opensObject B S hS U V ⟶ U :=
  Over.homMk (ObjectProperty.homMk V.ι) rfl

/-- The scheme underlying `AlgebraicGeometry.Space.opensObject` is the open subscheme. -/
@[simp]
theorem toScheme_obj_opensObject (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).obj (opensObject B S hS U V) = V.toScheme := rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.opensObjectι` is the inclusion
of the open subscheme. -/
@[simp]
theorem toScheme_map_opensObjectι (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map (opensObjectι B S hS U V) = V.ι := rfl

/-! ### The open subspace swept out by an étale chart -/

/-- For an étale chart `φ : yoneda.obj U ⟶ X` of an algebraic space over `S`, the subfunctor of
`X` cut out by the image of the points of `φ` is an open subspace, `φ` factors through it, and
the induced morphism is a *surjective* étale chart of it. -/
theorem exists_isOpenSubspace_etaleImage {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    ∃ (X' : Subfunctor X) (ψ : yoneda.obj U ⟶ X'.toFunctor),
      IsOpenSubspace B S hS X' ∧ ψ ≫ X'.ι = φ ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ψ ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ψ ∧
      Set.range (pointsMap B S hS X'.toFunctor X'.ι) =
        Set.range (pointsMap B S hS (yoneda.obj U) φ) := by
  have hopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj U) φ)) := by
    have := isOpenMap_pointsMap_of_etale B S hS hX U φ hφ Set.univ isOpen_univ
    rwa [Set.image_univ] at this
  set X' := openSubspaceOfPoints B S hS X (Set.range (pointsMap B S hS (yoneda.obj U) φ))
    with hX'def
  have hX'open : IsOpenSubspace B S hS X' :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _ hopen
  have hX'image : Set.range (pointsMap B S hS X'.toFunctor X'.ι) =
      Set.range (pointsMap B S hS (yoneda.obj U) φ) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  refine ⟨X', factorThroughEtaleImage B S hS hX U φ X' hX'open hX'image, hX'open,
    factorThroughEtaleImage_comp B S hS hX U φ X' hX'open hX'image, ?_, ?_, hX'image⟩
  · exact surjective_factor_through_etaleImage B S hS U φ X' hX'open hX'image _
      (factorThroughEtaleImage_comp B S hS hX U φ X' hX'open hX'image)
  · exact etale_factor_through_etaleImage B S hS U φ hφ X' hX'open _
      (factorThroughEtaleImage_comp B S hS hX U φ X' hX'open hX'image)

/-! ### The universal bound on the fibres of a degree-bounded open of a chart -/

/-- Let `φ : yoneda.obj U ⟶ X` be a morphism from an object of the site to an algebraic space
over `S`, let `V` be a Zariski open of `U`, and let `ψ` be a chart of a subspace `X'` of `X`
through which the restriction of `φ` to `V` factors. If above every field-valued point of `X'`
the fibre of `φ` is finite locally free of a degree below `n`, then the fibres of `ψ` are
universally bounded in the sense of Stacks 03JL, with bound `n`. -/
theorem hasUniversallyBoundedFibers_of_rank_lt
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    {X' : Subfunctor X} (ψ : yoneda.obj (opensObject B S hS U V) ⟶ X'.toFunctor)
    (hψ : ψ ≫ X'.ι = yoneda.map (opensObjectι B S hS U V) ≫ φ) (n : ℕ)
    (hbound : ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X'.toFunctor, ∃ r : ℕ, r < n ∧
        IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd (ξ ≫ X'.ι))) r) :
    HasUniversallyBoundedFibers B S hS (opensObject B S hS U V) ψ := by
  classical
  let F := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan F := by apply comp_preservesLimitsOfShape
  let hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ
  let ιV := opensObjectι B S hS U V
  have hoiV : _root_.AlgebraicGeometry.IsOpenImmersion (F.map ιV) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V.ι)
  refine ⟨(n : ℤ), ?_⟩
  intro k _ T e ξ
  obtain ⟨r, hrn, hr⟩ := hbound k T e ξ
  let fstS : hrep.pullback (ξ ≫ X'.ι) ⟶ U := yoneda.preimage (hrep.fst (ξ ≫ X'.ι))
  have hfstSmap : yoneda.map fstS = hrep.fst (ξ ≫ X'.ι) := yoneda.map_preimage _
  have htop : IsPullback (yoneda.map (Limits.pullback.snd fstS ιV))
      (yoneda.map (Limits.pullback.fst fstS ιV)) (yoneda.map ιV) (yoneda.map fstS) :=
    ((IsPullback.of_hasPullback fstS ιV).map yoneda).flip
  have hbot : IsPullback (yoneda.map fstS) (yoneda.map (hrep.snd (ξ ≫ X'.ι))) φ
      (ξ ≫ X'.ι) := by
    rw [hfstSmap]
    exact hrep.isPullback (ξ ≫ X'.ι)
  have hpaste := htop.paste_vert hbot
  rw [← Functor.map_comp] at hpaste
  have hsq : IsPullback (yoneda.map (Limits.pullback.snd fstS ιV))
      (yoneda.map (Limits.pullback.fst fstS ιV ≫ hrep.snd (ξ ≫ X'.ι))) ψ ξ := by
    refine isPullback_of_comp_mono X'.ι ?_
    rw [hψ]
    exact hpaste
  have hoi : _root_.AlgebraicGeometry.IsOpenImmersion
      (F.map (Limits.pullback.fst fstS ιV)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      ((IsPullback.of_hasPullback fstS ιV).map F).flip hoiV
  have hre : IsFiniteLocallyFreeOfRank (F.map (hrep.snd (ξ ≫ X'.ι)) ≫ e.hom) r :=
    ((IsFiniteLocallyFreeOfRank.property.{u} r).cancel_right_of_respectsIso
      (F.map (hrep.snd (ξ ≫ X'.ι))) e.hom).2 hr
  obtain ⟨s, hsle, hs⟩ := exists_rank_le_of_isOpenImmersion_over_field
    (F.map (Limits.pullback.fst fstS ιV)) (F.map (hrep.snd (ξ ≫ X'.ι)) ≫ e.hom) r hre
  refine ⟨Limits.pullback fstS ιV,
    Limits.pullback.fst fstS ιV ≫ hrep.snd (ξ ≫ X'.ι),
    yoneda.map (Limits.pullback.snd fstS ιV), s, ?_, ?_, hsq⟩
  · exact_mod_cast Nat.le_of_lt (lt_of_le_of_lt hsle hrn)
  · refine ((IsFiniteLocallyFreeOfRank.property.{u} s).cancel_right_of_respectsIso
      (F.map (Limits.pullback.fst fstS ιV ≫ hrep.snd (ξ ≫ X'.ι))) e.hom).1 ?_
    rw [Functor.map_comp, Category.assoc]
    exact hs

/-! ### The degree condition on a morphism of schemes -/

/-- `DegreeGe f d` says that `f` has degree at least `d`: either `f` is not finite, and so counts
as having infinite degree, or it is finite locally free of some degree `r ≥ d`. -/
def DegreeGe {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  ¬ _root_.AlgebraicGeometry.IsFinite f ∨ ∃ r : ℕ, d ≤ r ∧ IsFiniteLocallyFreeOfRank f r

/-- `AlgebraicGeometry.Space.DegreeGe` unfolded. -/
theorem degreeGe_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    DegreeGe f d ↔ (¬ _root_.AlgebraicGeometry.IsFinite f ∨
      ∃ r : ℕ, d ≤ r ∧ IsFiniteLocallyFreeOfRank f r) :=
  Iff.rfl

/-- A fibre whose degree is at least `0` and not at least `n` is finite locally free of a rank
strictly below `n`. -/
theorem exists_rank_lt_of_degree_ge_zero_of_not_degree_ge {A C : Scheme.{u}} (f : A ⟶ C)
    (n : ℕ)
    (h0 : ¬ _root_.AlgebraicGeometry.IsFinite f ∨
      ∃ r : ℕ, 0 ≤ r ∧ IsFiniteLocallyFreeOfRank f r)
    (hn : ¬ (¬ _root_.AlgebraicGeometry.IsFinite f ∨
      ∃ r : ℕ, n ≤ r ∧ IsFiniteLocallyFreeOfRank f r)) :
    ∃ r : ℕ, r < n ∧ IsFiniteLocallyFreeOfRank f r := by
  rw [not_or, not_not, not_exists] at hn
  obtain ⟨hfin, hno⟩ := hn
  rcases h0 with hnf | ⟨r, -, hr⟩
  · exact absurd hfin hnf
  exact ⟨r, not_le.1 fun h => hno r ⟨h, hr⟩, hr⟩

/-- A property which is fpqc local on the target holds for a morphism exactly when it holds
for its base change along a single fpqc covering morphism. -/
theorem property_iff_fpqc_singleton_pullback (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcov : Presieve.singleton g ∈ Scheme.fpqcPrecoverage.coverings Y) :
    P f ↔ P (pullback.snd f g) := by
  refine ⟨fun hf => MorphismProperty.IsLocalAtTarget.pullbackSnd
    (P := P) hcov (Presieve.singleton_self g) hf, fun h => ?_⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hcov ?_
  intro U g' _ hg'
  cases hg'
  simpa using h

/-- The degree condition is unchanged by base change along a single fpqc covering morphism. -/
private theorem degreeGe_iff_pullbackSnd {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (d : ℕ)
    (hcov : Presieve.singleton g ∈ Scheme.fpqcPrecoverage.coverings Y) :
    DegreeGe f d ↔ DegreeGe (pullback.snd f g) d := by
  have hfin : _root_.AlgebraicGeometry.IsFinite f ↔
      _root_.AlgebraicGeometry.IsFinite (pullback.snd f g) :=
    property_iff_fpqc_singleton_pullback (@_root_.AlgebraicGeometry.IsFinite.{u}) f g hcov
  have hrank (r : ℕ) : IsFiniteLocallyFreeOfRank f r ↔
      IsFiniteLocallyFreeOfRank (pullback.snd f g) r :=
    property_iff_fpqc_singleton_pullback (IsFiniteLocallyFreeOfRank.property.{u} r) f g hcov
  simp only [DegreeGe, hfin, hrank]

/-- The degree condition is unchanged by precomposition with an isomorphism. -/
theorem degreeGe_iff_comp_iso {X X' Y : Scheme.{u}} (e : X' ≅ X) (f : X ⟶ Y) (d : ℕ) :
    DegreeGe f d ↔ DegreeGe (e.hom ≫ f) d := by
  let Pfin : MorphismProperty Scheme.{u} := @_root_.AlgebraicGeometry.IsFinite
  have hfin : _root_.AlgebraicGeometry.IsFinite f ↔ _root_.AlgebraicGeometry.IsFinite (e.hom ≫ f) :=
    (Pfin.cancel_left_of_respectsIso e.hom f).symm
  have hrank (r : ℕ) : IsFiniteLocallyFreeOfRank f r ↔
      IsFiniteLocallyFreeOfRank (e.hom ≫ f) r :=
    ((IsFiniteLocallyFreeOfRank.property.{u} r).cancel_left_of_respectsIso e.hom f).symm
  simp only [DegreeGe, hfin, hrank]

/-- The degree condition is unchanged by swapping the factors of a fibre product. -/
private theorem degreeGe_pullbackSnd_iff_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (d : ℕ) : DegreeGe (pullback.snd f g) d ↔ DegreeGe (pullback.fst g f) d := by
  rw [← pullbackSymmetry_hom_comp_fst f g]
  exact (degreeGe_iff_comp_iso (pullbackSymmetry f g) (pullback.fst g f) d).symm

/-- A fibre product taken in the site and one taken in schemes carry the same degree
condition. -/
private theorem degreeGe_map_pullbackSnd_iff
    {A C T : BigFppfOver B S hS} (f : A ⟶ T) (g : C ⟶ T) (d : ℕ) :
    DegreeGe ((BigFppfOver.toScheme B S hS).map (pullback.snd f g)) d ↔
      DegreeGe (pullback.fst ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map f)) d := by
  let : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  set F := BigFppfOver.toScheme B S hS
  let e := ((IsPullback.of_hasPullback f g).map F).isoIsPullback _ _
    (IsPullback.of_hasPullback (F.map f) (F.map g)) ≪≫
    pullbackSymmetry (F.map f) (F.map g)
  have he : e.hom ≫ pullback.fst (F.map g) (F.map f) = F.map (pullback.snd f g) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
      IsPullback.isoIsPullback_hom_snd]
  rw [← he]
  exact (degreeGe_iff_comp_iso e (pullback.fst (F.map g) (F.map f)) d).symm

/-- Base-changing a representable morphism along a composite `yoneda.map g ≫ a` is
base-changing it along `a` and then along `g`. -/
private theorem degreeGe_snd_comp_iff {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W U T : BigFppfOver B S hS} {f : yoneda.obj W ⟶ X}
    (hf : yoneda.relativelyRepresentable f) (a : yoneda.obj U ⟶ X) (g : T ⟶ U) (d : ℕ) :
    DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yoneda.map g ≫ a))) d ↔
      DegreeGe ((BigFppfOver.toScheme B S hS).map (pullback.snd (hf.snd a) g)) d := by
  set F := BigFppfOver.toScheme B S hS
  have hcomp := ((IsPullback.of_hasPullback (hf.snd a) g).map yoneda).paste_horiz
    (hf.isPullback a)
  let e := yoneda.preimageIso
    (hcomp.isoIsPullback _ _ (hf.isPullback (yoneda.map g ≫ a)))
  have he : e.hom ≫ hf.snd (yoneda.map g ≫ a) = pullback.snd (hf.snd a) g := by
    apply yoneda.map_injective
    simp [e, hcomp.isoIsPullback_hom_snd _ _ (hf.isPullback (yoneda.map g ≫ a))]
  have he' : (F.mapIso e).hom ≫ F.map (hf.snd (yoneda.map g ≫ a)) =
      F.map (pullback.snd (hf.snd a) g) := by
    show F.map e.hom ≫ _ = _
    rw [← Functor.map_comp, he]
  rw [← he']
  exact degreeGe_iff_comp_iso (F.mapIso e) (F.map (hf.snd (yoneda.map g ≫ a))) d

/-- A morphism of field spectra is a one-element fpqc covering. -/
theorem fpqc_singleton_of_fieldSpecHom {K L : Type u} [Field K] [Field L]
    (e : Spec (.of L) ⟶ Spec (.of K)) :
    Presieve.singleton e ∈ Scheme.fpqcPrecoverage.coverings (Spec (.of K)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective e
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage (Spec.map φ)

/-- The degree condition on a fibre over a field-valued point is unchanged by extending the
field. -/
private theorem degreeGe_fieldExtension_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : Type u} [Field K] [Field L] (g : Spec (.of K) ⟶ Y)
    (e : Spec (.of L) ⟶ Spec (.of K)) (d : ℕ) :
    DegreeGe (pullback.fst g f) d ↔ DegreeGe (pullback.fst (e ≫ g) f) d := by
  have hbase : DegreeGe (pullback.fst g f) d ↔
      DegreeGe (pullback.snd (pullback.fst g f) e) d :=
    degreeGe_iff_pullbackSnd (pullback.fst g f) e d
      (fpqc_singleton_of_fieldSpecHom e)
  have hassoc : DegreeGe (pullback.fst (e ≫ g) f) d ↔
      DegreeGe (pullback.fst e (pullback.fst g f)) d := by
    rw [← pullbackRightPullbackFstIso_hom_fst g f e]
    exact degreeGe_iff_comp_iso (pullbackRightPullbackFstIso g f e)
      (pullback.fst (e ≫ g) f) d
  exact hbase.trans ((degreeGe_pullbackSnd_iff_fst _ e d).trans hassoc.symm)

/-- The degree condition on the fibre of a representable morphism over a field-valued point
only depends on the point of the point space it represents, for one dominating the other. -/
private theorem degreeGe_iff_of_dominates {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B S hS} {f : yoneda.obj W ⟶ X}
    (hf : yoneda.relativelyRepresentable f) (p q : FieldValuedPoint B S hS X)
    (hpq : FieldValuedPoint.Dominates B S hS X q p) (d : ℕ) :
    DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm p.value))) d ↔
      DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm q.value))) d := by
  set F := BigFppfOver.toScheme B S hS
  obtain ⟨g, hg⟩ := hpq
  have hα : yoneda.map g ≫ yonedaEquiv.symm p.value = yonedaEquiv.symm q.value := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality (yonedaEquiv.symm p.value) g]
    simpa [FieldValuedPoint.siteObject] using hg
  have hrepr : DegreeGe (F.map (hf.snd (yonedaEquiv.symm q.value))) d ↔
      DegreeGe (F.map (pullback.snd (hf.snd (yonedaEquiv.symm p.value)) g)) d := by
    rw [← hα]
    exact degreeGe_snd_comp_iff B S hS hf (yonedaEquiv.symm p.value) g d
  have hext : DegreeGe (F.map (hf.snd (yonedaEquiv.symm p.value))) d ↔
      DegreeGe (pullback.snd (F.map (hf.snd (yonedaEquiv.symm p.value))) (F.map g)) d :=
    degreeGe_iff_pullbackSnd _ (F.map g) d (fpqc_singleton_of_fieldSpecHom (F.map g))
  have hsite := degreeGe_map_pullbackSnd_iff B S hS (hf.snd (yonedaEquiv.symm p.value)) g d
  exact (hext.trans ((degreeGe_pullbackSnd_iff_fst _ _ d).trans hsite.symm)).trans hrepr.symm

/-- The degree condition on the fibre of a representable morphism over a field-valued point
only depends on the point of the point space it represents. -/
theorem degreeGe_iff_of_class_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B S hS} {f : yoneda.obj W ⟶ X}
    (hf : yoneda.relativelyRepresentable f) (p q : FieldValuedPoint B S hS X)
    (hclass : p.class B S hS X = q.class B S hS X) (d : ℕ) :
    DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm p.value))) d ↔
      DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm q.value))) d := by
  obtain ⟨r, hp, hq⟩ := (FieldValuedPoint.class_eq_class_iff B S hS X p q).mp hclass
  exact (degreeGe_iff_of_dominates B S hS hf p r hp d).trans
    (degreeGe_iff_of_dominates B S hS hf q r hq d).symm

/-! ### Properties of a fibre, on the presheaf and on the representing scheme -/

/-- A property of scheme morphisms stable under base change holds for the representing object
of the fibre of `f : yoneda.obj W ⟶ X` over a morphism `a : yoneda.obj A ⟶ X` exactly when its
relatively representable form holds for the first projection of the fibre product of
presheaves. -/
theorem presheaf_pullback_fst_iff_property_snd
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W A : BigFppfOver B S hS}
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {f : yoneda.obj W ⟶ X} (hf : yoneda.relativelyRepresentable f) (a : yoneda.obj A ⟶ X) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.fst a f) ↔
      P ((BigFppfOver.toScheme B S hS).map (hf.snd a)) := by
  set F := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan F := by apply comp_preservesLimitsOfShape
  let : (MorphismProperty.inverseImage P F).IsStableUnderBaseChange := by
    constructor
    intro _ _ _ _ _ _ _ _ hsq hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (hsq.map F) hg
  have hRI : (MorphismProperty.inverseImage P F).RespectsIso := inferInstance
  have hRI' : (MorphismProperty.inverseImage P F).presheaf.RespectsIso := inferInstance
  set e := (IsPullback.of_hasPullback a f).isoIsPullback _ _ (hf.isPullback a).flip
  have he : e.hom ≫ yoneda.map (hf.snd a) = pullback.fst a f := by
    simp [e]
  exact ((MorphismProperty.inverseImage P F).presheaf.arrow_mk_iso_iff
    (Arrow.isoMk e (Iso.refl _) he)).trans
    ((MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage P F)).trans Iff.rfl)

/-- The degree condition on the representing object of a fibre, written out on the fibre
product of presheaves. -/
theorem degreeGe_iff_presheaf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W A : BigFppfOver B S hS} {f : yoneda.obj W ⟶ X}
    (hf : yoneda.relativelyRepresentable f) (a : yoneda.obj A ⟶ X) (d : ℕ) :
    DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd a)) d ↔
      (¬ (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst a f) ∨
        ∃ r : ℕ, d ≤ r ∧
          (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst a f)) := by
  have hfin := presheaf_pullback_fst_iff_property_snd B S hS
    (P := @_root_.AlgebraicGeometry.IsFinite.{u}) hf a
  have hrank (r : ℕ) := presheaf_pullback_fst_iff_property_snd B S hS
    (P := IsFiniteLocallyFreeOfRank.property.{u} r) hf a
  constructor
  · rintro (hn | ⟨r, hr, hh⟩)
    · exact Or.inl fun hp => hn (hfin.mp hp)
    · exact Or.inr ⟨r, hr, (hrank r).mpr hh⟩
  · rintro (hn | ⟨r, hr, hh⟩)
    · exact Or.inl fun hp => hn (hfin.mpr hp)
    · exact Or.inr ⟨r, hr, (hrank r).mp hh⟩

/-- The fibre of `f` over a composite `yoneda.map g ≫ a` is the fibre over `g` of the base
change of `f` along `a`. -/
theorem degreeGe_snd_yoneda_comp_iff {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W U T : BigFppfOver B S hS} {f : yoneda.obj W ⟶ X}
    (hf : yoneda.relativelyRepresentable f) (a : yoneda.obj U ⟶ X) (g : T ⟶ U) (d : ℕ) :
    DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yoneda.map g ≫ a))) d ↔
      DegreeGe (pullback.fst ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map (hf.snd a))) d :=
  (degreeGe_snd_comp_iff B S hS hf a g d).trans
    (degreeGe_map_pullbackSnd_iff B S hS (hf.snd a) g d)

/-! ### Open sets of points from open subschemes of a chart -/

/-- The set of points of a represented presheaf whose underlying scheme point lies in a given
subset of the representing scheme. -/
private def pointsOfSchemeSet (U : BigFppfOver B S hS)
    (V : Set ((BigFppfOver.toScheme B S hS).obj U)) :
    Set (points B S hS (yoneda.obj U)) :=
  {y | ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
    p.class B S hS (yoneda.obj U) = y ∧ schemePoint B S hS U p ∈ V}

private theorem mem_pointsOfSchemeSet_iff (U : BigFppfOver B S hS)
    (V : Set ((BigFppfOver.toScheme B S hS).obj U))
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    p.class B S hS (yoneda.obj U) ∈ pointsOfSchemeSet B S hS U V ↔
      schemePoint B S hS U p ∈ V := by
  refine ⟨?_, fun hpV => ⟨p, rfl, hpV⟩⟩
  rintro ⟨q, hq, hqV⟩
  exact (schemePoint_eq_of_class_eq B S hS U q p hq).symm ▸ hqV

private theorem isOpen_pointsOfSchemeSet (U : BigFppfOver B S hS)
    (V : Set ((BigFppfOver.toScheme B S hS).obj U)) (hV : IsOpen V) :
    IsOpen (pointsOfSchemeSet B S hS U V) :=
  (isOpen_yoneda_iff_isSchemeOpen B S hS U _).2
    ⟨V, hV, fun p => mem_pointsOfSchemeSet_iff B S hS U V p⟩

/-- A field-valued point of a chart factors through an open subscheme of the chart exactly
when its underlying scheme point lies in that open. -/
private theorem factors_through_opens_iff_schemePoint (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (q : FieldValuedPoint B S hS (yoneda.obj U)) :
    (∃ h : Spec (.of q.carrier) ⟶ V.toScheme,
        h ≫ V.ι = (BigFppfOver.toScheme B S hS).map q.value) ↔
      schemePoint B S hS U q ∈ V := by
  rw [factors_through_open_iff_mem q.carrier _ V]
  have hpt : (default : ↥(Spec (CommRingCat.of q.carrier))) =
      IsLocalRing.closedPoint q.carrier := Subsingleton.elim _ _
  rw [hpt]
  exact Iff.rfl

/-- The image in the points of `X` of the points of a chart lying over an open subscheme of
it. -/
private def atlasPointImage {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : Set (points B S hS X) :=
  pointsMap B S hS (yoneda.obj U) a '' pointsOfSchemeSet B S hS U (V : Set _)

/-- The image of an open set of points of an étale chart is open, by clause (3) of
Tag 03BX. -/
private theorem isOpen_atlasPointImage {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    IsOpen (atlasPointImage B S hS U a V) :=
  isOpenMap_pointsMap_of_etale B S hS hX U a ha _
    (isOpen_pointsOfSchemeSet B S hS U (V : Set _) V.2)

private theorem atlasPointImage_mono {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (V W : ((BigFppfOver.toScheme B S hS).obj U).Opens) (hVW : V ≤ W) :
    atlasPointImage B S hS U a V ⊆ atlasPointImage B S hS U a W := by
  rintro p ⟨q, ⟨r, hr, hrV⟩, hq⟩
  exact ⟨q, ⟨r, hr, hVW hrV⟩, hq⟩

/-! ### Points of the tautological chart at a field-valued point -/

/-- The morphism `yoneda.obj (Spec k) ⟶ X` attached to a field-valued point of `X` carries
every point of its source to the point represented by that field-valued point. -/
private theorem pointsMap_yonedaEquiv_symm_class
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS X)
    (q : FieldValuedPoint B S hS (yoneda.obj p.siteObject)) :
    pointsMap B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value)
        (q.class B S hS (yoneda.obj p.siteObject)) = p.class B S hS X := by
  rw [pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS X
    ⟨FieldValuedPoint.map B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value) q,
      FieldValuedPoint.dominates_refl B S hS X _, q.value, ?_⟩
  show X.map q.value.op p.value = _
  simp [FieldValuedPoint.map]

/-- The point set of the tautological chart of a field-valued point is the single point that
field-valued point represents. -/
theorem range_pointsMap_yonedaEquiv_symm
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS X) :
    Set.range (pointsMap B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value)) =
      {p.class B S hS X} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨q, rfl⟩ := Quot.exists_rep y
    rw [pointsMap_yonedaEquiv_symm_class B S hS p q]
    simp
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    let q : FieldValuedPoint B S hS (yoneda.obj p.siteObject) :=
      { carrier := p.carrier
        field := p.field
        contained := p.contained
        toBase := p.toBase
        value := 𝟙 p.siteObject }
    exact ⟨q.class B S hS (yoneda.obj p.siteObject),
      pointsMap_yonedaEquiv_symm_class B S hS p q⟩

/-! ### The chain of opens on a chart -/

/-- Let `f : yoneda.obj W ⟶ X` be flat, locally of finite presentation, separated and locally
quasi-finite as a morphism of algebraic spaces over `S`, and let `a : yoneda.obj U ⟶ X` be an étale
chart of `X`. Then the morphism of schemes representing the base change of `f` along `a` has all
four properties at the level of schemes. -/
theorem baseChange_properties_of_etale_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W U : BigFppfOver B S hS}
    {f : yoneda.obj W ⟶ X} (a : yoneda.obj U ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hsep : IsSeparated B S hS f) (hlqf : IsLocallyQuasiFinite B S hS f) :
    Flat ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a)) ∧
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a)) ∧
      LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a)) := by
  set hf := relativelyRepresentable_of_isAlgebraicSpace B S hS hX f with hfdef
  have hfstEtale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hf.fst a) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback (hf.isPullback a).flip ha
  have hsepRelative : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u}) (BigFppfOver.toScheme B S hS))) f :=
    (isSeparated_iff_presheaf B S hS f (isAlgebraicSpace_yoneda B S hS W) hX hf).1 hsep
  exact ⟨hflat (hf.pullback a) U (hf.fst a) a (hf.snd a) hfstEtale ha (hf.w a).symm,
    hfp (hf.pullback a) U (hf.fst a) a (hf.snd a) hfstEtale ha (hf.w a).symm,
    hsepRelative.2 a (hf.fst a) (hf.snd a) (hf.isPullback a),
    (hlqf (hf.pullback a) U (hf.fst a) a (hf.snd a) hfstEtale ha (hf.w a).symm).2⟩

/-- For the base change of `f` to an étale chart of `X`, the chain of opens of the chart
detecting the degree of a fibre. -/
theorem exists_antitone_opens_of_etale_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W U : BigFppfOver B S hS}
    {f : yoneda.obj W ⟶ X} (a : yoneda.obj U ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hsep : IsSeparated B S hS f) (hlqf : IsLocallyQuasiFinite B S hS f) :
    ∃ V : ℕ → ((BigFppfOver.toScheme B S hS).obj U).Opens,
      V 0 = ⊤ ∧ Antitone V ∧
        ∀ (d : ℕ) (k : Type u) [Field k]
          (g : Spec (.of k) ⟶ (BigFppfOver.toScheme B S hS).obj U),
          (∃ h : Spec (.of k) ⟶ (V d).toScheme, h ≫ (V d).ι = g) ↔
            DegreeGe (pullback.fst g ((BigFppfOver.toScheme B S hS).map
              ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a))) d := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    baseChange_properties_of_etale_chart B S hS a hX ha hflat hfp hsep hlqf
  let := h₁; let := h₂; let := h₃; let := h₄
  exact exists_antitone_opens_iff_fiber_degree_ge ((BigFppfOver.toScheme B S hS).map
    ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a))

/-- The morphism `yoneda.obj (Spec k) ⟶ X` attached to the image in `X` of a field-valued point
`q` of a chart `a` is the composite of `a` with the morphism attached to `q`. -/
private theorem yonedaEquiv_symm_map_value {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ X)
    (q : FieldValuedPoint B S hS (yoneda.obj T)) :
    yonedaEquiv.symm (FieldValuedPoint.map B S hS (yoneda.obj T) a q).value =
      yoneda.map q.value ≫ a := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  erw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rfl

/-- Let `V` be the `d`-th member of the chain of
`AlgebraicGeometry.Space.exists_antitone_opens_of_etale_chart` for a morphism `f` and an étale
chart `a` of `X`. Then a field-valued point `q` of the chart has its underlying scheme point in `V`
exactly when the fibre of `f` above a field-valued point of `X` carrying the same point of the
point space has degree at least `d`. -/
theorem degreeGe_iff_mem_of_etale_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W U : BigFppfOver B S hS}
    {f : yoneda.obj W ⟶ X} (a : yoneda.obj U ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) (d : ℕ)
    (hVdeg : ∀ (k : Type u) [Field k]
        (g : Spec (.of k) ⟶ (BigFppfOver.toScheme B S hS).obj U),
        (∃ h : Spec (.of k) ⟶ V.toScheme, h ≫ V.ι = g) ↔
          DegreeGe (pullback.fst g ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a))) d)
    (q : FieldValuedPoint B S hS (yoneda.obj U)) (p : FieldValuedPoint B S hS X)
    (hqclass : pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U)) =
      p.class B S hS X) :
    schemePoint B S hS U q ∈ V ↔
      DegreeGe ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd
          (yonedaEquiv.symm p.value))) d := by
  set hf := relativelyRepresentable_of_isAlgebraicSpace B S hS hX f with hfdef
  let qX := FieldValuedPoint.map B S hS (yoneda.obj U) a q
  have hqXclass : qX.class B S hS X = p.class B S hS X := by
    rw [← hqclass]
    rfl
  calc schemePoint B S hS U q ∈ V
      ↔ DegreeGe (pullback.fst ((BigFppfOver.toScheme B S hS).map q.value)
        ((BigFppfOver.toScheme B S hS).map (hf.snd a))) d := by
        rw [← factors_through_opens_iff_schemePoint B S hS U V q]
        exact hVdeg q.carrier ((BigFppfOver.toScheme B S hS).map q.value)
    _ ↔ DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm qX.value))) d
        := by
        rw [yonedaEquiv_symm_map_value]
        exact (degreeGe_snd_yoneda_comp_iff B S hS hf a q.value d).symm
    _ ↔ DegreeGe ((BigFppfOver.toScheme B S hS).map
          (hf.snd (yonedaEquiv.symm p.value))) d :=
        degreeGe_iff_of_class_eq B S hS hf qX p hqXclass d

/-- A morphism `a : yoneda.obj T ⟶ X` whose source object has underlying scheme isomorphic to the
spectrum of a field carries a field-valued point `p` of `X`, and the fibre of `f` over `a` has
degree at least `d` exactly when the fibre over `p` does. -/
theorem exists_fieldValuedPoint_degreeGe_iff
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} (f : yoneda.obj W ⟶ X)
    (k : Type u) [Field k] (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) (a : yoneda.obj T ⟶ X) :
    ∃ p : FieldValuedPoint B S hS X,
      p.class B S hS X ∈ Set.range (pointsMap B S hS (yoneda.obj T) a) ∧
      ∀ d : ℕ,
        (DegreeGe ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd a)) d ↔
          DegreeGe ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd
              (yonedaEquiv.symm p.value))) d) := by
  classical
  set hf := relativelyRepresentable_of_isAlgebraicSpace B S hS hX f with hfdef
  have hTne : Nonempty ((BigFppfOver.toScheme B S hS).obj T) :=
    ⟨e.inv (IsLocalRing.closedPoint k)⟩
  obtain ⟨q⟩ : Nonempty (FieldValuedPoint B S hS (yoneda.obj T)) := by
    obtain ⟨y⟩ : Nonempty (points B S hS (yoneda.obj T)) :=
      ⟨(pointsEquivScheme B S hS T).symm hTne.some⟩
    obtain ⟨q, -⟩ := Quot.exists_rep y
    exact ⟨q⟩
  refine ⟨FieldValuedPoint.map B S hS (yoneda.obj T) a q, ?_, fun d => ?_⟩
  · exact ⟨q.class B S hS (yoneda.obj T), rfl⟩
  · have hfl : Flat ((BigFppfOver.toScheme B S hS).map q.value) := by
      have : Flat (((BigFppfOver.toScheme B S hS).map q.value ≫ e.hom) ≫ e.inv) := by
        obtain ⟨φ, hφ⟩ := Spec.map_surjective
          ((BigFppfOver.toScheme B S hS).map q.value ≫ e.hom)
        rw [← hφ]
        infer_instance
      simpa using this
    have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) := by
      refine ⟨fun x y => ?_⟩
      have hxy : e.hom.base x = e.hom.base y := Subsingleton.elim _ _
      calc x = e.inv (e.hom x) := by
            rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
        _ = e.inv (e.hom y) := by rw [hxy]
        _ = y := by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
    have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map q.value) :=
      ⟨fun _ => ⟨IsLocalRing.closedPoint q.carrier, hsub.elim _ _⟩⟩
    have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q.value) := by
      have hsubq : Subsingleton ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
        inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
      exact ⟨fun V _ _ =>
        (Set.Subsingleton.finite fun x _ y _ => hsubq.elim x y).isCompact⟩
    have hcov : Presieve.singleton ((BigFppfOver.toScheme B S hS).map q.value) ∈
        Scheme.fpqcPrecoverage.coverings ((BigFppfOver.toScheme B S hS).obj T) :=
      Scheme.Hom.singleton_mem_fpqcPrecoverage ((BigFppfOver.toScheme B S hS).map q.value)
    calc DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd a)) d
        ↔ DegreeGe (pullback.snd ((BigFppfOver.toScheme B S hS).map (hf.snd a))
            ((BigFppfOver.toScheme B S hS).map q.value)) d :=
          degreeGe_iff_pullbackSnd _ _ d hcov
      _ ↔ DegreeGe (pullback.fst ((BigFppfOver.toScheme B S hS).map q.value)
            ((BigFppfOver.toScheme B S hS).map (hf.snd a))) d :=
          degreeGe_pullbackSnd_iff_fst _ _ d
      _ ↔ DegreeGe ((BigFppfOver.toScheme B S hS).map (hf.snd (yoneda.map q.value ≫ a))) d :=
          (degreeGe_snd_yoneda_comp_iff B S hS hf a q.value d).symm
      _ ↔ _ := by rw [yonedaEquiv_symm_map_value]; exact Iff.rfl

/-- A morphism of presheaves which composes with a monomorphism to a relative open immersion is
itself a relative open immersion. -/
theorem isOpenImmersion_of_comp_mono {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (m : G ⟶ H) [Mono m] (hcomp : IsOpenImmersion B S hS (f ≫ m)) :
    IsOpenImmersion B S hS f :=
  MorphismProperty.relative.of_exists fun _ g =>
    ⟨hcomp.rep.pullback (g ≫ m), hcomp.rep.fst (g ≫ m), hcomp.rep.snd (g ≫ m),
      isPullback_of_comp_mono m (hcomp.rep.isPullback (g ≫ m)),
      hcomp.property_snd (g ≫ m)⟩

/-- If `Y` is an open subspace of `X` and `H` is a representable open subspace of `Y`, then `X` has
an open subspace which is representable and whose point set is the image of the point set of
`H`. -/
theorem exists_isOpenSubspace_isRepresentable_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Y : Subfunctor X} (hY : IsOpenSubspace B S hS Y)
    {H : Subfunctor Y.toFunctor} (hH : IsOpenSubspace B S hS H)
    (hHrep : H.toFunctor.IsRepresentable) :
    ∃ K : Subfunctor X, IsOpenSubspace B S hS K ∧ K.toFunctor.IsRepresentable ∧
      Set.range (pointsMap B S hS K.toFunctor K.ι) =
        Set.range (pointsMap B S hS H.toFunctor (H.ι ≫ Y.ι)) := by
  classical
  have _ := hHrep
  set Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)) with hQ
  have hQmul : Q.IsMultiplicative := inferInstance
  have hQiso : Q.RespectsIso := inferInstance
  set χ := H.toFunctor.reprW.hom ≫ H.ι ≫ Y.ι with hχ
  have hχopen : IsOpenImmersion B S hS χ :=
    MorphismProperty.RespectsIso.precomp Q H.toFunctor.reprW.hom _
      (Q.comp_mem _ _ hH.2 hY.2)
  have hle : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) := by
    intro A C k hk
    have hoi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map k) := hk
    exact (inferInstance : Etale ((BigFppfOver.toScheme B S hS).map k))
  have hχetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf χ :=
    MorphismProperty.relative_monotone (F := yoneda) hle _ hχopen
  obtain ⟨K, ψ, hKopen, hψχ, hψsurj, -, hKimage⟩ :=
    exists_isOpenSubspace_etaleImage B S hS hX H.toFunctor.reprX χ hχetale
  have hψopen : IsOpenImmersion B S hS ψ :=
    isOpenImmersion_of_comp_mono B S hS ψ K.ι (by rw [hψχ]; exact hχopen)
  have hψiso : IsIso ψ :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS ψ hψopen hψsurj
  have hsurjε : Function.Surjective (pointsMap B S hS (yoneda.obj H.toFunctor.reprX)
      H.toFunctor.reprW.hom) := by
    intro z
    refine ⟨pointsMap B S hS H.toFunctor H.toFunctor.reprW.inv z, ?_⟩
    have := congrFun (pointsMap_comp B S hS H.toFunctor H.toFunctor.reprW.inv
      H.toFunctor.reprW.hom) z
    simp only [Iso.inv_hom_id, Function.comp_apply] at this
    rw [← this]
    simp [pointsMap_id]
  refine ⟨K, hKopen, Functor.IsRepresentable.mk' (asIso ψ), ?_⟩
  rw [hKimage, hχ, pointsMap_comp, Set.range_comp, hsurjε.range_eq, Set.image_univ]

/-! ### Stacks 086T -/

/-- Let `X` be an algebraic space over a scheme `S` and let `f : yoneda.obj W ⟶ X` be a morphism
from a scheme which is flat, locally of finite presentation, separated and locally quasi-finite.
Then there is a descending chain of open subspaces
`X = X₀ ⊇ X₁ ⊇ X₂ ⊇ …`
such that a field-valued point of `X` factors through `Xᵈ` exactly when the fibre of `f`
above it has degree at least `d`; a fibre which is not finite counts as having infinite
degree. -/
@[stacks 086T]
theorem exists_antitone_isOpenSubspace_iff_fibre_degree_ge
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W : BigFppfOver B S hS} (f : yoneda.obj W ⟶ X)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hsep : IsSeparated B S hS f) (hlqf : IsLocallyQuasiFinite B S hS f) :
    ∃ Y : ℕ → Subfunctor X,
      Y 0 = ⊤ ∧ Antitone Y ∧ (∀ d, IsOpenSubspace B S hS (Y d)) ∧
      ∀ (d : ℕ) (p : FieldValuedPoint B S hS X),
        (∃ g : yoneda.obj p.siteObject ⟶ (Y d).toFunctor,
            g ≫ (Y d).ι = yonedaEquiv.symm p.value) ↔
          (¬ (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
                (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) f) ∨
            ∃ r : ℕ, d ≤ r ∧
              (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) f)) := by
  classical
  obtain ⟨U, a, hsurj, haEtale⟩ := hX.exists_atlas
  obtain ⟨V, hV0, hVanti, hVdeg⟩ :=
    exists_antitone_opens_of_etale_chart B S hS a hX haEtale hflat hfp hsep hlqf
  set hf := relativelyRepresentable_of_isAlgebraicSpace B S hS hX f with hfdef
  have hatlasSurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).1 hsurj
  refine ⟨fun d => openSubspaceOfPoints B S hS X (atlasPointImage B S hS U a (V d)), ?_, ?_,
    fun d => isOpenSubspace_openSubspaceOfPoints B S hS hX _
      (isOpen_atlasPointImage B S hS hX U a haEtale (V d)), ?_⟩
  · refine le_antisymm le_top fun T x _ => ?_
    rw [mem_openSubspaceOfPoints_iff]
    rintro y ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hatlasSurj (pointsMap B S hS (yoneda.obj T.unop) (yonedaEquiv.symm x) z)
    obtain ⟨q, rfl⟩ := Quot.exists_rep w
    exact ⟨q.class B S hS (yoneda.obj U), ⟨q, rfl, by rw [hV0]; trivial⟩, hw⟩
  · intro i j hij T x hx
    rw [mem_openSubspaceOfPoints_iff] at hx ⊢
    exact hx.trans (atlasPointImage_mono B S hS U a (V j) (V i) (hVanti hij))
  · intro d p
    rw [factorsThrough_openSubspace_iff_points B S hS hX
      (isAlgebraicSpace_yoneda B S hS p.siteObject) _
      (isOpenSubspace_openSubspaceOfPoints B S hS hX _
        (isOpen_atlasPointImage B S hS hX U a haEtale (V d))) (yonedaEquiv.symm p.value),
      range_pointsMap_yonedaEquiv_symm B S hS p,
      range_pointsMap_ι_openSubspaceOfPoints, Set.singleton_subset_iff,
      ← degreeGe_iff_presheaf B S hS hf (yonedaEquiv.symm p.value) d]
    have key (q : FieldValuedPoint B S hS (yoneda.obj U))
        (hqclass : pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U)) =
          p.class B S hS X) :
        schemePoint B S hS U q ∈ V d ↔
          DegreeGe ((BigFppfOver.toScheme B S hS).map
            (hf.snd (yonedaEquiv.symm p.value))) d :=
      degreeGe_iff_mem_of_etale_chart B S hS a hX (V d) d (hVdeg d) q p hqclass
    constructor
    · rintro ⟨y, ⟨q, hqy, hqV⟩, hy⟩
      exact (key q (by rw [hqy, hy])).1 hqV
    · intro hdeg
      obtain ⟨y, hy⟩ := hatlasSurj (p.class B S hS X)
      obtain ⟨q, rfl⟩ := Quot.exists_rep y
      exact ⟨q.class B S hS (yoneda.obj U), ⟨q, rfl, (key q hy).2 hdeg⟩, hy⟩

/-! ### Exhaustion of the chain on a decent algebraic space -/

/-- The fibre of an étale chart with quasi-compact source above a *quasi-compact* field-valued
point is finite locally free of some degree. -/
theorem exists_isFiniteLocallyFreeOfRank_snd_fieldMorphism
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS Y)
    (hp : IsQuasiCompact B S hS (fieldMorphism B S hS Y p))
    {V : BigFppfOver B S hS} (hV : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
    (φ : yoneda.obj V ⟶ Y)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    ∃ r : ℕ, IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (hφ.rep.snd (fieldMorphism B S hS Y p))) r := by
  set X₀ := (BigFppfOver.toScheme B S hS).obj p.siteObject with hX₀
  set g := (BigFppfOver.toScheme B S hS).map (hφ.rep.snd (fieldMorphism B S hS Y p)) with hg
  have hetale : Etale g := hφ.property_snd _
  have hqcs : IsQuasiCompactSpace B S hS (pullback φ (fieldMorphism B S hS Y p)) :=
    hp (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda_obj B S hS hV) _
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (hφ.rep.pullback (fieldMorphism B S hS Y p))) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (hqcs.of_iso B S hS
        ((IsPullback.of_hasPullback φ (fieldMorphism B S hS Y p)).isoIsPullback _ _
          (hφ.rep.isPullback (fieldMorphism B S hS Y p))))
  obtain ⟨hft, hqf⟩ := locallyQuasiFinite_of_etale g
  let := hft
  let := hqf
  obtain ⟨n, hn⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite g
  obtain ⟨r, -, hr⟩ := (boundsFiberDegrees_iff_field_baseChange g n).1 hn p.carrier (𝟙 X₀)
  refine ⟨r, ?_⟩
  have hiso : IsIso (pullback.snd (𝟙 X₀) g) :=
    (IsPullback.of_hasPullback (𝟙 X₀) g).isIso_snd_of_isIso
  have hcond : pullback.fst (𝟙 X₀) g = pullback.snd (𝟙 X₀) g ≫ g := by
    simpa using pullback.condition (f := 𝟙 X₀) (g := g)
  rw [hcond] at hr
  exact ((IsFiniteLocallyFreeOfRank.property.{u} r).cancel_left_of_respectsIso
    (pullback.snd (𝟙 X₀) g) g).1 hr

/-- Above every field-valued point of a *decent* algebraic space over `S`, an étale chart with
quasi-compact source has a fibre whose degree is finite: there is a `d` for which the fibre does
not have degree at least `d`, so the point does not lie in every member of the chain of
`AlgebraicGeometry.Space.exists_antitone_isOpenSubspace_iff_fibre_degree_ge`. -/
theorem exists_not_fibre_degree_ge_of_isDecentSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hdec : IsDecentSpace B S hS X)
    {U : BigFppfOver B S hS} (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (p : FieldValuedPoint B S hS X) :
    ∃ d : ℕ, ¬ (¬ (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.fst (yonedaEquiv.symm p.value) φ) ∨
      ∃ r : ℕ, d ≤ r ∧
        (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
          (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.fst (yonedaEquiv.symm p.value) φ)) := by
  obtain ⟨q, hqclass, -, hqqc⟩ := hdec (p.class B S hS X)
  obtain ⟨r, hr⟩ := exists_isFiniteLocallyFreeOfRank_snd_fieldMorphism B S hS q hqqc hU φ hφ
  refine ⟨r + 1, ?_⟩
  rw [← degreeGe_iff_presheaf B S hS hφ.rep (yonedaEquiv.symm p.value) (r + 1),
    degreeGe_iff_of_class_eq B S hS hφ.rep p q hqclass.symm (r + 1), degreeGe_iff]
  let := hr
  have hflf := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((BigFppfOver.toScheme B S hS).map (hφ.rep.snd (fieldMorphism B S hS X q))) r
  rintro (hnf | ⟨t, ht, hrt⟩)
  · exact hnf ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1 hflf).1
  · have := finiteLocallyFree_rank_unique
      (k := q.carrier)
      ((BigFppfOver.toScheme B S hS).map (hφ.rep.snd (fieldMorphism B S hS X q))) r t hr hrt
    omega

/-! ### Restatements -/

/-- `AlgebraicGeometry.Space.presheaf_pullback_fst_iff_property_snd`, with the morphism whose
fibre is being tested given explicitly. -/
theorem presheafFibreProperty_iff_schemeFibreProperty
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A : BigFppfOver B S hS}
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso] [P.IsStableUnderBaseChange]
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.fst a f) ↔
      P ((BigFppfOver.toScheme B S hS).map (hf.snd a)) :=
  presheaf_pullback_fst_iff_property_snd B S hS hf a

/-- A field-valued point factors through the subspace cut out by a set `W` of points exactly
when its own class lies in `W`. -/
theorem exists_comp_ι_openSubspaceOfPoints_iff
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : Set (points B S hS X))
    (p : FieldValuedPoint B S hS X) :
    (∃ g : yoneda.obj (FieldValuedPoint.siteObject B S hS X p) ⟶
        (openSubspaceOfPoints B S hS X W).toFunctor,
      g ≫ (openSubspaceOfPoints B S hS X W).ι = yonedaEquiv.symm p.value) ↔
      p.class B S hS X ∈ W := by
  have hmem : p.value ∈ (openSubspaceOfPoints B S hS X W).obj
      (Opposite.op (FieldValuedPoint.siteObject B S hS X p)) ↔ p.class B S hS X ∈ W := by
    rw [mem_openSubspaceOfPoints_iff, range_pointsMap_yonedaEquiv_symm]
    exact Set.singleton_subset_iff
  constructor
  · rintro ⟨g, hg⟩
    refine hmem.1 ?_
    rw [mem_openSubspaceOfPoints_iff, ← hg, pointsMap_comp]
    exact Set.Subset.trans (Set.range_comp_subset_range _ _)
      (range_pointsMap_ι_openSubspaceOfPoints B S hS W).le
  · intro h
    exact ⟨yonedaEquiv.symm ⟨p.value, hmem.2 h⟩,
      yonedaEquiv_symm_naturality_right _ (openSubspaceOfPoints B S hS X W).ι _⟩

/-- `AlgebraicGeometry.Space.exists_antitone_isOpenSubspace_iff_fibre_degree_ge` with its
conjuncts reordered and with three further hypotheses, which are not used. -/
theorem exists_antitone_openSubspaces_iff_fibreDegree_ge
    (_h02LA : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
    (_h02VO : ∀ r : ℕ, MorphismProperty.IsLocalAtTarget
      (IsFiniteLocallyFreeOfRank.property.{u} r) Scheme.fpqcPrecoverage)
    (_h086R : ∀ {Z Y : Scheme.{u}} (g : Z ⟶ Y), Flat g → LocallyOfFinitePresentation g →
      _root_.AlgebraicGeometry.IsSeparated g → LocallyQuasiFinite g →
      ∃ V : ℕ → Y.Opens, V 0 = ⊤ ∧ Antitone V ∧
        ∀ (d : ℕ) (k : Type u) (_ : Field k) (c : Spec (.of k) ⟶ Y),
          (∃ h : Spec (.of k) ⟶ (V d).toScheme, h ≫ (V d).ι = c) ↔
            (¬ _root_.AlgebraicGeometry.IsFinite (pullback.fst c g) ∨
              ∃ r : ℕ, d ≤ r ∧ IsFiniteLocallyFreeOfRank (pullback.fst c g) r))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : BigFppfOver B S hS) (f : yoneda.obj V ⟶ X)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hsep : IsSeparated B S hS f) (hlqf : IsLocallyQuasiFinite B S hS f) :
    ∃ U : ℕ → Subfunctor X,
      (∀ d, IsOpenSubspace B S hS (U d)) ∧ U 0 = ⊤ ∧ Antitone U ∧
      ∀ (d : ℕ) (p : FieldValuedPoint B S hS X),
        (∃ g : yoneda.obj (FieldValuedPoint.siteObject B S hS X p) ⟶ (U d).toFunctor,
          g ≫ (U d).ι = yonedaEquiv.symm p.value) ↔
        (¬ (MorphismProperty.inverseImage
              (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) f) ∨
          ∃ r : ℕ, d ≤ r ∧
            (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm p.value) f)) := by
  obtain ⟨Y, h0, hanti, hopen, hdeg⟩ :=
    exists_antitone_isOpenSubspace_iff_fibre_degree_ge B S hS hX f hflat hfp hsep hlqf
  exact ⟨Y, hopen, h0, hanti, hdeg⟩

end AlgebraicGeometry.Space

/-! ### The dichotomy on a descending chain of opens -/

namespace AlgebraicGeometry

/-- Let `U` be a nonempty scheme and `W : ℕ → U.Opens` any family of opens with `W 0 = ⊤`. Then
either some nonempty affine open of `U` misses some member of the family, or there is a descending
chain of nonempty affine opens `V 0 ⊇ V 1 ⊇ …` with `V n` inside `W n`. The family need not be
antitone. -/
theorem exists_isAffineOpen_disjoint_or_exists_antitone_isAffineOpen
    {U : Scheme.{u}} [Nonempty U] (W : ℕ → U.Opens) (hW0 : W 0 = ⊤) :
    (∃ (n : ℕ) (V : U.Opens), IsAffineOpen V ∧ (V : Set U).Nonempty ∧
        ∀ x : U, x ∈ V → x ∉ W n) ∨
      (∃ V : ℕ → U.Opens, Antitone V ∧ (∀ n, IsAffineOpen (V n)) ∧
        (∀ n, (V n : Set U).Nonempty) ∧ ∀ n, V n ≤ W n) := by
  classical
  by_cases hdisj : ∃ (n : ℕ) (V : U.Opens), IsAffineOpen V ∧ (V : Set U).Nonempty ∧
      ∀ x : U, x ∈ V → x ∉ W n
  · exact Or.inl hdisj
  refine Or.inr ?_
  have hmeet : ∀ (n : ℕ) (V : U.Opens), IsAffineOpen V → (V : Set U).Nonempty →
      ∃ x : U, x ∈ V ∧ x ∈ W n := by
    intro n V hV hVne
    by_contra hcon
    exact hdisj ⟨n, V, hV, hVne, fun x hx hxW => hcon ⟨x, hx, hxW⟩⟩
  have hstep : ∀ (n : ℕ) (V : U.Opens), IsAffineOpen V → (V : Set U).Nonempty →
      ∃ V' : U.Opens, IsAffineOpen V' ∧ (V' : Set U).Nonempty ∧ V' ≤ V ∧
        V' ≤ W (n + 1) := by
    intro n V hV hVne
    obtain ⟨x, hxV, hxW⟩ := hmeet (n + 1) V hV hVne
    obtain ⟨V', hV', hxV', hsub⟩ :=
      exists_isAffineOpen_mem_and_subset (x := x) (U := V ⊓ W (n + 1)) ⟨hxV, hxW⟩
    exact ⟨V', hV', ⟨x, hxV'⟩, fun y hy => (hsub hy).1, fun y hy => (hsub hy).2⟩
  choose! step hstepAff hstepNe hstepLe hstepW using hstep
  obtain ⟨V₀, hV₀, hxV₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := Classical.arbitrary U) (U := ⊤) trivial
  set V : ℕ → U.Opens := fun n => Nat.rec V₀ (fun m Vm => step m Vm) n with hVdef
  have hVsucc : ∀ n, V (n + 1) = step n (V n) := fun _ => rfl
  have hmain : ∀ n, IsAffineOpen (V n) ∧ (V n : Set U).Nonempty ∧ V n ≤ W n := by
    intro n
    induction n with
    | zero => exact ⟨hV₀, ⟨_, hxV₀⟩, by rw [hW0]; exact le_top⟩
    | succ m ih =>
      refine ⟨?_, ?_, ?_⟩
      · rw [hVsucc]; exact hstepAff m (V m) ih.1 ih.2.1
      · rw [hVsucc]; exact hstepNe m (V m) ih.1 ih.2.1
      · rw [hVsucc]; exact hstepW m (V m) ih.1 ih.2.1
  refine ⟨V, antitone_nat_of_succ_le fun n => ?_, fun n => (hmain n).1, fun n => (hmain n).2.1,
    fun n => (hmain n).2.2⟩
  rw [hVsucc]
  exact hstepLe n (V n) (hmain n).1 (hmain n).2.1

end AlgebraicGeometry

end

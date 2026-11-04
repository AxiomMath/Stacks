module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Products
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Specialization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeInvolutionRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsDenseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.CategoryTheory.Limits.KernelPairRestriction
public import StacksFrontier.Examples.Scheme.AxesNegation
public import StacksFrontier.Examples.Spaces.AffineOverSpaceNoImmersion
public import StacksFrontier.Topology.Compact.PuncturedDenseOpen

/-!
# A quasi-compact quasi-separated algebraic space with no quasi-compact dense open subscheme

Over a field `k` of characteristic different from two, let
`U = Spec k[x, z₁, z₂, …]/(x zᵢ, zᵢ zⱼ)` be the line `x` glued to countably many axes `zᵢ`
at a common origin, and let `a : U ⟶ U` be the reflection `x ↦ -x`, which fixes every axis.
The reflection acts freely on the punctured line `D(x)`, so

  `R = U ⨿ D(x) ⇉ U`

is an étale equivalence relation (the diagonal together with the graph of `a` over `D(x)`),
and the quotient `X = U/R` is an algebraic space. It is quasi-compact because `U` is affine
and quasi-separated because `R` is quasi-compact.

`X` has no quasi-compact dense open subscheme. An open subscheme `V ⊆ X` with dense image
pulls back to a quasi-compact dense open `W ⊆ U`, which must contain the origin: the
punctured spectrum of the axes has no quasi-compact dense open, since such an open would meet
only finitely many axes while being dense (Stacks 086H). But then the restriction of `R` over
`W` is an immersion into `W ⨯ W`, while the generic point of the punctured line and the
origin, which lie in different summands of `R` and so do not specialize there, do specialize
in `W ⨯ W` because the reflection fixes the origin. That contradicts the fact that an
immersion is an embedding.

## Main definitions

* `Stacks.Examples.AxesReflection.chart`: the scheme `U`.
* `Stacks.Examples.AxesReflection.puncturedLine`: the open `D(x) ⊆ U`.
* `Stacks.Examples.AxesReflection.reflection`: the reflection `a`.
* `Stacks.Examples.AxesReflection.relationScheme`: the relation `R = U ⨿ D(x)`.
* `Stacks.Examples.AxesReflection.graphGenericPoint` and
  `Stacks.Examples.AxesReflection.diagonalOrigin`: the two points of `R` that witness the
  failure of immersion.

## Main results

* `exists_quasiCompact_quasiSeparated_without_quasiCompact_dense_open_subscheme`, in the
  namespace `Stacks.Examples.AxesReflection`: Stacks 087I.

## Implementation notes

An open subscheme of an algebraic space is expressed as an open immersion from a
representable presheaf (Stacks 02YU); its density is density of the image on the point set of
Stacks 03BU, and its quasi-compactness is compactness of the underlying space of the
representing object.

The Stacks proof of 087I cites Stacks 02WW for the quotient being an algebraic space, and 02WW
rests on the effective descent along the covering sieves of the big fppf site at the
monomorphisms locally of finite type which Stacks 0265 consumes; that is
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. The site
itself is produced inside the proof, by `AlgebraicGeometry.BigFppfSite.exists_containing`.

The field is `ULift ℚ` so that the resulting scheme lives in a prescribed universe; any
field of characteristic different from two would do.

## References

* [Stacks Project, Tag 087I](https://stacks.math.columbia.edu/tag/087I)
* [Stacks Project, Tag 086H](https://stacks.math.columbia.edu/tag/086H)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.OpenInvolution

universe u

namespace Stacks.Examples.AxesReflection

attribute [local instance] AlgebraicGeometry.Space.pointTopology

/-! ### The data of the example -/

/-- The ground field of the example: the rationals, lifted into the ambient universe. Any
field of characteristic different from two would do. -/
abbrev groundField : Type u := ULift.{u} ℚ

/-- The ground field has characteristic different from two: `2 ≠ 0` in `groundField`. -/
instance : NeZero (2 : groundField.{u}) := ⟨by
  intro h
  have hh := congrArg ULift.down h
  change (2 : ℚ) = 0 at hh
  norm_num at hh⟩

/-- The chart of the example: the line `x` glued to countably many axes `zᵢ` at a common
origin, that is `Spec k[x, z₁, z₂, …]/(x zᵢ, zᵢ zⱼ)`. The line is the `0`-th axis of
`Stacks.Examples.puncturedAxisRing`. -/
noncomputable abbrev chart : Scheme.{u} := axesScheme groundField.{u}

/-- The punctured line inside the chart: the basic open of the coordinate `x`. -/
noncomputable abbrev puncturedLine : chart.{u}.Opens := axisOpen groundField.{u} 0

/-- The reflection `x ↦ -x` of the line, fixing every axis. -/
noncomputable abbrev reflection : chart.{u} ⟶ chart.{u} := axesReflection groundField.{u} 0

/-- The relation scheme `R = U ⨿ D(x)` of the example: the diagonal summand together with the
graph summand. -/
noncomputable abbrev relationScheme : Scheme.{u} :=
  OpenInvolution.relationScheme puncturedLine.{u}

/-- The target projection `R ⟶ U`. -/
noncomputable abbrev target : relationScheme.{u} ⟶ chart.{u} :=
  OpenInvolution.relationTarget puncturedLine.{u}

/-- The source projection `R ⟶ U`. -/
noncomputable abbrev source : relationScheme.{u} ⟶ chart.{u} :=
  OpenInvolution.relationSource puncturedLine.{u} reflection.{u}

/-- **The relation of the example is an étale equivalence relation.** The reflection is an
involution which preserves the punctured line and acts freely on it, away from characteristic
two. -/
theorem isEtaleEquivalenceRelation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (preRelation puncturedLine.{u} reflection.{u}) :=
  isEtaleEquivalenceRelation_preRelation puncturedLine reflection
    (axesReflection_comp_self groundField.{u} 0)
    (axisOpenReflection groundField.{u} 0)
    (axisOpenReflection_comp_ι groundField.{u} 0)
    fun f hf => isEmpty_of_eq_comp_axesReflection groundField.{u} 0 f hf

/-! ### The two points witnessing the failure of immersion -/

/-- The generic point of the punctured line, in the graph summand of the relation scheme. -/
noncomputable def graphGenericPoint : relationScheme.{u} :=
  (coprod.inr : puncturedLine.{u}.toScheme ⟶ relationScheme.{u})
    ⟨axisPoint groundField.{u} 0,
      (PrimeSpectrum.mem_basicOpen _ _).2
        (axisQuotientMap_X_notMem_axisPoint groundField.{u} 0)⟩

/-- The origin, in the diagonal summand of the relation scheme. -/
noncomputable def diagonalOrigin : relationScheme.{u} :=
  (coprod.inl : chart.{u} ⟶ relationScheme.{u}) (axisOrigin groundField.{u})

/-- Applying a composite of scheme morphisms to a point, with the composite rewritten. -/
private theorem comp_apply_eq_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← e]
  rfl

/-- The target projection sends `graphGenericPoint` to the generic point of the `0`-th axis. -/
theorem target_graphGenericPoint :
    target.{u} graphGenericPoint.{u} = axisPoint groundField.{u} 0 :=
  comp_apply_eq_of_comp_eq _ _ (OpenInvolution.inr_comp_relationTarget puncturedLine.{u}) _

/-- The target projection sends `diagonalOrigin` to the origin of the chart. -/
theorem target_diagonalOrigin :
    target.{u} diagonalOrigin.{u} = axisOrigin groundField.{u} :=
  comp_apply_eq_of_comp_eq _ _ (OpenInvolution.inl_comp_relationTarget puncturedLine.{u}) _

/-- Downstairs the two points specialize: the generic point of the line specializes to the
origin. -/
theorem specializes_target :
    target.{u} graphGenericPoint.{u} ⤳ target.{u} diagonalOrigin.{u} := by
  rw [target_graphGenericPoint, target_diagonalOrigin]
  exact axisPoint_specializes_axisOrigin groundField.{u} 0

/-- Upstairs they do not: they lie in different summands of a coproduct, and no point of the
right summand specializes to a point of the left one. -/
theorem not_specializes_graphGenericPoint_diagonalOrigin :
    ¬ graphGenericPoint.{u} ⤳ diagonalOrigin.{u} :=
  AffineOverAlgebraicSpace.not_specializes_coprod_inr_inl _ _

/-- **The two points specialize in the self-product of the chart.** On the graph summand the
pair `(source, target)` is the inclusion of the punctured line followed by
`(reflection, id)`, and on the diagonal summand it is the diagonal; the reflection fixes the
origin, so the two agree there, and the generic point of the line specializes to the
origin. -/
theorem specializes_prod_lift :
    (prod.lift source.{u} target.{u}) graphGenericPoint.{u} ⤳
      (prod.lift source.{u} target.{u}) diagonalOrigin.{u} := by
  set dg : chart.{u} ⟶ chart.{u} ⨯ chart.{u} := prod.lift (𝟙 _) (𝟙 _) with hdg
  set rf : chart.{u} ⟶ chart.{u} ⨯ chart.{u} := prod.lift reflection.{u} (𝟙 _) with hrf
  have hinr : (coprod.inr : puncturedLine.{u}.toScheme ⟶ relationScheme.{u}) ≫
      prod.lift source.{u} target.{u} = puncturedLine.{u}.ι ≫ rf := by
    refine prod.hom_ext ?_ ?_
    · rw [hrf]
      simp only [Category.assoc, prod.lift_fst, OpenInvolution.inr_comp_relationSource]
    · rw [hrf]
      simp only [Category.assoc, prod.lift_snd, OpenInvolution.inr_comp_relationTarget,
        Category.comp_id]
  have hinl : (coprod.inl : chart.{u} ⟶ relationScheme.{u}) ≫
      prod.lift source.{u} target.{u} = dg := by
    refine prod.hom_ext ?_ ?_
    · rw [hdg]
      simp only [Category.assoc, prod.lift_fst, OpenInvolution.inl_comp_relationSource]
    · rw [hdg]
      simp only [Category.assoc, prod.lift_snd, OpenInvolution.inl_comp_relationTarget]
  have hx : (prod.lift source.{u} target.{u}) graphGenericPoint.{u} =
      rf (axisPoint groundField.{u} 0) := by
    exact (comp_apply_eq_of_comp_eq _ _ hinr _)
  have hy : (prod.lift source.{u} target.{u}) diagonalOrigin.{u} =
      dg (axisOrigin groundField.{u}) := by
    exact comp_apply_eq_of_comp_eq _ _ hinl _
  have hfix : axesOriginPoint groundField.{u} ≫ rf =
      axesOriginPoint groundField.{u} ≫ dg := by
    refine prod.hom_ext ?_ ?_
    · rw [hrf, hdg]
      simp only [Category.assoc, prod.lift_fst, Category.comp_id]
      exact axesOriginPoint_comp_axesReflection groundField.{u} 0
    · rw [hrf, hdg]
      simp only [Category.assoc, prod.lift_snd, Category.comp_id]
  have horigin : rf (axisOrigin groundField.{u}) = dg (axisOrigin groundField.{u}) := by
    rw [← axesOriginPoint_closedPoint]
    exact (comp_apply_eq_of_comp_eq _ _ rfl _).symm.trans
      ((congrArg (fun m : Spec (.of groundField.{u}) ⟶ chart.{u} ⨯ chart.{u} =>
        m (IsLocalRing.closedPoint groundField.{u})) hfix).trans
        (comp_apply_eq_of_comp_eq _ _ rfl _))
  rw [hx, hy, ← horigin]
  exact (axisPoint_specializes_axisOrigin groundField.{u} 0).map rf.continuous

/-! ### A quasi-compact dense open of the chart contains the origin -/

/-- **A quasi-compact dense open of the chart contains the origin.** The punctured chart has
no quasi-compact dense open subset, by Stacks 086H, and the origin is a closed point. -/
theorem mem_range_of_isOpenImmersion_of_denseRange {W : Scheme.{u}} (i : W ⟶ chart.{u})
    (hi : IsOpenImmersion i) (hW : CompactSpace W) (hdense : Dense (Set.range i)) :
    axisOrigin groundField.{u} ∈ Set.range i :=
  have := hi
  have := hW
  TopologicalSpace.mem_of_isOpen_of_isCompact_of_dense _
    (puncturedAxisRing_has_no_quasiCompact_dense_open groundField.{u})
    i.isOpenEmbedding.isOpen_range (isCompact_range i.continuous) hdense
    (isClosed_axisOrigin groundField.{u})

/-- **The restriction of the relation to a quasi-compact dense open of the chart is not an
immersion.** Let `i : W ⟶ U` be an open immersion whose image contains the origin and let
`L = R ×_U W` be the restriction of the relation along the target projection. Then the
composite `L ⟶ R ⟶ U ⨯ U` is not an immersion.

The two points of `R` of `graphGenericPoint` and `diagonalOrigin` specialize under the target
projection and in `U ⨯ U`, but not in `R`; the target of the second is the origin, which lies
in the image of `i`. -/
theorem not_isImmersion_comp_prod_lift {W L : Scheme.{u}} (i : W ⟶ chart.{u})
    (hi : IsOpenImmersion i) (e : L ⟶ relationScheme.{u}) (p : L ⟶ W)
    (hsq : IsPullback e p target.{u} i)
    (horigin : axisOrigin groundField.{u} ∈ Set.range i) :
    ¬ IsImmersion (e ≫ prod.lift source.{u} target.{u}) :=
  have := hi
  not_isImmersion_comp_of_specializes_of_not_specializes
    (prod.lift source.{u} target.{u}) target.{u} i e p hsq
    graphGenericPoint diagonalOrigin specializes_target specializes_prod_lift
    not_specializes_graphGenericPoint_diagonalOrigin
    (by rw [target_diagonalOrigin]; exact horigin)

/-- The source projection of the relation is quasi-compact: the relation scheme is the
coproduct of the affine chart with the quasi-compact punctured line. -/
theorem quasiCompact_source : QuasiCompact source.{u} :=
  have := compactSpace_axisOpen groundField.{u} 0
  OpenInvolution.quasiCompact_relationSource puncturedLine.{u} reflection.{u}

/-! ### The algebraic space -/

section Site

variable (B : BigFppfSite.{u}) (hU : B.Contains chart.{u})
  (hR : B.Contains relationScheme.{u})

/-- The chart, as an object of a big fppf site over the terminal scheme. -/
noncomputable def chartObj : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal :=
  BigFppfOver.mk B _ B.contains_terminal hU (terminal.from chart.{u})

/-- The relation scheme, as an object of a big fppf site over the terminal scheme. -/
noncomputable def relationObj : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal :=
  BigFppfOver.mk B _ B.contains_terminal hR (terminal.from relationScheme.{u})

/-- The target projection, as a morphism of the site. -/
noncomputable def targetHom : relationObj B hR ⟶ chartObj B hU :=
  BigFppfOver.homMk B _ B.contains_terminal hU (terminal.from chart.{u}) target.{u}
    (terminal.hom_ext _ _)

/-- The source projection, as a morphism of the site. -/
noncomputable def sourceHom : relationObj B hR ⟶ chartObj B hU :=
  BigFppfOver.homMk B _ B.contains_terminal hU (terminal.from chart.{u}) source.{u}
    (terminal.hom_ext _ _)

/-- The pre-relation of the site attached to the two projections is the pre-relation of the
free involution. -/
theorem relation_eq_preRelation :
    Space.relation B (⊤_ Scheme.{u}) B.contains_terminal (sourceHom B hU hR)
        (targetHom B hU hR) =
      preRelation puncturedLine.{u} reflection.{u} := rfl

/-- The pre-relation of the site attached to the source and target projections is an étale
equivalence relation. -/
theorem isEtaleEquivalenceRelation_relation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.relation B (⊤_ Scheme.{u}) B.contains_terminal (sourceHom B hU hR)
        (targetHom B hU hR)) := by
  rw [relation_eq_preRelation]
  exact isEtaleEquivalenceRelation

/-- The algebraic space of the example: the quotient of the chart by the relation. -/
noncomputable abbrev space :
    (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf
    (BigFppfOver.topology B (⊤_ Scheme.{u}) B.contains_terminal) (Over.post B.inclusion)
    (Space.relation B (⊤_ Scheme.{u}) B.contains_terminal (sourceHom B hU hR)
      (targetHom B hU hR))).obj

/-- **The quotient is an algebraic space.** This is Stacks 02WW; the effective descent along the
covering sieves at the monomorphisms locally of finite type which Stacks 0265 consumes is
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. -/
theorem isAlgebraicSpace_space :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal (space B hU hR) :=
  have := isEtaleEquivalenceRelation_relation B hU hR
  have : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj
      (chartObj B hU)) := inferInstanceAs (IsAffine chart.{u})
  Space.isAlgebraicSpace_quotientSheaf_of_diagDescent B (⊤_ Scheme.{u}) B.contains_terminal
    (chartObj B hU) _
    (Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B (⊤_ Scheme.{u})
      B.contains_terminal)

/-- The presentation of the quotient by the chart and the relation, which is Stacks 02WV: the
relation is the kernel pair of the chart, and the chart is surjective and étale. -/
noncomputable def presentation :
    Space.Presentation B (⊤_ Scheme.{u}) B.contains_terminal (space B hU hR)
      (isAlgebraicSpace_space B hU hR) :=
  have := isEtaleEquivalenceRelation_relation B hU hR
  Space.quotientPresentation B (⊤_ Scheme.{u}) B.contains_terminal (sourceHom B hU hR)
    (targetHom B hU hR) (isAlgebraicSpace_space B hU hR)

/-- **The quotient is quasi-compact**: its chart is an affine scheme. -/
theorem isQuasiCompactSpace_space :
    Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal (space B hU hR) :=
  Space.isQuasiCompactSpace_of_presentation B (⊤_ Scheme.{u}) B.contains_terminal
    (isAlgebraicSpace_space B hU hR) (presentation B hU hR)
    (inferInstanceAs (CompactSpace chart.{u}))

/-- **The quotient is quasi-separated**: its chart is an affine scheme, hence
quasi-separated, and the source projection of the relation is quasi-compact because the
relation scheme is the coproduct of two quasi-compact schemes. -/
theorem isAbsolutelyQuasiSeparated_space :
    Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal
      B.contains_terminal (space B hU hR) :=
  Space.isAbsolutelyQuasiSeparated_of_presentation B (⊤_ Scheme.{u}) B.contains_terminal
    (isAlgebraicSpace_space B hU hR) (presentation B hU hR) B.contains_terminal
    (inferInstanceAs (QuasiSeparatedSpace chart.{u})) quasiCompact_source

/-- **The quotient has no quasi-compact dense open subscheme.**

Such a subscheme would base-change along the chart to a quasi-compact dense open `W` of the
chart, which must contain the origin because the punctured chart has no quasi-compact dense
open (Stacks 086H). The restriction of the relation over `W` is then an immersion into the
self-product of the chart, which
`Stacks.Examples.AxesReflection.not_isImmersion_comp_prod_lift` forbids. -/
theorem not_exists_compactSpace_isOpenImmersion_dense :
    ¬ ∃ (V : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)
        (f : yoneda.obj V ⟶ space B hU hR),
      CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj V) ∧
      Space.IsOpenImmersion B (⊤_ Scheme.{u}) B.contains_terminal f ∧
      Dense (Set.range (Space.pointsMap B (⊤_ Scheme.{u}) B.contains_terminal
        (yoneda.obj V) f)) := by
  rintro ⟨V, f, hV, hf, hdense⟩
  have hF := isAlgebraicSpace_space B hU hR
  set T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal with hT
  set P := presentation B hU hR with hPdef
  set i : hf.rep.pullback P.toSpace ⟶ P.U := hf.rep.snd P.toSpace with hidef
  set g : hf.rep.pullback P.toSpace ⟶ V := hf.rep.fst' P.toSpace with hgdef
  have hsq : IsPullback (yoneda.map i) (yoneda.map g) P.toSpace f :=
    (hf.rep.isPullback' P.toSpace).flip
  have hiopen : IsOpenImmersion (T.map i) := hf.property_snd P.toSpace
  have hqc := Space.presheaf_quasiCompact_toSpace_of_presentation B (⊤_ Scheme.{u})
    B.contains_terminal hF P quasiCompact_source
  have hgqc : QuasiCompact (T.map g) := hqc.property f (yoneda.map i) g hsq
  have := hV
  have := hgqc
  have hWcompact : CompactSpace (T.obj (hf.rep.pullback P.toSpace)) :=
    QuasiCompact.compactSpace_of_compactSpace (T.map g)
  have hWdense := Space.denseRange_toScheme_map_of_isPullback B (⊤_ Scheme.{u})
    B.contains_terminal i g P.toSpace f hsq P.etale hdense
  have := hiopen
  have := hWcompact
  have horigin : axisOrigin groundField.{u} ∈ Set.range (T.map i) :=
    mem_range_of_isOpenImmersion_of_denseRange (T.map i) hiopen hWcompact hWdense
  obtain ⟨j, hji, hjg⟩ := exists_isKernelPair_restrict_of_isKernelPair
    P.target P.source P.toSpace P.isPullback.flip i g f hsq
  have hpres : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B (⊤_ Scheme.{u}) B.contains_terminal
  have hpair : IsImmersion (T.map (pullback.fst P.target i) ≫
      prod.lift (T.map P.source) (T.map P.target)) :=
    isImmersion_comp_prod_lift_of_isPullback (T.map P.target) (T.map P.source) hiopen
      (hjg.map T) (by rw [← Functor.map_comp, ← Functor.map_comp, hji])
      (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  exact not_isImmersion_comp_prod_lift (T.map i) hiopen (T.map (pullback.fst P.target i))
    (T.map (pullback.snd P.target i)) ((IsPullback.of_hasPullback P.target i).map T)
    horigin hpair

end Site

/-! ### Stacks 087I -/

/-- **Stacks 087I.** There exists a quasi-compact and quasi-separated algebraic space which
does not contain a quasi-compact dense open subscheme.

The space is the quotient of `Spec k[x, z₁, z₂, …]/(x zᵢ, zᵢ zⱼ)` by the reflection
`x ↦ -x` over the punctured line, for `k` of characteristic different from two.

The space is an algebraic space by Stacks 02WW, through Stacks 0265 and the effective descent
along the covering sieves at the monomorphisms locally of finite type that it consumes. The big
fppf site carrying it is produced inside the proof, and so is existentially quantified. -/
@[stacks 087I "a quasi-compact quasi-separated algebraic space with no quasi-compact dense open \
subscheme: the quotient of a line glued to countably many axes by a reflection"]
theorem exists_quasiCompact_quasiSeparated_without_quasiCompact_dense_open_subscheme :
    ∃ (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
      (F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F),
      Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ F ∧
      Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ F ∧
      ¬ ∃ (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (f : yoneda.obj V ⟶ F),
        CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) ∧
        Space.IsOpenImmersion B (⊤_ Scheme.{u}) hZ f ∧
        Dense (Set.range (Space.pointsMap B (⊤_ Scheme.{u}) hZ (yoneda.obj V) f)) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing {chart.{u}, relationScheme.{u}}
  have hU : B.Contains chart.{u} := hB _ (by simp)
  have hR : B.Contains relationScheme.{u} := hB _ (by simp)
  exact ⟨B, B.contains_terminal, space B hU hR,
    isAlgebraicSpace_space B hU hR,
    isQuasiCompactSpace_space B hU hR,
    isAbsolutelyQuasiSeparated_space B hU hR,
    not_exists_compactSpace_isOpenImmersion_dense B hU hR⟩

end Stacks.Examples.AxesReflection

end

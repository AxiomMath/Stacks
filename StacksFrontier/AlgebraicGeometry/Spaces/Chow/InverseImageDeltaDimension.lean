module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionAntitone
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The δ-dimension of an inverse image

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a morphism over the base
of relative dimension `r`. Along `f` the δ-dimension of a closed set of points grows by at most
`r`: the induced dimension function at a point `u` of `X` is the one at `f u` plus the
transcendence degree of `u` over `f u`, and that degree is bounded by the relative dimension.

This bounds the δ-dimension of the two inverse images occurring in Stacks 0EPB. For a closed
subspace `Z ⊆ Y` with `dim_δ(Z) ≤ k` the scheme-theoretic inverse image satisfies
`dim_δ(f^{-1}(Z)) ≤ k + r`, and for a coherent `𝒪_Y`-module `F` whose support has
`dim_δ ≤ k` the support of the pullback `f^*F` satisfies `dim_δ(Supp(f^*F)) ≤ k + r`.

## Main results

* `AlgebraicGeometry.Space.deltaDimensionClosed_le_coe_iff`: the δ-dimension of a closed set of
  points is at most `k` exactly when the induced dimension function is at most `k` at every
  point of that set.
* `AlgebraicGeometry.Space.inducedDimensionValue_le_add_of_hasRelativeDimension`: along a
  morphism of relative dimension `r` the induced dimension function grows by at most `r`.
* `AlgebraicGeometry.Space.deltaDimensionClosed_preimage_le`: the δ-dimension of the inverse
  image of a closed set of points of `Y` is at most `r` more than that of the set.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_preimage_le`: the dimension clause of
  **Stacks 0EPB, part (1)**, for the scheme-theoretic inverse image of a closed subspace.
* `AlgebraicGeometry.Space.deltaDimensionClosed_supportOfSheaf_modulePullback_le`:
  the dimension clause of **Stacks 0EPB, part (2)**, for the support of the pullback of a
  coherent module.
* `AlgebraicGeometry.Space.transcendenceDegreeAt_le_of_hasRelativeDimensionAt`: the
  transcendence degree of a point over its image is at most the relative dimension there.
* `AlgebraicGeometry.Space.exists_hasFiberLocalRingDimension`: every point of the source of a
  morphism of algebraic spaces has a dimension of the local ring of its fibre there.

## Implementation notes

The characterization of the bound `dim_δ(T) ≤ k` by the pointwise bound is what both parts
reduce to. The δ-dimension of Stacks 0EDX is the supremum of the induced dimension function
over the generic points of the irreducible components of `T`, so the bound at every point of
`T` is formally stronger; the two agree because every point of `T` is a specialization of the
generic point of some component and the induced dimension function drops along a nontrivial
specialization, which is `AlgebraicGeometry.Space.lt_inducedDimensionValue_of_specializes`.

The growth bound is the pointwise formula of Stacks 0EDN on both sides, together with the
additivity of the transcendence degree along a composite, part (3) of Stacks 04NR. The
transcendence degree at a point is bounded by the relative dimension there because by
Stacks 04NQ the latter is the former plus the dimension of the local ring of the fibre; that
dimension is a value of `ringKrullDim` on a nonzero local ring, hence exists in `ℕ∞`, which is
`AlgebraicGeometry.Space.exists_hasFiberLocalRingDimension`.

Flatness of `f` is not used: the source assumes `f` flat of relative dimension `r`, and the
hypothesis is retained so that the statements are the ones of Stacks 0EPB, but the inequality
holds for any morphism of relative dimension `r`. Flatness is what upgrades the inequality to
the equality of Stacks 0EP5, which is not formed here.

For the support of a pullback only the containment `Supp(f^*F) ⊆ |f|^{-1} Supp(F)` is needed,
and that is `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_subset`; the equality of
Stacks 07TZ, part (3), is not required. The containment and the closedness of the support ask
for `F` to be of finite type on the small étale site, which a coherent module is by
`AlgebraicGeometry.Space.isFiniteTypeOnSite_of_isCoherentOnSite`; that lemma is stated for
modules whose coefficient universe is the universe of the site, so the support bound is stated
there too. Only the coherence-on-the-site half of Stacks 07UA is asked for, which is the half
that is used; `AlgebraicGeometry.Space.IsCoherent` extends it, so a coherent module satisfies
the hypothesis by instance resolution.

**The cycle identities of Stacks 0EPB are proved elsewhere.** The two bounds below are the
dimension clauses of the two parts; the full statements, each dimension bound together with its
cycle identity, are `AlgebraicGeometry.Space.flatPullback_closedSubspaceCycle_preimage` and
`AlgebraicGeometry.Space.flatPullback_associatedCycle_modulePullback` in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle`, which carry the tag.

## References

* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 04NQ](https://stacks.math.columbia.edu/tag/04NQ)
* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The local ring of the fibre of a morphism of germs of schemes at its distinguished point has
*some* Krull dimension in `ℕ∞`: a representative of the germ exhibits that local ring, which is
nonzero, so its `ringKrullDim` is not `⊥`. -/
private theorem exists_germHasFiberLocalRingDimension {X Y : GermOfScheme.{u}}
    (f : MorphismOfGerms X Y) : ∃ d : ℕ∞, HasFiberLocalRingDimension d f := by
  obtain ⟨g, hg⟩ := MorphismOfGerms.exists_rep f
  have hne : ringKrullDim ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
      (g.hom.asFiber ⟨X.point, g.mem_source⟩)) ≠ ⊥ := fun hbot => by
    simpa [hbot] using ringKrullDim_nonneg_of_nontrivial
      (R := (g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
        (g.hom.asFiber ⟨X.point, g.mem_source⟩))
  exact ⟨_, g, hg, (WithBot.coe_unbot _ hne).symm⟩

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Every point of the source of a morphism of algebraic spaces over `S` has a dimension of the
local ring of its fibre there: the invariant of Stacks 04NM is read on one pointed étale chart,
where it is a value of `ringKrullDim` on a nonzero local ring. -/
theorem exists_hasFiberLocalRingDimension (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : points B S hS F) :
    ∃ e : ℕ∞, HasFiberLocalRingDimension e B S hS hF hG f x := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hF hG f x
  obtain ⟨e, he⟩ := exists_germHasFiberLocalRingDimension
    (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS))
  exact ⟨e, (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
    (@_root_.AlgebraicGeometry.HasFiberLocalRingDimension.{u} e)
    (fiberLocalRingDimension_isEtaleLocalOnSourceAndTarget e) f x c).2 he⟩

/-- The transcendence degree of a point over its image under a morphism of algebraic spaces
locally of finite type is at most the relative dimension of the morphism there: by Stacks 04NQ
the relative dimension is the dimension of the local ring of the fibre plus the transcendence
degree. -/
theorem transcendenceDegreeAt_le_of_hasRelativeDimensionAt (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f)
    (x : points B S hS F) (d t : ℕ∞) (hd : HasRelativeDimensionAt d B S hS f x)
    (ht : HasTranscendenceDegreeAt B S hS f x t) : t ≤ d := by
  obtain ⟨e, he⟩ := exists_hasFiberLocalRingDimension B S hS hF hG f x
  exact relativeDimensionAt_eq_fiberLocalRingDimension_add_transcendenceDegreeAt
    B S hS hF hG f x hf d e t hd he ht ▸ le_add_self

/-- The support of a module coherent on the small étale site of an algebraic space is closed: a
coherent module is of finite type, and the support of a module of finite type is closed by
Stacks 07TZ. -/
theorem isClosed_supportOfSheaf_of_isCoherentOnSite (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) [SheafOfModules.IsCoherentOnSite M] :
    IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) :=
  have := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X M
  isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 M

/-- The support of the pullback of a module coherent on the small étale site is closed: the
pullback of a module of finite type is of finite type by Stacks 03DO, and the support of a
module of finite type is closed by Stacks 07TZ. -/
theorem isClosed_supportOfSheaf_modulePullback_of_isCoherentOnSite
    {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2)
    [SheafOfModules.IsCoherentOnSite M] :
    IsClosed (supportOfSheaf B S hS X'.1
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj M))) :=
  isClosed_supportOfSheaf_modulePullback B S hS g M
    (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X M)

end Space

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### The δ-dimension bound, pointwise -/

/-- The δ-dimension of a closed set of points of a good algebraic space is at most `k` exactly
when the induced dimension function is at most `k` at every point of the set.

One direction is immediate: the generic point of an irreducible component of the set lies in the
set. For the other, every point of the set is a specialization of the generic point of some
component, and the induced dimension function drops along a nontrivial specialization. -/
theorem deltaDimensionClosed_le_coe_iff (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T) (k : ℤ) :
    deltaDimensionClosed D sX hX T hT ≤ (k : EInt) ↔
      ∀ t ∈ T, inducedDimensionValue D.site D.base D.base_mem D.delta sX t ≤ k := by
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  have _hTsober : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  have hval : deltaDimensionClosed D sX hX T hT =
      ⨆ Z : irreducibleComponents T,
        (inducedDimensionValue D.site D.base D.base_mem D.delta sX Z.2.1.genericPoint.1 :
          EInt) := rfl
  rw [hval]
  refine ⟨fun hbound t ht => ?_,
    fun h => iSup_le fun Z => WithBotTop.coe_le_coe.mpr (h _ Z.2.1.genericPoint.2)⟩
  have hanti : ∀ ⦃x y : points D.site D.base D.base_mem X⦄, x ⤳ y → x ≠ y →
      inducedDimensionValue D.site D.base D.base_mem D.delta sX y <
        inducedDimensionValue D.site D.base D.base_mem D.delta sX x :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2
  obtain ⟨W, hW, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({(⟨t, ht⟩ : T)} : Set T))
      (isIrreducible_iff_closure.mpr isIrreducible_singleton)
  have hη : IsGenericPoint hW.1.genericPoint W := by
    simpa [isClosed_of_mem_irreducibleComponents W hW] using
      hW.1.isGenericPoint_genericPoint_closure
  have hηle :
      inducedDimensionValue D.site D.base D.base_mem D.delta sX hW.1.genericPoint.1 ≤ k :=
    WithBotTop.coe_le_coe.mp ((le_iSup _ (⟨W, hW⟩ : irreducibleComponents T)).trans hbound)
  by_cases hηt : hW.1.genericPoint = (⟨t, ht⟩ : T)
  · simpa [hηt] using hηle
  · have hlt : inducedDimensionValue D.site D.base D.base_mem D.delta sX t <
        inducedDimensionValue D.site D.base D.base_mem D.delta sX hW.1.genericPoint.1 :=
      hanti ((hη.specializes (hsub (subset_closure rfl))).map continuous_subtype_val)
        (fun h => hηt (Subtype.ext h))
    omega

/-- Along a morphism `f : X ⟶ Y` of good algebraic spaces over the base which has relative
dimension `r`, the induced dimension function at a point `u` of `X` is at most `r` more than the
induced dimension function at the image of `u`.

By the pointwise formula of Stacks 0EDN both values are the value of `δ` at the common image in
the base plus a transcendence degree, and the two degrees differ by the transcendence degree of
`u` over its image under `f`, by part (3) of Stacks 04NR; that degree is at most `r` because
`f` has relative dimension `r`. -/
theorem inducedDimensionValue_le_add_of_hasRelativeDimension (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (u : points D.site D.base D.base_mem X) :
    inducedDimensionValue D.site D.base D.base_mem D.delta sX u ≤
      inducedDimensionValue D.site D.base D.base_mem D.delta sY
        (pointsMap D.site D.base D.base_mem X f u) + (r : ℤ) := by
  have hfft : IsLocallyOfFiniteType D.site D.base D.base_mem f :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f sY
      (hbase ▸ hX.2.2)
  obtain ⟨a, ha⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem f hfft u
  obtain ⟨b, hb⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem sY hY.2.2
    (pointsMap D.site D.base D.base_mem X f u)
  have hcomp : HasTranscendenceDegreeAt D.site D.base D.base_mem sX u ((a + b : ℕ) : ℕ∞) := by
    rw [← hbase, Nat.cast_add]
    exact hasTranscendenceDegreeAt_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace
      f sY u (a : ℕ∞) (b : ℕ∞) ha hb
  have hXval := inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace
    D.delta sX hX.2.2 u ((a + b : ℕ) : ℕ∞) hcomp
  have hYval := inducedDimensionValue_eq D.site D.base D.base_mem hY.1 D.isAlgebraicSpace
    D.delta sY hY.2.2 (pointsMap D.site D.base D.base_mem X f u) (b : ℕ∞) hb
  have himg : pointsMap D.site D.base D.base_mem X sX u =
      pointsMap D.site D.base D.base_mem Y sY
        (pointsMap D.site D.base D.base_mem X f u) := by
    rw [← hbase, pointsMap_comp_apply]
  have har : a ≤ r :=
    Nat.cast_le.mp (transcendenceDegreeAt_le_of_hasRelativeDimensionAt D.site D.base D.base_mem
      hX.1 hY.1 f hfft u (r : ℕ∞) (a : ℕ∞) (hr u) ha)
  rw [hXval, hYval, himg]
  simp only [ENat.toNat_natCast]
  omega

/-- The δ-dimension of the inverse image of a closed set of points of `Y` along a morphism
`f : X ⟶ Y` of good algebraic spaces over the base of relative dimension `r` is at most `r` more
than the δ-dimension of that set. -/
theorem deltaDimensionClosed_preimage_le (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (T : Set (points D.site D.base D.base_mem Y)) (hT : IsClosed T) (k : ℤ)
    (hTk : deltaDimensionClosed D sY hY T hT ≤ (k : EInt))
    (T' : Set (points D.site D.base D.base_mem X))
    (hT' : IsClosed T')
    (hsub : T' ⊆ pointsMap D.site D.base D.base_mem X f ⁻¹' T) :
    deltaDimensionClosed D sX hX T' hT' ≤ ((k + (r : ℤ) : ℤ) : EInt) := by
  refine (deltaDimensionClosed_le_coe_iff D sX hX T' hT' (k + (r : ℤ))).2 fun t ht => ?_
  have hbound := (deltaDimensionClosed_le_coe_iff D sY hY T hT k).1 hTk _ (hsub ht)
  have hgrow := inducedDimensionValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr t
  omega

/-! ### The two dimension bounds of Stacks 0EPB -/

/-- **Stacks 0EPB, part (1), dimension bound.** In Situation 0EDT let `X/B` and `Y/B` be good and
let `f : X ⟶ Y` be a morphism over the base which is flat of relative dimension `r`. If
`Z ⊆ Y` is a closed subspace with `dim_δ(Z) ≤ k`, then its scheme-theoretic inverse image
satisfies `dim_δ(f^{-1}(Z)) ≤ k + r`. -/
theorem deltaDimensionSubspace_preimage_le (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (_hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (k : ℤ) (Z : Subfunctor Y)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z)
    (hZk : deltaDimensionSubspace D sY hY Z hZ ≤ (k : EInt)) :
    deltaDimensionSubspace D sX hX (Z.preimage f)
        (isClosedSubspace_preimage D.site D.base D.base_mem f Z hY.1 hX.1 hZ) ≤
      ((k + (r : ℤ) : ℤ) : EInt) :=
  deltaDimensionClosed_preimage_le D sX hX sY hY f hbase r hr
    (subspacePointSet D.site D.base D.base_mem Y Z) _ k hZk _ _
    (subspacePointSet_preimage D.site D.base D.base_mem f Z).le

/-- **Stacks 0EPB, part (2), support dimension bound.** In Situation 0EDT let `X/B` and `Y/B` be
good and let `f : X ⟶ Y` be a morphism over the base which is flat of relative dimension `r`. If
`F` is a coherent `𝒪_Y`-module with `dim_δ(Supp(F)) ≤ k`, then its pullback satisfies
`dim_δ(Supp(f^*F)) ≤ k + r`. -/
theorem deltaDimensionClosed_supportOfSheaf_modulePullback_le (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (_hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    [SheafOfModules.IsCoherentOnSite M] (k : ℤ)
    (hMk : deltaDimensionClosed D sY hY
        (supportOfSheaf D.site D.base D.base_mem Y ((SheafOfModules.toSheaf _).obj M))
        (isClosed_supportOfSheaf_of_isCoherentOnSite D.site D.base D.base_mem
          ⟨Y, hY.1⟩ M) ≤
      (k : EInt)) :
    deltaDimensionClosed D sX hX
        (supportOfSheaf D.site D.base D.base_mem X ((SheafOfModules.toSheaf _).obj
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f :
              (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).obj M)))
        (isClosed_supportOfSheaf_modulePullback_of_isCoherentOnSite D.site D.base D.base_mem
          (ObjectProperty.homMk f :
            (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩) M) ≤
      ((k + (r : ℤ) : ℤ) : EInt) :=
  deltaDimensionClosed_preimage_le D sX hX sY hY f hbase r hr _ _ k hMk _ _
    (supportOfSheaf_modulePullback_subset D.site D.base D.base_mem
      (ObjectProperty.homMk f :
        (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩) M
      (isFiniteTypeOnSite_of_isCoherentOnSite D.site D.base D.base_mem ⟨Y, hY.1⟩ M))

end AlgebraicGeometry.Space

end

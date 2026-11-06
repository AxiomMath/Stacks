module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.Codimension

/-!
# Dimension over a Jacobson base

Let `B` carry the standing datum of Situation 0EDT, assume in addition that `B` is Jacobson and
that its dimension function `δ` vanishes at every closed point of `|B|`, and let `X/B` be good.
**Stacks 0EDW** says that for an integral closed subspace `Z ⊆ X` with generic point `ξ ∈ |Z|`
the five numbers `δ_{X/B}(ξ)`, `dim |Z|`, `codim({z}, |Z|)` for `z ∈ |Z|` closed, the dimension
of the local ring of `Z` at such a `z`, and the dimension of the étale local ring of `Z` at a
geometric point above such a `z`, all agree; the first of them is a nonnegative integer.

The δ-dimension of `Z` is `AlgebraicGeometry.Space.deltaDimension`, the value of `δ_{X/B}` at
the generic point of `|Z|`, so part (1) of the source is the right-hand side of each of the
displayed equalities. Topological and local-ring dimensions take values in `ℕ∞` and in
`WithBot ℕ∞`, so each part states that the integer is nonnegative and equals the dimension
after conversion by `Int.toNat`, which is then lossless.

## Main definitions

* `AlgebraicGeometry.Space.subspaceDeltaDimensionFunction`: the dimension function of `|X|`
  pulled back along the closed embedding `|Z| → |X|`, a dimension function on `|Z|`.

## Main results

* `AlgebraicGeometry.Space.deltaDimension_eq_inducedDimensionValue`: part (1), the common value
  is `δ_{X/B}` at the generic point.
* `AlgebraicGeometry.Space.codimension_singleton_eq_deltaDimension`: parts (1) and (3), the
  codimension of a closed point of `|Z|`.
* `AlgebraicGeometry.Space.topologicalKrullDim_points_eq_deltaDimension`: parts (1) and (2), the
  dimension of `|Z|`.
* `AlgebraicGeometry.Space.localRingDimension_eq_deltaDimension`: parts (1) and (4), the
  dimension of the local ring of `Z` at a closed point.
* `AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_eq_deltaDimension`: parts (1) and (5),
  the dimension of the étale local ring of `Z` at a geometric point above a closed point.
* `AlgebraicGeometry.Space.deltaDimension_nonneg`: the common value is nonnegative.
* `AlgebraicGeometry.Space.subspaceDeltaDimensionFunction_eq_deltaValue`: the underlying function
  of `AlgebraicGeometry.Space.subspaceDeltaDimensionFunction` is `δ_{Z/B}`.

## References

* [Stacks Project, Tag 0EDW](https://stacks.math.columbia.edu/tag/0EDW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Topological preliminaries -/

/-- A closed embedding carries an immediate specialization to an immediate specialization. -/
private theorem isImmediateSpecialization_map_of_isClosedEmbedding {A C : Type*}
    [TopologicalSpace A] [TopologicalSpace C] {e : A → C} (he : Topology.IsClosedEmbedding e)
    {x y : A} (h : IsImmediateSpecialization x y) :
    IsImmediateSpecialization (e x) (e y) :=
  h.map_of_isClosedEmbedding he

/-- The pullback of a dimension function along a closed embedding. -/
private def dimensionFunctionComap {A C : Type*} [TopologicalSpace A] [TopologicalSpace C]
    {e : A → C} (he : Topology.IsClosedEmbedding e) (d : DimensionFunction C) :
    DimensionFunction A :=
  d.compClosedEmbedding he

/-- A bundled dimension function satisfies `IsDimensionFunctionForCatenary`. -/
private theorem isDimensionFunctionForCatenary_coe {A : Type*} [TopologicalSpace A]
    (d : DimensionFunction A) : IsDimensionFunctionForCatenary (d : A → ℤ) where
  strict_spec {_ _} hxy hne := d.strictAnti_specializes hxy hne
  immediate {_ _} himm := d.step_immediate himm

/-- The codimension of an irreducible closed subset is its codimension inside a largest
irreducible closed subset. -/
private theorem codimension_eq_topCodim_of_isTop {A : Type*} [TopologicalSpace A]
    (W U : IrreducibleCloseds A) (hU : ∀ V : IrreducibleCloseds A, V ≤ U) :
    codimension W = IrreducibleClosedsCodim.topCodim W U := by
  rw [codimension_eq_coheight]
  apply le_antisymm
  · apply Order.coheight_le
    intro p hp
    by_cases hlast : p.last = U
    · exact IrreducibleClosedsCodim.length_le_topCodim W U p hp hlast
    · let p' := p.snoc U (lt_of_le_of_ne (hU p.last) hlast)
      have hbound := IrreducibleClosedsCodim.length_le_topCodim W U p'
        (by simpa [p'] using hp) (by simp [p'])
      exact le_trans (by simp [p']) hbound
  · rw [IrreducibleClosedsCodim.topCodim_le_iff]
    intro p hp _
    exact Order.length_le_coheight (le_of_eq hp.symm)

/-- **Stacks 02IA, for a closed point of an irreducible sober space.** In a sober space with a
generic point `ξ` and a dimension function `d`, the codimension of a closed point `z` is
`d ξ - d z`. -/
private theorem codimension_singleton_eq_sub_dimensionFunction {A : Type*} [TopologicalSpace A]
    (hA : StacksSober A) (d : DimensionFunction A) (ξ z : A)
    (hξ : IsGenericPoint ξ (Set.univ : Set A)) (hz : IsClosed ({z} : Set A)) :
    codimension (⟨{z}, isIrreducible_singleton, hz⟩ : IrreducibleCloseds A) =
      ((d ξ - d z).toNat : ℕ∞) := by
  have hspec : ξ ⤳ z := hξ.specializes (Set.mem_univ z)
  have hc := codim_closure_singleton_eq_delta_diff hA d (isDimensionFunctionForCatenary_coe d)
    ξ z hspec
  have htop : ∀ V : IrreducibleCloseds A, V ≤ closureSingleton ξ := by
    intro V
    show (V : Set A) ⊆ closure ({ξ} : Set A)
    rw [hξ]
    exact Set.subset_univ _
  rw [← codimension_eq_topCodim_of_isTop _ _ htop] at hc
  rwa [show closureSingleton z = (⟨{z}, isIrreducible_singleton, hz⟩ : IrreducibleCloseds A) from
    IrreducibleCloseds.ext hz.closure_eq] at hc

/-- A nonempty space in which every irreducible closed subset contains a closed point, and in
which every closed point has codimension `n`, has dimension `n`. -/
private theorem topologicalKrullDim_eq_of_forall_codimension_singleton {A : Type*}
    [TopologicalSpace A] [Nonempty A]
    (hclosed : ∀ W : IrreducibleCloseds A, ∃ z ∈ (W : Set A), IsClosed ({z} : Set A)) (n : ℕ∞)
    (hcod : ∀ (z : A) (hz : IsClosed ({z} : Set A)),
      codimension (⟨{z}, isIrreducible_singleton, hz⟩ : IrreducibleCloseds A) = n) :
    topologicalKrullDim A = (n : WithBot ℕ∞) := by
  show Order.krullDim (IrreducibleCloseds A) = _
  apply le_antisymm
  · rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun W => ?_
    obtain ⟨z, hzW, hz⟩ := hclosed W
    have hZW : (⟨{z}, isIrreducible_singleton, hz⟩ : IrreducibleCloseds A) ≤ W :=
      Set.singleton_subset_iff.mpr hzW
    exact WithBot.coe_le_coe.mpr
      ((Order.coheight_anti hZW).trans_eq
        ((codimension_eq_coheight _).symm.trans (hcod z hz)))
  · obtain ⟨x⟩ := ‹Nonempty A›
    obtain ⟨z, -, hz⟩ := hclosed (closureSingleton x)
    rw [← hcod z hz, codimension_eq_coheight]
    exact Order.coheight_le_krullDim _

/-! ### Dimension over a Jacobson base, from a dimension function on `|X|` -/

section WithDimensionFunction

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)
    (hJac : HasEtaleLocalProperty D.site D.base D.base_mem D.space
      (fun T : Scheme.{u} => JacobsonSpace T))
    (hδ : ∀ b : points D.site D.base D.base_mem D.space,
      IsClosed ({b} : Set (points D.site D.base D.base_mem D.space)) → D.delta b = 0)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)

include hX hJac hδ hd

omit hd in
/-- Over a Jacobson base whose dimension function vanishes at closed points, the induced
dimension function of a good algebraic space vanishes at every closed point. -/
private theorem deltaValue_eq_zero_of_isClosed_singleton
    (x : points D.site D.base D.base_mem X)
    (hx : IsClosed ({x} : Set (points D.site D.base D.base_mem X))) :
    D.deltaValue sX x = 0 := by
  have hdecX : IsDecentSpace D.site D.base D.base_mem X := isDecentSpace_of_isGood D sX hX
  have hJacX := exists_jacobson_atlas_of_isLocallyOfFiniteType D.site D.base D.base_mem
    D.isAlgebraicSpace hX.1 sX hX.2.2 hJac
  have hxft : x ∈ finiteTypePoints D.site D.base D.base_mem X := by
    rwa [finiteTypePoints_eq_setOf_isClosed_singleton D.site D.base D.base_mem hX.1 hdecX hJacX]
  have hyft := mapsTo_finiteTypePoints D.site D.base D.base_mem sX hX.1 D.isAlgebraicSpace
    hX.2.2 hxft
  rw [finiteTypePoints_eq_setOf_isClosed_singleton D.site D.base D.base_mem D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated) hJac] at hyft
  have htrdeg := hasTranscendenceDegreeAt_zero_of_isFiniteTypePoint D.site D.base D.base_mem
    hX.1 D.isAlgebraicSpace sX hX.2.2 hJac x hxft
  show inducedDimensionValue D.site D.base D.base_mem D.delta.toFun sX x = 0
  rw [inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace D.delta.toFun
    sX hX.2.2 x 0 htrdeg]
  simpa using hδ _ hyft

omit hδ hd in
/-- **Stacks 06EK and 0BA5 for an integral closed subspace.** Every nonempty closed set of
points of an integral closed subspace of a good algebraic space over a Jacobson base contains a
closed point. -/
private theorem exists_isClosed_singleton_mem_of_isClosed
    (T : Set (points D.site D.base D.base_mem Z.subspace.toFunctor)) (hT : IsClosed T)
    (hne : T.Nonempty) :
    ∃ z ∈ T,
      IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor)) := by
  have hZlft := isLocallyOfFiniteType_of_isImmersion D.site D.base D.base_mem Z.subspace.ι
    (isImmersion_of_isClosedImmersion D.site D.base D.base_mem Z.isClosedSubspace.2)
  have hcomplft := isLocallyOfFiniteType_comp D.site D.base D.base_mem
    Z.isClosedSubspace.1 hX.1 D.isAlgebraicSpace Z.subspace.ι sX hZlft hX.2.2
  have hJacZ := exists_jacobson_atlas_of_isLocallyOfFiniteType D.site D.base D.base_mem
    D.isAlgebraicSpace Z.isClosedSubspace.1 (Z.subspace.ι ≫ sX) hcomplft hJac
  obtain ⟨z, hzT, hzft⟩ := inter_finiteTypePoints_nonempty D.site D.base D.base_mem
    Z.subspace.toFunctor Z.isClosedSubspace.1 hT.isLocallyClosed hne
  rw [finiteTypePoints_eq_setOf_isClosed_singleton D.site D.base D.base_mem
    Z.isClosedSubspace.1 Z.isIntegralSpace.2.1 hJacZ] at hzft
  exact ⟨z, hzT, hzft⟩

omit hJac hδ hd in
/-- The dimension function of `|X|` pulled back to the set of points of an integral closed
subspace along the closed embedding of Stacks 0ABJ and 04CD. -/
private noncomputable def deltaDimensionFunction :
    DimensionFunction (points D.site D.base D.base_mem Z.subspace.toFunctor) :=
  dimensionFunctionComap (Z.isClosedEmbedding_pointsMap D.site D.base D.base_mem hX.1) d

omit hJac hδ hd in
/-- **The dimension function of Situation 0EDT on an integral closed subspace.** The dimension
function of `|X|` pulled back to the set of points of an integral closed subspace `Z ⊆ X` along
the closed embedding of Stacks 0ABJ and 04CD. -/
noncomputable def subspaceDeltaDimensionFunction :
    DimensionFunction (points D.site D.base D.base_mem Z.subspace.toFunctor) :=
  d.compClosedEmbedding (Z.isClosedEmbedding_pointsMap D.site D.base D.base_mem hX.1)

omit hJac hδ in
/-- **The pulled-back dimension function of an integral closed subspace is `δ_{Z/B}`.** The
value of `AlgebraicGeometry.Space.subspaceDeltaDimensionFunction` at a point of `|Z|` is the
value of the dimension function of Situation 0EDT for the structure morphism `Z → B`. -/
theorem subspaceDeltaDimensionFunction_eq_deltaValue
    (x : points D.site D.base D.base_mem Z.subspace.toFunctor) :
    subspaceDeltaDimensionFunction D sX hX d Z x = D.deltaValue (Z.subspace.ι ≫ sX) x := by
  show d _ = _
  exact (hd _).trans (D.deltaValue_comp_of_isLocallyQuasiFinite Z.isClosedSubspace.1 hX.1
    Z.subspace.ι sX
    (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem Z.subspace.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem Z.isClosedSubspace.2))
    hX.2.2 x).symm

omit hd in
/-- The pulled-back dimension function vanishes at a closed point of the integral closed
subspace. -/
private theorem deltaDimensionFunction_eq_zero_of_isClosed_singleton
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor)
    (hz : IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor)))
    (hdz : d (pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι z) =
      D.deltaValue sX (pointsMap D.site D.base D.base_mem Z.subspace.toFunctor
        Z.subspace.ι z)) :
    deltaDimensionFunction D sX hX d Z z = 0 := by
  have hclosed : IsClosed ({pointsMap D.site D.base D.base_mem Z.subspace.toFunctor
                              Z.subspace.ι z} : Set (points D.site D.base D.base_mem X)) := by
    simpa only [Set.image_singleton] using
      ((Z.isClosedEmbedding_pointsMap D.site D.base D.base_mem hX.1).isClosedMap _ hz)
  show d _ = 0
  exact hdz.trans (deltaValue_eq_zero_of_isClosed_singleton D sX hX hJac hδ _ hclosed)

omit hJac hδ in
/-- The δ-dimension of an integral closed subspace is the value of the pulled-back dimension
function at the generic point of that subspace. -/
private theorem deltaDimensionFunction_genericPoint :
    deltaDimensionFunction D sX hX d Z (Z.genericPoint D.site D.base D.base_mem) =
      deltaDimension D sX Z :=
  hd _

/-- The codimension of a closed point of `|Z|`, computed from a dimension function `d` on `|X|`
with underlying function `δ_{X/B}`. -/
private theorem codimension_singleton_eq_deltaDimension_of_dimensionFunction
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor)
    (hz : IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor))) :
    codimension (⟨{z}, isIrreducible_singleton, hz⟩ :
        IrreducibleCloseds (points D.site D.base D.base_mem Z.subspace.toFunctor)) =
      ((deltaDimension D sX Z).toNat : ℕ∞) := by
  have hsober : StacksSober (points D.site D.base D.base_mem Z.subspace.toFunctor) :=
    (stacksSober_iff_t0_and_quasiSober.mpr
      ⟨Z.t0Space_points D.site D.base D.base_mem,
        Z.quasiSober_points D.site D.base D.base_mem⟩)
  have hzero := deltaDimensionFunction_eq_zero_of_isClosed_singleton D sX hX hJac hδ d Z z hz
    (hd _)
  have hval := deltaDimensionFunction_genericPoint D sX hX d hd Z
  have hcod := codimension_singleton_eq_sub_dimensionFunction hsober
    (deltaDimensionFunction D sX hX d Z) (Z.genericPoint D.site D.base D.base_mem) z
    (Z.closure_singleton_genericPoint D.site D.base D.base_mem) hz
  rwa [hzero, hval, sub_zero] at hcod

/-- The δ-dimension of `Z` is nonnegative, computed from a dimension function `d` on `|X|` with
underlying function `δ_{X/B}`. -/
private theorem deltaDimension_nonneg_of_dimensionFunction : 0 ≤ deltaDimension D sX Z := by
  obtain ⟨z, -, hz⟩ := exists_isClosed_singleton_mem_of_isClosed D sX hX hJac Z Set.univ
    isClosed_univ ⟨Z.genericPoint D.site D.base D.base_mem, Set.mem_univ _⟩
  have hgen : IsGenericPoint (Z.genericPoint D.site D.base D.base_mem)
      (Set.univ : Set (points D.site D.base D.base_mem Z.subspace.toFunctor)) :=
    Z.closure_singleton_genericPoint D.site D.base D.base_mem
  have hzero := deltaDimensionFunction_eq_zero_of_isClosed_singleton D sX hX hJac hδ d Z z hz
    (hd _)
  rw [← deltaDimensionFunction_genericPoint D sX hX d hd Z]
  by_cases heq : Z.genericPoint D.site D.base D.base_mem = z
  · subst heq
    omega
  · have := (deltaDimensionFunction D sX hX d Z).strictAnti_specializes
      (hgen.specializes (Set.mem_univ z)) heq
    omega

/-- The dimension of `|Z|`, computed from a dimension function `d` on `|X|` with underlying
function `δ_{X/B}`. -/
private theorem topologicalKrullDim_points_eq_deltaDimension_of_dimensionFunction :
    topologicalKrullDim (points D.site D.base D.base_mem Z.subspace.toFunctor) =
      (((deltaDimension D sX Z).toNat : ℕ∞) : WithBot ℕ∞) := by
  have : Nonempty (points D.site D.base D.base_mem Z.subspace.toFunctor) :=
    ⟨Z.genericPoint D.site D.base D.base_mem⟩
  exact topologicalKrullDim_eq_of_forall_codimension_singleton (fun W =>
    exists_isClosed_singleton_mem_of_isClosed D sX hX hJac Z W W.isClosed'
      W.isIrreducible'.nonempty) _ fun z hz =>
    codimension_singleton_eq_deltaDimension_of_dimensionFunction D sX hX hJac hδ d hd Z z hz

/-- The dimension of the local ring of `Z` at a closed point, computed from a dimension function
`d` on `|X|` with underlying function `δ_{X/B}`. -/
private theorem localRingDimension_eq_deltaDimension_of_dimensionFunction
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor)
    (hz : IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor))) :
    localRingDimension D.site D.base D.base_mem z = ((deltaDimension D sX Z).toNat : ℕ∞) := by
  rw [← codimension_eq_localRingDimension D.site D.base D.base_mem Z.isClosedSubspace.1
    Z.isIntegralSpace.2.1 ⟨{z}, isIrreducible_singleton, hz⟩ z hz.closure_eq]
  exact codimension_singleton_eq_deltaDimension_of_dimensionFunction D sX hX hJac hδ d hd Z z hz

/-- The dimension of the étale local ring of `Z` at a geometric point above a closed point,
computed from a dimension function `d` on `|X|` with underlying function `δ_{X/B}`. -/
private theorem ringKrullDim_etaleLocalRing_eq_deltaDimension_of_dimensionFunction
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor)
    (hz : IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor)))
    (zbar : GeometricPoint D.site D.base D.base_mem Z.subspace.toFunctor)
    (hzbar : zbar.LiesOver z) :
    ringKrullDim (etaleLocalRing D.site D.base D.base_mem Z.subspace.toFunctor zbar) =
      (((deltaDimension D sX Z).toNat : ℕ∞) : WithBot ℕ∞) := by
  have htfae := (localRingDimension_eq_tfae Z.isClosedSubspace.1 z
    ((deltaDimension D sX Z).toNat : ℕ∞)).out 1 3
  exact htfae.mp
    (localRingDimension_eq_deltaDimension_of_dimensionFunction D sX hX hJac hδ d hd Z z hz)
    zbar hzbar

end WithDimensionFunction

/-! ### Stacks 0EDW -/

section

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)
    (hJac : HasEtaleLocalProperty D.site D.base D.base_mem D.space
      (fun T : Scheme.{u} => JacobsonSpace T))
    (hδ : ∀ b : points D.site D.base D.base_mem D.space,
      IsClosed ({b} : Set (points D.site D.base D.base_mem D.space)) → D.delta b = 0)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)

include hX in
/-- **Stacks 0EDN for a good space.** The induced function `δ_{X/B}` of a good algebraic space
is a dimension function on `|X|`. -/
theorem exists_dimensionFunction_deltaValue :
    ∃ d : DimensionFunction (points D.site D.base D.base_mem X), ∀ x, d x = D.deltaValue sX x :=
  exists_dimensionFunction_inducedDimensionValue D.site D.base D.base_mem D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta hX.1 (isDecentSpace_of_isGood D sX hX) sX
    hX.2.2

include hX hJac hδ

/-- Over a Jacobson base whose dimension function vanishes at closed points, the δ-dimension of
an integral closed subspace of a good algebraic space is nonnegative. -/
theorem deltaDimension_nonneg : 0 ≤ deltaDimension D sX Z := by
  obtain ⟨d, hd⟩ := exists_dimensionFunction_deltaValue D sX hX
  exact deltaDimension_nonneg_of_dimensionFunction D sX hX hJac hδ d hd Z

/-- A statement that holds for every dimension function `d` on `|X|` with underlying function
`δ_{X/B}` holds together with the nonnegativity of the δ-dimension of `Z`. -/
private theorem and_of_forall_dimensionFunction {P : Prop}
    (h : ∀ d : DimensionFunction (points D.site D.base D.base_mem X),
      (∀ x, d x = D.deltaValue sX x) → P) :
    0 ≤ deltaDimension D sX Z ∧ P := by
  obtain ⟨d, hd⟩ := exists_dimensionFunction_deltaValue D sX hX
  exact ⟨deltaDimension_nonneg_of_dimensionFunction D sX hX hJac hδ d hd Z, h d hd⟩

/-- **Stacks 0EDW, part (1).** The common value is `δ(ξ) = δ_{X/B}(ξ)`, for `ξ` the generic point
of `|Z|`: the δ-dimension of `Z` is the value at `ξ` of the dimension function `δ_{X/B}` of
Stacks 0EDN, the value of `δ` at the image of `ξ` plus the transcendence degree of `ξ` over that
image, and it is a nonnegative integer. -/
@[stacks 0EDW "part (1): the common value is the induced delta function at the generic point"]
theorem deltaDimension_eq_inducedDimensionValue :
    0 ≤ deltaDimension D sX Z ∧
      deltaDimension D sX Z = inducedDimensionValue D.site D.base D.base_mem D.delta sX
        (pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
          (Z.genericPoint D.site D.base D.base_mem)) :=
  ⟨deltaDimension_nonneg D sX hX hJac hδ Z, rfl⟩

/-- **Stacks 0EDW, parts (1) and (3).** Over a Jacobson base whose dimension function vanishes
at closed points, the codimension of a closed point of the set of points of an integral closed
subspace `Z` of a good algebraic space is the δ-dimension of `Z`, the value of `δ_{X/B}` at the
generic point of `Z`; in particular that integer is nonnegative. -/
@[stacks 0EDW "part (3): the codimension of a closed point of the integral closed subspace is
  the value of the induced delta function at its generic point"]
theorem codimension_singleton_eq_deltaDimension
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor)
    (hz : IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor))) :
    0 ≤ deltaDimension D sX Z ∧
      codimension (⟨{z}, isIrreducible_singleton, hz⟩ :
          IrreducibleCloseds (points D.site D.base D.base_mem Z.subspace.toFunctor)) =
        ((deltaDimension D sX Z).toNat : ℕ∞) := by
  refine and_of_forall_dimensionFunction D sX hX hJac hδ Z fun d hd => ?_
  exact codimension_singleton_eq_deltaDimension_of_dimensionFunction D sX hX hJac hδ d hd Z z hz

/-- **Stacks 0EDW, parts (1) and (2).** Over a Jacobson base whose dimension function vanishes
at closed points, the dimension of the set of points of an integral closed subspace `Z` of a
good algebraic space is the δ-dimension of `Z`, a nonnegative integer. -/
@[stacks 0EDW "part (2): the dimension of the set of points of the integral closed subspace is
  the value of the induced delta function at its generic point"]
theorem topologicalKrullDim_points_eq_deltaDimension :
    0 ≤ deltaDimension D sX Z ∧
      topologicalKrullDim (points D.site D.base D.base_mem Z.subspace.toFunctor) =
        (((deltaDimension D sX Z).toNat : ℕ∞) : WithBot ℕ∞) := by
  refine and_of_forall_dimensionFunction D sX hX hJac hδ Z fun d hd => ?_
  exact topologicalKrullDim_points_eq_deltaDimension_of_dimensionFunction D sX hX hJac hδ d hd Z

/-- **Stacks 0EDW, parts (1) and (4).** Over a Jacobson base whose dimension function vanishes
at closed points, the dimension of the local ring of an integral closed subspace `Z` of a good
algebraic space at a closed point of `|Z|` is the δ-dimension of `Z`, a nonnegative integer. -/
@[stacks 0EDW "part (4): the dimension of the local ring at a closed point is the value of the
  induced delta function at the generic point"]
theorem localRingDimension_eq_deltaDimension
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor)
    (hz : IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor))) :
    0 ≤ deltaDimension D sX Z ∧
      localRingDimension D.site D.base D.base_mem z = ((deltaDimension D sX Z).toNat : ℕ∞) := by
  refine and_of_forall_dimensionFunction D sX hX hJac hδ Z fun d hd => ?_
  exact localRingDimension_eq_deltaDimension_of_dimensionFunction D sX hX hJac hδ d hd Z z hz

/-- **Stacks 0EDW, parts (1) and (5).** Over a Jacobson base whose dimension function vanishes
at closed points, the Krull dimension of the étale local ring of an integral closed subspace `Z`
of a good algebraic space at a geometric point above a closed point of `|Z|` is the δ-dimension
of `Z`, a nonnegative integer. -/
@[stacks 0EDW "part (5): the dimension of the étale local ring at a geometric point above a
  closed point is the value of the induced delta function at the generic point"]
theorem ringKrullDim_etaleLocalRing_eq_deltaDimension
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor)
    (hz : IsClosed ({z} : Set (points D.site D.base D.base_mem Z.subspace.toFunctor)))
    (zbar : GeometricPoint D.site D.base D.base_mem Z.subspace.toFunctor)
    (hzbar : zbar.LiesOver z) :
    0 ≤ deltaDimension D sX Z ∧
      ringKrullDim (etaleLocalRing D.site D.base D.base_mem Z.subspace.toFunctor zbar) =
        (((deltaDimension D sX Z).toNat : ℕ∞) : WithBot ℕ∞) := by
  refine and_of_forall_dimensionFunction D sX hX hJac hδ Z fun d hd => ?_
  exact ringKrullDim_etaleLocalRing_eq_deltaDimension_of_dimensionFunction D sX hX hJac hδ d hd Z z
    hz zbar hzbar

end

end AlgebraicGeometry.Space

end

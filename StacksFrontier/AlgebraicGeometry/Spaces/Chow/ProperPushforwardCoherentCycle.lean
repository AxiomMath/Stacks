module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Proper pushforward of the cycle of a closed subspace and of a coherent sheaf

In Situation 0EDT let `f : X ⟶ Y` be a proper morphism of good algebraic spaces over the base
`B`. **Stacks 0EP3** says two things (it is proved unconditionally in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/ProperPushforwardModuleCycle.lean`; this file keeps
an earlier conditional route).

Part (1): for a closed subspace `Z ⊂ X` with `dim_δ(Z) ≤ k`, proper pushforward of `k`-cycles
carries `[Z]_k` to the cycle of the direct image of its structure sheaf, `f_*[Z]_k = [f_*𝒪_Z]_k`.

Part (2): for a coherent `𝒪_X`-module `F` with `dim_δ(Supp(F)) ≤ k`, proper pushforward carries
`[F]_k` to the cycle of the direct image, `f_*[F]_k = [f_*F]_k`.

Here `𝒪_Z` is read, as in the source and as in the scheme-level
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme` of Stacks 02R6, as the
`𝒪_X`-module `i_*𝒪_Z` along the inclusion `i : Z → X`, so that `f_*𝒪_Z` is `f_*(i_*𝒪_Z)`.

## Main definitions

* `AlgebraicGeometry.Space.cycleResidueDegree`: the degree `[κ(x) : κ(f(x))]` of the extension
  of residue fields at a point, which at the generic point of `Z` is the degree `[R(Z) : R(Z')]`
  with which Stacks 0EP0 weights `Z`.
* `AlgebraicGeometry.Space.properPushforwardWeight`: the coefficient of `Z'` contributed by `Z`,
  the degree when `dim_δ(Z') = dim_δ(Z)` and zero otherwise.
* `AlgebraicGeometry.Space.properPushforwardCoeff` and
  `AlgebraicGeometry.Space.properPushforward`: proper pushforward of cycles, on coefficient
  families and on the group `Z_k(X)` of Stacks 0EDZ.

## Main results

* `AlgebraicGeometry.Space.properPushforward_associatedCycle`: a conditional form of
  Stacks 0EP3, part (2),
  conditionally on the three inputs listed below.
* `AlgebraicGeometry.Space.properPushforward_cycleOfClosedSubspace`: a conditional form of
  Stacks 0EP3, part (1),
  conditionally on the same three inputs for `i_*𝒪_Z` together with the two hypotheses under
  which this library states Stacks 0EED.
* `AlgebraicGeometry.Space.properPushforwardCoeff_cycleCoeffOfModule`: the coefficientwise form
  of part (2) from which both are read off.
* `AlgebraicGeometry.Space.properPushforwardCoeff_mem_cyclesOfDimension`: proper pushforward of
  a `k`-cycle is a `k`-cycle, by Stacks 0ENZ.
* `AlgebraicGeometry.Space.deltaDimensionClosed_le_of_subset_moduleSupport_image`: the support of
  the direct image has δ-dimension at most `k`, so that `[f_*F]_k` is defined.
* `AlgebraicGeometry.Space.inducedDimensionValue_pointsMap_le`: the induced dimension function
  does not grow under `f`, which is what the previous bound runs on.

## Implementation notes

**What is proved and what is assumed.** The source proves part (1) from part (2) and Lemma 0EED,
and part (2) by reducing — through Lemma 0EEG, dévissage of the support, and the finiteness of
Spaces over Fields Lemma 0AD6 — to the case of a *finite* morphism of *schemes*, where it is
Chow Homology Lemma 02R6. The reduction to schemes is not available here: it needs the
comparison of the cycle formalism of this chapter with the one of chapter 42, which no
declaration provides, so the local computation that the scheme case performs is carried as the
hypothesis `hlen`. Three hypotheses are carried in all, each named in the signature.

* `h08AR` is coherence of the direct image `f_*F`. This is Cohomology of Spaces Lemma 08AR,
  which has no presence in this library — see the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ProperCohomologyFinite.lean`, which record that neither
  08AR nor its scheme counterpart 02O5 is proved and that there are no higher direct images of
  modules along a morphism of algebraic spaces at all. Only the degree-zero direct image is
  needed here, `AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU, and only its
  coherence is assumed: the statement of 0EP3 does not make sense without it, since `[f_*F]_k`
  is formed from a coherent module. The remark of the source cites 08AR for exactly this.
* `hsupp` is the containment `Supp(f_*F) ⊆ |f|(Supp(F))`. On schemes this is
  `Stacks.Chow.supp_pushforward_subset_image`; for algebraic spaces nothing relates the support
  of a direct image to the image of the support. The δ-dimension bound on `Supp(f_*F)` is
  *proved* from it, in
  `AlgebraicGeometry.Space.deltaDimensionClosed_le_of_subset_moduleSupport_image`.
* `hlen` is the length of the direct image at the generic point of an integral closed subspace
  `W ⊂ Y` of δ-dimension `k`: it is the sum, over the integral closed subspaces of `X` of
  δ-dimension `k` with integral closed image `W`, of the length of `F` at the generic point
  times the degree of the residue field extension there. This is the content the scheme case
  supplies: on a scheme the stalk of `f_*F` at such a point is the product of the stalks of `F`
  along the finite fibre of the support, `Stacks.Chow.pushforwardStalkLinearEquivPi`, and length
  over the stalk of the target is additive along it and multiplies by the residue degree,
  `Stacks.Chow.sheafMultiplicity_pushforward_eq_finsum`. For algebraic spaces there is no stalk
  formula for a direct image, so the identity is assumed — pointwise, at lengths, not at cycles.

Everything else is proved. Properness enters directly through the quasi-compactness of `f`, which
is what Stacks 0ENZ asks for in
`AlgebraicGeometry.Space.properPushforwardCoeff_mem_cyclesOfDimension`: without it the
pushforward of a `k`-cycle is not known to be a `k`-cycle and neither side of either part is an
element of `Z_k(Y)`. The remaining force of properness in the source — that the fibre of
`Supp(F)` over a point of δ-dimension `k` is *finite*, which is what makes the sum of `hlen`
finite and is proved from the compactness of the fibre — is absorbed into `hlen` along with the
stalk computation, since neither is separable from it without a stalk formula for a direct image.
The bound `dim_δ(Supp(F)) ≤ k` enters twice, once to form `[F]_k` and once in the bound on
`Supp(f_*F)` of
`AlgebraicGeometry.Space.deltaDimensionClosed_le_of_subset_moduleSupport_image`, and the bound
`dim_δ(Z) ≤ k` of part (1) enters in the bound on `Supp(i_*𝒪_Z)` and in Stacks 0EED.

**The weight.** Stacks 0EP0 weights `Z` by `[R(Z) : R(Z')]`, the degree of the extension of
function fields induced by the proper surjective dominant morphism `Z ⟶ Z'` of Stacks 0EEG.
Since the function field of an integral closed subspace is the residue field of the ambient space
at its generic point — Stacks 0ENX, `AlgebraicGeometry.Space.residueFieldGenericPointRingEquiv` —
the degree is taken here directly as the degree of
`AlgebraicGeometry.Space.residueFieldHom` at the generic point of `Z`, the generic point of `Z'`
being the image of that point by
`AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint_closureImage`. No finiteness
is asserted: `Module.finrank` is zero on an infinite extension, which is also what Stacks 0EP0
assigns when the δ-dimension drops, and the finiteness itself is Stacks 0ENY, the theorem
`factorsThrough_properIntegralClosedSubspace_or_isDominant_and_finite_functionField` in the
namespace `AlgebraicGeometry.Space`.

**Cycles as coefficient families.** A `k`-cycle is a coefficient family on the integral closed
subspaces, `AlgebraicGeometry.Space.cyclesOfDimension` of Stacks 0EDZ, so the formal sum defining
the pushforward *is* a coefficient family: the coefficient of `W` is the `∑ᶠ` over the integral
closed subspaces with integral closed image `W`. Only finitely many terms are nonzero whenever
the argument is a cycle, but no such finiteness is needed to form the sum.

**Choices of geometric points.** The cycle of a module is taken at a chosen geometric
representative `γ` of each point. Stacks 0EE1 — independence of the length of that choice,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`
(`StacksFrontier/AlgebraicGeometry/Spaces/GeometricLengthPointIndependence.lean:244`) — means any
choice gives the same length, so parts (1) and (2) are stated here for an arbitrary `γX`, `γY`
on the two spaces, and part (1) for an arbitrary `γZ` on `Z` compatible with `γX`, which is the
hypothesis under which
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero` states
Stacks 0EED.

## References

* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP0](https://stacks.math.columbia.edu/tag/0EP0)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The induced dimension function does not grow under a morphism over the base -/

section DimensionBound

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- Along a morphism `f : X ⟶ Y` of good algebraic spaces over the base, the induced dimension
function at the image of a point is at most its value at the point.

By the pointwise formula of Stacks 0EDN both values are the value of `δ` at the common image in
the base plus a transcendence degree, and the two degrees differ by the transcendence degree of
the point over its image under `f`, by part (3) of Stacks 04NR, which is nonnegative. -/
theorem inducedDimensionValue_pointsMap_le (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (u : points D.site D.base D.base_mem X) :
    inducedDimensionValue D.site D.base D.base_mem D.delta sY
        (pointsMap D.site D.base D.base_mem X f u) ≤
      inducedDimensionValue D.site D.base D.base_mem D.delta sX u := by
  have hfft : IsLocallyOfFiniteType D.site D.base D.base_mem f :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f sY
      (by rw [hbase]; exact hX.2.2)
  obtain ⟨a, ha⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem f hfft u
  obtain ⟨b, hb⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem sY hY.2.2
    (pointsMap D.site D.base D.base_mem X f u)
  have hcomp : HasTranscendenceDegreeAt D.site D.base D.base_mem sX u ((a : ℕ∞) + (b : ℕ∞)) := by
    rw [← hbase]
    exact hasTranscendenceDegreeAt_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace
      f sY u (a : ℕ∞) (b : ℕ∞) ha hb
  have hcast : (a : ℕ∞) + (b : ℕ∞) = ((a + b : ℕ) : ℕ∞) := by push_cast; ring
  rw [hcast] at hcomp
  have hXval := inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace
    D.delta sX hX.2.2 u ((a + b : ℕ) : ℕ∞) hcomp
  have hYval := inducedDimensionValue_eq D.site D.base D.base_mem hY.1 D.isAlgebraicSpace
    D.delta sY hY.2.2 (pointsMap D.site D.base D.base_mem X f u) (b : ℕ∞) hb
  have himg : pointsMap D.site D.base D.base_mem X sX u =
      pointsMap D.site D.base D.base_mem Y sY
        (pointsMap D.site D.base D.base_mem X f u) := by
    rw [← hbase, pointsMap_comp_apply]
  rw [hXval, hYval, himg]
  simp only [ENat.toNat_natCast]
  omega

/-- A closed set of points contained in the image of a closed set of δ-dimension at most `k` has
δ-dimension at most `k`: the induced dimension function does not grow under the morphism. -/
theorem deltaDimensionClosed_le_of_subset_image (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T)
    (T' : Set (points D.site D.base D.base_mem Y)) (hT' : IsClosed T') (k : ℤ)
    (hTk : deltaDimensionClosed D sX hX T hT ≤ (k : EInt))
    (hsub : T' ⊆ pointsMap D.site D.base D.base_mem X f '' T) :
    deltaDimensionClosed D sY hY T' hT' ≤ (k : EInt) := by
  rw [deltaDimensionClosed_le_coe_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hsub hy
  exact (inducedDimensionValue_pointsMap_le D sX hX sY hY f hbase x).trans
    ((deltaDimensionClosed_le_coe_iff D sX hX T hT k).1 hTk x hx)

/-- A closed set of points contained in a closed subspace of δ-dimension at most `k` has
δ-dimension at most `k`. -/
theorem deltaDimensionClosed_le_of_subset_subspacePointSet (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z)
    (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T) (k : ℤ)
    (hZk : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    (hsub : T ⊆ subspacePointSet D.site D.base D.base_mem X Z) :
    deltaDimensionClosed D sX hX T hT ≤ (k : EInt) := by
  rw [deltaDimensionClosed_le_coe_iff]
  intro t ht
  exact (deltaDimensionClosed_le_coe_iff D sX hX _ _ k).1 hZk t (hsub ht)

end DimensionBound

/-! ### The integral closed image and the residue degree -/

section Weight

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The generic point of the integral closed image of an integral closed subspace is the image of
its generic point: the morphism carries the generic point to a generic point of the closure of
the image, and generic points are unique. -/
theorem IntegralClosedSubspace.ambientGenericPoint_closureImage
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY hYdec f Z).ambientGenericPoint
        D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem) := by
  have hgen := Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX
  have hstep : closure ({pointsMap D.site D.base D.base_mem X f
        (Z.ambientGenericPoint D.site D.base D.base_mem)} :
        Set (points D.site D.base D.base_mem Y)) =
      closure (pointsMap D.site D.base D.base_mem X f ''
        subspacePointSet D.site D.base D.base_mem X Z.subspace) := by
    rw [← hgen, closure_image_closure (continuous_pointsMap D.site D.base D.base_mem f),
      Set.image_singleton]
  have hgenY : IsGenericPoint
      (pointsMap D.site D.base D.base_mem X f (Z.ambientGenericPoint D.site D.base D.base_mem))
      (subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY hYdec f Z).subspace) :=
    hstep.trans
      (IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY hYdec
        f Z).symm
  exact (eq_pointsMap_genericPoint_of_isGenericPoint D.site D.base D.base_mem hY _ _ hgenY).symm

/-- The degree `[κ(x) : κ(f(x))]` of the extension of residue fields a morphism of good algebraic
spaces over the base induces at a point.

The extension is `AlgebraicGeometry.Space.residueFieldHom`; at the generic point of an integral
closed subspace it is the extension `R(Z)/R(Z')` of function fields of Stacks 0EP0, by
Stacks 0ENX. The degree is `Module.finrank`, so it is zero on an infinite extension; finiteness
when the δ-dimension is preserved is Stacks 0ENY. -/
def cycleResidueDegree (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (x : points D.site D.base D.base_mem X) : ℕ :=
  letI := (residueFieldHom D.site D.base D.base_mem X Y hY.1
    (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sY hY) f x).toAlgebra
  Module.finrank
    (residueField D.site D.base D.base_mem Y (D.isDecentSpace_of_isGood sY hY)
      (pointsMap D.site D.base D.base_mem X f x))
    (residueField D.site D.base D.base_mem X (D.isDecentSpace_of_isGood sX hX) x)

/-- **The weight of Stacks 0EP0.** The coefficient with which an integral closed subspace `Z ⊂ X`
contributes to its integral closed image `Z' ⊂ Y` under proper pushforward: the degree
`[R(Z) : R(Z')]` when `dim_δ(Z') = dim_δ(Z)`, and zero otherwise. -/
def properPushforwardWeight (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if deltaDimension D sY (cycleImageSubspace D sY hY f Z) = deltaDimension D sX Z then
    (cycleResidueDegree D sX hX sY hY f (Z.ambientGenericPoint D.site D.base D.base_mem) : ℤ)
  else 0

/-- The weight of an integral closed subspace whose integral closed image has δ-dimension other
than its own vanishes. -/
theorem properPushforwardWeight_eq_zero (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sY (cycleImageSubspace D sY hY f Z) ≠ deltaDimension D sX Z) :
    properPushforwardWeight D sX hX sY hY f Z = 0 := by
  rw [properPushforwardWeight, ite_eq_right hZ]

/-- The weight of an integral closed subspace whose integral closed image has the same
δ-dimension is the degree of the extension of function fields. -/
theorem properPushforwardWeight_eq_cycleResidueDegree (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sY (cycleImageSubspace D sY hY f Z) = deltaDimension D sX Z) :
    properPushforwardWeight D sX hX sY hY f Z =
      (cycleResidueDegree D sX hX sY hY f
        (Z.ambientGenericPoint D.site D.base D.base_mem) : ℤ) := by
  rw [properPushforwardWeight, ite_eq_left hZ]

end Weight

/-! ### Proper pushforward of cycles -/

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Proper pushforward of cycles, on coefficient families.** The coefficient of an integral
closed subspace `W ⊂ Y` in the pushforward of a coefficient family `α` on the integral closed
subspaces of `X` is the sum of `α Z` weighted by `AlgebraicGeometry.Space.properPushforwardWeight`
over the integral closed subspaces `Z ⊂ X` with integral closed image `W`. -/
def properPushforwardCoeff (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) : ℤ :=
  ∑ᶠ Z ∈ {Z : IntegralClosedSubspace D.site D.base D.base_mem X |
      cycleImageSubspace D sY hY f Z = W}, α Z * properPushforwardWeight D sX hX sY hY f Z

/-- A nonzero pushforward coefficient at `W` comes from an integral closed subspace with integral
closed image `W` which contributes a nonzero term. -/
theorem exists_ne_zero_of_properPushforwardCoeff_ne_zero (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hW : properPushforwardCoeff D sX hX sY hY f α W ≠ 0) :
    ∃ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      cycleImageSubspace D sY hY f Z = W ∧ α Z ≠ 0 ∧
        properPushforwardWeight D sX hX sY hY f Z ≠ 0 := by
  by_contra h
  refine hW (finsum_mem_eq_zero_of_forall_eq_zero fun Z hZ => ?_)
  rcases not_and_or.1 (fun hc => h ⟨Z, hZ, hc.1, hc.2⟩) with hc | hc
  · rw [not_not.1 hc, zero_mul]
  · rw [not_not.1 hc, mul_zero]

/-- An integral closed subspace of `Y` with nonzero pushforward coefficient has δ-dimension `k`:
some integral closed subspace of `X` of δ-dimension `k` has it as its integral closed image, with
the δ-dimension preserved. -/
theorem deltaDimension_eq_of_properPushforwardCoeff_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, α Z ≠ 0 →
      deltaDimension D sX Z = k)
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hW : properPushforwardCoeff D sX hX sY hY f α W ≠ 0) :
    deltaDimension D sY W = k := by
  obtain ⟨Z, hZW, hZα, hZw⟩ :=
    exists_ne_zero_of_properPushforwardCoeff_ne_zero D sX hX sY hY f α hW
  by_cases hd : deltaDimension D sY (cycleImageSubspace D sY hY f Z) = deltaDimension D sX Z
  · rw [← hZW, hd, hα Z hZα]
  · exact absurd (properPushforwardWeight_eq_zero D sX hX sY hY f hd) hZw

/-- **Stacks 0ENZ for the pushforward of a `k`-cycle.** The sets of points of the integral closed
subspaces of `Y` with nonzero pushforward coefficient form a locally finite collection.

Each of them is the closure of the image of the set of points of an integral closed subspace of
`X` with nonzero coefficient, so the collection is a subcollection of the image collection of
Stacks 0ENZ, which is locally finite because `f` is quasi-compact. -/
theorem locallyFinite_properPushforwardCoeff (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hαlf : LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if α Z = 0 then (∅ : Set (points D.site D.base D.base_mem X))
      else subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    LocallyFinite fun W : IntegralClosedSubspace D.site D.base D.base_mem Y =>
      if properPushforwardCoeff D sX hX sY hY f α W = 0 then
        (∅ : Set (points D.site D.base D.base_mem Y))
      else subspacePointSet D.site D.base D.base_mem Y W.subspace := by
  classical
  have himg := locallyFinite_closure_image_pointsMap D sX hX sY hY hbase hf
    (fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if α Z = 0 then (∅ : Set (points D.site D.base D.base_mem X))
      else subspacePointSet D.site D.base D.base_mem X Z.subspace)
    (fun Z => by
      by_cases h : α Z = 0
      · rw [ite_eq_left h]; exact isClosed_empty
      · rw [ite_eq_right h]
        exact isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 Z)
    hαlf
  intro p
  obtain ⟨V, hV, hfin⟩ := himg.1 p
  refine ⟨V, hV, (hfin.image (cycleImageSubspace D sY hY f)).subset ?_⟩
  intro W hW
  obtain ⟨q, hq, hqV⟩ := hW
  rw [Set.mem_ite_empty_left] at hq
  obtain ⟨Z, hZW, hZα, -⟩ :=
    exists_ne_zero_of_properPushforwardCoeff_ne_zero D sX hX sY hY f α hq.1
  have hZW' : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f Z = W := hZW
  refine ⟨Z, ⟨q, ?_, hqV⟩, hZW⟩
  simp only [ite_eq_right hZα]
  rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) f Z, hZW']
  exact hq.2

/-- Proper pushforward of a `k`-cycle is a `k`-cycle: its support is locally finite by
`AlgebraicGeometry.Space.locallyFinite_properPushforwardCoeff`, and a subspace with nonzero
coefficient has δ-dimension `k` by
`AlgebraicGeometry.Space.deltaDimension_eq_of_properPushforwardCoeff_ne_zero`. -/
theorem properPushforwardCoeff_mem_cyclesOfDimension (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : α ∈ cyclesOfDimension D sX k) :
    properPushforwardCoeff D sX hX sY hY f α ∈ cyclesOfDimension D sY k :=
  ⟨locallyFinite_properPushforwardCoeff D sX hX sY hY hbase hf α hα.1,
    fun _ hW => deltaDimension_eq_of_properPushforwardCoeff_ne_zero D sX hX sY hY f k α hα.2 hW⟩

/-- **Proper pushforward of `k`-cycles.** A proper morphism of good algebraic spaces over the base
carries `Z_k(X)` to `Z_k(Y)` by
`AlgebraicGeometry.Space.properPushforwardCoeff`.

Only quasi-compactness of `f` is used, which is what Stacks 0ENZ asks for; the full construction
of Stacks 0EP1, with its additivity and functoriality, is not formed here. -/
def properPushforward (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ)
    (c : CycleGroup D sX k) : CycleGroup D sY k :=
  ⟨properPushforwardCoeff D sX hX sY hY f c.1,
    properPushforwardCoeff_mem_cyclesOfDimension D sX hX sY hY hbase hf k c.1 c.2⟩

/-- The coefficient family of a proper pushforward is the pushforward of the coefficient
family. -/
theorem properPushforward_coe (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ) (c : CycleGroup D sX k) :
    (properPushforward D sX hX sY hY hbase hf k c).1 =
      properPushforwardCoeff D sX hX sY hY f c.1 :=
  rfl

end Pushforward

/-! ### The coefficientwise identity -/

section Coefficientwise

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The coefficientwise reduction of Stacks 0EP3, part (2), to a length identity.** Let `F` be
an `𝒪_X`-module and `G` an
`𝒪_Y`-module whose length at the generic point of an integral closed subspace `W ⊂ Y` of
δ-dimension `k` is the weighted sum `hlen` of the lengths of `F` over the integral closed
subspaces of δ-dimension `k` with integral closed image `W`. Then the pushforward of the
coefficient family of `[F]_k` is the coefficient family of `[G]_k`.

At an integral closed subspace of δ-dimension `k` this is `hlen`, after the pushforward sum —
which runs over all integral closed subspaces with integral closed image `W` — has been cut down
to those of δ-dimension `k`: a subspace of other δ-dimension has coefficient zero in `[F]_k`. At
an integral closed subspace of δ-dimension other than `k` both sides vanish: the coefficient in
`[G]_k` by definition, and every term of the pushforward sum because a nonzero coefficient in
`[F]_k` forces δ-dimension `k` and then the weight vanishes, the δ-dimension of the image not
being `k`. -/
theorem properPushforwardCoeff_cycleCoeffOfModule (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (G : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (k : ℤ)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hlen : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY W = k →
      ((moduleMultiplicity D.site D.base D.base_mem hY.1 G γY W).toNat : ℤ) =
        ∑ᶠ Z ∈ {Z : IntegralClosedSubspace D.site D.base D.base_mem X |
            cycleImageSubspace D sY hY f Z = W ∧ deltaDimension D sX Z = k},
          ((moduleMultiplicity D.site D.base D.base_mem hX.1 F γX Z).toNat : ℤ) *
            (cycleResidueDegree D sX hX sY hY f
              (Z.ambientGenericPoint D.site D.base D.base_mem) : ℤ)) :
    properPushforwardCoeff D sX hX sY hY f (cycleCoeffOfModule D sX hX F k γX) =
      cycleCoeffOfModule D sY hY G k γY := by
  classical
  have hk : ∀ Z, cycleCoeffOfModule D sX hX F k γX Z ≠ 0 → deltaDimension D sX Z = k :=
    fun Z hZ => by_contra fun h => hZ (ite_eq_right h)
  funext W
  by_cases hW : deltaDimension D sY W = k
  · have hcut : properPushforwardCoeff D sX hX sY hY f (cycleCoeffOfModule D sX hX F k γX) W =
        ∑ᶠ Z ∈ {Z : IntegralClosedSubspace D.site D.base D.base_mem X |
            cycleImageSubspace D sY hY f Z = W ∧ deltaDimension D sX Z = k},
          cycleCoeffOfModule D sX hX F k γX Z * properPushforwardWeight D sX hX sY hY f Z := by
      refine finsum_mem_inter_support_eq' _ _ _ fun Z hZ => ?_
      have hZk := hk Z (left_ne_zero_of_mul hZ)
      exact ⟨fun h => ⟨h, hZk⟩, fun h => h.1⟩
    rw [hcut, cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hW, hlen W hW]
    refine finsum_mem_congr rfl fun Z hZ => ?_
    obtain ⟨hZW, hZk⟩ := hZ
    have hd : deltaDimension D sY (cycleImageSubspace D sY hY f Z) = deltaDimension D sX Z := by
      rw [hZW, hW, hZk]
    rw [properPushforwardWeight_eq_cycleResidueDegree D sX hX sY hY f hd,
      cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hZk]
  · rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_right hW]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun Z hZ => ?_
    by_cases hZc : cycleCoeffOfModule D sX hX F k γX Z = 0
    · rw [hZc, zero_mul]
    · have hZk := hk Z hZc
      have hd : deltaDimension D sY (cycleImageSubspace D sY hY f Z) ≠
          deltaDimension D sX Z := by
        rw [(hZ : cycleImageSubspace D sY hY f Z = W), hZk]
        exact hW
      rw [properPushforwardWeight_eq_zero D sX hX sY hY f hd, mul_zero]

end Coefficientwise

/-! ### Stacks 0EP3 -/

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The direct image of an `𝒪_X`-module along a morphism of algebraic spaces over `S`, read
through the morphism of algebraic spaces the morphism of presheaves defines. This is
`AlgebraicGeometry.Space.modulePushforward`, the direct-image half of Stacks 03LU. -/
abbrev directImageModule (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y) (f : X ⟶ Y)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX) :
    Modules.{u, u} D.site D.base D.base_mem Y hY :=
  (modulePushforward D.site D.base D.base_mem
    (ObjectProperty.homMk f :
      (⟨X, hX⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY⟩)).obj F

/-- The support of a proper direct image has δ-dimension at most that of the support of the
module, granting the containment `hsupp` of the support of the direct image in the image of the
support: the induced dimension function does not grow under the morphism. -/
theorem deltaDimensionClosed_le_of_subset_moduleSupport_image (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F]
    (G : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    [IsCoherent D.site D.base D.base_mem Y hY.1 G] (k : ℤ)
    (hFk : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (hsupp : moduleSupport D.site D.base D.base_mem hY.1 G ⊆
      pointsMap D.site D.base D.base_mem X f ''
        moduleSupport D.site D.base D.base_mem hX.1 F) :
    deltaDimensionClosed D sY hY (moduleSupport D.site D.base D.base_mem hY.1 G)
      (isClosed_moduleSupport D.site D.base D.base_mem hY.1 G) ≤ (k : EInt) :=
  deltaDimensionClosed_le_of_subset_image D sX hX sY hY f hbase _ _ _ _ k hFk hsupp

/-- **A conditional form of Stacks 0EP3, part (2)**, superseded by the unconditional
`AlgebraicGeometry.Space.properCyclePushforward_associatedCycle_eq`. In Situation 0EDT let
`f : X ⟶ Y` be a proper morphism of good
algebraic spaces over the base and let `F` be a coherent `𝒪_X`-module with
`dim_δ(Supp(F)) ≤ k`. Then proper pushforward of `k`-cycles carries `[F]_k` to the cycle of the
direct image: `f_*[F]_k = [f_*F]_k`.

Three inputs this library does not have are carried, each named in the signature.

* `h08AR` is coherence of `f_*F`, which is Cohomology of Spaces Lemma 08AR — the remark of the
  source cites it for exactly this, and it is what makes `[f_*F]_k` expressible at all. The
  library has no statement of 08AR and no higher direct images of modules along a morphism of
  algebraic spaces; only the degree-zero direct image, `AlgebraicGeometry.Space.modulePushforward`
  of Stacks 03LU, is used here, and only its coherence is assumed.
* `hsupp` is the containment `Supp(f_*F) ⊆ |f|(Supp(F))`; the δ-dimension bound on `Supp(f_*F)`,
  which the right-hand side needs, is proved from it and `hFk`.
* `hlen` is the length of `f_*F` at the generic point of an integral closed subspace of `Y` of
  δ-dimension `k`, as the weighted sum of the lengths of `F` over the integral closed subspaces
  of δ-dimension `k` lying over it. This is what the scheme case Stacks 02R6 computes from the
  stalk of a direct image along a finite morphism, and the source's proof reduces to it; this
  library has no stalk formula for a direct image of modules on an algebraic space.

Properness is consumed through the quasi-compactness of `f`, by which Stacks 0ENZ makes the
pushforward of a `k`-cycle a `k`-cycle. -/
theorem properPushforward_associatedCycle (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F]
    [h08AR : IsCoherent D.site D.base D.base_mem Y hY.1
      (directImageModule D hX.1 hY.1 f F)] (k : ℤ)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y)
    (hFk : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (hsupp : moduleSupport D.site D.base D.base_mem hY.1 (directImageModule D hX.1 hY.1 f F) ⊆
      pointsMap D.site D.base D.base_mem X f ''
        moduleSupport D.site D.base D.base_mem hX.1 F)
    (hlen : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY W = k →
      ((moduleMultiplicity D.site D.base D.base_mem hY.1
          (directImageModule D hX.1 hY.1 f F) γY W).toNat : ℤ) =
        ∑ᶠ Z ∈ {Z : IntegralClosedSubspace D.site D.base D.base_mem X |
            cycleImageSubspace D sY hY f Z = W ∧ deltaDimension D sX Z = k},
          ((moduleMultiplicity D.site D.base D.base_mem hX.1 F γX Z).toNat : ℤ) *
            (cycleResidueDegree D sX hX sY hY f
              (Z.ambientGenericPoint D.site D.base D.base_mem) : ℤ)) :
    properPushforward D sX hX sY hY hbase hproper.2.1.2 k
        (associatedCycle D sX hX F k γX hγX hFk) =
      associatedCycle D sY hY (directImageModule D hX.1 hY.1 f F) k γY hγY
        (deltaDimensionClosed_le_of_subset_moduleSupport_image D sX hX sY hY f hbase F
          (directImageModule D hX.1 hY.1 f F) k hFk hsupp) :=
  Subtype.ext
    (properPushforwardCoeff_cycleCoeffOfModule D sX hX sY hY f F
      (directImageModule D hX.1 hY.1 f F) k γX γY hlen)

/-- The coefficient family of `[Z]_k` is a `k`-cycle, granting the hypotheses under which this
library states Stacks 0EED together with coherence of `i_*𝒪_Z` and the containment of its support
in `|Z|`: by Stacks 0EED it is the coefficient family of `[i_*𝒪_Z]_k`, which is a `k`-cycle by
Stacks 0EE5. -/
theorem cycleCoeffOfClosedSubspace_mem_cyclesOfDimension (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (k : ℤ)
    (hZk : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    (γZ : points D.site D.base D.base_mem Z.toFunctor →
      GeometricPoint D.site D.base D.base_mem Z.toFunctor)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (hγZ : ∀ z, (γZ z).LiesOver z)
    [IsCoherent D.site D.base D.base_mem X hX.1
      (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ)]
    (hsuppZ : moduleSupport D.site D.base D.base_mem hX.1
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ) ⊆
      subspacePointSet D.site D.base D.base_mem X Z) :
    cycleCoeffOfClosedSubspace D sX hX Z hZ k γZ ∈ cyclesOfDimension D sX k := by
  rw [cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero D sX hX Z hZ k hZk γZ γX hγZ
    hγX]
  exact cycleCoeffOfModule_mem_cyclesOfDimension D sX hX _ k γX hγX
    (deltaDimensionClosed_le_of_subset_subspacePointSet D sX hX Z hZ _ _ k hZk hsuppZ)

/-- **A conditional form of Stacks 0EP3, part (1)**, superseded by the unconditional
`AlgebraicGeometry.Space.properCyclePushforward_closedSubspaceCycle_eq`. In Situation 0EDT let
`f : X ⟶ Y` be a proper morphism of good
algebraic spaces over the base and let `Z ⊂ X` be a closed subspace with inclusion `i : Z → X`
and `dim_δ(Z) ≤ k`. Then proper pushforward of `k`-cycles carries `[Z]_k` to the cycle of the
direct image of its structure sheaf: `f_*[Z]_k = [f_*𝒪_Z]_k`.

As in the source, and as in the scheme-level
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme`, the sheaf `𝒪_Z` is read as the
`𝒪_X`-module `i_*𝒪_Z`, so that `f_*𝒪_Z` is `f_*(i_*𝒪_Z)`. The proof is the source's: by
Stacks 0EED the cycle `[Z]_k` is the cycle `[i_*𝒪_Z]_k`, and part (2) applies to that module.

The hypotheses are those of part (2) for `F = i_*𝒪_Z` — `h08AR`, `hsupp`, `hlen` — together with
the two hypotheses under which this library states Stacks 0EED, namely that `γZ` and `γX` are
geometric representatives lying over the points they are assigned to (`hγZ`, `hγX`); and with
coherence of `i_*𝒪_Z` and the containment `hsuppZ` of its support in `|Z|`, from which the bound
`dim_δ(Supp(i_*𝒪_Z)) ≤ k` needed to form `[i_*𝒪_Z]_k` is proved out of `dim_δ(Z) ≤ k`. -/
theorem properPushforward_cycleOfClosedSubspace (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem f)
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (k : ℤ)
    (hZk : deltaDimensionSubspace D sX hX Z hZ ≤ (k : EInt))
    (γZ : points D.site D.base D.base_mem Z.toFunctor →
      GeometricPoint D.site D.base D.base_mem Z.toFunctor)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (γY : points D.site D.base D.base_mem Y → GeometricPoint D.site D.base D.base_mem Y)
    (hγY : ∀ y, (γY y).LiesOver y)
    (hγZ : ∀ z, (γZ z).LiesOver z)
    [IsCoherent D.site D.base D.base_mem X hX.1
      (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ)]
    (hsuppZ : moduleSupport D.site D.base D.base_mem hX.1
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ) ⊆
      subspacePointSet D.site D.base D.base_mem X Z)
    [h08AR : IsCoherent D.site D.base D.base_mem Y hY.1
      (directImageModule D hX.1 hY.1 f
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ))]
    (hsupp : moduleSupport D.site D.base D.base_mem hY.1
        (directImageModule D hX.1 hY.1 f
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ)) ⊆
      pointsMap D.site D.base D.base_mem X f ''
        moduleSupport D.site D.base D.base_mem hX.1
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ))
    (hlen : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY W = k →
      ((moduleMultiplicity D.site D.base D.base_mem hY.1
          (directImageModule D hX.1 hY.1 f
            (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ))
          γY W).toNat : ℤ) =
        ∑ᶠ V ∈ {V : IntegralClosedSubspace D.site D.base D.base_mem X |
            cycleImageSubspace D sY hY f V = W ∧ deltaDimension D sX V = k},
          ((moduleMultiplicity D.site D.base D.base_mem hX.1
              (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ)
              γX V).toNat : ℤ) *
            (cycleResidueDegree D sX hX sY hY f
              (V.ambientGenericPoint D.site D.base D.base_mem) : ℤ)) :
    properPushforward D sX hX sY hY hbase hproper.2.1.2 k
        ⟨cycleCoeffOfClosedSubspace D sX hX Z hZ k γZ,
          cycleCoeffOfClosedSubspace_mem_cyclesOfDimension D sX hX Z hZ k hZk γZ γX hγX hγZ
            hsuppZ⟩ =
      associatedCycle D sY hY
        (directImageModule D hX.1 hY.1 f
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ))
        k γY hγY
        (deltaDimensionClosed_le_of_subset_moduleSupport_image D sX hX sY hY f hbase
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ)
          (directImageModule D hX.1 hY.1 f
            (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ))
          k
          (deltaDimensionClosed_le_of_subset_subspacePointSet D sX hX Z hZ _ _ k hZk hsuppZ)
          hsupp) := by
  refine Subtype.ext ?_
  show properPushforwardCoeff D sX hX sY hY f (cycleCoeffOfClosedSubspace D sX hX Z hZ k γZ) =
    cycleCoeffOfModule D sY hY
      (directImageModule D hX.1 hY.1 f
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Z hZ)) k γY
  rw [cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero D sX hX Z hZ k hZk γZ γX hγZ
    hγX]
  exact properPushforwardCoeff_cycleCoeffOfModule D sX hX sY hY f _ _ k γX γY hlen

end Main

end AlgebraicGeometry.Space

end

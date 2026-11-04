module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.JacobianCriterionNodal
public import StacksFrontier.AlgebraicGeometry.Curves.Node
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra

/-!
# Witnesses for the node vocabulary of chapter 53

Every predicate of `StacksFrontier.AlgebraicGeometry.Curves.IsNode` is a condition on the
*completed* local ring of a point of a scheme over a field, so none of them can be exhibited
without computing a completed local ring.  This file does that, at the closed point of the
affine scheme of the nodal power-series algebra

`nodeAlgebra k = k[[x, y]]/(xy)`,

making `HasMulticrossCompletion`, `IsOrdinaryDoublePoint` and `IsMulticrossSingularity`
inhabited rather than merely stated; and, over an algebraically closed field, where the base
change to the algebraic closure is an isomorphism, also `IsNode` and
`HasAtWorstNodalSingularities`.

## Main results

* `Stacks.Curves.hasMulticrossCompletion_nodeAlgebra` — the closed point of
  `Spec k[[x, y]]/(xy)`, over any field `k`, has multicross completed local ring with **two**
  branches.
* `Stacks.Curves.isOrdinaryDoublePoint_nodeAlgebra` and
  `Stacks.Curves.isMulticrossSingularity_nodeAlgebra` — over an algebraically closed field that
  point is an ordinary double point, hence a multicross singularity.
* `Stacks.Curves.ringKrullDim_nodeAlgebra` — the witness is **one-dimensional**: the local ring
  at the point has Krull dimension one.  (The ambient `k[[x, y]]` has dimension two, and the
  equation `xy = 0` cuts it down by one.)
* `Stacks.Curves.not_hasMulticrossCompletion_doubleLineAlgebra` — the **predicted-failure
  control, at the same dimension**: the closed point of `Spec k[[x, y]]/(x²)` is a
  one-dimensional singular point which is *not* a node, because the multicross ring is reduced
  (`Stacks.Curves.isReduced_multicross`) and `k[[x, y]]/(x²)` is not.  So the predicate is not
  vacuously true of singular one-dimensional points.
* `Stacks.Curves.isNodalAlgebra_nodeAlgebra` and `Stacks.Curves.isNagataRing_nodeAlgebra` — the
  *algebra*-level nodality of the same ring, so the scheme-level vocabulary of Tag 0C1W and the
  algebra-level vocabulary of Tags 0C49 and 0C4A are inhabited at one and the same object.
* `Stacks.Curves.hasMulticrossCompletion_of_isIso` — **base change of the node condition along
  an isomorphism of base fields**: `HasMulticrossCompletion` transports along an isomorphism of
  schemes lying over an isomorphism of the base fields.  This is the missing piece for the two
  conditions of Tag 0C47.
* `Stacks.Curves.isNode_nodeAlgebra` and
  `Stacks.Curves.hasAtWorstNodalSingularities_nodeAlgebra` — over an algebraically closed field
  `k`, the closed point of `Spec k̄[[x, y]]/(xy)` is a node in the sense of Tag 0C47, and that
  scheme has at worst nodal singularities over `k`.  The witness is taken over the algebraic
  closure `k̄` so that no base change of the multicross ring is needed: `k → k̄` is then an
  isomorphism, the base-change square is an isomorphism of schemes, and
  `Stacks.Curves.hasMulticrossCompletion_of_isIso` moves the computation across it.  Its
  dimension is again one, by `Stacks.Curves.ringKrullDim_nodeAlgebra` at `k̄`.
* `Stacks.Curves.not_isNode_doubleLineAlgebra` — the control for `IsNode` itself, again at
  dimension one: the closed point of `Spec k̄[[x, y]]/(x²)` is not a node.

The two general bridges are stated separately, since they are what any further witness needs:
`Stacks.Curves.hasMulticrossCompletion_of_ringEquiv` reduces `HasMulticrossCompletion` at a
point whose local ring is complete to a compatible ring isomorphism, and
`Stacks.Curves.nonempty_ringEquiv_of_hasMulticrossCompletion` extracts from it the bare ring
isomorphism, which is all that is needed to refute the predicate.

## Implementation notes

The `k`-algebra structure that `HasMulticrossCompletion` puts on the stalk is the structure
morphism on global sections followed by the germ map; it is named here
`Stacks.Curves.stalkCoeffHom`, parametrized by the morphism to `Spec k` rather than by the
`Scheme.Over` instance, so that the computation at `Spec` of a local ring can be stated without
fixing an instance.  At the closed point of `Spec R` that composite is Mathlib's
`AlgebraicGeometry.stalkClosedPointIso` precomposed with the ring map, which is what identifies
the stalk with `R` *as a `k`-algebra* and not merely as a ring.

Every statement about the stalk itself quantifies over a scheme `X` and a point `x : X`, and is
instantiated at `Spec` only by `exact`.  The reason is that `IsLocalRing (X.presheaf.stalk x)`
is found by instance search only when `x` is syntactically a term of `↥X`; at
`x = closedPoint R`, whose type is `PrimeSpectrum ↥R`, the search fails, so no statement
mentioning `maximalIdeal` of such a stalk can be written down directly.

Completeness of `k[[x, y]]/(xy)` is not quoted from anywhere.  Mathlib's completeness of
`k[[x_0, …, x_{n-1}]]` is for the ideal generated by the variables; that ideal is identified
with the maximal ideal inside `StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra`, and a
quotient of a complete Noetherian local ring is complete because it is a finite module over it.

## References

* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

open MvPowerSeries IsLocalRing AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Curves

/-! ### Completion of a complete ring -/

/-- For an `I`-adically complete ring the completion map is a ring isomorphism. -/
def adicCompletionRingEquivSelf {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    AdicCompletion I R ≃+* R :=
  (RingEquiv.ofBijective (algebraMap R (AdicCompletion I R))
    (AdicCompletion.of_bijective I R)).symm

/-- For an `I`-adically complete `k`-algebra the completion map is an isomorphism of
`k`-algebras. -/
def adicCompletionAlgEquivSelf (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] (I : Ideal R) [IsAdicComplete I R] :
    AdicCompletion I R ≃ₐ[k] R :=
  (AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective (algebraMap R (AdicCompletion I R))
      (AdicCompletion.of_bijective I R))
    (fun _ => rfl)).symm

/-! ### Completeness of hypersurface quotients of a power-series ring -/

variable (k : Type u) [Field k]

/-- `k[[x_0, …, x_{n-1}]]` is complete for its maximal ideal. -/
theorem isAdicComplete_maximalIdeal_mvPowerSeries (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) k)) (MvPowerSeries (Fin n) k) := by
  rw [maximalIdeal_mvPowerSeries_eq_span_X k n]
  infer_instance

/-- A quotient of a complete Noetherian local ring is complete for its own maximal ideal: the
quotient is a finite module over the ring, and its maximal ideal is the image of the maximal
ideal. -/
theorem isAdicComplete_maximalIdeal_quotient {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : IsAdicComplete (maximalIdeal A) A) (I : Ideal A)
    [IsLocalRing (A ⧸ I)] :
    IsAdicComplete (maximalIdeal (A ⧸ I)) (A ⧸ I) := by
  have hmap : Ideal.map (algebraMap A (A ⧸ I)) (maximalIdeal A) = maximalIdeal (A ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  rw [← hmap, IsAdicComplete.map_algebraMap_iff]
  have := hA
  exact isAdicComplete_of_iInf_smul_eq_bot (maximalIdeal A)
    (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ (maximalIdeal_le_jacobson _))

/-- A quotient of `k[[x_0, …, x_{n-1}]]` is complete for its own maximal ideal. -/
theorem isAdicComplete_maximalIdeal_quotient_mvPowerSeries {n : ℕ}
    (I : Ideal (MvPowerSeries (Fin n) k)) [IsLocalRing (MvPowerSeries (Fin n) k ⧸ I)] :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) k ⧸ I))
      (MvPowerSeries (Fin n) k ⧸ I) :=
  isAdicComplete_maximalIdeal_quotient (isAdicComplete_maximalIdeal_mvPowerSeries k n) I

/-! ### The coefficient map of a stalk -/

/-- The coefficient map `k → 𝒪_{X,x}` cut out by a morphism `f : X ⟶ Spec k`: the structure
morphism on global sections followed by the germ at `x`.  For `f = X ↘ Spec k` this is the
`k`-algebra structure on the stalk used by `Stacks.Curves.HasMulticrossCompletion`. -/
def stalkCoeffHom {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    k →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom

/-- At the closed point of `Spec R` for a local ring `R`, Mathlib's identification of the stalk
with `R` carries the coefficient map of a morphism `Spec R ⟶ Spec k` to the ring map it comes
from.  This is what identifies the stalk with `R` as a `k`-algebra. -/
theorem stalkClosedPointIso_stalkCoeffHom (R : CommRingCat.{u}) [IsLocalRing R]
    (φ : CommRingCat.of k ⟶ R) (a : k) :
    (stalkClosedPointIso R).hom.hom (stalkCoeffHom k (Spec.map φ) (closedPoint R) a) =
      φ.hom a := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Spec.map φ).appTop ≫
      (Spec R).presheaf.germ ⊤ (closedPoint R) trivial = φ ≫ (stalkClosedPointIso R).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]
  have key' : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Spec.map φ).appTop ≫
      (Spec R).presheaf.germ ⊤ (closedPoint R) trivial) ≫ (stalkClosedPointIso R).hom = φ := by
    rw [key, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g : CommRingCat.of k ⟶ R => g.hom a) key'

/-- A point whose local ring is isomorphic to a complete local ring has complete local ring. -/
theorem isAdicComplete_stalk_of_ringEquiv {X : Scheme.{u}} (x : X) {A : Type u} [CommRing A]
    [IsLocalRing A] (σ : (X.presheaf.stalk x) ≃+* A)
    (hA : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) := by
  have h := (IsAdicComplete.congr_ringEquiv (maximalIdeal A) σ.symm).2 hA
  rwa [show Ideal.map σ.symm (maximalIdeal A) = maximalIdeal (X.presheaf.stalk x) from
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)] at h

/-! ### The two general bridges -/

/-- **A criterion for `HasMulticrossCompletion`.**  If the local ring at `x` is isomorphic,
compatibly with the coefficient maps, to a complete local `k`-algebra `A` which is
`k`-isomorphic to the `n`-branch multicross ring, then the completed local ring at `x` is that
multicross ring. -/
theorem hasMulticrossCompletion_of_ringEquiv {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] (x : X) (n : ℕ) {A : Type u} [CommRing A] [IsLocalRing A]
    [Algebra k A] (hA : IsAdicComplete (maximalIdeal A) A)
    (σ : (X.presheaf.stalk x) ≃+* A)
    (hσ : ∀ a : k, σ (stalkCoeffHom k (X ↘ Spec (CommRingCat.of k)) x a) = algebraMap k A a)
    (e : A ≃ₐ[k] multicross k n) :
    HasMulticrossCompletion k X x n := by
  let : Algebra k (X.presheaf.stalk x) :=
    (stalkCoeffHom k (X ↘ Spec (CommRingCat.of k)) x).toAlgebra
  let := isAdicComplete_stalk_of_ringEquiv x σ hA
  exact ⟨(adicCompletionAlgEquivSelf k (maximalIdeal (X.presheaf.stalk x))).trans
    ((AlgEquiv.ofRingEquiv (f := σ) hσ).trans e)⟩

/-- The content of `HasMulticrossCompletion` as a bare ring isomorphism of the local ring at `x`
with the multicross ring, available whenever that local ring is complete. -/
theorem nonempty_ringEquiv_of_hasMulticrossCompletion {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] (x : X) (n : ℕ) {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : IsAdicComplete (maximalIdeal A) A) (σ : (X.presheaf.stalk x) ≃+* A)
    (h : HasMulticrossCompletion k X x n) :
    Nonempty (A ≃+* multicross k n) := by
  let : Algebra k (X.presheaf.stalk x) :=
    (stalkCoeffHom k (X ↘ Spec (CommRingCat.of k)) x).toAlgebra
  let := isAdicComplete_stalk_of_ringEquiv x σ hA
  obtain ⟨e⟩ := h
  exact ⟨σ.symm.trans
    ((adicCompletionRingEquivSelf (maximalIdeal (X.presheaf.stalk x))).symm.trans
      e.toRingEquiv)⟩

/-! ### The nodal algebra and the double line -/

/-- Every variable lies in the maximal ideal of `k[[x_0, …, x_{n-1}]]`. -/
theorem X_mem_maximalIdeal_mvPowerSeries {n : ℕ} (i : Fin n) :
    (X i : MvPowerSeries (Fin n) k) ∈ maximalIdeal (MvPowerSeries (Fin n) k) := by
  rw [maximalIdeal_mvPowerSeries_eq_span_X k n]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- A principal ideal generated by an element of the maximal ideal of a local ring is proper. -/
theorem span_singleton_ne_top {A : Type*} [CommRing A] [IsLocalRing A] {f : A}
    (hf : f ∈ maximalIdeal A) : Ideal.span {f} ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 hf))

/-- The nodal power-series algebra `k[[x, y]]/(xy)`, the completed local ring of a node. -/
abbrev nodeAlgebra : Type u :=
  MvPowerSeries (Fin 2) k ⧸ Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) * X 1}

/-- The double line `k[[x, y]]/(x²)`: a one-dimensional singularity which is not reduced. -/
abbrev doubleLineAlgebra : Type u :=
  MvPowerSeries (Fin 2) k ⧸ Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) ^ 2}

/-- The product `xy` lies in the maximal ideal of `k[[x, y]]`. -/
theorem X_zero_mul_X_one_mem_maximalIdeal :
    (X 0 : MvPowerSeries (Fin 2) k) * X 1 ∈ maximalIdeal (MvPowerSeries (Fin 2) k) :=
  Ideal.mul_mem_right _ _ (X_mem_maximalIdeal_mvPowerSeries k 0)

/-- The square `x²` lies in the maximal ideal of `k[[x, y]]`. -/
theorem X_zero_sq_mem_maximalIdeal :
    (X 0 : MvPowerSeries (Fin 2) k) ^ 2 ∈ maximalIdeal (MvPowerSeries (Fin 2) k) := by
  rw [pow_two]
  exact Ideal.mul_mem_right _ _ (X_mem_maximalIdeal_mvPowerSeries k 0)

/-- The nodal algebra `k[[x, y]]/(xy)` is nontrivial. -/
instance instNontrivialNodeAlgebra : Nontrivial (nodeAlgebra k) :=
  Submodule.Quotient.nontrivial_iff.mpr
    (span_singleton_ne_top (X_zero_mul_X_one_mem_maximalIdeal k))

/-- The nodal algebra `k[[x, y]]/(xy)` is a local ring. -/
instance instIsLocalRingNodeAlgebra : IsLocalRing (nodeAlgebra k) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- The double line `k[[x, y]]/(x²)` is nontrivial. -/
instance instNontrivialDoubleLineAlgebra : Nontrivial (doubleLineAlgebra k) :=
  Submodule.Quotient.nontrivial_iff.mpr (span_singleton_ne_top (X_zero_sq_mem_maximalIdeal k))

/-- The double line `k[[x, y]]/(x²)` is a local ring. -/
instance instIsLocalRingDoubleLineAlgebra : IsLocalRing (doubleLineAlgebra k) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-! ### The witness -/

/-- **The closed point of `Spec k[[x, y]]/(xy)` has multicross completed local ring with two
branches**, where the scheme is `Spec` of the nodal algebra over `Spec k` through the algebra
structure map. -/
theorem hasMulticrossCompletion_nodeAlgebra :
    letI : (Spec (CommRingCat.of (nodeAlgebra k))).Over (Spec (CommRingCat.of k)) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap k (nodeAlgebra k)))⟩
    HasMulticrossCompletion k (Spec (CommRingCat.of (nodeAlgebra k)))
      (closedPoint (nodeAlgebra k)) 2 :=
  hasMulticrossCompletion_of_ringEquiv k _ 2
    (isAdicComplete_maximalIdeal_quotient_mvPowerSeries k _)
    (stalkClosedPointIso (CommRingCat.of (nodeAlgebra k))).commRingCatIsoToRingEquiv
    (fun a => stalkClosedPointIso_stalkCoeffHom k (CommRingCat.of (nodeAlgebra k))
      (CommRingCat.ofHom (algebraMap k (nodeAlgebra k))) a)
    quotientAlgEquivMulticross

/-- The closed point of `Spec` of a local ring is a closed point of the scheme. -/
theorem isClosed_singleton_closedPoint (A : Type u) [CommRing A] [IsLocalRing A] :
    IsClosed ({closedPoint A} : Set (Spec (CommRingCat.of A))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (maximalIdeal.isMaximal A)

/-- **The closed point of `Spec k[[x, y]]/(xy)` over an algebraically closed field is an
ordinary double point**, i.e. a node in the sense of Tag 0C1W. -/
theorem isOrdinaryDoublePoint_nodeAlgebra [IsAlgClosed k] :
    letI : (Spec (CommRingCat.of (nodeAlgebra k))).Over (Spec (CommRingCat.of k)) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap k (nodeAlgebra k)))⟩
    IsOrdinaryDoublePoint k (Spec (CommRingCat.of (nodeAlgebra k)))
      (closedPoint (nodeAlgebra k)) :=
  ⟨isClosed_singleton_closedPoint (nodeAlgebra k), hasMulticrossCompletion_nodeAlgebra k⟩

/-- **The same point is a multicross singularity**, with two branches. -/
theorem isMulticrossSingularity_nodeAlgebra [IsAlgClosed k] :
    letI : (Spec (CommRingCat.of (nodeAlgebra k))).Over (Spec (CommRingCat.of k)) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap k (nodeAlgebra k)))⟩
    IsMulticrossSingularity k (Spec (CommRingCat.of (nodeAlgebra k)))
      (closedPoint (nodeAlgebra k)) :=
  IsOrdinaryDoublePoint.isMulticrossSingularity (isOrdinaryDoublePoint_nodeAlgebra k)

/-! ### The dimension of the witness, and its algebra-level nodality -/

/-- The two spellings of the nodal equation generate the same ideal. -/
theorem span_nodalBinaryQuadratic_zero_one_zero :
    Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) * X 1} =
      Ideal.span {nodalBinaryQuadratic (0 : k) 1 0} := by
  rw [nodalBinaryQuadratic_zero_one_zero]

/-- The change of spelling of the nodal equation, as an isomorphism of `k`-algebras. -/
def nodeAlgebraEquivQuadraticQuotient :
    nodeAlgebra k ≃ₐ[k]
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic (0 : k) 1 0}) :=
  Ideal.quotientEquivAlgOfEq k (span_nodalBinaryQuadratic_zero_one_zero k)

/-- `k[[x, y]]/(xy)` is reduced. -/
theorem isReduced_nodeAlgebra : IsReduced (nodeAlgebra k) :=
  have := isReduced_nodalBinaryQuadratic_quotient (0 : k) 1 0 (by norm_num)
  isReduced_of_injective (nodeAlgebraEquivQuadraticQuotient k)
    (nodeAlgebraEquivQuadraticQuotient k).injective

/-- `k[[x, y]]/(xy)` carries a nondegenerate quadratic relation on its cotangent space. -/
theorem hasNodalQuadraticRelation_nodeAlgebra :
    HasNodalQuadraticRelation (nodeAlgebra k) := by
  have hloc : IsLocalRing
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic (0 : k) 1 0}) := by
    rw [← span_nodalBinaryQuadratic_zero_one_zero k]
    infer_instance
  exact hasNodalQuadraticRelation_of_ringEquiv
    (nodeAlgebraEquivQuadraticQuotient k).symm.toRingEquiv
    (hasNodalQuadraticRelation_nodalBinaryQuadratic_quotient (0 : k) 1 0 (by norm_num))

/-- **The witness is one-dimensional**: the completed local ring `k[[x, y]]/(xy)` of the node
has Krull dimension one. -/
theorem ringKrullDim_nodeAlgebra : ringKrullDim (nodeAlgebra k) = 1 :=
  ringKrullDim_eq_one_of_isReduced_and_hasNodalQuadraticRelation (nodeAlgebra k)
    (isReduced_nodeAlgebra k) (hasNodalQuadraticRelation_nodeAlgebra k)

/-- `k[[x, y]]/(xy)` is a Nagata ring: it is Noetherian, local and complete. -/
theorem isNagataRing_nodeAlgebra : IsNagataRing (nodeAlgebra k) :=
  have := isAdicComplete_maximalIdeal_quotient_mvPowerSeries k
    (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) * X 1})
  IsNagataRing.of_isPrecomplete_maximalIdeal

/-- **`k[[x, y]]/(xy)` is a nodal `k`-algebra** in the sense of Tag 0C49, so the algebra-level
and the scheme-level node vocabularies are inhabited at one and the same object. -/
theorem isNodalAlgebra_nodeAlgebra : IsNodalAlgebra k (nodeAlgebra k) :=
  (isNodalAlgebra_quotient_iff _).2
    ⟨isReduced_nodeAlgebra k, hasNodalQuadraticRelation_nodeAlgebra k⟩

/-! ### The predicted-failure control -/

/-- A variable of `k[[x_0, …, x_{n-1}]]` is nonzero. -/
theorem X_ne_zero_mvPowerSeries {n : ℕ} (i : Fin n) :
    (X i : MvPowerSeries (Fin n) k) ≠ 0 := by
  intro h
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  simp at hc

/-- `k[[x, y]]` is a domain. -/
theorem isDomain_mvPowerSeries_fin_two : IsDomain (MvPowerSeries (Fin 2) k) :=
  have : IsRegularLocalRing (MvPowerSeries (Fin 2) k) :=
    isRegularLocalRing_mvPowerSeries k 2
  IsRegularLocalRing.isDomain (MvPowerSeries (Fin 2) k)

/-- `x` is not a multiple of `x²`: otherwise cancelling `x` in the domain `k[[x, y]]` would make
`x` a unit. -/
theorem X_zero_notMem_span_X_zero_sq :
    (X 0 : MvPowerSeries (Fin 2) k) ∉ Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) ^ 2} := by
  have := isDomain_mvPowerSeries_fin_two k
  intro hmem
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 hmem
  have h1 : (X 0 : MvPowerSeries (Fin 2) k) * (g * X 0) =
      (X 0 : MvPowerSeries (Fin 2) k) * 1 := by
    rw [mul_one]
    calc (X 0 : MvPowerSeries (Fin 2) k) * (g * X 0) = g * X 0 ^ 2 := by ring
      _ = X 0 := hg
  have h2 := mul_left_cancel₀ (X_ne_zero_mvPowerSeries k (0 : Fin 2)) h1
  exact IsLocalRing.notMem_maximalIdeal.mpr (IsUnit.of_mul_eq_one g ((mul_comm _ _).trans h2))
    (X_mem_maximalIdeal_mvPowerSeries k 0)

/-- `k[[x, y]]/(x²)` is **not** reduced: the class of `x` is a nonzero square root of zero. -/
theorem not_isReduced_doubleLineAlgebra : ¬ IsReduced (doubleLineAlgebra k) := by
  intro h
  have hnil : IsNilpotent
      ((Ideal.Quotient.mk (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) ^ 2})) (X 0)) := by
    refine ⟨2, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  exact X_zero_notMem_span_X_zero_sq k (Ideal.Quotient.eq_zero_iff_mem.1 (h.eq_zero _ hnil))

/-- The reduced multicross ring is not isomorphic to the non-reduced double line. -/
private theorem not_nonempty_ringEquiv_doubleLineAlgebra_multicross (K : Type u) [Field K] :
    ¬ Nonempty (doubleLineAlgebra K ≃+* multicross K 2) := by
  rintro ⟨E⟩
  have := isReduced_multicross K
  exact not_isReduced_doubleLineAlgebra K (isReduced_of_injective E E.injective)

private theorem eq_one_of_add_one_eq_two {d : WithBot ℕ∞} (h : d + 1 = 2) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe m =>
      have hm : ((m + 1 : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by push_cast; exact h
      have h2 : m + 1 = 2 := Nat.cast_injective hm
      simp [show m = 1 by omega]

/-- **The control has the same dimension as the witness**: `k[[x, y]]/(x²)` is also
one-dimensional, being `k[[x, y]]` cut by a nonzerodivisor lying in the maximal ideal. -/
theorem ringKrullDim_doubleLineAlgebra : ringKrullDim (doubleLineAlgebra k) = 1 := by
  have := isDomain_mvPowerSeries_fin_two k
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero
      (pow_ne_zero 2 (X_ne_zero_mvPowerSeries k (0 : Fin 2))))
    (X_zero_sq_mem_maximalIdeal k)
  rw [ringKrullDim_mvPowerSeries_fin_two k] at h
  exact eq_one_of_add_one_eq_two h

/-- **The predicted-failure control.**  The closed point of `Spec k[[x, y]]/(x²)` is a
one-dimensional singular point of a `k`-scheme whose completed local ring is *not* the
two-branch multicross ring: the multicross ring is reduced and `k[[x, y]]/(x²)` is not.  So
`Stacks.Curves.HasMulticrossCompletion _ _ _ 2` is not vacuously true of the closed points of
singular one-dimensional affine `k`-schemes. -/
theorem not_hasMulticrossCompletion_doubleLineAlgebra :
    letI : (Spec (CommRingCat.of (doubleLineAlgebra k))).Over (Spec (CommRingCat.of k)) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap k (doubleLineAlgebra k)))⟩
    ¬ HasMulticrossCompletion k (Spec (CommRingCat.of (doubleLineAlgebra k)))
      (closedPoint (doubleLineAlgebra k)) 2 := by
  intro hnode
  obtain ⟨E⟩ := nonempty_ringEquiv_of_hasMulticrossCompletion k _ 2
    (isAdicComplete_maximalIdeal_quotient_mvPowerSeries k _)
    (stalkClosedPointIso (CommRingCat.of (doubleLineAlgebra k))).commRingCatIsoToRingEquiv hnode
  exact not_nonempty_ringEquiv_doubleLineAlgebra_multicross k ⟨E⟩

/-! ### Base change to the algebraic closure: nodes in the sense of Tag 0C47 -/

/-- Naturality of the germ at the top open set against a stalk map. -/
theorem appTop_germ_top {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.appTop ≫ X.presheaf.germ ⊤ x trivial =
      Y.presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x :=
  (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm

/-- Transport of `HasMulticrossCompletion` along an isomorphism of schemes lying over an
isomorphism of the base fields. -/
theorem hasMulticrossCompletion_of_isIso
    {k K : Type u} [Field k] [Field K]
    (ψ : CommRingCat.of k ⟶ CommRingCat.of K) [IsIso ψ]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of K))]
    (h : Y ⟶ X) [IsIso h]
    (hsq : h ≫ (X ↘ Spec (CommRingCat.of k)) =
      (Y ↘ Spec (CommRingCat.of K)) ≫ Spec.map ψ)
    (y : Y) (x : X) (hxy : h.base y = x) (n : ℕ)
    {A : Type u} [CommRing A] [IsLocalRing A] [Algebra K A]
    (hA : IsAdicComplete (maximalIdeal A) A)
    (σ : X.presheaf.stalk x ≃+* A)
    (hσ : ∀ a : k, σ (stalkCoeffHom k (X ↘ Spec (CommRingCat.of k)) x a) =
      algebraMap K A (ψ.hom a))
    (e : A ≃ₐ[K] multicross K n) :
    HasMulticrossCompletion K Y y n := by
  subst hxy
  have key : (Y ↘ Spec (CommRingCat.of K)) =
      h ≫ (X ↘ Spec (CommRingCat.of k)) ≫ inv (Spec.map ψ) := by
    rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have nat : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec.map (inv ψ)).appTop =
      inv ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (inv ψ)).symm
  have key2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (Y ↘ Spec (CommRingCat.of K)).appTop ≫ Y.presheaf.germ ⊤ y trivial
      = inv ψ ≫ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ Spec (CommRingCat.of k)).appTop ≫
          X.presheaf.germ ⊤ (h.base y) trivial) ≫ h.stalkMap y :=
    calc (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (Y ↘ Spec (CommRingCat.of K)).appTop ≫ Y.presheaf.germ ⊤ y trivial
        = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec.map (inv ψ)).appTop) ≫
            (X ↘ Spec (CommRingCat.of k)).appTop ≫
              h.appTop ≫ Y.presheaf.germ ⊤ y trivial := by
          rw [key, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, ← Spec.map_inv]
          simp only [Category.assoc]
      _ = (inv ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv) ≫
            (X ↘ Spec (CommRingCat.of k)).appTop ≫
              X.presheaf.germ ⊤ (h.base y) trivial ≫ h.stalkMap y := by
          rw [nat, appTop_germ_top h y]
      _ = _ := by simp only [Category.assoc]
  refine hasMulticrossCompletion_of_ringEquiv K y n hA
    (((asIso (h.stalkMap y)).symm.commRingCatIsoToRingEquiv).trans σ) ?_ e
  intro a
  have hz : stalkCoeffHom K (Y ↘ Spec (CommRingCat.of K)) y a =
      (h.stalkMap y).hom
        (stalkCoeffHom k (X ↘ Spec (CommRingCat.of k)) (h.base y) ((inv ψ).hom a)) :=
    congrArg (fun g : CommRingCat.of K ⟶ Y.presheaf.stalk y => g.hom a) key2
  show σ (((asIso (h.stalkMap y)).symm.commRingCatIsoToRingEquiv)
    (stalkCoeffHom K (Y ↘ Spec (CommRingCat.of K)) y a)) = algebraMap K A a
  rw [hz]
  have hinv : ((asIso (h.stalkMap y)).symm.commRingCatIsoToRingEquiv)
      ((h.stalkMap y).hom
        (stalkCoeffHom k (X ↘ Spec (CommRingCat.of k)) (h.base y) ((inv ψ).hom a))) =
      stalkCoeffHom k (X ↘ Spec (CommRingCat.of k)) (h.base y) ((inv ψ).hom a) :=
    congrArg (fun g : X.presheaf.stalk (h.base y) ⟶ X.presheaf.stalk (h.base y) => g.hom _)
      (IsIso.hom_inv_id (h.stalkMap y))
  rw [hinv, hσ]
  exact congrArg (algebraMap K A)
    (congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a) (IsIso.inv_hom_id ψ))

section BaseChange

open CategoryTheory.Limits

/-- `Spec k̄[[x, y]]/(xy)` regarded as a scheme over `Spec k`, through the composite
`k → k̄ → k̄[[x, y]]/(xy)`. -/
instance nodeSchemeOverClosure :
    (Spec (CommRingCat.of (nodeAlgebra (AlgebraicClosure k)))).Over (Spec (CommRingCat.of k)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap k (nodeAlgebra (AlgebraicClosure k))))⟩

/-- Over an algebraically closed field, the map `k → k̄` is an isomorphism. -/
private theorem isIso_ofHom_algebraMap_algebraicClosure [IsAlgClosed k] :
    IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Over an algebraically closed field, `Spec k̄ → Spec k` is an isomorphism. -/
private theorem isIso_spec_map_ofHom_algebraMap_algebraicClosure [IsAlgClosed k] :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :=
  have := isIso_ofHom_algebraMap_algebraicClosure k
  inferInstance

/-- **The closed point of `Spec k̄[[x, y]]/(xy)`, as a `k`-scheme, is a node** in the sense of
Tag 0C47. -/
theorem isNode_nodeAlgebra [IsAlgClosed k] :
    IsNode k (Spec (CommRingCat.of (nodeAlgebra (AlgebraicClosure k))))
      (closedPoint (nodeAlgebra (AlgebraicClosure k))) := by
  have hψ := isIso_ofHom_algebraMap_algebraicClosure k
  have := isIso_spec_map_ofHom_algebraMap_algebraicClosure k
  set fX : Spec (CommRingCat.of (nodeAlgebra (AlgebraicClosure k))) ⟶
      Spec (CommRingCat.of k) :=
    Spec (CommRingCat.of (nodeAlgebra (AlgebraicClosure k))) ↘ Spec (CommRingCat.of k)
  set g : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsIso (pullback.fst fX g) := inferInstance
  let instY : (pullback fX g).Over (Spec (CommRingCat.of (AlgebraicClosure k))) :=
    ⟨pullback.snd fX g⟩
  have hbase : (pullback.fst fX g).base
      ((inv (pullback.fst fX g)).base (closedPoint (nodeAlgebra (AlgebraicClosure k)))) =
      closedPoint (nodeAlgebra (AlgebraicClosure k)) := by
    have hc := Scheme.Hom.comp_apply (inv (pullback.fst fX g)) (pullback.fst fX g)
      (closedPoint (nodeAlgebra (AlgebraicClosure k)))
    rw [IsIso.inv_hom_id] at hc
    exact hc.symm
  refine ⟨isClosed_singleton_closedPoint (nodeAlgebra (AlgebraicClosure k)),
    (inv (pullback.fst fX g)).base (closedPoint (nodeAlgebra (AlgebraicClosure k))),
    hbase, ?_, ?_⟩
  · -- the point above is closed
    have hpre : (pullback.fst fX g).base ⁻¹'
        {closedPoint (nodeAlgebra (AlgebraicClosure k))} =
        {(inv (pullback.fst fX g)).base (closedPoint (nodeAlgebra (AlgebraicClosure k)))} := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨hbase, fun z hz => ?_⟩
      have hc := Scheme.Hom.comp_apply (pullback.fst fX g) (inv (pullback.fst fX g)) z
      rw [IsIso.hom_inv_id, show (pullback.fst fX g).base z =
        closedPoint (nodeAlgebra (AlgebraicClosure k)) from hz] at hc
      exact hc
    rw [← hpre]
    exact (isClosed_singleton_closedPoint
      (nodeAlgebra (AlgebraicClosure k))).preimage (pullback.fst fX g).continuous
  · -- the completed local ring above is the two-branch multicross ring
    refine hasMulticrossCompletion_of_isIso
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) (pullback.fst fX g)
      pullback.condition _ (closedPoint (nodeAlgebra (AlgebraicClosure k))) hbase 2
      (isAdicComplete_maximalIdeal_quotient_mvPowerSeries (AlgebraicClosure k) _)
      (stalkClosedPointIso
        (CommRingCat.of (nodeAlgebra (AlgebraicClosure k)))).commRingCatIsoToRingEquiv
      (fun a => ?_) quotientAlgEquivMulticross
    exact (stalkClosedPointIso_stalkCoeffHom k
        (CommRingCat.of (nodeAlgebra (AlgebraicClosure k)))
        (CommRingCat.ofHom (algebraMap k (nodeAlgebra (AlgebraicClosure k)))) a).trans
      (IsScalarTower.algebraMap_apply k (AlgebraicClosure k)
        (nodeAlgebra (AlgebraicClosure k)) a)

/-- The only closed point of `Spec` of a local ring is the closed point. -/
theorem eq_closedPoint_of_isClosed (A : Type u) [CommRing A] [IsLocalRing A]
    (x : Spec (CommRingCat.of A)) (hx : IsClosed ({x} : Set (Spec (CommRingCat.of A)))) :
    x = closedPoint A := by
  have hx' : IsClosed ({x} : Set (PrimeSpectrum A)) := hx
  exact PrimeSpectrum.ext
    (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).1 hx'))

/-- **`Spec k̄[[x, y]]/(xy)` has at worst nodal singularities over `k`** (Tag 0C47): it has a
single closed point, and that point is a node. -/
theorem hasAtWorstNodalSingularities_nodeAlgebra [IsAlgClosed k] :
    HasAtWorstNodalSingularities k
      (Spec (CommRingCat.of (nodeAlgebra (AlgebraicClosure k)))) := by
  intro x hx
  obtain rfl := eq_closedPoint_of_isClosed (nodeAlgebra (AlgebraicClosure k)) x hx
  exact Or.inr (isNode_nodeAlgebra k)

/-- The converse transport: `HasMulticrossCompletion` upstairs gives a ring isomorphism of the
local ring downstairs with the multicross ring.  No compatibility with the coefficient maps is
needed, because the conclusion is only a ring isomorphism. -/
theorem nonempty_ringEquiv_of_hasMulticrossCompletion_of_isIso
    {k' K : Type u} [Field k'] [Field K]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k'))]
    [Y.Over (Spec (CommRingCat.of K))]
    (h : Y ⟶ X) [IsIso h] (y : Y) (x : X) (hxy : h.base y = x) (n : ℕ)
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : IsAdicComplete (maximalIdeal A) A) (σ : X.presheaf.stalk x ≃+* A)
    (hmc : HasMulticrossCompletion K Y y n) :
    Nonempty (A ≃+* multicross K n) := by
  subst hxy
  exact nonempty_ringEquiv_of_hasMulticrossCompletion K y n hA
    (((asIso (h.stalkMap y)).symm.commRingCatIsoToRingEquiv).trans σ) hmc

/-- `Spec k̄[[x, y]]/(x²)` regarded as a scheme over `Spec k`. -/
instance doubleLineSchemeOverClosure :
    (Spec (CommRingCat.of (doubleLineAlgebra (AlgebraicClosure k)))).Over
      (Spec (CommRingCat.of k)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap k (doubleLineAlgebra (AlgebraicClosure k))))⟩

/-- **The predicted-failure control for `IsNode` itself.**  The closed point of
`Spec k̄[[x, y]]/(x²)` is a closed point of a one-dimensional `k`-scheme which is *not* a node in
the sense of Tag 0C47: the base change is an isomorphism, so a node above it would exhibit a
ring isomorphism of the non-reduced ring `k̄[[x, y]]/(x²)` with the reduced two-branch multicross
ring. -/
theorem not_isNode_doubleLineAlgebra [IsAlgClosed k] :
    ¬ IsNode k (Spec (CommRingCat.of (doubleLineAlgebra (AlgebraicClosure k))))
      (closedPoint (doubleLineAlgebra (AlgebraicClosure k))) := by
  have hψ := isIso_ofHom_algebraMap_algebraicClosure k
  have := isIso_spec_map_ofHom_algebraMap_algebraicClosure k
  rintro ⟨-, ybar, hybar, -, hmc⟩
  have : IsIso (pullback.fst
      (Spec (CommRingCat.of (doubleLineAlgebra (AlgebraicClosure k))) ↘
        Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) := inferInstance
  obtain ⟨E⟩ := nonempty_ringEquiv_of_hasMulticrossCompletion_of_isIso (k' := k)
    (pullback.fst
      (Spec (CommRingCat.of (doubleLineAlgebra (AlgebraicClosure k))) ↘
        Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ybar
    (closedPoint (doubleLineAlgebra (AlgebraicClosure k))) hybar 2
    (isAdicComplete_maximalIdeal_quotient_mvPowerSeries (AlgebraicClosure k) _)
    (stalkClosedPointIso
      (CommRingCat.of (doubleLineAlgebra (AlgebraicClosure k)))).commRingCatIsoToRingEquiv hmc
  exact not_nonempty_ringEquiv_doubleLineAlgebra_multicross (AlgebraicClosure k) ⟨E⟩

end BaseChange

end Stacks.Curves

end

module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinCompletedCap
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes


/-!
# Classical Weil cohomology theories

Fix an algebraically closed field `k` and a field `F` of characteristic zero. Section 45.7 of
the Stacks Project (Tag 0FGS) defines a *classical Weil cohomology theory* over `k` with
coefficients in `F` (Definition 0FGV) as data

* (D1) a contravariant functor `H^*` from smooth projective varieties over `k` to graded
  commutative `F`-algebras,
* (D2) for every smooth projective variety `X` a group homomorphism `γ : CH^i(X) ⟶ H^{2i}(X)`,
* (D3) for every smooth projective variety `X` of dimension `d` a map `∫_X : H^{2d}(X) ⟶ F`,

subject to Poincaré duality (A), the Künneth formula (B), and the compatibility (C) of `γ` with
the Gysin pullback `f^!`, the proper pushforward `f_*`, the intersection product and the class
of a point. This file states that definition with the Chow groups, the Gysin maps, the proper
pushforward, the exterior product and the fundamental classes of Chapter 42, over the base
`Spec k` with the zero dimension function (Stacks 02QM).

## Main definitions

* `Stacks.Chow.SmoothFactorization.graph`: the graph factorization `X ⟶ X ×_S Y ⟶ Y` of a
  morphism whose source is smooth over `S`, through which its Gysin map exists (Stacks 0FFB).
* `Stacks.Chow.SmoothFactorization.ofIsImmersion`: an immersion factored through the identity.
* `Stacks.Chow.chowGroupConnectedComponentsEquiv`: `CH_n(X) = ∏_i CH_n(X_i)` over the connected
  components of `X`.
* `Stacks.Chow.completedCapChowGroup`: the cap product `c ∩ β ∈ CH_*(X)` of a completed
  bivariant class `c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0) with `β ∈ CH_m(Y)`.
* `Stacks.Chow.diagonalIntersectionProduct`: the intersection product `α · β = Δ^!(α × β)` of
  Stacks 0FC0 on the Chow groups of a scheme smooth over a field.
* `Stacks.WeilCohomology.SmoothProjective.gysinPullback`: the Gysin pullback `f^!` of Stacks
  0FF3 along a morphism of smooth projective varieties.
* `Stacks.WeilCohomology.SmoothProjective.point`: `Spec k` as a smooth projective variety.
* `Stacks.WeilCohomology.ClassicalWeilCohomology`: **a classical Weil cohomology theory**,
  Stacks 0FGV.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.dimension_point`: `Spec k` has
  dimension zero.
* `Stacks.WeilCohomology.ClassicalWeilCohomology.cycleClass_gysinPullback_self` and
  `Stacks.WeilCohomology.ClassicalWeilCohomology.cycleClass_diagonalIntersectionProduct_self`:
  axioms (C)(a) and (C)(c) in the degree of the right-hand side, and their `_of_ne` companions
  in the other degrees.
* `Stacks.WeilCohomology.ClassicalWeilCohomology.cycleClass_point_ne_zero`: the class of a
  point is nonzero.

## Implementation notes

**Chow groups.** `CH_n(X)` is `Stacks.Chow.chowGroup` for `Stacks.Chow.fieldChowSituation k`,
which is the convention of Chapter 45 (Tag 0FFI). A smooth projective variety `X` of dimension
`d` is integral, so it is its own piece in the decomposition of Stacks 0FE3 and its Chow group of
codimension-`i` cycles (Stacks 0FE2) is `CH^i(X) = CH_{d-i}(X)`; the cycle class map is written on
that group, with `d` the dimension that the Poincaré duality setup records and identifies with
the dimension of `X`.

**The operations of axiom (C).** All of them are the ones of Chapter 42, none is data:

* the Gysin pullback `f^!` is the cap product with the Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of
  Stacks 0FF3, `Stacks.Chow.lciGysinClass`, built on the graph factorization (Stacks 0FFB); a
  morphism of smooth projective varieties is a local complete intersection morphism by
  Stacks 0E9K, and the class does not depend on the factorization by Stacks 0FF2;
* the proper pushforward is `Stacks.Chow.properChowPushforward` (Stacks 02R4, 02S2);
* the intersection product is `α · β = Δ^!(α × β)` (Stacks 0FC0, Remark 0FGU), with the exterior
  product `Stacks.Chow.chowExteriorProduct` of Stacks 0FBV and the Gysin map `Δ^!` of the
  diagonal, a regular immersion (Stacks 0FBR), which is the Gysin map of Stacks 0FF3 for the
  factorization of `Δ` through the identity;
* `[Spec k]` is `Stacks.Chow.fundamentalChowClass` of `Spec k`, the fundamental class of
  Stacks 0FE4.

The Gysin map and the intersection product are classes in `CH_*(X)`, written as the family of
their parts `CH_n(X)`; axioms (C)(a) and (C)(c) compare `γ` of each part with the matching graded
piece of the right-hand side, which is how the equalities `γ(f^!β) = f^*γ(β)` and
`γ(α · β) = γ(α) ∪ γ(β)` read in `H^*(X) = ⨁_n H^n(X)`. Every class of `CH^*(X) = ⨁_i CH^i(X)`
is a finite sum of homogeneous ones and every map in the axioms is additive (the product
biadditive), so the axioms are stated for homogeneous classes.

**Poincaré duality and the Künneth formula** are as in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory`: (D1), (D3) and (A) are
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`, the pushforward of (C)(b) on cohomology
is the one that Poincaré duality determines, and (B) is stated for every fibre product of `X`
and `Y` over `k` in the category of smooth projective varieties.

## References

* [Stacks Project, Section 45.7 (Tag 0FGS)](https://stacks.math.columbia.edu/tag/0FGS)
* [Stacks Project, Tag 0FGV](https://stacks.math.columbia.edu/tag/0FGV)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
* [Stacks Project, Tag 0FE2](https://stacks.math.columbia.edu/tag/0FE2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct

universe u v w

namespace AlgebraicGeometry

/-- The spectrum of a field is a regular scheme. -/
theorem isRegular_spec_of_field (k : Type u) [Field k] : IsRegular (Spec (.of k)) := fun _ =>
  ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm⟩

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### Two factorizations through which a Gysin map exists -/

section Factorization

variable {X Y : Scheme.{u}}

/-- The graph factorization `X ⟶ X ×_S Y ⟶ Y` of a morphism `f : X ⟶ Y` over a base `S` whose
source is smooth over `S`: the graph `(1, f)` is an immersion, and the second projection is
smooth, being a base change of `X ⟶ S`. This is the factorization through which Stacks 0FFB
shows that the Gysin map of `f` exists. -/
def SmoothFactorization.graph {S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX] (sY : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ sY = sX) : SmoothFactorization f where
  ambient := pullback sX sY
  imm := pullback.lift (𝟙 X) f (by rw [Category.id_comp, hf])
  proj := pullback.snd sX sY
  isImmersion := by
    have : IsImmersion (pullback.lift (𝟙 X) f (by rw [Category.id_comp, hf]) ≫
        pullback.fst sX sY) := by
      rw [pullback.lift_fst]
      infer_instance
    exact IsImmersion.of_comp _ (pullback.fst sX sY)
  isSmooth := inferInstance
  imm_proj := pullback.lift_snd _ _ _

/-- The factorization of an immersion through the identity of its target. For a regular
immersion the Gysin map of Stacks 0FF3 built from it is the class of the regular immersion
itself. -/
def SmoothFactorization.ofIsImmersion (f : X ⟶ Y) [IsImmersion f] : SmoothFactorization f where
  ambient := Y
  imm := f
  proj := 𝟙 Y
  isImmersion := inferInstance
  isSmooth := inferInstance
  imm_proj := Category.comp_id f

end Factorization

/-! ### Capping a Chow class with a completed bivariant class -/

section Cap

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- `CH_n(X) = ∏_i CH_n(X_i)` over the connected components `X_i` of a scheme `X` locally of
finite type over the base: the components are restriction to the `X_i`. -/
def chowGroupConnectedComponentsEquiv (n : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    chowGroup C sX n ≃+ ∀ i : _root_.ConnectedComponents X,
      chowGroup C ((X.connectedComponentOpens i).ι ≫ sX) n :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  chowGroupClopenRestrictEquiv C sX (fun i => (X.connectedComponentOpens i).ι ≫ sX)
    (fun i => (X.connectedComponentOpens i).ι) (fun _ => rfl)
    (by simpa using X.isClopenDecomposition_connectedComponentOpens) n

variable (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- **The cap product `c ∩ β ∈ CH_*(X)` of a completed bivariant class
`c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0) with a class `β ∈ CH_m(Y)`**, as the family of its parts
`(c ∩ β)_n ∈ CH_n(X)`. On a connected component `X_i` of `X`, mapping into the connected
component `Y_{a(i)}` of `Y`, it is `c_i ∩ β|_{Y_{a(i)}}`, the cap product
`Stacks.Chow.completedCap` of the entry `c_i ∈ A^*(X_i ⟶ Y_{a(i)})` with the restriction of `β`;
the parts on the components are glued by `CH_n(X) = ∏_i CH_n(X_i)`. -/
def completedCapChowGroup (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (m : ℤ) (β : chowGroup C sY m) (n : ℤ) : chowGroup C sX n :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := LocallyOfFiniteType.isLocallyNoetherian sY
  (chowGroupConnectedComponentsEquiv C sX n).symm fun i =>
    completedCap C sX sY f hf c
      (fun j => Pi.single m (chowGroupConnectedComponentsEquiv C sY m β j)) i n

end Cap

/-! ### The intersection product on the Chow groups of a smooth scheme over a field -/

section Intersection

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
  [Smooth sX]

/-- The diagonal of a scheme smooth over a field is a local complete intersection morphism: its
source and target are smooth over the field, hence regular (Stacks 0E9K). -/
theorem isLocalCompleteIntersectionMorphism_diagonal_of_smooth :
    haveI : LocallyOfFiniteType (pullback.diagonal sX) :=
      locallyOfFiniteType_of_comp _ (pullback.fst sX sX)
    IsLocalCompleteIntersectionMorphism (pullback.diagonal sX) :=
  have : LocallyOfFiniteType (pullback.diagonal sX) :=
    locallyOfFiniteType_of_comp _ (pullback.fst sX sX)
  isLocalCompleteIntersectionMorphism_of_isRegular _
    (isRegular_of_smooth sX inferInstance (isRegular_spec_of_field k))
    (isRegular_of_smooth (pullback.fst sX sX ≫ sX) inferInstance (isRegular_spec_of_field k))

/-- **The intersection product of Stacks 0FC0, `α · β = Δ^!(α × β) ∈ CH_*(X)`**, for `X` smooth
over a field `k`, `α ∈ CH_n(X)` and `β ∈ CH_m(X)`, as the family of its parts
`(α · β)_p ∈ CH_p(X)`. Here `α × β ∈ CH_{n+m}(X ×_k X)` is the exterior product of Stacks 0FBV
and `Δ^! ∈ A^*(X ⟶ X ×_k X)^∧` is the Gysin map of the diagonal (Stacks 0FBR): the Gysin map of
Stacks 0FF3 for the regular immersion `Δ`, factored through the identity of `X ×_k X`, i.e. the
class `c(X ⟶ X ×_k X, 𝒩)` of the normal sheaf of `Δ`. The source writes the product in the
Chow group of `X ×_X X = X`, which is where the cap product with `Δ^!` lands. -/
def diagonalIntersectionProduct (n m : ℤ) (α : chowGroup (fieldChowSituation k) sX n)
    (β : chowGroup (fieldChowSituation k) sX m) (p : ℤ) : chowGroup (fieldChowSituation k) sX p :=
  haveI : LocallyOfFiniteType (pullback.diagonal sX) :=
    locallyOfFiniteType_of_comp _ (pullback.fst sX sX)
  completedCapChowGroup (fieldChowSituation k) sX (selfProductStructure (fieldChowSituation k) sX)
    (pullback.diagonal sX) (diagonal_comp_selfProductStructure (fieldChowSituation k) sX)
    (lciGysinClass (fieldChowSituation k) sX (selfProductStructure (fieldChowSituation k) sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure (fieldChowSituation k) sX)
      (isLocalCompleteIntersectionMorphism_diagonal_of_smooth k sX)
      (SmoothFactorization.ofIsImmersion (pullback.diagonal sX)))
    (n + m) (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) sX sX n m (α ⊗ₜ β)) p

end Intersection

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

/-! ### Smooth projective varieties as schemes over `k` -/

namespace SmoothProjective

variable {k : Type u} [Field k]

/-- A smooth projective variety over `k` is a smooth variety over `k`. -/
instance isSmoothVariety (X : (SmoothProjective k).FullSubcategory) :
    IsSmoothVariety k X.obj.hom :=
  X.2.1

/-- The structure morphism of a smooth projective variety over `k` is proper. -/
instance isProper (X : (SmoothProjective k).FullSubcategory) : IsProper X.obj.hom :=
  isProper_of_isProjectiveMorphism _ X.2.2

/-- A smooth projective variety over `k` is a regular scheme. -/
theorem isRegular (X : (SmoothProjective k).FullSubcategory) : IsRegular X.obj.left :=
  isRegular_of_smooth X.obj.hom inferInstance (isRegular_spec_of_field k)

variable {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y)

/-- The underlying morphism of schemes of a morphism of smooth projective varieties is locally of
finite type. -/
instance locallyOfFiniteType_hom_left : LocallyOfFiniteType f.hom.left := by
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
    rw [Over.w f.hom]
    infer_instance
  exact locallyOfFiniteType_of_comp _ Y.obj.hom

/-- The underlying morphism of schemes of a morphism of smooth projective varieties is proper. -/
instance isProper_hom_left : IsProper f.hom.left := by
  have : IsProper (f.hom.left ≫ Y.obj.hom) := by
    rw [Over.w f.hom]
    infer_instance
  exact IsProper.of_comp _ Y.obj.hom

/-- A morphism of smooth projective varieties is a local complete intersection morphism
(Stacks 0E9K). -/
theorem isLocalCompleteIntersectionMorphism_hom_left :
    IsLocalCompleteIntersectionMorphism f.hom.left :=
  isLocalCompleteIntersectionMorphism_of_isRegular _ (isRegular X) (isRegular Y)

/-- **The Gysin pullback `f^! : CH_m(Y) ⟶ CH_*(X)`** of a morphism `f : X ⟶ Y` of smooth
projective varieties, as the family of the parts `(f^!β)_n ∈ CH_n(X)`: the cap product with the
Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3, which exists by Stacks 0FFB, `f` being a local
complete intersection morphism (Stacks 0E9K) which factors as the graph immersion
`X ⟶ X ×_k Y` followed by the smooth projection `X ×_k Y ⟶ Y`. By Stacks 0FF2 the class does
not depend on that factorization. -/
def gysinPullback (m : ℤ) (β : chowGroup (fieldChowSituation k) Y.obj.hom m) (n : ℤ) :
    chowGroup (fieldChowSituation k) X.obj.hom n :=
  completedCapChowGroup (fieldChowSituation k) X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom)
    (lciGysinClass (fieldChowSituation k) X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom)
      (isLocalCompleteIntersectionMorphism_hom_left f)
      (SmoothFactorization.graph X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom)))
    m β n

/-- `Spec k` as a smooth projective variety over `k`, with the identity as structure
morphism. -/
def point (k : Type u) [Field k] : (SmoothProjective k).FullSubcategory :=
  haveI : IsVariety k (𝟙 (Spec (.of k))) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  ⟨Over.mk (𝟙 (Spec (.of k))), (isSmoothVariety_iff k (𝟙 (Spec (.of k)))).2 ⟨inferInstance,
    inferInstance⟩, isProjectiveMorphism_id _⟩

end SmoothProjective

open SmoothProjective

/-- The dimension of `Spec k` recorded by a Poincaré duality setup is zero, since that dimension
is the topological dimension of the one-point space `Spec k`. -/
theorem PoincareDualityPushforwardSetup.dimension_point {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [CharZero F] (S : PoincareDualityPushforwardSetup.{u, v, w} k F) :
    S.dimension (point k) = 0 := by
  have h := S.dimension_eq (point k)
  have : Subsingleton (point k).obj.left := inferInstanceAs (Subsingleton (Spec (.of k)))
  have h0 : topologicalKrullDim (point k).obj.left ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [h] at h0
  exact Nat.le_zero.mp (by exact_mod_cast h0)

/-- **Stacks Project, Definition 0FGV.** A *classical Weil cohomology theory* over an
algebraically closed field `k` with coefficients in a field `F` of characteristic zero: the data
(D1), (D2), (D3) subject to the axioms (A), (B), (C) of Section 45.7.

* (D1) and (D3), with axiom (A), Poincaré duality, are the parent structure
  `Stacks.WeilCohomology.PoincareDualityPushforwardSetup`: a contravariant functor `H^*` from
  smooth projective varieties over `k` to graded commutative `F`-algebras and the trace maps
  `∫_X : H^{2d}(X) ⟶ F`, with finite dimensionality, perfectness of the trace pairings, vanishing
  outside `[0, 2d]`, and `∫_X` an isomorphism.
* (D2) is `cycleClass`: a group homomorphism `γ : CH^i(X) ⟶ H^{2i}(X)`, where
  `CH^i(X) = CH_{d-i}(X)` is the Chow group of codimension-`i` cycles of the variety `X` of
  dimension `d` (Stacks 0FE2), `CH_*` being the Chow groups of Stacks 02RW over `Spec k` with the
  zero dimension function (Stacks 02QM).
* (B) is `kunneth`.
* (C)(a)–(d) are `cycleClass_gysinPullback`, `cycleClass_properChowPushforward`,
  `cycleClass_diagonalIntersectionProduct` and `integration_cycleClass_point`, for the Gysin
  pullback of Stacks 0FF3, the proper pushforward of Stacks 02R4, the intersection product
  `α · β = Δ^!(α × β)` of Stacks 0FC0, and the fundamental class `[Spec k]`.

The Gysin pullback `f^!β` and the intersection product `α · β` are classes in `CH_*(X)`, given
by their parts in each dimension; the identities `γ(f^!β) = f^*γ(β)` and
`γ(α · β) = γ(α) ∪ γ(β)` of `H^*(X) = ⨁_n H^n(X)` are stated in each degree `2j`, the right-hand
sides being homogeneous of degrees `2i` and `2(r + s)`. Since every class of
`CH^*(Y) = ⨁_i CH^i(Y)` is a finite sum of homogeneous classes and all the maps involved are
additive (the product biadditive), the axioms are stated for homogeneous classes. -/
@[stacks 0FGV]
structure ClassicalWeilCohomology (k : Type u) [Field k] [IsAlgClosed k]
    (F : Type v) [Field F] [CharZero F]
    extends PoincareDualityPushforwardSetup.{u, v, w} k F where
  /-- (D2) The cycle class map `γ : CH^i(X) ⟶ H^{2i}(X)`, a group homomorphism, where
  `CH^i(X) = CH_{d-i}(X)` for `X` of dimension `d`. -/
  cycleClass : ∀ (X : (SmoothProjective k).FullSubcategory) (i : ℤ),
    chowGroup (fieldChowSituation k) X.obj.hom ((dimension X : ℤ) - i) →+ (H X).piece (2 * i)
  /-- (B) The Künneth formula: for `P` a fibre product of `X` and `Y` over `k`, the map
  `H^*(X) ⊗_F H^*(Y) ⟶ H^*(P)`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, is an isomorphism. -/
  kunneth : ∀ (X Y P : (SmoothProjective k).FullSubcategory) (p : P ⟶ X) (q : P ⟶ Y),
    IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom →
      Function.Bijective
        (kunnethMap (H X) (H Y) (H P) (fun i => pullback p i) fun j => pullback q j)
  /-- (C)(a) Compatibility with the Gysin pullback, `γ(f^!β) = f^*γ(β)` for `β ∈ CH^i(Y)`,
  in each degree `2j` of `H^*(X)`. -/
  cycleClass_gysinPullback : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y)
    (i : ℤ) (β : chowGroup (fieldChowSituation k) Y.obj.hom ((dimension Y : ℤ) - i)) (j : ℤ),
    cycleClass X j (gysinPullback f ((dimension Y : ℤ) - i) β ((dimension X : ℤ) - j)) =
      DirectSum.of (fun n => (H X).piece n) (2 * i) (pullback f (2 * i) (cycleClass Y i β))
        (2 * j)
  /-- (C)(b) Compatibility with the proper pushforward, `γ(f_*α) = f_*γ(α)` for `α ∈ CH^r(X)`.
  On cycles `f_* : CH_{d-r}(X) ⟶ CH_{d-r}(Y) = CH^{e-d+r}(Y)` is proper pushforward
  (Stacks 02R4, descended to Chow groups by Stacks 02S2; `f` is proper since `X` is proper and
  `Y` separated over `k`), and on cohomology `f_* : H^{2r}(X) ⟶ H^{2(e-d+r)}(Y)` is the
  pushforward determined by Poincaré duality; `d`, `e` are the dimensions of `X`, `Y`. -/
  cycleClass_properChowPushforward : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y)
    (r : ℤ) (α : chowGroup (fieldChowSituation k) X.obj.hom ((dimension X : ℤ) - r)),
    toPoincareDualityPushforwardSetup.pushforward f (2 * (dimension X : ℤ) - 2 * r)
        (ExternallyGraded.degreeCast (R := F) (X := (H X).piece)
          (show 2 * r = 2 * (dimension X : ℤ) - (2 * (dimension X : ℤ) - 2 * r) by ring)
          (cycleClass X r α)) =
      ExternallyGraded.degreeCast (R := F) (X := (H Y).piece)
        (show 2 * ((dimension Y : ℤ) - ((dimension X : ℤ) - r)) =
            2 * (dimension Y : ℤ) - (2 * (dimension X : ℤ) - 2 * r) by ring)
        (cycleClass Y ((dimension Y : ℤ) - ((dimension X : ℤ) - r))
          (chowGroupDegreeEquiv (fieldChowSituation k) Y.obj.hom
            (show (dimension X : ℤ) - r =
              (dimension Y : ℤ) - ((dimension Y : ℤ) - ((dimension X : ℤ) - r)) by ring)
            (properChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom f.hom.left
              (Over.w f.hom) ((dimension X : ℤ) - r)
              (properPushforwardDescends (fieldChowSituation k) _ _ _ _ _) α)))
  /-- (C)(c) Compatibility with the intersection product, `γ(α · β) = γ(α) ∪ γ(β)` for
  `α ∈ CH^r(X)` and `β ∈ CH^s(X)`, in each degree `2j` of `H^*(X)`. -/
  cycleClass_diagonalIntersectionProduct : ∀ (X : (SmoothProjective k).FullSubcategory)
    (r s : ℤ) (α : chowGroup (fieldChowSituation k) X.obj.hom ((dimension X : ℤ) - r))
    (β : chowGroup (fieldChowSituation k) X.obj.hom ((dimension X : ℤ) - s)) (j : ℤ),
    cycleClass X j (diagonalIntersectionProduct k X.obj.hom ((dimension X : ℤ) - r)
        ((dimension X : ℤ) - s) α β ((dimension X : ℤ) - j)) =
      DirectSum.of (fun n => (H X).piece n) (2 * (r + s))
        ((H X).evenCup r s (cycleClass X r α) (cycleClass X s β)) (2 * j)
  /-- (C)(d) Normalisation, `∫_{Spec k} γ([Spec k]) = 1`, for the fundamental class
  `[Spec k] ∈ CH^0(Spec k)`. -/
  integration_cycleClass_point :
    integration (point k) (ExternallyGraded.degreeCast (R := F) (X := (H (point k)).piece)
      (show 2 * (0 : ℤ) = 2 * (dimension (point k) : ℤ) by
        have h : dimension (point k) = 0 := toPoincareDualityPushforwardSetup.dimension_point
        rw [h]
        rfl)
      (cycleClass (point k) 0
        (fundamentalChowClass (fieldChowSituation k) (point k).obj.hom
          ((dimension (point k) : ℤ) - 0)))) = 1


namespace ClassicalWeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ClassicalWeilCohomology.{u, v, w} k F) {X Y : (SmoothProjective k).FullSubcategory}

/-- Axiom (C)(a) in the degree of `β`: `γ((f^!β)^i) = f^*γ(β)` for `β ∈ CH^i(Y)`. -/
theorem cycleClass_gysinPullback_self (f : X ⟶ Y) (i : ℤ)
    (β : chowGroup (fieldChowSituation k) Y.obj.hom ((T.dimension Y : ℤ) - i)) :
    T.cycleClass X i (gysinPullback f ((T.dimension Y : ℤ) - i) β ((T.dimension X : ℤ) - i)) =
      T.pullback f (2 * i) (T.cycleClass Y i β) := by
  rw [T.cycleClass_gysinPullback, DirectSum.of_eq_same]

/-- Axiom (C)(a) away from the degree of `β`: for `β ∈ CH^i(Y)` the part of `f^!β` of
codimension `j ≠ i` has cycle class zero. -/
theorem cycleClass_gysinPullback_of_ne (f : X ⟶ Y) {i j : ℤ} (hij : i ≠ j)
    (β : chowGroup (fieldChowSituation k) Y.obj.hom ((T.dimension Y : ℤ) - i)) :
    T.cycleClass X j (gysinPullback f ((T.dimension Y : ℤ) - i) β ((T.dimension X : ℤ) - j)) =
      0 := by
  rw [T.cycleClass_gysinPullback, DirectSum.of_eq_of_ne _ _ _ (by omega)]

/-- Axiom (C)(c) in the degree `r + s`: `γ((α · β)^{r+s}) = γ(α) ∪ γ(β)` for `α ∈ CH^r(X)` and
`β ∈ CH^s(X)`. -/
theorem cycleClass_diagonalIntersectionProduct_self (r s : ℤ)
    (α : chowGroup (fieldChowSituation k) X.obj.hom ((T.dimension X : ℤ) - r))
    (β : chowGroup (fieldChowSituation k) X.obj.hom ((T.dimension X : ℤ) - s)) :
    T.cycleClass X (r + s) (diagonalIntersectionProduct k X.obj.hom ((T.dimension X : ℤ) - r)
        ((T.dimension X : ℤ) - s) α β ((T.dimension X : ℤ) - (r + s))) =
      (T.H X).evenCup r s (T.cycleClass X r α) (T.cycleClass X s β) := by
  rw [T.cycleClass_diagonalIntersectionProduct, DirectSum.of_eq_same]

/-- Axiom (C)(c) away from the degree `r + s`: the part of `α · β` of codimension
`j ≠ r + s` has cycle class zero. -/
theorem cycleClass_diagonalIntersectionProduct_of_ne {r s j : ℤ} (hj : r + s ≠ j)
    (α : chowGroup (fieldChowSituation k) X.obj.hom ((T.dimension X : ℤ) - r))
    (β : chowGroup (fieldChowSituation k) X.obj.hom ((T.dimension X : ℤ) - s)) :
    T.cycleClass X j (diagonalIntersectionProduct k X.obj.hom ((T.dimension X : ℤ) - r)
        ((T.dimension X : ℤ) - s) α β ((T.dimension X : ℤ) - j)) = 0 := by
  rw [T.cycleClass_diagonalIntersectionProduct, DirectSum.of_eq_of_ne _ _ _ (by omega)]

/-- The class of a point is nonzero: the cycle class map of a classical Weil cohomology theory
is not the zero map. -/
theorem cycleClass_point_ne_zero :
    T.cycleClass (point k) 0
        (fundamentalChowClass (fieldChowSituation k) (point k).obj.hom
          ((T.dimension (point k) : ℤ) - 0)) ≠ 0 := by
  intro h
  have h1 := T.integration_cycleClass_point
  rw [h] at h1
  simp at h1

end ClassicalWeilCohomology

end Stacks.WeilCohomology

end

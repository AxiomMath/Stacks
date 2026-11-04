module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfAdjointFunctor
public import StacksFrontier.Cotangent.ThreefoldPolynomialSite

/-!
# The threefold site over the two-term sites of the base and of the total ring

Let `A → B → C` be ring maps and let `C_{C/B/A}` be the site of polynomial towers of Tag 08QT,
with its functors `u₁` and `u₂` to the two-term sites `C_{B/A}` and `C_{C/A}`. This file builds
the fibred-category structure of `u₁`, the right adjoints of `u₁` and `u₂`, the final objects of
their fibres, and the identities `Lg_{i,!} ∘ g_i⁻¹ = id` of Tag 08QW for `i = 1, 2`. The case
`i = 3` is `CommAlgCat.derivedLowerShriekThirdInverseImageIso`, and the whole of Tag 08QW is
`CommAlgCat.derivedLowerShriek_comp_inverseImage_polynomialTower`.

Given a tower `(P → B, Q → C)` and a morphism `(P' → B) ⟶ (P → B)` of `C_{B/A}`, that is an
`A`-algebra map `P → P'` over `B`, the base change `Q' = P' ⊗_P Q` carries an augmentation to
`C` and makes `(P' → B, Q' → C)` a polynomial tower; the resulting morphism

```
(P' → B, Q' → C) ⟶ (P → B, Q → C)
```

of `C_{C/B/A}` is strongly cartesian over `C_{B/A}`, so `u₁` is a fibred category.

Both `u₁` and `u₂` have right adjoints, given on an object of the target by the final object of
the fibre over it:

```
s₁ (P → B) = (P → B, P → C),     s₂ (Q → C) = (A → B, Q → C),
```

with `u₁ ∘ s₁ = id` and `u₂ ∘ s₂ = id` and with `s₁`, `s₂` fully faithful. Hence `g_i⁻¹`, which
is restriction along `u_i`, is fully faithful with an exact right adjoint, and the identity
`Lg_{i,!} ∘ g_i⁻¹ = id` of Tag 08QW follows for `i = 1, 2` from Tag 08Q7 in the form
`Stacks.ChaoticSite.abelianDerivedLowerShriekInverseImageIso`.

## Main definitions

* `CommAlgCat.TowerBaseExtension`: a tower `(P → B, Q → C)` together with a morphism
  `(P → B) ⟶ (P' → B)` of augmented polynomial algebras, the data a cartesian lift is formed
  from.
* `CommAlgCat.TowerBaseExtension.pullbackAlgebra` and
  `CommAlgCat.TowerBaseExtension.pullbackAugmentation`: the algebra `P' ⊗_P Q` and its
  augmentation `p' ⊗ q ↦ p' · β(q)` to `C`.
* `CommAlgCat.TowerBaseExtension.pullbackTower`: the tower `(P' → B, P' ⊗_P Q → C)`.
* `CommAlgCat.TowerBaseExtension.toPullbackTower`: the morphism of towers
  `(P → B, Q → C) ⟶ (P' → B, P' ⊗_P Q → C)`, which in `C_{C/B/A}` points the other way.
* `CommAlgCat.TowerBaseExtension.PullbackCone` and
  `CommAlgCat.TowerBaseExtension.PullbackCone.lift`: a tower `Z` receiving `(P → B, Q → C)`
  through a morphism whose left component factors through `P'`, and the morphism
  `(P' → B, P' ⊗_P Q → C) ⟶ Z` the universal property of `P' ⊗_P Q` produces.
* `CommAlgCat.initialAugmentation`: `A` itself, as a polynomial `A`-algebra augmented to `B`.
* `CommAlgCat.secondFiberTower`: the tower `(A → B, Q → C)` attached to an object `(Q → C)` of
  `C_{C/A}`.
* `CommAlgCat.firstFiberTower` and `CommAlgCat.firstFiberFunctor`: the tower `(P → B, P → C)`
  attached to an object `(P → B)` of `C_{B/A}`, and the functor it defines.
* `CommAlgCat.secondFiberFunctor`: `(Q → C) ↦ (A → B, Q → C)`, as a functor.

## Main results

* `CommAlgCat.TowerBaseExtension.PullbackCone.existsUnique_lift`: **the universal property of
  the base change.** There is exactly one morphism `(P' → B, P' ⊗_P Q → C) ⟶ Z` of towers with a
  given left component `P' → P''` through which a given `(P → B, Q → C) ⟶ Z` factors.
* `CommAlgCat.TowerBaseExtension.isStronglyCartesian_toPullbackTower`: the morphism of
  `C_{C/B/A}` attached to a `TowerBaseExtension` is strongly cartesian over `C_{B/A}`.
* `CommAlgCat.polynomialTowerFirst_isFibered`: **`C_{C/B/A}` is a fibred category over
  `C_{B/A}`**, which is the first claim of the proof of Tag 08QW.
* `CommAlgCat.secondFiberTowerIsTerminal` and
  `CommAlgCat.hasTerminal_polynomialTowerSecondFiber`: **the fibre category of `u₂` over
  `(Q → C)` has a final object**, namely `(A → B, Q → C)`.
* `CommAlgCat.firstFiberTowerIsTerminal` and
  `CommAlgCat.hasTerminal_polynomialTowerFirstFiber`: **the fibre category of `u₁` over
  `(P → B)` has a final object**, namely `(P → B, P → C)`, which is the initial object of
  `C_{C/P}`.
* `CommAlgCat.firstFiberHomEquiv` and `CommAlgCat.secondFiberHomEquiv`: a morphism of towers out
  of `(P → B, P → C)` is its left component, and a morphism of towers out of `(A → B, Q → C)` is
  its right component.
* `CommAlgCat.polynomialTowerFirstAdjunction` and
  `CommAlgCat.polynomialTowerSecondAdjunction`: **`u₁` and `u₂` have right adjoints**, together
  with `CommAlgCat.fullyFaithfulFirstFiberFunctor` and
  `CommAlgCat.fullyFaithfulSecondFiberFunctor`, which say those right adjoints are fully
  faithful.
* `CommAlgCat.derivedLowerShriekFirstInverseImageIso` and
  `CommAlgCat.derivedLowerShriekSecondInverseImageIso`: **Tag 08QW for `i = 1` and `i = 2`**,
  that is `Lg_{i,!} ∘ g_i⁻¹ = id` on `D(Ab)`.

## Implementation notes

The source proves the cases `i = 1, 2` of Tag 08QW by Tag 08PJ, which computes `L_n g_{i,!}` as
the fibrewise homology, and for that it asserts that `C_{C/B/A}` is a fibred category over
`C_{C/A}` as well as over `C_{B/A}`, with the lift of `(Q' → C) ⟶ (Q → C)` at `(P → B, Q → C)`
taken to be `(P → B, Q' → C)`. **That lift is not an object of `C_{C/B/A}`**: `Q'` need not be a
polynomial algebra over `P`. Worse, no lift can be strongly cartesian, so `u₂` is *not* a fibred
category. Take `A = B = C = k[ε]/(ε²)` with the identity maps, `P = Q = A[x]` with `x ↦ 0` in
both `B` and `C`, `Q' = A[z]` with `z ↦ 0`, and `ψ : Q → Q'` the map `x ↦ z²`. A tower
`(P'' → B, Q' → C)` through which `ψ` lifts forces `P'' ≅ A[z]` with `P'' → Q'` invertible,
because `A[z]` must be a polynomial algebra over `P''` and `P → P'' → Q'` must hit `z²`; so the
image of `P''` in `Q'` generates `Q'`. Now let `Z` be the tower `(A → B, A[t] → C)` with
`t ↦ 0`, and let `Q' → A[t]` be `z ↦ εt`. Composing with `ψ` gives `x ↦ (εt)² = 0`, which does
factor through `Z` because the zero map `P → A` is a morphism of towers; but a lift
`P'' → A` would have to send the generator `z` to an element of `A` whose image in `A[t]` is
`εt`, and there is none. The two cases are therefore proved here from Tag 08Q7 instead, through
the right adjoints of `u₁` and `u₂`, which needs no acyclicity hypothesis and no fibredness.

## References

* [Stacks Project, Tag 08QW](https://stacks.math.columbia.edu/tag/08QW)
* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Tag 08Q7](https://stacks.math.columbia.edu/tag/08Q7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-! ### The data of a cartesian lift -/

/-- A polynomial tower `(P → B, Q → C)` together with a morphism `(P → B) ⟶ (P' → B)` of
polynomial `A`-algebras augmented to `B`. In `C_{B/A}` this is a morphism
`(P' → B) ⟶ (P → B)`, and it is the data from which a strongly cartesian lift is formed. -/
structure TowerBaseExtension where
  /-- The tower `(P → B, Q → C)` being extended. -/
  tower : PolynomialTower A B C
  /-- The polynomial `A`-algebra `P' → B` the tower is extended to. -/
  base : PolynomialAugmentation A (towerBaseAlgebra A B)
  /-- The `A`-algebra map `P → P'` over `B`. -/
  map : tower.obj.left ⟶ base

variable {A B C}

namespace TowerBaseExtension

variable (e : TowerBaseExtension A B C)

/-- The polynomial `A`-algebra `P'` the tower is extended to. -/
abbrev targetAlgebra : CommAlgCat.{u} A := e.base.obj.left

/-- `P` acts on `P'` through the map `P → P'` of the extension. -/
instance algebraTargetAlgebra : Algebra ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra :=
  (CommAlgCat.Hom.hom e.map.hom.left).toRingHom.toAlgebra

/-- The map `P → P'` is a map of `A`-algebras, so `A` acts on `P'` through `P`. -/
instance isScalarTowerTargetAlgebra :
    IsScalarTower A ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra :=
  IsScalarTower.of_algebraMap_eq fun a =>
    ((CommAlgCat.Hom.hom e.map.hom.left).commutes a).symm

/-- The augmentation `P' → B` makes `B` an algebra over `P'`. -/
instance algebraTargetBase : Algebra ↑e.targetAlgebra B :=
  (CommAlgCat.Hom.hom e.base.obj.hom).toRingHom.toAlgebra

/-- The augmentation `P' → B` is a map of `A`-algebras, so `A` acts on `B` through `P'`. -/
instance isScalarTowerTargetBase : IsScalarTower A ↑e.targetAlgebra B :=
  IsScalarTower.of_algebraMap_eq fun a =>
    ((CommAlgCat.Hom.hom e.base.obj.hom).commutes a).symm

/-- `P'` acts on `C` through `P' → B → C`. -/
instance algebraTargetTotal : Algebra ↑e.targetAlgebra C :=
  ((algebraMap B C).comp (algebraMap ↑e.targetAlgebra B)).toAlgebra

/-- By construction the action of `P'` on `C` factors through `B`. -/
instance isScalarTowerTargetTotal : IsScalarTower ↑e.targetAlgebra B C :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `A` acts on `C` through `P'`. -/
instance isScalarTowerTargetAlgebraTotal : IsScalarTower A ↑e.targetAlgebra C :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_apply ↑e.targetAlgebra B C,
      ← IsScalarTower.algebraMap_apply A ↑e.targetAlgebra B]

/-- The augmentation `P → B` of the tower factors through `P'`: the composite `P → P' → B` is
`P → B`. -/
theorem algebraMap_targetAlgebra_base (p : ↑(towerLeftAlgebra e.tower.obj)) :
    algebraMap ↑e.targetAlgebra B
        (algebraMap ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra p) =
      algebraMap ↑(towerLeftAlgebra e.tower.obj) B p := by
  change algebraMap ↑e.targetAlgebra B ((CommAlgCat.Hom.hom e.map.hom.left) p) = _
  exact congrArg (fun k => (CommAlgCat.Hom.hom k) p) (Over.w e.map.hom)

/-- The action of `P` on `B` factors through `P'`. -/
instance isScalarTowerLeftTargetBase :
    IsScalarTower ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra B :=
  IsScalarTower.of_algebraMap_eq fun p => (e.algebraMap_targetAlgebra_base p).symm

/-- The action of `P` on `C` factors through `P'`. -/
instance isScalarTowerLeftTargetTotal :
    IsScalarTower ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra C :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [IsScalarTower.algebraMap_apply ↑e.targetAlgebra B C, e.algebraMap_targetAlgebra_base p,
      ← IsScalarTower.algebraMap_apply ↑(towerLeftAlgebra e.tower.obj) B C]

/-! ### The base-changed algebra -/

/-- `P' ⊗_P Q`, as an object of `CommAlgCat A`. It is the pushout of `P' ← P → Q`, with `A`
acting through the left factor. -/
abbrev pullbackAlgebra : CommAlgCat.{u} A :=
  CommAlgCat.of A
    (↑e.targetAlgebra ⊗[↑(towerLeftAlgebra e.tower.obj)] ↑(towerRightAlgebra e.tower.obj))

/-- The augmentation `P' ⊗_P Q → C` of the base-changed algebra: `p' ⊗ q ↦ p' · β(q)`, where
`β : Q → C` is the augmentation of the tower. -/
def pullbackAugmentation : ↑e.pullbackAlgebra →ₐ[↑e.targetAlgebra] C :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId ↑e.targetAlgebra C)
    (towerRightAugmentation e.tower)

/-- The augmentation of the base-changed algebra on a pure tensor. -/
@[simp]
theorem pullbackAugmentation_tmul (p : ↑e.targetAlgebra)
    (q : ↑(towerRightAlgebra e.tower.obj)) :
    e.pullbackAugmentation (p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q) =
      algebraMap ↑e.targetAlgebra C p *
        (CommAlgCat.Hom.hom e.tower.obj.right.hom) q := by
  simp [pullbackAugmentation, towerRightAugmentation, Algebra.ofId_apply]

/-! ### The base-changed tower -/

/-- The tower `(P' → B, P' ⊗_P Q → C)`, as an object of the comma category: the structure map
`P' → P' ⊗_P Q` is `p' ↦ p' ⊗ 1`. -/
def pullbackObj : TowerComma A B C where
  left := e.base
  right := Over.mk (CommAlgCat.ofHom ((e.pullbackAugmentation).restrictScalars A))
  hom := CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeLeft (S := A) :
      ↑e.targetAlgebra →ₐ[A] ↑e.pullbackAlgebra))

/-- The left component of the base-changed tower is `P' → B`. -/
@[simp]
theorem pullbackObj_left : e.pullbackObj.left = e.base := rfl

/-- The structure map `P' → P' ⊗_P Q` of the base-changed tower sends `p'` to `p' ⊗ 1`. -/
@[simp]
theorem pullbackObj_hom_apply (p : ↑e.targetAlgebra) :
    (CommAlgCat.Hom.hom e.pullbackObj.hom) p =
      p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] (1 : ↑(towerRightAlgebra e.tower.obj)) :=
  rfl

/-- The augmentation of the right component of the base-changed tower is
`pullbackAugmentation`. -/
@[simp]
theorem pullbackObj_right_hom_apply (z : ↑e.pullbackAlgebra) :
    (CommAlgCat.Hom.hom e.pullbackObj.right.hom) z = e.pullbackAugmentation z :=
  rfl

/-- `P' ⊗_P Q` is a polynomial algebra over `P'`: if `Q = P[κ]` then `P' ⊗_P Q = P'[κ]`. -/
theorem isPolynomialAlgebra_pullbackAlgebra :
    IsPolynomialAlgebra ↑(towerLeftAlgebra e.pullbackObj)
      (CommAlgCat.of ↑(towerLeftAlgebra e.pullbackObj) ↑(towerRightAlgebra e.pullbackObj)) := by
  obtain ⟨κ, ⟨ε⟩⟩ := e.tower.property.1
  refine ⟨κ, ⟨?_⟩⟩
  have hf : Function.Bijective
      (Algebra.TensorProduct.map (S := ↑e.targetAlgebra)
        (AlgHom.id ↑e.targetAlgebra ↑e.targetAlgebra) ε.toAlgHom) :=
    Algebra.TensorProduct.map_bijective
      (f := (AlgHom.id ↑e.targetAlgebra ↑e.targetAlgebra).restrictScalars
        ↑(towerLeftAlgebra e.tower.obj)) (g := ε.toAlgHom) Function.bijective_id ε.bijective
  have τ := (MvPolynomial.scalarRTensorAlgEquiv (R := ↑(towerLeftAlgebra e.tower.obj))
      (N := ↑e.targetAlgebra) (σ := κ)).symm.trans
    (AlgEquiv.ofBijective (Algebra.TensorProduct.map
      (AlgHom.id ↑e.targetAlgebra ↑e.targetAlgebra) ε.toAlgHom) hf)
  exact AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun r => τ.commutes r

/-- `(P' → B, P' ⊗_P Q → C)` is a polynomial tower. -/
theorem isPolynomialTower_pullbackObj : IsPolynomialTower A B C e.pullbackObj := by
  refine ⟨e.isPolynomialAlgebra_pullbackAlgebra, ?_⟩
  have key : ∀ p : ↑e.targetAlgebra,
      e.pullbackAugmentation (p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)]
          (1 : ↑(towerRightAlgebra e.tower.obj))) =
        algebraMap B C (algebraMap ↑e.targetAlgebra B p) := by
    intro p
    rw [e.pullbackAugmentation_tmul, map_one, mul_one]
    rfl
  exact CommAlgCat.hom_ext (AlgHom.ext key)

/-- The tower `(P' → B, P' ⊗_P Q → C)`. In `C_{C/B/A}` it is the domain of the strongly
cartesian morphism lifting `(P' → B) ⟶ (P → B)`. -/
def pullbackTower : PolynomialTower A B C :=
  ⟨e.pullbackObj, e.isPolynomialTower_pullbackObj⟩

/-! ### The morphism of towers -/

/-- The morphism of towers `(P → B, Q → C) ⟶ (P' → B, P' ⊗_P Q → C)`: the map `P → P'` of the
extension on the left, and `q ↦ 1 ⊗ q` on the right. In `C_{C/B/A}` it points the other way. -/
def toPullbackObj : e.tower.obj ⟶ e.pullbackObj where
  left := e.map
  right := Over.homMk
    (CommAlgCat.ofHom ((Algebra.TensorProduct.includeRight
      (R := ↑(towerLeftAlgebra e.tower.obj)) (A := ↑e.targetAlgebra)
      (B := ↑(towerRightAlgebra e.tower.obj))).restrictScalars A)) (by
      have key : ∀ q : ↑(towerRightAlgebra e.tower.obj),
          e.pullbackAugmentation ((1 : ↑e.targetAlgebra) ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q) =
            (CommAlgCat.Hom.hom e.tower.obj.right.hom) q := by
        intro q
        rw [e.pullbackAugmentation_tmul, map_one, one_mul]
      exact CommAlgCat.hom_ext (AlgHom.ext key))
  w := by
    have key : ∀ p : ↑(towerLeftAlgebra e.tower.obj),
        (algebraMap ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra p)
            ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)]
              (1 : ↑(towerRightAlgebra e.tower.obj)) =
          (1 : ↑e.targetAlgebra) ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)]
            (algebraMap ↑(towerLeftAlgebra e.tower.obj)
              ↑(towerRightAlgebra e.tower.obj) p) :=
      fun p => Algebra.TensorProduct.tmul_one_eq_one_tmul p
    exact CommAlgCat.hom_ext (AlgHom.ext key)

/-- The morphism of towers `(P → B, Q → C) ⟶ (P' → B, P' ⊗_P Q → C)`. -/
def toPullbackTower : e.tower ⟶ e.pullbackTower :=
  ⟨e.toPullbackObj⟩

/-! ### The universal property of the base change -/

/-- A tower `Z = (P'' → B, Q'' → C)` receiving a morphism from `(P → B, Q → C)`, together with a
factorization `P → P' → P''` of its left component through `P'`. This is the data against which
the universal property of the base change is tested. -/
structure PullbackCone where
  /-- The receiving tower `Z`. -/
  tower : PolynomialTower A B C
  /-- The map `P' → P''` over `B`. -/
  map : e.base ⟶ tower.obj.left
  /-- The morphism of towers `(P → B, Q → C) ⟶ Z`. -/
  hom : e.tower ⟶ tower
  /-- Its left component is the composite `P → P' → P''`. -/
  fac : hom.hom.left = e.map ≫ map

namespace PullbackCone

variable {e} (c : e.PullbackCone)

/-- `P'` acts on `P''` through the map `P' → P''` of the cone. -/
instance algebraTargetConeLeft :
    Algebra ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj) :=
  (CommAlgCat.Hom.hom c.map.hom.left).toRingHom.toAlgebra

/-- `P'` acts on `Q''` through `P' → P'' → Q''`. -/
instance algebraTargetConeRight :
    Algebra ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj) :=
  ((algebraMap ↑(towerLeftAlgebra c.tower.obj) ↑(towerRightAlgebra c.tower.obj)).comp
    (algebraMap ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj))).toAlgebra

/-- `P` acts on `Q''` through `P → P' → P'' → Q''`. -/
instance algebraLeftConeRight :
    Algebra ↑(towerLeftAlgebra e.tower.obj) ↑(towerRightAlgebra c.tower.obj) :=
  ((algebraMap ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj)).comp
    (algebraMap ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra)).toAlgebra

/-- By construction the action of `P` on `Q''` factors through `P'`. -/
instance isScalarTowerLeftTargetConeRight :
    IsScalarTower ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra
      ↑(towerRightAlgebra c.tower.obj) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- By construction the action of `P'` on `Q''` factors through `P''`. -/
instance isScalarTowerTargetConeLeftRight :
    IsScalarTower ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj)
      ↑(towerRightAlgebra c.tower.obj) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The augmentation `P' → B` factors through `P''`: the composite `P' → P'' → B` is
`P' → B`. -/
theorem algebraMap_coneLeft_base (p : ↑e.targetAlgebra) :
    algebraMap ↑(towerLeftAlgebra c.tower.obj) B
        (algebraMap ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj) p) =
      algebraMap ↑e.targetAlgebra B p := by
  change algebraMap ↑(towerLeftAlgebra c.tower.obj) B
    ((CommAlgCat.Hom.hom c.map.hom.left) p) = _
  exact congrArg (fun k => (CommAlgCat.Hom.hom k) p) (Over.w c.map.hom)

/-- `A` acts on `Q''` through `P'`. -/
instance isScalarTowerTargetConeRight :
    IsScalarTower A ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj)
      ↑(towerRightAlgebra c.tower.obj), ← IsScalarTower.algebraMap_apply A ↑e.targetAlgebra
      ↑(towerLeftAlgebra c.tower.obj), IsScalarTower.algebraMap_apply A
      ↑(towerLeftAlgebra c.tower.obj) ↑(towerRightAlgebra c.tower.obj)]

/-- The right leg of the universal property: the augmentation `Q → Q''` of the cone, read as a
map of `P`-algebras for the action of `P` on `Q''` through `P'`. -/
def rightLeg : ↑(towerRightAlgebra e.tower.obj) →ₐ[↑(towerLeftAlgebra e.tower.obj)]
    ↑(towerRightAlgebra c.tower.obj) where
  toRingHom := (CommAlgCat.Hom.hom c.hom.hom.right.left).toRingHom
  commutes' p := by
    change (CommAlgCat.Hom.hom c.hom.hom.right.left)
        (algebraMap ↑(towerLeftAlgebra e.tower.obj) ↑(towerRightAlgebra e.tower.obj) p) =
      algebraMap ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj)
        (algebraMap ↑(towerLeftAlgebra e.tower.obj) ↑e.targetAlgebra p)
    rw [towerRight_hom_apply c.hom.hom p]
    change algebraMap ↑(towerLeftAlgebra c.tower.obj) ↑(towerRightAlgebra c.tower.obj)
        ((CommAlgCat.Hom.hom c.hom.hom.left.hom.left) p) = _
    rw [c.fac]
    rfl

/-- The map `P' ⊗_P Q → Q''` determined by `P' → P''` and `Q → Q''`: it sends `p' ⊗ q` to
`p' · ψ(q)`. -/
def desc : ↑e.pullbackAlgebra →ₐ[↑e.targetAlgebra] ↑(towerRightAlgebra c.tower.obj) :=
  Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj)) c.rightLeg

/-- The map `desc` sends `p' ⊗ q` to `p' · ψ(q)`. -/
@[simp]
theorem desc_tmul (p : ↑e.targetAlgebra) (q : ↑(towerRightAlgebra e.tower.obj)) :
    c.desc (p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q) =
      algebraMap ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj) p *
        (CommAlgCat.Hom.hom c.hom.hom.right.left) q := by
  simp [desc, rightLeg, Algebra.ofId_apply]

/-- The morphism of towers `(P' → B, P' ⊗_P Q → C) ⟶ Z` produced by the universal property of
the base change. -/
def liftObj : e.pullbackObj ⟶ c.tower.obj where
  left := c.map
  right := Over.homMk (CommAlgCat.ofHom (c.desc.restrictScalars A)) (by
    have key : ∀ z : ↑e.pullbackAlgebra,
        (CommAlgCat.Hom.hom c.tower.obj.right.hom) (c.desc z) =
          e.pullbackAugmentation z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul p q =>
          rw [c.desc_tmul, map_mul, e.pullbackAugmentation_tmul,
            towerRightAugmentation_hom_apply c.hom.hom q]
          congr 1
          change (CommAlgCat.Hom.hom c.tower.obj.right.hom)
              ((CommAlgCat.Hom.hom c.tower.obj.hom)
                (algebraMap ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj) p)) = _
          rw [towerRight_hom_towerMap_apply c.tower]
          change algebraMap B C (algebraMap ↑(towerLeftAlgebra c.tower.obj) B
            (algebraMap ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj) p)) = _
          rw [c.algebraMap_coneLeft_base p]
          rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    exact CommAlgCat.hom_ext (AlgHom.ext key))
  w := by
    have key : ∀ p : ↑e.targetAlgebra,
        algebraMap ↑(towerLeftAlgebra c.tower.obj) ↑(towerRightAlgebra c.tower.obj)
            (algebraMap ↑e.targetAlgebra ↑(towerLeftAlgebra c.tower.obj) p) =
          c.desc (p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)]
            (1 : ↑(towerRightAlgebra e.tower.obj))) := by
      intro p
      rw [c.desc_tmul, map_one, mul_one]
      rfl
    exact CommAlgCat.hom_ext (AlgHom.ext key)

/-- The morphism of towers `(P' → B, P' ⊗_P Q → C) ⟶ Z` produced by the universal property. -/
def lift : e.pullbackTower ⟶ c.tower := ⟨c.liftObj⟩

/-- The left component of `lift` is the given map `P' → P''`. -/
@[simp]
theorem lift_hom_left : (c.lift).hom.left = c.map := rfl

/-- The right component of `lift` sends `p' ⊗ q` to `p' · ψ(q)`. -/
@[simp]
theorem lift_hom_right_left_tmul (p : ↑e.targetAlgebra)
    (q : ↑(towerRightAlgebra e.tower.obj)) :
    (CommAlgCat.Hom.hom (c.lift).hom.right.left)
        (p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q) =
      algebraMap ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj) p *
        (CommAlgCat.Hom.hom c.hom.hom.right.left) q :=
  c.desc_tmul p q

/-- The morphism produced by the universal property is a factorization of the cone. -/
theorem toPullbackTower_comp_lift : e.toPullbackTower ≫ c.lift = c.hom := by
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · exact c.fac.symm
  · have key : ∀ q : ↑(towerRightAlgebra e.tower.obj),
        (CommAlgCat.Hom.hom (c.lift).hom.right.left)
            ((1 : ↑e.targetAlgebra) ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q) =
          (CommAlgCat.Hom.hom c.hom.hom.right.left) q := by
      intro q
      rw [c.lift_hom_right_left_tmul, map_one, one_mul]
    exact Over.OverMorphism.ext (CommAlgCat.hom_ext (AlgHom.ext key))

/-- A morphism out of the base change is determined by its left component and the
factorization it provides: the base change is generated by the images of `P'` and `Q`. -/
theorem lift_uniq (χ : e.pullbackTower ⟶ c.tower) (hleft : χ.hom.left = c.map)
    (hfac : e.toPullbackTower ≫ χ = c.hom) : χ = c.lift := by
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · exact hleft
  · have hright : ∀ q : ↑(towerRightAlgebra e.tower.obj),
        (CommAlgCat.Hom.hom χ.hom.right.left)
            ((1 : ↑e.targetAlgebra) ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q) =
          (CommAlgCat.Hom.hom c.hom.hom.right.left) q := fun q =>
      congrArg (fun k => (CommAlgCat.Hom.hom k.hom.right.left) q) hfac
    have hleft' : ∀ p : ↑e.targetAlgebra,
        (CommAlgCat.Hom.hom χ.hom.right.left)
            (p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)]
              (1 : ↑(towerRightAlgebra e.tower.obj))) =
          algebraMap ↑e.targetAlgebra ↑(towerRightAlgebra c.tower.obj) p := by
      intro p
      rw [← e.pullbackObj_hom_apply p]
      have hw : (CommAlgCat.Hom.hom c.tower.obj.hom)
            ((CommAlgCat.Hom.hom χ.hom.left.hom.left) p) =
          (CommAlgCat.Hom.hom χ.hom.right.left)
            ((CommAlgCat.Hom.hom e.pullbackObj.hom) p) :=
        congrArg (fun k => (CommAlgCat.Hom.hom k) p) χ.hom.w
      rw [← hw, hleft]
      rfl
    have key : ∀ z : ↑e.pullbackAlgebra,
        (CommAlgCat.Hom.hom χ.hom.right.left) z =
          (CommAlgCat.Hom.hom (c.lift).hom.right.left) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul p q =>
          have hsplit : p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q =
              (p ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)]
                (1 : ↑(towerRightAlgebra e.tower.obj))) *
                ((1 : ↑e.targetAlgebra) ⊗ₜ[↑(towerLeftAlgebra e.tower.obj)] q) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [hsplit]
          refine Eq.trans (map_mul _ _ _) (Eq.trans ?_ (map_mul _ _ _).symm)
          rw [hleft' p, hright q, c.lift_hom_right_left_tmul p 1,
            c.lift_hom_right_left_tmul 1 q]
          simp only [map_one, mul_one, one_mul]
      | add x y hx hy =>
          exact (map_add _ x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    exact Over.OverMorphism.ext (CommAlgCat.hom_ext (AlgHom.ext key))

/-- **The universal property of the base change.** There is exactly one morphism of towers
`(P' → B, P' ⊗_P Q → C) ⟶ Z` with left component the given `P' → P''` through which the given
morphism `(P → B, Q → C) ⟶ Z` factors. -/
theorem existsUnique_lift :
    ∃! χ : e.pullbackTower ⟶ c.tower,
      χ.hom.left = c.map ∧ e.toPullbackTower ≫ χ = c.hom :=
  ⟨c.lift, ⟨c.lift_hom_left, c.toPullbackTower_comp_lift⟩,
    fun χ hχ => c.lift_uniq χ hχ.1 hχ.2⟩

end PullbackCone

/-! ### The fibred structure of `u₁` -/

/-- The morphism of towers of an extension lies over the map `P → P'` for `u₁`. -/
theorem isHomLift_toPullbackTower :
    (polynomialTowerFirstAugmentations A B C).IsHomLift e.map e.toPullbackTower :=
  CategoryTheory.Functor.IsHomLift.map e.toPullbackTower

/-- The morphism of `C_{C/B/A}` attached to an extension lies over the corresponding morphism
`(P' → B) ⟶ (P → B)` of `C_{B/A}`. -/
theorem isHomLift_op_toPullbackTower :
    (polynomialTowerFirst A B C).IsHomLift e.map.op e.toPullbackTower.op :=
  CategoryTheory.isHomLift_op (polynomialTowerFirstAugmentations A B C) e.map
    e.toPullbackTower (inst := e.isHomLift_toPullbackTower)

/-- **The base change is strongly cartesian.** For a tower `(P → B, Q → C)` and a morphism
`(P' → B) ⟶ (P → B)` of `C_{B/A}`, the morphism
`(P' → B, P' ⊗_P Q → C) ⟶ (P → B, Q → C)` of `C_{C/B/A}` is strongly cartesian over
`C_{B/A}`. -/
theorem isStronglyCartesian_toPullbackTower :
    (polynomialTowerFirst A B C).IsStronglyCartesian e.map.op e.toPullbackTower.op := by
  have := e.isHomLift_op_toPullbackTower
  have left_eq : ∀ {X Y : (PolynomialTower A B C)ᵒᵖ}
      (f : (polynomialTowerFirst A B C).obj X ⟶ _) (φ : X ⟶ Y),
      (polynomialTowerFirst A B C).IsHomLift f φ → f.unop = φ.unop.hom.left :=
    fun f φ h => @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
      (polynomialTowerFirstAugmentations A B C) _ _ f.unop φ.unop
      (CategoryTheory.isHomLift_unop (polynomialTowerFirstAugmentations A B C) f φ (inst := h))
  constructor
  intro a' g φ' hφ'
  have hfac : e.map ≫ g.unop = φ'.unop.hom.left :=
    left_eq (X := a') (Y := Opposite.op e.tower) (g ≫ e.map.op) φ' hφ'
  let c : e.PullbackCone := ⟨a'.unop, g.unop, φ'.unop, hfac.symm⟩
  refine ⟨c.lift.op, ⟨?_, ?_⟩, ?_⟩
  · exact CategoryTheory.isHomLift_op (polynomialTowerFirstAugmentations A B C) g.unop
      c.lift (inst := CategoryTheory.Functor.IsHomLift.map c.lift)
  · exact Quiver.Hom.unop_inj c.toPullbackTower_comp_lift
  · intro χ hχ
    exact Quiver.Hom.unop_inj
      (c.lift_uniq χ.unop (left_eq g χ hχ.1).symm (Quiver.Hom.op_inj hχ.2))

end TowerBaseExtension

/-- **`C_{C/B/A}` is a fibred category over `C_{B/A}`**, by base change: a morphism
`(P' → B) ⟶ (P → B)` of `C_{B/A}` and a tower `(P → B, Q → C)` over `(P → B)` have the strongly
cartesian lift `(P' → B, P' ⊗_P Q → C) ⟶ (P → B, Q → C)`. This is the first claim of the proof
of Tag 08QW. -/
instance polynomialTowerFirst_isFibered :
    (polynomialTowerFirst A B C).IsFibered :=
  .of_exists_isStronglyCartesian fun a R f =>
    ⟨_, _, TowerBaseExtension.isStronglyCartesian_toPullbackTower ⟨a.unop, R.unop, f.unop⟩⟩

/-! ### The fibre of `u₂` -/

/-- An `A`-algebra map out of `A` is the structure map, so `A` is an initial object of
`CommAlgCat A`. -/
theorem commAlgCat_self_hom_ext {X : CommAlgCat.{u} A} (f g : CommAlgCat.of A A ⟶ X) : f = g :=
  CommAlgCat.hom_ext <| AlgHom.ext fun a =>
    ((CommAlgCat.Hom.hom f).commutes a).trans ((CommAlgCat.Hom.hom g).commutes a).symm

variable (A B C)

/-- `A` itself, as a polynomial `A`-algebra augmented to `B`. It is the initial object of the
category of polynomial `A`-algebras augmented to `B`. -/
def initialAugmentation : PolynomialAugmentation A (towerBaseAlgebra A B) :=
  ⟨Over.mk (CommAlgCat.ofHom (Algebra.ofId A B)),
    ⟨PEmpty.{u + 1}, ⟨MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}⟩⟩⟩

variable {A B C}

/-- The tower `(A → B, Q → C)` attached to an object `(Q → C)` of `C_{C/A}`. -/
def secondFiberObj (L : PolynomialAugmentation A (towerTotalAlgebra A C)) :
    TowerComma A B C where
  left := initialAugmentation A B
  right := L.obj
  hom := CommAlgCat.ofHom (Algebra.ofId A ↑L.obj.left)

/-- `(A → B, Q → C)` is a polynomial tower: `Q` is a polynomial `A`-algebra by assumption, and
both composites `A → Q → C` and `A → B → C` are the structure map of `C`. -/
theorem isPolynomialTower_secondFiberObj
    (L : PolynomialAugmentation A (towerTotalAlgebra A C)) :
    IsPolynomialTower A B C (secondFiberObj (B := B) L) := by
  refine ⟨?_, commAlgCat_self_hom_ext _ _⟩
  obtain ⟨κ, ⟨ε⟩⟩ := L.property
  exact ⟨κ, ⟨AlgEquiv.ofRingEquiv (f := ε.toRingEquiv) fun a => ε.commutes a⟩⟩

/-- The tower `(A → B, Q → C)`, the final object of the fibre of `u₂` over `(Q → C)`. -/
def secondFiberTower (L : PolynomialAugmentation A (towerTotalAlgebra A C)) :
    PolynomialTower A B C :=
  ⟨secondFiberObj L, isPolynomialTower_secondFiberObj L⟩

/-- The image of the tower `(A → B, Q → C)` under `u₂` is `(Q → C)`. -/
@[simp]
theorem polynomialTowerSecond_obj_secondFiberTower
    (L : PolynomialAugmentation A (towerTotalAlgebra A C)) :
    (polynomialTowerSecond A B C).obj (Opposite.op (secondFiberTower L)) = Opposite.op L :=
  rfl

/-- The morphism of towers `(A → B, Q → C) ⟶ Z` for a tower `Z` whose image under `u₂` is
`(Q → C)`: the structure map of `A` on the left, and the identity on the right. -/
def fromSecondFiberTower (Z : PolynomialTower A B C) :
    secondFiberTower (B := B) ((polynomialTowerSecondAugmentations A B C).obj Z) ⟶ Z :=
  ⟨{ left := ObjectProperty.homMk (Over.homMk
        (CommAlgCat.ofHom (Algebra.ofId A ↑(towerLeftAlgebra Z.obj)))
        (commAlgCat_self_hom_ext _ _))
     right := 𝟙 _
     w := commAlgCat_self_hom_ext _ _ }⟩

/-- Every object of the fibre of `u₂` over `(Q → C)` admits a morphism to `(A → B, Q → C)` in
that fibre. -/
theorem nonempty_hom_secondFiberTower
    (L : PolynomialAugmentation A (towerTotalAlgebra A C))
    (Y : (polynomialTowerSecond A B C).Fiber (Opposite.op L)) :
    Nonempty (Y ⟶ Functor.Fiber.mk
      (polynomialTowerSecond_obj_secondFiberTower (B := B) L)) := by
  obtain ⟨Z, hZ⟩ := Y
  obtain rfl : L = (polynomialTowerSecondAugmentations A B C).obj Z.unop :=
    (Opposite.op_injective hZ).symm
  exact ⟨⟨(fromSecondFiberTower Z.unop).op,
    CategoryTheory.Functor.IsHomLift.map (fromSecondFiberTower Z.unop).op⟩⟩

/-- There is at most one morphism from an object of the fibre of `u₂` over `(Q → C)` to
`(A → B, Q → C)`: the left component of a morphism of towers out of `(A → B, Q → C)` is the
structure map of `A`, and the right component is forced by the fibre condition. -/
theorem subsingleton_hom_secondFiberTower
    (L : PolynomialAugmentation A (towerTotalAlgebra A C))
    (Y : (polynomialTowerSecond A B C).Fiber (Opposite.op L)) :
    Subsingleton (Y ⟶ Functor.Fiber.mk
      (polynomialTowerSecond_obj_secondFiberTower (B := B) L)) := by
  obtain ⟨Z, hZ⟩ := Y
  obtain rfl : L = (polynomialTowerSecondAugmentations A B C).obj Z.unop :=
    (Opposite.op_injective hZ).symm
  refine ⟨fun m₁ m₂ => Functor.Fiber.hom_ext <| Quiver.Hom.unop_inj <|
    ObjectProperty.hom_ext _ <| CommaMorphism.ext
      (ObjectProperty.hom_ext _ (Over.OverMorphism.ext (commAlgCat_self_hom_ext _ _))) ?_⟩
  have hid : ∀ m : Z ⟶ Opposite.op (secondFiberTower (B := B)
      ((polynomialTowerSecondAugmentations A B C).obj Z.unop)),
      (polynomialTowerSecond A B C).IsHomLift (𝟙 ((polynomialTowerSecond A B C).obj Z)) m →
      (polynomialTowerSecond A B C).map m = 𝟙 _ :=
    fun m hm => (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ _ Z _ _ m hm).symm
  have h : (polynomialTowerSecondAugmentations A B C).map m₁.1.unop =
      (polynomialTowerSecondAugmentations A B C).map m₂.1.unop :=
    Quiver.Hom.op_inj ((hid _ m₁.2).trans (hid _ m₂.2).symm)
  exact congrArg CategoryTheory.InducedCategory.Hom.hom h

/-- **The fibre category of `u₂` over `(Q → C)` has a final object**, namely `(A → B, Q → C)`.
Beware the reversal of arrows: in `C_{C/B/A}` a morphism to it is a morphism of towers out of
`(A → B, Q → C)`, whose left component is the structure map of `A` and whose right component the
fibre condition forces to be the identity. -/
def secondFiberTowerIsTerminal
    (L : PolynomialAugmentation A (towerTotalAlgebra A C)) :
    Limits.IsTerminal (Functor.Fiber.mk
      (polynomialTowerSecond_obj_secondFiberTower (B := B) L)) :=
  Limits.IsTerminal.ofUniqueHom (fun Y => (nonempty_hom_secondFiberTower L Y).some)
    fun Y _ => (subsingleton_hom_secondFiberTower L Y).elim _ _

/-- The fibre category of `u₂` over `(Q → C)` has a final object. -/
theorem hasTerminal_polynomialTowerSecondFiber
    (L : PolynomialAugmentation A (towerTotalAlgebra A C)) :
    Limits.HasTerminal ((polynomialTowerSecond A B C).Fiber (Opposite.op L)) :=
  (secondFiberTowerIsTerminal (B := B) L).hasTerminal

/-! ### The right adjoint of `u₁` -/

variable (A B C)

/-- The tower `(P → B, P → C)` attached to a polynomial `A`-algebra `P` augmented to `B`: the
second layer adds no variables, and its augmentation is the composite `P → B → C`. -/
def firstFiberObj (P : PolynomialAugmentation A (towerBaseAlgebra A B)) : TowerComma A B C where
  left := P
  right := Over.mk (P.obj.hom ≫ towerBaseToTotal A B C)
  hom := 𝟙 _

/-- `(P → B, P → C)` is a polynomial tower: `P` is a polynomial algebra over itself on no
variables, and the composite `P → P → C` is `P → B → C` by construction. -/
theorem isPolynomialTower_firstFiberObj (P : PolynomialAugmentation A (towerBaseAlgebra A B)) :
    IsPolynomialTower A B C (firstFiberObj A B C P) :=
  ⟨⟨PEmpty.{u + 1}, ⟨MvPolynomial.isEmptyAlgEquiv _ _⟩⟩, Category.id_comp _⟩

/-- The tower `(P → B, P → C)`, as an object of `C_{C/B/A}`. -/
def firstFiberTower (P : PolynomialAugmentation A (towerBaseAlgebra A B)) :
    PolynomialTower A B C :=
  ⟨firstFiberObj A B C P, isPolynomialTower_firstFiberObj A B C P⟩

variable {A B C}

/-- The augmentation of the second layer of `(P → B, P → C)` is natural in `P`. -/
theorem firstFiber_comp_augmentation {P P' : PolynomialAugmentation A (towerBaseAlgebra A B)}
    (f : P.obj.left ⟶ P'.obj.left) (hf : f ≫ P'.obj.hom = P.obj.hom) :
    f ≫ P'.obj.hom ≫ towerBaseToTotal A B C = P.obj.hom ≫ towerBaseToTotal A B C := by
  rw [← Category.assoc, hf]

/-- A morphism `P → P'` into the first layer of a tower `(P' → B, Q' → C)` is compatible with
the augmentation `P → B → C` of `(P → B, P → C)`: the composite `P → P' → Q' → C` is
`P → B → C`. -/
theorem firstFiber_comp_tower_augmentation
    {P : PolynomialAugmentation A (towerBaseAlgebra A B)} {T : PolynomialTower A B C}
    (f : P.obj.left ⟶ T.obj.left.obj.left) (hf : f ≫ T.obj.left.obj.hom = P.obj.hom) :
    (f ≫ T.obj.hom) ≫ T.obj.right.hom = P.obj.hom ≫ towerBaseToTotal A B C := by
  rw [Category.assoc, T.property.2, ← Category.assoc, hf]

variable (A B C)

/-- `(P → B) ↦ (P → B, P → C)`, as a functor to the polynomial towers. -/
def firstFiberFunctor :
    PolynomialAugmentation A (towerBaseAlgebra A B) ⥤ PolynomialTower A B C where
  obj P := firstFiberTower A B C P
  map {_ _} f := ObjectProperty.homMk
    { left := f
      right := Over.homMk f.hom.left (firstFiber_comp_augmentation f.hom.left (Over.w f.hom))
      w := by
        change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
        rw [Category.comp_id, Category.id_comp] }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **A morphism of towers out of `(P → B, P → C)` is its left component.** For a tower
`(P' → B, Q' → C)` the right component of a morphism `(P → B, P → C) ⟶ (P' → B, Q' → C)` is
forced to be the composite `P → P' → Q'`. -/
def firstFiberHomEquiv (P : PolynomialAugmentation A (towerBaseAlgebra A B))
    (T : PolynomialTower A B C) :
    ((firstFiberFunctor A B C).obj P ⟶ T) ≃
      (P ⟶ (polynomialTowerFirstAugmentations A B C).obj T) where
  toFun φ := φ.hom.left
  invFun f := ObjectProperty.homMk
    { left := f
      right := Over.homMk (f.hom.left ≫ T.obj.hom)
        (firstFiber_comp_tower_augmentation f.hom.left (Over.w f.hom))
      w := by
        change f.hom.left ≫ T.obj.hom = 𝟙 _ ≫ f.hom.left ≫ T.obj.hom
        rw [Category.id_comp] }
  left_inv φ := by
    have h : φ.hom.left.hom.left ≫ T.obj.hom = φ.hom.right.left := by
      have hw := φ.hom.w
      change φ.hom.left.hom.left ≫ T.obj.hom = 𝟙 _ ≫ φ.hom.right.left at hw
      rwa [Category.id_comp] at hw
    exact ObjectProperty.hom_ext _ (CommaMorphism.ext rfl (Over.OverMorphism.ext h))
  right_inv _ := rfl

/-- **`u₁` has a right adjoint, before passing to opposite categories**, namely
`(P → B) ↦ (P → B, P → C)`. -/
def firstFiberAdjunction :
    firstFiberFunctor A B C ⊣ polynomialTowerFirstAugmentations A B C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := firstFiberHomEquiv A B C
      homEquiv_naturality_left_symm := fun _ _ =>
        ObjectProperty.hom_ext _ (CommaMorphism.ext rfl
          (Over.OverMorphism.ext (Category.assoc _ _ _)))
      homEquiv_naturality_right := fun _ _ => rfl }

/-- `(P → B) ↦ (P → B, P → C)` is fully faithful: a morphism of towers out of
`(P → B, P → C)` is its left component. -/
def fullyFaithfulFirstFiberFunctor : (firstFiberFunctor A B C).FullyFaithful where
  preimage {_ _} φ := φ.hom.left
  map_preimage {_ _} φ := by
    refine ObjectProperty.hom_ext _ (CommaMorphism.ext rfl (Over.OverMorphism.ext ?_))
    have hw := φ.hom.w
    change φ.hom.left.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ φ.hom.right.left at hw
    rwa [Category.comp_id, Category.id_comp] at hw
  preimage_map _ := rfl

/-- The functor `(P → B) ↦ (P → B, P → C)` is full. -/
instance full_firstFiberFunctor : (firstFiberFunctor A B C).Full :=
  (fullyFaithfulFirstFiberFunctor A B C).full

/-- The functor `(P → B) ↦ (P → B, P → C)` is faithful. -/
instance faithful_firstFiberFunctor : (firstFiberFunctor A B C).Faithful :=
  (fullyFaithfulFirstFiberFunctor A B C).faithful

/-- **`u₁ : C_{C/B/A} ⥤ C_{B/A}` has a right adjoint**, namely `(P → B) ↦ (P → B, P → C)`, and
the composite `u₁ ∘ s₁` is the identity. -/
def polynomialTowerFirstAdjunction :
    polynomialTowerFirst A B C ⊣ (firstFiberFunctor A B C).op :=
  (firstFiberAdjunction A B C).op

/-- The image of the tower `(P → B, P → C)` under `u₁` is `(P → B)`. -/
@[simp]
theorem polynomialTowerFirst_obj_firstFiberTower
    (P : PolynomialAugmentation A (towerBaseAlgebra A B)) :
    (polynomialTowerFirst A B C).obj (Opposite.op (firstFiberTower A B C P)) =
      Opposite.op P := rfl

/-- **The fibre category of `u₁` over `(P → B)` has a final object**, namely `(P → B, P → C)`.
Beware the reversal of arrows: in `C_{C/B/A}` a morphism to it is a morphism of towers out of
`(P → B, P → C)`, which is determined by its left component, and the fibre condition forces that
to be the identity of `P`. -/
def firstFiberTowerIsTerminal (P : PolynomialAugmentation A (towerBaseAlgebra A B)) :
    Limits.IsTerminal (Functor.Fiber.mk
      (polynomialTowerFirst_obj_firstFiberTower A B C P)) := by
  refine Limits.IsTerminal.ofUniqueHom (fun Y => ?_) (fun Y m => ?_)
  · obtain ⟨Z, hZ⟩ := Y
    obtain rfl : P = Z.unop.obj.left := (Opposite.op_injective hZ).symm
    exact ⟨((firstFiberHomEquiv A B C _ Z.unop).symm (𝟙 _)).op,
      CategoryTheory.Functor.IsHomLift.map
        ((firstFiberHomEquiv A B C _ Z.unop).symm (𝟙 _)).op⟩
  · obtain ⟨Z, hZ⟩ := Y
    obtain rfl : P = Z.unop.obj.left := (Opposite.op_injective hZ).symm
    refine Functor.Fiber.hom_ext (Quiver.Hom.unop_inj
      ((firstFiberHomEquiv A B C _ Z.unop).injective ?_))
    have h : (𝟙 ((polynomialTowerFirst A B C).obj Z)) =
        (polynomialTowerFirst A B C).map m.1 :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ (polynomialTowerFirst A B C) Z
        (Opposite.op (firstFiberTower A B C Z.unop.obj.left)) _ m.1 m.2
    exact (Quiver.Hom.op_inj h).symm

/-- The fibre category of `u₁` over `(P → B)` has a final object. -/
theorem hasTerminal_polynomialTowerFirstFiber
    (P : PolynomialAugmentation A (towerBaseAlgebra A B)) :
    Limits.HasTerminal ((polynomialTowerFirst A B C).Fiber (Opposite.op P)) :=
  (firstFiberTowerIsTerminal A B C P).hasTerminal

/-! ### The right adjoint of `u₂` -/

/-- `(Q → C) ↦ (A → B, Q → C)`, as a functor to the polynomial towers. -/
def secondFiberFunctor :
    PolynomialAugmentation A (towerTotalAlgebra A C) ⥤ PolynomialTower A B C where
  obj L := secondFiberTower (B := B) L
  map {_ _} f := ObjectProperty.homMk
    { left := 𝟙 _
      right := f.hom
      w := commAlgCat_self_hom_ext _ _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **A morphism of towers out of `(A → B, Q → C)` is its right component.** The left component
of a morphism `(A → B, Q → C) ⟶ (P' → B, Q' → C)` is the structure map of `A`. -/
def secondFiberHomEquiv (L : PolynomialAugmentation A (towerTotalAlgebra A C))
    (T : PolynomialTower A B C) :
    ((secondFiberFunctor A B C).obj L ⟶ T) ≃
      (L ⟶ (polynomialTowerSecondAugmentations A B C).obj T) where
  toFun φ := ObjectProperty.homMk φ.hom.right
  invFun g := ObjectProperty.homMk
    { left := ObjectProperty.homMk (Over.homMk
        (CommAlgCat.ofHom (Algebra.ofId A ↑(towerLeftAlgebra T.obj)))
        (commAlgCat_self_hom_ext _ _))
      right := g.hom
      w := commAlgCat_self_hom_ext _ _ }
  left_inv _ :=
    ObjectProperty.hom_ext _ (CommaMorphism.ext
      (ObjectProperty.hom_ext _ (Over.OverMorphism.ext (commAlgCat_self_hom_ext _ _))) rfl)
  right_inv _ := rfl

/-- **`u₂` has a right adjoint, before passing to opposite categories**, namely
`(Q → C) ↦ (A → B, Q → C)`. -/
def secondFiberAdjunction :
    secondFiberFunctor A B C ⊣ polynomialTowerSecondAugmentations A B C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := secondFiberHomEquiv A B C
      homEquiv_naturality_left_symm := fun _ _ =>
        ObjectProperty.hom_ext _ (CommaMorphism.ext
          (ObjectProperty.hom_ext _ (Over.OverMorphism.ext (commAlgCat_self_hom_ext _ _))) rfl)
      homEquiv_naturality_right := fun _ _ => rfl }

/-- `(Q → C) ↦ (A → B, Q → C)` is fully faithful: a morphism of towers out of `(A → B, Q → C)`
is its right component. -/
def fullyFaithfulSecondFiberFunctor : (secondFiberFunctor A B C).FullyFaithful where
  preimage {_ _} φ := ObjectProperty.homMk φ.hom.right
  map_preimage {_ _} _ :=
    ObjectProperty.hom_ext _ (CommaMorphism.ext
      (ObjectProperty.hom_ext _ (Over.OverMorphism.ext (commAlgCat_self_hom_ext _ _))) rfl)
  preimage_map _ := rfl

/-- The functor `(Q → C) ↦ (A → B, Q → C)` is full. -/
instance full_secondFiberFunctor : (secondFiberFunctor A B C).Full :=
  (fullyFaithfulSecondFiberFunctor A B C).full

/-- The functor `(Q → C) ↦ (A → B, Q → C)` is faithful. -/
instance faithful_secondFiberFunctor : (secondFiberFunctor A B C).Faithful :=
  (fullyFaithfulSecondFiberFunctor A B C).faithful

/-- **`u₂ : C_{C/B/A} ⥤ C_{C/A}` has a right adjoint**, namely `(Q → C) ↦ (A → B, Q → C)`, and
the composite `u₂ ∘ s₂` is the identity. -/
def polynomialTowerSecondAdjunction :
    polynomialTowerSecond A B C ⊣ (secondFiberFunctor A B C).op :=
  (secondFiberAdjunction A B C).op

/-! ### `Lg_{i,!} ∘ g_i⁻¹ = id` for `i = 1, 2` -/

section LowerShriek

attribute [local instance] HasDerivedCategory.standard

/-- The opposite of `(P → B) ↦ (P → B, P → C)` is continuous for the chaotic topologies on
`C_{B/A}` and `C_{C/B/A}`. -/
instance polynomialTowerFirstSection_isContinuous :
    ((firstFiberFunctor A B C).op).IsContinuous
      (polynomialTopology A (towerBaseAlgebra A B)) (polynomialTowerTopology A B C) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _
    (polynomialTopology_eq_bot A (towerBaseAlgebra A B))

/-- The opposite of `(Q → C) ↦ (A → B, Q → C)` is continuous for the chaotic topologies on
`C_{C/A}` and `C_{C/B/A}`. -/
instance polynomialTowerSecondSection_isContinuous :
    ((secondFiberFunctor A B C).op).IsContinuous
      (polynomialTopology A (towerTotalAlgebra A C)) (polynomialTowerTopology A B C) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _
    (polynomialTopology_eq_bot A (towerTotalAlgebra A C))

/-- Abelian presheaves on `C_{C/B/A}` with the chaotic topology admit sheafification. -/
instance hasSheafify_polynomialTowerTopology :
    HasSheafify (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1} := by
  rw [polynomialTowerTopology_eq_bot]
  infer_instance

/-- Abelian presheaves on `C_{D/A}` with the chaotic topology admit sheafification. -/
instance hasSheafify_polynomialTopology (D : CommAlgCat.{u} A) :
    HasSheafify (polynomialTopology A D) AddCommGrpCat.{u + 1} := by
  rw [polynomialTopology_eq_bot]
  infer_instance

/-- **Tag 08QW, the case `i = 1`.** Inverse image along `g₁` followed by derived lower shriek is
the identity of `D(Ab(C_{B/A}))`. On abelian sheaves `g₁⁻¹` is restriction along `u₁`, which is
fully faithful with an exact right adjoint because `u₁` has the fully faithful right adjoint
`(P → B) ↦ (P → B, P → C)`. The statement is for an arbitrary left derived functor `L` of lower
shriek, presented by `α`, and an arbitrary derived functor `G` of inverse image, presented by
`e`. -/
def derivedLowerShriekFirstInverseImageIso
    (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTopology A (towerBaseAlgebra A B))
        AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((polynomialTowerFirst A B C).sheafPullback AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology A (towerBaseAlgebra A B))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (G : DerivedCategory (Sheaf (polynomialTopology A (towerBaseAlgebra A B))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((polynomialTowerFirst A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology A (towerBaseAlgebra A B))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ :=
  Stacks.ChaoticSite.abelianDerivedLowerShriekInverseImageIso AddCommGrpCat.{u + 1}
    (polynomialTowerTopology A B C) (polynomialTopology A (towerBaseAlgebra A B))
    (polynomialTowerFirstAdjunction A B C) (polynomialTowerTopology_eq_bot A B C)
    (polynomialTopology_eq_bot A (towerBaseAlgebra A B)) L α G e

/-- **Tag 08QW, the case `i = 2`.** Inverse image along `g₂` followed by derived lower shriek is
the identity of `D(Ab(C_{C/A}))`. On abelian sheaves `g₂⁻¹` is restriction along `u₂`, which is
fully faithful with an exact right adjoint because `u₂` has the fully faithful right adjoint
`(Q → C) ↦ (A → B, Q → C)`, the final object of the fibre. -/
def derivedLowerShriekSecondInverseImageIso
    (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTopology A (towerTotalAlgebra A C))
        AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((polynomialTowerSecond A B C).sheafPullback AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology A (towerTotalAlgebra A C))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (G : DerivedCategory (Sheaf (polynomialTopology A (towerTotalAlgebra A C))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((polynomialTowerSecond A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology A (towerTotalAlgebra A C))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ :=
  Stacks.ChaoticSite.abelianDerivedLowerShriekInverseImageIso AddCommGrpCat.{u + 1}
    (polynomialTowerTopology A B C) (polynomialTopology A (towerTotalAlgebra A C))
    (polynomialTowerSecondAdjunction A B C) (polynomialTowerTopology_eq_bot A B C)
    (polynomialTopology_eq_bot A (towerTotalAlgebra A C)) L α G e

end LowerShriek

end CommAlgCat

end

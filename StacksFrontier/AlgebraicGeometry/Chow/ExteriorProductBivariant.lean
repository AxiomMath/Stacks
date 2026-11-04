module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence

/-!
# The exterior product and bivariant cap products

Let `(S, δ)` be a base situation whose base is a point, so that the exterior product
`α × β ∈ CH_{n+m}(X ×_S Y)` of Stacks 0FBV is defined. Let `u : Y ⟶ Z` be a morphism of schemes
locally of finite type over `S` and let `c ∈ A^p(Y ⟶ Z)` be a bivariant class. Stacks 0FBY asserts

  `α × (c ∩ β) = c ∩ (α × β)`

in `CH_*(X ×_S Y)`, for `α ∈ CH_n(X)` and `β ∈ CH_m(Z)`. The cap product of `c` lands on a fibre
product over `Z`, so both sides are transported to `CH_{n + (m - p)}(X ×_S Y)` along canonical
isomorphisms over `S` before they are compared.

## Main definitions

* `Stacks.Chow.exteriorCapIso` — the canonical identification `Y ×_Z (X ×_S Z) ≅ X ×_S Y`.
* `Stacks.Chow.BivariantClass.capTarget` — the cap product `c ∩ β` of a bivariant class for
  `u : Y ⟶ Z` against a class on its own target `Z`, read on `Y` through `Y ≅ Y ×_Z Z`.
* `Stacks.Chow.exteriorProductOnTarget`, `Stacks.Chow.capExteriorProduct`,
  `Stacks.Chow.exteriorProductCap` — the exterior product read on `pr_Z ≫ sZ`, and the two sides
  `c ∩ (α × β)` and `α × (c ∩ β)` of the equation.
* `Stacks.Chow.CommutesExteriorProductCap` — the equation of Stacks 0FBY, as a predicate.

## Main results

* `Stacks.Chow.exteriorCapIso_hom_fst`, `Stacks.Chow.exteriorCapIso_hom_snd`,
  `Stacks.Chow.exteriorCapIso_hom_comp_structureMorphism` — the identification is the one
  specified by its two projections, and it is a morphism over the base.
* `Stacks.Chow.BivariantClass.capTarget_zero`, `Stacks.Chow.BivariantClass.capTarget_add` — the
  cap product against a class on the target is additive in the class.
* `Stacks.Chow.commutesExteriorProductCap_zero` — the equation of Stacks 0FBY holds for the zero
  bivariant class.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The canonical identification `Y ×_Z (X ×_S Z) ≅ X ×_S Y` -/

section Comparison

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sZ : Z ⟶ S) {sY : Y ⟶ S} (u : Y ⟶ Z)
  (hu : u ≫ sZ = sY)

/-- The canonical identification `Y ×_Z (X ×_S Z) ≅ X ×_S Y`, for `u : Y ⟶ Z` a morphism over
`S`. -/
def exteriorCapIso :
    (pullback u (pullback.snd sX sZ) : Scheme.{u}) ≅ (pullback sX sY : Scheme.{u}) :=
  pullbackSymmetry u (pullback.snd sX sZ) ≪≫
    pullbackLeftPullbackSndIso sX sZ u ≪≫ pullback.congrHom rfl hu

/-- Composed with the first projection of `X ×_S Y`, the identification
`Y ×_Z (X ×_S Z) ≅ X ×_S Y` is the projection to `X ×_S Z` followed by its first projection. -/
@[reassoc (attr := simp)]
theorem exteriorCapIso_hom_fst :
    (exteriorCapIso sX sZ u hu).hom ≫ pullback.fst sX sY =
      pullback.snd u (pullback.snd sX sZ) ≫ pullback.fst sX sZ := by
  simp [exteriorCapIso]

/-- Composed with the second projection of `X ×_S Y`, the identification
`Y ×_Z (X ×_S Z) ≅ X ×_S Y` is the first projection to `Y`. -/
@[reassoc (attr := simp)]
theorem exteriorCapIso_hom_snd :
    (exteriorCapIso sX sZ u hu).hom ≫ pullback.snd sX sY =
      pullback.fst u (pullback.snd sX sZ) := by
  simp [exteriorCapIso]

/-- The identification `Y ×_Z (X ×_S Z) ≅ X ×_S Y` is a morphism over `S`: it carries the
structure morphism of `X ×_S Y` to that of `Y ×_Z (X ×_S Z)`. -/
theorem exteriorCapIso_hom_comp_structureMorphism :
    (exteriorCapIso sX sZ u hu).hom ≫ (pullback.fst sX sY ≫ sX) =
      pullback.fst u (pullback.snd sX sZ) ≫ sY := by
  rw [← Category.assoc, exteriorCapIso_hom_fst, Category.assoc,
    pullback.condition (f := sX) (g := sZ), ← Category.assoc, ← pullback.condition,
    Category.assoc, hu]

end Comparison

/-! ### The cap product against a class on the target -/

section CapTarget

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Z : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z)
  [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)

/-- The cap product `c ∩ β ∈ CH_{k-p}(Y)` of a bivariant class `c ∈ A^p(Y ⟶ Z)` against a class
`β ∈ CH_k(Z)` on its own target, read on `Y` itself.

The cap operation of `Stacks.Chow.BivariantClass` is indexed by a test morphism, and at the test
morphism `𝟙 Z` it lands on the fibre product `Y ×_Z Z`. That scheme is canonically `Y`, by
`Stacks.Chow.pullbackIdIso`, and the class is pushed forward along the inverse of this
identification. -/
def BivariantClass.capTarget (c : BivariantClass C G sY sZ u hu p) (k : ℤ)
    (β : chowGroup C sZ k) : chowGroup C sY (k - p) :=
  chowPushforwardOfIso C (pullback.fst u (𝟙 Z) ≫ sY) sY (pullbackIdIso u).inv
    (pullbackIdIso_inv_comp u sY) (k - p)
    (c.cap (𝟙 Z) k (chowGroupCongr C (Category.id_comp sZ).symm k β))

/-- The cap product of a bivariant class against the zero class on the target is zero. -/
@[simp]
theorem BivariantClass.capTarget_zero (c : BivariantClass C G sY sZ u hu p) (k : ℤ) :
    c.capTarget C G sY sZ u hu p k 0 = 0 := by
  simp [BivariantClass.capTarget]

/-- The cap product of a bivariant class against a class on the target is additive in the
class. -/
@[simp]
theorem BivariantClass.capTarget_add (c : BivariantClass C G sY sZ u hu p) (k : ℤ)
    (β β' : chowGroup C sZ k) :
    c.capTarget C G sY sZ u hu p k (β + β') =
      c.capTarget C G sY sZ u hu p k β + c.capTarget C G sY sZ u hu p k β' := by
  simp [BivariantClass.capTarget]

/-- The cap product against a class on the target, as a homomorphism of abelian groups. -/
def BivariantClass.capTargetHom (c : BivariantClass C G sY sZ u hu p) (k : ℤ) :
    chowGroup C sZ k →+ chowGroup C sY (k - p) where
  toFun := c.capTarget C G sY sZ u hu p k
  map_zero' := c.capTarget_zero C G sY sZ u hu p k
  map_add' := c.capTarget_add C G sY sZ u hu p k

/-- The homomorphism `capTargetHom` evaluates to the cap product `capTarget`. -/
@[simp]
theorem BivariantClass.capTargetHom_apply (c : BivariantClass C G sY sZ u hu p) (k : ℤ)
    (β : chowGroup C sZ k) :
    c.capTargetHom C G sY sZ u hu p k β = c.capTarget C G sY sZ u hu p k β :=
  rfl

end CapTarget

/-! ### The equation of Stacks 0FBY -/

section Statement

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (hfp : FlatPullbackDescends C)

/-- The exterior product `α × β` of Stacks 0FBV, presented on the structure morphism
`pr_Z ≫ sZ` of `X ×_S Z` rather than on `pr_X ≫ sX`. -/
def exteriorProductOnTarget (n m : ℤ) (α : chowGroup C sX n) (β : chowGroup C sZ m) :
    chowGroup C (pullback.snd sX sZ ≫ sZ) (n + m) :=
  chowGroupCongr C (pullback.condition (f := sX) (g := sZ)) (n + m)
    (chowExteriorProduct C hδ sX sZ n m (TensorProduct.tmul ℤ α β))

/-- The right-hand side of Stacks 0FBY, `c ∩ (α × β)`, read in `CH_{n + (m - p)}(X ×_S Y)`.

The cap is taken at the test morphism `pr_Z : X ×_S Z ⟶ Z`, so it lands on `Y ×_Z (X ×_S Z)` in
degree `(n + m) - p`; the degree is matched by `Stacks.Chow.chowGroupDegreeEquiv` and the class is
then pushed forward along `Stacks.Chow.exteriorCapIso`. -/
def capExteriorProduct (c : BivariantClass C G sY sZ u hu p) (n m : ℤ)
    (α : chowGroup C sX n) (β : chowGroup C sZ m) :
    chowGroup C (pullback.fst sX sY ≫ sX) (n + (m - p)) :=
  chowPushforwardOfIso C (pullback.fst u (pullback.snd sX sZ) ≫ sY) (pullback.fst sX sY ≫ sX)
    (exteriorCapIso sX sZ u hu).hom (exteriorCapIso_hom_comp_structureMorphism sX sZ u hu)
    (n + (m - p))
    (chowGroupDegreeEquiv C (pullback.fst u (pullback.snd sX sZ) ≫ sY)
      (by omega : n + m - p = n + (m - p))
      (c.cap (pullback.snd sX sZ) (n + m)
        (exteriorProductOnTarget C hδ sX sZ n m α β)))

/-- The left-hand side of Stacks 0FBY, `α × (c ∩ β)`, in `CH_{n + (m - p)}(X ×_S Y)`. -/
def exteriorProductCap (c : BivariantClass C G sY sZ u hu p) (n m : ℤ)
    (α : chowGroup C sX n) (β : chowGroup C sZ m) :
    chowGroup C (pullback.fst sX sY ≫ sX) (n + (m - p)) :=
  chowExteriorProduct C hδ sX sY n (m - p)
    (TensorProduct.tmul ℤ α (c.capTarget C G sY sZ u hu p m β))

/-- The equation of Stacks 0FBY, as a predicate: for every class `α` on `X` and every class `β`
on `Z`, the exterior product with `α` commutes with the cap product of `c`,

  `α × (c ∩ β) = c ∩ (α × β)`,

both sides read in `CH_{n + (m - p)}(X ×_S Y)` through the canonical identifications of
`Stacks.Chow.exteriorProductCap` and `Stacks.Chow.capExteriorProduct`. -/
def CommutesExteriorProductCap (c : BivariantClass C G sY sZ u hu p) (n m : ℤ) : Prop :=
  ∀ (α : chowGroup C sX n) (β : chowGroup C sZ m),
    exteriorProductCap C hδ G sX sY sZ u hu p c n m α β =
      capExteriorProduct C hδ G sX sY sZ u hu p c n m α β

/-- The equation of Stacks 0FBY holds for the zero bivariant class: both sides vanish. -/
theorem commutesExteriorProductCap_zero (n m : ℤ) :
    CommutesExteriorProductCap C hδ G sX sY sZ u hu p 0 n m := by
  intro α β
  simp only [exteriorProductCap, capExteriorProduct, exteriorProductOnTarget,
    BivariantClass.capTarget, BivariantClass.zero_cap, map_zero, TensorProduct.tmul_zero]

end Statement

end Stacks.Chow

end

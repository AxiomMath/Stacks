module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map of a local complete intersection morphism

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S`. Given a
factorization `f = g ∘ i` with `i : X ⟶ P` an immersion and `g : P ⟶ Y` smooth, the immersion `i`
is a regular immersion, its normal sheaf `𝒩_{X/P} = 𝒞_{X/P}^∨` is finite locally free, and
Stacks 0FF3 defines the *Gysin map*

  `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧`,

where `i^! = c(X ⟶ P, 𝒩_{X/P}) ∈ A^*(X ⟶ P)^∧` is the class of section 42.54 of the Stacks Project
for the immersion `i` (Stacks 0FBK, 0FBQ (3)) and `g^* ∈ A^*(P ⟶ Y)^∧` is the flat pullback of
Stacks 0B78, composed in the completed bivariant groups of Stacks 0FE0.

## Main definitions

* `Stacks.Chow.SmoothFactorization.gysinMap` — **Stacks 0FF3**, the class `i^! ∘ g^*` attached to
  a factorization of `f`.
* `Stacks.Chow.lciGysinMap` — **Stacks 0FF3**, the Gysin map `f^!` of a local complete intersection
  morphism whose Gysin map exists, built from a chosen factorization; that the choice does not
  matter is Stacks 0FF2.

## Implementation notes

The composite of the two completed classes is a class for `i ≫ g`; it is transported to a class
for `f` along `i ≫ g = f` by `Stacks.Chow.completedBivariantGroup.copy`. The structure morphism of
`P` over the base is `g ≫ sY`, which is locally of finite type because `g` is smooth.

The normal sheaf of `i` is `Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`, the dual of the
conormal sheaf with the canonical isomorphism `𝒩_{X/P}^∨ ≅ 𝒞_{X/P}` as its structural surjection;
the regularity of `i` is `Stacks.Chow.SmoothFactorization.isRegularImmersion` (Stacks 069G and
Stacks 063L). Its rank is only locally constant, which is why `i^!` lies in the completed group.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
include hf in
/-- The immersion of a factorization of `f` is a morphism over the base, for the structure
morphism `g ≫ sY` of the intermediate scheme. -/
theorem SmoothFactorization.imm_comp_structureMorphism (F : SmoothFactorization f) :
    F.imm ≫ F.proj ≫ sY = sX := by
  rw [← Category.assoc, F.imm_proj, hf]

/-- **Stacks 0FF3, the Gysin map of a factorization.** For a local complete intersection morphism
`f : X ⟶ Y` and a factorization `f = g ∘ i` with `i : X ⟶ P` an immersion and `g : P ⟶ Y` smooth,
the class

  `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧`,

the composite (Stacks 0FE0) of the class `i^! = c(X ⟶ P, 𝒩_{X/P})` of the regular immersion `i`
(Stacks 0FBK, 0FBQ (3)) with the flat pullback `g^*` of the smooth morphism `g` (Stacks 0B78). -/
@[stacks 0FF3 "the Gysin map f^! = i^! ∘ g^* ∈ A^*(X → Y)^∧ of a factorization f = g ∘ i, i an \
immersion and g smooth, of a local complete intersection morphism"]
def SmoothFactorization.gysinMap (F : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsLocallyNoetherian F.ambient := LocallyOfFiniteType.isLocallyNoetherian (F.proj ≫ sY)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  completedBivariantGroup.copy C F.imm_proj (comp_comp_structureMorphism_eq
      (F.imm_comp_structureMorphism C sX sY hf) rfl) hf
    (completedBivariantCompositeOfInvertible C sX (F.proj ≫ sY) sY F.imm F.proj
      (F.imm_comp_structureMorphism C sX sY hf) rfl
      (completedVirtualNormalGysinClassOfImmersion C sX (F.proj ≫ sY) F.imm
        (F.imm_comp_structureMorphism C sX sY hf)
        (VirtualNormalBundle.ofIsRegularImmersion F.imm (F.isRegularImmersion hlci)))
      (completedFlatPullbackOfSmooth C (F.proj ≫ sY) sY F.proj rfl))

/-- **Stacks 0FF3, the Gysin map `f^!`** of a local complete intersection morphism `f : X ⟶ Y` of
schemes locally of finite type over the base for which the Gysin map exists: the class
`i^! ∘ g^*` of a chosen factorization `f = g ∘ i`. By Stacks 0FF2 it does not depend on the choice
(`Stacks.Chow.SmoothFactorization.gysinMap_eq_lciGysinMap`). -/
@[stacks 0FF3 "the Gysin map f^! ∈ A^*(X → Y)^∧ of a local complete intersection morphism for \
which the Gysin map exists"]
def lciGysinMap (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf :=
  (Classical.choice ((gysinMapExists_iff_nonempty f).1 h)).gysinMap C sX sY hf hlci

end Stacks.Chow

end

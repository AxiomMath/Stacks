module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSectionCriterion
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackTwistPower
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerMul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-!
# Untwisting the contraction against a tensor power is the identity

Let `L` be an invertible sheaf of modules over a sheaf of commutative rings. The coherent
multiplication of [Stacks, Tag 01CU] supplies two inverse laws for the tensor power `L^{⊗ n}`,
the multiplication in the bidegrees `(n, -n)` and `(-n, n)`, and both occur in the module
`ℳ̃_T` of [Stacks, Tag 01O6]: the contraction
`Stacks.AlgebraicGeometry.PullbackTwistPower.powContractIso`

`(𝒩 ⊗ L^{⊗ n}) ⊗ L^{⊗ (-n)} ≅ 𝒩`

uses the first, while the untwisting
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.laurentInvLaw` that makes a
balancing relation checkable on global sections uses the second. This file proves that the two
cancel:

`untwist (laurentInvLaw L n) ((powContractIso 𝒩 n).hom) = 𝟙 (𝒩 ⊗ L^{⊗ n})`.

## The snake identity

Inserting one inverse law and cancelling with the other is a zig-zag, and for a *bare* pair of
inverse laws `m₁ : A ⊗ B ≅ 𝟙` and `m₂ : B ⊗ A ≅ 𝟙` it is **false**: the two laws must be
compatible in the sense of `Stacks.Monoidal.braiding_eval_snake`,

`(α_ A B A).hom ≫ A ◁ m₂.hom ≫ (ρ_ A).hom = m₁.hom ▷ A ≫ (λ_ A).hom`,

and in super vector spaces the odd line is invertible with the two sides differing by a sign.
Given that identity the cancellation is formal — `untwist_contract_eq_id` below — by the pentagon,
the triangle, and the naturality of the associator in its middle and right variables.

For the tensor powers of an invertible sheaf of modules the compatibility is available:
`Stacks.SheafOfModules.TensorPower.coherentMulIso_comm` says the multiplication in the bidegree
`(-n, n)` is the one in the bidegree `(n, -n)` precomposed with the braiding, and
`Stacks.SheafOfModules.TensorPower.tensorSheafBraiding_tensorPower_self` says `L^{⊗ n}` braids
trivially with itself, which is the hypothesis of `braiding_eval_snake`.

## The braided structure

`Stacks.Monoidal.braiding_eval_snake` asks for a `CategoryTheory.BraidedCategory` instance on the
monoidal category `powContractIso` lives in, namely the strict monoidal structure of [Stacks, Tag
01CA] on sheaves of modules. It is already there:
`Stacks.SheafOfModules.Strict.braidedCategory`, whose braiding is the symmetry constraint of the
tensor product sheaf by `Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding`, and
`Stacks.PullbackGradedAlgebra.monoidalCategory` — the spelling the summands of [Stacks, Tag 01O6]
are built with — is `Stacks.SheafOfModules.Strict.monoidalCategory` on the nose, by
`Stacks.PullbackGradedAlgebra.monoidalCategory_eq`. So no braided structure has to be
constructed; it only has to be named at the spelling in force.

## Main results

* `Stacks.Monoidal.untwist_contract_eq_id`: **untwisting the contraction against a compatible pair
  of inverse laws is the identity**, in an arbitrary monoidal category with every object and
  morphism free.
* `Stacks.Monoidal.untwist_eq_of_whiskerRight`: a morphism out of `X ⊗ K` whose first factor is
  an isomorphism `X ≅ 𝒩 ⊗ K'` whiskered by `K`, followed by a morphism whose untwisting is the
  identity, untwists to that isomorphism.
* `Stacks.SheafOfModules.TensorPower.braiding_comp_coherentMulIso`: **the two inverse laws of
  `L^{⊗ n}` supplied by the coherent multiplication of [Stacks, Tag 01CU] differ by the
  braiding.**
* `Stacks.SheafOfModules.TensorPower.untwist_contract_coherentMul`: the snake identity for those
  two laws.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.untwist_powContractIso`: **the snake identity at
  the spelling of [Stacks, Tag 01O6]**, for `powContractIso` and `laurentInvLaw`.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.tensorModulesMapIso_hom_eq_tensorSheafMapIso_hom`:
  the two spellings of the functorial action of the tensor product sheaf on a pair of
  isomorphisms agree.
* `Stacks.AlgebraicGeometry.PullbackTwistPower.untwist_pullbackShiftedContractIso`: **the
  untwisting of `pullbackShiftedContractIso` is `pullbackShiftedIso`** — the normalisation of the
  degree-`n` comparison of property (1) of [Stacks, Tag 01O7] that the balancing relations
  consume.

## What is NOT here

No balancing relation of [Stacks, Tag 01O6] is verified here, and no tag is carried.

This file belongs to the route to property (1) of [Stacks, Tag 01O7] through the
isomorphism `α : h^*𝒪(d) ≅ L`, and the remarks in this section concern that route only.
The comparison `ℳ̃_T ≅ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] is built by another route,
in `StacksFrontier/AlgebraicGeometry/RelativeProjQuadrupleTilde/`, which uses nothing from this file:
on a chart datum (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`) the
degreewise maps send `x ⊗ l` to `g^*(x / c^m) · (l · w^m)`, their balancing relations are
verified directly (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.bmap_balanced`), and the
inverse is written down.

On this route the remaining content of the relations is the interaction of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.arrow` and
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedIso` with the action of `𝒜` and with
`ψ`, which the identities below say nothing about.

## Implementation notes

Every statement that mentions the unit object together with a tensor power is stated with the
isomorphisms `m₁`, `m₂` and the contraction as *free variables* constrained by hypotheses, rather
than with their values substituted: `Stacks.SheafOfModules.TensorPower.tensorPower O hO L 0` and
`𝟙_` are equal by `rfl` but not unifiable at the `implicit` transparency level, so a goal naming
both is rejected after `rw` has unfolded anything. With the free-variable form each hypothesis is
discharged by `rfl` at the point of use, where the comparison happens at default transparency.
This is why the three hypotheses of `untwist_contract_coherentMul` are stated on the `hom`s and
not on the isomorphisms.

`Stacks.RelativeVeryAmple.tensorModulesMapIso` and
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso` are the same isomorphism, but **not by
`rfl`**: the first composes the two legs of the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, each of which sheafifies a tensor product with an
identity, while the second sheafifies the tensor product of both morphisms at once, so the
composite carries two sheafified morphisms where the other spelling carries one. They are
identified through the monoidal tensor product, by
`tensorModulesMapIso_hom_eq_tensorSheafMapIso_hom`, and that is the bridge the whiskering
hypothesis of `untwist_contract_whiskerRight_coherentMul` is discharged with at
`pullbackShiftedContractIso`. Stating that hypothesis directly at the
`AlgebraicGeometry.Scheme.Modules` spelling is not possible: right whiskering needs a monoidal
instance, and instance search does not unfold `AlgebraicGeometry.Scheme.Modules` to find the one
registered at `Stacks.RingedSpace.structureRingSheaf`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

universe v u t

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The contraction of `(N ⊗ A) ⊗ B` against an inverse law `m₁ : A ⊗ B ≅ 𝟙`, whiskered by
`A`, is the insertion of the opposite law `m₂ : B ⊗ A ≅ 𝟙`.** This is the snake identity for
`m₁` and `m₂` transported from `A` to `N ⊗ A`: the pentagon moves the outer `A` across the
associator, the triangle turns the whiskered right unitor into the left unitor the snake
identity produces, and the naturality of the associator in its middle and right variables carries
`m₁` and `m₂` past it. -/
theorem contract_whiskerRight {A B : C} (m₁ : A ⊗ B ⟶ 𝟙_ C) (m₂ : B ⊗ A ⟶ 𝟙_ C)
    (hsnake : (α_ A B A).hom ≫ A ◁ m₂ ≫ (ρ_ A).hom = m₁ ▷ A ≫ (λ_ A).hom) (N : C) :
    ((α_ N A B).hom ≫ N ◁ m₁ ≫ (ρ_ N).hom) ▷ A
      = (α_ (N ⊗ A) B A).hom ≫ (N ⊗ A) ◁ m₂ ≫ (ρ_ (N ⊗ A)).hom := by
  rw [MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight,
    ← MonoidalCategory.triangle N A, ← Category.assoc ((N ◁ m₁) ▷ A),
    MonoidalCategory.associator_naturality_middle, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← hsnake, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  rw [MonoidalCategory.pentagon_assoc, ← MonoidalCategory.associator_naturality_right_assoc,
    ← MonoidalCategory.rightUnitor_tensor_hom]

/-- **Untwisting the contraction against a compatible pair of inverse laws is the identity.**
For `m₁ : A ⊗ B ≅ 𝟙` and `m₂ : B ⊗ A ≅ 𝟙` satisfying the snake identity, the contraction
`(N ⊗ A) ⊗ B ⟶ N` built from `m₁` untwists, along `m₂`, to the identity of `N ⊗ A`.

Without the snake identity this is false: a pair of inverse laws for an invertible object need
not be compatible, and `Stacks.Monoidal.braiding_eval_snake` is where the compatibility comes
from. -/
theorem untwist_contract_eq_id {A B : C} (m₁ : A ⊗ B ≅ 𝟙_ C) (m₂ : B ⊗ A ≅ 𝟙_ C)
    (hsnake : (α_ A B A).hom ≫ A ◁ m₂.hom ≫ (ρ_ A).hom = m₁.hom ▷ A ≫ (λ_ A).hom) (N : C) :
    untwist m₂ ((α_ N A B).hom ≫ N ◁ m₁.hom ≫ (ρ_ N).hom) = 𝟙 (N ⊗ A) := by
  rw [untwist, untwistIso, contract_whiskerRight m₁.hom m₂.hom hsnake N]
  simp

/-- **A morphism out of `X ⊗ K` whose first factor unwhiskers to an isomorphism untwists to that
isomorphism**, provided the remaining factor untwists to the identity. This is
`Stacks.Monoidal.untwist_whiskerRight_comp` packaged so that the splitting of the composite is
supplied as a hypothesis rather than produced by rewriting. -/
theorem untwist_eq_of_whiskerRight {X N K K' : C} (e : K ⊗ K' ≅ 𝟙_ C)
    {v : X ⟶ N ⊗ K'} {u : (N ⊗ K') ⊗ K ⟶ N} {w : X ⊗ K ⟶ N}
    (hu : untwist e u = 𝟙 (N ⊗ K')) (hw : w = v ▷ K ≫ u) :
    untwist e w = v := by
  rw [hw, untwist_whiskerRight_comp, hu, Category.comp_id]

end Stacks.Monoidal

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{v})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{v} RingCat.{v})]

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory

open Stacks.SheafOfModules (tensorSheafBraiding braiding_eq_tensorSheafBraiding
  tensorSheafAssociator tensorLeftFunctorObjUnitIso associator_eq_tensorSheafAssociator
  rightUnitor_eq_tensorSheafRightUnitor tensorSheafMapIso_hom_eq)

variable (L : SheafOfModules.{v} (structureSheaf O hO)) [Stacks.SheafOfModules.IsInvertible O hO L]

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{v} RingCat.{v})] in
/-- Two reindexings of tensor powers compose to a reindexing: the three equalities of integers are
proofs of propositions, so only their endpoints matter. -/
private theorem reindex_trans {a b c : ℤ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) :
    (tensorPowerReindex O hO L h₁).hom ≫ (tensorPowerReindex O hO L h₂).hom
      = (tensorPowerReindex O hO L h₃).hom := by
  cases h₁; cases h₂; simp

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{v} RingCat.{v})] in
/-- **A tensor power of an invertible sheaf of modules has trivial self-braiding**, for the strict
monoidal structure of [Stacks, Tag 01CA]. This is the commutativity law of the coherent
multiplication of [Stacks, Tag 01CU] in the bidegree `(n, n)`, read through
`Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding`. -/
theorem hasTrivialSelfBraiding_tensorPower (n : ℤ) :
    Stacks.GradedSections.HasTrivialSelfBraiding (tensorPower O hO L n) := by
  refine ⟨?_⟩
  rw [braiding_eq_tensorSheafBraiding, tensorSheafBraiding_tensorPower_self]
  rfl

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{v} RingCat.{v})] in
/-- **The two inverse laws of `L^{⊗ n}` differ by the braiding.** The multiplication of [Stacks,
Tag 01CU] in the bidegree `(-n, n)`, reindexed to the degree zero, is the multiplication in the
bidegree `(n, -n)` reindexed to the degree zero, precomposed with the symmetry constraint. This
is `Stacks.SheafOfModules.TensorPower.coherentMulIso_comm` with the two reindexings composed. -/
theorem braiding_comp_coherentMulIso (n : ℤ) :
    (β_ (tensorPower O hO L (-n)) (tensorPower O hO L n)).hom ≫
        (coherentMulIso O hO L n (-n)).hom ≫ (tensorPowerReindex O hO L (add_neg_cancel n)).hom
      = (coherentMulIso O hO L (-n) n).hom ≫
        (tensorPowerReindex O hO L (neg_add_cancel n)).hom := by
  have hbraid : (β_ (tensorPower O hO L (-n)) (tensorPower O hO L n)).hom =
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding O hO
        (tensorPower O hO L (-n)) (tensorPower O hO L n)).hom :=
    congrArg Iso.hom
      (braiding_eq_tensorSheafBraiding O hO (tensorPower O hO L (-n)) (tensorPower O hO L n))
  have hcomm : (coherentMulIso O hO L (-n) n).hom =
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding O hO
          (tensorPower O hO L (-n)) (tensorPower O hO L n)).hom ≫
        (coherentMulIso O hO L n (-n)).hom ≫
          (tensorPowerReindex O hO L (Int.add_comm n (-n))).hom :=
    congrArg Iso.hom (coherentMulIso_comm O hO L (-n) n)
  have hre := reindex_trans O hO L (Int.add_comm n (-n)) (neg_add_cancel n) (add_neg_cancel n)
  refine (congrArg (· ≫ (coherentMulIso O hO L n (-n)).hom ≫
    (tensorPowerReindex O hO L (add_neg_cancel n)).hom) hbraid).trans (Eq.symm ?_)
  refine (congrArg (· ≫ (tensorPowerReindex O hO L (neg_add_cancel n)).hom) hcomm).trans ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (Stacks.SheafOfModules.Invertible.tensorProductBraiding O hO
        (tensorPower O hO L (-n)) (tensorPower O hO L n)).hom ≫ z)
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => (coherentMulIso O hO L n (-n)).hom ≫ z) hre)))

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{v} RingCat.{v})] in
/-- The tensor product sheaf of an isomorphism with the identity is right whiskering in the strict
monoidal structure of [Stacks, Tag 01CA]. -/
theorem tensorSheafMapIso_refl_right_hom
    {A A' B : SheafOfModules.{v} (structureSheaf O hO)} (e : A ≅ A') :
    (tensorSheafMapIso O hO e (Iso.refl B)).hom = e.hom ▷ B := by
  rw [tensorSheafMapIso_hom_eq, Iso.refl_hom, MonoidalCategory.tensorHom_id]

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{v} RingCat.{v})] in
/-- **The snake identity for the coherent multiplication of [Stacks, Tag 01CU].** The contraction
`(𝒩 ⊗ L^{⊗ n}) ⊗ L^{⊗ (-n)} ≅ 𝒩` assembled from the multiplication in the bidegree `(n, -n)`
untwists, along the multiplication in the bidegree `(-n, n)`, to the identity.

The three hypotheses pin `m₁`, `m₂` and the contraction; each is `rfl` at the point of use. They
are hypotheses rather than substituted values because a goal naming both
`tensorPower O hO L 0` and `𝟙_` is not type-correct at the `implicit` transparency level. -/
theorem untwist_contract_coherentMul (N : SheafOfModules.{v} (structureSheaf O hO)) (n : ℤ)
    (m₁ : tensorPower O hO L n ⊗ tensorPower O hO L (-n) ≅
      𝟙_ (SheafOfModules.{v} (structureSheaf O hO)))
    (m₂ : tensorPower O hO L (-n) ⊗ tensorPower O hO L n ≅
      𝟙_ (SheafOfModules.{v} (structureSheaf O hO)))
    (contract : (N ⊗ tensorPower O hO L n) ⊗ tensorPower O hO L (-n) ≅ N)
    (hm₁ : m₁.hom = (coherentMulIso O hO L n (-n)).hom ≫
      (tensorPowerReindex O hO L (add_neg_cancel n)).hom)
    (hm₂ : m₂.hom = (coherentMulIso O hO L (-n) n).hom ≫
      (tensorPowerReindex O hO L (neg_add_cancel n)).hom)
    (hcontract : contract.hom =
      (tensorSheafAssociator O hO N (tensorPower O hO L n) (tensorPower O hO L (-n))).hom ≫
        (tensorSheafMapIso O hO (Iso.refl N) m₁).hom ≫
          (tensorLeftFunctorObjUnitIso O hO N).hom) :
    Stacks.Monoidal.untwist m₂ contract.hom = 𝟙 (N ⊗ tensorPower O hO L n) := by
  have := hasTrivialSelfBraiding_tensorPower O hO L n
  have hcomm : (β_ (tensorPower O hO L (-n)) (tensorPower O hO L n)).hom ≫ m₁.hom = m₂.hom := by
    rw [hm₁, hm₂]; exact braiding_comp_coherentMulIso O hO L n
  have hsnake := Stacks.Monoidal.braiding_eval_snake
    (C := SheafOfModules.{v} (structureSheaf O hO)) (L := tensorPower O hO L n)
    (L' := tensorPower O hO L (-n)) m₁.hom
  rw [hcomm] at hsnake
  have hc : contract.hom =
      (α_ N (tensorPower O hO L n) (tensorPower O hO L (-n))).hom ≫
        N ◁ m₁.hom ≫ (ρ_ N).hom := by
    have hρ : (tensorLeftFunctorObjUnitIso O hO N).hom = (ρ_ N).hom :=
      (congrArg Iso.hom (rightUnitor_eq_tensorSheafRightUnitor O hO N)).symm
    rw [hcontract, tensorSheafMapIso_hom_eq, Iso.refl_hom, MonoidalCategory.id_tensorHom,
      ← associator_eq_tensorSheafAssociator, hρ]
    rfl
  rw [hc]
  exact Stacks.Monoidal.untwist_contract_eq_id m₁ m₂ hsnake N

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{v} RingCat.{v})] in
/-- **The contraction preceded by an isomorphism of its left factor untwists to that
isomorphism.** This is `untwist_contract_coherentMul` composed with
`Stacks.Monoidal.untwist_eq_of_whiskerRight`, stated so that the whiskering appears as the tensor
product sheaf of an isomorphism with the identity, which is the form the comparison of [Stacks,
Tag 01O6]'s degreewise summands is built in. -/
theorem untwist_contract_whiskerRight_coherentMul
    {X N : SheafOfModules.{v} (structureSheaf O hO)} (n : ℤ)
    (m₁ : tensorPower O hO L n ⊗ tensorPower O hO L (-n) ≅
      𝟙_ (SheafOfModules.{v} (structureSheaf O hO)))
    (m₂ : tensorPower O hO L (-n) ⊗ tensorPower O hO L n ≅
      𝟙_ (SheafOfModules.{v} (structureSheaf O hO)))
    (contract : (N ⊗ tensorPower O hO L n) ⊗ tensorPower O hO L (-n) ≅ N)
    (shift : X ≅ N ⊗ tensorPower O hO L n)
    (w : X ⊗ tensorPower O hO L (-n) ⟶ N)
    (hm₁ : m₁.hom = (coherentMulIso O hO L n (-n)).hom ≫
      (tensorPowerReindex O hO L (add_neg_cancel n)).hom)
    (hm₂ : m₂.hom = (coherentMulIso O hO L (-n) n).hom ≫
      (tensorPowerReindex O hO L (neg_add_cancel n)).hom)
    (hcontract : contract.hom =
      (tensorSheafAssociator O hO N (tensorPower O hO L n) (tensorPower O hO L (-n))).hom ≫
        (tensorSheafMapIso O hO (Iso.refl N) m₁).hom ≫
          (tensorLeftFunctorObjUnitIso O hO N).hom)
    (hw : w = (tensorSheafMapIso O hO shift (Iso.refl (tensorPower O hO L (-n)))).hom ≫
      contract.hom) :
    Stacks.Monoidal.untwist m₂ w = shift.hom :=
  Stacks.Monoidal.untwist_eq_of_whiskerRight m₂
    (untwist_contract_coherentMul O hO L N n m₁ m₂ contract hm₁ hm₂ hcontract)
    (hw.trans (congrArg (· ≫ contract.hom) (tensorSheafMapIso_refl_right_hom O hO shift)))

end Stacks.SheafOfModules.TensorPower

namespace Stacks.AlgebraicGeometry.PullbackTwistPower

open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist toProj)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (isSheafStruct)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections
  (laurentInvLaw laurentHasInverse)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.GradedModule (shiftedGrading)
open Stacks.RelativeVeryAmple (tensorModules)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- **Untwisting the contraction against `L^{⊗ (-n)}` is the identity**, at the spelling of
[Stacks, Tag 01O6]: the contraction
`Stacks.AlgebraicGeometry.PullbackTwistPower.powContractIso` of a tensor power out of
`(𝒩 ⊗ L^{⊗ n}) ⊗ L^{⊗ (-n)}` and the insertion
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.laurentInvLaw` of the opposite
tensor power that the untwisting criterion uses cancel each other.

The two inverse laws are the coherent multiplication of [Stacks, Tag 01CU] in the bidegrees
`(n, -n)` and `(-n, n)`, so this is `untwist_contract_coherentMul` with its three hypotheses
discharged by `rfl`. -/
theorem untwist_powContractIso {Y : Scheme.{u}} {L : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y L]
    [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf (isSheafStruct Y) L]
    (N : Y.Modules) (n : ℤ) :
    Stacks.Monoidal.untwist (laurentInvLaw L n) ((powContractIso N n).hom) =
      𝟙 (tensorModules Y N (tensorPowerModule Y L n)) :=
  Stacks.SheafOfModules.TensorPower.untwist_contract_coherentMul
    Y.toRingedSpace.presheaf (isSheafStruct Y) L N n (laurentHasInverse L n).isoLeft
    (laurentInvLaw L n) (powContractIso N n) rfl rfl rfl

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)
  {Y : Scheme.{u}} (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme)
  {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]
  [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf (isSheafStruct Y) L]
  {M : Type u} {τ : Type t} [AddCommGroup M] [Module S M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The two spellings of the functorial action of the tensor product sheaf on a pair of
isomorphisms agree.** `Stacks.RelativeVeryAmple.tensorModulesMapIso` composes the two legs of the
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`, while
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso` sheafifies the tensor product of the
underlying morphisms of presheaves; both are the tensor product of the forward maps in the strict
monoidal structure of [Stacks, Tag 01CA], by
`Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom` and
`Stacks.SheafOfModules.tensorSheafMapIso_hom_eq` respectively.

The two are *not* equal by `rfl`: the left leg of the bifunctor is a sheafification of a tensor
product with an identity and the right leg another, so the composite is two sheafified morphisms
where the other spelling has one. Going through the monoidal tensor product is what identifies
them. -/
theorem tensorModulesMapIso_hom_eq_tensorSheafMapIso_hom {A A' B B' : Y.Modules} (e : A ≅ A')
    (g : B ≅ B') :
    (Stacks.RelativeVeryAmple.tensorModulesMapIso Y e g).hom =
      (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso Y.toRingedSpace.presheaf
        (isSheafStruct Y) e g).hom :=
  (Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom Y e g).trans
    (Stacks.SheafOfModules.tensorSheafMapIso_hom_eq Y.toRingedSpace.presheaf
      (isSheafStruct Y) e g).symm

/-- **The untwisting of `pullbackShiftedContractIso` is `pullbackShiftedIso`.** The degree-`n`
comparison

`φ^*(ℳ(dn)~) ⊗ L^{⊗ (-n)} ≅ φ^*ℳ̃`

of property (1) of [Stacks, Tag 01O7] is, after the untwisting that makes a balancing relation of
[Stacks, Tag 01O6] checkable on global sections, the comparison
`φ^*(ℳ(dn)~) ≅ φ^*ℳ̃ ⊗ L^{⊗ n}` it was built from — the contraction and the insertion cancel.

This is the normalisation the balancing relations consume: it removes the tensor powers of `L`
from the verification, leaving the interaction of the comparison with the action of `𝒜` and
with `ψ`, which is not proved here. -/
theorem untwist_pullbackShiftedContractIso (α : pullbackTwist 𝒮 φ (d : ℤ) ≅ L) (n : ℤ) :
    Stacks.Monoidal.untwist (laurentInvLaw L n)
        ((pullbackShiftedContractIso 𝒮 d φ 𝒨 α n).hom) =
      (pullbackShiftedIso 𝒮 d φ 𝒨 α n).hom :=
  Stacks.SheafOfModules.TensorPower.untwist_contract_whiskerRight_coherentMul
    Y.toRingedSpace.presheaf (isSheafStruct Y) L n (laurentHasInverse L n).isoLeft
    (laurentInvLaw L n)
    (powContractIso ((Scheme.Modules.pullback (toProj 𝒮 φ)).obj (associatedModuleSheaf 𝒮 𝒨)) n)
    (pullbackShiftedIso 𝒮 d φ 𝒨 α n) _ rfl rfl rfl
    (congrArg (· ≫ (powContractIso ((Scheme.Modules.pullback (toProj 𝒮 φ)).obj
        (associatedModuleSheaf 𝒮 𝒨)) n).hom)
      (tensorModulesMapIso_hom_eq_tensorSheafMapIso_hom (pullbackShiftedIso 𝒮 d φ 𝒨 α n)
        (Iso.refl (tensorPowerModule Y L (-n)))))

end Stacks.AlgebraicGeometry.PullbackTwistPower

end

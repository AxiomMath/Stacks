module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairGroup

/-!
# The tensor product of pairs is associative

A pair on a scheme is an invertible sheaf together with a trivialization of its `n`-th tensor
power, and `AlgebraicGeometry.tensorPair` is the tensor product of two pairs. This file proves
that the tensor product of three pairs is associative up to isomorphism of pairs, the
associativity constraint of the invertible sheaves being the isomorphism that realizes it.

## Main results

* `AlgebraicGeometry.tensorMu_eq_tensorDelta`: **in a symmetric monoidal category the
  middle-four interchange with its two middle arguments exchanged is the inverse interchange.**
  This is what turns `CategoryTheory.MonoidalCategory.tensor_associativity`, which is stated for
  the interchange in one grouping, into the identity the recursion below needs.
* `AlgebraicGeometry.tensorMu_assoc_core`: **the associativity of the middle-four interchange in
  the grouping the tensor-power comparison produces.**
* `AlgebraicGeometry.tpowTensorIso_assoc`: **the tensor-power comparison is associative.**
  Proved by induction out of `AlgebraicGeometry.tensorMu_assoc_whisker_step`.
* `AlgebraicGeometry.tensorTriv_assoc`: **the trivialization of a tensor product of three pairs
  does not depend on the bracketing**, once transported along the associativity constraint.
* `AlgebraicGeometry.pairIsoTensorPairAssoc`: **the tensor product of pairs is associative up to
  isomorphism of pairs**, and `AlgebraicGeometry.tensorPairClass_assoc` is the resulting
  associativity on isomorphism classes.

## Implementation notes

The monoidal coherences are isolated as statements of an abstract symmetric monoidal category
and applied to sheaves of modules by `exact`, exactly as the two unit laws of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairGroup` are.

The inductive step is stated in the shape the recursion leaves it in — with the successor
comparison of the inner tensor product and its inverse still present, cancelled inside the step
by the hypotheses `hp` and `hq` — because those two occurrences sit inside tensor products of
morphisms rather than next to each other, so `simp` does not cancel them.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible (tensorPower tensorProductAssociator)

universe u v w

namespace AlgebraicGeometry

attribute [local instance] ringedSiteModulesMonoidal ringedSiteModulesSymmetric
  isInvertible_tensorObj isInvertible_unitRingedSite isInvertible_tensorUnitRingedSite
  isInvertible_schemeRingedSite

/-! ### Splitting a tensor product of a composite -/

/-- A tensor product whose first factor is a composite, split into two tensor products. -/
private theorem tensorHom_comp_left {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A₁ A₂ A₃ B₁ B₂ : D} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (k : B₁ ⟶ B₂) :
    (f ≫ g) ⊗ₘ k = (f ⊗ₘ 𝟙 B₁) ≫ (g ⊗ₘ k) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- A tensor product whose second factor is a composite, split into two tensor products. -/
private theorem tensorHom_comp_right {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A₁ A₂ A₃ B₁ B₂ : D} (k : B₁ ⟶ B₂) (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    k ⊗ₘ (f ≫ g) = (𝟙 B₁ ⊗ₘ f) ≫ (k ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- A tensor product whose first factor is a threefold composite, split into three tensor
products. -/
theorem tensorHom_left_comp_three {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A₁ A₂ A₃ A₄ B₁ B₂ : D} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (h : A₃ ⟶ A₄) (k : B₁ ⟶ B₂) :
    (f ≫ g ≫ h) ⊗ₘ k = (f ⊗ₘ 𝟙 B₁) ≫ (g ⊗ₘ 𝟙 B₁) ≫ (h ⊗ₘ k) := by
  rw [tensorHom_comp_left, tensorHom_comp_left]

/-- A tensor product whose second factor is a threefold composite, split into three tensor
products. -/
theorem tensorHom_right_comp_three {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A₁ A₂ A₃ A₄ B₁ B₂ : D} (k : B₁ ⟶ B₂) (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (h : A₃ ⟶ A₄) :
    k ⊗ₘ (f ≫ g ≫ h) = (𝟙 B₁ ⊗ₘ f) ≫ (𝟙 B₁ ⊗ₘ g) ≫ (k ⊗ₘ h) := by
  rw [tensorHom_comp_right, tensorHom_comp_right]

/-! ### The monoidal coherences behind the associativity -/

/-- **In a symmetric monoidal category the middle-four interchange with its two middle arguments
exchanged is the inverse interchange.** Both morphisms exchange the two middle factors of a
fourfold tensor product; they differ only in which of the two inverse braidings of the symmetry
they use, so the braiding alone does not suffice. -/
theorem tensorMu_eq_tensorDelta {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] (A B L M : D) :
    tensorμ A L B M = tensorδ A B L M := by
  simp [tensorμ, tensorδ, SymmetricCategory.braiding_swap_eq_inv_braiding B L]

/-- **The associativity of the middle-four interchange, in the grouping the tensor-power
comparison produces.** `CategoryTheory.MonoidalCategory.tensor_associativity` states the same
coherence with the interchanges grouped the other way; the two are exchanged by
`AlgebraicGeometry.tensorMu_eq_tensorDelta`, which identifies each interchange appearing there
with the inverse of one appearing here. -/
theorem tensorMu_assoc_core {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] (A B C L M N : D) :
    tensorμ (A ⊗ B) C (L ⊗ M) N ≫ (tensorμ A B L M ⊗ₘ 𝟙 (C ⊗ N)) ≫
        (α_ (A ⊗ L) (B ⊗ M) (C ⊗ N)).hom =
      ((α_ A B C).hom ⊗ₘ (α_ L M N).hom) ≫ tensorμ A (B ⊗ C) L (M ⊗ N) ≫
        (𝟙 (A ⊗ L) ⊗ₘ tensorμ B C M N) := by
  rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  have key := MonoidalCategory.tensor_associativity (C := D) A L B M C N
  rw [tensorMu_eq_tensorDelta A B L M, tensorMu_eq_tensorDelta (A ⊗ B) C (L ⊗ M) N,
    tensorMu_eq_tensorDelta B C M N, tensorMu_eq_tensorDelta A (B ⊗ C) L (M ⊗ N)] at key
  have hP : (tensorμ A B L M ▷ (C ⊗ N)) ≫ (tensorδ A B L M ▷ (C ⊗ N)) =
      𝟙 (((A ⊗ B) ⊗ (L ⊗ M)) ⊗ (C ⊗ N)) := by
    rw [← MonoidalCategory.comp_whiskerRight, tensorμ_tensorδ,
      MonoidalCategory.id_whiskerRight]
  have hT : ((A ⊗ L) ◁ tensorδ B C M N) ≫ ((A ⊗ L) ◁ tensorμ B C M N) =
      𝟙 ((A ⊗ L) ⊗ ((B ⊗ M) ⊗ (C ⊗ N))) := by
    rw [← MonoidalCategory.whiskerLeft_comp, tensorδ_tensorμ,
      MonoidalCategory.whiskerLeft_id]
  have h1 : tensorμ (A ⊗ B) C (L ⊗ M) N ≫ (tensorμ A B L M ▷ (C ⊗ N)) ≫
        ((α_ (A ⊗ L) (B ⊗ M) (C ⊗ N)).hom ≫ ((A ⊗ L) ◁ tensorδ B C M N) ≫
          tensorδ A (B ⊗ C) L (M ⊗ N)) =
      ((α_ A B C).hom ⊗ₘ (α_ L M N).hom) := by
    rw [← key, ← Category.assoc, ← Category.assoc, Category.assoc
      (tensorμ (A ⊗ B) C (L ⊗ M) N), hP, Category.comp_id, tensorμ_tensorδ_assoc]
  calc tensorμ (A ⊗ B) C (L ⊗ M) N ≫ (tensorμ A B L M ▷ (C ⊗ N)) ≫
        (α_ (A ⊗ L) (B ⊗ M) (C ⊗ N)).hom
      = tensorμ (A ⊗ B) C (L ⊗ M) N ≫ (tensorμ A B L M ▷ (C ⊗ N)) ≫
          ((α_ (A ⊗ L) (B ⊗ M) (C ⊗ N)).hom ≫ ((A ⊗ L) ◁ tensorδ B C M N) ≫
            tensorδ A (B ⊗ C) L (M ⊗ N)) ≫
            tensorμ A (B ⊗ C) L (M ⊗ N) ≫ ((A ⊗ L) ◁ tensorμ B C M N) := by
        simp only [Category.assoc, tensorδ_tensorμ_assoc, hT, Category.comp_id]
    _ = _ := by
        rw [← Category.assoc (tensorμ A B L M ▷ (C ⊗ N)), ← Category.assoc, h1]

/-- **The inductive step of the associativity of the tensor-power comparison**, isolated as an
identity of a symmetric monoidal category. Both sides are read after the leading inverse
successor comparison has been cancelled; the hypothesis `ih` is the associativity at the
previous exponent. -/
theorem tensorMu_assoc_step {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] {W W' A B C L M N A' B' C' P Q : D}
    (pg : W ⟶ W') (TL : W ⟶ P ⊗ C) (TR : W' ⟶ A ⊗ Q)
    (u : P ⟶ A ⊗ B) (v : Q ⟶ B ⊗ C)
    (sl : A ⊗ L ⟶ A') (sm : B ⊗ M ⟶ B') (sn : C ⊗ N ⟶ C')
    (ih : TL ≫ (u ⊗ₘ 𝟙 C) ≫ (α_ A B C).hom = pg ≫ TR ≫ (𝟙 A ⊗ₘ v)) :
    (TL ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫ tensorμ P C (L ⊗ M) N ≫
        (((u ⊗ₘ 𝟙 (L ⊗ M)) ≫ tensorμ A B L M ≫ (sl ⊗ₘ sm)) ⊗ₘ sn) ≫ (α_ A' B' C').hom =
      (pg ⊗ₘ (α_ L M N).hom) ≫ (TR ⊗ₘ 𝟙 (L ⊗ (M ⊗ N))) ≫ tensorμ A Q L (M ⊗ N) ≫
        (sl ⊗ₘ ((v ⊗ₘ 𝟙 (M ⊗ N)) ≫ tensorμ B C M N ≫ (sm ⊗ₘ sn))) := by
  have hL : (TL ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫ tensorμ P C (L ⊗ M) N ≫
        (((u ⊗ₘ 𝟙 (L ⊗ M)) ≫ tensorμ A B L M ≫ (sl ⊗ₘ sm)) ⊗ₘ sn) ≫ (α_ A' B' C').hom =
      ((TL ≫ (u ⊗ₘ 𝟙 C)) ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫
        (tensorμ (A ⊗ B) C (L ⊗ M) N ≫ (tensorμ A B L M ⊗ₘ 𝟙 (C ⊗ N)) ≫
          (α_ (A ⊗ L) (B ⊗ M) (C ⊗ N)).hom) ≫ (sl ⊗ₘ (sm ⊗ₘ sn)) := by
    rw [tensorHom_left_comp_three, Category.assoc, Category.assoc,
      MonoidalCategory.associator_naturality,
      ← Category.assoc (tensorμ P C (L ⊗ M) N),
      show tensorμ P C (L ⊗ M) N ≫ ((u ⊗ₘ 𝟙 (L ⊗ M)) ⊗ₘ 𝟙 (C ⊗ N)) =
          ((u ⊗ₘ 𝟙 C) ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫ tensorμ (A ⊗ B) C (L ⊗ M) N from by
        rw [← MonoidalCategory.id_tensorHom_id C N, ← MonoidalCategory.tensorμ_natural,
          MonoidalCategory.id_tensorHom_id]]
    simp only [Category.assoc]
    rw [← Category.assoc (TL ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)),
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have hR : (pg ⊗ₘ (α_ L M N).hom) ≫ (TR ⊗ₘ 𝟙 (L ⊗ (M ⊗ N))) ≫ tensorμ A Q L (M ⊗ N) ≫
        (sl ⊗ₘ ((v ⊗ₘ 𝟙 (M ⊗ N)) ≫ tensorμ B C M N ≫ (sm ⊗ₘ sn))) =
      ((TL ≫ (u ⊗ₘ 𝟙 C)) ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫
        (((α_ A B C).hom ⊗ₘ (α_ L M N).hom) ≫ tensorμ A (B ⊗ C) L (M ⊗ N) ≫
          (𝟙 (A ⊗ L) ⊗ₘ tensorμ B C M N)) ≫ (sl ⊗ₘ (sm ⊗ₘ sn)) := by
    rw [tensorHom_right_comp_three, ← Category.assoc (tensorμ A Q L (M ⊗ N)),
      show tensorμ A Q L (M ⊗ N) ≫ (𝟙 (A ⊗ L) ⊗ₘ (v ⊗ₘ 𝟙 (M ⊗ N))) =
          ((𝟙 A ⊗ₘ v) ⊗ₘ 𝟙 (L ⊗ (M ⊗ N))) ≫ tensorμ A (B ⊗ C) L (M ⊗ N) from by
        rw [← MonoidalCategory.id_tensorHom_id A L, ← MonoidalCategory.tensorμ_natural,
          MonoidalCategory.id_tensorHom_id]]
    simp only [Category.assoc]
    rw [← Category.assoc (TR ⊗ₘ 𝟙 (L ⊗ (M ⊗ N))), MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, ← Category.assoc (pg ⊗ₘ (α_ L M N).hom),
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, ← ih,
      show ((TL ≫ (u ⊗ₘ 𝟙 C) ≫ (α_ A B C).hom) ⊗ₘ (α_ L M N).hom) =
          ((TL ≫ (u ⊗ₘ 𝟙 C)) ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫
            ((α_ A B C).hom ⊗ₘ (α_ L M N).hom) from by
        rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.assoc]]
    simp only [Category.assoc]
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact congrArg (fun z => ((TL ≫ (u ⊗ₘ 𝟙 C)) ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫ z ≫
    (sl ⊗ₘ (sm ⊗ₘ sn))) (tensorMu_assoc_core A B C L M N)

/-- **The inductive step of the associativity of the tensor-power comparison, in the shape the
recursion leaves it in.** The successor comparisons of the two inner tensor products are
cancelled against their inverses by `hp` and `hq`; they are not adjacent in the composite, each
sitting inside a tensor product of morphisms, which is why they are carried here rather than
cancelled beforehand. -/
theorem tensorMu_assoc_whisker_step {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] {W W' A B C L M N A' B' C' P Q R S : D}
    (pg : W ⟶ W') (TL : W ⟶ P ⊗ C) (TR : W' ⟶ A ⊗ Q)
    (u : P ⟶ A ⊗ B) (v : Q ⟶ B ⊗ C)
    (sl : A ⊗ L ⟶ A') (sm : B ⊗ M ⟶ B') (sn : C ⊗ N ⟶ C')
    (p : P ⊗ (L ⊗ M) ⟶ R) (pinv : R ⟶ P ⊗ (L ⊗ M)) (hp : p ≫ pinv = 𝟙 (P ⊗ (L ⊗ M)))
    (q : Q ⊗ (M ⊗ N) ⟶ S) (qinv : S ⟶ Q ⊗ (M ⊗ N)) (hq : q ≫ qinv = 𝟙 (Q ⊗ (M ⊗ N)))
    (ih : TL ≫ (u ⊗ₘ 𝟙 C) ≫ (α_ A B C).hom = pg ≫ TR ≫ (𝟙 A ⊗ₘ v)) :
    (TL ⊗ₘ 𝟙 ((L ⊗ M) ⊗ N)) ≫ tensorμ P C (L ⊗ M) N ≫ (p ⊗ₘ sn) ≫
        ((pinv ≫ (u ⊗ₘ 𝟙 (L ⊗ M)) ≫ tensorμ A B L M ≫ (sl ⊗ₘ sm)) ⊗ₘ 𝟙 C') ≫
          (α_ A' B' C').hom =
      (pg ⊗ₘ (α_ L M N).hom) ≫ (TR ⊗ₘ 𝟙 (L ⊗ (M ⊗ N))) ≫ tensorμ A Q L (M ⊗ N) ≫
        (sl ⊗ₘ q) ≫
          (𝟙 A' ⊗ₘ (qinv ≫ (v ⊗ₘ 𝟙 (M ⊗ N)) ≫ tensorμ B C M N ≫ (sm ⊗ₘ sn))) := by
  have hpm : (p ⊗ₘ sn) ≫
        ((pinv ≫ (u ⊗ₘ 𝟙 (L ⊗ M)) ≫ tensorμ A B L M ≫ (sl ⊗ₘ sm)) ⊗ₘ 𝟙 C') =
      (((u ⊗ₘ 𝟙 (L ⊗ M)) ≫ tensorμ A B L M ≫ (sl ⊗ₘ sm)) ⊗ₘ sn) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, ← Category.assoc, hp,
      Category.id_comp]
  have hqm : (sl ⊗ₘ q) ≫
        (𝟙 A' ⊗ₘ (qinv ≫ (v ⊗ₘ 𝟙 (M ⊗ N)) ≫ tensorμ B C M N ≫ (sm ⊗ₘ sn))) =
      (sl ⊗ₘ ((v ⊗ₘ 𝟙 (M ⊗ N)) ≫ tensorμ B C M N ≫ (sm ⊗ₘ sn))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, ← Category.assoc, hq,
      Category.id_comp]
  rw [← Category.assoc (p ⊗ₘ sn), hpm, hqm]
  exact tensorMu_assoc_step pg TL TR u v sl sm sn ih

/-- The base case of the associativity of the tensor-power comparison: at the zero exponent the
comparison is an inverse unit constraint, and what is left is a coherence of the unit object. -/
theorem rightUnitor_inv_assoc_unit {D : Type w} [Category.{v} D] [MonoidalCategory D] :
    (ρ_ (𝟙_ D)).inv ≫ ((ρ_ (𝟙_ D)).inv ⊗ₘ 𝟙 (𝟙_ D)) ≫ (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).hom =
      (ρ_ (𝟙_ D)).inv ≫ (𝟙 (𝟙_ D) ⊗ₘ (ρ_ (𝟙_ D)).inv) := by
  monoidal

/-- **Three morphisms to the unit object, multiplied by the right unit constraint, associate.**
The right unit constraint of the unit object is the multiplication of the unit monoid, and this
is its associativity. -/
theorem tensorHom_assoc_rightUnitor {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A B C : D} (a : A ⟶ 𝟙_ D) (b : B ⟶ 𝟙_ D) (c : C ⟶ 𝟙_ D) :
    (((a ⊗ₘ b) ≫ (ρ_ (𝟙_ D)).hom) ⊗ₘ c) ≫ (ρ_ (𝟙_ D)).hom =
      (α_ A B C).hom ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ (ρ_ (𝟙_ D)).hom)) ≫ (ρ_ (𝟙_ D)).hom := by
  have hcoh : ((ρ_ (𝟙_ D)).hom ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom =
      (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).hom ≫ (𝟙 (𝟙_ D) ⊗ₘ (ρ_ (𝟙_ D)).hom) ≫
        (ρ_ (𝟙_ D)).hom := by monoidal
  calc (((a ⊗ₘ b) ≫ (ρ_ (𝟙_ D)).hom) ⊗ₘ c) ≫ (ρ_ (𝟙_ D)).hom
      = ((a ⊗ₘ b) ⊗ₘ c) ≫ ((ρ_ (𝟙_ D)).hom ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom := by
        rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    _ = ((a ⊗ₘ b) ⊗ₘ c) ≫ (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).hom ≫
          (𝟙 (𝟙_ D) ⊗ₘ (ρ_ (𝟙_ D)).hom) ≫ (ρ_ (𝟙_ D)).hom := by rw [hcoh]
    _ = ((α_ A B C).hom ≫ (a ⊗ₘ (b ⊗ₘ c))) ≫
          (𝟙 (𝟙_ D) ⊗ₘ (ρ_ (𝟙_ D)).hom) ≫ (ρ_ (𝟙_ D)).hom := by
        rw [← MonoidalCategory.associator_naturality a b c]
        simp only [Category.assoc]
    _ = _ := by
        rw [Category.assoc, ← Category.assoc (a ⊗ₘ (b ⊗ₘ c)),
          MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-! ### The tensor-power comparison is associative -/

/-- **The tensor-power comparison is associative**: comparing the `n`-th power of `(L ⊗ M) ⊗ N`
with `(L^{⊗ n} ⊗ M^{⊗ n}) ⊗ N^{⊗ n}` and reassociating is the same as taking the `n`-th power of
the associativity constraint first and then comparing in the other bracketing. -/
theorem tpowTensorIso_assoc (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 N] (n : ℕ) :
    (tpowTensorIso X (L ⊗ M) N n).hom ≫
        ((tpowTensorIso X L M n).hom ⊗ₘ 𝟙 (tpow X N n)) ≫
          (α_ (tpow X L n) (tpow X M n) (tpow X N n)).hom =
      (powerMap X (α_ L M N) n).hom ≫ (tpowTensorIso X L (M ⊗ N) n).hom ≫
        (𝟙 (tpow X L n) ⊗ₘ (tpowTensorIso X M N n).hom) := by
  induction n with
  | zero => exact rightUnitor_inv_assoc_unit
  | succ k ih =>
    show (tpowTensorIso X (L ⊗ M) N (k + 1)).hom ≫
        ((tpowTensorIso X L M (k + 1)).hom ⊗ₘ 𝟙 (tpow X N (k + 1))) ≫
          (α_ (tpow X L (k + 1)) (tpow X M (k + 1)) (tpow X N (k + 1))).hom =
      (powerMap X (α_ L M N) (k + 1)).hom ≫ (tpowTensorIso X L (M ⊗ N) (k + 1)).hom ≫
        (𝟙 (tpow X L (k + 1)) ⊗ₘ (tpowTensorIso X M N (k + 1)).hom)
    simp only [powerMap_succ_tensorIsoOfModules, tpowTensorIso_succ, Iso.trans_hom, Iso.symm_hom,
      Iso.refl_hom, tensorIsoOfModules_hom, tensorInterchangeIso_hom, ← tensorObj_eq,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun z => (tpowSuccIso X ((L ⊗ M) ⊗ N) k).inv ≫ z)
      (tensorMu_assoc_whisker_step (powerMap X (α_ L M N) k).hom
        (tpowTensorIso X (L ⊗ M) N k).hom (tpowTensorIso X L (M ⊗ N) k).hom
        (tpowTensorIso X L M k).hom (tpowTensorIso X M N k).hom
        (tpowSuccIso X L k).hom (tpowSuccIso X M k).hom (tpowSuccIso X N k).hom
        (tpowSuccIso X (L ⊗ M) k).hom (tpowSuccIso X (L ⊗ M) k).inv (Iso.hom_inv_id _)
        (tpowSuccIso X (M ⊗ N) k).hom (tpowSuccIso X (M ⊗ N) k).inv (Iso.hom_inv_id _) ih)

/-- **The trivialization of a tensor product of three pairs does not depend on the bracketing**,
read as an identity of an abstract monoidal category: the three trivializations enter only as
morphisms to the unit object, and `hassoc` is the associativity of the tensor-power
comparison. -/
theorem tensorTriv_assoc_core {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {V V' A B C P Q : D}
    (pg : V ⟶ V') (TL : V ⟶ P ⊗ C) (TR : V' ⟶ A ⊗ Q) (u : P ⟶ A ⊗ B) (v : Q ⟶ B ⊗ C)
    (a : A ⟶ 𝟙_ D) (b : B ⟶ 𝟙_ D) (c : C ⟶ 𝟙_ D)
    (hassoc : TL ≫ (u ⊗ₘ 𝟙 C) ≫ (α_ A B C).hom = pg ≫ TR ≫ (𝟙 A ⊗ₘ v)) :
    (TL ≫ (((u ≫ (a ⊗ₘ b)) ≫ (ρ_ (𝟙_ D)).hom) ⊗ₘ c)) ≫ (ρ_ (𝟙_ D)).hom =
      pg ≫ ((TR ≫ (a ⊗ₘ ((v ≫ (b ⊗ₘ c)) ≫ (ρ_ (𝟙_ D)).hom))) ≫ (ρ_ (𝟙_ D)).hom) := by
  have hmerge : (𝟙 A ⊗ₘ v) ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ (ρ_ (𝟙_ D)).hom)) =
      (a ⊗ₘ ((v ≫ (b ⊗ₘ c)) ≫ (ρ_ (𝟙_ D)).hom)) := by
    rw [Category.assoc v, tensorHom_comp_right a v]
  rw [Category.assoc u, tensorHom_comp_left, ← hmerge]
  simp only [Category.assoc]
  rw [tensorHom_assoc_rightUnitor, ← Category.assoc (u ⊗ₘ 𝟙 C), ← Category.assoc TL, hassoc]
  simp only [Category.assoc]

/-- **The trivialization of a tensor product of three pairs does not depend on the
bracketing**, once transported along the `n`-th power of the associativity constraint. -/
theorem tensorTriv_assoc (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 N] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (cl : tpow X N n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    powerMap X (α_ L M N) n ≪≫
        tensorTriv X L (M ⊗ N) n al (tensorTriv X M N n bl cl) =
      tensorTriv X (L ⊗ M) N n (tensorTriv X L M n al bl) cl :=
  Iso.ext (tensorTriv_assoc_core (powerMap X (α_ L M N) n).hom
    (tpowTensorIso X (L ⊗ M) N n).hom (tpowTensorIso X L (M ⊗ N) n).hom
    (tpowTensorIso X L M n).hom (tpowTensorIso X M N n).hom al.hom bl.hom cl.hom
    (tpowTensorIso_assoc X L M N n)).symm

/-! ### The tensor product of pairs is associative -/

/-- **The tensor product of pairs is associative up to isomorphism of pairs**: the isomorphism
of invertible sheaves is the associativity constraint, and its compatibility with the
trivializations is `AlgebraicGeometry.tensorTriv_assoc`. -/
def pairIsoTensorPairAssoc {S : Scheme.{u}} {n : ℕ} (P Q R : TrivializedPower S n) :
    PairIso (tensorPair S n (tensorPair S n P Q) R)
      (tensorPair S n P (tensorPair S n Q R)) where
  sheafIso := tensorProductAssociator S.presheaf (ringSheafCond S) P.sheaf Q.sheaf R.sheaf
  compatible := by
    let := P.invertible
    let := Q.invertible
    let := R.invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj P.sheaf).obj Q.sheaf)) :=
      (tensorPair S n P Q).invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj Q.sheaf).obj R.sheaf)) :=
      (tensorPair S n Q R).invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
              (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj P.sheaf).obj Q.sheaf))).obj
          R.sheaf)) :=
      (tensorPair S n (tensorPair S n P Q) R).invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj P.sheaf).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
              (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj Q.sheaf).obj R.sheaf)))) :=
      (tensorPair S n P (tensorPair S n Q R)).invertible
    refine Eq.trans (congrArg
      (fun z => z ≪≫ (tensorPair S n P (tensorPair S n Q R)).trivialization)
      (tensorPowerMap_eq_powerMap S
        (tensorProductAssociator S.presheaf (ringSheafCond S) P.sheaf Q.sheaf R.sheaf) n)) ?_
    exact tensorTriv_assoc (schemeRingedSite S) P.sheaf Q.sheaf R.sheaf n
      P.trivialization Q.trivialization R.trivialization

/-- **The tensor product of isomorphism classes of pairs is associative.** -/
theorem tensorPairClass_assoc (S : Scheme.{u}) (n : ℕ) (x y z : PairClasses S n) :
    tensorPairClass S n (tensorPairClass S n x y) z =
      tensorPairClass S n x (tensorPairClass S n y z) :=
  Quotient.inductionOn₃ x y z fun P Q R => (pairClass_eq_iff _ _).2 ⟨pairIsoTensorPairAssoc P Q R⟩

end AlgebraicGeometry

end

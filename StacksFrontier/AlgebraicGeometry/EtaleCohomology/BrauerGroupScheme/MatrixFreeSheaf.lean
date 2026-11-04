module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AlgebraSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTensorFree
public import StacksFrontier.AlgebraicTopology.EilenbergMacLane
public import StacksFrontier.CategoryTheory.Monoidal.UnitEndomorphism

/-!
# A matrix dictionary for free sheaves of modules on a scheme

Let `S` be a scheme and let `Mod(𝒪_S)` be the sheaves of `𝒪_S`-modules with the tensor product
sheaf of [Stacks, Tag 01CA], in the spelling
`Stacks.EtaleCohomology.BrauerScheme.ModuleSheaf` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AlgebraSheaf`.

A free sheaf of modules on a finite index type is a finite direct sum of copies of the monoidal
unit `𝒪_S`, so its endomorphisms are square matrices over the endomorphism ring of the unit.
That endomorphism ring is *commutative* — this is the classical Eckmann–Hilton computation, read
off the right unit constraint — so the dictionary is a dictionary of matrices over a commutative
ring, and composition of endomorphisms is matrix multiplication with no order reversal to watch.

## Main definitions

* `CategoryTheory.MonoidalCategory.commRingUnitEnd`: `End (𝟙_ C)` is a **commutative** ring in a
  preadditive monoidal category.
* `Stacks.EtaleCohomology.BrauerScheme.R₀`: the coefficient ring `End (𝟙_ (ModuleSheaf S))`.
* `Stacks.EtaleCohomology.BrauerScheme.freeBiproductIso`: a free sheaf of modules on
  `ULift I` for a finite `I : Type 0` is the biproduct of `I` copies of `𝒪_S`.
* `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv`: endomorphisms of that free sheaf are
  `I × I` matrices over `R₀ S`.
* `CategoryTheory.MonoidalCategory.unitMatrixEquiv`: endomorphisms of a finite direct sum of
  copies of the unit are square matrices over `End (𝟙_ C)`, with `unitMatrixEquiv_id`,
  `unitMatrixEquiv_comp` and `unitMatrixEquiv_tensorHom` the three laws.
* `CategoryTheory.MonoidalCategory.unitTensorBiproductIso`: the standard-basis identification
  `(⨁_I 𝟙) ⊗ (⨁_K 𝟙) ≅ ⨁_{I × K} 𝟙`, and
  `Stacks.EtaleCohomology.BrauerScheme.freeTensorFreeBiproductIso` the same for free sheaves of
  modules, `free (ULift I) ⊗ free (ULift K) ≅ free (ULift (I × K))`.

## Main results

* `CategoryTheory.MonoidalCategory.comp_comm_unitEnd`: **endomorphisms of the tensor unit
  commute.**
* `CategoryTheory.MonoidalCategory.iso_unit_conj_tensorHom`: for *any* isomorphism
  `w : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C`, conjugating `a ⊗ₘ b` by `w` gives `a ≫ b`. No coherence is needed
  beyond the previous item: two such isomorphisms differ by an automorphism of `𝟙_ C`, and those
  commute with everything.
* `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_id` and
  `freeEndMatrixEquiv_comp`: the dictionary takes `𝟙` to `1` and **composition in diagrammatic
  order to the matrix product in the same order**, `M (f ≫ g) = M f * M g`. The order does not
  reverse because `R₀ S` is commutative; see the implementation notes.
* `Stacks.EtaleCohomology.BrauerScheme.freeEndRingEquiv`: the dictionary packaged as a ring
  isomorphism `End (free (ULift I)) ≃+* Matrix I I (R₀ S)`, which needs the transpose.
* `CategoryTheory.MonoidalCategory.unitMatrixEquiv_tensorHom` and
  `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_tensorHom`: **the Kronecker law.**
  Under the standard-basis identification `free (ULift I) ⊗ free (ULift K) ≅ free (ULift (I×K))`
  the morphism `f ⊗ₘ g` has matrix the Kronecker product: its entry at `((i,k), (i',k'))` is
  `(matrix of f) i i' * (matrix of g) k k'`.

## Implementation notes

**Which multiplication order is true.** `CategoryTheory.End` multiplies in the order of
`Function.comp`, `x * y = y ≫ x`. `freeEndMatrixEquiv` is stated as a plain `Equiv` and the
composition law is written in diagrammatic order, `M (f ≫ g) = M f * M g`; this is the true
statement, and it is true with the matrix product in that order *because* `R₀ S` is commutative
(`comp_comm_unitEnd`). Over a noncommutative coefficient ring the entrywise identity
`components (F ≫ G) j l = ∑ k, components F j k ≫ components G k l` is anti-multiplicative in
`End`'s convention, and no order of the matrix product makes it a ring map. For the same reason
`freeEndRingEquiv`, which is a ring map out of `End (free (ULift I))` with `End`'s own
multiplication, has to transpose: transposition is an anti-automorphism of a matrix ring, and it
undoes the one reversal that `End`'s convention introduces.

**The index type lies in `Type 0`.** `CategoryTheory.Limits.biproduct.matrix` and
`biproduct.matrixEquiv` require it, while `SheafOfModules.free` takes its index in the universe
of the sheaf of modules; hence the `ULift.{u, 0}`, exactly as in
`Stacks.EtaleCohomology.BrauerScheme.matrixAlgebra`.

**Which isomorphism `free I ⊗ free K ≅ free (I × K)`.** The one used here,
`freeTensorFreeBiproductIso`, is built from the distributivity of the tensor product over finite
direct sums (`CategoryTheory.rightDistributor` and `leftDistributor`), so it is the
standard-basis map `e_i ⊗ e_k ↦ e_{(i,k)}` and the Kronecker law is a computation with
`biproduct.ι` and `biproduct.π`. `Stacks.SheafOfModules.freeTensorFreeIso` is the same map, but
it is assembled from `PreservesCoproduct.iso`, `Stacks.TensorCoherence.tensorSheafUnitIso` and
`SheafOfModules.freeSigmaIso`, and identifying it with this one means computing the whiskering
`f ▷ F` of the strict structure through the `Stacks.sheafTensorRight` spelling of the same
endofunctor. Those two are only *isomorphic*, by
`Stacks.SheafOfModules.sheafTensorRightIso`, which is a whiskering of
`Stacks.SheafOfModules.tensorRightIso` and not an identity, so the crossing is a genuine
computation and not a defeq — it is the crossing `FreeTensorFree`'s own implementation notes
record as the thing that file keeps inside its proofs. That identification is not done here.

**`HasFiniteBiproducts (ModuleSheaf S)` and `MonoidalPreadditive (ModuleSheaf S)`** are local
instances: the first is `HasFiniteBiproducts.of_hasFiniteProducts`, as in
`StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.LocallyFree`; the second is
`Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf`, which is deliberately not an
instance upstream because the monoidal structure it is stated at is not one either.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe v u

noncomputable section

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Endomorphisms of the tensor unit commute.** The interchange law writes `a ⊗ₘ b` both as
`(a ▷ 𝟙) ≫ (𝟙 ◁ b)` and as `(𝟙 ◁ b) ≫ (a ▷ 𝟙)`; reading the two through the right unit
constraint, and using that the two unitors of the unit agree, gives `a ≫ b` on one side and
`b ≫ a` on the other. -/
theorem comp_comm_unitEnd (a b : 𝟙_ C ⟶ 𝟙_ C) : a ≫ b = b ≫ a := by
  have h1 : (ρ_ (𝟙_ C)).hom ≫ (a ≫ b) = (a ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom :=
    (tensorHom_unitEnd_comp_rightUnitor a b).symm
  have h2 : (a ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ (b ≫ a) := by
    rw [tensorHom_def', Category.assoc, rightUnitor_naturality, ← unitors_equal,
      leftUnitor_naturality_assoc]
  exact (cancel_epi (ρ_ (𝟙_ C)).hom).mp (h1.trans h2)

/-- **Conjugating `a ⊗ₘ b` by any isomorphism `𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C` gives `a ≫ b`.** The right
unit constraint is one such isomorphism and `tensorHom_unitEnd_comp_rightUnitor` is this
statement for it; any other differs from it by an automorphism of `𝟙_ C`, and by
`comp_comm_unitEnd` that automorphism cancels. -/
theorem iso_unit_conj_tensorHom (w : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C) (a b : 𝟙_ C ⟶ 𝟙_ C) :
    w.inv ≫ (a ⊗ₘ b) ≫ w.hom = a ≫ b := by
  obtain ⟨q, hq⟩ : ∃ q : 𝟙_ C ⟶ 𝟙_ C, w.hom = (ρ_ (𝟙_ C)).hom ≫ q :=
    ⟨(ρ_ (𝟙_ C)).inv ≫ w.hom, by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]⟩
  rw [Iso.inv_comp_eq, hq, Category.assoc, ← comp_comm_unitEnd (a ≫ b) q,
    reassoc_of% tensorHom_unitEnd_comp_rightUnitor a b, Category.assoc]

/-- **The endomorphism ring of the tensor unit of a preadditive monoidal category is
commutative.** -/
scoped instance commRingUnitEnd [Preadditive C] : CommRing (End (𝟙_ C)) :=
  { (inferInstance : Ring (End (𝟙_ C))) with
    mul_comm := fun a b => comp_comm_unitEnd b a }

section Biproducts

variable [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Nested direct sums over `I` and over `K` form the direct sum over `I × K`. -/
def biproductProdIso (I K : Type) [Finite I] [Finite K] (X : C) :
    (⨁ fun _ : I => ⨁ fun _ : K => X) ≅ ⨁ fun _ : I × K => X where
  hom := biproduct.desc fun i => biproduct.desc fun k => biproduct.ι (fun _ : I × K => X) (i, k)
  inv := biproduct.desc fun p : I × K => biproduct.ι (fun _ : K => X) p.2 ≫
    biproduct.ι (fun _ : I => ⨁ fun _ : K => X) p.1
  hom_inv_id := biproduct.hom_ext' _ _ fun _ => biproduct.hom_ext' _ _ fun _ => by simp
  inv_hom_id := biproduct.hom_ext' _ _ fun _ => by simp

omit [MonoidalCategory C] [MonoidalPreadditive C] in
/-- The identification of nested direct sums sends the `k`-th summand of the `i`-th summand to the
`(i, k)`-th summand. -/
@[reassoc (attr := simp)]
lemma biproduct_ι_ι_comp_biproductProdIso_hom (I K : Type) [Finite I] [Finite K] (X : C)
    (i : I) (k : K) :
    biproduct.ι (fun _ : K => X) k ≫ biproduct.ι (fun _ : I => ⨁ fun _ : K => X) i ≫
        (biproductProdIso I K X).hom =
      biproduct.ι (fun _ : I × K => X) (i, k) := by
  simp [biproductProdIso]

/-- **The standard-basis identification `(⨁_I 𝟙) ⊗ (⨁_K 𝟙) ≅ ⨁_{I × K} 𝟙`**, from the
distributivity of the tensor product over finite direct sums. -/
def unitTensorBiproductIso (I K : Type) [Finite I] [Finite K] :
    ((⨁ fun _ : I => 𝟙_ C) ⊗ ⨁ fun _ : K => 𝟙_ C) ≅ ⨁ fun _ : I × K => 𝟙_ C :=
  rightDistributor (fun _ : I => 𝟙_ C) (⨁ fun _ : K => 𝟙_ C) ≪≫
    biproduct.mapIso (fun _ : I =>
      leftDistributor (𝟙_ C) (fun _ : K => 𝟙_ C) ≪≫
        biproduct.mapIso fun _ : K => λ_ (𝟙_ C)) ≪≫
    biproductProdIso I K (𝟙_ C)

/-- The standard-basis identification sends `e_i ⊗ e_k` to `e_{(i,k)}`. -/
@[reassoc]
theorem biproduct_ι_tensor_ι_comp_unitTensorBiproductIso_hom (I K : Type) [Finite I] [Finite K]
    (i : I) (k : K) :
    (biproduct.ι (fun _ : I => 𝟙_ C) i ⊗ₘ biproduct.ι (fun _ : K => 𝟙_ C) k) ≫
        (unitTensorBiproductIso I K).hom =
      (λ_ (𝟙_ C)).hom ≫ biproduct.ι (fun _ : I × K => 𝟙_ C) (i, k) := by
  rw [tensorHom_def', unitTensorBiproductIso]
  simp only [Iso.trans_hom, biproduct.mapIso_hom, Category.assoc]
  rw [biproduct_ι_comp_rightDistributor_hom_assoc, biproduct.ι_map_assoc]
  simp only [Category.assoc]
  rw [biproduct_ι_comp_leftDistributor_hom_assoc, biproduct.ι_map_assoc,
    biproduct_ι_ι_comp_biproductProdIso_hom]

/-- `biproduct_ι_tensor_ι_comp_unitTensorBiproductIso_hom` read on the inverse. -/
@[reassoc]
theorem biproduct_ι_comp_unitTensorBiproductIso_inv (I K : Type) [Finite I] [Finite K]
    (i : I) (k : K) :
    biproduct.ι (fun _ : I × K => 𝟙_ C) (i, k) ≫ (unitTensorBiproductIso I K).inv =
      (λ_ (𝟙_ C)).inv ≫
        (biproduct.ι (fun _ : I => 𝟙_ C) i ⊗ₘ biproduct.ι (fun _ : K => 𝟙_ C) k) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    biproduct_ι_tensor_ι_comp_unitTensorBiproductIso_hom, Iso.inv_hom_id_assoc]

/-- The standard-basis identification read on the projections. -/
@[reassoc]
theorem unitTensorBiproductIso_hom_comp_biproduct_π (I K : Type) [Finite I] [Finite K]
    (i : I) (k : K) :
    (unitTensorBiproductIso I K).hom ≫ biproduct.π (fun _ : I × K => 𝟙_ C) (i, k) =
      (biproduct.π (fun _ : I => 𝟙_ C) i ⊗ₘ biproduct.π (fun _ : K => 𝟙_ C) k) ≫
        (λ_ (𝟙_ C)).hom := by
  rw [← Iso.eq_inv_comp]
  refine biproduct.hom_ext' _ _ fun p => ?_
  obtain ⟨i₀, k₀⟩ := p
  rw [biproduct_ι_comp_unitTensorBiproductIso_inv_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]
  rcases eq_or_ne i₀ i with rfl | hi <;> rcases eq_or_ne k₀ k with rfl | hk <;> simp [*]

/-- **Endomorphisms of a finite direct sum of copies of the unit are square matrices over
`End (𝟙_ C)`.** This is `CategoryTheory.Limits.biproduct.matrixEquiv`, read at the type
`Matrix`: the ascription matters, because instance search keys on `Matrix` and on `End` and
cannot see either through the bare function type that `biproduct.matrixEquiv` is stated at. -/
def unitMatrixEquiv (I : Type) [Finite I] :
    ((⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : I => 𝟙_ C) ≃ Matrix I I (End (𝟙_ C)) :=
  biproduct.matrixEquiv

omit [MonoidalPreadditive C] in
/-- The `(i, j)` entry of the matrix of `F` is the `(i, j)` component of `F` as a morphism of
biproducts. -/
lemma unitMatrixEquiv_apply (I : Type) [Finite I]
    (F : (⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : I => 𝟙_ C) (i j : I) :
    unitMatrixEquiv I F i j = biproduct.components F i j := rfl

omit [MonoidalPreadditive C] in
/-- **The identity has the identity matrix.** -/
theorem unitMatrixEquiv_id (I : Type) [Finite I] [DecidableEq I] :
    unitMatrixEquiv I (𝟙 (⨁ fun _ : I => 𝟙_ C)) = 1 := by
  funext i j
  rw [unitMatrixEquiv_apply]
  rcases eq_or_ne i j with rfl | h
  · simp [biproduct.components, Matrix.one_apply_eq]
  · simp [biproduct.components, Matrix.one_apply_ne h, biproduct.ι_π_ne _ h]

omit [MonoidalPreadditive C] in
/-- **Composition of endomorphisms of a direct sum of copies of the unit is the matrix product,
in the same order.** The entrywise identity is
`components (F ≫ G) j l = ∑ k, components F j k ≫ components G k l`, and `End`'s multiplication
reverses composition; the two reversals cancel because `End (𝟙_ C)` is commutative. -/
theorem unitMatrixEquiv_comp (I : Type) [Fintype I]
    (F G : (⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : I => 𝟙_ C) :
    unitMatrixEquiv I (F ≫ G) = unitMatrixEquiv I F * unitMatrixEquiv I G := by
  have h : F ≫ G = biproduct.matrix (fun j l =>
      ∑ k, biproduct.components F j k ≫ biproduct.components G k l) := by
    rw [← CategoryTheory.SimplicialObject.EilenbergMacLane.biproduct_matrix_comp,
      biproduct.components_matrix, biproduct.components_matrix]
  funext j l
  rw [unitMatrixEquiv_apply, h, biproduct.matrix_components, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => comp_comm_unitEnd _ _

/-- **The Kronecker law.** Under the standard-basis identification
`(⨁_I 𝟙) ⊗ (⨁_K 𝟙) ≅ ⨁_{I × K} 𝟙`, the matrix of `F ⊗ₘ G` at `((i,k), (i',k'))` is the product
of the matrix of `F` at `(i,i')` and the matrix of `G` at `(k,k')`. -/
theorem unitMatrixEquiv_tensorHom (I K : Type) [Finite I] [Finite K]
    (F : (⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : I => 𝟙_ C)
    (G : (⨁ fun _ : K => 𝟙_ C) ⟶ ⨁ fun _ : K => 𝟙_ C) (i i' : I) (k k' : K) :
    unitMatrixEquiv (I × K) ((unitTensorBiproductIso I K).inv ≫ (F ⊗ₘ G) ≫
        (unitTensorBiproductIso I K).hom) (i, k) (i', k') =
      unitMatrixEquiv I F i i' * unitMatrixEquiv K G k k' := by
  rw [unitMatrixEquiv_apply]
  simp only [biproduct.components, Category.assoc]
  rw [biproduct_ι_comp_unitTensorBiproductIso_inv_assoc,
    unitTensorBiproductIso_hom_comp_biproduct_π]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [iso_unit_conj_tensorHom]
  exact comp_comm_unitEnd _ _

end Biproducts

end CategoryTheory.MonoidalCategory

namespace Stacks.EtaleCohomology.BrauerScheme

variable (S : Scheme.{u})

local instance hasFiniteBiproductsModuleSheaf : HasFiniteBiproducts (ModuleSheaf S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance monoidalPreadditiveModuleSheaf : MonoidalPreadditive (ModuleSheaf S) :=
  Strict.monoidalPreadditiveRingSheaf S.sheaf

/-- **The coefficient ring of the matrix dictionary**: the endomorphisms of `𝒪_S` as a sheaf of
`𝒪_S`-modules, i.e. of the monoidal unit. It is a commutative ring by
`CategoryTheory.MonoidalCategory.commRingUnitEnd`. -/
abbrev R₀ := End (𝟙_ (ModuleSheaf S))

/-- **A free sheaf of `𝒪_S`-modules on a finite index type is the direct sum of copies of
`𝒪_S`.** `SheafOfModules.free I` is by definition the coproduct of `I` copies of the unit, and a
finite coproduct is a biproduct. -/
def freeBiproductIso (I : Type) [Finite I] :
    _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ≅
      ⨁ (fun _ : I => 𝟙_ (ModuleSheaf S)) :=
  Sigma.whiskerEquiv
      (f := fun _ : ULift.{u, 0} I => _root_.SheafOfModules.unit (Tensor.ringSheaf S.sheaf))
      (g := fun _ : I => 𝟙_ (ModuleSheaf S)) (Equiv.ulift (α := I))
      (fun _ => Iso.refl _) ≪≫
    (biproduct.isoCoproduct (fun _ : I => 𝟙_ (ModuleSheaf S))).symm

/-- **Endomorphisms of a free sheaf of `𝒪_S`-modules of finite rank are square matrices over
`R₀ S`.** -/
def freeEndMatrixEquiv (I : Type) [Finite I] :
    (_root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) ≃
      Matrix I I (R₀ S) :=
  (Iso.homCongr (freeBiproductIso S I) (freeBiproductIso S I)).trans (unitMatrixEquiv I)

/-- The matrix of an endomorphism `f` of a free sheaf is the matrix of `f` transported along the
isomorphism `freeBiproductIso` with the direct sum of copies of the unit. -/
lemma freeEndMatrixEquiv_apply (I : Type) [Finite I]
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) :
    freeEndMatrixEquiv S I f =
      unitMatrixEquiv I ((freeBiproductIso S I).inv ≫ f ≫ (freeBiproductIso S I).hom) :=
  rfl

/-- **The matrix of the identity is the identity matrix.** -/
@[simp]
theorem freeEndMatrixEquiv_id (I : Type) [Finite I] [DecidableEq I] :
    freeEndMatrixEquiv S I (𝟙 _) = 1 := by
  rw [freeEndMatrixEquiv_apply, Category.id_comp, Iso.inv_hom_id, unitMatrixEquiv_id]

/-- **Composition goes to the matrix product, in the same order.** The order does not reverse:
`biproduct.components (F ≫ G) j l` is `∑ k, components F j k ≫ components G k l`, which is the
`(j, l)` entry of the product of the two matrices because `R₀ S` is commutative
(`CategoryTheory.MonoidalCategory.comp_comm_unitEnd`). -/
theorem freeEndMatrixEquiv_comp (I : Type) [Fintype I]
    (f g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) :
    freeEndMatrixEquiv S I (f ≫ g) = freeEndMatrixEquiv S I f * freeEndMatrixEquiv S I g := by
  have hFG : (freeBiproductIso S I).inv ≫ (f ≫ g) ≫ (freeBiproductIso S I).hom =
      ((freeBiproductIso S I).inv ≫ f ≫ (freeBiproductIso S I).hom) ≫
        ((freeBiproductIso S I).inv ≫ g ≫ (freeBiproductIso S I).hom) :=
    Iso.homCongr_comp (freeBiproductIso S I) (freeBiproductIso S I) (freeBiproductIso S I) f g
  rw [freeEndMatrixEquiv_apply, freeEndMatrixEquiv_apply, freeEndMatrixEquiv_apply, hFG,
    unitMatrixEquiv_comp]

/-- **The dictionary is additive.** Stated for morphisms rather than for `End`: the two
additions are definitionally the same, but `CategoryTheory.Preadditive.add_comp` is keyed on the
hom type and does not rewrite a sum written at `End`. -/
theorem freeEndMatrixEquiv_add (I : Type) [Finite I]
    (f g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) :
    freeEndMatrixEquiv S I (f + g) = freeEndMatrixEquiv S I f + freeEndMatrixEquiv S I g := by
  funext i j
  simp only [freeEndMatrixEquiv_apply, unitMatrixEquiv_apply, Matrix.add_apply,
    biproduct.components, Category.assoc, Preadditive.comp_add, Preadditive.add_comp]

/-- **The matrix dictionary as a ring isomorphism.** `CategoryTheory.End` multiplies in the
order of `Function.comp`, so the entrywise dictionary is anti-multiplicative for that
convention; transposing — an anti-automorphism of a matrix ring over a commutative ring — undoes
the reversal. -/
def freeEndRingEquiv (I : Type) [Fintype I] [DecidableEq I] :
    End (_root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) ≃+*
      Matrix I I (R₀ S) where
  toFun f := (freeEndMatrixEquiv S I f).transpose
  invFun M := (freeEndMatrixEquiv S I).symm M.transpose
  left_inv f := by simp
  right_inv M := by simp
  map_add' f g :=
    (congrArg Matrix.transpose (freeEndMatrixEquiv_add S I f g)).trans
      (Matrix.transpose_add _ _)
  map_mul' f g := by
    change (freeEndMatrixEquiv S I (g ≫ f)).transpose = _
    rw [freeEndMatrixEquiv_comp, Matrix.transpose_mul]

/-- **The standard-basis identification `free (ULift I) ⊗ free (ULift K) ≅ free (ULift (I×K))`**
of free sheaves of `𝒪_S`-modules of finite rank. -/
def freeTensorFreeBiproductIso (I K : Type) [Finite I] [Finite K] :
    (_root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⊗
        _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K)) ≅
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (I × K)) :=
  (freeBiproductIso S I ⊗ᵢ freeBiproductIso S K) ≪≫ unitTensorBiproductIso I K ≪≫
    (freeBiproductIso S (I × K)).symm

/-- **The Kronecker law for free sheaves of modules.** Under the standard-basis identification
`free (ULift I) ⊗ free (ULift K) ≅ free (ULift (I × K))`, the matrix of `f ⊗ₘ g` at
`((i,k), (i',k'))` is the product of the matrix of `f` at `(i,i')` and the matrix of `g` at
`(k,k')`: the matrix of a tensor product of endomorphisms of free sheaves of modules is the
Kronecker product of their matrices. -/
theorem freeEndMatrixEquiv_tensorHom (I K : Type) [Finite I] [Finite K]
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I))
    (g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K))
    (i i' : I) (k k' : K) :
    freeEndMatrixEquiv S (I × K)
        ((freeTensorFreeBiproductIso S I K).inv ≫ (f ⊗ₘ g) ≫
          (freeTensorFreeBiproductIso S I K).hom) (i, k) (i', k') =
      freeEndMatrixEquiv S I f i i' * freeEndMatrixEquiv S K g k k' := by
  have key : (freeBiproductIso S (I × K)).inv ≫
        ((freeTensorFreeBiproductIso S I K).inv ≫ (f ⊗ₘ g) ≫
          (freeTensorFreeBiproductIso S I K).hom) ≫ (freeBiproductIso S (I × K)).hom =
      (unitTensorBiproductIso I K).inv ≫
        (((freeBiproductIso S I).inv ≫ f ≫ (freeBiproductIso S I).hom) ⊗ₘ
          ((freeBiproductIso S K).inv ≫ g ≫ (freeBiproductIso S K).hom)) ≫
        (unitTensorBiproductIso I K).hom := by
    simp only [freeTensorFreeBiproductIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, tensorIso_hom, tensorIso_inv, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id, tensorHom_comp_tensorHom_assoc]
  rw [freeEndMatrixEquiv_apply, key, unitMatrixEquiv_tensorHom, freeEndMatrixEquiv_apply,
    freeEndMatrixEquiv_apply]

end Stacks.EtaleCohomology.BrauerScheme

end

end

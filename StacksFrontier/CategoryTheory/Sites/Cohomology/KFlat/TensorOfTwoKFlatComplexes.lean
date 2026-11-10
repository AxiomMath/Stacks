module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of two K-flat complexes

Let `(C, O)` be a ringed site and `Mod(O)` the abelian category of sheaves of `O`-modules. A
complex `K^•` of `O`-modules is *K-flat* (Stacks 06YN) if for every acyclic complex `F^•` the
total complex `Tot(F^• ⊗_O K^•)` is acyclic. Stacks 07A2 (Lemma 21.17.5): if `K^•` and `L^•` are
K-flat, then so is `Tot(K^• ⊗_O L^•)`.

The statement is formulated for cochain complexes indexed by `ℤ` in an abelian monoidal category
`A` whose tensor product is additive and preserves the colimits needed to form total complexes of
iterated tensor products; `Mod(O) = SheafOfModules O` is such a category. The total complex
`Tot(K^• ⊗ L^•)` is the monoidal product `K ⊗ L` of `HomologicalComplex.monoidalCategory`, whose
degree `n` term is the coproduct of the `K^p ⊗ L^q` over `p + q = n`, with the Koszul-sign
differential; acyclicity is `HomologicalComplex.Acyclic`.

All names are in the namespace `CochainComplex.KFlatMonoidal`.

## Main definitions

* `Acyclic`: a complex all of whose cohomology objects vanish.
* `totalComplexTensor`: the total complex `Tot(K^• ⊗ L^•)` of two complexes.
* `totalComplexTensor.ι`: the structure map `K^p ⊗ L^q ⟶ Tot(K^• ⊗ L^•)^n` for `p + q = n`.
* `KFlat`: K-flatness of a complex.

## Main results

* `acyclic_iff_exactAt`: a complex is acyclic iff it is exact in every degree.
* `tensor_eq_totalComplex`: `totalComplexTensor K L` is `HomologicalComplex.tensorObj K L`.
* `KFlat.tensorObj`: the total complex of the tensor product of two K-flat complexes is K-flat.

## References

* [Stacks Project, Tag 07A2](https://stacks.math.columbia.edu/tag/07A2)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace CochainComplex.KFlatMonoidal

/-- A cochain complex is *acyclic* when all of its cohomology objects vanish. -/
abbrev Acyclic (K : CochainComplex A ℤ) : Prop := K.Acyclic

/-- A complex is acyclic if and only if it is exact in every degree. -/
theorem acyclic_iff_exactAt (K : CochainComplex A ℤ) :
    Acyclic K ↔ ∀ n, K.ExactAt n :=
  K.acyclic_iff

variable [MonoidalCategory A] [(curriedTensor A).Additive]
  [∀ (X₁ : A), ((curriedTensor A).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), X₁.HasTensor X₂]
  [∀ (X₁ : A), PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ (X₂ : A), PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), X₁.HasGoodTensor₁₂Tensor X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), X₁.HasGoodTensorTensor₂₃ X₂ X₃]

/-- The total complex `Tot(K^• ⊗ L^•)`: the monoidal product of `K` and `L` in
`CochainComplex A ℤ`, whose degree `n` term is the coproduct `⨁_{p+q=n} K^p ⊗ L^q`, with the
Koszul-sign differential. -/
@[sga "4 XVII 1.1.10"]
noncomputable abbrev totalComplexTensor (K L : CochainComplex A ℤ) : CochainComplex A ℤ := K ⊗ L

/-- The total complex of the tensor product of `K` and `L` is
`HomologicalComplex.tensorObj K L`. -/
theorem tensor_eq_totalComplex (K L : CochainComplex A ℤ) :
    totalComplexTensor K L = HomologicalComplex.tensorObj K L := rfl

/-- For `p + q = n`, the inclusion `K^p ⊗ L^q ⟶ Tot(K^• ⊗ L^•)^n` of a summand of the
coproduct `⨁_{p+q=n} K^p ⊗ L^q`. -/
noncomputable abbrev totalComplexTensor.ι (K L : CochainComplex A ℤ) (p q n : ℤ) (h : p + q = n) :
    K.X p ⊗ L.X q ⟶ (totalComplexTensor K L).X n :=
  HomologicalComplex.ιTensorObj K L p q n h

/-- A cochain complex `K^•` is *K-flat* (Stacks 06YN) if for every acyclic complex `F^•` the
total complex `Tot(F^• ⊗ K^•)` is acyclic. -/
def KFlat (K : CochainComplex A ℤ) : Prop :=
  ∀ F : CochainComplex A ℤ, Acyclic F → Acyclic (totalComplexTensor F K)

/-- If `K^•` and `L^•` are K-flat complexes, then their total tensor product `Tot(K^• ⊗ L^•)`
is K-flat. -/
@[stacks 07A2]
theorem KFlat.tensorObj {K L : CochainComplex A ℤ} (hK : KFlat K) (hL : KFlat L) :
    KFlat (totalComplexTensor K L) := fun F hF n =>
  (hL _ (hK F hF) n).of_iso (α_ F K L)

end CochainComplex.KFlatMonoidal

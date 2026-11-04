module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# The Laurent algebra of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `O`-modules.
The integer tensor powers `L^{⊗ n}`, `n : ℤ`, carry the coherent multiplication
`L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU. This file assembles them into the
`ℤ`-graded **Laurent algebra** `⨁_{n ∈ ℤ} L^{⊗ n}`, a sheaf of graded algebras over `O` in the
sense of Tag 0FQW.

Unlike the symmetric algebra `Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}`, this algebra is supported in all
degrees, positive and negative. Its relative spectrum is the punctured total space of the line
bundle attached to `L`: inverting the degree-one generator is what deletes the zero section.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.mulBilinear`: the multiplication
  `L^{⊗ n} × L^{⊗ m} → L^{⊗ (n + m)}` on local sections, read off from the coherent
  multiplication isomorphism of Tag 01CU.
* `Stacks.SheafOfModules.TensorPower.oneSection`: the unit, the global section `1` of
  `L^{⊗ 0} = O`.
* `Stacks.SheafOfModules.TensorPower.laurentAlgebra`: **the Laurent algebra
  `⨁_{n ∈ ℤ} L^{⊗ n}` of an invertible sheaf of modules, as a sheaf of graded algebras.**

## Main results

* `Stacks.SheafOfModules.TensorPower.mulBilinear_assoc`,
  `Stacks.SheafOfModules.TensorPower.mulBilinear_one_mul` and
  `Stacks.SheafOfModules.TensorPower.mulBilinear_mul_one`: the three algebra laws, as the
  heterogeneous equalities of local sections that `SheafOfModules.GradedAlgebra` demands.
* `Stacks.SheafOfModules.TensorPower.mulBilinear_comm`: **homogeneous multiplication in the
  Laurent algebra commutes**, in every pair of degrees.
* `Stacks.SheafOfModules.TensorPower.heq_reindex`: reindexing a tensor power along an equality
  of exponents does not change a local section, up to heterogeneous equality.

## Implementation notes

The multiplication is obtained from the coherent multiplication isomorphism
`Stacks.SheafOfModules.TensorPower.coherentMulIso` by `PresheafOfModules.toBilinear`, which
reads a morphism out of the objectwise tensor product as a bilinear map on local sections. The
resulting bilinear map therefore evaluates on arbitrary local sections as the isomorphism
applied to `Stacks.SheafOfModules.tensorSectionsAt`, by `rfl`, and no hypothesis that such
sections generate the tensor product sheaf is needed.

Each of the four laws is proved by the same three steps: apply `congrArg Iso.hom` to the
corresponding coherence law of `coherentMulIso`, evaluate both sides on the section determined
by the pure tensor of the given local sections through the section formulas
`Stacks.SheafOfModules.tensorSections_associatorAt`,
`tensorSections_leftUnitorAt`, `tensorSections_rightUnitorAt`, `tensorSections_braidingAt` and
`tensorSections_tensorProductIsoAt`, and absorb the residual reindexing with `heq_reindex`.
Stating the evaluated coherence law by `change` rather than by rewriting the composite is what
keeps the two spellings of the tensor product sheaf from being compared by the unifier.

The unit is the identity of `L^{⊗ 0}` read through `SheafOfModules.unitHomEquiv`: the zeroth
tensor power is the structure sheaf by `rfl`, so that identity is a morphism out of the monoidal
unit and the section it names is `1` in every degree, again by `rfl`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L]

/-- Reindexing a tensor power along an equality of exponents leaves a local section unchanged,
up to heterogeneous equality. -/
theorem heq_reindex (U : Cᵒᵖ) {a b : ℤ} (h : a = b)
    (x : (tensorPower O hO L a).val.obj U) :
    HEq (((tensorPowerReindex O hO L h).hom.val.app U) x) x := by
  cases h
  exact HEq.refl _

/-- **Multiplication of the Laurent algebra in degrees `n` and `m`**: the coherent
multiplication isomorphism `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU, read as a
bilinear map on local sections. -/
def mulBilinear (n m : ℤ) :
    SheafOfModules.BilinearMap (tensorPower O hO L n) (tensorPower O hO L m)
      (tensorPower O hO L (n + m)) :=
  PresheafOfModules.toBilinear
    (TensorSheafification.toSheafify O hO
        ((tensorPower O hO L n).val ⊗ (tensorPower O hO L m).val) ≫
      (coherentMulIso O hO L n m).hom.val)

/-- Multiplication of the Laurent algebra on a pair of local sections is the coherent
multiplication isomorphism applied to the section they determine. -/
theorem mulBilinear_app (n m : ℤ) (U : Cᵒᵖ) (s : (tensorPower O hO L n).val.obj U)
    (t : (tensorPower O hO L m).val.obj U) :
    (mulBilinear O hO L n m).app U s t =
      ((coherentMulIso O hO L n m).hom.val.app U)
        (tensorSectionsAt O hO U (tensorPower O hO L n) (tensorPower O hO L m) s t) :=
  rfl

/-- **The unit of the Laurent algebra**: the global section `1` of the zeroth tensor power,
which is the structure sheaf. -/
def oneSection : (tensorPower O hO L 0).sections :=
  (tensorPower O hO L 0).unitHomEquiv (𝟙 _)

/-- The unit of the Laurent algebra evaluates on each object `U` to `1 : O.obj U`. -/
@[simp]
theorem oneSection_eval (U : Cᵒᵖ) : (oneSection O hO L).eval U = (1 : O.obj U) := rfl

/-- A local section equal to the reindexing of another one is heterogeneously equal to it. -/
private theorem heq_of_eq_reindex {U : Cᵒᵖ} {a b : ℤ} {h : a = b}
    {x : (tensorPower O hO L b).val.obj U} {y : (tensorPower O hO L a).val.obj U}
    (e : x = ((tensorPowerReindex O hO L h).hom.val.app U) y) : HEq x y :=
  (heq_of_eq e).trans (heq_reindex O hO L U h y)

/-- **Multiplication of the Laurent algebra is associative**, as a heterogeneous equality of
local sections: the two sides sit in the degrees `(n + m) + k` and `n + (m + k)`. -/
theorem mulBilinear_assoc (n m k : ℤ) (U : Cᵒᵖ)
    (x : (tensorPower O hO L n).val.obj U) (y : (tensorPower O hO L m).val.obj U)
    (z : (tensorPower O hO L k).val.obj U) :
    HEq ((mulBilinear O hO L (n + m) k).app U ((mulBilinear O hO L n m).app U x y) z)
      ((mulBilinear O hO L n (m + k)).app U x ((mulBilinear O hO L m k).app U y z)) := by
  let α := Invertible.tensorProductAssociator O hO
    (tensorPower O hO L n) (tensorPower O hO L m) (tensorPower O hO L k)
  let μ₁ := coherentMulIso O hO L n m
  let μ₂ := coherentMulIso O hO L (n + m) k
  let μ₃ := coherentMulIso O hO L m k
  let μ₄ := coherentMulIso O hO L n (m + k)
  let ρ := tensorPowerReindex O hO L (Int.add_assoc n m k).symm
  let S := tensorSectionsAt O hO U
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          ((tensorPower O hO L n))).obj ((tensorPower O hO L m))))
    (tensorPower O hO L k)
    (tensorSectionsAt O hO U (tensorPower O hO L n) (tensorPower O hO L m) x y) z
  have happ := congrArg (fun f => (f.val.app U) S)
    (congrArg Iso.hom (coherentMulIso_assoc O hO L n m k))
  change (μ₂.hom.val.app U)
      ((Invertible.tensorProductIso O hO μ₁ (Iso.refl _)).hom.val.app U S) =
    (ρ.hom.val.app U)
      ((μ₄.hom.val.app U)
        ((Invertible.tensorProductIso O hO (Iso.refl _) μ₃).hom.val.app U
          (α.hom.val.app U S))) at happ
  have leftProduct := tensorSections_tensorProductIsoAt O hO U _ _ _ _ μ₁
    (Iso.refl (tensorPower O hO L k))
    (tensorSectionsAt O hO U (tensorPower O hO L n) (tensorPower O hO L m) x y) z
  have associatorSections := tensorSections_associatorAt O hO U
    (tensorPower O hO L n) (tensorPower O hO L m) (tensorPower O hO L k) x y z
  have rightProduct := (congrArg
    ((Invertible.tensorProductIso O hO (Iso.refl (tensorPower O hO L n)) μ₃).hom.val.app U)
    associatorSections).trans
      (tensorSections_tensorProductIsoAt O hO U _ _ _ _
        (Iso.refl (tensorPower O hO L n)) μ₃ x
        (tensorSectionsAt O hO U (tensorPower O hO L m) (tensorPower O hO L k) y z))
  have multiplicationEquality :=
    (congrArg (μ₂.hom.val.app U) leftProduct).symm.trans
      (happ.trans (congrArg (fun value ↦ (ρ.hom.val.app U) ((μ₄.hom.val.app U) value))
        rightProduct))
  exact heq_of_eq_reindex O hO L multiplicationEquality

/-- **The unit of the Laurent algebra is a left identity**, as a heterogeneous equality of local
sections: the left-hand side sits in degree `0 + n`. -/
theorem mulBilinear_one_mul (n : ℤ) (U : Cᵒᵖ) (x : (tensorPower O hO L n).val.obj U) :
    HEq ((mulBilinear O hO L 0 n).app U ((oneSection O hO L).eval U) x) x := by
  have happ := congrArg (fun f => (f.val.app U)
      (tensorSectionsAt O hO U (SheafOfModules.unit (TensorSheafification.structureSheaf O hO))
        (tensorPower O hO L n) (1 : O.obj U) x))
    (congrArg Iso.hom (coherentMulIso_zero_left O hO L n))
  change ((tensorPowerReindex O hO L (Int.zero_add n)).hom.val.app U)
      ((mulBilinear O hO L 0 n).app U ((oneSection O hO L).eval U) x) =
    ((Invertible.tensorProductLeftUnitor O hO (tensorPower O hO L n)).hom.val.app U)
      (tensorSectionsAt O hO U (SheafOfModules.unit (TensorSheafification.structureSheaf O hO))
        (tensorPower O hO L n) (1 : O.obj U) x) at happ
  rw [tensorSections_leftUnitorAt] at happ
  exact (heq_of_eq_reindex O hO L happ.symm).symm

/-- **The unit of the Laurent algebra is a right identity**, as a heterogeneous equality of
local sections: the left-hand side sits in degree `n + 0`. -/
theorem mulBilinear_mul_one (n : ℤ) (U : Cᵒᵖ) (x : (tensorPower O hO L n).val.obj U) :
    HEq ((mulBilinear O hO L n 0).app U x ((oneSection O hO L).eval U)) x := by
  have happ := congrArg (fun f => (f.val.app U)
      (tensorSectionsAt O hO U (tensorPower O hO L n)
        (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) x (1 : O.obj U)))
    (congrArg Iso.hom (coherentMulIso_zero_right O hO L n))
  change ((tensorPowerReindex O hO L (Int.add_zero n)).hom.val.app U)
      ((mulBilinear O hO L n 0).app U x ((oneSection O hO L).eval U)) =
    ((Invertible.tensorProductRightUnitor O hO (tensorPower O hO L n)).hom.val.app U)
      (tensorSectionsAt O hO U (tensorPower O hO L n)
        (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) x (1 : O.obj U)) at happ
  rw [tensorSections_rightUnitorAt] at happ
  exact (heq_of_eq_reindex O hO L happ.symm).symm

/-- **Homogeneous multiplication in the Laurent algebra commutes**, in every pair of degrees:
the commutativity law of Tag 01CU says the coherent multiplication is unchanged by the braiding
of the tensor product sheaf, and the braiding exchanges the two local sections. -/
theorem mulBilinear_comm (n m : ℤ) (U : Cᵒᵖ)
    (x : (tensorPower O hO L n).val.obj U) (y : (tensorPower O hO L m).val.obj U) :
    HEq ((mulBilinear O hO L n m).app U x y) ((mulBilinear O hO L m n).app U y x) := by
  have happ := congrArg (fun f => (f.val.app U)
      (tensorSectionsAt O hO U (tensorPower O hO L n) (tensorPower O hO L m) x y))
    (congrArg Iso.hom (coherentMulIso_comm O hO L n m))
  change (mulBilinear O hO L n m).app U x y =
    ((tensorPowerReindex O hO L (Int.add_comm m n)).hom.val.app U)
      ((coherentMulIso O hO L m n).hom.val.app U
        ((Invertible.tensorProductBraiding O hO (tensorPower O hO L n)
            (tensorPower O hO L m)).hom.val.app U
          (tensorSectionsAt O hO U (tensorPower O hO L n)
            (tensorPower O hO L m) x y))) at happ
  rw [tensorSections_braidingAt] at happ
  exact heq_of_eq_reindex O hO L happ

/-- **The Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of an invertible sheaf of modules**, as a sheaf of
graded algebras over the structure sheaf: the homogeneous piece in degree `n` is the `n`th
integer tensor power of `L`, and multiplication is the coherent multiplication of Tag 01CU. -/
def laurentAlgebra :
    SheafOfModules.GradedAlgebra.{w, w} (TensorSheafification.structureSheaf O hO) where
  piece n := tensorPower O hO L n
  mul := mulBilinear O hO L
  one := oneSection O hO L
  mul_assoc := mulBilinear_assoc O hO L
  one_mul := mulBilinear_one_mul O hO L
  mul_one := mulBilinear_mul_one O hO L

/-- The homogeneous piece of the Laurent algebra in degree `n` is the tensor power
`tensorPower O hO L n`. -/
@[simp]
theorem laurentAlgebra_piece (n : ℤ) :
    (laurentAlgebra O hO L).piece n = tensorPower O hO L n :=
  rfl

/-- The multiplication of the Laurent algebra in degrees `n` and `m` is
`mulBilinear O hO L n m`. -/
@[simp]
theorem laurentAlgebra_mul (n m : ℤ) :
    (laurentAlgebra O hO L).mul n m = mulBilinear O hO L n m :=
  rfl

/-- The unit of the Laurent algebra is `oneSection O hO L`. -/
@[simp]
theorem laurentAlgebra_one : (laurentAlgebra O hO L).one = oneSection O hO L := rfl

/-- **Homogeneous multiplication in the Laurent algebra commutes**, stated for the sheaf of
graded algebras itself. -/
theorem laurentAlgebra_mul_comm (n m : ℤ) (U : Cᵒᵖ)
    (x : ((laurentAlgebra O hO L).piece n).val.obj U)
    (y : ((laurentAlgebra O hO L).piece m).val.obj U) :
    HEq (((laurentAlgebra O hO L).mul n m).app U x y)
      (((laurentAlgebra O hO L).mul m n).app U y x) :=
  mulBilinear_comm O hO L n m U x y

end Stacks.SheafOfModules.TensorPower

end

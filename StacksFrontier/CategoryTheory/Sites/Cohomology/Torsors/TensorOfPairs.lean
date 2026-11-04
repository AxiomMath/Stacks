module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.NormalizedGenerators
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfATensorProduct

/-!
# The tensor product of two pairs on a ringed site

Let `(C, O)` be a ringed site, let `L` and `M` be invertible `O`-modules and let
`α : L^{⊗ n} ≅ O` and `β : M^{⊗ n} ≅ O` be trivializations of their `n`-th tensor powers. The
tensor product of the two pairs `(L, α)` and `(M, β)` is `L ⊗ M` with the trivialization
obtained from the comparison `(L ⊗ M)^{⊗ n} ≅ L^{⊗ n} ⊗ M^{⊗ n}`, from `α ⊗ β` and from the
right unit constraint `O ⊗ O ≅ O`. On a tensor product of sections its trivialization value is
the product of the two trivialization values, so the tensor product of two trivializations of
the two pairs is a trivialization of the tensor product pair, and tensoring sections is a
morphism of sheaves of sets from the product of the two sheaves of trivializations to the sheaf
of trivializations of the tensor product.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.tensorTriv` is the trivialization of the `n`-th tensor
  power of `L ⊗ M`.
* `Stacks.Cohomology.Torsors.Generators.normalizedTensor` is the tensor product of two
  trivializations, and
  `Stacks.Cohomology.Torsors.Generators.normalizedTensorPairing` is the resulting morphism of
  sheaves of sets.

## Main results

* `Stacks.Cohomology.Torsors.Generators.rightUnitor_unitSection_tensorSection`: the right unit
  constraint multiplies two sections of the structure sheaf read as a module over itself.
* `Stacks.Cohomology.Torsors.Generators.trivValue_tensorTriv`: **the trivialization value of the
  tensor product pair on a tensor product of sections is the product of the two trivialization
  values.**
* `Stacks.Cohomology.Torsors.Generators.normalizedTensor_val`: the underlying section of the
  tensor product of two trivializations is the tensor product of their underlying sections.
* `Stacks.Cohomology.Torsors.Generators.tensorSection_smul_unit`: scaling the two factors by two
  units scales the tensor product by their product, which is the equivariance making the
  pairing add the acting roots of unity.

## Implementation notes

`tensorTriv` composes its three constituents to the *left*, `(A ≪≫ B) ≪≫ C`, exactly as
`Stacks.Cohomology.Torsors.Generators.powerMap` does, so that the value of the composite on a
section is the nested application by `rfl`. Associated to the right, the inner
`CategoryTheory.Iso.trans` has a middle object whose sheaf condition is a projection of the
ringed site, which is not type-correct at `implicit` transparency and so blocks `rw` and `simp`.

The multiplication of two sections of the structure sheaf is read off the right unit constraint
rather than postulated: a tensor product of two sections of `O` is the product of the two
sections times the tensor product of the two unit sections, by bilinearity, and the right unit
constraint carries the latter to the unit section.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules (IsInvertible)

universe u v w

namespace Stacks.Cohomology.Torsors.Generators

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]

-- The tensor product sheaf of Tag 01CA and its symmetry constraint, as a monoidal and a
-- symmetric structure on the modules of a ringed site.  Both instances are `local` where they
-- are declared, so the attribute is re-enabled here rather than the declarations repeated.
attribute [local instance] ringedSiteModulesMonoidal ringedSiteModulesSymmetric

/-- **The right unit constraint multiplies two sections of the structure sheaf** read as a
module over itself. -/
theorem rightUnitor_unitSection_tensorSection (U : X.C)
    (a b : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    unitVal X U
        (((ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.val.app
          (op U)).hom
          (tensorSection X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U a b)) =
      unitVal X U a * unitVal X U b := by
  have ha : (unitVal X U a) • (ofUnitVal X U 1) = a := mul_one (unitVal X U a)
  have hb : (unitVal X U b) • (ofUnitVal X U 1) = b := mul_one (unitVal X U b)
  have h1 : tensorSection X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U a b =
      (unitVal X U a * unitVal X U b) •
        tensorSection X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U (ofUnitVal X U 1)
          (ofUnitVal X U 1) := by
    refine Eq.trans ?_ (tensorSection_smul' X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U (unitVal X U a)
      (unitVal X U b) (ofUnitVal X U 1) (ofUnitVal X U 1))
    exact congrArg₂ (tensorSection X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) ha.symm hb.symm
  refine Eq.trans (congrArg (fun z => unitVal X U
    (((ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.val.app
      (op U)).hom z))
    h1) ?_
  refine Eq.trans (congrArg (unitVal X U)
    (((ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.val.app
      (op U)).hom.map_smul _ _)) ?_
  refine Eq.trans (unitVal_smul X U _ _) ?_
  refine Eq.trans (congrArg (fun z => (unitVal X U a * unitVal X U b) * unitVal X U z)
    (rightUnitor_tensorSection X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      U (ofUnitVal X U 1))) ?_
  exact mul_one _

/-- **The trivialization of the `n`-th tensor power of a tensor product of two pairs.** -/
def tensorTriv (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    tpow X (tensorSheafOfModules X L M) n ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (tpowTensorIso X L M n ≪≫ tensorIsoOfModules X al bl) ≪≫
    ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The trivialization value of the tensor product pair on a tensor product of sections is the
product of the two trivialization values.** -/
theorem trivValue_tensorTriv (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : L.val.obj (op U)) (t : M.val.obj (op U)) :
    trivValue X (tensorSheafOfModules X L M) n (tensorTriv X L M n al bl) U
        (tensorSection X L M U s t) =
      trivValue X L n al U s * trivValue X M n bl U t := by
  have h0 : ((tensorTriv X L M n al bl).hom.val.app (op U)).hom
        (powerSection X (tensorSheafOfModules X L M) U (tensorSection X L M U s t) n) =
      ((ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.val.app
        (op U)).hom
        (((al.hom ⊗ₘ bl.hom).val.app (op U)).hom
          (((tpowTensorIso X L M n).hom.val.app (op U)).hom
            (powerSection X (tensorSheafOfModules X L M) U
              (tensorSection X L M U s t) n))) := rfl
  refine Eq.trans (congrArg (unitVal X U) h0) ?_
  refine Eq.trans (congrArg (fun z => unitVal X U
      (((ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.val.app
        (op U)).hom
        (((al.hom ⊗ₘ bl.hom).val.app (op U)).hom z)))
    (tpowTensorIso_powerSection X L M U s t n)) ?_
  refine Eq.trans (congrArg (fun z => unitVal X U
      (((ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.val.app
        (op U)).hom z))
    (tensorHom_tensorSection X al.hom bl.hom U
      (powerSection X L U s n) (powerSection X M U t n))) ?_
  exact rightUnitor_unitSection_tensorSection X U _ _

/-- The tensor product of two trivializations of the two pairs is a trivialization of the
tensor product pair. -/
theorem tensorSection_mem_normalizedSubfunctor
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (s : (normalizedSubfunctor X L n al).obj U)
    (t : (normalizedSubfunctor X M n bl).obj U) :
    tensorSection X L M U.unop s.val t.val ∈
      (normalizedSubfunctor X (tensorSheafOfModules X L M) n
        (tensorTriv X L M n al bl)).obj U := by
  refine ⟨(tensorGeneratorSections' X L M U.unop ⟨s.val, s.property.1⟩
    ⟨t.val, t.property.1⟩).property, ?_⟩
  refine Eq.trans (trivValue_tensorTriv X L M n al bl U.unop s.val t.val) ?_
  rw [s.property.2, t.property.2, one_mul]

/-- **The tensor product of two trivializations of the two pairs**, as a trivialization of the
tensor product pair. -/
def normalizedTensor (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (s : (normalizedSubfunctor X L n al).obj U)
    (t : (normalizedSubfunctor X M n bl).obj U) :
    (normalizedSubfunctor X (tensorSheafOfModules X L M) n
      (tensorTriv X L M n al bl)).obj U :=
  ⟨tensorSection X L M U.unop s.val t.val,
    tensorSection_mem_normalizedSubfunctor X L M n al bl U s t⟩

/-- The underlying section of the tensor product of two trivializations. -/
theorem normalizedTensor_val (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (s : (normalizedSubfunctor X L n al).obj U)
    (t : (normalizedSubfunctor X M n bl).obj U) :
    (normalizedTensor X L M n al bl U s t).val =
      tensorSection X L M U.unop s.val t.val := rfl

/-- **Tensoring trivializations is a morphism of sheaves of sets** from the product of the two
sheaves of trivializations to the sheaf of trivializations of the tensor product pair. -/
def normalizedTensorPairing (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    productPresheaf' (normalizedSheaf X L n al).obj (normalizedSheaf X M n bl).obj ⟶
      (normalizedSheaf X (tensorSheafOfModules X L M) n (tensorTriv X L M n al bl)).obj where
  app U := ↾(fun x => normalizedTensor X L M n al bl U x.1 x.2)
  naturality _ _ f := ConcreteCategory.hom_ext _ _ fun x =>
    Subtype.ext (tensorSection_restrict X L M f.unop x.1.val x.2.val).symm

/-- Scaling the two factors of a tensor product of sections by two units scales the tensor
product by their product. This is the equivariance that makes
`Stacks.Cohomology.Torsors.Generators.normalizedTensorPairing` add the acting roots of
unity. -/
theorem tensorSection_smul_unit
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (a b : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ)
    (s : L.val.obj (op U)) (t : M.val.obj (op U)) :
    tensorSection X L M U (a.val • s) (b.val • t) =
      (a * b).val • tensorSection X L M U s t :=
  tensorSection_smul' X L M U a.val b.val s t

end Stacks.Cohomology.Torsors.Generators

end

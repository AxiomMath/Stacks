module

public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridgeSuccIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherenceUnique

/-!
# The power-system multiplication of tensor powers is the multiplication of Tag 01CU

`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean` builds the multiplication
isomorphism `Stacks.SheafOfModules.Invertible.tensorSheafPowerMulIso` of the nonnegative tensor
powers of an invertible sheaf of modules, as the multiplication isomorphism of a
`Stacks.Monoidal.PowerSystem` for the monoidal structure
`Stacks.SheafOfModules.monoidalCategory`, written through the comparison
`Stacks.SheafOfModules.tensorObjIso` of that structure's tensor product with the tensor product
sheaf of Tag 05NA.

The coherence laws Tag 01CU asserts for *its* multiplication
`Stacks.SheafOfModules.TensorPower.coherentMulIso` are stated instead against the fixed
constraints `Stacks.SheafOfModules.Invertible.tensorProduct…` of the tensor product sheaf, and
the two languages are reconciled by
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalInduced.lean`. This file carries out that
reconciliation for the two unit normalisations, in degrees `(a, 0)` and `(a, 1)`, and for
associativity, and concludes that the two multiplications agree in all nonnegative degrees.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorSheafPowerMulIso_zero_right`: **the power-system
  multiplication in degree `(a, 0)` is the fixed right unit constraint of the tensor product
  sheaf** — the same normalisation
  `Stacks.SheafOfModules.TensorPower.coherentMulIso_zero_right` records for Tag 01CU's
  multiplication.
* `Stacks.SheafOfModules.Invertible.tensorSheafPowerMulIso_assoc`: **the power-system
  multiplication is associative for the fixed associativity constraint of the tensor product
  sheaf** — the shape of `Stacks.SheafOfModules.TensorPower.coherentMulIso_assoc`.
* `Stacks.SheafOfModules.Invertible.tensorSheafPowerMulIso_one_right`: **the power-system
  multiplication in degree `(a, 1)` is the successor comparison** of Tag 01CU's powers,
  precomposed with the identification of the first power with `L` — the normalisation
  `Stacks.SheafOfModules.TensorPower.coherentMulIso_one_right` records.
* `Stacks.SheafOfModules.Invertible.tensorSheafPowerMulIso_eq_coherentMulIso`: **the power-system
  multiplication of the nonnegative tensor powers is the coherent multiplication of Tag 01CU**,
  in every pair of non-negative degrees.
* `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_zero` and
  `Stacks.SheafOfModules.Invertible.tensorPowerOneIso_eq_tensorProductLeftUnitor`: the two
  identifications the degree-`(a, 1)` normalisation is stated against. Both hold by `rfl`: the
  successor comparison out of the zeroth power is the identity, and the identification of the
  first power with `L` *is* the fixed left unit constraint.

## Implementation notes

The zeroth tensor power is the tensor unit on the nose, so the power system's zeroth-power
identification is the identity and the multiplication isomorphism in degree `(a, 0)` is the
right unitor of the *localized* monoidal structure, read through `tensorObjIso`. That the result
is the fixed right unit constraint of the tensor product sheaf is exactly
`Stacks.SheafOfModules.tensorObjIso_rightUnitor`, which is the right-unitality axiom of the
monoidal functor structure on sheafification.

Associativity is the localized `tensorPowerMulIso_assoc` conjugated by `tensorObjIso`: once each
fixed constraint is replaced by its comparison form, both sides acquire the same prefix and what
is left is the localized identity verbatim. No new coherence is used.

The degree-`(a, 1)` normalisation needs, beyond the two `rfl` identifications below, only the
triangle identity of the localized structure and `Stacks.SheafOfModules.tensorObjIso_leftUnitor`:
the second argument contributes its single tensor factor through the successor comparison in
degree `0`, and the zeroth power left behind is absorbed by the triangle. That argument is
carried out for an arbitrary power system in
`Stacks.Monoidal.PowerSystem.mulIso_one_hom`, where no sheaf theory is involved.

With the three normalisations and associativity in hand, the power-system multiplication is
*the* multiplication of Tag 01CU: `tensorSheafPowerMulIso_eq_coherentMulIso` is an ascending
induction on the right exponent against `coherentMulIso_zero_right`, `coherentMulIso_one_right`
and `coherentMulIso_assoc` directly, in the shape of
`Stacks.SheafOfModules.TensorPower.TensorPowerCoherence.mulIso_succ_right_eq`. It does *not* go
through `Stacks.SheafOfModules.TensorPower.coherentMulIso_eq`, which asks for a coherence datum
in all integer degrees — data the nonnegative powers do not carry. The one identification needed
beyond the laws is that the two developments of the successor comparison agree at a nonnegative
exponent, which is `tensorPowerSuccIso_eq_tensorPowerSuccIso`: both are the same recursion on
the exponent, so it is an induction with `rfl` in each case.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.Monoidal.PowerSystem

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The multiplication isomorphism of a power system in degree `(a, 1)`** is the `a`-th
successor comparison, precomposed with the identification of the first power with the generator.
The single tensor factor of the second argument is split off by the successor comparison in
degree `0`, and the zeroth power it leaves behind is absorbed by the triangle identity. -/
theorem mulIso_one_hom (S : PowerSystem C) (a : ℕ) :
    (S.mulIso a 1).hom
      = (S.obj a ◁ ((S.succIso 0).inv ≫ (S.objZeroIso.hom ▷ S.gen) ≫ (λ_ S.gen).hom))
          ≫ (S.succIso a).hom := by
  rw [S.mulIso_succ a 0, S.mulIso_zero a]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc, triangle_assoc_comp_right_assoc]
  rfl

end Stacks.Monoidal.PowerSystem

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.braidedCategory Stacks.SheafOfModules.symmetricCategory

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]

/-- **The multiplication isomorphism of the nonnegative tensor powers, in degree `(a, 0)`, is
the right unit constraint of the tensor product sheaf.** This is the normalisation Tag 01CU
asserts for its canonical multiplication, here for the multiplication built from the power
system of the tensor powers. -/
theorem tensorSheafPowerMulIso_zero_right (a : ℕ) :
    tensorSheafPowerMulIso O hO L a 0
      = tensorProductRightUnitor O hO (tensorPower O hO L (a : ℤ)) := by
  refine Iso.ext ?_
  change (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L (a : ℤ))
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).inv ≫
      (tensorPower O hO L (a : ℤ) ◁ 𝟙 (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))) ≫
      (ρ_ (tensorPower O hO L (a : ℤ))).hom
    = (tensorProductRightUnitor O hO (tensorPower O hO L (a : ℤ))).hom
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← Stacks.SheafOfModules.tensorObjIso_rightUnitor O hO (tensorPower O hO L (a : ℤ)),
    Iso.inv_hom_id_assoc]

/-- The tensor product sheaf of a pair of isomorphisms, read through the comparison with the
localized monoidal structure. -/
theorem tensorProductIso_hom_eq_tensorObjIso
    {M M' N N' : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (e : M ≅ M') (f : N ≅ N') :
    (tensorProductIso O hO e f).hom
      = (Stacks.SheafOfModules.tensorObjIso O hO M N).inv ≫ (e.hom ⊗ₘ f.hom) ≫
        (Stacks.SheafOfModules.tensorObjIso O hO M' N').hom :=
  Stacks.SheafOfModules.sheafifyTensorHom_eq_comparison O hO e.hom f.hom

/-- The multiplication isomorphism of the nonnegative tensor powers, written with the tensor
product sheaf, is the one for the localized tensor product read through the comparison. -/
theorem tensorSheafPowerMulIso_hom (a b : ℕ) :
    (tensorSheafPowerMulIso O hO L a b).hom
      = (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L (a : ℤ))
          (tensorPower O hO L (b : ℤ))).inv ≫ (tensorPowerMulIso O hO L a b).hom := rfl

/-- **The multiplication isomorphisms of the nonnegative tensor powers are associative for the
fixed associativity constraint of the tensor product sheaf.** This is
`Stacks.SheafOfModules.Invertible.tensorPowerMulIso_assoc`, which is stated for the localized
monoidal structure, carried across the comparison `Stacks.SheafOfModules.tensorObjIso`; it is
the shape in which Tag 01CU asserts associativity. -/
theorem tensorSheafPowerMulIso_assoc (a b c : ℕ) :
    tensorProductIso O hO (tensorSheafPowerMulIso O hO L a b)
          (Iso.refl (tensorPower O hO L (c : ℤ))) ≪≫
        tensorSheafPowerMulIso O hO L (a + b) c
      = tensorProductAssociator O hO (tensorPower O hO L (a : ℤ))
            (tensorPower O hO L (b : ℤ)) (tensorPower O hO L (c : ℤ)) ≪≫
          tensorProductIso O hO (Iso.refl (tensorPower O hO L (a : ℤ)))
            (tensorSheafPowerMulIso O hO L b c) ≪≫
          tensorSheafPowerMulIso O hO L a (b + c) ≪≫
          eqToIso (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ))
            (Nat.add_assoc a b c).symm) := by
  refine Iso.ext ?_
  have key := tensorPowerMulIso_assoc O hO L a b c
  simp only [Iso.trans_hom, tensorProductIso_hom_eq_tensorObjIso, tensorSheafPowerMulIso_hom,
    Iso.refl_hom,
    tensorIso_hom, tensorHom_id, id_tensorHom, eqToIso.hom, Iso.symm_hom,
    Stacks.SheafOfModules.tensorProductAssociator_eq_comparison, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc, Iso.hom_inv_id_assoc,
    MonoidalCategory.whiskerLeft_hom_inv_assoc]
  rw [key]

/-- The successor comparison out of the zeroth tensor power is the identity: the zeroth power is
the tensor unit on the nose and the first power is the tensor product sheaf of the unit with `L`
on the nose, so the comparison between them has nothing to do. -/
theorem tensorPowerSuccIso_zero : tensorPowerSuccIso O hO L (0 : ℤ) = Iso.refl _ := rfl

/-- **The identification of the first tensor power with `L` is the fixed left unit constraint of
the tensor product sheaf.** Both are the sheafification of the left unitor of the underlying
presheaves followed by the sheafification counit. -/
theorem tensorPowerOneIso_eq_tensorProductLeftUnitor :
    tensorPowerOneIso O hO L = tensorProductLeftUnitor O hO L := rfl

/-- The identification of the first tensor power with `L`, read through the comparison of the
localized tensor product with the tensor product sheaf: it is the left unitor of the localized
monoidal structure. -/
theorem tensorPowerOneIso_hom_eq :
    (tensorPowerOneIso O hO L).hom
      = (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L (0 : ℤ)) L).inv
          ≫ (λ_ L).hom :=
  (Iso.eq_inv_comp _).mpr (Stacks.SheafOfModules.tensorObjIso_leftUnitor O hO L)

/-- The multiplication isomorphism of the nonnegative tensor powers in degree `(a, 1)`, for the
localized tensor product: the identification of the first power with `L`, then the successor
comparison. -/
theorem tensorPowerMulIso_one_hom (a : ℕ) :
    (tensorPowerMulIso O hO L a 1).hom
      = (tensorPower O hO L (a : ℤ) ◁ (tensorPowerOneIso O hO L).hom)
          ≫ (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L (a : ℤ)) L).hom
          ≫ (tensorPowerSuccIso O hO L (a : ℤ)).hom := by
  have hid : (𝟙 (tensorPower O hO L (0 : ℤ)) ▷ L) ≫ (λ_ L).hom = (λ_ L).hom := by
    rw [id_whiskerRight]
    exact Category.id_comp _
  have hsucc : (tensorPowerSuccIso O hO L (0 : ℤ)).inv
        ≫ (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L (0 : ℤ)) L).inv
      = (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L (0 : ℤ)) L).inv :=
    Category.id_comp _
  have hinner :
      ((tensorPowerSuccIso O hO L (0 : ℤ)).inv
          ≫ (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L (0 : ℤ)) L).inv)
        ≫ ((𝟙 (tensorPower O hO L (0 : ℤ)) ▷ L) ≫ (λ_ L).hom)
      = (tensorPowerOneIso O hO L).hom := by
    rw [hid, hsucc]
    exact (tensorPowerOneIso_hom_eq O hO L).symm
  refine ((tensorPowerSystem O hO L).mulIso_one_hom a).trans ?_
  rw [show ((tensorPowerSystem O hO L).succIso 0).inv
        ≫ ((tensorPowerSystem O hO L).objZeroIso.hom ▷ (tensorPowerSystem O hO L).gen)
          ≫ (λ_ (tensorPowerSystem O hO L).gen).hom
      = (tensorPowerOneIso O hO L).hom from hinner]
  rfl

/-- **The multiplication isomorphism of the nonnegative tensor powers in degree `(a, 1)` is the
successor comparison**, precomposed with the identification of the first power with `L`. This is
the third normalisation Tag 01CU asserts for its canonical multiplication, in the shape of
`Stacks.SheafOfModules.TensorPower.coherentMulIso_one_right`. -/
theorem tensorSheafPowerMulIso_one_right (a : ℕ) :
    tensorSheafPowerMulIso O hO L a 1
      = tensorProductIso O hO (Iso.refl (tensorPower O hO L (a : ℤ)))
          (tensorPowerOneIso O hO L) ≪≫ tensorPowerSuccIso O hO L (a : ℤ) := by
  refine Iso.ext ?_
  rw [tensorSheafPowerMulIso_hom, tensorPowerMulIso_one_hom, Iso.trans_hom,
    tensorProductIso_hom_eq_tensorObjIso, Iso.refl_hom, id_tensorHom]
  simp only [Category.assoc]
  rfl

/-! ### Agreement with the coherent multiplication of Tag 01CU -/

-- `Stacks.SheafOfModules.Invertible.powNatSuccIso_eq` -- that the successor comparisons of the
-- library's two developments of the integer tensor powers agree at a non-negative exponent --
-- was proved here and, identically, in
-- `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridgeSuccIso`.  The two copies had
-- the same full name, so importing both failed.  The canonical copy is the one in that module:
-- it is where the `Equivalence.powNat` vocabulary this lemma bridges is developed, its import
-- closure is 7 modules against this file's 37, and it also carries the integer-exponent
-- versions.  This file now imports it.

/-- **The two developments of the successor comparison of the integer tensor powers agree at a
non-negative exponent.** The two differ only in the form in which invertibility of `L` is taken;
`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower` records that the powers themselves
are the same sheaf. -/
theorem tensorPowerSuccIso_eq_tensorPowerSuccIso (a : ℕ) :
    tensorPowerSuccIso O hO L (a : ℤ)
      = Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso O hO L (a : ℤ) :=
  powNatSuccIso_eq _ a _

/-- In degree `(a, 1)` the power-system multiplication is the coherent multiplication of Tag
01CU: both are the successor comparison read through the identification of the first power
with `L`. -/
theorem tensorSheafPowerMulIso_one_eq (a : ℕ) :
    tensorSheafPowerMulIso O hO L a 1
      = Stacks.SheafOfModules.TensorPower.coherentMulIso O hO L (a : ℤ) 1 := by
  refine (tensorSheafPowerMulIso_one_right O hO L a).trans ?_
  rw [Stacks.SheafOfModules.TensorPower.coherentMulIso_one_right,
    tensorPowerSuccIso_eq_tensorPowerSuccIso]
  rfl

/-- **The multiplication of the nonnegative tensor powers is the coherent multiplication of
Tag 01CU**, in every pair of non-negative degrees. The induction is on the right exponent: the
multiplication in degree `(a, 0)` is the right unit constraint on both sides, the multiplication
in degree `(a, 1)` is the successor comparison on both sides, and associativity in degrees
`(a, b, 1)` carries the agreement in degree `(a, b)` to degree `(a, b + 1)`. -/
theorem tensorSheafPowerMulIso_eq_coherentMulIso (a b : ℕ) :
    tensorSheafPowerMulIso O hO L a b
      = Stacks.SheafOfModules.TensorPower.coherentMulIso O hO L (a : ℤ) (b : ℤ) := by
  suffices h : ∀ b a : ℕ, tensorSheafPowerMulIso O hO L a b
      = Stacks.SheafOfModules.TensorPower.coherentMulIso O hO L (a : ℤ) (b : ℤ) from h b a
  intro b
  induction b with
  | zero =>
      intro a
      have h0 : Stacks.SheafOfModules.TensorPower.coherentMulIso O hO L (a : ℤ) ((0 : ℕ) : ℤ)
            ≪≫ Iso.refl _
          = tensorProductRightUnitor O hO (tensorPower O hO L (a : ℤ)) :=
        Stacks.SheafOfModules.TensorPower.coherentMulIso_zero_right O hO L (a : ℤ)
      rw [Iso.trans_refl] at h0
      exact (tensorSheafPowerMulIso_zero_right O hO L a).trans h0.symm
  | succ b ih =>
      intro a
      have hn := tensorSheafPowerMulIso_assoc O hO L a b 1
      rw [ih a, tensorSheafPowerMulIso_one_eq, tensorSheafPowerMulIso_one_eq] at hn
      exact Stacks.SheafOfModules.TensorPower.iso_cancel_right _
        (Stacks.SheafOfModules.TensorPower.iso_cancel_left _
          (Stacks.SheafOfModules.TensorPower.iso_cancel_left _
            (hn.symm.trans (Stacks.SheafOfModules.TensorPower.coherentMulIso_assoc O hO L
              (a : ℤ) (b : ℤ) 1))))

end Stacks.SheafOfModules.Invertible

end

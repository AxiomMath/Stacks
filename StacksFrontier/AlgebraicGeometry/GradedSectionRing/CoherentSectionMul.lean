module

public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.CoherentNormalisation
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.NatPowerSystem
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The product of two global sections is their pure tensor, and the two products agree

Let `O` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `O`-modules.
There are two descriptions of the product of a global section of `L^{⊗ n}` with a global
section of `L^{⊗ m}`.

* As a morphism out of the tensor unit. A global section is a morphism
  `𝟙 ⟶ L^{⊗ n}`, two of them tensor to `Stacks.Monoidal.sectionTensor`, and the product is that
  followed by the multiplication isomorphism of the power system of tensor powers:
  `Stacks.Monoidal.PowerSystem.sectionMul`. This is the description the chart of [Stacks, Tag
  01N8] is built on.
* As a local section. A global section is an element of `Γ(L^{⊗ n}, ⊤)`, two of them determine a
  section `Stacks.SheafOfModules.tensorSectionsAt` of the tensor product sheaf, and the product
  is the image of that under the coherent multiplication of [Stacks, Tag 01CU]:
  `Stacks.SheafOfModules.TensorPower.mulBilinear`, the multiplication of the Laurent algebra.
  This is the description the map `ψ` of a quadruple of Section 01NS is stated against.

**The two agree.** The multiplication isomorphisms already agree
(`Stacks.SheafOfModules.Invertible.tensorSheafPowerMulIso_eq_coherentMulIso`), so what is proved
here is the identification of the two spellings of the *pure tensor of two global sections*: the
section of `𝟙 ⊗ 𝟙` carrying the pair of units is the one carrying the two unit sections, and so
`sectionTensor` reads on local sections as `tensorSectionsAt`.

## Main results

* `Stacks.SheafOfModules.tensorObjIso_hom_val_app_sectionTensor`: **the tensor product of two
  morphisms out of the tensor unit reads, on local sections, as the section of the tensor
  product sheaf determined by their two local sections.**
* `Stacks.SheafOfModules.Invertible.sectionMul_val_app_one`: **the two products of global
  sections agree** — the power-system product of two morphisms out of the tensor unit, read on
  local sections, is the Laurent multiplication of the two local sections.
* `Stacks.SheafOfModules.Invertible.mulBilinear_natTensorPowCompare`: **the comparison of the
  iterated tensor powers with the integer tensor powers of [Stacks, Tag 01CU] is multiplicative
  for the Laurent multiplication**, on local sections. This is
  `Stacks.SheafOfModules.Invertible.mul_comp_natTensorPowCompare` with the multiplication on the
  integer-power side written as the multiplication of the Laurent algebra rather than as the
  power-system product.

## Implementation notes

The left unit constraint does the work. `Stacks.Monoidal.sectionTensor p q` is
`(λ_ 𝟙).inv ≫ (p ⊗ₘ q)`, so naturality of the comparison
`Stacks.SheafOfModules.tensorObjIso` of the localized tensor product with the tensor product
sheaf of Tag 05NA moves `p ⊗ₘ q` out of the way, and what is left is the localized left unitor
of the unit against the comparison — which `Stacks.SheafOfModules.tensorObjIso_leftUnitor`
identifies with the fixed left unit constraint of the tensor product sheaf. On the section `1`
that constraint is computed by `Stacks.SheafOfModules.tensorSheafLeftUnitor_hom_val_app_tmul`,
whose value `1 • 1 = 1` is what makes the pure tensor of the two unit sections the preimage of
`1`.

Every statement below is for an arbitrary object `U` of the site, not only for a terminal one:
all three are identities between morphisms of sheaves of modules read on sections, and none of
them needs global sections to be a special case.

The `1` of `(structureSheaf O hO).obj.obj U` and the `1` of `(𝟙_ _).val.obj U` are the same
element of the same type, but only definitionally; a `rw` on a goal mentioning both reports the
mixed term as not type-correct. The proofs below are therefore given as composites of `congrArg`
rather than by rewriting, which is the discipline
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorLeftUnitorSections.lean` records for the
same reason.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

attribute [local instance_reducible] TensorSheafification.structureSheaf
  CategoryTheory.LocalizedMonoidal CategoryTheory.Localization.Monoidal.toMonoidalCategory

attribute [local implicit_reducible] Tensor.ringSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory braidedCategory symmetricCategory

/-- **The localized left unitor of the tensor unit against the comparison with the tensor
product sheaf is the inverse of the fixed left unit constraint.** This is
`tensorObjIso_leftUnitor` at `M = 𝟙`, rearranged. -/
theorem leftUnitor_inv_comp_tensorObjIso_hom :
    (λ_ (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv ≫
        (tensorObjIso O hO (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
          (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).hom
      = (Invertible.tensorProductLeftUnitor O hO
          (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv :=
  (Iso.inv_comp_eq (λ_ (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO))))).mpr
    ((Iso.eq_comp_inv (Invertible.tensorProductLeftUnitor O hO
          (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO))))).mpr
      (tensorObjIso_leftUnitor O hO
        (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))))

/-- **The tensor product of two morphisms out of the tensor unit, read through the comparison
with the tensor product sheaf of Tag 05NA**: it is the fixed left unit constraint of the unit
against itself, followed by the sheafified tensor product of the two morphisms. -/
theorem sectionTensor_comp_tensorObjIso_hom
    (M N : _root_.SheafOfModules.{w} (structureSheaf O hO))
    (p : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶ M)
    (q : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶ N) :
    Stacks.Monoidal.sectionTensor p q ≫ (tensorObjIso O hO M N).hom
      = (Invertible.tensorProductLeftUnitor O hO
            (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv ≫
          sheafifyTensorHom O hO p q :=
  (Category.assoc (λ_ (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv (p ⊗ₘ q)
        (tensorObjIso O hO M N).hom).trans
    ((congrArg
          (fun φ => (λ_ (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv ≫ φ)
          (tensorObjIso_naturality O hO p q)).trans
      ((Category.assoc (λ_ (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv
            (tensorObjIso O hO (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
              (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).hom
            (sheafifyTensorHom O hO p q)).symm.trans
        (congrArg (fun φ => φ ≫ sheafifyTensorHom O hO p q)
          (leftUnitor_inv_comp_tensorObjIso_hom O hO))))

/-- **The inverse of the left unit constraint carries `1` to the pure tensor of the two unit
sections.** The constraint itself carries that pure tensor to `1 • 1 = 1`
(`tensorSheafLeftUnitor_hom_val_app_tmul`), and it is an isomorphism. -/
theorem tensorProductLeftUnitor_inv_val_app_one (U : Cᵒᵖ) :
    (Invertible.tensorProductLeftUnitor O hO
          (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv.val.app U
        (1 : (structureSheaf O hO).obj.obj U)
      = tensorSectionsAt O hO U (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
          (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
          (1 : (structureSheaf O hO).obj.obj U) (1 : (structureSheaf O hO).obj.obj U) := by
  have hhom : (Invertible.tensorProductLeftUnitor O hO
        (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).hom.val.app U
      (tensorSectionsAt O hO U (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
        (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
        (1 : (structureSheaf O hO).obj.obj U) (1 : (structureSheaf O hO).obj.obj U))
      = (1 : (structureSheaf O hO).obj.obj U) :=
    (tensorSheafLeftUnitor_hom_val_app_tmul O hO
      (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO))) U
      (1 : (structureSheaf O hO).obj.obj U)
      (1 : (structureSheaf O hO).obj.obj U)).trans (one_smul _ _)
  calc (Invertible.tensorProductLeftUnitor O hO
          (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv.val.app U
          (1 : (structureSheaf O hO).obj.obj U)
      = (Invertible.tensorProductLeftUnitor O hO
            (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).inv.val.app U
          ((Invertible.tensorProductLeftUnitor O hO
              (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))).hom.val.app U
            (tensorSectionsAt O hO U (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
              (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
              (1 : (structureSheaf O hO).obj.obj U)
              (1 : (structureSheaf O hO).obj.obj U))) := by rw [hhom]
    _ = tensorSectionsAt O hO U (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
          (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)))
          (1 : (structureSheaf O hO).obj.obj U)
          (1 : (structureSheaf O hO).obj.obj U) := by
        rw [← comp_val_app_apply, Iso.hom_inv_id]
        rfl

/-- **The pure tensor of two global sections, in the two spellings.** The tensor product
`Stacks.Monoidal.sectionTensor p q` of two morphisms out of the tensor unit, read on local
sections over `U` and transported along the comparison with the tensor product sheaf of Tag
05NA, is the section `tensorSectionsAt` of that sheaf determined by the two local sections of
`p` and `q`. -/
theorem tensorObjIso_hom_val_app_sectionTensor
    (M N : _root_.SheafOfModules.{w} (structureSheaf O hO))
    (p : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶ M)
    (q : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶ N) (U : Cᵒᵖ) :
    (tensorObjIso O hO M N).hom.val.app U
        ((Stacks.Monoidal.sectionTensor p q).val.app U
          (1 : (structureSheaf O hO).obj.obj U))
      = tensorSectionsAt O hO U M N (p.val.app U (1 : (structureSheaf O hO).obj.obj U))
          (q.val.app U (1 : (structureSheaf O hO).obj.obj U)) :=
  ((congrArg
        (fun φ : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
                (M)).obj (N)) =>
          φ.val.app U (1 : (structureSheaf O hO).obj.obj U))
        (sectionTensor_comp_tensorObjIso_hom O hO M N p q)).trans
      (congrArg (fun z => (sheafifyTensorHom O hO p q).val.app U z)
        (tensorProductLeftUnitor_inv_val_app_one O hO U))).trans
    (tensorSections_tensorMapAt O hO U _ M _ N p q
      (1 : (structureSheaf O hO).obj.obj U) (1 : (structureSheaf O hO).obj.obj U))

namespace Invertible

open AlgebraicGeometry.SheafOfModules (IsInvertible)

variable (L : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO L]

/-- **The multiplication isomorphism of the power system of tensor powers, written with the
tensor product sheaf of Tag 05NA**: it is the comparison with that sheaf followed by the
coherent multiplication of Tag 01CU. This is
`tensorSheafPowerMulIso_eq_coherentMulIso` rearranged. -/
theorem tensorPowerMulIso_hom (a b : ℕ) :
    (tensorPowerMulIso O hO L a b).hom
      = (tensorObjIso O hO (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ))).hom ≫
          (Stacks.SheafOfModules.TensorPower.coherentMulIso O hO L (a : ℤ) (b : ℤ)).hom :=
  (Iso.inv_comp_eq _).mp
    (congrArg Iso.hom (tensorSheafPowerMulIso_eq_coherentMulIso O hO L a b))

/-- **The two products of global sections of tensor powers agree.** The power-system product
`Stacks.Monoidal.PowerSystem.sectionMul` of two morphisms out of the tensor unit, read on local
sections over `U`, is the multiplication
`Stacks.SheafOfModules.TensorPower.mulBilinear` of the Laurent algebra — the coherent
multiplication of Tag 01CU — applied to the two local sections.

This is the identification that lets a graded map into `Γ_*(T, L)` written with one of the two
products be used where the other is expected. -/
theorem sectionMul_val_app_one (a b : ℕ) (U : Cᵒᵖ)
    (p : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶ tensorPower O hO L (a : ℤ))
    (q : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶ tensorPower O hO L (b : ℤ)) :
    ((tensorPowerSystem O hO L).sectionMul p q).val.app U
        (1 : (structureSheaf O hO).obj.obj U)
      = (Stacks.SheafOfModules.TensorPower.mulBilinear O hO L (a : ℤ) (b : ℤ)).app U
          (p.val.app U (1 : (structureSheaf O hO).obj.obj U))
          (q.val.app U (1 : (structureSheaf O hO).obj.obj U)) :=
  (congrArg
        (fun φ : tensorPower O hO L (a : ℤ) ⊗ tensorPower O hO L (b : ℤ) ⟶
            tensorPower O hO L ((a + b : ℕ) : ℤ) =>
          φ.val.app U ((Stacks.Monoidal.sectionTensor p q).val.app U
            (1 : (structureSheaf O hO).obj.obj U)))
        (tensorPowerMulIso_hom O hO L a b)).trans
    (congrArg
      (fun z => (Stacks.SheafOfModules.TensorPower.coherentMulIso O hO L
          (a : ℤ) (b : ℤ)).hom.val.app U z)
      (tensorObjIso_hom_val_app_sectionTensor O hO _ _ p q U))

/-- **The comparison of the iterated tensor powers with the integer tensor powers of Tag 01CU
is multiplicative for the multiplication of the Laurent algebra**, read on local sections. On
the iterated side the product is `Stacks.GradedSections.mul`, on the integer side it is
`Stacks.SheafOfModules.TensorPower.mulBilinear`.

This is `mul_comp_natTensorPowCompare`, whose right-hand side is the power-system product, with
that product replaced by the Laurent multiplication through `sectionMul_val_app_one`. -/
theorem mulBilinear_natTensorPowCompare (a b : ℕ) (U : Cᵒᵖ)
    (s : Stacks.GradedSections.powSections L a) (t : Stacks.GradedSections.powSections L b) :
    (Stacks.SheafOfModules.TensorPower.mulBilinear O hO L (a : ℤ) (b : ℤ)).app U
        ((s ≫ (natTensorPowCompare O hO L a).hom).val.app U
          (1 : (structureSheaf O hO).obj.obj U))
        ((t ≫ (natTensorPowCompare O hO L b).hom).val.app U
          (1 : (structureSheaf O hO).obj.obj U))
      = (Stacks.GradedSections.mul s t ≫ (natTensorPowCompare O hO L (a + b)).hom).val.app U
          (1 : (structureSheaf O hO).obj.obj U) :=
  ((congrArg
      (fun φ : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf O hO)) ⟶
          tensorPower O hO L ((a + b : ℕ) : ℤ) =>
        φ.val.app U (1 : (structureSheaf O hO).obj.obj U))
      (mul_comp_natTensorPowCompare O hO L s t)).trans
    (sectionMul_val_app_one O hO L a b U _ _)).symm

end Invertible

end Stacks.SheafOfModules

end

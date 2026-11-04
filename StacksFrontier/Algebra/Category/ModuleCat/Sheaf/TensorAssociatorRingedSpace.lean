module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The associativity constraint of the tensor product sheaf of Tag 01CB

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace` builds the tensor product
of two sheaves of `𝒪_X`-modules on a ringed space `X` by hand, as the sheafification
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` of the presheaf
`U ↦ ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)`. That is the tensor product the ideal-sheaf and generating-sections
development uses: `Stacks.Divisors.idealTensorMulIso` and
`Stacks.SheafOfModules.kernelTensorGeneratingSections` are stated over it.

The associativity constraint, on the other hand, was only available for the Tag 05NA tensor
product `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, as
`Stacks.SheafOfModules.tensorSheafAssociator`. This file supplies it for the Tag 01CB spelling.

## Main results

* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafAssociator`:
  `(ℱ ⊗ 𝒢) ⊗ ℋ ≅ ℱ ⊗ (𝒢 ⊗ ℋ)` for the Tag 01CB tensor product sheaf.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafAssociator'`: the same isomorphism
  read in the other direction, `ℱ ⊗ (𝒢 ⊗ ℋ) ≅ (ℱ ⊗ 𝒢) ⊗ ℋ`.

## Implementation notes

The two tensor products are definitionally equal, by
`Stacks.TensorSheafDedup.tensorSheaf_eq`, so one might expect the Tag 05NA associator to be
usable at the Tag 01CB spelling directly, with the elaborator discharging the comparison. It is
not. A *single* comparison `ℱ ⊗ 𝒢 = ℱ ⊗' 𝒢` is what `Stacks.TensorSheafDedup.tensorSheaf_eq`
proves by `rfl`, and that is affordable; the comparison needed to apply the associator is the
*nested* one, `(ℱ ⊗ 𝒢) ⊗ ℋ = (ℱ ⊗' 𝒢) ⊗' ℋ`, in which each tensor product sheaf is a
sheafification of a presheaf tensor product whose arguments are themselves sheafifications of
presheaf tensor products, and asking the elaborator for it exhausts the heartbeat budget.

So no nested comparison is ever requested here. `tensorSheaf05NA` retypes the Tag 05NA tensor
product so that its arguments and its value live in the category of modules over
`structureSheafRing`, which costs exactly the
comparison `Stacks.TensorSheafDedup.structureSheafRing_eq` of the two ring sheaves, and
`tensorSheaf_eq'` restates `Stacks.TensorSheafDedup.tensorSheaf_eq` there; both are single,
unnested comparisons. The nested identifications `tensorSheaf_assocLeft_eq` and
`tensorSheaf_assocRight_eq` are then assembled from that one *proved equality* by `congrArg` and
`Eq.trans`, so they are instantiations of an already-proved theorem rather than new work for the
kernel, and the associator is transported along them by `eqToIso`. Every isomorphism composed in
`tensorSheafAssociator` is an isomorphism of the single category
`SheafOfModules (structureSheafRing X)` between objects that match syntactically.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The Tag 05NA tensor product sheaf of a ringed space, retyped so that its arguments and its
value are modules over `structureSheafRing X`, the ring sheaf the Tag 01CB development uses.
The retyping is the comparison `Stacks.TensorSheafDedup.structureSheafRing_eq` of the two ring
sheaves, and nothing else. -/
noncomputable def tensorSheaf05NA (A B : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (structureSheafRing X) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
      (_root_.structureSheafRing X).property⟩).obj A).obj B

/-- `Stacks.TensorSheafDedup.tensorSheaf_eq`, read at the retyped Tag 05NA tensor product. This
is the only comparison of the two constructions that is ever asked of the elaborator here. -/
theorem tensorSheaf_eq' (A B : SheafOfModules.{u} (structureSheafRing X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj B =
      tensorSheaf05NA X A B :=
  Stacks.TensorSheafDedup.tensorSheaf_eq X A B

/-- The Tag 05NA associativity constraint, retyped as an isomorphism of modules over
`structureSheafRing X`. -/
noncomputable def assoc05NA (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    tensorSheaf05NA X (tensorSheaf05NA X A B) C ≅
      tensorSheaf05NA X A (tensorSheaf05NA X B C) :=
  Stacks.SheafOfModules.tensorSheafAssociator X.presheaf
    (_root_.structureSheafRing X).property A B C

/-- The left-bracketed triple tensor products of the two constructions agree. Assembled from the
single proved equality `tensorSheaf_eq'` by `congrArg`, so that the nested comparison is never
requested of the elaborator. -/
theorem tensorSheaf_assocLeft_eq (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj B)).obj C =
      tensorSheaf05NA X (tensorSheaf05NA X A B) C :=
  (tensorSheaf_eq' X
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj B) C).trans
    (congrArg (fun Z => tensorSheaf05NA X Z C) (tensorSheaf_eq' X A B))

/-- The right-bracketed triple tensor products of the two constructions agree. -/
theorem tensorSheaf_assocRight_eq (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj B).obj C) =
      tensorSheaf05NA X A (tensorSheaf05NA X B C) :=
  (tensorSheaf_eq' X A
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj B).obj C)).trans
    (congrArg (fun Z => tensorSheaf05NA X A Z) (tensorSheaf_eq' X B C))

/-- **The associativity constraint of the tensor product sheaf of Tag 01CB.** For sheaves of
`𝒪_X`-modules `ℱ`, `𝒢`, `ℋ` on a ringed space there is a canonical isomorphism
`(ℱ ⊗_{𝒪_X} 𝒢) ⊗_{𝒪_X} ℋ ≅ ℱ ⊗_{𝒪_X} (𝒢 ⊗_{𝒪_X} ℋ)`.

It is `Stacks.SheafOfModules.tensorSheafAssociator`, the associativity constraint of the Tag 05NA
tensor product — on local pure tensors the re-bracketing map
`(m ⊗ n) ⊗ p ↦ m ⊗ (n ⊗ p)`, by
`Stacks.SheafOfModules.tensorSheafAssociator_hom_val_app_tmul` — transported along the
identification of the two constructions. -/
noncomputable def tensorSheafAssociator (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj B)).obj C ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj B).obj C) :=
  eqToIso (tensorSheaf_assocLeft_eq X A B C) ≪≫ assoc05NA X A B C ≪≫
    eqToIso (tensorSheaf_assocRight_eq X A B C).symm

/-- `tensorSheafAssociator` read in the other direction:
`ℱ ⊗_{𝒪_X} (𝒢 ⊗_{𝒪_X} ℋ) ≅ (ℱ ⊗_{𝒪_X} 𝒢) ⊗_{𝒪_X} ℋ`. -/
noncomputable def tensorSheafAssociator' (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj B).obj C) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj B)).obj C :=
  (tensorSheafAssociator X A B C).symm

end Stacks.SheafOfModules.TensorStalkRingedSpace

end

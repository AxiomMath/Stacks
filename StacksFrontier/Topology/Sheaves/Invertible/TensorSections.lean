module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product of two sections of sheaves of modules

Let `𝒪` be a sheaf of commutative rings on a site and let `F` and `G` be sheaves of
`𝒪`-modules. Over every object `U` of the site there is a canonical map
`F(U) × G(U) → (F ⊗ G)(U)`, sending a pair of sections to the image of their elementary
tensor under the unit of sheafification. On a ringed space, taken at the terminal open set,
this is the product of two global sections.

## Main definitions

* `AlgebraicGeometry.tensorSectionsOver`: the product of two sections over an object of the
  site, as a section of the tensor product sheaf of Tag 05NA.
* `AlgebraicGeometry.tensorSectionsTerminal`: the product of two global sections, that is, of
  two sections over the terminal object of the site.

## Implementation notes

The tensor product sheaf is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, the sheafification of the pointwise
tensor product of the underlying presheaves of modules, and the map is the component at `U` of
the unit `Stacks.SheafOfModules.TensorSheafification.toSheafify` of the sheafification
adjunction applied to an elementary tensor. The monoidal structure on presheaves of modules
over the ring presheaf is supplied as a local instance, as that file prescribes.

Nothing here needs `F` or `G` to be invertible, and nothing needs the site to have a terminal
object except `tensorSectionsTerminal` itself, which is why the general form over an arbitrary
object is stated separately.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped TensorProduct

universe v u w

namespace AlgebraicGeometry

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The product of a section of `F` and a section of `G` over an object `U` of the site, as a
section of the tensor product sheaf `F ⊗ G`: the image of the elementary tensor under the unit
of sheafification. -/
noncomputable def tensorSectionsOver (U : Cᵒᵖ)
    (F G : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (s : F.val.obj U) (t : G.val.obj U) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F)).obj (G))).val.obj U := by
  letI : MonoidalCategory (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :=
    PresheafOfModules.monoidalCategory (R := O)
  exact (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U
    (s ⊗ₜ[O.obj U] t)

variable [HasTerminal C]

/-- **Stacks Project, Tag 01CV.** The product of two global sections of sheaves of modules, as
a global section of their tensor product. This is the pairing whose iteration on the tensor
powers of an invertible sheaf gives the multiplication of the graded ring `Γ_*(X, L)`.

This is the pairing on a general site; `AlgebraicGeometry.tensorSections` is the pairing on the
sheaves of modules of a scheme, taken for
`Stacks.SheafOfModules.Invertible.tensorProduct` instead of
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`. -/
noncomputable def tensorSectionsTerminal
    (F G : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (s : F.val.obj (op (⊤_ C))) (t : G.val.obj (op (⊤_ C))) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F)).obj (G))).val.obj (op (⊤_ C)) :=
  tensorSectionsOver O hO (op (⊤_ C)) F G s t

end AlgebraicGeometry

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.MonoidalStructureOnPresheaves

/-!
# Composition of internal Hom sheaves

Let `(C, O)` be a ringed site and let `A`, `B`, `C` be sheaves of `O`-modules. A section of the
internal Hom sheaf `Hom_O(A, B)` of Stacks 03EM over an object `U` of the site is by definition a
morphism `A|_U ⟶ B|_U` of `O|_U`-modules, so two such sections may simply be composed. This file
packages that composition into a morphism of sheaves of modules

`Hom_O(B, C) ⊗_O Hom_O(A, B) ⟶ Hom_O(A, C)`,

the *composition pairing* of the internal Hom sheaves.

The order of the factors is the one of the composition morphism of internal Hom complexes of
Stacks 0A91, which has the Hom out of the *intermediate* object on the left; so the pairing is
`(β, γ) ↦ γ ≫ β`, and it is the degreewise shadow of Stacks 0A91 rather than a new construction.

## Main definitions

* `AlgebraicGeometry.RingedSite.internalHomComposeSection`: **composition of two local sections
  of internal Hom sheaves.**
* `AlgebraicGeometry.RingedSite.internalHomCompositionPresheafMap`: the pairing at the level of
  the pointwise tensor product of the underlying presheaves of modules.
* `AlgebraicGeometry.RingedSite.internalHomComposition`: **the composition pairing
  `Hom_O(B, C) ⊗_O Hom_O(A, B) ⟶ Hom_O(A, C)`** of sheaves of `O`-modules.
* `AlgebraicGeometry.RingedSite.internalHomTensorSection`: the local pure tensor of two sections
  of internal Hom sheaves, inside the sheafified tensor product.

## Main results

* `AlgebraicGeometry.RingedSite.internalHomComposeSection_apply`: a composed section evaluates as
  the composite of the evaluations.
* `AlgebraicGeometry.RingedSite.internalHomComposeSection_restrict`: composition of sections is
  compatible with restriction along an arrow of the site.
* `AlgebraicGeometry.RingedSite.internalHomComposition_tensorSection`: **the pairing sends a local
  pure tensor to the composite of its factors**, which is the characterising property.

## Implementation notes

**Why the pairing is built by hand rather than taken from the monoidal closed structure.** Sheaves
of `O`-modules are monoidal closed, and `CategoryTheory.MonoidalClosed.comp` is a composition
pairing for the monoidal-closed internal hom; transporting it along the identification
`AlgebraicGeometry.RingedSite.ihomIsoInternalHomSheaf` of that internal hom with Stacks 03EM's
produces a morphism of the right type in four lines. That morphism is unusable here. The
identification is a comparison of two right adjoints of the same functor, so it is only known
through the uniqueness of adjoints, and nothing in it describes either the evaluation morphism or
the pairing on local sections. Every consumer of the pairing in the Koszul computation needs
exactly that description, since what has to be recognised there is a determinant of local
pairings. Building the pairing out of `internalHomComposeSection` makes
`internalHomComposition_tensorSection` hold by construction.

**The source is the sheafified pointwise tensor product.** It is spelt as the sheafification of
`A.val ⊗ B.val` rather than as `Stacks.SheafOfModules.Tensor.sheafTensor`, although the two are
the same sheaf of modules, because this is the spelling in which
`AlgebraicGeometry.RingedSite.tensorTotal` presents the source of Stacks 0A91 and in which
`AlgebraicGeometry.RingedSite.tensorTotalSection` presents its local pure tensors. Keeping one
spelling is what lets the degreewise comparison with Stacks 0A91 be stated without a transport.

**Bilinearity of composition is four category-theoretic identities.** Additivity in each variable
is `CategoryTheory.Preadditive.comp_add` and `CategoryTheory.Preadditive.add_comp`. The scalar
action on a section of an internal Hom sheaf is postcomposition with multiplication by the scalar,
so homogeneity in the left-hand factor is associativity of composition; homogeneity in the
right-hand factor instead needs that multiplication by a scalar commutes with the section being
composed, which is the `O|_U`-linearity of that section.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory

section Sections

variable {A B D : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- **Composition of two local sections of internal Hom sheaves.** A section of `Hom_O(A, B)`
over `U` is a morphism `A|_U ⟶ B|_U`, and a section of `Hom_O(B, D)` over `U` is a morphism
`B|_U ⟶ D|_U`; their composite is a section of `Hom_O(A, D)` over `U`.

The section of the Hom out of the intermediate object is the first argument, matching the order
of the factors in the composition morphism of internal Hom complexes of Stacks 0A91. -/
def internalHomComposeSection (U : X.C)
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) :
    (internalHomSheaf X A D).val.obj (op U) :=
  γ ≫ β

/-- Composition of local sections of internal Hom sheaves is composition of the morphisms of
`O|_U`-modules they are. -/
theorem internalHomComposeSection_eq (U : X.C)
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) :
    internalHomComposeSection X U β γ = γ ≫ β :=
  rfl

/-- **A composed section evaluates, over every object of the slice site, as the composite of the
evaluations of its factors.** -/
theorem internalHomComposeSection_app (U : X.C)
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (internalHomComposeSection X U β γ).app V = γ.app V ≫ β.app V :=
  rfl

/-- Composition of local sections is additive in the section of `Hom_O(B, D)`. -/
theorem internalHomComposeSection_add_left (U : X.C)
    (β β' : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) :
    internalHomComposeSection X U (β + β') γ =
      internalHomComposeSection X U β γ + internalHomComposeSection X U β' γ :=
  Preadditive.comp_add _ _ _ _ _ _

/-- Composition of local sections is additive in the section of `Hom_O(A, B)`. -/
theorem internalHomComposeSection_add_right (U : X.C)
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ γ' : (internalHomSheaf X A B).val.obj (op U)) :
    internalHomComposeSection X U β (γ + γ') =
      internalHomComposeSection X U β γ + internalHomComposeSection X U β γ' :=
  Preadditive.add_comp _ _ _ _ _ _

/-- Composition of local sections is homogeneous in the section of `Hom_O(B, D)`: the scalar
action is postcomposition with multiplication by the scalar, so this is associativity of
composition. -/
theorem internalHomComposeSection_smul_left (U : X.C)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) :
    internalHomComposeSection X U (c • β) γ = c • internalHomComposeSection X U β γ :=
  (Category.assoc _ _ _).symm

/-- Composition of local sections is homogeneous in the section of `Hom_O(A, B)`: pulling a
scalar through the second factor is the `O|_U`-linearity of the first. -/
theorem internalHomComposeSection_smul_right (U : X.C)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) :
    internalHomComposeSection X U β (c • γ) = c • internalHomComposeSection X U β γ := by
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (β.app V).hom.map_smul _ _

/-- Composition of local sections commutes with restriction along an arrow of the site: the
restriction map of an internal Hom sheaf is relocalisation, a functor, so it preserves
composites. -/
theorem internalHomComposeSection_restrict {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (β : (internalHomSheaf X B D).val.obj U)
    (γ : (internalHomSheaf X A B).val.obj U) :
    internalHomComposeSection X V.unop ((internalHomSheaf X B D).val.map f β)
        ((internalHomSheaf X A B).val.map f γ) =
      (internalHomSheaf X A D).val.map f (internalHomComposeSection X U.unop β γ) :=
  rfl

end Sections

section Pairing

variable (A B D : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The composition pairing at the level of the pointwise tensor product of the underlying
presheaves of modules: on a pure tensor of local sections it is their composite. -/
def internalHomCompositionPresheafMap :
    (internalHomSheaf X B D).val ⊗ (internalHomSheaf X A B).val ⟶
      (internalHomSheaf X A D).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (M₁ := (internalHomSheaf X B D).val.obj U) (M₂ := (internalHomSheaf X A B).val.obj U)
    (M₃ := (internalHomSheaf X A D).val.obj U)
    (fun β γ => internalHomComposeSection X U.unop β γ)
    (fun β β' γ => internalHomComposeSection_add_left X U.unop β β' γ)
    (fun c β γ => internalHomComposeSection_smul_left X U.unop c β γ)
    (fun β γ γ' => internalHomComposeSection_add_right X U.unop β γ γ')
    (fun c β γ => internalHomComposeSection_smul_right X U.unop c β γ)
  naturality f :=
    ModuleCat.MonoidalCategory.tensor_ext fun β γ => internalHomComposeSection_restrict X f β γ

/-- **The composition pairing of internal Hom sheaves**

`Hom_O(B, D) ⊗_O Hom_O(A, B) ⟶ Hom_O(A, D)`,

a morphism of sheaves of `O`-modules out of the sheafified pointwise tensor product. It is the
extension to the sheafification of the pairing
`AlgebraicGeometry.RingedSite.internalHomCompositionPresheafMap`, which composes local sections,
along the unit of the sheafification adjunction. -/
def internalHomComposition :
    (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
        ((internalHomSheaf X B D).val ⊗ (internalHomSheaf X A B).val) ⟶
      internalHomSheaf X A D :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv _ _).symm
    (internalHomCompositionPresheafMap X A B D)

/-- The local pure tensor of a section of `Hom_O(B, D)` and a section of `Hom_O(A, B)` over the
same object, as a section of the sheafified tensor product. -/
def internalHomTensorSection (U : X.C)
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
      ((internalHomSheaf X B D).val ⊗ (internalHomSheaf X A B).val)).val.obj (op U) :=
  (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
    ((internalHomSheaf X B D).val ⊗ (internalHomSheaf X A B).val)).app (op U))
      (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] γ)

/-- **The composition pairing restricts along the sheafification unit to the pairing on local
sections.** This is the characterising property of
`AlgebraicGeometry.RingedSite.internalHomComposition`: a morphism out of a sheafification is
determined by its restriction along the unit. -/
theorem internalHomComposition_unit :
    (PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((internalHomSheaf X B D).val ⊗ (internalHomSheaf X A B).val) ≫
        (internalHomComposition X A B D).val =
      internalHomCompositionPresheafMap X A B D :=
  ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv
      ((internalHomSheaf X B D).val ⊗ (internalHomSheaf X A B).val)
      (internalHomSheaf X A D)).apply_symm_apply
    (internalHomCompositionPresheafMap X A B D)

/-- **The composition pairing sends a local pure tensor to the composite of its factors.** -/
theorem internalHomComposition_tensorSection (U : X.C)
    (β : (internalHomSheaf X B D).val.obj (op U))
    (γ : (internalHomSheaf X A B).val.obj (op U)) :
    (internalHomComposition X A B D).val.app (op U)
        (internalHomTensorSection X A B D U β γ) =
      internalHomComposeSection X U β γ :=
  congrArg
    (fun g => g.app (op U) (β ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] γ))
    (internalHomComposition_unit X A B D)

end Pairing

end AlgebraicGeometry.RingedSite

end

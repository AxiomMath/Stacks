module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.CechCofree
public import StacksFrontier.CategoryTheory.Sites.CechSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing

/-!
# Čech cohomology of an injective sheaf

`StacksFrontier/CategoryTheory/Sites/CechCofree.lean` proves that the positive-degree Čech
cohomology of a presheaf which is injective *in the presheaf category* vanishes, and
`StacksFrontier/CategoryTheory/Sites/CechSheaf.lean` identifies the degree `0` Čech cohomology
of a sheaf with its sections over the terminal object. This file joins the two for an
injective *sheaf*: an injective object of `Sheaf J A` is injective as a presheaf, because
sheafification is a left adjoint of the inclusion of sheaves into presheaves which preserves
monomorphisms. That step is Stacks Tag 03F6,
`CategoryTheory.sheafToPresheaf_preservesInjectiveObjects` and
`CategoryTheory.Sheaf.injective_obj`, which need no additive structure
on `A`; the abelian special case through exactness of sheafification is Stacks Tag 015Z,
proved as `preservesInjectiveObjects_of_isExact`.

This is the argument of [Stacks, Tag 01EP] carried out in the generality of an abelian
sheaf category. The tag itself is about an injective sheaf of `𝒪_X`-modules, where the
Čech complex is formed in the category of modules over the sections of `𝒪_X` on the covered
open; that case is **not** covered here, and the reason is recorded under "Implementation
notes".

## Main results

* `Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_injective_sheaf`: the
  positive-degree Čech cohomology of an injective sheaf vanishes.
* `Stacks.CategoryTheory.CechComplex.existsUnique_isIso_homologyZero_of_sheaf`: the degree
  `0` Čech cohomology of a sheaf is its object of sections over the terminal object, by the
  isomorphism induced by the augmentation.

## Implementation notes

`CategoryTheory.sheafToPresheaf` is not known to Mathlib to be additive, although its
additivity is definitional: addition of morphisms of sheaves is addition of the underlying
morphisms of presheaves. The instance is supplied here.

The route taken by the Stacks Project for a sheaf of `𝒪_X`-modules is the same one — an
injective sheaf of modules is injective in the category of *presheaves* of modules — and
that step is available for the same reason, through the sheafification adjunction for
presheaves of modules. What is missing for the tag itself is the next step: the Čech complex
of a sheaf of modules for a covering of an open `V` is formed after applying
`PresheafOfModules.forgetToPresheafModuleCat`, which views a presheaf of `𝒪_X`-modules as a
presheaf of modules over the single ring `𝒪_X(V)`. The left adjoint of that functor is
pointwise extension of scalars, `Q ↦ (T ↦ 𝒪_X(T) ⊗_{𝒪_X(V)} Q(T))`, which is right exact but
not exact, so injectivity does not transport along it and the hypothesis of
`isZero_homology_cechComplex_of_injective` is not available for the module-valued complex.
What is available is `isZero_homology_cechComplex_of_retract`, which needs only a splitting;
producing one requires the cofree object of the category of presheaves of modules, namely
`T ↦ ∏_{W ⟶ T} J` with `J` an `𝒪_X(W)`-module and each factor regarded as an `𝒪_X(T)`-module
by restriction of scalars along `𝒪_X(T) ⟶ 𝒪_X(W)`. That object is not in Mathlib, but it is
constructed in `StacksFrontier/CategoryTheory/Sites/Modules/Cofree.lean` as
`Stacks.CategoryTheory.PresheafOfModules.cofreeOne`, and
`Stacks.CategoryTheory.PresheafOfModules.forgetCofreeOneIso` of
`StacksFrontier/CategoryTheory/Sites/Modules/CofreeForget.lean` identifies its image under
`PresheafOfModules.forgetToPresheafModuleCat` with `cofreeOne` of this file. What is still
missing for the tag is the splitting itself; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Cohomology/CechModules.lean`.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type u')
  [Category.{v'} A] [Abelian A]

/-- The inclusion of sheaves into presheaves is additive: addition of morphisms of sheaves is
addition of the underlying morphisms of presheaves. -/
instance sheafToPresheaf_additive : (sheafToPresheaf J A).Additive where
  map_add := rfl

end CategoryTheory

namespace Stacks.CategoryTheory.CechComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [Abelian A]
  [HasFiniteProducts C] {ι : Type w} [HasProducts.{w} A] (U : ι → C)
  (J : GrothendieckTopology C) (I : Sheaf J A)

section Vanishing

variable [EnoughInjectives A] [HasProducts.{v} A] [HasSheafify J A] [Injective I]

/-- **Positive-degree Čech cohomology of an injective sheaf vanishes.** This is the
injectivity step of [Stacks, Tag 01EP] for a sheaf with values in an abelian category: the
underlying presheaf of an injective sheaf is injective in the presheaf category, where it is
a retract of a cofree presheaf whose Čech complex carries a contracting homotopy.

As in `isZero_homology_cechComplex_of_injective`, the family `obj` indexing the cofree
presheaf is only required to hit every object of `C`. -/
theorem isZero_homology_cechComplex_of_injective_sheaf {κ : Type t} [HasProducts.{t} A]
    (obj : κ → C) (hobj : ∀ W : C, ∃ k, obj k = W) (n : ℕ) (hn : 0 < n) :
    IsZero (((cechComplexFunctor U).obj I.obj).homology n) :=
  have : Injective I.obj := I.injective_obj
  isZero_homology_cechComplex_of_injective U obj I.obj hobj n hn

/-- **Positive-degree Čech cohomology of an injective sheaf vanishes**, with the cofree
presheaf taken over the family of all objects of `C`. -/
theorem isZero_homology_cechComplex_of_injective_sheaf' [HasProducts.{u} A] (n : ℕ)
    (hn : 0 < n) : IsZero (((cechComplexFunctor U).obj I.obj).homology n) :=
  isZero_homology_cechComplex_of_injective_sheaf U J I (id : C → C) (fun W ↦ ⟨W, rfl⟩) n hn

end Vanishing

/-- **Degree `0` Čech cohomology of a sheaf, for an object of `Sheaf J A`.** There is a
unique morphism from the sections over the terminal object to the degree `0` Čech cohomology
compatible with the augmentation, and it is an isomorphism. Injectivity is not used; this is
`existsUnique_isIso_homologyZero_of_isSheaf` for the underlying presheaf of a sheaf, recorded
here next to the positive-degree vanishing so that the two halves of [Stacks, Tag 01EP]
appear together. -/
theorem existsUnique_isIso_homologyZero_of_sheaf
    (hU : Sieve.ofArrows U (fun i ↦ terminal.from (U i)) ∈ J (⊤_ C)) :
    ∃! f : I.obj.obj (op (⊤_ C)) ⟶ ((cechComplexFunctor U).obj I.obj).homology 0,
      IsIso f ∧ f ≫ ((cechComplexFunctor U).obj I.obj).homologyι 0 =
        Stacks.Cohomology.CechZero.aug U I.obj terminalIsTerminal ≫
          ((cechComplexFunctor U).obj I.obj).pOpcycles 0 :=
  existsUnique_isIso_homologyZero_of_isSheaf U I.obj J I.property hU

end Stacks.CategoryTheory.CechComplex

end

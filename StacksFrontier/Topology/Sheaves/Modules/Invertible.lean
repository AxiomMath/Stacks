module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible and trivial sheaves of modules

Let `O` be a sheaf of commutative rings on a site. A sheaf `L` of `O`-modules is invertible
when tensoring on the left by `L` is an equivalence of the category of `O`-modules. It is
trivial when it is isomorphic to the structure sheaf, regarded as a module over itself.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsTrivial`: the module is isomorphic to the structure
  sheaf.
* `Stacks.SheafOfModules.Tensor.sheafTensor`: the canonical tensor bifunctor, used directly
  where sheafification of abelian-group-valued presheaves is available.

## Main results

Invertibility is exactly the assertion that the constructed sheafified tensor functor is an
equivalence; that is `Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`), and this module no longer
carries a second copy of it.

## Implementation notes

The universal property `TensorLeftUniversal` and the predicate `IsInvertible` are *not* defined
here: these names abbreviate `Stacks.SheafOfModules.TensorLeftUniversal` and
`Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, so there is one structure,
one class and one copy of each of `lift`, `ι_lift`, `comparison`, `uniqueIso`. The two namespaces
previously carried byte-identical definitions of all six, over the *same* structure sheaf
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`; only the copies are gone, the
names and what they mean are unchanged, and `lift`, `ι_lift`, `comparison` and `uniqueIso` are
reached by dot notation on the one structure.

The tensor functor is the canonical bifunctor evaluated at its left factor. This file does not
define another tensor-functor view; its universal-property and equivalence declarations name
the native expression directly.

The tensor product is characterised by the universal property of the associated sheaf of the
pointwise tensor product. `IsInvertible` asserts that a functor with this property is an
equivalence; it needs no sheafification instances on the site. When sheafification is
available, `tensorLeftFunctorUniversal` proves the universal property for the constructed
functor, and the comparison theorem recovers the usual tensor-functor interface. The
structure sheaf as a module over itself is `SheafOfModules.unit`.

The site object and morphism universes are independent of the section universe. The ring and
module sections share a universe, as required by the monoidal structure on presheaves of
modules. The general predicate imposes no relation between this universe and the size of the
site.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))

/-- The universal property pinning down the tensor functor: this is
`Stacks.SheafOfModules.TensorLeftUniversal`, not a second copy of it. -/
public abbrev TensorLeftUniversal
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
      ⥤
      _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
  Stacks.SheafOfModules.TensorLeftUniversal O hO L F

/-- **Stacks Project, Tag 01CS.** An `O`-module sheaf is invertible when its tensor functor is an
equivalence. This is `Stacks.SheafOfModules.IsInvertible`, not a second copy of it; the tag is
registered there, on the class itself. -/
public abbrev IsInvertible
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      : Prop :=
  Stacks.SheafOfModules.IsInvertible O hO L

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sheafified tensor functor has the tensor universal property; this is
`Stacks.SheafOfModules.tensorLeftFunctorUniversal`. -/
public noncomputable abbrev tensorLeftFunctorUniversal
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    TensorLeftUniversal O hO L
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L) :=
  Stacks.SheafOfModules.tensorLeftFunctorUniversal O hO L

/-- The universal-property definition agrees with the constructed tensor functor. The proof is
`Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`:260); because the class and
the functor above are that module's, this is the same statement, kept under this name for the
call sites that spell it this way. -/
public theorem isInvertible_iff_tensorLeftFunctor_isEquivalence
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    IsInvertible O hO L ↔
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          L).IsEquivalence :=
  Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L

/-- Existing tensor-functor APIs apply to any invertible sheaf; this is
`Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence` (same file, :272) under the name this
namespace's call sites use. -/
public instance tensorLeftFunctor_isEquivalence
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [h : IsInvertible O hO L] :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          L).IsEquivalence :=
  Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence O hO L

end Sheafification

/-- An `O`-module sheaf is trivial when it is isomorphic, as an `O`-module, to `O`
itself. -/
@[stacks 01CS "trivial"]
noncomputable abbrev IsTrivial
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      : Prop :=
  Nonempty (L ≅ _root_.SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

end AlgebraicGeometry.SheafOfModules

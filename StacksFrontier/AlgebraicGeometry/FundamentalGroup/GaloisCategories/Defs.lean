module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Galois categories with a fixed fibre functor

A category together with a functor to sets is a Galois category when the category has finite
limits and colimits, every object is a finite coproduct of connected objects, all fibres are
finite, and the functor is exact and reflects isomorphisms.

## Main definitions

* `CategoryTheory.IsGaloisCategory` expresses the Galois category axioms for a fixed
  type-valued functor.

## Main results

The fields of `IsGaloisCategory` provide the finite connected-component decomposition and the
finiteness of every fibre. Its structural axioms are registered as instances.

## Implementation notes

Connected objects are expressed by `PreGaloisCategory.IsConnected`, Mathlib's categorical notion
of a noninitial object with no nontrivial subobjects. A finite coproduct decomposition is recorded
by a finite indexing type and a colimit cocone. Exactness is Mathlib's `exactFunctor`, namely
preservation of finite limits and finite colimits. Mathlib's class `CategoryTheory.GaloisCategory`
uses a different axiom system and does not retain a specified fibre functor, so it is not the
notion defined here.

## References

* [Stacks Project, Tag 0BMY](https://stacks.math.columbia.edu/tag/0BMY)
* [SGA1, Expose V, Definition 5.1]
* [BS, Definition 7.2.1]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory

/-- The Galois category axioms for a category `C` equipped with a fixed functor from `C` to
sets. -/
@[stacks 0BMY]
public class IsGaloisCategory {C : Type u} [Category.{v, u} C] (F : C ⥤ Type w) : Prop where
  /-- The category has all finite limits. -/
  hasFiniteLimits : HasFiniteLimits C
  /-- The category has all finite colimits. -/
  hasFiniteColimits : HasFiniteColimits C
  /-- Every object is a finite coproduct of connected objects. -/
  exists_finite_coproduct_connected (X : C) :
    ∃ (ι : Type) (A : ι → C) (f : (i : ι) → A i ⟶ X) (_ : IsColimit (Cofan.mk X f)),
      Finite ι ∧ (∀ i, PreGaloisCategory.IsConnected (A i))
  /-- Every set in the image of the fibre functor is finite. -/
  finite_obj (X : C) : Finite (F.obj X)
  /-- The fibre functor reflects isomorphisms. -/
  reflectsIsomorphisms : F.ReflectsIsomorphisms
  /-- The fibre functor preserves finite limits and finite colimits. -/
  exact : exactFunctor C (Type w) F

attribute [instance] IsGaloisCategory.hasFiniteLimits IsGaloisCategory.hasFiniteColimits
  IsGaloisCategory.finite_obj IsGaloisCategory.reflectsIsomorphisms

/-- The fibre functor of a Galois category preserves finite limits. -/
public instance {C : Type u} [Category.{v, u} C] (F : C ⥤ Type w) [IsGaloisCategory F] :
    PreservesFiniteLimits F := IsGaloisCategory.exact.1

/-- The fibre functor of a Galois category preserves finite colimits. -/
public instance {C : Type u} [Category.{v, u} C] (F : C ⥤ Type w) [IsGaloisCategory F] :
    PreservesFiniteColimits F := IsGaloisCategory.exact.2

end CategoryTheory

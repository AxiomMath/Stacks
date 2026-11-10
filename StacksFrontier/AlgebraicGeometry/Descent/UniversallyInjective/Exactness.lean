module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Exact functors reflecting zero objects

An exact functor between abelian categories which sends no nonzero object to a zero object
reflects monomorphisms and epimorphisms. Faithfully flat extension of scalars is such a
functor.

## Main results

* `CategoryTheory.Functor.reflectsMonomorphisms_of_preservesFiniteLimits_of_reflectsZeroObjects`
  says that left exactness and reflection of zero objects suffice to reflect monomorphisms.
* `CategoryTheory.Functor.reflectsEpimorphisms_of_preservesFiniteColimits_of_reflectsZeroObjects`
  is the dual statement for epimorphisms.
* `ModuleCat.extendScalars_isZero_iff_of_faithfullyFlat` says that faithfully flat extension of
  scalars detects zero modules.
* `ModuleCat.extendScalars_reflectsMonomorphisms_of_faithfullyFlat` and
  `ModuleCat.extendScalars_reflectsEpimorphisms_of_faithfullyFlat` give the faithfully flat
  example.

## Implementation notes

The hypothesis that nonzero objects remain nonzero is expressed as reflection of zero objects.
The two halves of exactness are separated: only preservation of finite limits is needed for
monomorphisms, and only preservation of finite colimits for epimorphisms. Exactness of
extension of scalars is represented by `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
registered below, together with its automatic preservation of finite colimits as a left
adjoint.

## References

* [Stacks Project, Tag 08WK](https://stacks.math.columbia.edu/tag/08WK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

add_to_stacks 08WK "exactness of extension of scalars"
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
add_to_ega "0 20.6.21" "partial" ModuleCat.preservesFiniteLimits_extendScalars_of_flat

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- A left exact functor between abelian categories which reflects zero objects reflects
monomorphisms. -/
@[stacks 08WK "monomorphisms"]
theorem reflectsMonomorphisms_of_preservesFiniteLimits_of_reflectsZeroObjects
    (F : A ⥤ B) [PreservesFiniteLimits F]
    (hF : ∀ X, IsZero (F.obj X) → IsZero X) : F.ReflectsMonomorphisms :=
  ⟨fun f hf => (Preadditive.mono_iff_isZero_kernel f).mpr <| hF _ <|
    ((Preadditive.mono_iff_isZero_kernel (F.map f)).mp hf).of_iso (PreservesKernel.iso F f)⟩

/-- A right exact functor between abelian categories which reflects zero objects reflects
epimorphisms. -/
@[stacks 08WK "epimorphisms"]
theorem reflectsEpimorphisms_of_preservesFiniteColimits_of_reflectsZeroObjects
    (F : A ⥤ B) [PreservesFiniteColimits F]
    (hF : ∀ X, IsZero (F.obj X) → IsZero X) : F.ReflectsEpimorphisms :=
  ⟨fun f hf => (Preadditive.epi_iff_isZero_cokernel f).mpr <| hF _ <|
    ((Preadditive.epi_iff_isZero_cokernel (F.map f)).mp hf).of_iso (PreservesCokernel.iso F f)⟩

end CategoryTheory.Functor

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extension of scalars along a faithfully flat ring homomorphism detects zero modules. -/
@[stacks 08WK "faithfully flat extension of scalars detects zero objects",
  ega "IV 2.2.7" "special case"]
theorem extendScalars_isZero_iff_of_faithfullyFlat (f : R →+* S)
    (hf : f.FaithfullyFlat) (M : ModuleCat.{u} R) :
    IsZero ((ModuleCat.extendScalars f).obj M) ↔ IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  algebraize [f]
  change Subsingleton (TensorProduct R S M) ↔ Subsingleton M
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S

/-- Extension of scalars along a faithfully flat ring homomorphism reflects monomorphisms. -/
@[stacks 08WK "faithfully flat extension of scalars reflects monomorphisms",
  sga "1 IV 2.1" "special case",
  sga "4½ Arcata 1.4.2" "Clause (i), special case"]
theorem extendScalars_reflectsMonomorphisms_of_faithfullyFlat (f : R →+* S)
    (hf : f.FaithfullyFlat) :
    (ModuleCat.extendScalars.{u, u, u} f).ReflectsMonomorphisms := by
  let _ := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf.flat
  exact Functor.reflectsMonomorphisms_of_preservesFiniteLimits_of_reflectsZeroObjects _
    (fun M => (extendScalars_isZero_iff_of_faithfullyFlat f hf M).mp)

/-- Extension of scalars along a faithfully flat ring homomorphism reflects epimorphisms. -/
@[stacks 08WK "faithfully flat extension of scalars reflects epimorphisms",
  sga "1 IV 2.1" "special case"]
theorem extendScalars_reflectsEpimorphisms_of_faithfullyFlat (f : R →+* S)
    (hf : f.FaithfullyFlat) :
    (ModuleCat.extendScalars.{u, u, u} f).ReflectsEpimorphisms :=
  Functor.reflectsEpimorphisms_of_preservesFiniteColimits_of_reflectsZeroObjects _
    (fun M => (extendScalars_isZero_iff_of_faithfullyFlat f hf M).mp)

end ModuleCat

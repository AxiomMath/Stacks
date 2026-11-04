module

public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.TensorExact
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic

/-!
# Tensoring by an invertible module on a scheme is exact

For a scheme `X` and an invertible `𝒪_X`-module `N`, tensoring on the right by `N` is an
autoequivalence of the category of `𝒪_X`-modules, and hence carries short exact sequences to
short exact sequences. In particular, for subobjects `I' ≤ I` of an `𝒪_X`-module, the sequence
`0 → I' ⊗ N → I ⊗ N → (I/I') ⊗ N → 0` is short exact, as used in the proof of [Stacks, Tag 0B5P].

## Main results

* `Stacks.AmpleCohomologicalCriterion.additive_tensorRight`, `preservesZeroMorphisms_tensorRight`
  and `isEquivalence_tensorRight`: tensoring on the right by an `𝒪_X`-module is additive and
  preserves zero morphisms, and it is an equivalence when the module is invertible.
* `Stacks.AmpleCohomologicalCriterion.tensorRightFunctor_obj`:
  `((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj N).obj M` is
  `((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).obj N`, by `rfl`.
* `Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight`: **tensoring a short exact
  sequence of `𝒪_X`-modules by an invertible module is short exact.**
* `Stacks.AmpleCohomologicalCriterion.subobjectShortComplex` and
  `Stacks.AmpleCohomologicalCriterion.shortExact_subobjectShortComplex`: for subobjects `I' ≤ I` of
  any `𝒪_X`-module, the short exact sequence `0 → I' → I → I/I' → 0`.
* `Stacks.AmpleCohomologicalCriterion.shortExact_map_subobjectShortComplex`: the short exact
  sequence `0 → I' ⊗ N → I ⊗ N → (I/I') ⊗ N → 0` for `N` invertible.

## Implementation notes

The category of `𝒪_X`-modules is written as
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, _⟩)`, with the sheaf
condition `Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X`; this is the category the
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` acts on.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe u

namespace Stacks.AmpleCohomologicalCriterion

/-- Tensoring on the right by a fixed `𝒪_X`-module on a scheme is additive. -/
instance additive_tensorRight (X : Scheme.{u}) (N : X.Modules) :
    Functor.Additive
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩))
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩).flip.obj N) :=
  Stacks.ProjTwistFunctor.additive_tensorRightFunctor _ _ N

/-- Tensoring on the right by a fixed `𝒪_X`-module preserves zero morphisms. -/
instance preservesZeroMorphisms_tensorRight (X : Scheme.{u}) (N : X.Modules) :
    Functor.PreservesZeroMorphisms
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩))
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩).flip.obj N) :=
  inferInstance

/-- **Tensoring on the right by an invertible `𝒪_X`-module is an autoequivalence of
`X.Modules`.** -/
instance isEquivalence_tensorRight (X : Scheme.{u}) (N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X N] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (isSheaf_structureRingPresheaf X)⟩).flip.obj N).IsEquivalence :=
  Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X N

/-- The tensor product sheaf of [Stacks, Tag 05NA] is the value of the tensor functor. -/
theorem tensorRightFunctor_obj (X : Scheme.{u}) (M N : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (isSheaf_structureRingPresheaf X)⟩).flip.obj N).obj M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩).obj M).obj N :=
  rfl

/-- **Tensoring a short exact sequence of `𝒪_X`-modules by an invertible module is short
exact.** -/
theorem shortExact_map_tensorRight (X : Scheme.{u}) (N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X N]
    {S : ShortComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩))} (hS : S.ShortExact) :
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (isSheaf_structureRingPresheaf X)⟩).flip.obj N)).ShortExact :=
  Stacks.ProjTwistFunctor.shortExact_map_tensorRightFunctor X.presheaf
    (isSheaf_structureRingPresheaf X) N hS

section Subobject

variable {X : Scheme.{u}}
  {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
      (isSheaf_structureRingPresheaf X)⟩)}

/-- **The short exact sequence of a pair of nested subobjects**, `0 → I' → I → I/I' → 0`. The
quotient is the cokernel of the inclusion `CategoryTheory.Subobject.ofLE`. -/
noncomputable abbrev subobjectShortComplex (I' I : Subobject M) (h : I' ≤ I) :
    ShortComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩)) :=
  ShortComplex.mk (Subobject.ofLE I' I h) (cokernel.π (Subobject.ofLE I' I h))
    (cokernel.condition _)

/-- `Stacks.AmpleCohomologicalCriterion.subobjectShortComplex` is short exact. -/
theorem shortExact_subobjectShortComplex (I' I : Subobject M) (h : I' ≤ I) :
    (subobjectShortComplex I' I h).ShortExact :=
  have : Mono (Subobject.ofLE I' I h) := mono_of_mono_fac (Subobject.ofLE_arrow h)
  { exact := ShortComplex.exact_cokernel _ }

/-- For subobjects `I' ≤ I` of an `𝒪_X`-module and an invertible `𝒪_X`-module `N`, the
sequence `0 → I' ⊗ N → I ⊗ N → (I/I') ⊗ N → 0` is short exact. -/
theorem shortExact_map_subobjectShortComplex (I' I : Subobject M) (h : I' ≤ I) (N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X N] :
    ((subobjectShortComplex I' I h).map
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (isSheaf_structureRingPresheaf X)⟩).flip.obj N)).ShortExact :=
  shortExact_map_tensorRight X N (shortExact_subobjectShortComplex I' I h)

end Subobject

end Stacks.AmpleCohomologicalCriterion

end

module

public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence

/-!
# Global sections across a short exact sequence whose first term is acyclic

Let `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact sequence of `𝒪_X`-modules on a scheme and let `U`
be an open. The long exact cohomology sequence of [Stacks, Tag 010Q] — available in this
repository as `Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived` — says that
`Γ(U, ℱ₂) → Γ(U, ℱ₃)` is

* injective as soon as `Γ(U, ℱ₁) = 0`, and
* surjective as soon as `H¹(U, ℱ₁) = 0`.

The surjectivity half is `Stacks.SerreAffinenessCriterion.epi_secF_map_g_of_isZero_hgroup_one`.
This file adds the injectivity half and packages the two as a bijection, which is the form the
Enriques–Severi–Zariski connectedness argument of [Stacks, Tag 0FD9] consumes: there `ℱ₁` is a
very negative twist of an ample invertible module, whose `H⁰` and `H¹` both vanish, `ℱ₂` is
`𝒪_X` and `ℱ₃` is the direct image of the structure sheaf of the zero scheme, so the bijection
says that the zero scheme has the same ring of global functions as `X`.

## Main results

* `Stacks.AmpleSectionConnected.mono_secF_map_g_of_isZero_secF`: injectivity, as a
  monomorphism.
* `Stacks.AmpleSectionConnected.isZero_secF_of_isZero_hgroup_zero`: `H⁰(U, -) = 0` is
  `Γ(U, -) = 0`.
* `Stacks.AmpleSectionConnected.bijective_secF_map_g_of_isZero`: the two halves together, read
  on elements.

## Implementation notes

Both halves are read off the same δ-functor
`Stacks.SerreAffinenessCriterion.cohomologyDeltaFunctor`, whose degree-zero part is `R⁰Γ(U, -)`
rather than `Γ(U, -)`; the comparison is the `isoZero` field of
`Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor`, and transporting a monomorphism across it
is the only bookkeeping in the proof. In positive degrees no transport is needed, which is why the
surjectivity half can be stated directly about `Hgroup _ _ 1`.

`[HasDerivedCategory _]` is a local instance and appears in no statement, as in the file this
one builds on: `Hgroup` and `secF` mention no derived category, so the statements do not depend
on the model.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.CohomologyVanishing
open Stacks.SerreAffinenessCriterion

universe u

namespace Stacks.AmpleSectionConnected

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (U : X.Opens)
  {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}

/-- **`Γ(U, -)` is injective on the middle term of a short exact sequence whose first term has
no sections over `U`.** This is exactness of `Γ(U, ℱ₁) → Γ(U, ℱ₂) → Γ(U, ℱ₃)` in the long exact
cohomology sequence: the first map is zero because its source is, so the second is a
monomorphism.

No hypothesis on `X`, on `U`, or on the quasi-coherence of the sheaves. -/
theorem mono_secF_map_g_of_isZero_secF (hS : S.ShortExact)
    (h : IsZero ((secF X.ringCatSheaf U).obj S.X₁)) :
    Mono ((secF X.ringCatSheaf U).map S.g) := by
  have hD := Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived X.ringCatSheaf U
  have h0 : IsZero (((cohomologyDeltaFunctor X U).functor 0).obj S.X₁) :=
    h.of_iso (hD.isoZero.app S.X₁)
  have hadd : ((cohomologyDeltaFunctor X U).functor 0).Additive :=
    CategoryTheory.DeltaFunctor.additive (cohomologyDeltaFunctor X U) 0
  have hpz : ((cohomologyDeltaFunctor X U).functor 0).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hf : ((cohomologyDeltaFunctor X U).functor 0).map S.f = 0 := h0.eq_of_src _ _
  have hmono : Mono (((cohomologyDeltaFunctor X U).functor 0).map S.g) :=
    (ShortComplex.exact_iff_mono (S.map ((cohomologyDeltaFunctor X U).functor 0)) hf).1
      ((cohomologyDeltaFunctor X U).exact_map hS 0)
  have hnat := hD.isoZero.hom.naturality S.g
  have : IsIso (hD.isoZero.hom.app S.X₂) :=
    inferInstanceAs (IsIso (hD.isoZero.app S.X₂).hom)
  have : IsIso (hD.isoZero.hom.app S.X₃) :=
    inferInstanceAs (IsIso (hD.isoZero.app S.X₃).hom)
  have key : (secF X.ringCatSheaf U).map S.g =
      inv (hD.isoZero.hom.app S.X₂) ≫
        ((cohomologyDeltaFunctor X U).functor 0).map S.g ≫ hD.isoZero.hom.app S.X₃ := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  rw [key]
  have := hmono
  infer_instance

/-- **`H⁰(U, M) = 0` is `Γ(U, M) = 0`.** The degree-zero part of the right derived δ-functor of
`Γ(U, -)` is `Γ(U, -)` itself, by the `isoZero` field of
`Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor`; this is that comparison read on
vanishing, for a vanishing theorem stated about `Hgroup _ _ 0` rather than about `secF`. -/
theorem isZero_secF_of_isZero_hgroup_zero (M : SheafOfModules.{u} X.ringCatSheaf)
    (h : IsZero (Hgroup X.ringCatSheaf U 0 M)) :
    IsZero ((secF X.ringCatSheaf U).obj M) :=
  h.of_iso ((Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived
    X.ringCatSheaf U).isoZero.app M).symm

/-- **A short exact sequence whose first term has vanishing `Γ(U, -)` and `H¹(U, -)` identifies
the sections of its other two terms.** The map is the one induced by the sequence, read on
elements.

This is the two exactness statements of the long exact cohomology sequence adjacent to
`Γ(U, ℱ₂) → Γ(U, ℱ₃)`, with both neighbours killed. -/
theorem bijective_secF_map_g_of_isZero (hS : S.ShortExact)
    (h0 : IsZero ((secF X.ringCatSheaf U).obj S.X₁))
    (h1 : IsZero (Hgroup X.ringCatSheaf U 1 S.X₁)) :
    Function.Bijective ((secF X.ringCatSheaf U).map S.g).hom :=
  ⟨(AddCommGrpCat.mono_iff_injective _).1 (mono_secF_map_g_of_isZero_secF X U hS h0),
    (AddCommGrpCat.epi_iff_surjective _).1
      (epi_secF_map_g_of_isZero_hgroup_one X U hS h1)⟩

end Stacks.AmpleSectionConnected

end

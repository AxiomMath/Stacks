module

public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported

/-!
# Injective modules are acyclic for sections with support

Let `A` be a commutative ring and `T ⊆ Spec(A)` a subset. For an injective `A`-module `E` the
complex `E[0]` is K-injective, so the local cohomology of `E` with support in `T` is computed by
the complex of `T`-supported sections of `E[0]`, which is `Γ_T(E)` in degree zero and zero
elsewhere:

`H^0_T(E) = Γ_T(E)` and `H^i_T(E) = 0` for `i ≠ 0`.

This is the acyclicity half of the input to [Stacks, Remark 0EF4]'s assertion that a `T`-torsion
module `N` satisfies `H^0_T(N) = N` and `H^i_T(N) = 0` for `i > 0`; see the implementation notes
for what is still missing for the latter.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_injective` — **`H^i_T(E) = 0` for
  `i ≠ 0` and `E` injective.**
* `Stacks.LocalCohomology.nonempty_localCohomologyWithSupportIn_zero_iso_of_injective` —
  **`H^0_T(E) ≅ Γ_T(E)` for `E` injective.**

## Implementation notes

**What is not proved here, and exactly what is missing.** The acyclicity of a `T`-torsion module
`N` — `H^i_T(N) = 0` for `i > 0`, which is what the Faltings induction of [Stacks, Tag 0AW8] uses
at the step "by construction of `RΓ_T` we find that `H^i_T(N) = 0` for `i > 0`" — reduces, with
the long exact sequence of
`StacksFrontier/RingTheory/LocalCohomology/DepthVanishing/Triangulated.lean` and
`Stacks.LocalCohomology.exists_injective_supported_envelope` of
`StacksFrontier/Algebra/Module/Matlis.lean`, to a single missing statement:

> the canonical comparison `γ_M : Γ_T(M) ⟶ H^0_T(M)`, natural in the `A`-module `M`, is an
> isomorphism.

`γ` is obtained from `Stacks.LocalCohomology.derivedSectionsWithSupportInUnit` whiskered with the
single-complex functor and composed with `HomologicalComplex.singleMapHomologicalComplex` and
`DerivedCategory.singleFunctorCompHomologyFunctorIso`; this file proves that `γ_E` is invertible
for `E` injective, which is the base case. Given `γ` as a natural transformation, the rest is a
two-step diagram chase using only results already in the library:

1. `γ` is a monomorphism. Embed `M` in an injective `E` with quotient `C`. The map
   `H^0_T(M) ⟶ H^0_T(E)` is a monomorphism, because the connecting map into it comes from
   `H^{-1}_T(C) = 0`
   (`Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_neg` and
   `Stacks.LocalCohomology.mono_localCohomologyMap_f_iff`). Naturality of `γ` and invertibility of
   `γ_E` then force `γ_M` to be a monomorphism.
2. `γ` is an epimorphism. With the same notation, exactness of
   `H^0_T(M) → H^0_T(E) → H^0_T(C)` identifies `H^0_T(M)` with the kernel of
   `H^0_T(E) → H^0_T(C)`; since `γ_C` is a monomorphism by step 1, that kernel is the kernel of
   `Γ_T(E) → Γ_T(C)`, which is `Γ_T(M)` because a section is `T`-supported as a condition on its
   own annihilator (`Stacks.LocalCohomology.mem_sectionsWithSupportIn_iff`).

Acyclicity then follows: for `N` supported in `T`, take `N ↪ J` with `J` injective and supported
in `T`, put `C = J/N`, and note that `Γ_T(J) ⟶ Γ_T(C)` is `J ⟶ C` because both are supported in
`T`, hence an epimorphism; by `γ` and
`Stacks.LocalCohomology.epi_localCohomologyMap_g_iff` the connecting map
`H^0_T(C) ⟶ H^1_T(N)` vanishes, so `H^1_T(N) = 0`, and the degrees `i ≥ 2` follow by induction
from `Stacks.LocalCohomology.isZero_localCohomology_X₁` since `C` is again supported in `T`.

No Stacks attribute is placed. Remark 0EF4's covering set in this library is carried by the
declarations tagged `@[stacks 0EF4]` in
`StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport` and
`StacksFrontier.RingTheory.LocalCohomology.BoundedComparison`, and the statements here are not
among them.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The single complex of an injective module is K-injective: it is concentrated in degree zero and
degreewise injective, the terms away from degree zero being zero objects. -/
lemma isKInjective_singleFunctor_obj_of_injective (E : ModuleCat.{max u v} A)
    [CategoryTheory.Injective E] :
    ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj E).IsKInjective := by
  have : ∀ n : ℤ, CategoryTheory.Injective
      (((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj E).X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact CategoryTheory.Injective.of_iso
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).symm) inferInstance
    · exact CategoryTheory.Injective.of_iso
        ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 E n hn).isoZero).symm
        inferInstance
  exact CochainComplex.isKInjective_of_injective _ 0

/-- Local cohomology of an injective module is the cohomology of the single complex of its
`T`-supported sections. -/
private lemma nonempty_localCohomology_iso_single_homology_of_injective
    (T : Set (PrimeSpectrum A)) (E : ModuleCat.{max u v} A) [CategoryTheory.Injective E] (i : ℤ) :
    Nonempty (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj E) i ≅
      ((HomologicalComplex.single (ModuleCat.{max u v} A) (ComplexShape.up ℤ) 0).obj
        ((sectionsWithSupportInFunctor.{u, v} A T).obj E)).homology i) := by
  have := isKInjective_singleFunctor_obj_of_injective.{u, v} E
  let L := (CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj E
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ)).obj L) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj E :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} A) 0).app E).symm
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_homology_of_isKInjective.{u, v} T _ i L e
  exact ⟨iso ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A)
    (ComplexShape.up ℤ) i).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ) 0).app E)⟩

/-- **Injective modules are acyclic for sections with support in `T`.** For `E` an injective
`A`-module, `H^i_T(E) = 0` whenever `i ≠ 0`. -/
theorem isZero_localCohomologyWithSupportIn_of_injective (T : Set (PrimeSpectrum A))
    (E : ModuleCat.{max u v} A) [CategoryTheory.Injective E] (i : ℤ) (hi : i ≠ 0) :
    IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj E) i) := by
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_single_homology_of_injective.{u, v} T E i
  exact IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
    ((sectionsWithSupportInFunctor.{u, v} A T).obj E) i hi) iso

/-- **`H^0_T(E) = Γ_T(E)` for `E` an injective `A`-module.** -/
theorem nonempty_localCohomologyWithSupportIn_zero_iso_of_injective (T : Set (PrimeSpectrum A))
    (E : ModuleCat.{max u v} A) [CategoryTheory.Injective E] :
    Nonempty (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj E) 0 ≅
      (sectionsWithSupportInFunctor.{u, v} A T).obj E) := by
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_single_homology_of_injective.{u, v} T E 0
  exact ⟨iso ≪≫ HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
    ((sectionsWithSupportInFunctor.{u, v} A T).obj E)⟩

end Stacks.LocalCohomology

end

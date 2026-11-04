module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SchemeOpenSectionsDerived
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.OrderedCechModuleComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a module on the complement of a zero locus, as a module over the ring

Let `R` be a commutative ring, let `I ⊆ R` be an ideal, let `X = Spec R`, let `Z = V(I)` and let
`U = X ∖ Z`. For a sheaf of modules `F` on the open subscheme `U`, the cohomology `H^p(U, F)` is a
module over `Γ(U, 𝒪_U)`, and hence an `R`-module through `R ≅ Γ(X, 𝒪_X) → Γ(U, 𝒪_U)`. If `I` is
finitely generated and `F ≅ M̃|_U` for an `R`-module `M`, then `H^p(U, F) ≅ H^{p+1}_Z(M)` as
`R`-modules for every `p ≥ 1`. This is the second half of clause (2) of [Stacks, Tag 0DWR].

## Main definitions

* `Stacks.LocalCohomology.complementSheafCohomology` — `H^p(U, -)` on sheaves of modules on the
  open subscheme `U`, valued in `R`-modules.
* `Stacks.LocalCohomology.complementSheafCohomologyTildeIso` — on `M̃|_U` it is
  `Stacks.LocalCohomologySequence.complementCohomologyBase`, the cohomology over `U` of `M̃` on
  the ambient `X`.

## Main results

* `Stacks.LocalCohomology.nonempty_complementSheafCohomology_iso_localCohomologyModule` —
  **[Stacks, Tag 0DWR] (2), the isomorphisms above degree zero**, `R`-linearly, for every `F`
  with `F ≅ M̃|_U`.

## Implementation notes

The cohomology of `F` is the right derived functor of global sections on the open subscheme `U`,
with its scalars restricted along `U.ι.appTop` and then along `R ≅ Γ(X, 𝒪_X)`. On `M̃|_U` this
agrees with `complementCohomologyBase`, the derived functor of sections over `U` of sheaves on
`X`, by [Stacks, Tag 01E1] (2) in the form
`Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso`; the latter is where the
`R`-linear comparison with local cohomology,
`Stacks.LocalCohomologySequence.nonempty_complementCohomologyBase_iso_localCohomologyModule`, is
proved. For an arbitrary `F` the isomorphism is transported along `F ≅ M̃|_U` by functoriality.

The open `U` is `Stacks.LocalCohomology.complementZeroLocus R I`, the spelling on which the
low-degree sequence `Stacks.LocalCohomology.exact_lowDegreeSequence` and the extension
`Stacks.LocalCohomology.exists_module_iso_restrict_tilde` are stated, so that the three clauses
of the tag speak about the same `F`.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.SchemeOpenSections
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomology

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- **`H^p(U, -)` on `U = Spec R ∖ V(I)`, as `R`-modules.** The `p`-th right derived functor of
global sections on the open subscheme `U`, with the scalars restricted from `Γ(U, 𝒪_U)` to
`Γ(Spec R, 𝒪)` along `U.ι.appTop` and then to `R` along `R ≅ Γ(Spec R, 𝒪)`. -/
abbrev complementSheafCohomology (p : ℕ) :
    (complementZeroLocus R I : Scheme).Modules ⥤ ModuleCat.{u} R :=
  (Stacks.Cohomology.AffineBase.moduleGlobalSections
      (complementZeroLocus R I : Scheme)).rightDerived p ⋙
    ModuleCat.restrictScalars (complementZeroLocus R I).ι.appTop.hom ⋙
      globalToBase (CommRingCat.of R)

/-- **On `M̃|_U`, `H^p(U, -)` is the cohomology over `U` of `M̃` on `Spec R`.** The cohomology of
the restriction `M̃|_U` on the open subscheme `U`, as an `R`-module, is
`Stacks.LocalCohomologySequence.complementCohomologyBase`, the derived functor of sections over
`U` of sheaves of modules on `Spec R` evaluated at `M̃`. This is [Stacks, Tag 01E1] (2), as
`Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso`, read over `R`. -/
def complementSheafCohomologyTildeIso (M : ModuleCat.{u} R) (p : ℕ) :
    (complementSheafCohomology R I p).obj (complementTilde R I M) ≅
      Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of R) I M p :=
  (globalToBase (CommRingCat.of R)).mapIso
    ((derivedSectionsOnOpenIso (Spec (CommRingCat.of R)) (complementZeroLocus R I) p).app
      (tilde (R := CommRingCat.of R) M)).symm

/-- **[Stacks, Tag 0DWR] (2), the isomorphisms above degree zero.** Let `R` be a ring and let
`I ⊆ R` be a finitely generated ideal. Set `X = Spec R`, `Z = V(I)` and `U = X ∖ Z`. Let `F` be
an `𝒪_U`-module and let `M` be an `R`-module with `F ≅ M̃|_U`. Then
`H^p(U, F) ≅ H^{p+1}_Z(M)` as `R`-modules for every `p ≥ 1`.

The isomorphism is transported along `F ≅ M̃|_U`, then
`complementSheafCohomologyTildeIso` passes to the cohomology over `U` of `M̃` on `X`, where
`Stacks.LocalCohomologySequence.nonempty_complementCohomologyBase_iso_localCohomologyModule` is
the comparison with local cohomology. The source only asserts that the two modules are
isomorphic, so the conclusion is nonemptiness of the type of isomorphisms. -/
@[stacks 0DWR "higher_cohomology_comparison"]
theorem nonempty_complementSheafCohomology_iso_localCohomologyModule (hI : I.FG)
    (M : ModuleCat.{u} R) (F : (complementZeroLocus R I : Scheme).Modules)
    (e : F ≅ complementTilde R I M) (p : ℕ) (hp : 1 ≤ p) :
    Nonempty ((complementSheafCohomology R I p).obj F ≅
      localCohomologyModule R I hI M ((p + 1 : ℕ) : ℤ)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨g⟩ :=
    Stacks.LocalCohomologySequence.nonempty_complementCohomologyBase_iso_localCohomologyModule
      (A := CommRingCat.of R) I hI M q
  have hdeg : ((q + 1 + 1 : ℕ) : ℤ) = ((q + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [hdeg]
  exact ⟨(complementSheafCohomology R I (q + 1)).mapIso e ≪≫
    complementSheafCohomologyTildeIso R I M (q + 1) ≪≫ g⟩

end Stacks.LocalCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.InjectiveAcyclicity
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyTildeFunctor
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksCore.Tactic.StacksAttribute

/-!
# Local cohomology of a module along a principal vanishing locus

Let `A` be a Noetherian ring, let `f : A`, let `X = Spec A` and let `Z = V(f)`.  For an
`A`-module `M` the cohomology of `X` with support in `Z` of the sheaf `M̃`, read as an
`A`-module, is the algebraic local cohomology `H^n_Z(M)` of `M` in every degree, and the
cohomology sequence of the vanishing locus becomes the exact sequence

`0 ⟶ H⁰_Z(M) ⟶ H⁰(X, M̃) ⟶ H⁰(X ∖ Z, M̃) ⟶ H¹_Z(M) ⟶ 0`

together with isomorphisms `H^p(X ∖ Z, M̃) ≅ H^{p+1}_Z(M)` for `p ≥ 1`.

## Main results

* `Stacks.LocalCohomologySequence.localCohomologySpanSingleton`: `H^n_{V(f)}(-)`, the `n`-th
  right derived functor of the algebraic sections with support in `V(f)`.
* `Stacks.LocalCohomologySequence.cohomologyWithSupportTildeSpanSingletonIso`: in every degree,
  the cohomology with support in `V(f)` of `M̃` is the algebraic local cohomology of `M`.
* `Stacks.LocalCohomologySequence.exact_localCohomology_sequence_span_singleton`: the four-term
  exact sequence and the isomorphisms in degrees `≥ 1`, with the algebraic local cohomology in
  the support slots.

## Implementation notes

The identification of the two cohomologies with support in positive degrees is the degreewise
comparison `Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso` of the right derived
functors of a composite with those of its second factor, applied to the composite
`M ↦ Γ_Z(X, M̃)`.  Its two inputs are both available for a principal vanishing locus over a
Noetherian ring: the associated sheaf of an injective module has vanishing cohomology with
support in `V(f)` in positive degrees
(`Stacks.LocalCohomologySequence.isZero_cohomologyWithSupport_tilde_span_singleton`), which is
right acyclicity for `Γ_Z(X, -)` because that functor is left exact; and `M ↦ M̃` is exact, so
every module is right acyclic for it ([Stacks, Tag 05T8] for the class of all objects).
Composing with the comparison of `M ↦ Γ_Z(X, M̃)` with the algebraic sections with
support, `Stacks.LocalCohomologyTilde.rightDerivedSectionsWithSupportTildeIso`, gives the
identification.

The hypothesis that the ideal is principal is not removable by this argument: it is what makes
the open complement affine, hence what makes the cohomology of `M̃` on the complement vanish in
positive degrees.  For an ideal with more generators the complement is covered by `r` basic
opens and the comparison needs the extended alternating Čech complex instead.

The comparison is pointwise in `M` rather than a natural isomorphism of functors, because the
identification of `RF(M[0])` with `F(M)[0]` for `F : M ↦ M̃` is the inverse of a component of
the unit of `RF`.  The exact sequence is correspondingly stated at a single module, with the
connecting map existentially quantified as in
`Stacks.LocalCohomologySequence.exact_cohomologyWithSupport_sequence`.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-- **Sections with support in a closed subset are left exact.**  Global sections vanishing on
the open complement of a closed subset `Z` of a ringed space form the kernel of restriction to
that complement, and both functors in that transformation are left exact. -/
@[sga "2 VI 1.5" "special case", sga "4 V 6.3" "special case"]
instance preservesFiniteLimits_sectionsWithSupport (X : RingedSpace.{u, u}) (Z : Set X)
    (hZ : IsClosed Z) : PreservesFiniteLimits (sectionsWithSupport X Z hZ) := by
  change PreservesFiniteLimits (kernel (restrictionToComplement X Z hZ))
  have : (kernel (restrictionToComplement X Z hZ)).Additive :=
    sectionsWithSupport_additive X Z hZ
  exact Stacks.Cohomology.LerayDegreewise.preservesFiniteLimits_kernel _

/-! ### The two acyclicity inputs -/

/-- **Every module is right acyclic for the associated-sheaf functor.**  The functor `M ↦ M̃` is
exact, so the class of all `A`-modules is adapted to it in the sense of [Stacks, Tag 05T8]. -/
theorem rightAcyclic_tildeSheafFunctor (M : ModuleCat.{u} A) :
    (tildeSheafFunctor A).rightAcyclic M :=
  Functor.le_rightAcyclic _ ⊤ (fun N => ⟨N, trivial, 𝟙 N, inferInstance⟩)
    (fun _ hS _ _ => ⟨trivial, hS.map_of_exact _⟩) M trivial

/-- **The associated sheaf of an injective module is right acyclic for sections with support in
a principal vanishing locus.**  For a Noetherian ring `A`, an element `f : A` and an injective
`A`-module `I`, the cohomology with support in `V(f)` of `Ĩ` vanishes in positive degrees, and
sections with support are left exact, so `Ĩ` computes the derived functor. -/
theorem rightAcyclic_tilde_of_injective [IsNoetherianRing A] (f : A) (I : ModuleCat.{u} A)
    [CategoryTheory.Injective I] :
    (sectionsWithSupport (Spec A).toRingedSpace (zeroLocusSubset (Ideal.span {f}))
      (isClosed_zeroLocusSubset _)).rightAcyclic ((tildeSheafFunctor A).obj I) := by
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  exact isZero_cohomologyWithSupport_tilde_span_singleton f I p hp

/-! ### The degreewise identification -/

/-- `H^n_{V(f)}(-)`, the `n`-th right derived functor of the algebraic sections of an
`A`-module with support in the vanishing locus of `(f)`. -/
abbrev localCohomologySpanSingleton (A : CommRingCat.{u}) (f : A) (n : ℕ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  (Stacks.LocalCohomology.sectionsWithSupportInFunctor.{u, u} A
    (PrimeSpectrum.zeroLocus (Ideal.span {f} : Set A))).rightDerived n

/-- **Stacks 0A6T degreewise, for a module and a principal ideal.**  Let `A` be a Noetherian
ring, `f : A`, `X = Spec A` and `Z = V(f)`.  For an `A`-module `M` the cohomology of `X` with
support in `Z` of the sheaf `M̃`, read as an `A`-module, is the algebraic local cohomology
`H^n_Z(M)` of `M`, in every degree `n`. -/
@[stacks 0A6T "degreewise, for a module and a principal ideal",
  ega "III 1.1.10" "principal ideal, Noeth."]
def cohomologyWithSupportTildeSpanSingletonIso [IsNoetherianRing A] (f : A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    (globalToBase A).obj ((cohomologyWithSupport (Ideal.span {f}) n).obj (tildeSheaf M)) ≅
      (localCohomologySpanSingleton A f n).obj M :=
  (globalToBase A).mapIso
      (Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso (tildeSheafFunctor A)
        (sectionsWithSupport (Spec A).toRingedSpace
          (zeroLocusSubset (Ideal.span {f})) (isClosed_zeroLocusSubset _))
        (fun I hI => have := hI; rightAcyclic_tilde_of_injective f I)
        M (rightAcyclic_tildeSheafFunctor M) n).symm ≪≫
    (rightDerivedSectionsWithSupportTildeIso
      (PrimeSpectrum.zeroLocus (Ideal.span {f} : Set A))
      (isClosed_zeroLocusSubset (Ideal.span {f})) n).app M

/-! ### The cohomology sequence with algebraic local cohomology -/

/-- The inclusion `H⁰_{V(f)}(M) ⟶ H⁰(Spec A, M̃)` forgetting the support condition, read as a
map of `A`-modules through the degreewise identification in degree zero. -/
def localCohomologyToGlobalSections [IsNoetherianRing A] (f : A) (M : ModuleCat.{u} A) :
    (localCohomologySpanSingleton A f 0).obj M ⟶
      (globalToBase A).obj ((ambientCohomology A 0).obj (tildeSheaf M)) :=
  (cohomologyWithSupportTildeSpanSingletonIso f M 0).inv ≫
    (globalToBase A).map ((supportInclusion (Ideal.span {f}) 0).app (tildeSheaf M))

/-- **Stacks Project, Tag 0BK0 (2) for a principal ideal.**  Let `A` be a Noetherian ring, let
`f : A` and write `X = Spec A`, `Z = V(f)` and `U = X ∖ Z`.  For an `A`-module `M` there is a
connecting map `H⁰(U, M̃) ⟶ H¹_Z(M)` for which the sequence

`0 ⟶ H⁰_Z(M) ⟶ H⁰(X, M̃) ⟶ H⁰(U, M̃) ⟶ H¹_Z(M) ⟶ 0`

is exact, and `H^p(U, M̃) ≅ H^{p+1}_Z(M)` for every `p ≥ 1`, with `H^i_Z(M)` the algebraic
local cohomology of `M`. -/
@[stacks 0BK0 "(2), principal ideal"]
theorem exact_localCohomology_sequence_span_singleton [IsNoetherianRing A] (f : A)
    (M : ModuleCat.{u} A) :
    ∃ (d : (globalToBase A).obj
          ((complementCohomology (Ideal.span {f}) 0).obj (tildeSheaf M)) ⟶
        (localCohomologySpanSingleton A f 1).obj M)
      (hir : localCohomologyToGlobalSections f M ≫ (globalToBase A).map
        ((complementRestriction (Ideal.span {f}) 0).app (tildeSheaf M)) = 0)
      (hrd : (globalToBase A).map
        ((complementRestriction (Ideal.span {f}) 0).app (tildeSheaf M)) ≫ d = 0),
      Mono (localCohomologyToGlobalSections f M) ∧ (ShortComplex.mk _ _ hir).Exact ∧
        (ShortComplex.mk _ _ hrd).Exact ∧ Epi d ∧
        ∀ p : ℕ, 0 < p → Nonempty ((globalToBase A).obj
          ((complementCohomology (Ideal.span {f}) p).obj (tildeSheaf M)) ≅
            (localCohomologySpanSingleton A f (p + 1)).obj M) := by
  obtain ⟨delta, hmono, hexact, hepi, hiso⟩ :=
    exact_cohomologyWithSupport_sequence (Ideal.span {f}) M
  have hz0 : (supportInclusion (Ideal.span {f}) 0).app (tildeSheaf M) ≫
      (complementRestriction (Ideal.span {f}) 0).app (tildeSheaf M) = 0 :=
    hexact.toIsComplex.zero 0
  have hz1 : (complementRestriction (Ideal.span {f}) 0).app (tildeSheaf M) ≫
      (delta 0).app (tildeSheaf M) = 0 := hexact.toIsComplex.zero 1
  refine ⟨(globalToBase A).map ((delta 0).app (tildeSheaf M)) ≫
    (cohomologyWithSupportTildeSpanSingletonIso f M 1).hom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [localCohomologyToGlobalSections, Category.assoc, ← (globalToBase A).map_comp, hz0,
      (globalToBase A).map_zero, comp_zero]
  · rw [← Category.assoc, ← (globalToBase A).map_comp, hz1, (globalToBase A).map_zero,
      zero_comp]
  · exact mono_comp _ _
  · refine ShortComplex.exact_of_iso ?_ ((hexact.exact' 0 1 2).map (globalToBase A))
    exact ShortComplex.isoMk (cohomologyWithSupportTildeSpanSingletonIso f M 0) (Iso.refl _)
      (Iso.refl _) (by simp [localCohomologyToGlobalSections]) (by rfl)
  · refine ShortComplex.exact_of_iso ?_ ((hexact.exact' 1 2 3).map (globalToBase A))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (cohomologyWithSupportTildeSpanSingletonIso f M 1) (by rfl) (by rfl)
  · exact epi_comp _ _
  · intro p hp
    obtain ⟨e⟩ := nonempty_iso_complementCohomology (Ideal.span {f}) M p hp
    exact ⟨(globalToBase A).mapIso e ≪≫ cohomologyWithSupportTildeSpanSingletonIso f M (p + 1)⟩

end Stacks.LocalCohomologySequence

end

module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.InjectiveLocalization
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologySequence
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering

/-!
# Vanishing of cohomology with support in a principal vanishing locus

Let `A` be a Noetherian ring, let `f : A`, let `X = Spec A` and let `Z = V(f)` be the vanishing
locus of the principal ideal `(f)`, so that the open complement `X ∖ Z` is the basic open `D(f)`
and is itself affine.  For an injective `A`-module `M` the cohomology with support in `Z` of the
sheaf `M̃` vanishes in every positive degree.

## Main results

* `Stacks.LocalCohomologySequence.openComplement_zeroLocusSubset_span_singleton`: the open
  complement of the vanishing locus of `(f)` is the basic open `D(f)`.
* `Stacks.LocalCohomologySequence.isZero_complementCohomology_tilde`: when the open complement
  of the vanishing locus is affine, the positive-degree cohomology of `M̃` on it vanishes.
* `Stacks.LocalCohomologySequence.epi_complementRestriction_zero_tilde_span_singleton`: for an
  injective module over a Noetherian ring, restriction of global sections of `M̃` to `D(f)` is
  surjective on the degree-zero terms of the cohomology sequence.
* `Stacks.LocalCohomologySequence.isZero_cohomologyWithSupport_tilde_span_singleton`: for an
  injective module over a Noetherian ring, `H^n_{V(f)}(Spec A, M̃) = 0` for every `n > 0`.

## Implementation notes

Degree one and the degrees above it come from the two ends of the cohomology sequence of the
vanishing locus, `Stacks.LocalCohomologySequence.exact_cohomologyWithSupport_sequence`.  In
degree one the sequence ends `Γ(X, M̃) ⟶ Γ(D(f), M̃) ⟶ H¹_Z(X, M̃) ⟶ 0`, so the connecting map is
both zero — the map before it being epimorphic — and epimorphic, which forces its target to
vanish.  Surjectivity of the restriction on global sections is
`AlgebraicGeometry.tilde.surjective_presheaf_map_basicOpen_of_injective`; what the sequence
needs is the same statement about the degree-zero *derived* terms, and the passage between the
two is the naturality of `CategoryTheory.Functor.toRightDerivedZero` in the functor
(`ModuleSheafCohomology.toRightDerivedZero_naturality_functor`) together with invertibility of
that transformation at a left exact functor.  In degrees two and above the sequence identifies
`H^{p+1}_Z(X, M̃)` with `H^p(D(f), M̃)`, which vanishes by Serre vanishing on the affine open
`D(f)`; this is the statement of
`Stacks.LocalCohomologySequence.isZero_ambientCohomology_tilde` with the whole space replaced by
a general affine open, and it is obtained the same way, from
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` and
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`.

Sections over the open complement carry the global functions as scalars, so the functor is
module-valued sections over the complement followed by restriction of scalars.  Forgetting the
module structure altogether removes that discrepancy, which is why the comparison with the
abelian-group-valued cohomology functor is taken through
`CategoryTheory.forget₂ ... AddCommGrpCat` in one step rather than through the comparison at the
complement and the restriction of scalars separately.

The hypothesis that `A` is Noetherian is not removable: it is what makes a localization of an
injective module at the powers of one element surjective, hence the restriction on global
sections surjective.  The hypothesis that the ideal is principal is not removable either: for an
ideal with more generators the open complement is not affine and the cohomology of `M̃` on it
does not vanish.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SectionsWithSupport

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-! ### The open complement of a principal vanishing locus -/

/-- The open complement of the vanishing locus of a principal ideal `(f)` is the basic open
`D(f)`. -/
theorem openComplement_zeroLocusSubset_span_singleton (f : A) :
    openComplement (zeroLocusSubset (Ideal.span {f})) (isClosed_zeroLocusSubset _) =
      PrimeSpectrum.basicOpen f := by
  refine Opens.ext ?_
  change (PrimeSpectrum.zeroLocus (Ideal.span {f} : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span]
  exact (PrimeSpectrum.basicOpen_eq_zeroLocus_compl f).symm

/-- The open complement of the vanishing locus of a principal ideal is an affine open. -/
theorem isAffineOpen_openComplement_span_singleton (f : A) :
    IsAffineOpen (X := Spec A)
      (openComplement (zeroLocusSubset (Ideal.span {f})) (isClosed_zeroLocusSubset _)) :=
  openComplement_zeroLocusSubset_span_singleton f ▸ IsAffineOpen.Spec_basicOpen f

/-! ### Serre vanishing on an affine open complement -/

/-- Deriving the sections over the open complement and then forgetting the module structure is
the abelian-group-valued cohomology functor of the open complement. -/
def complementCohomologyForgetIso (I : Ideal A) (n : ℕ) :
    complementCohomology I n ⋙
        forget₂ (GlobalModules (Spec A).toRingedSpace) AddCommGrpCat.{u} ≅
      (SheafOfModules.toSheaf (Spec A).ringCatSheaf ⋙
        (sheafSections (Opens.grothendieckTopology (Spec A).toRingedSpace)
          AddCommGrpCat.{u}).obj
            (op (openComplement (zeroLocusSubset I)
              (isClosed_zeroLocusSubset I)))).rightDerived n :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ (Iso.refl _) n

/-- **Serre vanishing on an affine open complement.**  If the open complement of the vanishing
locus of `I` is affine then the cohomology of `M̃` on it vanishes in positive degrees, as a
module over the global functions. -/
theorem isZero_complementCohomology_tilde (I : Ideal A)
    (hU : IsAffineOpen (X := Spec A)
      (openComplement (zeroLocusSubset I) (isClosed_zeroLocusSubset I)))
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 0 < n) :
    IsZero ((complementCohomology I n).obj (tildeSheaf M)) := by
  refine isZero_of_faithful
    (forget₂ (GlobalModules (Spec A).toRingedSpace) AddCommGrpCat.{u}) ?_
  refine IsZero.of_iso ?_ ((complementCohomologyForgetIso I n).app (tildeSheaf M))
  exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen (Spec A)
    (tilde M : (Spec A).Modules) _ hU n hn

/-! ### Surjectivity of the restriction to a principal open -/

/-- Sections over the open complement of a closed subset form a left exact functor. -/
instance preservesFiniteLimits_sectionsOnComplement (X : RingedSpace.{u, u}) (Z : Set X)
    (hZ : IsClosed Z) : PreservesFiniteLimits (sectionsOnComplement X Z hZ) := by
  have := Stacks.Cohomology.CechAcyclic.preservesFiniteLimits_restrictScalars
    (((structureSheafRing X).obj.map
      (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op).hom)
  infer_instance

/-- For an injective module over a Noetherian ring, restriction of the global sections of `M̃` to
an open which is a basic open is surjective. -/
theorem surjective_presheaf_map_of_eq_basicOpen [IsNoetherianRing A] (M : ModuleCat.{u} A)
    [CategoryTheory.Injective M] (f : A) (V : (Spec A).Opens)
    (hV : V = PrimeSpectrum.basicOpen f) :
    Function.Surjective ((tilde M).val.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom := by
  subst hV
  exact AlgebraicGeometry.tilde.surjective_presheaf_map_basicOpen_of_injective M f

/-- For an injective module over a Noetherian ring, restriction of the global sections of `M̃` to
the complement of the vanishing locus of `(f)` is an epimorphism. -/
theorem epi_restrictionToComplement_tilde_span_singleton [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [CategoryTheory.Injective M] (f : A) :
    Epi ((restrictionToComplement (Spec A).toRingedSpace
      (zeroLocusSubset (Ideal.span {f})) (isClosed_zeroLocusSubset _)).app (tildeSheaf M)) := by
  rw [ModuleCat.epi_iff_surjective]
  exact surjective_presheaf_map_of_eq_basicOpen M f _
    (openComplement_zeroLocusSubset_span_singleton f)

/-- The degree-zero restriction map of the cohomology sequence of `V(f)` is an epimorphism at
`M̃` for an injective module `M` over a Noetherian ring. -/
theorem epi_complementRestriction_zero_tilde_span_singleton [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [CategoryTheory.Injective M] (f : A) :
    Epi ((complementRestriction (Ideal.span {f}) 0).app (tildeSheaf M)) := by
  have hsq := NatTrans.congr_app
    (ModuleSheafCohomology.toRightDerivedZero_naturality_functor
      (restrictionToComplement (Spec A).toRingedSpace
        (zeroLocusSubset (Ideal.span {f})) (isClosed_zeroLocusSubset _))) (tildeSheaf M)
  simp only [NatTrans.comp_app] at hsq
  have := epi_restrictionToComplement_tilde_span_singleton M f
  exact epi_of_epi_fac hsq.symm

/-! ### The vanishing -/

/-- In degree one the cohomology with support in `V(f)` of `M̃` vanishes for an injective module
`M` over a Noetherian ring: the connecting map onto it is an epimorphism, and it is zero because
the map before it is an epimorphism. -/
theorem isZero_cohomologyWithSupport_one_tilde_span_singleton [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [CategoryTheory.Injective M] (f : A) :
    IsZero ((cohomologyWithSupport (Ideal.span {f}) 1).obj (tildeSheaf M)) := by
  obtain ⟨delta, -, hexact, hepi, -⟩ :=
    exact_cohomologyWithSupport_sequence (Ideal.span {f}) M
  have := epi_complementRestriction_zero_tilde_span_singleton M f
  have hzero : (complementRestriction (Ideal.span {f}) 0).app (tildeSheaf M) ≫
      (delta 0).app (tildeSheaf M) = 0 := hexact.toIsComplex.zero 1
  have hd : (delta 0).app (tildeSheaf M) = 0 := zero_of_epi_comp _ hzero
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  have := hepi
  apply (cancel_epi ((delta 0).app (tildeSheaf M))).1
  simp [hd]

/-- **The sheaf attached to an injective module is acyclic for sections with support in a
principal vanishing locus.**  For a Noetherian ring `A`, an element `f : A` and an injective
`A`-module `M`, the cohomology with support in `V(f)` of `M̃` on `Spec A` vanishes in every
positive degree. -/
theorem isZero_cohomologyWithSupport_tilde_span_singleton [IsNoetherianRing A] (f : A)
    (M : ModuleCat.{u} A) [CategoryTheory.Injective M] (n : ℕ) (hn : 0 < n) :
    IsZero ((cohomologyWithSupport (Ideal.span {f}) n).obj (tildeSheaf M)) := by
  match n, hn with
  | 1, _ => exact isZero_cohomologyWithSupport_one_tilde_span_singleton M f
  | (p + 2), _ =>
    obtain ⟨e⟩ := nonempty_iso_complementCohomology (Ideal.span {f}) M (p + 1) p.succ_pos
    exact IsZero.of_iso (isZero_complementCohomology_tilde (Ideal.span {f})
      (isAffineOpen_openComplement_span_singleton f) M (p + 1) p.succ_pos) e.symm

end Stacks.LocalCohomologySequence

end

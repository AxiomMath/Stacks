module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsGeometricFactor
public import StacksFrontier.Homology.Perfect.PowerTorsionTarget
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a perfect complex on an affine scheme, killed by a power of a scalar

Let `R` be a commutative ring, let `f ∈ R` and let `X = Spec R`. Let `α : E ⟶ E'` be a morphism
of `D_QCoh(𝒪_X)` with `E` perfect and `E'` supported on the closed subset `T = V(f)`. Then
`f ^ n • α = 0` for some `n`.

This is [Stacks, Tag 08EJ] for an affine scheme, stated on the scheme rather than in `D(R)`.
`StacksDraft.Perfect.exists_pow_smul_eq_zero_of_isPerfect_of_support_subset_zeroLocus` is the
same statement in `D(R)`, with the support condition read on the module side; what is done here
is to transport it across the equivalence `D(R) ≌ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0],
with the support condition in the geometric form the source states it, namely that the
cohomology sheaves of `E'` have vanishing stalks off `V(f)`.

## Main results

* `Stacks.PowerTorsion.derivedTilde_linear`: derived sheafification
  `D(R) ⥤ D(𝒪_{Spec R})` is `R`-linear.
* `Stacks.PowerTorsion.exists_pow_smul_eq_zero_homology_of_cohomologySupportedOn`: if `Ñ` is
  supported on `V(f)` then every element of every cohomology module of `N` is `f`-power torsion.
* `Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn`:
  **[Stacks, Tag 08EJ] on an affine scheme**.

## Implementation notes

The three ingredients of the transport are the equivalence, the dictionary between geometric
support and algebraic torsion, and `R`-linearity.

*The equivalence.* `AlgebraicGeometry.derivedTilde_isEquivalence` is [Stacks, Tag 06Z0]; what is
used of it is the two clauses
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`, that an object of
`D(𝒪_{Spec R})` with quasi-coherent cohomology is `Ñ` for some `N` in `D(R)`, and
`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful`, that `N ↦ Ñ` is fully
faithful, so that `α` has a unique preimage `β : M ⟶ N`. Perfectness crosses the equivalence by
`AlgebraicGeometry.isPerfect_tilde_iff`, which is [Stacks, Tag 08EB].

*The support dictionary* is `Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isZero_stalk_tilde`:
the stalks of `M̃` vanish at every prime not containing `f` exactly when `M` is `f`-power
torsion. It is applied to the cohomology modules of `N` through
`Stacks.AffineTilde.nonempty_homology_mapDerivedCategory_tilde_iso`, that the cohomology sheaves
of `Ñ` are the sheaves associated to the cohomology modules of `N`. The resulting elementwise
torsion statement is exactly the hypothesis that
`StacksDraft.Perfect.homPowerTorsion_of_isPerfect` consumes, so no reformulation through
`IsElementPowerTorsion` is needed.

*Linearity.* A scalar `f ∈ R` acts on the morphisms of `D(𝒪_{Spec R})` through the `R`-linear
structure `AlgebraicGeometry.modulesLinear` attached to the identity structure morphism of
`Spec R`, which is a definition and not an instance -- the ring is not determined by the scheme
-- and so appears as a `letI` in the statements below. That derived sheafification is linear for
it is `CategoryTheory.Localization.functor_linear_iff` applied at
`CategoryTheory.DerivedCategory.Q` to the degreewise statement
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_tildeFunctor`. Linearity is what carries
`f ^ n • β = 0` back to `f ^ n • α = 0`: the conjugation of `α` by the two isomorphisms is
`R`-linear by `CategoryTheory.Linear.comp_smul` and `CategoryTheory.Linear.smul_comp`.

*The reduction of a quasi-compact quasi-separated scheme to this case* is
`Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn_qcqs`, in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/QcqsPowerTorsion.lean`: the statement below is the
base case of the induction of [Stacks, Tag 08DR] run there, whose step is
`Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_cover`, Mayer--Vietoris for morphisms of the
derived category ([Stacks, Tag 08BW]).

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.10.7 (Tag 08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Lemma 30.3.2 (Tag 08DR)](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.TopDegreeBaseChange (specBase linear_tildeFunctor)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.PowerTorsion

variable (R : Type u) [CommRing R]

/-- **Derived sheafification `D(R) ⥤ D(𝒪_{Spec R})` is `R`-linear.** Degreewise sheafification
is `R`-linear (`Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_tildeFunctor`), and a
functor induced on localizations by a linear functor is linear. -/
theorem derivedTilde_linear :
    letI : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
    Functor.Linear R
      (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapDerivedCategory := by
  let : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
  let : Functor.Linear R (AlgebraicGeometry.tilde.functor (CommRingCat.of R)) :=
    linear_tildeFunctor R
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) R
    ((AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapDerivedCategory).1 inferInstance

/-- **From geometric support to algebraic torsion, for a single element and in every degree.**
Let `N` be an object of `D(R)` whose derived sheafification is isomorphic to an object of
`D(𝒪_{Spec R})` supported on `V(f)`. Then every element of every cohomology module of `N` is
annihilated by a power of `f`.

The cohomology sheaves of `Ñ` are the sheaves associated to the cohomology modules of `N`, so
the vanishing of their stalks off `V(f)` is the vanishing of the stalks of `H^p(N)^~` at every
prime not containing `f`, which is `f`-power torsion by
`Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isZero_stalk_tilde`. -/
theorem exists_pow_smul_eq_zero_homology_of_cohomologySupportedOn (f : R)
    (N : DerivedCategory (ModuleCat.{u} (CommRingCat.of R)))
    {E' : DerivedCategory (Spec (CommRingCat.of R)).Modules}
    (e : (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapDerivedCategory.obj N ≅ E')
    (hE' : CohomologySupportedOn (Spec (CommRingCat.of R)).ringCatSheaf
      (PrimeSpectrum.zeroLocus {f}) E')
    (p : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of R)) p).obj N) :
    ∃ k : ℕ, f ^ k • y = 0 := by
  obtain ⟨iso⟩ := Stacks.AffineTilde.nonempty_homology_mapDerivedCategory_tilde_iso N p
  refine Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isZero_stalk_tilde _ f (fun x hx => ?_) y
  exact IsZero.of_iso (hE' p x fun hmem => hx (hmem rfl))
    ((Scheme.Modules.toPresheaf (Spec (CommRingCat.of R)) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of R)).Modules p).mapIso e.symm
          ≪≫ iso)).symm

/-- **[Stacks, Tag 08EJ] on an affine scheme.** Let `R` be a commutative ring, let `f : R` and
let `X = Spec R`. Let `α : E ⟶ E'` be a morphism of `D_QCoh(𝒪_X)` such that `E` is perfect and
`E'` is supported on the closed subset `T = V(f)`, that is, the cohomology sheaves of `E'` have
vanishing stalks at every point off `V(f)`. Then `f ^ n • α = 0` for some `n ≥ 0`.

Both objects are `Ñ` for an object `N` of `D(R)` by [Stacks, Tag 06Z0], perfectness of `E`
becomes perfectness of its preimage `M` by [Stacks, Tag 08EB], and the support condition on `E'`
becomes `f`-power torsion of the cohomology modules of the preimage `N`. The statement in `D(R)`
is `StacksDraft.Perfect.homPowerTorsion_of_isPerfect`; derived sheafification carries its
conclusion back, being `R`-linear and fully faithful.

This is the base case of the induction over the quasi-compact opens that proves the statement
for a quasi-compact quasi-separated scheme,
`Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn_qcqs`. -/
@[stacks 08EJ "on an affine scheme, in D(𝒪_X); the base case of the induction over the \
quasi-compact opens that gives the quasi-compact quasi-separated case"]
theorem exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn (f : R)
    {E E' : DerivedCategory (Spec (CommRingCat.of R)).Modules}
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of R)).toRingedSpace) E)
    (hEq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of R)).Modules n).obj E).IsQuasicoherent)
    (hE'q : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of R)).Modules n).obj E').IsQuasicoherent)
    (hsupp : CohomologySupportedOn (Spec (CommRingCat.of R)).ringCatSheaf
      (PrimeSpectrum.zeroLocus {f}) E')
    (α : E ⟶ E') :
    letI : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
    ∃ k : ℕ, f ^ k • α = 0 := by
  let : Linear R (Spec (CommRingCat.of R)).Modules := modulesLinear R (specBase R)
  let : Functor.Linear R
      (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapDerivedCategory :=
    derivedTilde_linear R
  obtain ⟨M, ⟨eM⟩⟩ :=
    AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of R) E hEq
  obtain ⟨N, ⟨eN⟩⟩ :=
    AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of R) E' hE'q
  have hM : StacksDraft.Perfect.IsPerfect M :=
    (AlgebraicGeometry.isPerfect_tilde_iff M).1
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        (X := (Spec (CommRingCat.of R)).toRingedSpace) eM.symm hE)
  have hff := AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful (CommRingCat.of R)
  obtain ⟨k, hk⟩ := StacksDraft.Perfect.homPowerTorsion_of_isPerfect f N
    (exists_pow_smul_eq_zero_homology_of_cohomologySupportedOn R f N eN hsupp)
    hM (hff.preimage (eM.hom ≫ α ≫ eN.inv))
  refine ⟨k, ?_⟩
  have h0 : (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapDerivedCategory.map
      (f ^ k • hff.preimage (eM.hom ≫ α ≫ eN.inv)) = 0 := by
    rw [hk, Functor.map_zero]
  rw [Functor.map_smul, hff.map_preimage] at h0
  calc f ^ k • α
      = f ^ k • (eM.inv ≫ (eM.hom ≫ α ≫ eN.inv) ≫ eN.hom) := by simp
    _ = eM.inv ≫ (f ^ k • (eM.hom ≫ α ≫ eN.inv)) ≫ eN.hom := by
          rw [Linear.smul_comp, Linear.comp_smul]
    _ = 0 := by rw [h0, Limits.zero_comp, Limits.comp_zero]

end Stacks.PowerTorsion

end

module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiStack
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement

/-!
# Fpqc descent over an affine base reduces to a standard fpqc covering

Over an **affine** base every fpqc covering family is refined by a *standard* one — finitely many
flat morphisms out of spectra of rings — by Stacks 022E,
`AlgebraicGeometry.exists_fin_affineCover_flat_hom_of_mem_fpqcPrecoverage`.  Mathlib's descent
API transports the stack condition along such a refinement, so the fpqc stack condition over an
affine base is exactly Stacks 023S, the standard-covering case.

This file carries out that reduction.  It is the affine half of the reduction of Stacks 023T to
`Stacks.Descent.qcohPseudofunctor.IsStack AlgebraicGeometry.Scheme.fpqcTopology`, begun in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/StackReduction.lean`.  The two inputs it
still consumes as hypotheses, and which are not available in the library, are recorded below.

## Main results

* `AlgebraicGeometry.exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage`: Stacks 022E read
  as an inequality of generated sieves, which is the form Mathlib's refinement lemmas take.  This
  is unconditional and is not about modules.
* `Stacks.Descent.isEquivalence_qcohToDescentData_of_isAffine` and
  `Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine`: over an affine base, the fpqc stack
  condition for quasi-coherent modules follows from the standard-covering case.

## What Stacks 023T still needs

`CategoryTheory.Pseudofunctor.IsStack.of_precoverage` asks for
`CategoryTheory.Pseudofunctor.IsStackFor` at **every** fpqc presieve on **every** scheme, so
beyond the results here two things are missing, and neither is in Mathlib or in this library.

1. **Stacks 023S**, appearing here as the hypothesis `hstd`: for a finite family of flat
   morphisms `Spec A k ⟶ T` covering an affine `T`, the descent functor on quasi-coherent modules
   is an equivalence.  Its algebraic content is available —
   `ModuleCat.isEffectiveDescentMorphismForModules_of_faithfullyFlat` (Stacks 023N),
   `Stacks.Descent.isEffective_of_faithfullyFlat` and
   `Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat` (Stacks 023M) — but
   the comparison between `AlgebraicGeometry.QuasicoherentDescentData` over affine schemes and
   `ModuleCat.DescentData` over the corresponding ring map does not exist.  It cannot be routed
   through `Stacks.Descent.comonadicPullbackQcoh` either, because the comparison between
   `CategoryTheory.Pseudofunctor.DescentData` and
   `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra` is an open `TODO` of
   `Mathlib/CategoryTheory/Sites/Descent/DescentDataAsCoalgebra.lean`, and
   `Stacks.Descent.qcohPseudofunctor` is not valued in adjunctions.
2. **Locality of the stack condition on the base**: from the stack condition for an affine open
   covering `V j ⟶ S` together with the stack condition for an fpqc covering of each `V j`, the
   stack condition for the composite family.  This is the paragraph of the Stacks proof of 023T
   that glues the descended modules `F j` along the double and triple intersections.  Mathlib has
   refinement at a *fixed* base (`CategoryTheory.Pseudofunctor.IsStackFor.of_le` and
   `CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`) and nothing
   that changes it, so this is a genuinely absent general theorem rather than a packaging step.
   The Zariski input it would consume is `Stacks.Descent.isStack_qcohPseudofunctor`.

The hypothesis `[Stacks.Descent.qcohPseudofunctor.IsPrestack
AlgebraicGeometry.Scheme.fpqcTopology]` is a third absent input, but not an independent one: both
Mathlib refinement lemmas carry it, and
`CategoryTheory.Pseudofunctor.IsStack.of_precoverage` derives it from `hF`, so it disappears once
(1) and (2) are available.

## Implementation notes

The sieve inequality of `AlgebraicGeometry.exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage`
is proved from the refinement morphism of Stacks 022E rather than from Mathlib's
`CategoryTheory.PreZeroHypercover.Hom.sieve₀_le_sieve₀`: the latter binds both families at a
single index universe, whereas the refining family of 022E is indexed in `Type 0` and the refined
one in an arbitrary `Type v`.

`Sieve.ofArrows` has to be given its target explicitly as `Sieve.ofArrows (X := T)`.  With the
target left implicit, elaboration of the refining family's arrow function postpones and the
inequality is reported as a type mismatch against `Sieve ?m`.

The hypothesis `hstd` is deliberately stated at sources of the form `Spec (A k)` rather than at
arbitrary affine schemes, which makes it the weaker hypothesis and hence this reduction the
stronger statement; it is also the shape `AlgebraicGeometry.Scheme.AffineCover` produces.  Joint
surjectivity and flatness of the family are not listed separately, being part of membership of
the presieve in `AlgebraicGeometry.Scheme.fpqcPrecoverage`.

No stacks attribute is placed in this file.  Both declarations are conditional on `hstd` and on
the fpqc prestack condition, so neither proves 023S or 023T.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe v u

namespace AlgebraicGeometry

/-- **Stacks 022E as an inequality of sieves.**  An fpqc covering family of an affine scheme `T`
is refined by a standard fpqc covering: finitely many flat morphisms out of spectra of rings whose
images cover `T`.  The refinement is recorded as the inclusion of the generated sieves, which is
what `CategoryTheory.Pseudofunctor.IsStackFor.of_le'` and
`CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le` consume. -/
public theorem exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage {T : Scheme.{u}}
    [IsAffine T] {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} T) :
    ∃ (K : Type) (_ : Finite K) (A : K → CommRingCat.{u}) (g : ∀ k, Spec (A k) ⟶ T),
      Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T ∧
        Sieve.ofArrows (X := T) (fun k ↦ Spec (A k)) g ≤ Sieve.ofArrows X f := by
  obtain ⟨n, 𝒱, φ, hn, hmem, -⟩ :=
    exists_fin_affineCover_flat_hom_of_mem_fpqcPrecoverage
      (⟨I, X, f⟩ : PreZeroHypercover.{v} T) hf
  refine ⟨𝒱.I₀, hn ▸ inferInstance, 𝒱.X, 𝒱.f, hmem, ?_⟩
  rw [Sieve.ofArrows, Sieve.ofArrows, Sieve.generate_le_iff]
  rintro Z g ⟨k⟩
  exact ⟨_, φ.h₀ k, f (φ.s₀ k), ⟨_⟩, φ.w₀ k⟩

end AlgebraicGeometry

namespace Stacks.Descent

/-- **Fpqc descent of quasi-coherent modules over an affine base, reduced to the standard
case.**  If the descent functor on quasi-coherent modules is an equivalence for every standard
fpqc covering of an affine scheme — which is Stacks 023S, the hypothesis `hstd` — then it is an
equivalence for every fpqc covering family of an affine scheme.

The reduction is the refinement of Stacks 022E, in the form
`AlgebraicGeometry.exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage`, transported along
`CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`. -/
theorem isEquivalence_qcohToDescentData_of_isAffine
    [qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u}]
    (hstd : ∀ (T : Scheme.{u}) (_ : IsAffine T) (K : Type) (_ : Finite K)
      (A : K → CommRingCat.{u}) (g : ∀ k, Spec (A k) ⟶ T)
      (_ : Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T),
      (qcohPseudofunctor.toDescentData g).IsEquivalence)
    {T : Scheme.{u}} [IsAffine T] {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} T) :
    (qcohPseudofunctor.toDescentData f).IsEquivalence := by
  obtain ⟨K, hK, A, g, hmem, hle⟩ :=
    exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage f hf
  have := hstd T ‹_› K hK A g hmem
  exact Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le
    (F := qcohPseudofunctor) (f' := g) (Precoverage.generate_mem_toGrothendieck hmem) hle

/-- **The fpqc stack condition for quasi-coherent modules over an affine base, reduced to
Stacks 023S.**  This is the restriction to affine bases of the hypothesis of
`CategoryTheory.Pseudofunctor.IsStack.of_precoverage`; what remains for Stacks 023T is the same
condition over a general base, for which see the module documentation. -/
theorem isStackFor_qcohPseudofunctor_of_isAffine
    [qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u}]
    (hstd : ∀ (T : Scheme.{u}) (_ : IsAffine T) (K : Type) (_ : Finite K)
      (A : K → CommRingCat.{u}) (g : ∀ k, Spec (A k) ⟶ T)
      (_ : Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T),
      (qcohPseudofunctor.toDescentData g).IsEquivalence)
    {T : Scheme.{u}} [IsAffine T] (R : Presieve T) (hR : R ∈ Scheme.fpqcPrecoverage.{u} T) :
    qcohPseudofunctor.IsStackFor R := by
  obtain ⟨_, _, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  exact isEquivalence_qcohToDescentData_of_isAffine hstd hR

end Stacks.Descent

end

end

module

public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibres
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresNoetherianApprox
public import StacksFrontier.RingTheory.GeometricallyIntegral.Constructible

/-!
# Stacks 05FT from constructibility of the geometrically integral fibre locus

Stacks 05FT says that a flat ring map `R → S` of finite presentation whose fibres are
geometrically integral makes `S` a projective `R`-module. Its proof is Noetherian approximation
from the Noetherian case 05FS: write `R → S` as the base change of a pair `R₀ → S₀` with `R₀` of
finite type over `ℤ`, pass to a stage `R_λ → S_λ` of the system of Stacks 00R1 which is still flat
with geometrically integral fibres, apply 05FS there, and base change back. The Noetherian case is
`Module.Flat.projective_of_finiteType_of_geometricallyIntegral_fibres` and is already proved.

Flatness reaches a stage by Stacks 02JO
(`Algebra.FiniteTypeSystem.exists_flat_stage_self`). Geometrically integral fibres do not, by a
descent argument alone: `Spec R → Spec R_λ` has dense image but is not surjective, so the primes
of `R_λ` outside the image are unconstrained. Moving to a later stage at which they disappear is
exactly the limit lemma of Stacks 05F4, whose affine case is
`Algebra.FiniteTypeSystem.exists_range_comap_baseMap_subset`, and the input it needs is that the
geometrically integral fibre locus over a Noetherian base is **constructible**.

So the results below are 05FT granted one hypothesis, namely that constructibility. That
hypothesis is Stacks 0579 (local constructibility of the geometrically reduced fibre locus)
together with Stacks 055B (local constructibility of the level sets of the number of geometrically
irreducible components of the fibres), restricted to the affine flat finite type case; it is EGA
IV 9.7.7 and is a true theorem, so neither statement is vacuous. Nothing else is missing: the
scheme-level tower of Stacks 05FB, 05FE and 05FL does not appear, and `hNoeth` of
`Algebra.projective_of_flat_of_geometricallyIntegral_of_finitePresentation` is discharged here by
Stacks 05FS.

`Algebra.projective_of_flat_of_geometricallyIntegral_of_isOpen` records the same conclusion from
*openness* of the locus, which is EGA IV 12.2.4(viii). It is a formal consequence of the
constructible form, because over a Noetherian ring an open subset of the spectrum is constructible
(`PrimeSpectrum.isConstructible_of_isOpen`); the converse implication is false, so the
constructible form is the stronger of the two statements and is the one to aim at.

`Algebra.geometricallyIntegralFibreLocus_eq_inter` splits the remaining hypothesis into its two
Stacks halves: the locus is the intersection of the geometrically irreducible and the
geometrically reduced fibre loci, so it is constructible as soon as those two are, which is 055B
and 0579 respectively.

## Main definitions

* `Algebra.geometricallyReducedFibreLocus`, `Algebra.geometricallyIrreducibleFibreLocus`: the sets
  of primes of the base at which the fibre is geometrically reduced, respectively geometrically
  irreducible, defined exactly like `Algebra.geometricallyIntegralFibreLocus`.

## Main results

* `Algebra.geometricallyIntegralFibreLocus_eq_inter`: the geometrically integral fibre locus is
  the intersection of the other two, and
  `Algebra.isConstructible_geometricallyIntegralFibreLocus` assembles its constructibility from
  theirs.
* `Algebra.FiniteTypeSystem.exists_geometricallyIntegral_stage_of_isConstructible`: a
  geometrically integral stage of the system of Stacks 00R1, granted constructibility of the
  locus at one stage. This strengthens
  `Algebra.FiniteTypeSystem.exists_geometricallyIntegral_stage`, which assumes openness.
* `Algebra.projective_of_flat_of_geometricallyIntegral_of_isConstructible`: Stacks 05FT,
  conditional on constructibility of the geometrically integral fibre locus over a Noetherian
  base, and on nothing else.
* `Algebra.projective_of_flat_of_geometricallyIntegral_of_isOpen`: the same with openness in place
  of constructibility.
* `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible`: the same conclusion
  stated with the hypothesis on the fibres in the residue field form that Stacks 05FT and 05FS
  use, so that supplying one argument yields Stacks 05FT verbatim.

## Implementation notes

Nothing here carries a `@[stacks 05FT]` attribute: the statements are conditional, and tagging a
conditional statement with the tag of an unconditional one would misreport what is proved.
Constructibility of the locus is proved as
`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_finiteType`, and supplying it to
`Algebra.projective_of_flat_of_geometricallyIntegral_of_isConstructible` is what gives
Stacks 05FT, proved as `Algebra.projective_of_geometricallyIntegral_fibres` in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus`.

## References

* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
* [Stacks Project, Tag 00R1](https://stacks.math.columbia.edu/tag/00R1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat Topology
open scoped TensorProduct

universe u

namespace Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section FibreLoci

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]

/-- The **geometrically reduced fibre locus** of an `A`-algebra `C`: the set of primes `p` of `A`
such that `C ⊗[A] K` is reduced for every field `K` over `A` with `ker (A → K) = p`. This is the
pointwise form of the hypothesis of Stacks 0579. -/
def geometricallyReducedFibreLocus : Set (PrimeSpectrum A) :=
  {p | ∀ (K : Type u) [Field K] [Algebra A K], RingHom.ker (algebraMap A K) = p.asIdeal →
    IsReduced (C ⊗[A] K)}

/-- The **geometrically irreducible fibre locus** of an `A`-algebra `C`: the set of primes `p` of
`A` such that `Spec (C ⊗[A] K)` is irreducible for every field `K` over `A` with
`ker (A → K) = p`. This is the pointwise form of the `n = 1` level set of Stacks 055B. -/
def geometricallyIrreducibleFibreLocus : Set (PrimeSpectrum A) :=
  {p | ∀ (K : Type u) [Field K] [Algebra A K], RingHom.ker (algebraMap A K) = p.asIdeal →
    IrreducibleSpace (PrimeSpectrum (C ⊗[A] K))}

/-- **The geometrically integral fibre locus splits into its two Stacks halves.** A fibre is
geometrically integral exactly when it is geometrically irreducible and geometrically reduced
(Stacks 05DY), so the locus of Stacks 05FT is the intersection of the locus of Stacks 055B with
the locus of Stacks 0579. -/
theorem geometricallyIntegralFibreLocus_eq_inter :
    geometricallyIntegralFibreLocus A C =
      geometricallyIrreducibleFibreLocus A C ∩ geometricallyReducedFibreLocus A C := by
  ext p
  simp only [geometricallyIntegralFibreLocus, geometricallyIrreducibleFibreLocus,
    geometricallyReducedFibreLocus, Set.mem_inter_iff, Set.mem_ofPred_eq,
    isDomain_iff_irreducibleSpace_and_isReduced, imp_and, forall_and]

/-- The geometrically integral fibre locus is constructible as soon as the geometrically
irreducible and the geometrically reduced fibre loci are. This reduces the hypothesis of
`Algebra.projective_of_flat_of_geometricallyIntegral_of_isConstructible` to Stacks 055B and
Stacks 0579. -/
theorem isConstructible_geometricallyIntegralFibreLocus
    (hirr : IsConstructible (geometricallyIrreducibleFibreLocus A C))
    (hred : IsConstructible (geometricallyReducedFibreLocus A C)) :
    IsConstructible (geometricallyIntegralFibreLocus A C) :=
  geometricallyIntegralFibreLocus_eq_inter A C ▸ hirr.inter hred

end FibreLoci

namespace FiniteTypeSystem

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (R₀ : Subring A) (S₀ : Type u) [CommRing S₀] [Algebra R₀ S₀] [Algebra S₀ B]
  [IsScalarTower R₀ S₀ B] [Algebra.IsPushout R₀ A S₀ B]

/-- **A geometrically integral stage of the system, granted constructibility of the locus.**
Suppose `Spec B ⟶ Spec A` is geometrically integral and that at the stage `λ` the geometrically
integral fibre locus of `S_λ` over `R_λ` is constructible. Then `Spec S_μ ⟶ Spec R_μ` is
geometrically integral for some `μ ≥ λ`.

The locus contains the image of `Spec A` by
`Algebra.mem_geometricallyIntegralFibreLocus_of_mem_rangeComap`, so by the affine limit lemma
`Algebra.FiniteTypeSystem.exists_range_comap_baseMap_subset` it contains the image of `Spec R_μ`
for some `μ ≥ λ`. The fibres of `R_μ → S_μ` are the base changes of those of `R_λ → S_λ`, so they
are geometrically integral by
`Algebra.mem_geometricallyIntegralFibreLocus_of_isPushout`.

This strengthens `Algebra.FiniteTypeSystem.exists_geometricallyIntegral_stage`, which assumes the
locus open: over the Noetherian ring `R_λ` an open subset of the spectrum is constructible. -/
theorem exists_geometricallyIntegral_stage_of_isConstructible (i : Index R₀)
    (hc : IsConstructible (geometricallyIntegralFibreLocus (Base R₀ i) (Ring R₀ S₀ i)))
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap A B)))) :
    ∃ j, i ≤ j ∧
      GeometricallyIntegral (Spec.map (ofHom (algebraMap (Base R₀ j) (Ring R₀ S₀ j)))) := by
  have : Algebra.IsPushout (Base R₀ i) A (Ring R₀ S₀ i) B := ringToRing_isPushout R₀ S₀ i
  have hS := (geometricallyIntegral_iff_forall_isDomain_tensorProduct A B).mp h
  obtain ⟨j, hij, hj⟩ := exists_range_comap_baseMap_subset R₀ i hc
    fun _ hp => mem_geometricallyIntegralFibreLocus_of_mem_rangeComap hS _ hp
  refine ⟨j, hij, ?_⟩
  have : Fact (i ≤ j) := ⟨hij⟩
  have : Algebra.IsPushout (Base R₀ i) (Base R₀ j) (Ring R₀ S₀ i) (Ring R₀ S₀ j) :=
    ringMap_isPushout R₀ S₀
  rw [geometricallyIntegral_iff_forall_mem_geometricallyIntegralFibreLocus]
  exact fun q => mem_geometricallyIntegralFibreLocus_of_isPushout (A := Base R₀ i)
    (C := Ring R₀ S₀ i) q (hj (Set.mem_range_self q))

end FiniteTypeSystem

open Algebra.FiniteTypeSystem in
/-- **Stacks 05FT from constructibility of the geometrically integral fibre locus.** Let
`R → S` be flat of finite presentation with geometrically integral fibres and assume that for
every flat finite type algebra over a Noetherian ring the geometrically integral fibre locus is
constructible. Then `S` is a projective `R`-module.

Write `R → S` as the base change of `R₀ → S₀` with `R₀ ⊆ R` of finite type over `ℤ` (Stacks
00R1). Flatness holds at a stage `R_λ → S_λ` of the system of finite type `ℤ`-subalgebras of `R`
(Stacks 02JO), that stage is Noetherian, and `hConstr` feeds
`Algebra.FiniteTypeSystem.exists_geometricallyIntegral_stage_of_isConstructible` to move to a
stage `R_μ → S_μ` which moreover has geometrically integral fibres. It is still flat, by base
change along `R_λ → R_μ`. So `S_μ` is a projective `R_μ`-module by Stacks 05FS, and
`S = R ⊗_{R_μ} S_μ` is a projective `R`-module by Stacks 05A3. -/
theorem projective_of_flat_of_geometricallyIntegral_of_isConstructible
    (hConstr : ∀ (R₀ S₀ : Type u) [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
      [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Flat R₀ S₀],
      IsConstructible (geometricallyIntegralFibreLocus R₀ S₀))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] :
    Module.Projective R S := by
  obtain ⟨R₀, S₀, -, _, _, _, _, -, -, -, -, -, hZ, hS₀, -, hpush, -⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := R) (S := S) S
  have := hZ
  have := hS₀
  have := hpush
  obtain ⟨i, hi⟩ := exists_flat_stage_self R₀ S₀ (B := S)
  have := hi
  have noeth (k : Index R₀) : IsNoetherianRing (Base R₀ k) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨j, hij, hj⟩ :=
    exists_geometricallyIntegral_stage_of_isConstructible R₀ S₀ i (hConstr _ _) ‹_›
  have : Fact (i ≤ j) := ⟨hij⟩
  have : Module.Flat (Base R₀ j) (Ring R₀ S₀ j) :=
    Module.Flat.isBaseChange (Base R₀ i) (Base R₀ j) (Ring R₀ S₀ i) (Ring R₀ S₀ j)
      (ringMap_isPushout R₀ S₀ (i := i) (j := j)).out
  have := hj
  have := Module.Flat.projective_of_finiteType_of_geometricallyIntegral_fibres
    (R := Base R₀ j) (S := Ring R₀ S₀ j)
    (geometricallyIntegral_algebraMap_iff_residueField.mp ‹_›)
  have : Algebra.IsPushout (Base R₀ j) R (Ring R₀ S₀ j) S := ringToRing_isPushout R₀ S₀ j
  exact Module.Projective.of_equiv'
    (Algebra.IsPushout.equiv (Base R₀ j) R (Ring R₀ S₀ j) S).toLinearEquiv

/-- **Stacks 05FT from openness of the geometrically integral fibre locus.** The same statement as
`Algebra.projective_of_flat_of_geometricallyIntegral_of_isConstructible` with openness of the
locus, which is EGA IV 12.2.4(viii), in place of constructibility. It follows formally, an open
subset of the spectrum of a Noetherian ring being constructible.

This is also
`Algebra.projective_of_flat_of_geometricallyIntegral_of_finitePresentation` with its hypothesis
`hNoeth` discharged by Stacks 05FS. -/
theorem projective_of_flat_of_geometricallyIntegral_of_isOpen
    (hOpen : ∀ (R₀ S₀ : Type u) [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
      [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Flat R₀ S₀],
      IsOpen (geometricallyIntegralFibreLocus R₀ S₀))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] :
    Module.Projective R S :=
  projective_of_flat_of_geometricallyIntegral_of_isConstructible
    (fun R₀ S₀ _ _ _ _ _ _ => PrimeSpectrum.isConstructible_of_isOpen (hOpen R₀ S₀))

/-- **Stacks 05FT in fibre form, conditional on constructibility of the locus.** This is
`Algebra.projective_of_flat_of_geometricallyIntegral_of_isConstructible` with the hypothesis on
the fibres written as geometric integrality of `S ⊗[R] κ(p)` over `κ(p)` for every prime `p`,
which is how Stacks 05FT and the proved Stacks 05FS
(`Module.Flat.projective_of_finiteType_of_geometricallyIntegral_fibres`) state it. The two forms
agree by `AlgebraicGeometry.geometricallyIntegral_algebraMap_iff_residueField`.

Supplying the single argument `hConstr` turns this into Stacks 05FT. -/
theorem projective_of_geometricallyIntegral_fibres_of_isConstructible
    (hConstr : ∀ (R₀ S₀ : Type u) [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
      [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Flat R₀ S₀],
      IsConstructible (geometricallyIntegralFibreLocus R₀ S₀))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  have := geometricallyIntegral_algebraMap_iff_residueField.mpr h
  projective_of_flat_of_geometricallyIntegral_of_isConstructible hConstr

end Algebra

end

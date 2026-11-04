module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Homology.Perfect.MinimalRepresentative

/-!
# Perfect complexes whose derived fibre is concentrated in one degree

Let `R` be a commutative ring, `p` a prime of `R` and `K` a perfect object of `D(R)`. If the
derived fibre `K ⊗ᴸ_R κ(p)` has no cohomology outside a single degree `i`, then on a principal
neighbourhood of `p` the object `K` *is* a finite free module placed in degree `i`, of rank the
one surviving fibre dimension.

This is the local input to [stacks 0BDK], the openness of the locus where a perfect complex on a
scheme is a finite locally free module in a prescribed degree and of a prescribed rank: it is the
statement that supplies, around each point of that locus, a neighbourhood on which the complex has
the asserted shape.

## Main results

* `StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated`: the principal
  neighbourhood and the identification of `K` on it with a finite free module in degree `i`.
* `StacksDraft.Perfect.isOpen_fibre_finrank_eq`: the locus in `Spec R` where the fibre dimension
  of a finite projective module equals a prescribed value is open — the module-level form of the
  rank stratification used by the same tag.

## Implementation notes

The neighbourhood and the representative both come from
`StacksDraft.Perfect.exists_away_bounded_free_complex_representing` ([stacks 0BCD]), which
produces over some `R_f` a strictly bounded complex whose term in degree `j` is free of rank the
`j`-th fibre dimension at `p`. Under the concentration hypothesis every rank other than the `i`-th
is zero, so every term other than the `i`-th is a zero module and the complex is concentrated in
degree `i`; `CochainComplex.exists_iso_single` then identifies it with its own degree-`i` term
placed in degree `i`, and that term is free of the remaining rank. No separate appeal to the
derived-category single-degree criterion of
`StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree` is needed, because the vanishing is
already visible on the complex rather than only on its homology.

The openness of the rank locus is not new mathematics here: `Module.rankAtStalk` is locally
constant on a finite projective module by `Module.isLocallyConstant_rankAtStalk`, and
`Module.rankAtStalk_eq` identifies it with the fibre dimension. What is recorded is the composite,
in the fibre-dimension form in which the tag states it, since that is the form in which the degree
and rank loci of a perfect complex are described.

## References

* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- The `j`-th cohomology of the derived fibre at `p` of an object of `D(R)`. -/
public abbrev derivedFibreHomology {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max v u} R)) (j : ℤ) :
    ModuleCat.{max v u} p.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.ResidueField) j).obj
    ((totalDerivedExtensionScalars.{u, u, v} (algebraMap R p.ResidueField)).functor.obj K)

/-- Let `R` be a commutative ring, `p` a prime of `R`, `K` a perfect object of `D(R)` and `i` an
integer. If the derived fibre `K ⊗ᴸ_R κ(p)` has vanishing cohomology in every degree other than
`i`, then there is an `f ∈ R` outside `p` such that `K ⊗ᴸ_R R_f` is isomorphic in `D(R_f)` to the
free `R_f`-module of rank `dim_{κ(p)} Hⁱ(K ⊗ᴸ_R κ(p))` placed in degree `i`.

This is the local structure statement underlying [stacks 0BDK]. -/
public theorem exists_away_iso_singleFunctor_free_of_fibre_concentrated
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) (i : ℤ)
    (hvanish : ∀ j : ℤ, j ≠ i →
      Module.finrank p.ResidueField (derivedFibreHomology.{u, v} p K j) = 0) :
    ∃ f : R, f ∉ p ∧
      Nonempty
        ((totalDerivedExtensionScalars.{u, u, v}
              (algebraMap R (Localization.Away f))).functor.obj K ≅
          (DerivedCategory.singleFunctor (ModuleCat.{max v u} (Localization.Away f)) i).obj
            (ModuleCat.of (Localization.Away f)
              (ULift.{v} (Fin (Module.finrank p.ResidueField (derivedFibreHomology.{u, v} p K i)) →
                Localization.Away f)))) := by
  obtain ⟨-, -, f, hf, P, a, b, hPa, hPb, hPX, ⟨hPK⟩⟩ :=
    exists_away_bounded_free_complex_representing.{u, v} p K hK
  refine ⟨f, hf, ?_⟩
  have hzero : ∀ j : ℤ, j ≠ i → IsZero (P.X j) := by
    intro j hj
    refine IsZero.of_iso ?_ (hPX j).some
    rw [hvanish j hj]
    exact ModuleCat.isZero_of_subsingleton _
  have : P.IsStrictlyGE i :=
    (CochainComplex.isStrictlyGE_iff P i).2 fun j hj => hzero j (by omega)
  have : P.IsStrictlyLE i :=
    (CochainComplex.isStrictlyLE_iff P i).2 fun j hj => hzero j (by omega)
  obtain ⟨M, ⟨e⟩⟩ := P.exists_iso_single i
  have eMX : M ≅ P.X i :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M).symm ≪≫
      ((HomologicalComplex.eval _ _ i).mapIso e).symm
  refine ⟨hPK.symm ≪≫ DerivedCategory.Q.mapIso
      (e ≪≫ (HomologicalComplex.single _ (ComplexShape.up ℤ) i).mapIso
        (eMX ≪≫ (hPX i).some)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} (Localization.Away f))
      i).app _).symm⟩

/-- The locus in `Spec R` where the fibre dimension of a finite projective `R`-module equals a
prescribed value is open. -/
public theorem isOpen_fibre_finrank_eq {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] (r : ℕ) :
    IsOpen {q : PrimeSpectrum R |
      Module.finrank q.asIdeal.ResidueField (q.asIdeal.Fiber M) = r} := by
  have : Module.Flat R M := Module.Flat.of_projective
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have h : {q : PrimeSpectrum R |
        Module.finrank q.asIdeal.ResidueField (q.asIdeal.Fiber M) = r} =
      Module.rankAtStalk (R := R) M ⁻¹' {r} := by
    ext q
    simp [Ideal.finrank_fiber_eq_rankAtStalk]
  rw [h]
  exact Module.isLocallyConstant_rankAtStalk _

end StacksDraft.Perfect

end

module

public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.Homology.Perfect.FibreDescent
public import StacksFrontier.Homology.Perfect.ProjectiveAmplitude
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChange

/-!
# Bounds for the cohomology of a relative dualizing complex

Let `R → A` be a flat finite type homomorphism of Noetherian rings, let `𝔮 ⊂ A` be a prime and
let `d` be the dimension at `𝔮` of the fibre of `Spec(A) → Spec(R)` through `𝔮`.  Then the
localization at `𝔮` of `H^i(ω^•_{A/R})` vanishes unless `-d ≤ i ≤ 0`, where
`ω^•_{A/R} = f^!(R)` is the relative dualizing complex.

## Main results

* `Dualizing.isZero_homology_upperShriekFunctor_unit_of_pos` — the upper bound, in the stronger
  unlocalized form: `H^i(ω^•_{A/R}) = 0` for every `i > 0`.
* `Dualizing.upperShriekFunctor_relativeDimensionAt_bounds_of_nontrivial_localizedHomology` —
  the two-sided local bound `-d ≤ i ≤ 0` of [Stacks, Tag 0E9Q].
* `Dualizing.isZero_homology_upperShriekFunctor_unit_of_notMem_Icc` — cohomological
  concentration in `[-d, 0]` under a bound `d` on every fibre dimension.

## Implementation notes

The relative dualizing complex of [Stacks, Tag 0E9M] is `f^!` applied to `R` placed in degree
zero, and `f^!` is only defined up to isomorphism; as in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound` the statements below are
therefore made for the functor of an arbitrary polynomial presentation
`R → P = R[x_1, …, x_n] → A`, which is stronger than any statement about one chosen
presentation.

The argument is the source's.  The lower bound is [Stacks, Tag 0E9P], already available as
`Dualizing.upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology`.  For
the upper bound, the identification `f^!(R) = RHom_P(A, P)[n]` turns the claim into the vanishing
of `Ext^k_P(A, P)` for `k > n`.  Flatness of `R → A` makes `A` a module of Tor amplitude `[0, 0]`
over `R`, and the fibres of `R → P` are polynomial algebras over residue fields, of global
dimension at most `n`; so [Stacks, Tag 068X] makes `A` a perfect `P`-module of Tor amplitude in
`[-n, 0]`, whence [Stacks, Tag 0G9A] gives it projective amplitude in `[-n, 0]` and kills
`Ext^k_P(A, P)` outside `[0, n]`.

The Tor amplitude of `A` over `R` is taken against the canonical certified derived tensor
product, and transported to the termwise form that [Stacks, Tag 068X] asks for, so that no
derived tensor product appears in the statements.

## References

* [Stacks Project, Tag 0E9Q](https://stacks.math.columbia.edu/tag/0E9Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The target of a polynomial presentation, restricted along the presentation all the way down
to the coefficient ring, is the target with its own structure of module over the coefficient
ring. -/
private noncomputable def restrictScalarsSingleULiftIso
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : PolynomialPresentation (algebraMap R A)) :
    (ModuleCat.restrictScalars (algebraMap R p.Poly)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
          ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{u} A)) := by
  let F := ModuleCat.restrictScalars (algebraMap R p.Poly)
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  have hr (r : R) : p.toRingHom (algebraMap R p.Poly r) = algebraMap R A r :=
    congrArg (fun g : R →+* A => g r) p.commutes
  letI : Module R (M₀ : Type u) := (F.obj M₀).isModule
  have e : F.obj M₀ ≅ ModuleCat.of R (ULift.{u} A) := by
    refine LinearEquiv.toModuleIso { AddEquiv.refl (ULift.{u} A) with map_smul' := ?_ }
    intro r x
    change ULift.up (p.toRingHom (algebraMap R p.Poly r) * (x.down : A)) =
      ULift.up (r • (x.down : A))
    rw [hr, Algebra.smul_def]
  exact (F.mapDerivedCategorySingleFunctor 0).app M₀ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e

/-- The target of a polynomial presentation, read as a module over the polynomial ring and placed
in degree zero, is pseudo-coherent. -/
private theorem isPseudoCoherent_single_restrictScalars_ulift
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
        ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))) := by
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  let instM₀ : Module p.Poly (M₀ : Type u) := M₀.isModule
  have hM₀ : Module.Finite p.Poly (M₀ : Type u) := finite_restrictScalars_ulift p
  exact isPseudoCoherent_single_of_finite M₀

/-- **[Stacks, Tag 068X] at a polynomial presentation.** For a flat finite type homomorphism of
Noetherian rings and a polynomial presentation `R → P = R[x_1, …, x_n] → A`, the target `A`, read
as a `P`-module and placed in degree zero, is a perfect object of `D(P)` with a flat
representative in degrees `[-n, 0]` — that is, of Tor amplitude in `[-n, 0]` over `P`.

Flatness of `R → A` makes `A` a module of Tor amplitude `[0, 0]` over `R`, and the fibres of
`R → P` are polynomial algebras over residue fields, of global dimension at most `n`; so
[Stacks, Tag 068X] —
`StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le` — applies
with `a = b = 0` and `d = n`.

The module is carried as `ULift A` so that the statement stays inside one universe; the
pseudo-coherence that accompanies it in every consumer is
`Dualizing.isPseudoCoherent_single_of_finite` applied to
`Dualizing.finite_restrictScalars_ulift`. -/
theorem isPerfect_and_hasFlatRepresentative_single_restrictScalars_ulift_of_flat
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) :
    StacksDraft.Perfect.IsPerfect
        ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
          ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))) ∧
      StacksDraft.Perfect.HasFlatRepresentative
        ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
          ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))))
        (-(p.variableCount : ℤ)) 0 := by
  have hP : IsNoetherianRing p.Poly := inferInstance
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj M₀
  have hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
    isPseudoCoherent_single_restrictScalars_ulift p
  have hflatULift : Module.Flat R (ULift.{u} A) :=
    Module.Flat.of_linearEquiv (ULift.moduleEquiv.{u, u, u} (R := R) (M := A))
  -- `A` has Tor amplitude `[0, 0]` over `R`, being flat; transport to the termwise form.
  have htor : StacksDraft.TorAmplitude.HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{u} A))) 0 0 :=
    (StacksDraft.TorAmplitude.hasTorDimensionLE_iff_hasFlatRepresentative
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      (ModuleCat.of R (ULift.{u} A)) 0).2.mpr hflatULift
  have hterm := StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) _ 0 0 htor
  have hres := restrictScalarsSingleULiftIso p
  have hamp : ∀ E : CochainComplex (ModuleCat.{u} R) ℤ,
      StacksDraft.TorAmplitude.BoundedAbove E →
      StacksDraft.TorAmplitude.IsComplexOfFlats E →
      Nonempty ((ModuleCat.restrictScalars (algebraMap R p.Poly)).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj E) →
      StacksDraft.TorAmplitude.HasTorAmplitudeIn E 0 0 := by
    rintro E hbounded hflats ⟨e⟩
    exact hterm E hbounded hflats ⟨hres.symm ≪≫ e⟩
  have hdesc := StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le
    (A := R) (B := p.Poly) 0 0 p.variableCount
    (RingHom.polynomial_fibre_globalDimension_le R p.variableCount) K hK hamp
  refine ⟨hdesc.1, ?_⟩
  simpa only [zero_sub] using hdesc.2.1

/-- **The vanishing of `Ext^k_P(A, P)` for `k > n`.** For a flat finite type homomorphism of
Noetherian rings and a polynomial presentation `R → P → A` in `n` variables, the cohomology of
`RHom_P(A, P)` vanishes in degrees above `n`: by [Stacks, Tag 068X] the target is a perfect
`P`-module of Tor amplitude in `[-n, 0]`, so by [Stacks, Tag 0G9A] it has projective amplitude in
`[-n, 0]`. -/
private theorem isZero_homology_derivedHom_poly_unit
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A))
    (k : ℤ) (hk : (p.variableCount : ℤ) < k) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
      ((derivedHom.{u, 0, u} p.toRingHom).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
          (ModuleCat.of p.Poly p.Poly)))) := by
  have hperfectTor := isPerfect_and_hasFlatRepresentative_single_restrictScalars_ulift_of_flat p
  have hext :=
    (StacksDraft.ProjectiveAmplitude.hasProjectiveAmplitude_iff_perfect_iff_ext_vanishing _
      (isPseudoCoherent_single_restrictScalars_ulift p) (-(p.variableCount : ℤ)) 0).2.1.mp
      hperfectTor
  have hzeroExt := hext (ModuleCat.of p.Poly p.Poly) inferInstance k (by
    intro h
    simp only [Set.mem_Icc, neg_zero, neg_neg] at h
    omega)
  let RF := derivedHom.{u, 0, u} p.toRingHom
  let α := (coextendScalarsToDerivedCategory p.toRingHom).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} p.Poly) (ComplexShape.up ℤ))
  let eExt := (derivedCoextendScalarsHomologyLinearEquivExt p.toRingHom RF α).linearEquiv
    ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
      (ModuleCat.of p.Poly p.Poly)) k
  have hzeroRestrict : Subsingleton ((ModuleCat.restrictScalars p.toRingHom).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
        (RF.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
          (ModuleCat.of p.Poly p.Poly))))) :=
    eExt.toEquiv.subsingleton_congr.mpr hzeroExt
  exact ModuleCat.isZero_iff_subsingleton.mpr hzeroRestrict

/-- **The upper bound of [Stacks, Tag 0E9Q].** For a flat finite type homomorphism of Noetherian
rings, `H^i(ω^•_{A/R})` vanishes for every `i > 0`.  This is stronger than the localized form the
source states, which follows from it at every prime. -/
theorem isZero_homology_upperShriekFunctor_unit_of_pos
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A))
    (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  let RF := derivedHom.{u, 0, u} p.toRingHom
  let input := (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
    (ModuleCat.of p.Poly p.Poly)
  let shifted := (shiftFunctor (DerivedCategory (ModuleCat.{u} A))
    (p.variableCount : ℤ)).obj (RF.obj input)
  have eUpper :
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        shifted := by
    dsimp [PolynomialPresentation.upperShriekFunctor, shifted, RF, input]
    exact (shiftFunctor (DerivedCategory (ModuleCat.{u} A))
      (p.variableCount : ℤ)).mapIso
        ((derivedHom.{u, 0, u} p.toRingHom).mapIso p.derivedExtensionUnitIso)
  have hzeroShift : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj shifted) :=
    (isZero_homology_derivedHom_poly_unit p (p.variableCount + i) (by omega)).of_iso
      ((StacksDraft.PseudoCoherence.homologyFunctorShiftIso.{u, u}
        (R := A) (p.variableCount : ℤ) i).app (RF.obj input))
  exact hzeroShift.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eUpper)

/-- **[Stacks, Tag 0E9Q], the local bounds.** Let `R → A` be a flat finite type homomorphism of
Noetherian rings, let `𝔮 ⊂ A` be a prime and let `d` be the dimension at `𝔮` of the fibre of
`Spec(A) → Spec(R)` over the prime below `𝔮`.  If the localization at `𝔮` of `H^i(ω^•_{A/R})` is
nonzero then `-d ≤ i ≤ 0`.  Here `ω^•_{A/R} = f^!(R)` is computed from an arbitrary polynomial
presentation of `f`. -/
@[stacks 0E9Q "the local bounds: H^i(omega)_q nonzero implies -d <= i <= 0, d the dimension at \
q of the fibre through q, for the upper shriek functor of an arbitrary polynomial presentation of \
the homomorphism, the relative dualizing complex being well defined only up to isomorphism; the \
Tor amplitude clause is Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le"]
theorem upperShriekFunctor_relativeDimensionAt_bounds_of_nontrivial_localizedHomology
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A))
    (q : PrimeSpectrum A) (d : ℕ)
    (hd : Algebra.relativeDimensionAt R q.asIdeal = (d : WithBot ℕ∞)) (i : ℤ) :
    Nontrivial
        (LocalizedModule q.asIdeal.primeCompl
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (p.upperShriekFunctor.{u, 0}.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                (ModuleCat.of R R))))) →
      -(d : ℤ) ≤ i ∧ i ≤ 0 := by
  intro hlocal
  refine ⟨upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology
    p q d hd i hlocal, ?_⟩
  by_contra hnot
  have hzero := isZero_homology_upperShriekFunctor_unit_of_pos p i (lt_of_not_ge hnot)
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
    ModuleCat.isZero_iff_subsingleton.mp hzero
  refine (not_nontrivial_iff_subsingleton.mpr (LocalizedModule.subsingleton_iff.mpr ?_)) hlocal
  intro x
  exact ⟨1, Submonoid.one_mem _, by rw [Subsingleton.elim x 0, smul_zero]⟩

/-- A bound on the local fibre dimension at a prime names it as a natural number, the local
dimension of a fibre through a point of it being neither `⊥` nor infinite. -/
private theorem relativeDimensionAt_exists_nat_le {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (q : PrimeSpectrum A) (d : ℕ)
    (hd : Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, Algebra.relativeDimensionAt R q.asIdeal = (e : WithBot ℕ∞) ∧ e ≤ d := by
  refine Stacks.RelativeDimension.Semicontinuity.exists_nat_eq_of_zero_le_of_le_nat ?_ hd
  rw [Algebra.relativeDimensionAt]
  exact topologicalKrullDimAt_nonneg _

/-- **Cohomological concentration under a bound on every fibre dimension.** Let `R → A` be a flat
finite type homomorphism of Noetherian rings all of whose fibres have dimension at most `d`.
Then `H^i(ω^•_{A/R})` vanishes for every `i` outside `[-d, 0]`: the local bounds above, applied at
every maximal ideal.  This is the form in which the proof of the Tor-amplitude clause of
[Stacks, Tag 0E9Q], `Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le`, applies
the local bounds after base change. -/
theorem isZero_homology_upperShriekFunctor_unit_of_notMem_Icc
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ q : PrimeSpectrum A, Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : i ∉ Set.Icc (-(d : ℤ)) 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  let N : ModuleCat.{u} A := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
    (p.upperShriekFunctor.{u, 0}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  rw [ModuleCat.isZero_iff_subsingleton]
  refine Module.subsingleton_of_localization_maximal (R := A) (M := (N : Type u))
    (fun m _ => LocalizedModule m.primeCompl (N : Type u))
    (fun m _ => LocalizedModule.mkLinearMap m.primeCompl (N : Type u)) fun m hm => ?_
  obtain ⟨e, he, hed⟩ :=
    relativeDimensionAt_exists_nat_le (⟨m, hm.isPrime⟩ : PrimeSpectrum A) d (hd _)
  refine not_nontrivial_iff_subsingleton.mp fun hn => ?_
  have h := upperShriekFunctor_relativeDimensionAt_bounds_of_nontrivial_localizedHomology
    p ⟨m, hm.isPrime⟩ e he i hn
  exact hi ⟨by omega, h.2⟩

end Dualizing

end

module

public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import all StacksFrontier.RingTheory.Dualizing.Gorenstein
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dualizing complexes over Gorenstein rings

A Noetherian Gorenstein ring has a dualizing complex exactly when the ring itself, placed in
degree zero, is one. Equivalently, such a ring has a dualizing complex exactly when it has finite
injective dimension as a module over itself.

## Main results

* `Dualizing.isDualizingComplex_single_self_iff` — for any Noetherian ring, the ring in degree
  zero is a dualizing complex precisely when the ring has finite injective dimension over itself.
  The other two conditions of [Stacks, Tag 0A7B] hold for the ring in degree zero over any
  Noetherian ring.
* `Dualizing.exists_isDualizingComplex_iff_regularModule` — **[Stacks, Tag 0DW9 (2)]**.

## Implementation notes

The forward implication is local: at every prime the dualizing complex becomes a shifted copy of
the ring on a principal neighbourhood
(`Dualizing.IsDualizingComplex.exists_isLocalized_iso_shift_single`), so each localized ring in
degree zero is dualizing, and those neighbourhoods cover the spectrum, so [Stacks, Tag 0A7H]
glues them. The converse produces a dualizing complex in the larger module universe demanded by
the statement by viewing the identity of the ring as a localization twice over, once in each
direction, and transporting along [Stacks, Tag 0A7G].

A witnessing dualizing complex is allowed to live in a module universe `max u v` unrelated to the
ring's universe `u`, whereas the ring in degree zero lives in the ring's own universe, as in the
definition of a Gorenstein ring. The two are reconciled by
`Dualizing.isDualizingComplex_single_self_of_ulift`, which descends the conclusion rather than the
hypothesis: of the three conditions only finite injective dimension is universe-sensitive, and it
is equivalent to a statement about the module `A`, which has no module universe of its own.

## References

* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

section InjectiveDimension

open StacksDraft.InjectiveDimension

/-- A module whose associated complex in degree zero has finite injective dimension has finite
injective dimension: the upper end of an injective amplitude bounds it. -/
@[sga "6 I 5.7" "b)"]
private theorem exists_hasInjectiveDimensionLE_of_hasFiniteInjectiveDimension_single
    {A : Type u} [CommRing A] [Small.{w} A] {M : ModuleCat.{w} A}
    (h : HasFiniteInjectiveDimension
      ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M)) :
    ∃ n : ℕ, HasInjectiveDimensionLE M n := by
  obtain ⟨a, b, I, hGE, hLE, hI, ⟨e⟩⟩ := h
  let K := (DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M
  have hExt := (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing K a b).1.mp
    ⟨I, hGE, hLE, hI, ⟨e⟩⟩
  refine ⟨b.toNat, ?_⟩
  change CategoryTheory.HasInjectiveDimensionLT M (b.toNat + 1)
  rw [CategoryTheory.hasInjectiveDimensionLT_iff]
  intro i hi N x
  have : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj N) K (i : ℤ)) :=
    hExt N (i : ℤ) (Or.inr (by omega))
  exact (Equiv.subsingleton (CategoryTheory.Abelian.Ext.homEquiv
    (C := ModuleCat.{w} A) (X := N) (Y := M) (n := i))).elim x _

/-- A module of finite injective dimension gives a complex of finite injective dimension when
placed in degree zero: the module itself is an injective resolution of bounded length. -/
@[sga "6 I 5.7" "b)"]
private theorem hasFiniteInjectiveDimension_single_of_exists_hasInjectiveDimensionLE
    {A : Type u} [CommRing A] [Small.{u} A] {M : ModuleCat.{u} A}
    (h : ∃ n : ℕ, HasInjectiveDimensionLE M n) :
    HasFiniteInjectiveDimension
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  have hterms : ∀ i : ℤ, ∃ n : ℕ, HasInjectiveDimensionLE (L.X i) n := by
    intro i
    obtain rfl | hi := eq_or_ne i 0
    · exact h
    · have : CategoryTheory.HasInjectiveDimensionLT (L.X i) 0 := IsZero.hasInjectiveDimensionLT_zero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
      exact ⟨0, hasInjectiveDimensionLT_of_ge (L.X i) 0 1 (by omega)⟩
  exact (hasFiniteInjectiveDimension_of_bounded K).2 L
    ⟨((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).symm⟩
    ⟨0, 0, inferInstance, inferInstance⟩ hterms

end InjectiveDimension

/-- The homothety condition of [Stacks, Tag 0A7B] holds for the ring in degree zero over any
commutative ring: on a bounded injective representative it is the scalar action on the identity
cochain, which computes the derived endomorphisms of the ring. -/
private theorem isDerivedHomothetyQuasiIso_single_self (A : Type u) [CommRing A] :
    IsDerivedHomothetyQuasiIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  intro I hI hInj hBounds
  obtain ⟨a, b, hGE, hLE⟩ := hBounds
  have : I.IsStrictlyGE a := hGE
  have : ∀ i, Injective (I.X i) := hInj
  let srcIso := (CategoryTheory.Functor.mapCochainComplexSingleFunctor
    (AddCommGrpCat.uliftFunctor.{u, u}) 0).app (AddCommGrpCat.of A)
  let liftedBase := ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (homothetyBase I)
  have : QuasiIso liftedBase := (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (homothetyBase I) (AddCommGrpCat.uliftFunctor.{u, u})).2 (homothetyBase_quasiIso I hI a)
  have hmap : srcIso.inv ≫ liftedBase = homothety I := by
    apply HomologicalComplex.from_single_hom_ext
    ext x
    rfl
  rw [← hmap]
  exact (inferInstance : QuasiIso (srcIso.inv ≫ liftedBase))

/-- A Noetherian ring in degree zero is a dualizing complex exactly when the ring has finite
injective dimension as a module over itself; the finiteness of the cohomology and the homothety
condition of [Stacks, Tag 0A7B] hold for any Noetherian ring. -/
theorem isDualizingComplex_single_self_iff (A : Type u) [CommRing A] [IsNoetherianRing A] :
    IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ↔
      ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of A A : ModuleCat.{u} A) n :=
  ⟨fun h => exists_hasInjectiveDimensionLE_of_hasFiniteInjectiveDimension_single
      h.finiteInjectiveDimension,
    fun h => ⟨hasFiniteInjectiveDimension_single_of_exists_hasInjectiveDimensionLE h,
      finiteCohomology_single_regularModule A, isDerivedHomothetyQuasiIso_single_self A⟩⟩

/-- Being a dualizing complex passes from the universe-lifted ring in degree zero down to the ring
in degree zero: both are equivalent to the ring having finite injective dimension over itself,
a property of the module `A` that does not refer to a module universe. -/
theorem isDualizingComplex_single_self_of_ulift
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{max u w} A) 0).obj
        (ModuleCat.of A (ULift.{w} A)))) :
    IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  obtain ⟨n, hn⟩ := exists_hasInjectiveDimensionLE_of_hasFiniteInjectiveDimension_single
    (M := (ModuleCat.of A (ULift.{w} A) : ModuleCat.{max u w} A)) h.finiteInjectiveDimension
  refine (isDualizingComplex_single_self_iff A).2 ⟨n, ?_⟩
  have e : (ModuleCat.of A A : ModuleCat.{u} A) ≃ₗ[A]
      (ModuleCat.of A (ULift.{w} A) : ModuleCat.{max u w} A) :=
    (ULift.moduleEquiv (R := A) (M := A)).symm
  exact (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv e n).2 hn

/-- Extending scalars along a ring isomorphism carries a dualizing complex to a dualizing complex,
as the isomorphism is a localization at the units. -/
private theorem isDualizingComplex_derivedExtensionScalars_ringEquiv
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] (e : R ≃+* S) (K : DerivedCategory (ModuleCat.{v} R))
    (hK : IsDualizingComplex K) :
    IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars e.toRingHom).obj K) := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have : IsLocalization (IsUnit.submonoid R) R := IsLocalization.self le_rfl
  have : IsLocalization (IsUnit.submonoid R) S :=
    IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))
  exact isDualizingComplex_localization (IsUnit.submonoid R) K hK

/-- **Stacks Project, Tag 0DW9 (2).** A Noetherian Gorenstein ring has a dualizing complex if and
only if the ring itself, placed in degree zero, is a dualizing complex. -/
@[stacks 0DW9 "(2)"]
theorem exists_isDualizingComplex_iff_regularModule
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hA : IsGorensteinRing A) :
    (∃ K : DerivedCategory (ModuleCat.{max u v} A), IsDualizingComplex K) ↔
      IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  classical
  let U := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  constructor
  · rintro ⟨K, hK⟩
    have hW (p : {p : Ideal A // p.IsPrime}) := by
      have : p.1.IsPrime := p.2
      exact IsDualizingComplex.exists_isLocalized_iso_shift_single K hK p.1 (hA p.1)
    choose f hf n he using hW
    have hspan : Ideal.span (Set.range f) = ⊤ := by
      by_contra hnot
      obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hnot
      exact hf ⟨m, hm.isPrime⟩ (hsm (Ideal.subset_span ⟨⟨m, hm.isPrime⟩, rfl⟩))
    refine isDualizingComplex_of_localizations f U hspan fun p => ?_
    let Rf := Localization.Away (f p)
    have hKf : IsDualizingComplex
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A Rf)).obj K) :=
      isDualizingComplex_localization (S := Submonoid.powers (f p)) K hK
    obtain ⟨e⟩ := he p
    let M := (ModuleCat.uliftFunctor.{max u v} Rf).obj (ModuleCat.of Rf Rf)
    have hDn : IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} Rf) (n p)).obj M) :=
      isDualizingComplex_of_iso
        (e ≪≫ ((DerivedCategory.singleFunctors
          (ModuleCat.{max u v} Rf)).shiftIso (-n p) (n p) 0 (by omega)).app M) hKf
    have hUhi : IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} Rf) 0).obj M) :=
      isDualizingComplex_of_iso
        (((DerivedCategory.singleFunctors
          (ModuleCat.{max u v} Rf)).shiftIso (n p) 0 (n p) (by omega)).app M)
        (isDualizingComplex_shift _ hDn (n p))
    exact isDualizingComplex_of_iso (localizationAwayUnitIso (R := A) (f p)).symm
      (isDualizingComplex_single_self_of_ulift Rf hUhi)
  · intro hU
    let e : A ≃+* ULift.{v} A := (ULift.ringEquiv (R := A)).symm
    have : IsNoetherianRing (ULift.{v} A) := isNoetherianRing_of_ringEquiv A e
    exact ⟨(StacksDraft.PseudoCoherence.derivedExtensionScalars e.symm.toRingHom).obj _,
      isDualizingComplex_derivedExtensionScalars_ringEquiv e.symm _
        (isDualizingComplex_derivedExtensionScalars_ringEquiv e U hU)⟩

end Dualizing

end

module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Basic.FirstProperties
public import StacksFrontier.RingTheory.Etale.FilteredColimitStage
public import StacksFrontier.RingTheory.Etale.PushoutLift.Auxiliary
public import StacksFrontier.RingTheory.Smooth.Pi
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRingEtale

/-!
# Results on étale ring maps

This file states Stacks Lemma 00U2, the list of eleven first results on étale ring maps, as one
conjunction, `Algebra.Etale.results_on_etale_ring_maps`.

## Main results

* `Algebra.etale_at_set_eq_etaleLocus`: for an algebra of finite presentation, the set of primes
  `q` at which `R → S` is étale in the sense of Definition 00U1 (there is `g ∉ q` with `R → S_g`
  étale) is Mathlib's `Algebra.etaleLocus R S`.
* `Algebra.Etale.prod_iff`: a product of two algebras is étale if and only if both factors are.
* `Algebra.Etale.results_on_etale_ring_maps`: items (1)–(11) of Stacks 00U2.

## Where each item comes from

1. `Algebra.Etale.of_isLocalizationAway` (Mathlib).
2. `Algebra.Etale.comp` (Mathlib).
3. The instance `Algebra.Etale.baseChange` (Mathlib).
4. `RingHom.Etale.ofLocalizationSpanTarget` (Mathlib).
5. `Algebra.etaleLocus_eq_of_isPushout`, together with `Algebra.etale_at_set_eq_etaleLocus` to
   read the étale locus as the source's set of primes where the map is étale.
6. `Algebra.Smooth.syntomic` (Stacks 00TA), an étale algebra being smooth.
7. `Algebra.FormallyEtale.of_formallyUnramified_of_field` (Mathlib), with
   `Algebra.FinitePresentation.of_finiteType` over the Noetherian ring `k`.
8. `Algebra.Etale.exists_subalgebra_fg` (Mathlib), at the base ring `ℤ`.
9. `Algebra.Etale.exists_etale_stage_of_isColimit_of_smallCategory`.
10. `StacksDraft.ArtinApproximation.etaleDescentAlongLocalization`.
11. `Algebra.Etale.prod_iff`.

## Implementation notes

All rings lie in one universe `u`, as in the source all rings are sets. In (5) the base change
`S' = R' ⊗_R S` is the abstract `Algebra.IsPushout R S R' S'`, of which the tensor product is an
instance. In (8) the ring `R₀` of finite type over `ℤ` is a `ℤ`-subalgebra of `R`, the map
`R₀ → R` along which `S` is the base change being the inclusion. In (9) the filtered colimit is a
filtered diagram `F : J ⥤ CommRingCat` over a small category with a colimiting cocone `c` whose
vertex is `A`. In (10) the ring `S⁻¹A` is any ring `L` with `IsLocalization M L`, and
`B' ≅ S⁻¹B` says that `B'` is, through an `A`-algebra map `B → B'`, the localization of `B` at
the image of `M`. In (11) the product `B' × B''` carries the componentwise algebra structure.

## References

* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

/-- For an algebra `S` of finite presentation over `R`, the set of primes `q` of `S` at which
`R → S` is étale in the sense of Stacks Definition 00U1, that is, for which there is `g ∉ q` with
`R → S_g` étale, is `Algebra.etaleLocus R S`. -/
theorem Algebra.etale_at_set_eq_etaleLocus (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    {q : PrimeSpectrum S | ∃ g ∉ q.asIdeal, Algebra.Etale R (Localization.Away g)} =
      Algebra.etaleLocus R S := by
  ext q
  refine ⟨fun ⟨g, hg, hS⟩ => ?_, fun hq => ?_⟩
  · exact (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hS) hg
  · have : Algebra.IsEtaleAt R q.asIdeal := hq
    exact Algebra.exists_etale_of_isEtaleAt q.asIdeal

/-- A product `S × T` of two `R`-algebras is étale over `R` if and only if both `S` and `T` are
étale over `R`. -/
theorem Algebra.Etale.prod_iff (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    Algebra.Etale R (S × T) ↔ Algebra.Etale R S ∧ Algebra.Etale R T := by
  refine ⟨fun h => ?_, fun ⟨hS, hT⟩ => Stacks.Etale.PushoutLift.etale_prod R S T⟩
  obtain ⟨hU, hSm⟩ := Algebra.Etale.iff_formallyUnramified_and_smooth.mp h
  obtain ⟨hS, hT⟩ := (Algebra.Smooth.prod_iff R S T).mp hSm
  exact ⟨Algebra.Etale.iff_formallyUnramified_and_smooth.mpr
      ⟨.of_surjective (AlgHom.fst R S T) Prod.fst_surjective, hS⟩,
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr
      ⟨.of_surjective (AlgHom.snd R S T) Prod.snd_surjective, hT⟩⟩

/-- **Stacks 00U2, results on étale ring maps.**
1. The ring map `R → R_f` is étale for any ring `R` and any `f ∈ R`.
2. Compositions of étale ring maps are étale.
3. A base change of an étale ring map is étale.
4. Being étale is local: given `R → S` and `g₁, …, gₘ ∈ S` generating the unit ideal with each
   `R → S_{gⱼ}` étale, `R → S` is étale.
5. Given `R → S` of finite presentation and a flat `R → R'`, with `S' = R' ⊗_R S`, the set of
   primes where `R' → S'` is étale is the inverse image under `Spec S' → Spec S` of the set of
   primes where `R → S` is étale.
6. An étale ring map is syntomic, in particular flat.
7. If `S` is of finite type over a field `k`, then `S` is étale over `k` if and only if
   `Ω_{S/k} = 0`.
8. Any étale `R → S` is the base change of an étale `R₀ → S₀` with `R₀` of finite type over `ℤ`.
9. If `A = colim Aᵢ` is a filtered colimit of rings and `A → B` is étale, there are an `i` and an
   étale `Aᵢ → Bᵢ` with `B ≅ A ⊗_{Aᵢ} Bᵢ`.
10. If `S ⊆ A` is multiplicative and `S⁻¹A → B'` is étale, there is an étale `A → B` with
   `B' ≅ S⁻¹B`.
11. A product `B' × B''` of `A`-algebras is étale over `A` if and only if both factors are. -/
@[stacks 00U2 "Items (1)–(11) in order, as one conjunction; all rings in one universe. (1) is
for `Localization.Away f`. (4) has the generators as `g : Fin m → S` with
`Ideal.span (Set.range g) = ⊤`. (5): `S' = R' ⊗_R S` is the abstract `Algebra.IsPushout R S R' S'`,
and 'the set of primes where `R → S` is étale' is Definition 00U1's
`{q | ∃ g ∉ q, R → S_g étale}`. (6): syntomic is `Algebra.Syntomic` (Definition 00SL). (7):
`Ω_{S/k} = 0` is `Subsingleton Ω[S⁄k]`. (8): `R₀` is a `ℤ`-subalgebra of `R` of finite type and
`S ≅ R ⊗_{R₀} S₀` as `R`-algebras. (9): the colimit is a filtered diagram over a small category
with a colimiting cocone `c`, the `Aᵢ`-algebra structure of `A` being the leg `c.ι.app i`, and the
isomorphism is one of `A`-algebras. (10): `S⁻¹A` is any `L` with `IsLocalization M L`, and
`B' ≅ S⁻¹B` is an `A`-algebra map `B → B'` exhibiting `B'` as the localization of `B` at the image
of `M`, compatibly with `L → B'`. (11): the product carries the componentwise structure. Mathlib
also registers item (8) on `Algebra.Etale.exists_subalgebra_fg`."]
theorem Algebra.Etale.results_on_etale_ring_maps :
    -- (1)
    (∀ (R : Type u) [CommRing R] (f : R), Algebra.Etale R (Localization.Away f)) ∧
    -- (2)
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
        [Algebra A C] [IsScalarTower A B C], Algebra.Etale A B → Algebra.Etale B C →
        Algebra.Etale A C) ∧
    -- (3)
    (∀ (R S R' : Type u) [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R'],
        Algebra.Etale R S → Algebra.Etale R' (R' ⊗[R] S)) ∧
    -- (4)
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (m : ℕ) (g : Fin m → S),
        Ideal.span (Set.range g) = ⊤ → (∀ j, Algebra.Etale R (Localization.Away (g j))) →
        Algebra.Etale R S) ∧
    -- (5)
    (∀ (R S R' S' : Type u) [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [CommRing S']
        [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S']
        [IsScalarTower R S S'] [Algebra.IsPushout R S R' S'], Algebra.FinitePresentation R S →
        Module.Flat R R' →
        {q : PrimeSpectrum S' | ∃ g ∉ q.asIdeal, Algebra.Etale R' (Localization.Away g)} =
          PrimeSpectrum.comap (algebraMap S S') ⁻¹'
            {q : PrimeSpectrum S | ∃ g ∉ q.asIdeal, Algebra.Etale R (Localization.Away g)}) ∧
    -- (6)
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S], Algebra.Etale R S →
        Algebra.Syntomic R S ∧ Module.Flat R S) ∧
    -- (7)
    (∀ (k S : Type u) [Field k] [CommRing S] [Algebra k S], Algebra.FiniteType k S →
        (Algebra.Etale k S ↔ Subsingleton Ω[S⁄k])) ∧
    -- (8)
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S], Algebra.Etale R S →
        ∃ (R₀ : Subalgebra ℤ R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
          Algebra.FiniteType ℤ R₀ ∧ Algebra.Etale R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀)) ∧
    -- (9)
    (∀ (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) (c : Cocone F),
        IsColimit c → ∀ (B : Type u) [CommRing B] [Algebra (c.pt : Type u) B],
        Algebra.Etale (c.pt : Type u) B →
        ∃ (i : J) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i : Type u) Bᵢ),
          Algebra.Etale (F.obj i : Type u) Bᵢ ∧
            (letI : Algebra (F.obj i : Type u) (c.pt : Type u) := (c.ι.app i).hom.toAlgebra;
              Nonempty (B ≃ₐ[(c.pt : Type u)] (c.pt : Type u) ⊗[(F.obj i : Type u)] Bᵢ))) ∧
    -- (10)
    (∀ (A : Type u) [CommRing A] (M : Submonoid A) (L : Type u) [CommRing L] [Algebra A L]
        [IsLocalization M L] (B' : Type u) [CommRing B'] [Algebra L B'] [Algebra A B']
        [IsScalarTower A L B'], Algebra.Etale L B' →
        ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra B B'),
          Algebra.Etale A B ∧ IsScalarTower A B B' ∧
            IsLocalization (Algebra.algebraMapSubmonoid B M) B') ∧
    -- (11)
    (∀ (A B' B'' : Type u) [CommRing A] [CommRing B'] [CommRing B''] [Algebra A B']
        [Algebra A B''],
        Algebra.Etale A (B' × B'') ↔ Algebra.Etale A B' ∧ Algebra.Etale A B'') := by
  refine ⟨fun R _ f => .of_isLocalizationAway f, fun A B C _ _ _ _ _ _ _ hB hC => .comp A B C,
    fun R S R' _ _ _ _ _ hS => inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun A B' B'' _ _ _ _ _ => Algebra.Etale.prod_iff A B' B''⟩
  · -- (4)
    intro R S _ _ _ m g hg hS
    refine RingHom.etale_algebraMap.mp
      (RingHom.Etale.ofLocalizationSpanTarget (algebraMap R S) (Set.range g) hg ?_)
    rintro ⟨_, j, rfl⟩
    rw [← IsScalarTower.algebraMap_eq, RingHom.etale_algebraMap]
    exact hS j
  · -- (5)
    intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hfp hflat
    have : Algebra.IsPushout R R' S S' := .symm inferInstance
    have : Algebra.FinitePresentation R' S' :=
      .equiv (Algebra.IsPushout.equiv R R' S S')
    rw [Algebra.etale_at_set_eq_etaleLocus, Algebra.etale_at_set_eq_etaleLocus]
    exact Algebra.etaleLocus_eq_of_isPushout R S R' S'
  · -- (6)
    intro R S _ _ _ hS
    exact ⟨Algebra.Smooth.syntomic R S, inferInstance⟩
  · -- (7)
    intro k S _ _ _ hft
    have : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp hft
    refine ⟨fun _ => inferInstance, fun h => ?_⟩
    have : Algebra.FormallyUnramified k S := ⟨h⟩
    exact ⟨.of_formallyUnramified_of_field k S, inferInstance⟩
  · -- (8)
    intro R S _ _ _ hS
    obtain ⟨R₀, S₀, _, _, hfg, hS₀, e⟩ := Algebra.Etale.exists_subalgebra_fg ℤ R S
    exact ⟨R₀, S₀, inferInstance, inferInstance, (Subalgebra.fg_iff_finiteType R₀).mp hfg, hS₀, e⟩
  · -- (9)
    intro J _ _ F c hc B _ _ hB
    exact Algebra.Etale.exists_etale_stage_of_isColimit_of_smallCategory F hc B
  · -- (10)
    intro A _ M L _ _ _ B' _ _ _ _ hB'
    obtain ⟨D⟩ := StacksDraft.ArtinApproximation.etaleDescentAlongLocalization A M L B' hB'
    exact ⟨D.carrier, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      D.isLocalization⟩

end

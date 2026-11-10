module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.RingHom.Surjective
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.RingTheory.Serre.CohenMacaulay
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's condition along a surjection of Noetherian rings

Let `R → A` be a surjection of Noetherian rings and let `M` be a finite `A`-module, read as an
`R`-module through the map.  This file shows that Serre's condition `(Sₖ)` for `M` over `R`
implies -- in fact is equivalent to -- Serre's condition `(Sₖ)` for `M` over `A`.

The two quantities `(Sₖ)` compares are each unchanged by the surjection, and the file proves
that separately, over a pair of rings with no primes in sight:

* the depth of `M` along the maximal ideal is the same computed over `R` or over `A`, because a
  regular sequence in the maximal ideal of `R` maps to one in the maximal ideal of `A` and every
  sequence in the maximal ideal of `A` lifts back;
* the dimension of the support of `M` is the same, because `R ⧸ ann_R(M) ≅ A ⧸ ann_A(M)` --
  the annihilator over `R` is the preimage of the annihilator over `A`.

Serre's condition is read prime by prime, so the transfer needs one more step: at a prime `𝔮` of
`A` sitting over `𝔭 ⊆ R`, the ring map `R_𝔭 → A_𝔮` is again surjective
(`RingHom.surjective_localRingHom_of_surjective`) and `M_𝔭` and `M_𝔮` are the same module,
because the image of `R ∖ 𝔭` in `A` is exactly `A ∖ 𝔮`
(`Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective`), so `M_𝔮` is a localization of
`M` at `𝔭` as well.

## Main results

* `moduleDepth_eq_of_surjective_algebraMap`
* `moduleSupportDim_eq_of_surjective_algebraMap`
* `propertySkModule_of_surjective_algebraMap` -- `(Sₖ)` over `R` gives `(Sₖ)` over `A`.
* `propertySkModule_two_of_linearEquiv_dual` -- an `A`-module carried by an `R`-linear
  isomorphism onto an `R`-dual `Hom_R(M, R)` satisfies `(S₂)` over `A` as soon as `R` satisfies
  `(S₂)`; `propertySkModule_two_of_linearEquiv_dual_of_isCohenMacaulayRing` is the same with `R`
  Cohen--Macaulay.

## Implementation notes

`PropertySkModule R M k` needs `IsNoetherianRing R` and `Module.Finite R M` to be stated and
`PropertySkModule A M k` needs `IsNoetherianRing A` and `Module.Finite A M`, so all four appear
as hypotheses of `propertySkModule_of_surjective_algebraMap` even though the `R`-side pair
implies the `A`-side one and `Module.Finite A M` implies `Module.Finite R M`: an instance cannot
be derived from `hsurj` before the statement is elaborated.

The `R_𝔭`-module structure on `M_𝔮` is restriction of scalars along `R_𝔭 → A_𝔮`, written
`Module.compHom`; it is local to the proof, which is why no instance is declared for it.

## References

* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P)
* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

/-- **Depth is unchanged by a surjection.**  For a surjection `S → T` of local rings and a
module `N` over `T`, read as an `S`-module through the map, the depth of `N` over `S` and over
`T` agree: a regular sequence in the maximal ideal of `S` maps to one in the maximal ideal of
`T`, and conversely every sequence in the maximal ideal of `T` is the image of one in the
maximal ideal of `S`. -/
public theorem moduleDepth_eq_of_surjective_algebraMap {S T : Type*} [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T] [Algebra S T]
    (hsurj : Function.Surjective (algebraMap S T))
    (N : Type*) [AddCommGroup N] [Module S N] [Module T N] [IsScalarTower S T N] :
    moduleDepth S N = moduleDepth T N := by
  have hm : IsLocalRing.maximalIdeal T =
      (IsLocalRing.maximalIdeal S).map (algebraMap S T) :=
    (IsLocalRing.map_maximalIdeal_of_surjective (algebraMap S T) hsurj).symm
  have hreg : ∀ xs : List S, RingTheory.Sequence.IsRegular N xs ↔
      RingTheory.Sequence.IsRegular N (xs.map (algebraMap S T)) := fun xs =>
    (AddEquiv.refl N).isRegular_congr <| List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ x => (algebraMap_smul T r x).symm
  have hlift : ∀ ys : List T, (∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal T) →
      ∃ xs : List S, (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal S) ∧
        xs.map (algebraMap S T) = ys := by
    intro ys
    induction ys with
    | nil => exact fun _ => ⟨[], by simp, rfl⟩
    | cons y ys ih =>
      intro hmem
      obtain ⟨xs, hxs, hmap⟩ := ih fun t ht => hmem t (List.mem_cons_of_mem _ ht)
      have hy : y ∈ (IsLocalRing.maximalIdeal S).map (algebraMap S T) :=
        hm ▸ hmem y List.mem_cons_self
      obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hy
      exact ⟨x :: xs, by simpa using ⟨hx, hxs⟩, by simp [hmap]⟩
  unfold moduleDepth
  refine le_antisymm (iSup₂_le fun xs hxs => ?_) (iSup₂_le fun ys hys => ?_)
  · refine le_iSup₂_of_le (xs.map (algebraMap S T)) ⟨fun t ht => ?_, (hreg xs).mp hxs.2⟩ (by simp)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    rw [hm]
    exact Ideal.mem_map_of_mem _ (hxs.1 x hx)
  · obtain ⟨xs, hxs, rfl⟩ := hlift ys hys.1
    exact le_iSup₂_of_le xs ⟨hxs, (hreg xs).mpr hys.2⟩ (by simp)

/-- **The dimension of the support is unchanged by a surjection.**  For a surjection `S → T` of
commutative rings and a finite `T`-module `N`, read as an `S`-module through the map, the
annihilator of `N` over `S` is the preimage of its annihilator over `T`, so
`S ⧸ ann_S(N) ≅ T ⧸ ann_T(N)` and the two supports have the same dimension. -/
public theorem moduleSupportDim_eq_of_surjective_algebraMap {S T : Type*} [CommRing S]
    [CommRing T] [Algebra S T] (hsurj : Function.Surjective (algebraMap S T))
    (N : Type*) [AddCommGroup N] [Module S N] [Module T N] [IsScalarTower S T N]
    [Module.Finite T N] :
    moduleSupportDim S N = moduleSupportDim T N := by
  have : Module.Finite S T := Module.Finite.of_surjective (Algebra.linearMap S T) hsurj
  have : Module.Finite S N := Module.Finite.trans T N
  rw [moduleSupportDim_eq_Module_supportDim, moduleSupportDim_eq_Module_supportDim,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  have hann : Module.annihilator S N =
      (Module.annihilator T N).comap (algebraMap S T) := by
    ext r
    simp only [Ideal.mem_comap, Module.mem_annihilator]
    exact forall_congr' fun n => by rw [← algebraMap_smul T r n]
  have hker : RingHom.ker
      ((Ideal.Quotient.mk (Module.annihilator T N)).comp (algebraMap S T)) =
      Module.annihilator S N := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hann]
  exact RingEquiv.ringKrullDim ((Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hsurj)))

/-- **A surjection of rings localizes to a surjection at a prime and its contraction.**  This is
`RingHom.surjective_localRingHom_of_surjective` without that lemma's restriction of `R` and `A`
to a single universe, and for an arbitrary `p` equal to the contraction of `q`. -/
public theorem Localization.surjective_localRingHom {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime] (q : Ideal A)
    [q.IsPrime] (hpq : p = q.comap f) :
    Function.Surjective (Localization.localRingHom p q f hpq) := by
  intro x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
  obtain ⟨r, rfl⟩ := hf a
  obtain ⟨t, ht⟩ := hf s
  have htp : t ∈ p.primeCompl := by
    refine Ideal.mem_primeCompl_iff.mpr fun hmem => ?_
    rw [hpq, Ideal.mem_comap, ht] at hmem
    exact Ideal.mem_primeCompl_iff.mp s.2 hmem
  refine ⟨IsLocalization.mk' (Localization.AtPrime p) r (⟨t, htp⟩ : p.primeCompl), ?_⟩
  rw [Localization.localRingHom_mk']
  congr 1
  exact Subtype.ext ht

/-- **Serre's condition transfers along a surjection of Noetherian rings.**  Let `R → A` be a
surjection of Noetherian rings and let `M` be a finite `A`-module, read as an `R`-module through
the map.  If `M` satisfies `(Sₖ)` over `R`, then it satisfies `(Sₖ)` over `A`.

At a prime `𝔮` of `A`, lying over `𝔭 ⊆ R`, the map `R_𝔭 → A_𝔮` is again surjective and `M_𝔮` is
a localization of `M` at `𝔭` too, so the condition at `𝔮` is the condition at `𝔭`. -/
@[ega "IV 5.7.3" "(vi), special case"]
public theorem propertySkModule_of_surjective_algebraMap {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra R A]
    (hsurj : Function.Surjective (algebraMap R A))
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [Module.Finite A M] (k : ℕ) (h : PropertySkModule R M k) :
    PropertySkModule A M k := by
  intro q _
  obtain ⟨p, hp⟩ : ∃ p : Ideal R, p = q.comap (algebraMap R A) := ⟨_, rfl⟩
  have : p.IsPrime := hp ▸ Ideal.comap_isPrime (algebraMap R A) q
  have : q.LiesOver p := ⟨hp⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have hsurj' : Function.Surjective
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq (p := p) (P := q)]
    exact Localization.surjective_localRingHom (algebraMap R A) hsurj p q hp
  let : Module (Localization.AtPrime p) (LocalizedModule q.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
  have hsmul : ∀ (x : Localization.AtPrime p) (n : LocalizedModule q.primeCompl M),
      x • n = algebraMap (Localization.AtPrime p) (Localization.AtPrime q) x • n :=
    fun _ _ => rfl
  have : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q)
      (LocalizedModule q.primeCompl M) :=
    IsScalarTower.of_algebraMap_smul fun r n => (hsmul r n).symm
  have : IsScalarTower R (Localization.AtPrime p) (LocalizedModule q.primeCompl M) := by
    refine IsScalarTower.of_algebraMap_smul fun r n => ?_
    rw [hsmul, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
        (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply R A (Localization.AtPrime q),
      algebraMap_smul (Localization.AtPrime q), algebraMap_smul A]
  have : IsLocalizedModule p.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl M).restrictScalars R) := by
    have hsub : Algebra.algebraMapSubmonoid A p.primeCompl = q.primeCompl :=
      Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective q p hsurj
    have : IsLocalizedModule (Algebra.algebraMapSubmonoid A p.primeCompl)
        (LocalizedModule.mkLinearMap q.primeCompl M) := hsub ▸ inferInstance
    exact IsLocalizedModule.restrictScalars _ _
  let e : LocalizedModule p.primeCompl M ≃ₗ[Localization.AtPrime p]
      LocalizedModule q.primeCompl M :=
    LinearEquiv.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
      (IsLocalizedModule.linearEquiv p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl M)
        ((LocalizedModule.mkLinearMap q.primeCompl M).restrictScalars R))
  have hd := h p
  rwa [moduleDepth_eq_of_linearEquiv e, moduleSupportDim_eq_of_linearEquiv e,
    moduleDepth_eq_of_surjective_algebraMap hsurj',
    moduleSupportDim_eq_of_surjective_algebraMap hsurj'] at hd

/-- **Serre's condition `(S₂)` for an `R`-dual, read over the quotient.**  Let `R → A` be a
surjection of Noetherian rings with `R` satisfying `(S₂)`, let `M` be a finite `R`-module, and
let `N` be a finite `A`-module carrying an `R`-linear isomorphism onto the dual
`Hom_R(M, R)`.  Then `N` satisfies `(S₂)` over `A`.

This is the elementary route to the `(S₂)` clause of [Stacks, Tag 0E9R] for a surjective
`φ : R → A`:  there `ω^•_{A/R} = RHom_R(A, R)`, so its zeroth cohomology is `Hom_R(A, R)` and
`M = A`.  Over `R` the dual inherits `(S₂)` from `R` itself by [Stacks, Tag 0AV6]; what the
quotient needs on top of that is `propertySkModule_of_surjective_algebraMap`.  The isomorphism
`e` is supplied, and the clause proved, in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingSerreSurjective`.

The isomorphism is a hypothesis rather than `N` being spelled as the dual because the `A`-module
structure on `H^0(ω^•_{A/R})` comes from the complex and is not the one a bare `Hom_R(M, R)`
carries. -/
public theorem propertySkModule_two_of_linearEquiv_dual {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra R A]
    (hsurj : Function.Surjective (algebraMap R A)) (hR : PropertySkRing R 2)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type*) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A N] (e : N ≃ₗ[R] (M →ₗ[R] R)) :
    PropertySkModule A N 2 := by
  have : Module.Finite R A := Module.Finite.of_surjective (Algebra.linearMap R A) hsurj
  have : Module.Finite R N := Module.Finite.trans A N
  exact propertySkModule_of_surjective_algebraMap hsurj N 2 <|
    propertySkModule_of_linearEquiv e 2
      ((propertySk_linearMap_one_two_and_isTorsionFree (R := R) (M := M) (N := R)).2.1
        ((propertySkModule_self_iff_propertySkRing 2).mpr hR))

/-- **Serre's condition `(S₂)` for an `R`-dual over the quotient, with `R` Cohen--Macaulay.**
`propertySkModule_two_of_linearEquiv_dual` with the hypothesis on `R` supplied by
`Stacks.propertySkRing_of_isCohenMacaulayRing`:  a Cohen--Macaulay ring satisfies `(Sₖ)` for
every `k`. -/
public theorem propertySkModule_two_of_linearEquiv_dual_of_isCohenMacaulayRing
    {R A : Type*} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (hsurj : Function.Surjective (algebraMap R A))
    (hR : IsCohenMacaulayRing R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type*) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A N] (e : N ≃ₗ[R] (M →ₗ[R] R)) :
    PropertySkModule A N 2 :=
  propertySkModule_two_of_linearEquiv_dual hsurj
    (Stacks.propertySkRing_of_isCohenMacaulayRing R hR 2) M N e

end

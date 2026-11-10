module

public import StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibre
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Rig.FlatIsLocal

/-!
# Cohen--Macaulay fibres of an adic completion, for a dualizing complex in any universe

`Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height` computes the depth of the local
ring `A'_{P'}/P A'_{P'}` of a fibre of `B → A' = AdicCompletion J B` as the height of the image
of `P'` in `A'/P A'`, but only for a dualizing complex living in `ModuleCat.{u} B`, the module
universe of `B` itself. This file removes that restriction: the dualizing complex may live in
`ModuleCat.{v} B` for an arbitrary universe `v`.

## Main results

* `Stacks.AdicCompletionFibreUniverse.depth_fibre_localization_eq_height_univ`: the depth of
  `A'_{P'}/P A'_{P'}` over `A'_{P'}` is the height of the image of `P'` in `A'/P A'`, for a
  dualizing complex on `B` in an arbitrary module universe.

## Implementation notes

The ring `ULift.{v} B` is a localization of `B` (at the submonoid of units), so
`Dualizing.isDualizingComplex_localization` -- which is cross-universe in both the ring and the
module universe -- carries a dualizing complex in `ModuleCat.{v} B` to one on `ULift.{v} B` in
`ModuleCat.{max u v} (ULift.{v} B)`, that is, in the module universe of `ULift.{v} B` itself.
So the restricted statement applies to `ULift.{v} B`, and the conclusion -- an equality of
elements of `ℕ∞` -- is transported back along `ULift.ringEquiv`.

The transport is `depth_eq_height_of_ringEquiv`, stated for an arbitrary isomorphism
`e : B ≃+* C` of commutative rings and needing no Noetherian, local or dualizing hypothesis: it
takes the conclusion at `C`, for every prime of the completion of `C` lying over the transported
prime, and returns the conclusion at `B`. Its ingredients are an isomorphism of the adic
completions (`exists_adicCompletion_ringEquiv_of_map_eq`), an isomorphism of the localizations
at the two primes (`exists_localizationAtPrime_ringEquiv`), invariance of `Module.depth` under a
ring isomorphism (`depth_quotient_eq_of_ringEquiv`, which trades the depth over the localization
for the depth over the fibre ring by `Module.depth_eq_depth_map_algebraMap` and then applies
`Module.depth_eq_of_ringEquiv`), and invariance of `Ideal.height` under a ring isomorphism
(`height_map_quotientMk_eq_of_ringEquiv`, from Mathlib's `RingEquiv.height_map`).

## References

* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AdicCompletionFibreUniverse

universe u v

/-! ### Transporting an adic completion along a ring isomorphism -/

/-- An isomorphism of rings carrying one ideal to another induces an isomorphism of the adic
completions, compatibly with the canonical maps from the base rings.

Unlike `exists_adicCompletion_ringEquiv_of_flat` this needs no finiteness hypothesis on the
ideal, and unlike `StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv` it applies to an
arbitrary pair of matched ideals rather than to the maximal ideals of local rings. -/
public theorem exists_adicCompletion_ringEquiv_of_map_eq {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map (e : R →+* S) = J) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ x : R, E (algebraMap R (AdicCompletion I R) x) =
        algebraMap S (AdicCompletion J S) (e x) := by
  refine ⟨Rig.adicCompletionCongr e I J hIJ, fun x => AdicCompletion.ext_evalₐ fun n => ?_⟩
  change AdicCompletion.evalₐ J n (adicCompletionMap (e : R →+* S) I J hIJ.le
    (algebraMap R (AdicCompletion I R) x)) = _
  rw [adicCompletionMap_evalₐ, AdicCompletion.algebraMap_apply,
    AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  simp

/-! ### Transporting a localization at a prime along a ring isomorphism -/

/-- The image of a prime ideal under a ring isomorphism, written through the underlying ring
homomorphism, is prime. -/
public theorem isPrime_map_coe_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : Ideal R) [p.IsPrime] : (p.map (e : R →+* S)).IsPrime := by
  rw [Ideal.map_comap_of_equiv e]
  exact Ideal.IsPrime.comap _

/-- An isomorphism of rings carrying a prime to a prime induces an isomorphism of the
localizations at those primes, compatibly with the canonical maps from the base rings. -/
public theorem exists_localizationAtPrime_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (h : p.map (e : R →+* S) = q) :
    ∃ L : Localization.AtPrime p ≃+* Localization.AtPrime q,
      ∀ x : R, L (algebraMap R (Localization.AtPrime p) x) =
        algebraMap S (Localization.AtPrime q) (e x) := by
  have hcomap : q.comap (e : R →+* S) = p := by
    rw [← h, Ideal.comap_map_of_bijective (e : R →+* S) e.bijective]
  subst hcomap
  exact ⟨IsLocalization.ringEquivOfRingEquiv (M := (q.comap (e : R →+* S)).primeCompl)
    (T := q.primeCompl) _ _ e (e.map_primeCompl_comap_eq q),
    fun x => IsLocalization.ringEquivOfRingEquiv_eq _ x⟩

/-! ### Transporting depth and height along a ring isomorphism -/

/-- The depth of a quotient of a local ring along the maximal ideal is invariant under a ring
isomorphism carrying the ideal along. -/
private theorem depth_quotient_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (L : R ≃+* S) (I : Ideal R) (I' : Ideal S)
    (hI : I.map (L : R →+* S) = I') :
    Module.depth R (IsLocalRing.maximalIdeal R) (R ⧸ I) =
      Module.depth S (IsLocalRing.maximalIdeal S) (S ⧸ I') := by
  have hsurjR : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have hsurjS : Function.Surjective (algebraMap S (S ⧸ I')) := Ideal.Quotient.mk_surjective
  rw [Module.depth_eq_depth_map_algebraMap hsurjR (IsLocalRing.maximalIdeal R) (R ⧸ I),
    Module.depth_eq_depth_map_algebraMap hsurjS (IsLocalRing.maximalIdeal S) (S ⧸ I'),
    Module.depth_eq_of_ringEquiv (Ideal.quotientEquiv I I' L hI.symm)]
  congr 1
  have hcomp : ((Ideal.quotientEquiv I I' L hI.symm : (R ⧸ I) ≃+* (S ⧸ I')) :
        (R ⧸ I) →+* (S ⧸ I')).comp (algebraMap R (R ⧸ I)) =
      (algebraMap S (S ⧸ I')).comp (L : R →+* S) := by
    ext x
    exact Ideal.quotientEquiv_mk I I' L hI.symm x
  rw [Ideal.map_map, hcomp, ← Ideal.map_map,
    IsLocalRing.map_maximalIdeal_of_surjective (L : R →+* S) L.surjective]

/-- The height of the image of an ideal in a quotient is invariant under a ring isomorphism
carrying both the ideal and the ideal defining the quotient along. -/
private theorem height_map_quotientMk_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (E : R ≃+* S) (I : Ideal R) (I' : Ideal S) (hI : I.map (E : R →+* S) = I') (p : Ideal R) :
    (p.map (Ideal.Quotient.mk I)).height =
      ((p.map (E : R →+* S)).map (Ideal.Quotient.mk I')).height := by
  have hcomp : ((Ideal.quotientEquiv I I' E hI.symm : (R ⧸ I) ≃+* (S ⧸ I')) :
        (R ⧸ I) →+* (S ⧸ I')).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk I').comp (E : R →+* S) := by
    ext x
    exact Ideal.quotientEquiv_mk I I' E hI.symm x
  have hmap : (p.map (Ideal.Quotient.mk I)).map
      ((Ideal.quotientEquiv I I' E hI.symm : (R ⧸ I) ≃+* (S ⧸ I')) : (R ⧸ I) →+* (S ⧸ I')) =
      (p.map (E : R →+* S)).map (Ideal.Quotient.mk I') := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  rw [← hmap]
  exact (RingEquiv.height_map (Ideal.quotientEquiv I I' E hI.symm)
    (p.map (Ideal.Quotient.mk I))).symm

/-! ### The depth-equals-height identity transports along a ring isomorphism -/

/-- **The depth-equals-height identity for a fibre of an adic completion transports along an
isomorphism of the base rings.** Given `e : B ≃+* C` matching `J` with `JC` and `P` with `PC`,
the identity at `B` for a prime `P'` of `AdicCompletion J B` follows from the identity at `C`
for every prime of `AdicCompletion JC C` lying over `PC`.

No Noetherian, local or dualizing hypothesis is involved: this is pure transport. -/
private theorem depth_eq_height_of_ringEquiv {B C : Type*} [CommRing B] [CommRing C]
    (e : B ≃+* C) {J P : Ideal B} [P.IsPrime] {JC PC : Ideal C} [PC.IsPrime]
    (hJ : J.map (e : B →+* C) = JC) (hP : P.map (e : B →+* C) = PC)
    (P' : Ideal (AdicCompletion J B)) [P'.IsPrime] [P'.LiesOver P]
    (H : ∀ (P'C : Ideal (AdicCompletion JC C)) (_ : P'C.IsPrime), P'C.LiesOver PC →
        Module.depth (Localization.AtPrime P'C)
            (IsLocalRing.maximalIdeal (Localization.AtPrime P'C))
            (Localization.AtPrime P'C ⧸ PC.map (algebraMap C (Localization.AtPrime P'C))) =
          (P'C.map (Ideal.Quotient.mk (PC.map (algebraMap C (AdicCompletion JC C))))).height) :
    Module.depth (Localization.AtPrime P') (IsLocalRing.maximalIdeal (Localization.AtPrime P'))
        (Localization.AtPrime P' ⧸ P.map (algebraMap B (Localization.AtPrime P'))) =
      (P'.map (Ideal.Quotient.mk (P.map (algebraMap B (AdicCompletion J B))))).height := by
  obtain ⟨E, hE⟩ := exists_adicCompletion_ringEquiv_of_map_eq e J JC hJ
  -- the square relating the two completions over their base rings, and its inverse
  have hsq : (E : AdicCompletion J B →+* AdicCompletion JC C).comp
      (algebraMap B (AdicCompletion J B)) =
      (algebraMap C (AdicCompletion JC C)).comp (e : B →+* C) :=
    RingHom.ext fun x => hE x
  have hsymm : (E.symm : AdicCompletion JC C →+* AdicCompletion J B).comp
      (algebraMap C (AdicCompletion JC C)) =
      (algebraMap B (AdicCompletion J B)).comp (e.symm : C →+* B) :=
    RingHom.ext fun y => by
    have hy := hE (e.symm y)
    rw [RingEquiv.apply_symm_apply] at hy
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [← hy, RingEquiv.symm_apply_apply]
  -- the transported prime of the completion lies over `PC`
  have hP'Cp : (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C)).IsPrime :=
    isPrime_map_coe_of_ringEquiv E P'
  have hunder : (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C)).comap
      (algebraMap C (AdicCompletion JC C)) = PC := by
    have h1 : P'.map (E : AdicCompletion J B →+* AdicCompletion JC C) =
        P'.comap (E.symm : AdicCompletion JC C →+* AdicCompletion J B) :=
      Ideal.map_comap_of_equiv E
    have h2 : P.comap (e.symm : C →+* B) = PC := by
      rw [← hP]
      exact (Ideal.map_comap_of_equiv e).symm
    rw [h1, Ideal.comap_comap, hsymm, ← Ideal.comap_comap, ← Ideal.under_def,
      ← Ideal.LiesOver.over (p := P) (P := P'), h2]
  have hLO : (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C)).LiesOver PC :=
    ⟨hunder.symm⟩
  -- the isomorphism of the localizations at the two primes, read over the base rings
  obtain ⟨L, hL⟩ := exists_localizationAtPrime_ringEquiv E P'
    (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C)) rfl
  have hcompL : (L : Localization.AtPrime P' →+* Localization.AtPrime
        (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C))).comp
      (algebraMap B (Localization.AtPrime P')) =
      (algebraMap C (Localization.AtPrime
        (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C)))).comp (e : B →+* C) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [IsScalarTower.algebraMap_apply B (AdicCompletion J B) (Localization.AtPrime P'), hL, hE,
      ← IsScalarTower.algebraMap_apply]
  -- the two ideals of the localization, and the two ideals of the completion, correspond
  have hIL : (P.map (algebraMap B (Localization.AtPrime P'))).map
      (L : Localization.AtPrime P' →+* Localization.AtPrime
        (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C))) =
      PC.map (algebraMap C (Localization.AtPrime
        (P'.map (E : AdicCompletion J B →+* AdicCompletion JC C)))) := by
    rw [Ideal.map_map, hcompL, ← Ideal.map_map, hP]
  have hIE : (P.map (algebraMap B (AdicCompletion J B))).map
      (E : AdicCompletion J B →+* AdicCompletion JC C) =
      PC.map (algebraMap C (AdicCompletion JC C)) := by
    rw [Ideal.map_map, hsq, ← Ideal.map_map, hP]
  rw [depth_quotient_eq_of_ringEquiv L _ _ hIL,
    height_map_quotientMk_eq_of_ringEquiv E _ _ hIE P']
  exact H _ hP'Cp hLO

/-! ### The depth of the fibres, for a dualizing complex in an arbitrary universe -/

/-- **The depth of a local ring of a fibre of an adic completion is the height of the
corresponding prime of the fibre, for a dualizing complex in any module universe.** For `B` a
Noetherian ring carrying a dualizing complex in `ModuleCat.{v} B` for an arbitrary
universe `v`, `J ⊆ B` an ideal, `A' = AdicCompletion J B` and `P'` a prime of `A'` over a prime
`P` of `B`, the depth of `A'_{P'}/P A'_{P'}` over `A'_{P'}` is the height of the image of `P'`
in `A'/P A'`.

This is `Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height` with the module universe
of the dualizing complex freed from the universe of `B`. -/
theorem depth_fibre_localization_eq_height_univ
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    {K : DerivedCategory (ModuleCat.{v} B)} (hK : Dualizing.IsDualizingComplex K)
    (J : Ideal B) (P : Ideal B) [P.IsPrime]
    (P' : Ideal (AdicCompletion J B)) [P'.IsPrime] [P'.LiesOver P] :
    Module.depth (Localization.AtPrime P') (IsLocalRing.maximalIdeal (Localization.AtPrime P'))
        (Localization.AtPrime P' ⧸ P.map (algebraMap B (Localization.AtPrime P'))) =
      (P'.map (Ideal.Quotient.mk (P.map (algebraMap B (AdicCompletion J B))))).height := by
  -- `ULift.{v} B` is a localization of `B`, so it carries a dualizing complex in its own
  -- module universe `max u v`
  let e : B ≃+* ULift.{v} B := ULift.ringEquiv.symm
  let _ : Algebra B (ULift.{v} B) := e.toRingHom.toAlgebra
  let M₀ : Submonoid (ULift.{v} B) := IsUnit.submonoid (ULift.{v} B)
  let M : Submonoid B := M₀.map e.symm.toRingHom
  have hloc : IsLocalization M (ULift.{v} B) :=
    IsLocalization.isLocalization_of_base_ringEquiv M₀ (ULift.{v} B) e.symm
  have hN : IsNoetherianRing (ULift.{v} B) :=
    IsLocalization.isNoetherianRing M (ULift.{v} B) inferInstance
  have hKC := Dualizing.isDualizingComplex_localization (B := ULift.{v} B) M K hK
  have hPC : (P.map (e : B →+* ULift.{v} B)).IsPrime := isPrime_map_coe_of_ringEquiv e P
  exact depth_eq_height_of_ringEquiv e rfl rfl P' fun P'C _ _ =>
    Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height hKC _ _ P'C

end Stacks.AdicCompletionFibreUniverse

end

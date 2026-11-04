module

public import StacksFrontier.RingTheory.FormallySmooth.Topological

/-!
# Adic formal smoothness depends only on the isomorphism class of the arrow

Formal smoothness of `φ : R →+* S` for the `n`-adic topology is a property of the arrow `φ`
together with the ideal `n`, not of the particular rings presenting it. Given isomorphisms
`eR : R ≃+* R'` and `eS : S ≃+* S'` which carry `φ` to `φ'`, the lifting problems for `φ'` and
the ideal `n.map eS` are the lifting problems for `φ` and `n` read through the isomorphisms, so
the two adic formal smoothness statements agree.

This is the transport that identifies the stalk map of a morphism of schemes with a map of
localizations: the two vertical isomorphisms of such a square are isomorphisms of rings and not
algebra maps over a common base, so the fixed-base transport
`RingHom.FormallySmoothNAdic.of_algEquiv` does not apply.

## Main results

* `RingHom.FormallySmoothNAdic.of_arrowEquiv`: transport along an isomorphism of arrows.
* `RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq`: the same with the transported ideal
  supplied by hand, which is how the local case with `n` a maximal ideal is used.

## Implementation notes

The test-ring universe of `RingHom.FormallySmoothNAdic` is a parameter independent of the
universes of the source and the target, and it is left untouched here: a lifting problem for
`φ'` is turned into one for `φ` over the *same* test ring. The source and target universes may
differ on the two sides.

## References

* [Stacks Project, Tag 07EE](https://stacks.math.columbia.edu/tag/07EE)
* [Stacks Project, Tag 07NI](https://stacks.math.columbia.edu/tag/07NI)
-/

public section

universe u v w v' w'

namespace RingHom

/-- **Adic formal smoothness transports along an isomorphism of arrows.** If `eR : R ≃+* R'` and
`eS : S ≃+* S'` satisfy `φ' ∘ eR = eS ∘ φ` and `φ` is formally smooth for the `n`-adic topology,
then `φ'` is formally smooth for the `n.map eS`-adic topology.

A lifting problem for `φ'` is transported to one for `φ` by composing the two given maps with
`eR` and `eS`, and the resulting lift is composed back with `eS.symm`. -/
theorem FormallySmoothNAdic.of_arrowEquiv {R : Type v} {S : Type w} {R' : Type v'} {S' : Type w'}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] {φ : R →+* S} {φ' : R' →+* S'}
    {n : Ideal S} (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : φ'.comp eR.toRingHom = eS.toRingHom.comp φ)
    (h : FormallySmoothNAdic.{u, v, w} φ n) :
    FormallySmoothNAdic.{u, v', w'} φ' (n.map eS.toRingHom) := by
  intro A _ J hJ f ψ hsq hk
  obtain ⟨k, hk1, hkle⟩ := hk
  have hpt : ∀ a : R, φ' (eR a) = eS (φ a) := RingHom.congr_fun hcomm
  have hsqpt : ∀ b : R', ψ (φ' b) = Ideal.Quotient.mk J (f b) := RingHom.congr_fun hsq
  have hsq' : (ψ.comp eS.toRingHom).comp φ = (Ideal.Quotient.mk J).comp (f.comp eR.toRingHom) :=
    RingHom.ext fun x => (congrArg ψ (hpt x)).symm.trans (hsqpt (eR x))
  have hker : n ^ k ≤ RingHom.ker (ψ.comp eS.toRingHom) := by
    intro x hx
    have hmem : eS x ∈ n.map eS.toRingHom ^ k := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    simpa [RingHom.mem_ker] using hkle hmem
  obtain ⟨g, hgψ, hgφ⟩ :=
    h A J hJ (f.comp eR.toRingHom) (ψ.comp eS.toRingHom) hsq' ⟨k, hk1, hker⟩
  have hgψpt : ∀ b : S, Ideal.Quotient.mk J (g b) = ψ (eS b) := RingHom.congr_fun hgψ
  have hgφpt : ∀ a : R, g (φ a) = f (eR a) := RingHom.congr_fun hgφ
  refine ⟨g.comp eS.symm.toRingHom, RingHom.ext fun y => ?_, RingHom.ext fun y => ?_⟩
  · exact (hgψpt (eS.symm y)).trans (congrArg ψ (eS.apply_symm_apply y))
  · have h1 : φ' y = eS (φ (eR.symm y)) :=
      (congrArg φ' (eR.apply_symm_apply y)).symm.trans (hpt (eR.symm y))
    have hy : eS.symm (φ' y) = φ (eR.symm y) :=
      (congrArg eS.symm h1).trans (eS.symm_apply_apply _)
    exact (congrArg g hy).trans
      ((hgφpt (eR.symm y)).trans (congrArg f (eR.apply_symm_apply y)))

/-- **Adic formal smoothness transports along an isomorphism of arrows**, with the ideal
upstairs named. This is the form used when `n` and `n'` are the maximal ideals of two local
rings identified by `eS`. -/
theorem FormallySmoothNAdic.of_arrowEquiv_of_map_eq {R : Type v} {S : Type w} {R' : Type v'}
    {S' : Type w'} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] {φ : R →+* S}
    {φ' : R' →+* S'} {n : Ideal S} {n' : Ideal S'} (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : φ'.comp eR.toRingHom = eS.toRingHom.comp φ) (hn : n.map eS.toRingHom = n')
    (h : FormallySmoothNAdic.{u, v, w} φ n) :
    FormallySmoothNAdic.{u, v', w'} φ' n' :=
  hn ▸ FormallySmoothNAdic.of_arrowEquiv eR eS hcomm h

end RingHom

end

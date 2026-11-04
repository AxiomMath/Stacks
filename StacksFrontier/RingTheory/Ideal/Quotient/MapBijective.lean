module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Bijectivity of the quotient maps attached to a ring map

For a ring map `f : R → S` and an ideal `I` of `R`, the induced map
`R ⧸ I → S ⧸ I.map f` is `Ideal.quotientMap (I.map f) f Ideal.le_comap_map`. Bijectivity of
that map says that `f` identifies `R ⧸ I` with `S ⧸ I S`, and it is inherited by every larger
ideal: if it holds for `I` then it holds for any `K ⊇ I`, because `R ⧸ K` and `S ⧸ K S` are the
quotients of `R ⧸ I` and `S ⧸ I S` by the images of `K`, which correspond to each other under
the isomorphism.

## Main results

* `Ideal.quotientMap_bijective_of_le`: bijectivity of the quotient map attached to `I` passes to
  any ideal containing `I`.
-/

@[expose] public section

/-- If the map `R ⧸ I → S ⧸ I S` induced by a ring map `f : R → S` is bijective, then so is the
map `R ⧸ K → S ⧸ K S` induced by `f` for every ideal `K` containing `I`. -/
public theorem Ideal.quotientMap_bijective_of_le {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I K : Ideal R} (hIK : I ≤ K)
    (h : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap (K.map f) f Ideal.le_comap_map) := by
  let q := Ideal.quotientMap (I.map f) f Ideal.le_comap_map
  have hm : (K.map (Ideal.Quotient.mk I)).map q =
      (K.map f).map (Ideal.Quotient.mk (I.map f)) := by
    rw [Ideal.map_map, Ideal.map_map, Ideal.quotientMap_comp_mk]
  refine ⟨Ideal.quotientMap_injective' fun r hr ↦ ?_, fun x ↦ ?_⟩
  · have hx : q (Ideal.Quotient.mk I r) ∈ (K.map (Ideal.Quotient.mk I)).map q := by
      rw [hm]
      exact Ideal.mem_map_of_mem _ hr
    have hx' : Ideal.Quotient.mk I r ∈ K.map (Ideal.Quotient.mk I) :=
      (Ideal.apply_mem_of_equiv_iff (f := RingEquiv.ofBijective q h)).mp hx
    exact Ideal.comap_map_mk hIK ▸ hx'
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, hr⟩ := h.2 (Ideal.Quotient.mk (I.map f) s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨Ideal.Quotient.mk K r, ?_⟩
    simpa using congrArg (Ideal.Quotient.factor (Ideal.map_mono hIK)) hr

end

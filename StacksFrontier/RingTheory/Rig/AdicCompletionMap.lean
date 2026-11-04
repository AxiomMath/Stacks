module

public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# Functoriality of the map on adic completions

`adicCompletionMap f I J h` is the map `AdicCompletion I R → AdicCompletion J S` induced by a
ring homomorphism `f : R →+* S` carrying `I` into `J`. This file records that the assignment is
functorial; its level-`n` evaluation is `adicCompletionMap_evalₐ`.

## Main results

* `Rig.adicCompletionMap_comp` and `Rig.adicCompletionMap_id`: the assignment is functorial.
-/

@[expose] public section

namespace Rig

/-- `adicCompletionMap` is functorial. -/
theorem adicCompletionMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (hf : I.map f ≤ J) (hg : J.map g ≤ K) (hgf : I.map (g.comp f) ≤ K) :
    (adicCompletionMap g J K hg).comp (adicCompletionMap f I J hf) =
      adicCompletionMap (g.comp f) I K hgf := by
  ext x : 1
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [RingHom.comp_apply, adicCompletionMap_evalₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  rfl

/-- `adicCompletionMap` of the identity is the identity. -/
theorem adicCompletionMap_id {R : Type*} [CommRing R] (I : Ideal R)
    (h : I.map (RingHom.id R) ≤ I) :
    adicCompletionMap (RingHom.id R) I I h = RingHom.id _ := by
  ext x : 1
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [adicCompletionMap_evalₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  simp only [RingHom.id_apply]
  rw [← hr]
  rfl

end Rig

end

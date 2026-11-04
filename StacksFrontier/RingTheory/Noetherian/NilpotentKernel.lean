module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Noetherian.OfPrime
import StacksCore.Tactic.StacksAttribute

/-!
# Noetherianity through a nilpotent kernel

A surjection of rings whose kernel is finitely generated and contained in the nilradical
reflects the Noetherian property: if the target is Noetherian, so is the source. For a
finitely generated ideal, being contained in the nilradical is the same as being nilpotent
(`Ideal.FG.isNilpotent_iff_le_nilradical`), so this is the familiar statement that a
Noetherian ring stays Noetherian under a nilpotent thickening with finitely generated
kernel.

The proof is `IsNoetherianRing.of_prime`: it suffices to finitely generate the primes, and
a prime contains the nilradical, hence the kernel, so lifting generators of its image and
adjoining generators of the kernel recovers it.

Mathlib has the module-level analogue `Module.finite_of_surjective_of_ker_le_nilradical`,
but not this ring-level statement.

## Main results

* `Ideal.fg_of_fg_map_of_fg_ker_of_surjective` — an ideal containing the kernel of a
  surjection is finitely generated as soon as its image and the kernel are.
* `isNoetherianRing_of_surjective_fg_le_nilradical_ker` and
  `isNoetherianRing_of_surjective_fg_nilpotent_ker` — the surjection form.
* `isNoetherianRing_of_fg_nilpotent` — the quotient form.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An ideal containing the kernel of a surjective ring homomorphism is finitely generated
as soon as its image and that kernel are: lifting a finite generating set of the image and
adjoining a finite generating set of the kernel recovers the ideal. -/
public theorem Ideal.fg_of_fg_map_of_fg_ker_of_surjective {f : R →+* S}
    (hf : Function.Surjective f) {I : Ideal R} (hIker : RingHom.ker f ≤ I)
    (hker : (RingHom.ker f).FG) (hmap : (I.map f).FG) : I.FG := by
  classical
  obtain ⟨s, hs⟩ := hmap
  set t : Finset R := s.image (Function.surjInv hf) with ht
  have himage : f '' (t : Set R) = (s : Set S) := by
    rw [ht, Finset.coe_image, Set.image_image]
    simp [Function.surjInv_eq hf]
  have hmapt : (Ideal.span (t : Set R)).map f = I.map f := by
    rw [Ideal.map_span, himage, hs]
  have hsup : Ideal.span (t : Set R) ⊔ RingHom.ker f = I := by
    have := (Ideal.map_eq_iff_sup_ker_eq_of_surjective f hf).mp hmapt
    rwa [sup_eq_left.mpr hIker] at this
  exact hsup ▸ Submodule.FG.sup (Submodule.fg_span t.finite_toSet) hker

/-- A surjection of rings whose kernel is finitely generated and contained in the nilradical
reflects Noetherianity. -/
public theorem isNoetherianRing_of_surjective_fg_le_nilradical_ker {f : R →+* S}
    (hf : Function.Surjective f) (hfg : (RingHom.ker f).FG)
    (hn : RingHom.ker f ≤ nilradical R) [IsNoetherianRing S] : IsNoetherianRing R := by
  refine IsNoetherianRing.of_prime fun p hp ↦ ?_
  have : p.IsPrime := hp
  exact Ideal.fg_of_fg_map_of_fg_ker_of_surjective hf (hn.trans (nilradical_le_prime p)) hfg
    (Ideal.fg_of_isNoetherianRing _)

/-- A nilpotent thickening with finitely generated kernel of a Noetherian ring is
Noetherian. -/
public theorem isNoetherianRing_of_surjective_fg_nilpotent_ker (f : R →+* S)
    (hf : Function.Surjective f) (hfg : (RingHom.ker f).FG)
    (hn : IsNilpotent (RingHom.ker f)) [IsNoetherianRing S] : IsNoetherianRing R :=
  isNoetherianRing_of_surjective_fg_le_nilradical_ker hf hfg
    (hfg.isNilpotent_iff_le_nilradical.mp hn)

/-- A ring with a finitely generated nilpotent ideal whose quotient is Noetherian is
Noetherian. -/
public theorem isNoetherianRing_of_fg_nilpotent {I : Ideal R} (hfg : I.FG)
    (hn : IsNilpotent I) [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing R := by
  refine isNoetherianRing_of_surjective_fg_nilpotent_ker (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective ?_ ?_ <;> rw [Ideal.mk_ker]
  · exact hfg
  · exact hn

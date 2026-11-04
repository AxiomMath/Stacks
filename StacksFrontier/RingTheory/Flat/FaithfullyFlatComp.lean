module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Faithful flatness of a composite ring homomorphism

Mathlib proves that faithful flatness composes for algebras,
`Module.FaithfullyFlat.trans`. This file records the same fact for ring homomorphisms, with the
three rings allowed to live in different universes.

`RingHom.FaithfullyFlat.stableUnderComposition` is the same statement for three rings in one
universe, which is what the local-property API of `RingHom` is phrased for; the proof here is
universe-polymorphic, `Module.FaithfullyFlat.trans` being so.

## Main results

* `RingHom.FaithfullyFlat.comp`
-/

@[expose] public section

namespace RingHom.FaithfullyFlat

/-- A composite of faithfully flat ring homomorphisms is faithfully flat. -/
@[ega "0 6.6.4"]
theorem comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.FaithfullyFlat) (hg : g.FaithfullyFlat) : (g.comp f).FaithfullyFlat := by
  algebraize [f, g, g.comp f]
  rw [← RingHom.algebraMap_toAlgebra (g.comp f), RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.trans R S T

end RingHom.FaithfullyFlat

end

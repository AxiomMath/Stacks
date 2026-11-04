module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic

/-!
# The Frobenius-crystal situation

A global crystalline situation is a *Frobenius-crystal situation* when its divided power base
is affine, its divided power ideal contains the fixed prime `p`, and the base ring carries a
divided power endomorphism lifting the absolute Frobenius modulo `p`. This is the standing
data for the theory of `F`-crystals.

## Main definitions

* `Crystalline.FCrystalSituation` — the affine global crystalline situation together with its
  Frobenius lift.

## Implementation notes

For an affine base the ring `A` is canonically the ring of global sections of `S`, and its
divided powers are the divided powers on global sections of the ideal sheaf. Congruence modulo
`pA` is expressed as divisibility of the difference by `p`.

## References

* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Crystalline

/-- A global crystalline situation over an affine divided power base, with the distinguished
prime in its divided power ideal and a divided power endomorphism of the base ring lifting the
absolute Frobenius modulo that prime.

See [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2). -/
@[stacks 07N2]
public structure FCrystalSituation where
  /-- The underlying global crystalline situation. -/
  global : GlobalCrystallineSituation.{u}
  /-- The base is affine, hence is the spectrum of its global sections. -/
  [affine : IsAffine global.S.scheme]
  /-- The distinguished prime belongs to the divided power ideal. -/
  prime_mem : (global.p : global.S.scheme.sheaf.obj.obj (op ⊤)) ∈
    global.S.ideal.obj (op ⊤)
  /-- A divided power endomorphism of the base ring. -/
  sigma : DividedPowers.DPMorphism (global.S.dividedPowers.dividedPowers (op ⊤))
    (global.S.dividedPowers.dividedPowers (op ⊤))
  /-- The endomorphism reduces to the absolute Frobenius modulo `p`. -/
  sigma_mod_prime : ∀ x : global.S.scheme.sheaf.obj.obj (op ⊤),
    ∃ y : global.S.scheme.sheaf.obj.obj (op ⊤), sigma x - x ^ global.p = global.p * y

attribute [instance] FCrystalSituation.affine

end Crystalline

end

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem

/-!
# Invertible objects of `Coh(X, 𝓘)`

Let `X` be a scheme and `𝓘` a quasi-coherent ideal sheaf. An object `(𝓛ₙ)` of `Coh(X, 𝓘)` is
*invertible* when each term `𝓛ₙ` is an invertible module over the `(n + 1)`-st infinitesimal
neighbourhood `Yₙ = V(𝓘 ^ (n + 1))`, equivalently when `𝓛ₙ` is the direct image of an invertible
module on `Yₙ`. This is the notion in which the modules `(𝓛ₙ)` of [Stacks, Tag 0EHE] form an
invertible object of `Coh(U, I𝒪_U)`.

Invertibility must be read over `Yₙ` and not over `𝒪_X`: a term of a coherent adic system is
annihilated by `𝓘 ^ (n + 1)`, so over `𝒪_X` the only invertible such term is the zero module
when `𝓘` is a proper ideal. This is the same correction `Stacks.Algebraization`'s
`IsFiniteLocallyFreeAdic` makes to the local-freeness hypothesis of Stacks 0EL6, and the two
predicates are stated in the same shape.

## Main definitions

* `Stacks.Coherent.IsInvertibleAdic` — invertibility of a coherent adic system, termwise over
  the infinitesimal neighbourhoods.

## Main results

* `Stacks.Coherent.IsInvertibleAdic.of_iso` — invertibility depends only on the underlying
  inverse system, so it is a property of the isomorphism class in `Coh(X, 𝓘)`.

## Implementation notes

Invertibility of an object of a monoidal category is `CategoryTheory.MonoidalCategory.IsInvertible`
(`StacksFrontier/CategoryTheory/Monoidal/InvertibleObject.lean`), and `Coh(X, 𝓘)` does carry a
monoidal structure, the termwise tensor product over `𝒪_X / 𝓘 ^ (n + 1)`. That route is not taken
here. Equipping `Coh(X, 𝓘)` with it would require, for every pair of systems, that the termwise
tensor product again satisfy all three clauses of `IsCoherentAdicSystem` — in particular the
clause pinning down the transition maps, whose proof needs the compatibility of
`idealPowerQuotient` with tensor products — and then the associator, unitors and pentagon
coherence for the resulting operation. The condition below is instead the termwise reading of
that invertibility — a system is monoidally invertible exactly when its terms are invertible
over the `Yₙ` — it reuses `Stacks.Ample.IsInvertibleModule` on the subschemes `Yₙ`, and it is
what the proof sketch of Tag 0EHE uses: that sketch passes at once to the invertibility of a
single term, `𝓛₂`.

The transition maps need no separate compatibility clause: the third clause of
`Stacks.Coherent.IsCoherentAdicSystem` already identifies `𝓛ₙ` with
`𝓛ₙ₊₁ / 𝓘 ^ (n + 1) 𝓛ₙ₊₁` *through* the transition map, so a system satisfying the condition
below has the transition maps of a compatible family of invertible modules.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

/-- An object of `Coh(X, 𝓘)` is **invertible** when each term `𝓛ₙ` is the direct image of an
invertible module on the infinitesimal neighbourhood cut out by `𝓘 ^ (n + 1)`, which is the
scheme-theoretic reading of "invertible over `𝒪_X / 𝓘 ^ (n + 1)`". -/
public def IsInvertibleAdic {X : Scheme.{u}} (I : X.IdealSheafData)
    (L : CoherentAdicSystems I) : Prop :=
  ∀ n : ℕ, ∃ M : (I ^ (n + 1)).subscheme.Modules,
    Stacks.Ample.IsInvertibleModule (I ^ (n + 1)).subscheme M ∧
      Nonempty ((Scheme.Modules.pushforward (I ^ (n + 1)).subschemeι).obj M ≅ L.obj.obj (op n))

/-- Invertibility of a coherent adic system depends only on the underlying inverse system. -/
public theorem IsInvertibleAdic.of_iso {X : Scheme.{u}} {I : X.IdealSheafData}
    {L L' : CoherentAdicSystems I} (h : IsInvertibleAdic I L) (e : L.obj ≅ L'.obj) :
    IsInvertibleAdic I L' := fun n => by
  obtain ⟨M, hM, ⟨f⟩⟩ := h n
  exact ⟨M, hM, ⟨f ≪≫ e.app (op n)⟩⟩

end Stacks.Coherent

end

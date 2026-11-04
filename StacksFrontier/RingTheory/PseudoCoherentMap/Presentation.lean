module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Module
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs

/-! # Polynomial presentations of a pseudo-coherent ring map

`Algebra.PseudoCoherent R S` says that `S` is a quotient `R[x₁, …, x_n] ⧸ I` of a polynomial
algebra such that the `R[x₁, …, x_n]`-module `R[x₁, …, x_n] ⧸ I` has a resolution by finite free
modules, and such a resolution then exists over every finite polynomial presentation of `S`
(`Algebra.PseudoCoherent.nonempty_finiteFreeModuleResolution`). This file reads the condition in a
derived category: for a surjection `α : R[x₁, …, x_n] → S`, the ring map `R → S` is
pseudo-coherent exactly when `S` is a pseudo-coherent `R[x₁, …, x_n]`-module, for any model of the
derived category of `R[x₁, …, x_n]`-modules.

By Stacks 064T pseudo-coherence of a module over a single ring is the existence of a resolution by
finite free modules. That is the datum of the definition, read for `S` instead of the isomorphic
module `R[x₁, …, x_n] ⧸ I`
(`Algebra.PseudoCoherent.nonempty_finiteFreeModuleResolution_quotient_iff_compHom`), so the
equivalence needs no transport of objects of the derived category along restriction of scalars.

## Main results

* `Algebra.pseudoCoherent_iff_isModulePseudoCoherent` — a ring map is pseudo-coherent exactly
  when its target is a pseudo-coherent module over one finite polynomial presentation of it, in
  any model of the derived category.
* `Algebra.PseudoCoherent.isModulePseudoCoherent` — the direction used in practice: a
  pseudo-coherent ring map makes its target a pseudo-coherent module over each of its
  presentations.

## Relation to Tag 0BZ9

Tag 0BZ9 asks for a Tate resolution with finitely many generators in each degree over a
pseudo-coherent ring map, and its proof opens by using the hypothesis in exactly the form proved
here: *`S` is a pseudo-coherent `R[x₁, …, x_n]`-module* for the polynomial ring of the chosen
presentation. Nothing in this file claims Tag 0BZ9, which also needs the finiteness of the
degree-`m` homology of each stage of the tower and a tower whose chosen families span the cycles
only modulo boundaries.

## Implementation notes

A presentation is a surjective `R`-algebra map `α : MvPolynomial (Fin n) R →ₐ[R] S`, and the
module structure it induces on `S` is `Module.compHom S α.toRingHom`, which is the structure both
Stacks 0675 and Stacks 064T are stated with. It is supplied by a `letI` rather than through
instance search, since `S` already carries unrelated module structures.

The model of the derived category of `R[x₁, …, x_n]`-modules is an instance argument. The
statements are about one presentation at a time, so each of them takes one model.

## References

* [Stacks Project, Tag 067H](https://stacks.math.columbia.edu/tag/067H)
* [Stacks Project, Tag 0675](https://stacks.math.columbia.edu/tag/0675)
* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
-/

@[expose] public section

open CategoryTheory

namespace Algebra

universe u w

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- **Pseudo-coherence of a ring map through one presentation, in any model.** For a finite
polynomial presentation `α : R[x₁, …, x_n] → S`, the ring map `R → S` is pseudo-coherent exactly
when `S` is a pseudo-coherent `R[x₁, …, x_n]`-module (Stacks 064T), read in any model of the
derived category. -/
public theorem pseudoCoherent_iff_isModulePseudoCoherent {n : ℕ}
    [HasDerivedCategory.{w} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    (α : MvPolynomial (Fin n) R →ₐ[R] S) (hα : Function.Surjective α) :
    PseudoCoherent R S ↔
      letI : Module (MvPolynomial (Fin n) R) S := Module.compHom S α.toRingHom
      StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := MvPolynomial (Fin n) R) S := by
  let : Module (MvPolynomial (Fin n) R) S := Module.compHom S α.toRingHom
  rw [(StacksDraft.PseudoCoherence.modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
    (R := MvPolynomial (Fin n) R) S).2.2.2]
  refine ⟨fun h => ?_, fun h => ⟨n, α, hα, ?_⟩⟩
  · exact (PseudoCoherent.nonempty_finiteFreeModuleResolution_quotient_iff_compHom hα).mp
      (h.nonempty_finiteFreeModuleResolution α hα)
  · exact (PseudoCoherent.nonempty_finiteFreeModuleResolution_quotient_iff_compHom hα).mpr h

/-- **The target of a pseudo-coherent ring map is a pseudo-coherent module over each of its
finite polynomial presentations**, in any model of the derived category. This is the form in which
pseudo-coherence of `R → S` enters the finiteness arguments for complexes of modules over
`R[x₁, …, x_n]`. -/
public theorem PseudoCoherent.isModulePseudoCoherent
    [h : PseudoCoherent R S] {n : ℕ}
    [HasDerivedCategory.{w} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    (α : MvPolynomial (Fin n) R →ₐ[R] S) (hα : Function.Surjective α) :
    letI : Module (MvPolynomial (Fin n) R) S := Module.compHom S α.toRingHom
    StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := MvPolynomial (Fin n) R) S :=
  (pseudoCoherent_iff_isModulePseudoCoherent α hα).mp h

/-- **The target of a pseudo-coherent ring map is `m`-pseudo-coherent over each of its finite
polynomial presentations**, for every `m`, in any model of the derived category. -/
public theorem PseudoCoherent.isModulePseudoCoherentFrom
    [h : PseudoCoherent R S] {n : ℕ}
    [HasDerivedCategory.{w} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    (α : MvPolynomial (Fin n) R →ₐ[R] S) (hα : Function.Surjective α) (m : ℤ) :
    letI : Module (MvPolynomial (Fin n) R) S := Module.compHom S α.toRingHom
    StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom (R := MvPolynomial (Fin n) R) S m := by
  let : Module (MvPolynomial (Fin n) R) S := Module.compHom S α.toRingHom
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1 (h.isModulePseudoCoherent α hα) m

end Algebra

end

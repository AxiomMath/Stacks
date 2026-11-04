module

public import StacksFrontier.RingTheory.CompleteIntersection.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Syntomic ring maps

A ring map `R → S` is *syntomic*, equivalently `S` is a *flat local complete intersection over
`R`*, if it is flat, of finite presentation, and if all of its fibre rings `S ⊗_R κ(p)`, for `p`
a prime of `R`, are local complete intersections over the residue field `κ(p)` in the sense of
`IsLocalCompleteIntersection`. Over a field the notion collapses onto that definition: a
`k`-algebra is syntomic over `k` if and only if it is a local complete intersection over `k`, the
only prime of `k` being `(0)` and the fibre there being the algebra itself.

The fibre condition is a condition on the scheme-theoretic fibres of `Spec S → Spec R`: the
spectrum of `κ(p) ⊗_R S` is the fibre over `p`, by
`PrimeSpectrum.preimageHomeomorphFiber`.

## Main definitions

* `Algebra.Syntomic`: `S` is flat and of finite presentation over `R`, and every fibre ring of
  `R → S` is a local complete intersection over the residue field of the corresponding prime.

## Implementation notes

*Stated for an `R`-algebra, not for a bare ring map.* This is how Mathlib states `Algebra.Smooth`
and `Algebra.Etale`, both of which the Stacks Project also words as properties of a ring map (and
`Algebra.Smooth` carries the tag of Stacks Definition 00T2). The form for a ring map
`f : R →+* S` is `Algebra.Syntomic R S` for the algebra structure `f.toAlgebra`, which is how
`RingHom.Smooth` is defined from `Algebra.Smooth`.

*The fibre ring is `κ(p) ⊗_R S`, the source's `S ⊗_R κ(p)` with the factors exchanged.* The two
are isomorphic as `κ(p)`-algebras by `Algebra.TensorProduct.comm`, and it is the first factor
that carries the `κ(p)`-algebra structure of a tensor product in Mathlib, so writing the fibre
this way needs no local instance. It is Mathlib's `Ideal.Fiber p S`, whose spectrum is the
set-theoretic fibre; the residue field `κ(p)` is `p.ResidueField`, the fraction field of `R / p`,
and `Ideal.ker_algebraMap_residueField` pins `p` as the kernel of `R → κ(p)`.

*Flatness and finite presentation are fields, re-registered as instances.* As for
`Algebra.Smooth`, they are populated by `infer_instance` when a syntomic algebra is constructed,
and `Algebra.Syntomic.flat` and `Algebra.Syntomic.finitePresentation` are instances, so an
`Algebra.Syntomic R S` in the context is found by instance search wherever `Module.Flat R S` or
`Algebra.FinitePresentation R S` is wanted.

*No finite type hypothesis on the fibres.* Definition 00S9 is stated for finite type
`k`-algebras, and none of that appears here, nor is any of it missing: `S` is of finite
presentation over `R`, hence `κ(p) ⊗_R S` is of finite presentation, in particular of finite
type, over `κ(p)`.

## References

* [Stacks 00SL](https://stacks.math.columbia.edu/tag/00SL), Definition 10.136.1, in Section
  10.136 "Syntomic morphisms". Definition 00S9, cited there for "local complete intersection",
  is `IsGlobalCompleteIntersection` and `IsLocalCompleteIntersection`.
-/

@[expose] public section

/-- A ring map `R → S` is **syntomic**, and `S` is a **flat local complete intersection over
`R`**, if it is flat, of finite presentation, and if all of its fibre rings `S ⊗_R κ(p)` are
local complete intersections over `κ(p)` (`IsLocalCompleteIntersection`). -/
@[stacks 00SL "Stated for an `R`-algebra `S`, as Mathlib states `Algebra.Smooth`; for a ring map
`f : R →+* S` it is `Algebra.Syntomic R S` at `f.toAlgebra`. The fibre ring is Mathlib's
`Ideal.Fiber p S = κ(p) ⊗[R] S`, the source's `S ⊗_R κ(p)` with the factors exchanged so that the
`κ(p)`-algebra structure is the one Mathlib puts on a tensor product. See the module docstring.",
  ega "IV 19.3.6" "affine case"]
public class Algebra.Syntomic (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] :
    Prop where
  /-- A syntomic algebra is flat. -/
  flat : Module.Flat R S := by infer_instance
  /-- A syntomic algebra is of finite presentation. -/
  finitePresentation : Algebra.FinitePresentation R S := by infer_instance
  /-- Every fibre ring `κ(p) ⊗_R S` of a syntomic algebra is a local complete intersection over
  the residue field `κ(p)`. -/
  isLocalCompleteIntersection_fiber (p : Ideal R) [p.IsPrime] :
    IsLocalCompleteIntersection p.ResidueField (p.Fiber S)

attribute [instance] Algebra.Syntomic.flat Algebra.Syntomic.finitePresentation

end

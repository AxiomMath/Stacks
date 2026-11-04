module

public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertibility of the twists at a common multiple of the degrees of a covering family

Let `𝒮` be a nonnegatively graded ring and let `f k`, homogeneous of degrees `d k`, be a family
whose standard opens cover `Proj 𝒮`. If `m` is a common multiple of the degrees `d k`, then the
twisting sheaf `𝒪(m)` is **invertible**, trivialized on `D₊(f k)` by `f k ^ (m / d k)`.

This is the hypothesis-free replacement for
`Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf`, which asks that `𝒮` be
generated in degree one over `𝒮 0` and then gets invertibility of *every* twist. Generation in
degree one is not available over an arbitrary graded ring, and it is not what the sources use:
the proof of Stacks Tag 0801 takes `d` to be the least common multiple of the degrees of a
covering family `f_0, …, f_n` and uses invertibility only of the twists `𝒪(n d)`, which is
exactly the statement proved here.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.coversTop_basicOpen`: a family of standard
  opens covering `Proj 𝒮` covers the terminal object of the site of opens.
* `Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.twistingSheafOverBasicOpenIsoUnitOfMul`: the
  trivialization of `𝒪(m)` on `D₊(f)` for `f` homogeneous of degree `d` and `m = e d`.
* `Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.isInvertible_twistingSheaf_of_cover`: **`𝒪(m)`
  is invertible** when the `D₊(f k)` cover `Proj 𝒮` and each `d k` divides `m`, with the
  cofactors given as data.
* `Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.isInvertible_twistingSheaf_of_cover_of_dvd`:
  the same with the divisibility given only up to existence.

## Implementation notes

The degree arithmetic is carried by `▸` on the isomorphism rather than inside a proof, for the
reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Blowup/TwistDegreeOne.lean`: the twisting sheaf appears in the
*type* of the trivialization, and `e * (d : ℤ)` is not syntactically `m`.

The cofactors `e k` with `e k * d k = m` are taken as **data** in the main statement rather than
extracted from a divisibility hypothesis.
`Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit` consumes the trivializations as a family
of isomorphisms, so pulling them out of an `∃` with `Exists.choose` would put a choice inside the
trivializing data; the divisibility form is derived from the explicit one in
`isInvertible_twistingSheaf_of_cover_of_dvd`, where the choice is harmless because the conclusion
is a `Prop`.

Invertibility is read off the covering and the trivializations directly, by
`Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit`, rather than deduced from finite local
freeness — the same route `…ProjDegreeOne.isInvertible_twistingSheaf` takes.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)

## Scope of the tag attribute

No `@[stacks]` attribute is attached. Invertibility of the twists on a standard open is Tag 01MS
and already carries the attribute at
`Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit`; what is added
here is the globalization of that trivialization over a covering family, which is the step the
proof of Tag 0801 cites and which Tag 0801 itself is not about.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf
  twistingSheafOverBasicOpenIsoUnit)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistCommonMultiple

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **A family of standard opens covering `Proj 𝒮` is a covering of the terminal object** of the
site of opens, which is the shape the descent criterion for invertibility consumes. -/
public theorem coversTop_basicOpen {ι : Type*} (f : ι → S)
    (hcover : ⨆ k, Proj.basicOpen 𝒮 (f k) = ⊤) :
    (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)).CoversTop
      (fun k ↦ ProjectiveSpectrum.basicOpen 𝒮 (f k)) :=
  (Opens.coversTop_iff _ _).mpr (TopologicalSpace.IsOpenCover.mk hcover)

/-- **The trivialization of `𝒪(m)` on `D₊(f)` for `f` homogeneous of degree `d` and `m = e d`.**
This is Tag 01MS with the exponent `e * (d : ℤ)` rewritten to `m`; the rewriting is done with `▸`
on the isomorphism because the twisting sheaf occurs in its type. -/
public def twistingSheafOverBasicOpenIsoUnitOfMul {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) {m : ℤ} (e : ℤ)
    (he : e * (d : ℤ) = m) :
    (twistingSheaf 𝒮 m).over (ProjectiveSpectrum.basicOpen 𝒮 f) ≅
      SheafOfModules.unit ((projRingSheaf 𝒮).over (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  he ▸ twistingSheafOverBasicOpenIsoUnit 𝒮 hf e

/-- **The twisting sheaf `𝒪(m)` is invertible when `m` is a common multiple of the degrees of a
covering family.** The standard opens of homogeneous `f k` of degrees `d k` cover `Proj 𝒮`, and
on `D₊(f k)` the twist `𝒪(m)` is trivialized by `f k ^ (e k)` where `e k * d k = m`; a sheaf of
modules trivial on each member of a covering is invertible.

No generation in degree one and no Noetherian hypothesis is used. This is the form in which the
proof of Stacks Tag 0801 uses invertibility of the twists, with `m` running over the multiples of
the least common multiple of the degrees of a covering family. -/
@[ega "II 3.2.5" "Second assertion"]
public theorem isInvertible_twistingSheaf_of_cover {ι : Type*} (f : ι → S) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒮 (d k)) (hcover : ⨆ k, Proj.basicOpen 𝒮 (f k) = ⊤) {m : ℤ} (e : ι → ℤ)
    (he : ∀ k, e k * (d k : ℤ) = m) :
    Stacks.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (projRingSheaf 𝒮).property
      (twistingSheaf 𝒮 m) :=
  Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit _ _ _
    (coversTop_basicOpen 𝒮 f hcover)
    (fun k ↦ twistingSheafOverBasicOpenIsoUnitOfMul 𝒮 (hf k) (e k) (he k))

/-- **The same, with the divisibility given only up to existence.** The conclusion is a `Prop`,
so the cofactors may be chosen. -/
@[ega "II 8.14.4" "invertibility clause"]
public theorem isInvertible_twistingSheaf_of_cover_of_dvd {ι : Type*} (f : ι → S) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒮 (d k)) (hcover : ⨆ k, Proj.basicOpen 𝒮 (f k) = ⊤) {m : ℤ}
    (hdvd : ∀ k, (d k : ℤ) ∣ m) :
    Stacks.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (projRingSheaf 𝒮).property
      (twistingSheaf 𝒮 m) :=
  isInvertible_twistingSheaf_of_cover 𝒮 f d hf hcover (fun k ↦ (hdvd k).choose)
    fun k ↦ by rw [mul_comm]; exact ((hdvd k).choose_spec).symm

end Stacks.AlgebraicGeometry.ProjTwistCommonMultiple

end

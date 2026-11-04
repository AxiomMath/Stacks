module

public import StacksFrontier.AlgebraicGeometry.Etale.AffineOfCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.AffineOfKrullDimLEOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affineness of the complement of the ramification locus: the closing argument

Let `A` be a regular local ring containing a field, let `f : V ⟶ Spec A` be étale and
quasi-compact, and let `f` factor through the punctured spectrum `Spec A ∖ {𝔪}` by an affine
morphism `g`. Writing `d` for the Krull dimension of `A`, the last paragraph of the proof of
[Stacks, Tag 0ECD] concludes that `V` is affine from the bound `e(V) ≤ max(0, d - 2)` on the
largest degree in which `H ⁱ(V, 𝒪_V)` is nonzero, by splitting into two cases:

* for `d ≥ 2` the bound feeds [Stacks, Tag 0ECC], which needs vanishing only above `d - 1`;
* for `d ≤ 1` the punctured spectrum of `A` is itself affine ([Stacks, Tag 0BCR]), and `V` is
  affine over it, so no cohomological input is needed at all.

This file proves that closing argument. Both cases are discharged, so the only remaining input to
[Stacks, Tag 0ECD] in this local situation is the cohomological bound itself.

## Main results

* `Stacks.PuncturedSpectrum.isAffine_of_isAffineHom_puncturedSpectrum_of_krullDimLE_one` — the
  case `d ≤ 1`: a scheme affine over the punctured spectrum of a Noetherian local ring of Krull
  dimension at most one is affine.
* `Stacks.PuncturedSpectrum.isAffine_of_isZero_cohomologyOverBase_above_dim_sub_two` — the two
  cases combined: in the situation of [Stacks, Tag 0ECB], if `H ⁿ(V, 𝒪_V) = 0` for every
  `n > d - 2`, then `V` is affine.

## What is *not* proved here

The bound `e(V) ≤ max(0, d - 2)` itself, which is the hypothesis of the second result above. The
source obtains it by reading the cohomological dimension of `V` off the local rings of the points
of `X ∖ V` ([Stacks, Tag 0DXB], [Stacks, Tag 0DX7]), bounding each by
`dim(𝒪_{X,x}) - 1` ([Stacks, Tag 0DXC]), and then improving that to `dim(𝒪_{X,x}) - 2` at the
points of codimension at least two by combining purity of the ramification locus
([Stacks, Tag 0EA4]) with Hartshorne–Lichtenbaum vanishing ([Stacks, Tag 0EB7]). That argument,
and the whole of [Stacks, Tag 0ECD], is carried out in
`StacksFrontier/AlgebraicGeometry/Etale/AffineMaximalEtaleOpen.lean`.

## Implementation notes

The punctured spectrum carries two names in this library,
`Stacks.LocalCohomology.puncturedSpectrum`, which is the one [Stacks, Tag 0ECC] is stated with,
and `Stacks.puncturedSpectrum`, which is the one [Stacks, Tag 0BCR] is stated with. They are the
same open — the complement of the closed point — and
`Stacks.PuncturedSpectrum.localCohomology_puncturedSpectrum_eq` records that, so that the
affineness criterion applies to the former.

The dimension `d` is written `((ringKrullDim A).unbotD 0).toNat`, as in
`Stacks.PuncturedSpectrum.isAffine_of_cohomologyOverBase_vanishing`, and the case split is on
`2 ≤ d`. Subtraction of naturals is truncated, so for `d ≤ 1` the hypothesis `d - 2 < n` reads
`0 < n`; that hypothesis is simply not used in that case, which is why the statement is the
source's `max(0, d - 2)` bound rather than something weaker.

## References

* [Stacks Project, Tag 0ECD](https://stacks.math.columbia.edu/tag/0ECD)
* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0BCR](https://stacks.math.columbia.edu/tag/0BCR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.LocalCohomology

universe u

namespace Stacks.PuncturedSpectrum

/-- The two names this library gives the punctured spectrum of a local ring agree: both are the
open complement of the closed point of `Spec A`. -/
theorem localCohomology_puncturedSpectrum_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A) = Stacks.puncturedSpectrum A :=
  rfl

/-- **The punctured spectrum of a Noetherian local ring of Krull dimension at most one is an
affine scheme.** This is the affineness half of [Stacks, Tag 0BCR], transported to the name for
the punctured spectrum that [Stacks, Tag 0ECC] uses. -/
@[ega "IV 21.12.9" "special case"]
theorem isAffine_puncturedSpectrum_of_krullDimLE_one (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : Ring.KrullDimLE 1 A) :
    IsAffine (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme) := by
  have h : IsAffineOpen (Stacks.puncturedSpectrum A) :=
    isAffineOpen_puncturedSpectrum_of_krullDimLE_one A hA
  rwa [← localCohomology_puncturedSpectrum_eq A] at h

/-- **[Stacks, Tag 0ECD], the case `dim(A) ≤ 1`.** A scheme affine over the punctured spectrum of
a Noetherian local ring of Krull dimension at most one is affine: the punctured spectrum is
itself affine by [Stacks, Tag 0BCR], and an affine morphism to an affine scheme has affine
source.

No cohomological hypothesis is needed, which is exactly what the source observes about this
case. -/
@[ega "IV 21.12.9" "special case"]
theorem isAffine_of_isAffineHom_puncturedSpectrum_of_krullDimLE_one (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : Ring.KrullDimLE 1 A) {V : Scheme.{u}}
    (g : V ⟶ (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    [IsAffineHom g] :
    IsAffine V :=
  have := isAffine_puncturedSpectrum_of_krullDimLE_one A hA
  isAffine_of_isAffineHom g

/-- **[Stacks, Tag 0ECD], the closing argument.** In the situation of [Stacks, Tag 0ECB] — `A` a
regular local ring containing a field `k`, `f : V ⟶ Spec A` étale and quasi-compact, and the
structure morphism factored through the punctured spectrum by an affine morphism `g` — write `d`
for the Krull dimension of `A`. If `H ⁿ(V, 𝒪_V) = 0` for every natural number `n > d - 2`, then
`V` is affine.

This is the source's bound `e(V) ≤ max(0, d - 2)` turned into affineness. For `d ≥ 2` it is
[Stacks, Tag 0ECC], whose own bound `d - 1` is weaker; for `d ≤ 1` the punctured spectrum of `A`
is affine and the cohomological hypothesis is not used. See the module documentation for the
bound itself, which is not proved here. -/
theorem isAffine_of_isZero_cohomologyOverBase_above_dim_sub_two (A k : Type u) [CommRing A]
    [IsRegularLocalRing A] [Field k] [Algebra k A] {V : Scheme.{u}}
    (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    [IsAffineHom g]
    (hg : g ≫ (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    (hvanish : ∀ n : ℕ, ((ringKrullDim A).unbotD 0).toNat - 2 < n →
      IsZero (cohomologyOverBase A f (SheafOfModules.unit V.ringCatSheaf) n)) :
    IsAffine V := by
  set d := ((ringKrullDim A).unbotD 0).toNat with hd
  by_cases hge : 2 ≤ d
  · exact isAffine_of_cohomologyOverBase_vanishing A k f g hg fun n hn => hvanish n (by omega)
  · refine isAffine_of_isAffineHom_puncturedSpectrum_of_krullDimLE_one A ?_ g
    refine Ring.krullDimLE_iff.mpr ?_
    have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
    cases hr : ringKrullDim A with
    | bot => exact absurd hr hbot
    | coe y =>
      cases y with
      | top => exact absurd hr htop
      | coe m =>
        have hdm : d = m := by rw [hd, hr]; simp
        have hm : m ≤ 1 := by omega
        exact_mod_cast hm

end Stacks.PuncturedSpectrum

end

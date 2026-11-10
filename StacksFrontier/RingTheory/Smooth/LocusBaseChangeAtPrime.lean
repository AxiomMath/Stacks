module

public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.LocalRing.ResidueField.FiberBaseChange
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.Smooth.SmoothAt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The smooth locus under base change, at a single prime

Let `R → A` be of finite presentation, let `R → R'` be any ring map and let `A'` be the base
change `R' ⊗_R A`. Let `q'` be a prime of `A'` lying over the prime `q` of `A`. This file proves
that `A` is smooth over `R` at `q` if and only if `A'` is smooth over `R'` at `q'`, provided that
`R → A` is flat or that `R → R'` is flat.

Only the second case is Lemma 00TG, the flat base change of the smooth locus, which is
`Algebra.smoothLocus_comap_of_isPushout`. The first case has no flatness on the
morphism along which one base changes, and is instead the fibre criterion: a flat algebra of
finite presentation is smooth at `q` exactly when its fibre over the image prime is smooth at the
corresponding prime (Lemma 00TF and Lemma 00TT), while the fibre of a base change is the base
change of the fibre along the residue field extension, where Lemma 02UQ applies because the base
is a field.

One half of the equivalence needs no flatness at all: smoothness at a prime is inherited by every
base change, because a finitely presented algebra smooth at `q` is smooth on a basic open
neighbourhood of `q`, and smoothness of an algebra is stable under base change.

## Main results

* `Algebra.isSmoothAt_of_isSmoothAt_of_isPushout`: smoothness at a prime passes to an arbitrary
  base change, at any prime lying over it.
* `Algebra.isSmoothAt_iff_isSmoothAt_fiber`: for a flat algebra of finite presentation,
  smoothness at a prime is smoothness of the fibre at the corresponding prime. This is the
  equivalence of conditions (1) and (2) of Lemma 01V9, read on rings.
* `Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat`: the equivalence described above.

## Implementation notes

The base change is the abstract one, `Algebra.IsPushout R A R' A'`, rather than the model
`R' ⊗_R A`; the model is a witness by `TensorProduct.isPushout`, and stating the hypothesis lets
a consumer apply the results to the base change already in hand. The correspondence of primes is
`Ideal.LiesOver`.

The two fibres are compared through the algebra structure `Ideal.Fiber.baseChangeAlgebra`, the
scalar tower `Ideal.Fiber.isScalarTower_baseChange` and the pushout square
`Ideal.Fiber.isPushout_baseChange`. These are not global instances, since they depend on the
chosen pushout square, so they are introduced with `let` and `have` below.

## References

* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF), flat with a smooth fibre
  implies smooth at a prime.
* [Stacks Project, Tag 00TG](https://stacks.math.columbia.edu/tag/00TG), the smooth locus of a
  flat base change.
* [Stacks Project, Tag 02UQ](https://stacks.math.columbia.edu/tag/02UQ), smoothness at a prime
  under extension of the base field.
-/

@[expose] public section

open Algebra TensorProduct

namespace Algebra

/-- Finite presentation is inherited by the base change `A'` of `A` along `R → R'`. -/
private theorem finitePresentation_of_isPushout (R A R' A' : Type*) [CommRing R] [CommRing A]
    [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra A A'] [Algebra R' A']
    [Algebra R A'] [IsScalarTower R R' A'] [IsScalarTower R A A']
    [Algebra.IsPushout R A R' A'] [Algebra.FinitePresentation R A] :
    Algebra.FinitePresentation R' A' :=
  have : Algebra.IsPushout R R' A A' := Algebra.IsPushout.symm inferInstance
  .equiv (Algebra.IsPushout.equiv R R' A A')

/-- **Smoothness at a prime passes to any base change.** Let `R → A` be of finite presentation,
let `A'` be the base change of `A` along an arbitrary `R → R'` and let `q'` be a prime of `A'`
lying over `q ⊆ A`. If `A` is smooth over `R` at `q` then `A'` is smooth over `R'` at `q'`.

No flatness is needed: by openness of the smooth locus (Lemma 00TB and Lemma 07BU, in the shape
`Algebra.IsSmoothAt.exists_notMem_smooth`) there is a `g ∉ q` with `A_g` smooth over `R`, and the
base change `A'_{g'}` of `A_g`, for `g'` the image of `g`, is then smooth over `R'`; the prime
`q'` lies in the basic open of `g'`. -/
theorem isSmoothAt_of_isSmoothAt_of_isPushout (R A R' A' : Type*) [CommRing R] [CommRing A]
    [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra A A'] [Algebra R' A']
    [Algebra R A'] [IsScalarTower R R' A'] [IsScalarTower R A A']
    [Algebra.IsPushout R A R' A'] [Algebra.FinitePresentation R A]
    (q : Ideal A) (q' : Ideal A') [q.IsPrime] [q'.IsPrime] [q'.LiesOver q]
    [Algebra.IsSmoothAt R q] : Algebra.IsSmoothAt R' q' := by
  obtain ⟨g, hgq, hg⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  have hgq' : algebraMap A A' g ∉ q' := fun hmem ↦ hgq (by rw [q'.over_def q]; exact hmem)
  have := finitePresentation_of_isPushout R A R' A'
  let φ : Localization.Away g →+* Localization.Away (algebraMap A A' g) :=
    IsLocalization.Away.map _ _ (algebraMap A A') g
  let _ : Algebra (Localization.Away g) (Localization.Away (algebraMap A A' g)) := φ.toAlgebra
  have hmapcomp : φ.comp (algebraMap A (Localization.Away g)) =
      (algebraMap A' (Localization.Away (algebraMap A A' g))).comp (algebraMap A A') :=
    IsLocalization.map_comp (M := Submonoid.powers g) _
  have : IsScalarTower A (Localization.Away g)
      (Localization.Away (algebraMap A A' g)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, hmapcomp, ← IsScalarTower.algebraMap_eq])
  have : IsScalarTower R (Localization.Away g)
      (Localization.Away (algebraMap A A' g)) :=
    IsScalarTower.to₁₃₄ R A _ _
  have : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers g))
      (Localization.Away (algebraMap A A' g)) := by
    rw [show Algebra.algebraMapSubmonoid A' (Submonoid.powers g)
        = Submonoid.powers (algebraMap A A' g) from Submonoid.map_powers _ _]
    infer_instance
  have : Algebra.IsPushout A (Localization.Away g) A'
      (Localization.Away (algebraMap A A' g)) :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers g) (Localization.Away g) A'
      (Localization.Away (algebraMap A A' g))).symm
  have hbig : Algebra.IsPushout R (Localization.Away g) R'
      (Localization.Away (algebraMap A A' g)) :=
    (Algebra.IsPushout.comp_iff R A R' A'
      (T' := Localization.Away (algebraMap A A' g))).mpr inferInstance
  have : Algebra.Smooth R' (Localization.Away (algebraMap A A' g)) := by
    have := hg
    have := hbig.symm
    exact .of_equiv (Algebra.IsPushout.equiv R R' (Localization.Away g)
      (Localization.Away (algebraMap A A' g)))
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr ‹_›
    (show (⟨q', ‹_›⟩ : PrimeSpectrum A') ∈ PrimeSpectrum.basicOpen _ from hgq')

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **A flat algebra of finite presentation is smooth at a prime exactly when its fibre is.**
Let `R → A` be flat and of finite presentation, let `q ⊆ A` be a prime lying over `p ⊆ R` and let
`Q` be the prime of the fibre `κ(p) ⊗_R A` contracting to `q`. Then `A` is smooth over `R` at `q`
if and only if the fibre is smooth over `κ(p)` at `Q`.

This is the equivalence of conditions (1) and (2) of Lemma 01V9 read on rings, the flatness
conjunct of condition (2) being a hypothesis here. The implication from the fibre is Lemma 00TF;
the other implication is `Algebra.isSmoothAt_of_isSmoothAt_of_isPushout` for the base change of
`A` along `R → κ(p)`. -/
@[sga "3 VIB 3.10" "special case"]
theorem isSmoothAt_iff_isSmoothAt_fiber (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A) = q) :
    Algebra.IsSmoothAt R q ↔ Algebra.IsSmoothAt p.ResidueField Q := by
  have hpo : Algebra.IsPushout R A p.ResidueField (p.Fiber A) :=
    (TensorProduct.isPushout (R := R) (S := p.ResidueField) (T := A)).symm
  have hlo : Q.LiesOver q := ⟨hQ.symm⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h
    exact isSmoothAt_of_isSmoothAt_of_isPushout R A p.ResidueField (p.Fiber A) q Q
  · have := h
    have : Module.Flat R (Localization.AtPrime q) := Module.Flat.trans R A _
    obtain ⟨g, hgq, hsm⟩ := Algebra.exists_notMem_smooth_of_isSmoothAt_fiber p Q q hQ
      ⟨1, (Ideal.ne_top_iff_one _).mp ‹q.IsPrime›.ne_top, inferInstance⟩
    exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm
      (show (⟨q, ‹_›⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen g from hgq)

/-- **The smooth locus commutes with base change at a prime, flatness being needed on only one
of the two sides.** Let `R → A` be of finite presentation, let `A'` be the base change of `A`
along `R → R'` and let `q'` be a prime of `A'` lying over `q ⊆ A`. Assume that `R → A` is flat,
or that `R → R'` is flat. Then `A` is smooth over `R` at `q` if and only if `A'` is smooth over
`R'` at `q'`.

Flatness of `R → R'` is the case of Lemma 00TG. Flatness of `R → A` instead goes through the
fibres: both sides are smoothness of a fibre at the corresponding prime
(`Algebra.isSmoothAt_iff_isSmoothAt_fiber`, the ring form of Lemma 01V9), and the fibre of `A'`
over `p'` is the base change of the fibre of `A` over `p` along `κ(p) → κ(p')`
(`Ideal.Fiber.isPushout_baseChange`), to which Lemma 02UQ applies.

This is the commutative algebra underlying Lemma 02V4 on schemes. -/
@[ega "IV 17.7.2" "(ii), affine case", sga "3 VIB 3.10" "special case"]
theorem isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat (R A R' A' : Type*) [CommRing R]
    [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra A A']
    [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A'] [IsScalarTower R A A']
    [Algebra.IsPushout R A R' A'] [Algebra.FinitePresentation R A]
    (hflat : Module.Flat R A ∨ Module.Flat R R')
    (q : Ideal A) (q' : Ideal A') [q.IsPrime] [q'.IsPrime] [q'.LiesOver q] :
    Algebra.IsSmoothAt R q ↔ Algebra.IsSmoothAt R' q' := by
  have hsymm : Algebra.IsPushout R R' A A' := Algebra.IsPushout.symm inferInstance
  have := finitePresentation_of_isPushout R A R' A'
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h
    exact isSmoothAt_of_isSmoothAt_of_isPushout R A R' A' q q'
  rcases hflat with hA | hR'
  · have := hA
    have hqu : Ideal.under A q' = q := (q'.over_def q).symm
    have hflat' : Module.Flat R' A' :=
      Module.Flat.of_linearEquiv (M := TensorProduct R R' A)
        (Algebra.IsPushout.equiv R R' A A').toLinearEquiv.symm
    have hlo : (Ideal.under R' q').LiesOver (Ideal.under R q) :=
      ⟨by rw [← hqu, Ideal.under_under, Ideal.under_under]⟩
    obtain ⟨Q', hQp', hQ'⟩ :=
      Ideal.Fiber.exists_comap_includeRight_eq q' (Ideal.under R' q') rfl
    have := hQp'
    have hQ'' : Ideal.comap ((Algebra.TensorProduct.includeRight :
        A' →ₐ[R'] (Ideal.under R' q').Fiber A').toRingHom) Q' = q' := hQ'
    let := Ideal.residueFieldAlgebra (Ideal.under R q) (Ideal.under R' q')
    have := Ideal.isScalarTower_residueField (Ideal.under R q) (Ideal.under R' q')
    let := Ideal.Fiber.baseChangeAlgebra R R' A A' (Ideal.under R q) (Ideal.under R' q')
    have := Ideal.Fiber.isScalarTower_baseChange R R' A A' (Ideal.under R q) (Ideal.under R' q')
    have := (Ideal.Fiber.isPushout_baseChange R R' A A'
      (Ideal.under R q) (Ideal.under R' q')).symm
    have hft : Algebra.FiniteType (Ideal.under R q).ResidueField
        ((Ideal.under R q).Fiber A) := by
      have : Algebra.FinitePresentation (Ideal.under R q).ResidueField
          ((Ideal.under R q).Fiber A) := Algebra.FinitePresentation.baseChange _
      infer_instance
    obtain ⟨Q, hQprime, hQQ', hQ⟩ :
        ∃ Q : Ideal ((Ideal.under R q).Fiber A), Q.IsPrime ∧ Q'.LiesOver Q ∧
          Q.comap (Algebra.TensorProduct.includeRight :
            A →ₐ[R] (Ideal.under R q).Fiber A) = q := by
      refine ⟨Ideal.comap (algebraMap ((Ideal.under R q).Fiber A)
        ((Ideal.under R' q').Fiber A')) Q', inferInstance, ⟨rfl⟩, ?_⟩
      change Ideal.comap ((Algebra.TensorProduct.includeRight :
        A →ₐ[R] (Ideal.under R q).Fiber A).toRingHom) _ = q
      rw [Ideal.comap_comap, Ideal.Fiber.algebraMap_baseChange_comp_includeRight R R' A A'
        (Ideal.under R q) (Ideal.under R' q'), ← Ideal.comap_comap, hQ'']
      exact hqu
    have := hQprime
    have := hQQ'
    refine (isSmoothAt_iff_isSmoothAt_fiber R A (Ideal.under R q) q Q hQ).mpr ?_
    refine (Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout
      (k := (Ideal.under R q).ResidueField)
      (K := (Ideal.under R' q').ResidueField) Q Q').mpr ?_
    exact (isSmoothAt_iff_isSmoothAt_fiber R' A' (Ideal.under R' q') q' Q' hQ').mp h
  · have := hR'
    obtain rfl : q = Ideal.under A q' := q'.over_def q
    exact (Set.ext_iff.mp (Algebra.smoothLocus_comap_of_isPushout R A R' A') ⟨q', ‹_›⟩).mpr h

end Algebra

end

module

import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite free étale algebras realizing a separable residue field extension

Let `R` be a ring, `p` a prime of `R` and `κ(p)` its residue field, and let `L/κ(p)` be a finite
separable field extension. Stacks 00UD produces an *étale* `R`-algebra `R'` with a prime `p'` over
`p` and `κ(p') ≅ L`; its witness `R[x, 1/f']/(f)` is a localization and is not finite over `R`.
This file produces instead a *finite free* `R`-algebra with the same property, étale only at `p'`:
the algebra `R[x]/(f)` itself, for `f` a monic lift of the minimal polynomial of a primitive
element of `L/κ(p)`.

The reason for wanting the finite form is Stacks 0551 (Making the components of the generic fibre
geometrically irreducible). Its proof takes `V = Spec A` a nonempty affine open of the irreducible
base, `p = √(0)` the nilradical of `A`, `K = κ(p)` the function field, and a finite separable
`K'/K` over which all irreducible components of `X_{K'}` become geometrically irreducible; it then
sets `A' = A[T]/(P)` and must know that `A → A'` is *finite* free, that `Spec(A') → Spec(A)` is
étale at the unique prime over `p`, and that the residue field there is `K'`. That is exactly
`Stacks.GeometricComponents.exists_finite_free_isEtaleAt_liesOver_residueFieldRingEquiv` below.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.GeometricComponents.etale_localizationAway_mk_derivative`: for monic `f : R[X]`, the
  localization of `R[x]/(f)` away from the image of `f'` is étale over `R`. This is the standard
  étale algebra `R[x, 1/f']/(f)` read through `AdjoinRoot`.
* `Stacks.GeometricComponents.isEtaleAt_of_derivative_notMem`: consequently `R[x]/(f)` is étale
  over `R` at every prime not containing the image of `f'`.
* `Stacks.GeometricComponents.isEtaleAt_of_liesOver`: if the reduction of `f` over `R ⧸ p` is
  coprime to its derivative, then `R[x]/(f)` is étale over `R` at *every* prime lying over `p`.
* `Stacks.GeometricComponents.exists_notMem_etale_localizationAway`: a module-finite finitely
  presented algebra that is étale at every prime over `p` becomes étale after inverting one
  element outside `p`, and `..._adjoinRoot` is that statement for `R[x]/(f)`.
* `Stacks.GeometricComponents.exists_finite_free_isEtaleAt_liesOver_residueFieldRingEquiv`: the
  finite free refinement of Stacks 00UD described above.

## Implementation notes

The étaleness of `R[x, 1/f']/(f)` is Mathlib's: `StandardEtalePair R` asks for `f` monic together
with a `g` such that `f'` divides a power of `g` in `R[x]`, and `g = f'` satisfies this trivially,
so `StandardEtalePair.equivAwayAdjoinRoot` identifies the standard étale algebra of the pair
`(f, f')` with `Localization.Away (AdjoinRoot.mk f (derivative f))`. Étaleness *at a prime* is then
read off `Algebra.basicOpen_subset_etaleLocus_iff`, which turns a formally étale localization away
from an element into containment of its basic open in the étale locus; no appeal to the local
criterion of Stacks 00U6 (`Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal`) is needed, and in
particular neither flatness of `R_p → R'_{p'}` nor maximality of `p R'_{p'}` has to be checked.

The polynomial data — a monic `f ∈ R[x]` and a primitive element `β` of `L/κ(p)` with `f(β) = 0`
and `f'(β)` invertible — is the data the proof of Stacks 00UD extracts, by the primitive element
theorem followed by clearing denominators via `Polynomial.scaleRoots`. In this repository that
extraction lives as a private lemma inside `Stacks.Etale.ResidueFieldRealization` in
`StacksFrontier/RingTheory/Etale/ResidueFieldExtension.lean`, so it is reproved here as
`Stacks.Etale.ResidueFieldRealization.exists_monic_aeval_eq_zero_and_adjoin_eq_top`; the two
should be merged into one public lemma when either file is promoted.

The isomorphism of residue field extensions is pinned exactly as in Stacks 00UD: as a ring
isomorphism `e : κ(p') ≃+* L` with `e ∘ Ideal.ResidueField.map p p' (algebraMap R R') =
algebraMap κ(p) L`, which is `κ(p)`-semilinearity of `e` for the canonical structures without
assuming an `Algebra κ(p) κ(p')` instance.

## References

* [Stacks Project, Tag 00UD](https://stacks.math.columbia.edu/tag/00UD)
* [Stacks Project, Tag 0551](https://stacks.math.columbia.edu/tag/0551)
-/

@[expose] public section

open Polynomial

universe u v

namespace Stacks.GeometricComponents

/-- For a monic `f : R[X]`, the pair `(f, f')` is a standard étale pair: `f'` divides the first
power of `f'`. -/
private noncomputable def standardEtalePairDerivative {R : Type u} [CommRing R] {f : R[X]}
    (hf : f.Monic) : StandardEtalePair R :=
  ⟨f, hf, derivative f, ⟨1, 0, 1, by ring⟩⟩

/-- **The standard étale algebra of a monic polynomial.** For monic `f : R[X]` the localization of
`R[x]/(f)` away from the image of the derivative `f'` is étale over `R`. -/
@[ega "IV 18.4.2" "(i), special case, (ii)"]
public theorem etale_localizationAway_mk_derivative {R : Type u} [CommRing R] {f : R[X]}
    (hf : f.Monic) : Algebra.Etale R (Localization.Away (AdjoinRoot.mk f (derivative f))) :=
  Algebra.Etale.of_equiv (standardEtalePairDerivative hf).equivAwayAdjoinRoot

/-- **`R[x]/(f)` is étale over `R` away from the derivative.** For monic `f : R[X]`, the algebra
`R[x]/(f)` is étale over `R` at every prime that does not contain the image of `f'`. -/
public theorem isEtaleAt_of_derivative_notMem {R : Type u} [CommRing R] {f : R[X]} (hf : f.Monic)
    (q : Ideal (AdjoinRoot f)) [q.IsPrime] (hq : AdjoinRoot.mk f (derivative f) ∉ q) :
    Algebra.IsEtaleAt R q :=
  have := etale_localizationAway_mk_derivative hf
  (Algebra.basicOpen_subset_etaleLocus_iff.mpr inferInstance)
    (show (⟨q, ‹_›⟩ : PrimeSpectrum (AdjoinRoot f)) ∈ PrimeSpectrum.basicOpen _ from hq)

/-- **The fibre of `R[x]/(f)` over `p` is étale when `f` is separable there.** If the image of a
monic `f : R[X]` in `(R ⧸ p)[X]` is coprime to its derivative, then `R[x]/(f)` is étale over `R` at
*every* prime lying over `p`, not merely at the one cut out by a chosen root.

The hypothesis is separability of the reduction of `f` over the residue *ring* `R ⧸ p`, which is
what one has after inverting a single element of `R ∖ p`; it is strictly stronger than
separability over `κ(p)` and is the form in which no localization is needed. The proof needs no
description of the fibre: were some prime `q` over `p` to contain the image of `f'`, evaluating a
Bézout identity `u f + v f' = 1` of `(R ⧸ p)[X]` in the domain `(R[x]/(f)) ⧸ q` — which receives
`R ⧸ p` because `q` lies over `p`, and sends `x` to a root of `f` at which `f'` vanishes — would
give `0 = 1`. -/
public theorem isEtaleAt_of_liesOver {R : Type u} [CommRing R] {f : R[X]} (hf : f.Monic)
    (p : Ideal R) [p.IsPrime]
    (hsep : IsCoprime (f.map (Ideal.Quotient.mk p)) (derivative (f.map (Ideal.Quotient.mk p))))
    (q : Ideal (AdjoinRoot f)) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsEtaleAt R q := by
  refine isEtaleAt_of_derivative_notMem hf q fun hd => ?_
  have hker : ∀ a ∈ p, (Ideal.Quotient.mk q) (algebraMap R (AdjoinRoot f) a) = 0 := by
    intro a ha
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hmem : a ∈ Ideal.under R q := (q.over_def p) ▸ ha
    rwa [Ideal.under_def, Ideal.mem_comap] at hmem
  let j : R ⧸ p →+* AdjoinRoot f ⧸ q :=
    Ideal.Quotient.lift p ((Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot f))) hker
  set γ : AdjoinRoot f ⧸ q := Ideal.Quotient.mk q (AdjoinRoot.root f)
  have hcomp : j.comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot f)) :=
    RingHom.ext fun _ => rfl
  have key : ∀ g : R[X], eval₂ j γ (g.map (Ideal.Quotient.mk p)) =
      Ideal.Quotient.mk q (AdjoinRoot.mk f g) := by
    intro g
    rw [eval₂_map, hcomp, show (Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot f)) =
      (Ideal.Quotient.mk q : AdjoinRoot f →+* _).comp
        ((AdjoinRoot.mk f).comp (Polynomial.C : R →+* R[X])) from RingHom.ext fun _ => rfl,
      ← Polynomial.hom_eval₂]
    congr 1
    rw [← AdjoinRoot.aeval_eq g]
    rfl
  obtain ⟨u, v, huv⟩ := hsep
  have h1 : eval₂ j γ (f.map (Ideal.Quotient.mk p)) = 0 := by
    rw [key f, AdjoinRoot.mk_self, map_zero]
  have h2 : eval₂ j γ (derivative (f.map (Ideal.Quotient.mk p))) = 0 := by
    rwa [Polynomial.derivative_map, key, Ideal.Quotient.eq_zero_iff_mem]
  have hone := congrArg (eval₂ j γ) huv
  simp only [eval₂_add, eval₂_mul, eval₂_one, h1, h2, mul_zero, add_zero] at hone
  exact zero_ne_one hone

/-- **Spreading out étaleness over the fibre of a finite algebra.** A module-finite, finitely
presented `R`-algebra `A` that is étale over `R` at every prime lying over a prime `p` of `R` is
étale over `R` after inverting a single element outside `p`.

This is the last step of the proof of Stacks 0551: "since `g` is finite and `q` is the only point
lying over `p` we see that `Z = g(Y' ∖ W)` is a closed subset of `V` not containing `p`; hence
after replacing `V` by a principal affine open of `V` which does not meet `Z` we obtain that `g` is
finite étale." The non-étale locus is closed because the étale locus is open for a finitely
presented algebra, and its image is closed because a module-finite algebra is integral, so
`Spec(A) → Spec(R)` is a closed map. -/
public theorem exists_notMem_etale_localizationAway {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Algebra.FinitePresentation R A] (p : Ideal R) [p.IsPrime]
    (hetale : ∀ (q : Ideal A) [q.IsPrime], q.LiesOver p → Algebra.IsEtaleAt R q) :
    ∃ h ∉ p, Algebra.Etale R (Localization.Away (algebraMap R A h)) := by
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R _
  set Z : Set (PrimeSpectrum A) := (Algebra.etaleLocus R A)ᶜ
  have hWclosed : IsClosed (PrimeSpectrum.comap (algebraMap R A) '' Z) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral x) _
      Algebra.isOpen_etaleLocus.isClosed_compl
  have hpW : (⟨p, ‹_›⟩ : PrimeSpectrum R) ∉ PrimeSpectrum.comap (algebraMap R A) '' Z := by
    rintro ⟨Q, hQZ, hQ⟩
    exact hQZ (hetale Q.asIdeal ⟨congrArg PrimeSpectrum.asIdeal hQ.symm⟩)
  obtain ⟨_, ⟨h, rfl⟩, hph, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpW
      hWclosed.isOpen_compl
  refine ⟨h, hph, ?_⟩
  rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
  intro Q hQ
  by_contra hQn
  exact hsub (show PrimeSpectrum.comap (algebraMap R A) Q ∈ _ by
    simpa [PrimeSpectrum.mem_basicOpen] using hQ) ⟨Q, hQn, rfl⟩

/-- **`R[x]/(f)` becomes étale after inverting one element outside `p`.** For monic `f : R[X]`
whose reduction over `R ⧸ p` is coprime to its derivative, there is an `h ∉ p` such that
`R[x]/(f)` localized away from `h` is étale over `R`. -/
public theorem exists_notMem_etale_localizationAway_adjoinRoot {R : Type u} [CommRing R]
    {f : R[X]} (hf : f.Monic) (p : Ideal R) [p.IsPrime]
    (hsep : IsCoprime (f.map (Ideal.Quotient.mk p)) (derivative (f.map (Ideal.Quotient.mk p)))) :
    ∃ h ∉ p, Algebra.Etale R
      (Localization.Away (algebraMap R (AdjoinRoot f) h)) := by
  have := hf.finite_adjoinRoot
  exact exists_notMem_etale_localizationAway p fun q _ _ => isEtaleAt_of_liesOver hf p hsep q

/-- **The finite free refinement of Stacks 00UD.** Let `R` be a ring, `p` a prime of `R` and
`L/κ(p)` a finite separable field extension. Then there are a finite free `R`-algebra `R'` and a
prime `p'` of `R'` lying over `p` at which `R'` is étale over `R`, together with an isomorphism
`κ(p') ≃ L` of extensions of `κ(p)`, i.e. one carrying the canonical map `κ(p) → κ(p')` induced by
`R → R'` to the structure map `κ(p) → L`.

Compare `Algebra.exists_etale_liesOver_residueFieldRingEquiv` (Stacks 00UD), which asserts
étaleness of `R → R'` everywhere but produces an `R'` that is a localization of this one, hence not
finite. Both are needed: this form is the one used in the proof of Stacks 0551, where `R'` must be
finite over `R` so that `Spec(R') → Spec(R)` is a closed map. -/
public theorem exists_finite_free_isEtaleAt_liesOver_residueFieldRingEquiv {R : Type u}
    [CommRing R] (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Free R R')
      (_ : Module.Finite R R') (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      (_ : Algebra.IsEtaleAt R p') (e : p'.ResidueField ≃+* L),
      (e : p'.ResidueField →+* L).comp
        (Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)) =
          algebraMap p.ResidueField L := by
  let _ : Algebra R L :=
    ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField)).toAlgebra
  have : IsScalarTower R p.ResidueField L := .of_algebraMap_eq' rfl
  obtain ⟨f, β, hfmon, hf0, hfu, hβ⟩ :=
    Stacks.Etale.ResidueFieldRealization.exists_monic_aeval_eq_zero_and_adjoin_eq_top p L
  let φ : AdjoinRoot f →ₐ[R] L := AdjoinRoot.liftAlgHom f (Algebra.ofId R L) β hf0
  have hφalg : ∀ r : R, φ (algebraMap R (AdjoinRoot f) r) = algebraMap R L r := φ.commutes
  let ψ : AdjoinRoot f →+* L := φ.toRingHom
  set p' : Ideal (AdjoinRoot f) := RingHom.ker ψ with hp'def
  have hp'prime : p'.IsPrime := RingHom.ker_isPrime ψ
  have hkerRL : RingHom.ker (algebraMap R L) = p := by
    ext x
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R p.ResidueField L,
      map_eq_zero_iff _ (algebraMap p.ResidueField L).injective,
      Ideal.algebraMap_residueField_eq_zero]
  have hlo : p'.LiesOver p := by
    refine ⟨?_⟩
    rw [Ideal.under_def, hp'def, RingHom.comap_ker, ← hkerRL]
    congr 1
    exact (RingHom.ext hφalg).symm
  have hd : AdjoinRoot.mk f (derivative f) ∉ p' := by
    rw [hp'def, RingHom.mem_ker]
    exact hfu.ne_zero
  let e0 : p'.ResidueField →+* L := IsFractionRing.lift (RingHom.kerLift_injective ψ)
  have he0 : ∀ y : AdjoinRoot f, e0 (algebraMap (AdjoinRoot f) p'.ResidueField y) = ψ y := by
    intro y
    rw [← Ideal.algebraMap_quotient_residueField_mk p' y]
    exact (IsFractionRing.lift_algebraMap _ _).trans (RingHom.kerLift_mk ψ y)
  have heq : e0.comp (Ideal.ResidueField.map p p' (algebraMap R (AdjoinRoot f))
      (p'.over_def p)) = algebraMap p.ResidueField L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p)) ?_
    ext r
    simp only [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk,
      Ideal.ResidueField.map_algebraMap, he0]
    exact (hφalg r).trans (IsScalarTower.algebraMap_apply R p.ResidueField L r)
  have hsurj : Function.Surjective e0 := by
    have hmem : ∀ x : p.ResidueField, algebraMap p.ResidueField L x ∈ e0.fieldRange := fun x =>
      ⟨_, by rw [← RingHom.comp_apply, heq]⟩
    have hle : (⊤ : IntermediateField p.ResidueField L) ≤
        (e0.fieldRange).toIntermediateField hmem := by
      rw [← hβ, IntermediateField.adjoin_simple_le_iff]
      exact ⟨_, (he0 _).trans (AdjoinRoot.liftAlgHom_root f (Algebra.ofId R L) β hf0)⟩
    exact fun _ => RingHom.mem_fieldRange.mp (hle IntermediateField.mem_top)
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, hfmon.free_adjoinRoot,
    hfmon.finite_adjoinRoot, p', hp'prime, hlo, isEtaleAt_of_derivative_notMem hfmon p' hd,
    RingEquiv.ofBijective e0 ⟨e0.injective, hsurj⟩, heq⟩

end Stacks.GeometricComponents

end

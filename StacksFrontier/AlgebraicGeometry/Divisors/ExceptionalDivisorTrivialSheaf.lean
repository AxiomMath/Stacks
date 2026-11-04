module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleTrivialInCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower

/-!
# An exceptional effective Cartier divisor with trivial invertible sheaf is zero

Let `A` be a Noetherian local ring of dimension two, and let `f : X ⟶ Spec(A)` be a surjective
morphism inducing an isomorphism `A = Γ(X, 𝒪_X)` on global sections — for instance a
modification of `Spec(A)` with `A` normal. Let `E ⊆ X` be an effective Cartier divisor supported
on the fibre of `f` over the closed point. If `𝒪_X(E)` has a nowhere vanishing global section
`t`, then `E = 0`.

This is the last step of the second sentence of [Stacks, Tag 0EA2]: there `𝒪_X(E) ≅ ω_X`, and the
source shows that `f^*ω_A = 𝒪_X ⟶ ω_X` is surjective, which provides `t`.

## The argument

Since `t` vanishes nowhere, multiplication by `t` identifies `𝒪_X` with `𝒪_X(E)`
([Stacks, Tag 01CY]), so the canonical section is `1_E = b · t` for a global function `b`, and
`1_E` vanishes exactly on `E` (`Stacks.Divisors.nonvanishingLocus_canonicalSections`). So `E` is
the zero locus of `b`. Write `b = f^*a` with `a ∈ A`. If `a` were not a unit, then `a` would lie in
a prime `𝔭 ≠ 𝔪` (a prime minimal over `(a)` has height at most one by Krull's principal ideal
theorem, while `𝔪` has height two), and a point of `X` over `𝔭` would lie on `E`, which is
supported over `𝔪`. So `a` is a unit, `E` is empty, i.e. `E = 0`.

## Main results

* `Stacks.Divisors.exists_isPrime_ne_maximalIdeal_mem`: in a Noetherian local ring of dimension
  two, every element of the maximal ideal lies in a prime other than the maximal ideal.
* `Stacks.Divisors.eq_top_of_forall_mem_nonvanishingLocus`: the vanishing of `E`, given a
  nowhere vanishing global section of `𝒪_X(E)`.
* `Stacks.Divisors.eq_top_of_nonempty_iso_unit`: the same, given `𝒪_X ≅ 𝒪_X(E)`.
* `Stacks.Divisors.eq_top_of_pullback_iso_unit`: the same for a modification of `Spec(A)` with
  `A` normal and `X` normal, given only that `𝒪_X(E)` is trivial over an open containing every
  point of codimension at most one: by [Stacks, Tag 0E9I] it is then trivial
  (`AlgebraicGeometry.nonempty_iso_unit_of_pullback_iso`).
* `Stacks.Divisors.eq_top_of_nonempty_pullback_iso_unit`: the same with the coherence of
  `𝒪_X(E)` proved rather than assumed.

## Implementation notes

The zero divisor is the top ideal sheaf, which cuts out the empty closed subscheme.
`Stacks.Divisors.invertibleSheaf` and `Stacks.Divisors.invertibleSheaf'` are the same sheaf
(`rfl`), spelled with `X.sheaf.obj` respectively `X.presheaf`; the statement is made with the
former, the spelling of `Stacks.Divisors.nonvanishingLocus_canonicalSections`.

## References

* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **In a Noetherian local ring of dimension two every element of the maximal ideal lies in a
prime other than the maximal ideal.** A prime minimal over `(a)` has height at most one by
Krull's principal ideal theorem, while the maximal ideal has height two. -/
theorem exists_isPrime_ne_maximalIdeal_mem {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (hdim : ringKrullDim A = 2) {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    ∃ p : Ideal A, p.IsPrime ∧ p ≠ IsLocalRing.maximalIdeal A ∧ a ∈ p := by
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a})
    (J := IsLocalRing.maximalIdeal A) ((Ideal.span_singleton_le_iff_mem _).2 ha)
  have hpp : p.IsPrime := hp.1.1
  refine ⟨p, hpp, fun hpm => ?_, hp.1.2 (Ideal.mem_span_singleton_self a)⟩
  have hle : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  have h2 : ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) = 2 := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
  rw [← hpm] at h2
  have : ((p.height : ℕ∞) : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hle
  rw [h2] at this
  exact absurd this (by decide)

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **An effective Cartier divisor supported over the closed point whose invertible sheaf has a
nowhere vanishing global section is zero**, for a surjective `f : X ⟶ Spec(A)` inducing an
isomorphism on global sections, `A` Noetherian local of dimension two. -/
theorem eq_top_of_forall_mem_nonvanishingLocus (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hsurj : Function.Surjective f) [IsIso f.appTop]
    (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]
    (hE : ∀ x : X, x ∈ E.support → f x = IsLocalRing.closedPoint A)
    (t : (invertibleSheaf E).val.obj (op ⊤))
    (ht : ∀ x : X, x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (invertibleSheaf E) (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) _ t)) :
    E = ⊤ := by
  have : ∀ x : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x) :=
    fun x => X.isLocalRing x
  have hbij := Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen
    (X := X.toRingedSpace) (invertibleSheaf E)
    (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) _ t) ⊤
    (fun x _ => ht x)
  obtain ⟨b, hb⟩ := hbij.2 (canonicalSection E)
  rw [Stacks.SheafOfModules.sectionsOfTop_eval_top] at hb
  have hsupp : ∀ x : X, x ∈ (E.supportSet)ᶜ ↔ x ∈ X.toRingedSpace.basicOpen b := by
    intro x
    rw [← nonvanishingLocus_canonicalSections E]
    show x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (invertibleSheaf E)
      (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) _ (canonicalSection E)) ↔ _
    rw [← hb, Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_smul]
    exact ⟨fun h => h.1, fun h => ⟨h, ht x⟩⟩
  obtain ⟨a', ha'⟩ := (ConcreteCategory.bijective_of_isIso f.appTop).2 b
  set a : A := (Scheme.ΓSpecIso (.of A)).hom a' with ha
  have hmem : ∀ x : X, x ∈ X.toRingedSpace.basicOpen b ↔ a ∉ (f x).asIdeal := by
    intro x
    show x ∈ X.basicOpen b ↔ _
    rw [← ha', ← Scheme.preimage_basicOpen_top]
    exact (congrArg (fun U : (Spec (.of A)).Opens => f x ∈ U) (basicOpen_eq_of_affine' a')).to_iff
  have hunit : a ∉ IsLocalRing.maximalIdeal A := by
    intro ham
    obtain ⟨p, hp, hpm, hap⟩ := exists_isPrime_ne_maximalIdeal_mem hdim ham
    obtain ⟨x, hx⟩ := hsurj ⟨p, hp⟩
    have hxE : x ∈ E.support := by
      by_contra hxE
      have := (hmem x).1 ((hsupp x).1 hxE)
      rw [hx] at this
      exact this hap
    have := hE x hxE
    rw [hx] at this
    exact hpm (congrArg PrimeSpectrum.asIdeal this)
  apply (Scheme.IdealSheafData.support_eq_bot_iff E).1
  ext x
  simp only [Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact (hsupp x).2 ((hmem x).2 fun hax =>
    hunit (IsLocalRing.le_maximalIdeal (f x).isPrime.ne_top hax)) hx

/-- **An effective Cartier divisor supported over the closed point with `𝒪_X(E) ≅ 𝒪_X` is
zero**, in the situation of `Stacks.Divisors.eq_top_of_forall_mem_nonvanishingLocus`: the image
of the unit section under the isomorphism vanishes nowhere. -/
theorem eq_top_of_nonempty_iso_unit (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hsurj : Function.Surjective f) [IsIso f.appTop]
    (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]
    (hE : ∀ x : X, x ∈ E.support → f x = IsLocalRing.closedPoint A)
    (e : Nonempty ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ invertibleSheaf' E)) :
    E = ⊤ := by
  obtain ⟨e⟩ := e
  let s := SheafOfModules.sectionsMap e.hom
    (Stacks.SheafOfModules.unitSections X.toRingedSpace)
  refine eq_top_of_forall_mem_nonvanishingLocus hdim f hsurj E hE (s.eval (op ⊤)) fun x => ?_
  rw [Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_eval (X := X.toRingedSpace)
    (invertibleSheaf E) s]
  refine (nonvanishingLocus_iso (L := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M := (invertibleSheaf' E : X.Modules)) e _ x).2 ?_
  exact (Set.ext_iff.1 (Stacks.SheafOfModules.nonvanishingLocus_unitSections X.toRingedSpace) x).2
    trivial

/-- **The second sentence of [Stacks, Tag 0EA2], from triviality in codimension one.** Let `A` be
a Noetherian normal local domain of dimension two, `f : X ⟶ Spec(A)` a modification with `X`
normal, and `E` an effective Cartier divisor on `X` supported on the closed fibre. If `𝒪_X(E)`
is trivial over an open `V ⊆ X` containing every point of codimension at most one, then
`E = 0`. The coherence of `𝒪_X(E)` is an argument `hcoh` here. -/
theorem eq_top_of_pullback_iso_unit [IsNormalDomain A]
    (hdim : ringKrullDim A = 2) {X : Scheme.{u}} [IsNormal X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of A)) (hf : IsModification f)
    (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]
    (hE : ∀ x : X, x ∈ E.support → f x = IsLocalRing.closedPoint A)
    (hcoh : (invertibleSheaf' E : X.Modules).IsCoherent)
    (V : X.Opens) (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V)
    (e : Nonempty ((Scheme.Modules.pullback V.ι).obj (invertibleSheaf' E : X.Modules) ≅
      (Scheme.Modules.pullback V.ι).obj (SheafOfModules.unit X.ringCatSheaf))) :
    E = ⊤ := by
  obtain ⟨e⟩ := e
  have := hf.isProper
  have := hf.source_isIntegral
  have : IsIso f.appTop := hf.isIso_appTop
  have : IsDominant f := IsBirational.isDominant hf.isBirational
  have hsurj : Function.Surjective f := (inferInstance : Surjective f).surj
  obtain ⟨e'⟩ := @nonempty_iso_unit_of_pullback_iso X _ _ (invertibleSheaf' E : X.Modules)
    (invertibleSheaf_isInvertible E) hcoh V hV e
  exact eq_top_of_nonempty_iso_unit hdim f hsurj E hE ⟨e'.symm⟩

/-- `Stacks.Divisors.eq_top_of_pullback_iso_unit` without the coherence hypothesis: the sheaf
`𝒪_X(E)` of an effective Cartier divisor is invertible, hence coherent on the locally Noetherian
scheme `X` (`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible`). -/
theorem eq_top_of_nonempty_pullback_iso_unit [IsNormalDomain A]
    (hdim : ringKrullDim A = 2) {X : Scheme.{u}} [IsNormal X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of A)) (hf : IsModification f)
    (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]
    (hE : ∀ x : X, x ∈ E.support → f x = IsLocalRing.closedPoint A)
    (V : X.Opens) (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V)
    (e : Nonempty ((Scheme.Modules.pullback V.ι).obj (invertibleSheaf' E : X.Modules) ≅
      (Scheme.Modules.pullback V.ι).obj (SheafOfModules.unit X.ringCatSheaf))) :
    E = ⊤ :=
  eq_top_of_pullback_iso_unit hdim f hf E hE
    (Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _) V hV e

end Stacks.Divisors

end

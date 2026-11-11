module

public import Mathlib.Algebra.Polynomial.Roots
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInductionStep
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTriviality
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnit
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardInjectivitySGA2
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsionExponent
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.PuncturedSpectrumCompletion

/-!
# Torsion in the Picard group of a punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪` be a nonzerodivisor with
`depth(A/fA) ≥ 2`, equivalently `depth(A) ≥ 3`. Let `U`, resp. `U₀`, be the punctured spectrum
of `A`, resp. of `A/fA`. Then `Pic(U) → Pic(U₀)` is injective on torsion. This is
[Stacks, Tag 0F2A].

## The proof

The argument is the source's. Let `ℒ` be an invertible module on `U` whose class is torsion and
whose restriction to `U₀` is trivial. Triviality on `U₀` is exactly what is needed to complete
`ℒ` to an *invertible coherent triple* `(ℒ, 𝒪_{X₀}, λ)`: the member on the closed fibre may be
taken to be the structure sheaf there, and the identification over the punctured closed fibre is
the given trivialisation. Twisting the unit coherent triple by the `n`-th power of that triple
produces a family whose member on the punctured spectrum is `ℒ^{⊗ n}`, so by the vanishing
criterion [Stacks, Tag 0F28] the Euler characteristic of the `n`-th twist vanishes exactly when
`n` times the class of `ℒ` is zero. By [Stacks, Tag 0F27] those Euler characteristics are the
values of a rational polynomial. If the class of `ℒ` has finite order `m`, that polynomial
vanishes at every nonnegative multiple of `m`, hence identically; its value at `1` is then zero
too, so the class of `ℒ` itself is zero.

## The polynomiality input

[Stacks, Tag 0F27] -- the polynomiality of `n ↦ χ((ℱ, ℱ₀, α) ⊗ (ℒ, ℒ₀, λ)^{⊗ n})` -- is
`Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp`, proved in
`StacksFrontier/AlgebraicGeometry/Algebraization/CoherentTripleHilbertInductionStep.lean`. The
deduction here uses it with its bound on the degree forgotten.

## Main definitions

* `Stacks.Algebraization.coherentTripleOfTrivialRestriction`: the invertible coherent triple
  built from an invertible module on `U` whose restriction to `U₀` is trivial.

## Main results

* `Stacks.Algebraization.three_le_depth_of_two_le_depth_quotient`: the equivalence the source
  records in its hypothesis -- for `f ∈ 𝔪` a nonzerodivisor, `depth(A/fA) ≥ 2` gives
  `depth(A) ≥ 3`.
* `Stacks.Algebraization.isSMulRegular_structureSheafSections`: a nonzerodivisor of a ring is a
  nonzerodivisor on the sections of the structure sheaf over every open of its spectrum.
* `Stacks.Algebraization.isFTorsionFree_unitModule`: hence the structure sheaf of the punctured
  spectrum is `f`-torsion-free for every nonzerodivisor `f`, which the rest of this section
  carries as a hypothesis.
* `Stacks.Algebraization.eq_zero_of_schemePullbackClass_eq_zero_of_isOfFinAddOrder`: a torsion
  class on `U` restricting to zero on `U₀` is zero.
* `Stacks.Algebraization.picRestrictionInjOnTorsion`: **[Stacks, Tag 0F2A]**.

## Implementation notes

`U` is `Stacks.Divisors.puncturedSpectrum A` and `U₀` is
`Stacks.Algebraization.puncturedClosedFibre A f`, the part of `Spec(A/fA)` lying over `U`; for
`f ∈ 𝔪` that is the punctured spectrum of `A/fA`. The restriction `U₀ ⟶ U` is
`Stacks.Algebraization.puncturedClosedFibreRestriction A f`, the arrow already used for the
compatibility datum of a coherent triple, and the map on Picard groups is
`Stacks.Picard.schemePullbackClass` of it -- the spelling [Stacks, Tag 0F2G] and
[Stacks, Tag 0FIX] are stated at. Torsion is `IsOfFinAddOrder`, the Picard group of
`Stacks.Picard` being additive, and injectivity on it is `Set.InjOn` on the set of classes of
finite order.

That the structure sheaf of the punctured spectrum is `f`-torsion-free -- which the rest of this
section carries as a hypothesis, and whose obstruction is recorded in
`StacksFrontier/AlgebraicGeometry/Algebraization/CoherentTripleUnit.lean` -- is *not* assumed here.
It is proved, as `Stacks.Algebraization.isFTorsionFree_unitModule`, from `f` being a
nonzerodivisor. The route that note describes goes through associated points; the route taken
here does not need them, since a section of the structure sheaf is determined by its germs and
each stalk is a flat, hence torsion-free, `A`-algebra.
`Stacks.Algebraization.isFTorsionFree_of_isInvertible` then carries it to every invertible module
on `U`, which is what a coherent triple needs.

Only nonnegative tensor powers occur: the polynomial is shown to vanish on the nonnegative
multiples of the order, which are already infinitely many, and the conclusion is read off at the
exponent `1`. That is why `Stacks.Picard.classOf_tensorPower`, which is available for natural
number exponents only, suffices.

## References

* [Stacks Project, Tag 0F2A](https://stacks.math.columbia.edu/tag/0F2A)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

open Stacks.RingedSpace (structureIsSheaf)

open scoped Pointwise

universe u

namespace Stacks.Algebraization

/-! ### The two elementary inputs -/

/-- **The equivalence recorded in the hypothesis of [Stacks, Tag 0F2A]**, in the direction its
proof needs: for `f ∈ 𝔪` a nonzerodivisor, `depth(A/fA) ≥ 2` gives `depth(A) ≥ 3`. This is
[Stacks, Tag 090R], which says `depth(A/fA) + 1 = depth(A)`. -/
public theorem three_le_depth_of_two_le_depth_quotient (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (hfm : f ∈ maximalIdeal A)
    (hf : IsSMulRegular A f)
    (hb : 2 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f})) :
    3 ≤ Module.depth A (maximalIdeal A) A := by
  have hspan : (f • (⊤ : Submodule A A)) = Ideal.span {f} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have hbridge : Module.depth A (maximalIdeal A) (QuotSMulTop f A) =
      Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f}) :=
    Module.depth_eq_depth_of_linearEquiv _ (Submodule.quotEquivOfEq _ _ hspan)
  have h090R := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (maximalIdeal A) A).1 f hfm hf
  rw [hbridge] at h090R
  rw [← h090R]
  exact le_trans (by norm_num : (3 : ℕ∞) ≤ 2 + 1) (add_le_add hb le_rfl)

/-- **A rational polynomial vanishing at every nonnegative multiple of a positive integer is
zero.** The multiples are infinitely many, so the polynomial has infinitely many roots. -/
public theorem eq_zero_of_eval_natMul_eq_zero {P : Polynomial ℚ} {m : ℕ} (hm : 0 < m)
    (h : ∀ k : ℕ, P.eval ((k * m : ℕ) : ℚ) = 0) : P = 0 := by
  refine P.eq_zero_of_infinite_isRoot ?_
  have hinj : Function.Injective fun k : ℕ => ((k * m : ℕ) : ℚ) := fun a b hab => by
    have hab' : a * m = b * m := Nat.cast_injective hab
    exact Nat.eq_of_mul_eq_mul_right hm hab'
  exact Set.infinite_of_injective_forall_mem hinj fun k => h k

/-! ### `f`-torsion-freeness of the structure sheaf of the punctured spectrum -/

/-- **A nonzerodivisor of a ring is a nonzerodivisor on the sections of the structure sheaf over
every open of its spectrum.** A section is determined by its germs, each stalk is a localization
of the ring, and a localization is flat, so multiplication by the element stays injective on each
stalk and hence on the sections.

This is the elementary route to the `f`-torsion-freeness that the rest of this section used to
carry as a hypothesis. The route recorded as missing in
`StacksFrontier/AlgebraicGeometry/Algebraization/CoherentTripleUnit.lean` -- that a nonzerodivisor
lies in no associated prime, so [Stacks, Tag 0AVL] makes multiplication by it a monomorphism --
needs a comparison of the associated points of a structure sheaf with the associated primes of
the ring. No such comparison is needed: flatness of localization already gives injectivity at
every point of the spectrum, associated or not. -/
public theorem isSMulRegular_structureSheafSections (A : Type u) [CommRing A] {f : A}
    (hf : IsSMulRegular A f) (W : TopologicalSpace.Opens (PrimeSpectrum.Top A)) :
    IsSMulRegular ((Spec.structureSheaf A).obj.obj (Opposite.op W))
      (algebraMap A ((Spec.structureSheaf A).obj.obj (Opposite.op W)) f) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext (Spec.structureSheaf A) W s t fun x hx => ?_
  have hstalk : IsSMulRegular ((Spec.structureSheaf A).presheaf.stalk x)
      (algebraMap A ((Spec.structureSheaf A).presheaf.stalk x) f) :=
    hf.of_isLocalization _ x.asIdeal.primeCompl
  refine hstalk ?_
  have key : ∀ z : (Spec.structureSheaf A).obj.obj (Opposite.op W),
      (Spec.structureSheaf A).presheaf.germ W x hx
          (algebraMap A ((Spec.structureSheaf A).obj.obj (Opposite.op W)) f * z)
        = algebraMap A ((Spec.structureSheaf A).presheaf.stalk x) f *
            (Spec.structureSheaf A).presheaf.germ W x hx z := by
    intro z
    rw [map_mul]
    congr 1
    exact AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply W x hx f
  have hst' : algebraMap A ((Spec.structureSheaf A).obj.obj (Opposite.op W)) f * s
      = algebraMap A ((Spec.structureSheaf A).obj.obj (Opposite.op W)) f * t := hst
  have hgerm := congrArg ((Spec.structureSheaf A).presheaf.germ W x hx) hst'
  rw [key s, key t] at hgerm
  exact hgerm

/-- **The structure sheaf of the punctured spectrum is `f`-torsion-free for every nonzerodivisor
`f` of `A`.** An open of the punctured spectrum is an open of `Spec A`, the image of `f` in its
functions is the image of `f` under the structure map, and
`Stacks.Algebraization.isSMulRegular_structureSheafSections` applies.

This discharges the hypothesis that [Stacks, Tag 0F2A] does not make and that the rest of this
section carries: a coherent triple on `(A, f)` may now be built out of any invertible module on
the punctured spectrum with no torsion-freeness assumed. -/
public theorem isFTorsionFree_unitModule (A : Type u) [CommRing A] [IsLocalRing A] {f : A}
    (hf : IsSMulRegular A f) :
    IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) := fun V =>
  isSMulRegular_structureSheafSections A hf
    ((Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ V)

/-! ### The invertible coherent triple attached to a trivial restriction -/

/-- **The invertible coherent triple of an invertible module trivial on the punctured closed
fibre.** Its member on the punctured spectrum is the given module, its member on the closed fibre
is the structure sheaf of `Spec(A/fA)`, and its identification over the punctured closed fibre is
the given trivialisation followed by the canonical identification of the inverse image of a
structure sheaf.

This is the completion [Stacks, Tag 0F2A] makes: an invertible module on `U` extends to an
invertible coherent triple as soon as it is trivial on `U₀`. -/
public def coherentTripleOfTrivialRestriction (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A)
    (htf : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    (L : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme L]
    (e : (Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj L ≅
      Stacks.Ample.unitModule (puncturedClosedFibre A f).toScheme) :
    CoherentTriple A f where
  F := L
  F₀ := Stacks.Ample.unitModule (closedFibre A f)
  coherent_F := by
    exact @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _
      (isLocallyNoetherian_of_isOpenImmersion (Stacks.Divisors.puncturedSpectrum A).ι) L
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›)
  coherent_F₀ := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit _
  torsionFree :=
    isFTorsionFree_of_isInvertible A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) L htf
  alpha :=
    e ≪≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
      (puncturedClosedFibre A f).ι).symm

/-- The punctured-spectrum member of
`Stacks.Algebraization.coherentTripleOfTrivialRestriction` is the given module. -/
@[simp]
public theorem coherentTripleOfTrivialRestriction_F (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A)
    (htf : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    (L : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme L]
    (e : (Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj L ≅
      Stacks.Ample.unitModule (puncturedClosedFibre A f).toScheme) :
    (coherentTripleOfTrivialRestriction A f htf L e).F = L := rfl

/-- The triple of `Stacks.Algebraization.coherentTripleOfTrivialRestriction` is invertible: its
member on the punctured spectrum is the given invertible module and its member on the closed
fibre is a structure sheaf. -/
public theorem isInvertibleTriple_coherentTripleOfTrivialRestriction (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (htf : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    (L : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme L]
    (e : (Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj L ≅
      Stacks.Ample.unitModule (puncturedClosedFibre A f).toScheme) :
    IsInvertibleTriple (coherentTripleOfTrivialRestriction A f htf L e) where
  invertible_F := ‹_›
  invertible_F₀ := Stacks.Ample.isInvertibleModule_unit _

/-- The unit coherent triple is invertible: both its members are structure sheaves. -/
public theorem isInvertibleTriple_unit (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A)
    (htf : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme)) :
    IsInvertibleTriple (CoherentTriple.unit A f htf) where
  invertible_F := Stacks.Ample.isInvertibleModule_unit _
  invertible_F₀ := Stacks.Ample.isInvertibleModule_unit _

/-! ### A torsion class trivial on the punctured closed fibre is zero -/

/-- **A torsion class on the punctured spectrum whose restriction to the punctured closed fibre
is zero is itself zero.** This is the content of [Stacks, Tag 0F2A]; the injectivity statement
follows from it by subtraction.

Let `ℒ` represent the class. Its restriction being zero makes `ℒ^{⊗ n}` the punctured-spectrum
member of the `n`-th twist of the unit coherent triple by the invertible coherent triple
`(ℒ, 𝒪_{X₀}, λ)` of `Stacks.Algebraization.coherentTripleOfTrivialRestriction`, so by
[Stacks, Tag 0F28] the Euler characteristic of that twist vanishes exactly when `n` times the
class does. Those Euler characteristics are polynomial in `n` by [Stacks, Tag 0F27]
(`Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp`), and the
polynomial vanishes at every nonnegative multiple of the order of the class, hence identically,
hence at `1`. -/
public theorem eq_zero_of_schemePullbackClass_eq_zero_of_isOfFinAddOrder (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A)
    (hreg : IsRegular f) (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A)
    {x : Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum A).toScheme}
    (hx : IsOfFinAddOrder x)
    (h0 : Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f) x = 0) :
    x = 0 := by
  have htf : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) :=
    isFTorsionFree_unitModule A hreg.left
  -- the invertible module representing `x`
  set L := (Stacks.Picard.picardRepresentative
    (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace x).obj with hLdef
  have hLs : Stacks.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L :=
    (Stacks.Picard.picardRepresentative
      (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace x).property
  have hclass : Stacks.SheafOfModules.picardClass
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L hLs = x :=
    Stacks.Picard.classOf_picardRepresentative _ x
  have hLamp : Stacks.Ample.IsInvertibleModule
      (Stacks.Divisors.puncturedSpectrum A).toScheme L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1 hLs
  -- `L` is trivial on the punctured closed fibre, so it completes to an invertible triple
  have hpull : Stacks.SheafOfModules.picardClass (puncturedClosedFibre A f).toScheme.presheaf
      (structureIsSheaf (puncturedClosedFibre A f).toScheme.toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom).obj L)
      (Stacks.RingedSpace.modulePullback_isInvertible_of
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom L hLs) = 0 := by
    rw [← Stacks.Picard.pullbackClass_classOf
      (puncturedClosedFibreRestriction A f).toLRSHom.toShHom L hLs, hclass]
    exact h0
  have htriv : Stacks.SheafOfModules.IsTrivial
      (puncturedClosedFibre A f).toScheme.presheaf
      (puncturedClosedFibre A f).toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj L) :=
    (Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit _ _).1 hpull
  obtain ⟨e⟩ := htriv
  have e' : (Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).obj L ≅
      Stacks.Ample.unitModule (puncturedClosedFibre A f).toScheme := e
  set T := coherentTripleOfTrivialRestriction A f htf L e' with hTdef
  have hT : IsInvertibleTriple T :=
    isInvertibleTriple_coherentTripleOfTrivialRestriction A f htf L e'
  -- the Euler characteristics of the twists of the unit triple
  obtain ⟨P, -, hP⟩ := exists_polynomial_natDegree_le_dim_supp hf T hT
    (CoherentTriple.unit A f htf)
  have hkey : ∀ n : ℕ,
      ((CoherentTriple.unit A f htf).twistZ T hT (n : ℤ)).eulerCharacteristic = 0 ↔
        (n : ℤ) • x = 0 := by
    intro n
    have hinv := isInvertibleTriple_twistZ (isInvertibleTriple_unit A f htf) hT (n : ℤ)
    have h1 := hinv.invertible_F
    have h2 := hinv.invertible_F₀
    have hpow : Stacks.SheafOfModules.IsInvertible
        (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
        (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L (n : ℤ)) :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
        (isInvertibleModule_tensorPowScheme _ L (n : ℤ))
    have hiso := CoherentTriple.unit_twistZ_F_iso A f htf T hT (n : ℤ)
    rw [CoherentTriple.eulerCharacteristic_eq_zero_iff_isTrivial A f hf hreg _ hdepth,
      ← hclass, ← Stacks.Picard.classOf_tensorPower
        (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
        (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L n,
      Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit _ hpow]
    exact ⟨fun ⟨e₁⟩ => ⟨hiso.symm ≪≫ e₁⟩, fun ⟨e₁⟩ => ⟨hiso ≪≫ e₁⟩⟩
  -- the polynomial vanishes on the multiples of the order of `x`, hence identically
  have hm : 0 < addOrderOf x := hx.addOrderOf_pos
  have hmx : ((addOrderOf x : ℕ) : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    exact addOrderOf_nsmul_eq_zero x
  have hroot : ∀ k : ℕ, P.eval ((k * addOrderOf x : ℕ) : ℚ) = 0 := by
    intro k
    have hz : ((k * addOrderOf x : ℕ) : ℤ) • x = 0 := by
      have hcast : ((k * addOrderOf x : ℕ) : ℤ) = (k : ℤ) * ((addOrderOf x : ℕ) : ℤ) := by
        push_cast; ring
      rw [hcast, ← smul_smul, hmx, smul_zero]
    have hq := hP ((k * addOrderOf x : ℕ) : ℤ)
    rw [(hkey (k * addOrderOf x)).2 hz] at hq
    have hq2 : P.eval ((((k * addOrderOf x : ℕ) : ℤ) : ℚ)) = 0 := by rw [← hq]; norm_num
    simpa using hq2
  have hP0 : P = 0 := eq_zero_of_eval_natMul_eq_zero hm hroot
  have hone : ((1 : ℕ) : ℤ) • x = 0 := by
    refine (hkey 1).1 ?_
    have hq := hP ((1 : ℕ) : ℤ)
    rw [hP0, Polynomial.eval_zero] at hq
    exact_mod_cast hq
  rwa [Nat.cast_one, one_zsmul] at hone

/-! ### Tag 0F2A -/

/-- **Stacks Project, Tag 0F2A.** Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪` be a
nonzerodivisor with `depth(A/fA) ≥ 2`. Let `U` be the punctured spectrum of `A` and `U₀` the
punctured spectrum of `A/fA`. Then `Pic(U) → Pic(U₀)` is injective on torsion.

Two classes of finite order with the same restriction have a difference of finite order
restricting to zero, and such a difference is zero by
`Stacks.Algebraization.eq_zero_of_schemePullbackClass_eq_zero_of_isOfFinAddOrder`.

The Euler-characteristic polynomiality the argument rests on is [Stacks, Tag 0F27], proved as
`Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp`, and the `f`-torsion-freeness of
`𝒪_U` is proved, from `f` being a nonzerodivisor, by
`Stacks.Algebraization.isFTorsionFree_unitModule`. -/
@[stacks 0F2A]
public theorem picRestrictionInjOnTorsion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hfm : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hb : 2 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f})) :
    Set.InjOn (Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f))
      {x : Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum A).toScheme |
        IsOfFinAddOrder x} := by
  have hdepth : 3 ≤ Module.depth A (maximalIdeal A) A :=
    three_le_depth_of_two_le_depth_quotient A f hfm hreg.left hb
  intro x hx y hy hxy
  have hx' : IsOfFinAddOrder x := hx
  have hy' : IsOfFinAddOrder y := hy
  have hsub : Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f) (x - y)
      = 0 := by
    have h := (Stacks.Picard.schemePullbackClassHom
      (puncturedClosedFibreRestriction A f)).map_sub x y
    rw [Stacks.Picard.pullbackClassHom_apply, Stacks.Picard.pullbackClassHom_apply,
      Stacks.Picard.pullbackClassHom_apply] at h
    have hxy' : Stacks.Picard.pullbackClass
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom x =
      Stacks.Picard.pullbackClass
        (puncturedClosedFibreRestriction A f).toLRSHom.toShHom y := hxy
    change Stacks.Picard.pullbackClass
      (puncturedClosedFibreRestriction A f).toLRSHom.toShHom (x - y) = 0
    rw [h, hxy', sub_self]
  have htors : IsOfFinAddOrder (x - y) := by
    rw [sub_eq_add_neg]
    exact hx'.add hy'.neg
  exact sub_eq_zero.1 (eq_zero_of_schemePullbackClass_eq_zero_of_isOfFinAddOrder A f hfm hreg
    hdepth htors hsub)

end Stacks.Algebraization

end

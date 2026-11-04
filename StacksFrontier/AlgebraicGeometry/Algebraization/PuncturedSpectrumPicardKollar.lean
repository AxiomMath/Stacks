module

public import StacksFrontier.Algebra.Polynomial.NonnegLinearBound
public import StacksFrontier.AlgebraicGeometry.Algebraization.KollarLinearBound
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardTorsion
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInductionStep
public import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Serre.LocalizationDepthCodimension

/-!
# Kollár's injectivity for the Picard group of a punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring admitting a dualizing complex and let `f ∈ 𝔪` be a
nonzerodivisor with `depth(A/fA) ≥ 2`. Assume moreover that every prime `𝔭 ∋ f` with
`dim(A/𝔭) = 2` satisfies `depth(A_𝔭) ≥ 2`. Let `U`, resp. `U₀`, be the punctured spectrum of `A`,
resp. of `A/fA`. Then `Pic(U) → Pic(U₀)` is injective. Finally, that last hypothesis is automatic
when `A` satisfies Serre's condition `(S₂)` and `dim(A) ≥ 4`. This is [Stacks, Tag 0F2B].

## The proof

The shape of the argument is that of [Stacks, Tag 0F2A], which is the same statement for torsion
classes only. Let `ℒ` be an invertible module on `U` whose restriction to `U₀` is trivial. The
trivialisation completes `ℒ` to an invertible coherent triple `(ℒ, 𝒪_{X₀}, λ)`
(`Stacks.Algebraization.coherentTripleOfTrivialRestriction`), and the `n`-th twist of the unit
triple by it has `ℒ^{⊗ n}` on the punctured spectrum, so by the vanishing criterion
[Stacks, Tag 0F28] its Euler characteristic `χ(n)` vanishes exactly when `n` times the class of
`ℒ` is zero. By [Stacks, Tag 0F27] those Euler characteristics are the values `P(n)` of a
rational polynomial.

Where Tag 0F2A uses torsion to produce infinitely many roots of `P`, Kollár's argument pins `P`
down by three inequalities instead:

* `P(0) = 0`, since `0 · [ℒ] = 0`;
* `P(n) ≥ 0` for every integer `n`, since an Euler characteristic of an invertible coherent
  triple is the length of a cokernel (`CoherentTriple.eulerCharacteristic_nonneg`);
* `P(-n) ≤ c · n` for every natural number `n`, which is the linear bound
  `Stacks.Algebraization.exists_linear_bound_eulerCharacteristic_twistZ_neg` proved by local
  duality against a normalized dualizing complex.

A rational polynomial satisfying those three conditions is zero
(`Stacks.Polynomial.eq_zero_of_nonneg_of_eval_zero_of_neg_linear_bound`), so `P(1) = 0`, that is
`[ℒ] = 0`. Injectivity follows by subtraction, since the map on Picard groups is a group
homomorphism.

## Main results

* `Stacks.Algebraization.eq_zero_of_schemePullbackClass_eq_zero`: a class on `U` restricting to
  zero on `U₀` is zero.
* `Stacks.Algebraization.picRestrictionInjective_kollar`: hence `Pic(U) → Pic(U₀)` is injective.
* `Stacks.Algebraization.kollar_picRestrictionInjective`: **[Stacks, Tag 0F2B]**, the
  proposition's own conclusion, under the source's four hypotheses. The source's closing
  sentence, that `(S₂)` and `dim(A) ≥ 4` give its hypothesis (4), is the other half of the tag
  and already carries the attribute for that assertion in
  `StacksFrontier/RingTheory/Serre/LocalizationDepthCodimension.lean`.
* `Stacks.Algebraization.isKollarPicardInjectivity`: the same statement in the packaged form
  `Stacks.Algebraization.IsKollarPicardInjectivity`, which the SGA2 route of [Stacks, Tag 0FIX]
  had to carry as a hypothesis and can now be given.

## Implementation notes

`U` is `Stacks.Divisors.puncturedSpectrum A` and `U₀` is
`Stacks.Algebraization.puncturedClosedFibre A f`, which for `f ∈ 𝔪` is the punctured spectrum of
`A/fA`; the map on Picard groups is `Stacks.Picard.schemePullbackClass` of the restriction
`U₀ ⟶ U`, the spelling [Stacks, Tag 0F2G], [Stacks, Tag 0F2A] and [Stacks, Tag 0FIX] are stated
at.

The source's hypothesis (3) is `depth(A/fA) ≥ 2`, and the Euler-characteristic machinery is
stated at `depth(A) ≥ 3`; the two are the same condition by [Stacks, Tag 090R], which is
`Stacks.Algebraization.le_depth_quotient_span_singleton_iff` at `n = 2`.

The source assumes only that `A` *has* a dualizing complex, while the linear bound is proved
against a *normalized* one. The translation is
`Dualizing.exists_isNormalizedDualizingComplex_shift`: exactly one shift of a dualizing complex
over a Noetherian local ring is normalized, so the shift may be taken without strengthening the
hypothesis.

The source's closing sentence, that `(S₂)` and `dim(A) ≥ 4` give its hypothesis (4), is not
restated here: it is already proved and registered as
`Stacks.Serre.LocalizationDepth.two_le_ringDepth_localization_of_isDualizingComplex`. The tag
therefore has two carriers whose attribute strings partition it — that one for the closing
sentence, `Stacks.Algebraization.kollar_picRestrictionInjective` below for the proposition — and
the hypothesis (4) that the proposition demands is phrased here with `Module.depth` of the
localization over itself, which is its `ringDepth` by `ringDepth_eq_depth_maximalIdeal`.

## References

* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Tag 0F2A](https://stacks.math.columbia.edu/tag/0F2A)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0FIX](https://stacks.math.columbia.edu/tag/0FIX)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

open Stacks.RingedSpace (structureIsSheaf)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### A class trivial on the punctured closed fibre is zero -/

/-- **A class on the punctured spectrum whose restriction to the punctured closed fibre is zero
is itself zero**, under the hypotheses of [Stacks, Tag 0F2B] with the dualizing complex taken
normalized. This is the content of that tag; the injectivity statement follows from it by
subtraction.

Let `ℒ` represent the class. Its restriction being zero makes `ℒ^{⊗ n}` the punctured-spectrum
member of the `n`-th twist of the unit coherent triple by the invertible coherent triple
`(ℒ, 𝒪_{X₀}, λ)` of `Stacks.Algebraization.coherentTripleOfTrivialRestriction`, so by
[Stacks, Tag 0F28] the Euler characteristic of that twist vanishes exactly when `n` times the
class does. Those Euler characteristics are the values of a rational polynomial `P` by
[Stacks, Tag 0F27]. Now `P(0) = 0`, `P` is nonnegative at every integer because an Euler
characteristic of an invertible triple is a length, and `P(-n) ≤ c · n` by
`Stacks.Algebraization.exists_linear_bound_eulerCharacteristic_twistZ_neg`; a rational polynomial
with those three properties is zero, so `P(1) = 0` and the class itself is zero. -/
public theorem eq_zero_of_schemePullbackClass_eq_zero (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hfm : f ∈ maximalIdeal A)
    (hreg : IsRegular f) (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (h4 : ∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
      2 ≤ Module.depth (Localization.AtPrime p)
        (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
    {x : Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum A).toScheme}
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
  have hF₀ : T.F₀ = Stacks.Ample.unitModule (closedFibre A f) := by rw [hTdef]; rfl
  -- the Euler characteristics of the twists of the unit triple
  obtain ⟨P, -, hP⟩ :=
    exists_polynomial_natDegree_le_dim_supp hfm hreg T hT (CoherentTriple.unit A f htf)
  have hinv := fun n : ℤ => isInvertibleTriple_twistZ (isInvertibleTriple_unit A f htf) hT n
  have h1 := fun n => (hinv n).invertible_F
  have h2 := fun n => (hinv n).invertible_F₀
  have hkey : ∀ n : ℕ,
      ((CoherentTriple.unit A f htf).twistZ T hT (n : ℤ)).eulerCharacteristic hfm hreg = 0 ↔
        (n : ℤ) • x = 0 := by
    intro n
    have hpow : Stacks.SheafOfModules.IsInvertible
        (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
        (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L (n : ℤ)) :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
        (isInvertibleModule_tensorPowScheme _ L (n : ℤ))
    have hiso := CoherentTriple.unit_twistZ_F_iso A f htf T hT (n : ℤ)
    rw [CoherentTriple.eulerCharacteristic_eq_zero_iff_isTrivial A f hfm hreg _ hdepth,
      ← hclass, ← Stacks.Picard.classOf_tensorPower
        (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
        (structureIsSheaf (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L n,
      Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit _ hpow]
    exact ⟨fun ⟨e₁⟩ => ⟨hiso.symm ≪≫ e₁⟩, fun ⟨e₁⟩ => ⟨hiso ≪≫ e₁⟩⟩
  -- `P` vanishes at `0`
  have hzero : P.eval 0 = 0 := by
    have hq := hP ((0 : ℕ) : ℤ)
    rw [(hkey 0).2 (by simp)] at hq
    simpa using hq.symm
  -- `P` is nonnegative at every integer
  have hnonneg : ∀ n : ℤ, 0 ≤ P.eval (n : ℚ) := by
    intro n
    rw [← hP n]
    exact_mod_cast CoherentTriple.eulerCharacteristic_nonneg A f hfm hreg
      ((CoherentTriple.unit A f htf).twistZ T hT n) hdepth
  -- `P` satisfies the linear bound on the negative axis
  obtain ⟨c, hc⟩ := exists_linear_bound_eulerCharacteristic_twistZ_neg A f hfm hreg hdepth ω hω
    h4 htf T hT hF₀
  have hbound : ∀ n : ℕ, P.eval (-(n : ℚ)) ≤ (c : ℚ) * n := by
    intro n
    have hq := hP (-(n : ℤ))
    have hcn : ((((CoherentTriple.unit A f htf).twistZ T hT (-(n : ℤ))).eulerCharacteristic
        hfm hreg : ℤ) : ℚ) ≤ ((c * n : ℤ) : ℚ) := by exact_mod_cast hc n
    rw [hq] at hcn
    push_cast at hcn
    exact hcn
  -- hence `P = 0`, and reading it off at `1` gives the claim
  have hP0 : P = 0 :=
    Stacks.Polynomial.eq_zero_of_nonneg_of_eval_zero_of_neg_linear_bound hnonneg hzero hbound
  have hone : ((1 : ℕ) : ℤ) • x = 0 := by
    refine (hkey 1).1 ?_
    have hq := hP ((1 : ℕ) : ℤ)
    rw [hP0, Polynomial.eval_zero] at hq
    exact_mod_cast hq
  simpa using hone

/-! ### The injectivity -/

/-- **`Pic(U) → Pic(U₀)` is injective** under the hypotheses of [Stacks, Tag 0F2B], with the
dualizing complex taken normalized. Two classes with the same restriction have a difference
restricting to zero, and such a difference is zero by
`Stacks.Algebraization.eq_zero_of_schemePullbackClass_eq_zero`. -/
public theorem picRestrictionInjective_kollar (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hfm : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (h4 : ∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
      2 ≤ Module.depth (Localization.AtPrime p)
        (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) :
    Function.Injective
      (Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f)) := by
  intro x y hxy
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
    show Stacks.Picard.pullbackClass
      (puncturedClosedFibreRestriction A f).toLRSHom.toShHom (x - y) = 0
    rw [h, hxy', sub_self]
  exact sub_eq_zero.1
    (eq_zero_of_schemePullbackClass_eq_zero A f hfm hreg hdepth ω hω h4 hsub)

/-! ### Tag 0F2B -/

/-- **Stacks Project, Tag 0F2B** (Kollár). Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`.
Assume

1. `A` has a dualizing complex,
2. `f` is a nonzerodivisor,
3. `depth(A/fA) ≥ 2`, and
4. every prime `𝔭 ∋ f` with `dim(A/𝔭) = 2` has `depth(A_𝔭) ≥ 2`.

Let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. Then `Pic(U) → Pic(U₀)`
is injective. Finally, if (1), (2), (3) hold, `A` satisfies Serre's condition `(S₂)` and
`dim(A) ≥ 4`, then (4) holds.

This is the proposition's own conclusion, under the source's four hypotheses and nothing else:
`Stacks.Algebraization.picRestrictionInjective_kollar`, after translating hypothesis (3) into
`depth(A) ≥ 3` by `Stacks.Algebraization.le_depth_quotient_span_singleton_iff` and replacing the
dualizing complex by the unique shift of it that is normalized
(`Dualizing.exists_isNormalizedDualizingComplex_shift`).

The source's closing sentence — that (1), (2), (3) together with `(S₂)` and `dim(A) ≥ 4` imply
(4) — is the other half of the tag, and is
`Stacks.Serre.LocalizationDepth.two_le_ringDepth_localization_of_isDualizingComplex`, which
carries the tag's attribute for that assertion. The two attribute strings partition the
proposition, so this one claims only the injectivity. -/
@[stacks 0F2B "the proposition: Pic(U) → Pic(U₀) is injective"]
public theorem kollar_picRestrictionInjective (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A) :
    ∀ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K →
      IsSMulRegular A f →
      2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f}) →
      (∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
        2 ≤ Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) →
      Function.Injective
        (Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f)) := by
  intro K hK hf h3 h4
  have hreg : IsRegular f := isLeftRegular_iff_isRegular.1 hf.isLeftRegular
  have hdepth : 3 ≤ Module.depth A (maximalIdeal A) A :=
    (le_depth_quotient_span_singleton_iff A f hfm hf 2).1 h3
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} K hK
  exact picRestrictionInjective_kollar A f hfm hreg hdepth (K⟦-m⟧) hm h4

/-! ### Discharging the hypothesis the SGA2 route carried -/

/-- **Kollár's proposition, in the form the SGA2 route assumes it.**
`Stacks.Algebraization.IsKollarPicardInjectivity` is the statement of [Stacks, Tag 0F2B] as
`StacksFrontier/AlgebraicGeometry/Algebraization/PuncturedSpectrumPicardInjectivitySGA2.lean` has to
assume it: that file deduces the SGA2 lemma [Stacks, Tag 0FIX] from Kollár's proposition exactly
as the remark there describes, but carries the proposition as a hypothesis
(`Stacks.Algebraization.picRestrictionInjective_of_regularQuotient`) because it cannot prove it.
It is proved here, so the hypothesis can now be supplied.

Two translations are needed. That statement bundles the dualizing complex existentially, while
`kollar_picRestrictionInjective` is quantified over the complexes, so the witness is extracted
first. And its hypothesis (4) is read at an arbitrary ring presenting `A_𝔭`
(`Stacks.Algebraization.TwoLeDepthLocalization`), while Kollár's proposition asks it of the model
`Localization.AtPrime 𝔭`, which is one instance of it. -/
public theorem isKollarPicardInjectivity : IsKollarPicardInjectivity.{u} := by
  intro A _ _ _ f hfm hK hf h2 h4
  obtain ⟨K, hK⟩ := hK
  exact kollar_picRestrictionInjective A f hfm K hK hf h2
    fun p hp hfp hdim => h4 p hp hfp hdim (Localization.AtPrime p)

end Stacks.Algebraization

end

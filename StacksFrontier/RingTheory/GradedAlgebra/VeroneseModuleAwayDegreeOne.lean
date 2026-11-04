module

public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseAwayDegreeOne

/-!
# A graded module localized at a homogeneous element of degree `d`, on its `d`-th Veronese part

Let `S = ⨁_{n ≥ 0} S_n` be a graded ring, `T = ⨁_{n ∈ ℤ} T_n` a graded `S`-module and `a ∈ S_d`.
In the `d`-th Veronese subring `S⁽ᵈ⁾` the element `a` is homogeneous of degree **one**
(`Stacks.Veronese.veroneseOfDegree`), and the Veronese part `T⁽ᵈ⁾ = ⨁_n T_{nd}`
(`Stacks.Veronese.veroneseSubmodule`) is a graded `S⁽ᵈ⁾`-module. This file proves that the
degree-zero localizations agree:

  `T₍a₎ ≃+ (T⁽ᵈ⁾)₍a₎`,

by the identity on fractions `x / aⁿ ↦ x / aⁿ`. Nothing has to move: a degree-zero element of
`T[1/a]` is a fraction `x / aⁿ` with `x` homogeneous of degree `n · d`, so the numerator already
lies in `T⁽ᵈ⁾`, where it is homogeneous of Veronese degree `n`. Only the degree in which the
numerator is counted changes.

This is the module half of `Stacks.Veronese.veroneseAwayDegreeOneEquiv`, and like it, it is what
lets a chart of `Proj` at an element of arbitrary degree `d` be computed by the degree-**one**
theory applied to the Veronese data.

Note the distinction from `Stacks.Veronese.veroneseModuleAwayEquiv` of
`StacksFrontier/RingTheory/GradedAlgebra/VeroneseGrading.lean`, which compares `(T⁽ᵈ⁾)₍f ᵈ₎` with
`T₍f₎` for `f` of *arbitrary* degree `e`: there the element passed to the Veronese side is `f ^ d`,
of Veronese degree `e`. Here the element passed to the Veronese side is `a` itself, of Veronese
degree one; the two statements have the same source `T₍a₎` but different targets, and neither
follows from the other by substitution.

## Main definitions

* `Stacks.Veronese.veroneseModuleProj` is the homogeneous projection of `T` onto its degree
  `n · d` piece, read as a map into `T⁽ᵈ⁾`.
* `Stacks.Veronese.veroneseModuleFraction` is the fraction `y / aⁿ` of the Veronese data, as an
  element of `(T⁽ᵈ⁾)₍a₎`.
* `Stacks.Veronese.veroneseModuleNumerator` is the family of additive maps that reads a numerator
  of degree `n · d` as such a fraction; it is the input to the lift of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DegreeZeroLocalizationArbitraryDegree.lean`.
* `Stacks.Veronese.veroneseModuleAwayDegreeOneHom` is the induced additive map, and
  `Stacks.Veronese.veroneseModuleAwayDegreeOneEquiv` the additive isomorphism.

## Main results

* `Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degree`: **a bijectivity
  criterion for the lift out of a degree-zero localization at an element of arbitrary degree.**
  `Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree` is the same criterion for
  an element of degree one only; the generalization is needed here, where the element whose
  localization is the *source* has degree `d`.
* `Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degreewise`:
  **bijectivity transports along a comparison of two graded modules that is bijective in each
  degree**, with no comparison of the two graded rings. Two gradings over two different graded
  rings, localized at homogeneous elements `f` and `f'` of degrees `d` and `d'`, with maps to a
  common target: if the numerators of degree `n · d` on one side correspond bijectively to those
  of degree `n · d'` on the other, compatibly with multiplication by `f` and `f'` and with the
  two maps, then one map is bijective as soon as the other is.
* `Stacks.Veronese.veroneseModuleAwayDegreeOneHom_mk`: **the comparison is the identity on
  fractions**, `x / aⁿ ↦ x / aⁿ`.
* `Stacks.Veronese.veroneseModuleAwayDegreeOneHom_bijective`: **the comparison is bijective.**

## Implementation notes

The fraction calculus of the target is proved through `Subtype.ext`: the degree-zero localization
is a submodule of `LocalizedModule.Away`, so each identity between fractions reduces to the
corresponding identity between `LocalizedModule.mk`s, and the homogeneity witnesses, being
proofs, never enter.

As on the ring side, the numerator family has to be additive on all of `T` and not only on a
homogeneous component, so it is defined through the homogeneous projection
`DirectSum.decompositionProj`; `Stacks.Veronese.veroneseModuleNumerator_apply_of_mem` then says
that on a numerator of the expected degree the projection does nothing, and every statement below
goes through that lemma rather than through the definition.

`0 < d` is never assumed; the gradings of the Veronese data enter only as the typeclass
hypotheses `[GradedRing (veroneseGrading 𝒜 d)]` and
`[DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)]`, following the convention of
`VeroneseGrading.lean`, and positivity of `d` is what makes those satisfiable.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open DirectSum

universe u v w t

/-! ### A bijectivity criterion at an element of arbitrary degree -/

namespace Stacks.SheafOfModules

/-- **A compatible family of numerator maps lifts to a bijection out of the degree-zero
localization** as soon as every element of the target is the value of some member on a numerator
of the matching degree, and every member kills a homogeneous numerator only if a power of the
element does.

`Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree` is this criterion for an
element of degree one; here the element has an arbitrary degree `d`, which is what a comparison
whose source is a chart at an element of degree `d` needs. -/
public theorem bijective_degreeZeroLocalizationLiftOfDegree_of_degree
    {R : Type u} {M : Type v} {σ : Type w} {τ : Type t}
    [CommRing R] [AddCommGroup M] [Module R M]
    [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
    [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [Decomposition B]
    [SetLike.GradedSMul A B] {f : R} {d : ℕ} (hf : f ∈ A d)
    {N : Type*} [AddCommGroup N] (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (hsurj : ∀ y : N, ∃ (n : ℕ) (x : M), ∃ _ : x ∈ B ((n * d : ℕ) : ℤ), e n x = y)
    (hinj : ∀ (n : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e n x = 0 → ∃ k : ℕ, f ^ k • x = 0) :
    Function.Bijective (degreeZeroLocalizationLiftOfDegree A B hf e he) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz0 => ?_, fun y => ?_⟩
  · obtain ⟨n, x, hx, hfrac⟩ := degreeZeroLocalization_exists_fraction_of_degree A B hf z
    rw [degreeZeroLocalizationLiftOfDegree_fraction A B hf e he z n x hx hfrac] at hz0
    rw [eq_zero_iff_exists_pow_smul_eq_zero A B z n x hfrac]
    exact hinj n x hx hz0
  · obtain ⟨n, x, hxmem, hxy⟩ := hsurj y
    refine ⟨⟨LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩,
      mk_mem_degreeZeroLocalization_of_degree A B hf n x hxmem⟩, ?_⟩
    rwa [degreeZeroLocalizationLiftOfDegree_fraction A B hf e he _ n x hxmem rfl]

/-- **A degreewise bijective comparison of graded modules transports bijectivity of the lift out
of the degree-zero localization**, whatever the comparison of the two graded rings is.

Two graded modules are compared: `M`, graded by `B` over the graded ring `A` and localized at
`f ∈ A d`, and `M'`, graded by `B'` over `A'` and localized at `f' ∈ A' d'`. Both carry a map to
the same target `N`: on the `M` side the lift of the family `e`, and on the `M'` side an
arbitrary additive map `g` whose value on a fraction `x' / f' ^ n` is `e' n x'`. The comparison is
a family `ψ` of additive maps `M →+ M'`, the `n`-th of which carries numerators of degree `n · d`
to numerators of degree `n · d'`, bijectively, intertwines multiplication by `f` with
multiplication by `f'`, and intertwines the two numerator families.

No comparison of the two graded *rings* is assumed and none is needed: in a fraction the
numerator and the denominator are compared separately, and that is all a fraction is.
Surjectivity transports because every element of `N` is already `e' n x'` for a numerator `x'` in
the image of `ψ`; injectivity transports because `e n x = 0` says `g` kills the fraction
`ψ x / f' ^ n`, so `f' ^ k • ψ x = ψ (f ^ k • x)` vanishes for some `k`, and then so does
`f ^ k • x`. -/
public theorem bijective_degreeZeroLocalizationLiftOfDegree_of_degreewise
    {R : Type*} {M : Type*} {σ : Type*} {τ : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
    [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [Decomposition B]
    [SetLike.GradedSMul A B] {f : R} {d : ℕ} (hf : f ∈ A d)
    {R' : Type*} {M' : Type*} {σ' : Type*} {τ' : Type*}
    [CommRing R'] [AddCommGroup M'] [Module R' M']
    [SetLike σ' R'] [AddSubgroupClass σ' R'] (A' : ℕ → σ') [GradedRing A']
    [SetLike τ' M'] [AddSubgroupClass τ' M'] (B' : ℤ → τ') [Decomposition B']
    [SetLike.GradedSMul A' B'] {f' : R'} {d' : ℕ} (hf' : f' ∈ A' d')
    {N : Type*} [AddCommGroup N]
    (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (e' : ℕ → M' →+ N) (g : GradedModuleDegreeZeroLocalization A' B' f' →+ N)
    (hg : ∀ (z' : GradedModuleDegreeZeroLocalization A' B' f') (n : ℕ) (x' : M'),
      x' ∈ B' ((n * d' : ℕ) : ℤ) →
      (z' : LocalizedModule.Away f' M') =
        LocalizedModule.mk (S := Submonoid.powers f') x' ⟨f' ^ n, by exact ⟨n, rfl⟩⟩ →
      g z' = e' n x')
    (hgbij : Function.Bijective g) (ψ : ℕ → M →+ M')
    (hψmem : ∀ (n : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → ψ n x ∈ B' ((n * d' : ℕ) : ℤ))
    (hψpow : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) →
      ψ (n + k) (f ^ k • x) = f' ^ k • ψ n x)
    (hψsurj : ∀ (n : ℕ) (x' : M'), x' ∈ B' ((n * d' : ℕ) : ℤ) →
      ∃ x : M, x ∈ B ((n * d : ℕ) : ℤ) ∧ ψ n x = x')
    (hψinj : ∀ (n : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → ψ n x = 0 → x = 0)
    (hcomm : ∀ (n : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) → e' n (ψ n x) = e n x) :
    Function.Bijective (degreeZeroLocalizationLiftOfDegree A B hf e he) := by
  have hsmul : ∀ (n k : ℕ) (x : M), x ∈ B ((n * d : ℕ) : ℤ) →
      f ^ k • x ∈ B (((n + k) * d : ℕ) : ℤ) := by
    intro n k x hx
    have hpow : f ^ k ∈ A (k * d) := by simpa [smul_eq_mul] using SetLike.pow_mem_graded k hf
    have h : f ^ k • x ∈ B ((k * d : ℕ) +ᵥ ((n * d : ℕ) : ℤ)) :=
      SetLike.GradedSMul.smul_mem hpow hx
    have hdeg : (((n + k) * d : ℕ) : ℤ) = ((k * d : ℕ) : ℤ) + ((n * d : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hdeg]
    simpa using h
  refine bijective_degreeZeroLocalizationLiftOfDegree_of_degree A B hf e he
    (fun y => ?_) (fun n x hx hzero => ?_)
  · obtain ⟨z', rfl⟩ := hgbij.2 y
    obtain ⟨n, x', hx', hz'⟩ := degreeZeroLocalization_exists_fraction_of_degree A' B' hf' z'
    obtain ⟨x, hx, rfl⟩ := hψsurj n x' hx'
    exact ⟨n, x, hx, ((hg z' n (ψ n x) hx' hz').trans (hcomm n x hx)).symm⟩
  · have hψx : ψ n x ∈ B' ((n * d' : ℕ) : ℤ) := hψmem n x hx
    have hgz : g ⟨LocalizedModule.mk (S := Submonoid.powers f') (ψ n x)
          ⟨f' ^ n, by exact ⟨n, rfl⟩⟩,
        mk_mem_degreeZeroLocalization_of_degree A' B' hf' n (ψ n x) hψx⟩ = 0 :=
      (hg _ n (ψ n x) hψx rfl).trans ((hcomm n x hx).trans hzero)
    obtain ⟨k, hk⟩ := (eq_zero_iff_exists_pow_smul_eq_zero A' B' _ n (ψ n x) rfl).mp
      (hgbij.1 (hgz.trans (map_zero g).symm))
    exact ⟨k, hψinj (n + k) (f ^ k • x) (hsmul n k x hx) ((hψpow n k x hx).trans hk)⟩

end Stacks.SheafOfModules

/-! ### The module comparison in Veronese degree one -/

namespace Stacks.Veronese

section ModuleDegreeOne

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) [GradedRing (veroneseGrading 𝒜 d)]
  {M : Type w} [AddCommGroup M] [Module A M] (ℳ : ℤ → AddSubgroup M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] {a : A}

/-! #### The Veronese part and its homogeneous projection -/

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)]
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- A homogeneous element of degree divisible by `d` lies in the Veronese part. -/
public theorem mem_veroneseSubmodule_of_mem {n : ℤ} {x : M} (hx : x ∈ ℳ (n * (d : ℤ))) :
    x ∈ veroneseSubmodule 𝒜 ℳ d :=
  Submodule.subset_span ((mem_veroneseModuleSet_iff ℳ).mpr ⟨n, hx⟩)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)]
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- A numerator homogeneous of degree `n * d` lies in the Veronese part. -/
public theorem mem_veroneseSubmodule_of_mem_mul {n : ℕ} {x : M}
    (hx : x ∈ ℳ ((n * d : ℕ) : ℤ)) : x ∈ veroneseSubmodule 𝒜 ℳ d :=
  mem_veroneseSubmodule_of_mem 𝒜 d ℳ (n := (n : ℤ))
    (by rwa [show (n : ℤ) * (d : ℤ) = ((n * d : ℕ) : ℤ) by push_cast; ring])

omit [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- **The homogeneous projection onto degree `n · d`, as a map into the Veronese part.** -/
public def veroneseModuleProj (n : ℕ) : M →+ veroneseSubmodule 𝒜 ℳ d where
  toFun x := ⟨decompositionProj ℳ ((n : ℤ) * (d : ℤ)) x,
    mem_veroneseSubmodule_of_mem 𝒜 d ℳ (n := (n : ℤ))
      (by rw [decompositionProj_apply]; exact SetLike.coe_mem _)⟩
  map_zero' := Subtype.ext (map_zero (decompositionProj ℳ ((n : ℤ) * (d : ℤ))))
  map_add' x y := Subtype.ext (map_add (decompositionProj ℳ ((n : ℤ) * (d : ℤ))) x y)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)]
  [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- The underlying element of `veroneseModuleProj n x` is the homogeneous component of `x` of
degree `n · d`. -/
public theorem coe_veroneseModuleProj (n : ℕ) (x : M) :
    ((veroneseModuleProj 𝒜 d ℳ n x : veroneseSubmodule 𝒜 ℳ d) : M) =
      decompositionProj ℳ ((n : ℤ) * (d : ℤ)) x :=
  rfl

/-! #### Degrees on the two sides -/

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)]
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- Membership in the Veronese module grading at the degree `n * 1` in which the fraction
calculus of the degree-zero localization states it. -/
public theorem mem_veroneseModuleGrading_mul_one {n : ℕ} {y : veroneseSubmodule 𝒜 ℳ d}
    (hy : (y : M) ∈ ℳ ((n * d : ℕ) : ℤ)) :
    y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ) := by
  rwa [mem_veroneseModuleGrading,
    show (((n * 1 : ℕ) : ℤ)) * (d : ℤ) = ((n * d : ℕ) : ℤ) by push_cast; ring]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)]
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- The underlying element of a numerator of Veronese degree `n * 1` is homogeneous of degree
`n * d`. -/
public theorem coe_mem_of_mem_veroneseModuleGrading_mul_one {n : ℕ}
    {y : veroneseSubmodule 𝒜 ℳ d} (hy : y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ)) :
    (y : M) ∈ ℳ ((n * d : ℕ) : ℤ) := by
  rwa [mem_veroneseModuleGrading,
    show (((n * 1 : ℕ) : ℤ)) * (d : ℤ) = ((n * d : ℕ) : ℤ) by push_cast; ring] at hy

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)]
  [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- The projection onto degree `n · d` is homogeneous of Veronese degree `n`. -/
public theorem veroneseModuleProj_mem (n : ℕ) (x : M) :
    veroneseModuleProj 𝒜 d ℳ n x ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ) := by
  refine mem_veroneseModuleGrading_mul_one 𝒜 d ℳ ?_
  rw [coe_veroneseModuleProj,
    show ((n * d : ℕ) : ℤ) = (n : ℤ) * (d : ℤ) by push_cast; ring, decompositionProj_apply]
  exact SetLike.coe_mem _

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)]
  [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition (veroneseModuleGrading 𝒜 ℳ d)] in
/-- On a numerator of the expected degree the projection does nothing. -/
public theorem veroneseModuleProj_of_mem {n : ℕ} {x : M} (hx : x ∈ ℳ ((n * d : ℕ) : ℤ)) :
    veroneseModuleProj 𝒜 d ℳ n x =
      ⟨x, mem_veroneseSubmodule_of_mem_mul 𝒜 d ℳ hx⟩ := by
  refine Subtype.ext ?_
  rw [coe_veroneseModuleProj]
  refine decompositionProj_of_mem_same ℳ ?_
  rwa [show (n : ℤ) * (d : ℤ) = ((n * d : ℕ) : ℤ) by push_cast; ring]

/-! #### The fraction calculus of the target -/

/-- **The fraction `y / aⁿ` of the Veronese data**, as an element of `(T⁽ᵈ⁾)₍a₎`. -/
public def veroneseModuleFraction (ha : a ∈ 𝒜 d) (n : ℕ) (y : veroneseSubmodule 𝒜 ℳ d)
    (hy : y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ)) :
    GradedModuleDegreeZeroLocalization (veroneseGrading 𝒜 d) (veroneseModuleGrading 𝒜 ℳ d)
      (veroneseOfDegree 𝒜 d ha) :=
  ⟨LocalizedModule.mk (S := Submonoid.powers (veroneseOfDegree 𝒜 d ha)) y
      ⟨veroneseOfDegree 𝒜 d ha ^ n, by exact ⟨n, rfl⟩⟩,
    Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (veroneseGrading 𝒜 d)
      (veroneseModuleGrading 𝒜 ℳ d) (veroneseOfDegree_mem 𝒜 d ha) n y hy⟩

omit [GradedRing 𝒜] [DirectSum.Decomposition ℳ] in
/-- The underlying element of `veroneseModuleFraction ha n y hy` in the localization of the
Veronese part is the fraction `y / aⁿ`. -/
public theorem coe_veroneseModuleFraction (ha : a ∈ 𝒜 d) (n : ℕ)
    (y : veroneseSubmodule 𝒜 ℳ d)
    (hy : y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ)) :
    (veroneseModuleFraction 𝒜 d ℳ ha n y hy :
        LocalizedModule.Away (R := veroneseSubring 𝒜 d) (veroneseOfDegree 𝒜 d ha)
          (veroneseSubmodule 𝒜 ℳ d)) =
      LocalizedModule.mk y ⟨veroneseOfDegree 𝒜 d ha ^ n, by exact ⟨n, rfl⟩⟩ :=
  rfl

omit [GradedRing 𝒜] [DirectSum.Decomposition ℳ] in
/-- Two fractions with the same numerator and the same denominator are equal: the homogeneity
witnesses are proofs, so they do not enter. -/
public theorem veroneseModuleFraction_congr (ha : a ∈ 𝒜 d) (n : ℕ)
    {y z : veroneseSubmodule 𝒜 ℳ d}
    (hy : y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ))
    (hz : z ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ)) (h : y = z) :
    veroneseModuleFraction 𝒜 d ℳ ha n y hy = veroneseModuleFraction 𝒜 d ℳ ha n z hz := by
  subst h
  rfl

omit [GradedRing 𝒜] [DirectSum.Decomposition ℳ] in
/-- A fraction with numerator `0` vanishes. -/
public theorem veroneseModuleFraction_zero (ha : a ∈ 𝒜 d) (n : ℕ)
    (hy : (0 : veroneseSubmodule 𝒜 ℳ d) ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ)) :
    veroneseModuleFraction 𝒜 d ℳ ha n 0 hy = 0 :=
  Subtype.ext (LocalizedModule.zero_mk _)

omit [GradedRing 𝒜] [DirectSum.Decomposition ℳ] in
/-- Fractions with a common denominator add by adding numerators. -/
public theorem veroneseModuleFraction_add (ha : a ∈ 𝒜 d) (n : ℕ)
    {y z : veroneseSubmodule 𝒜 ℳ d}
    (hy : y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ))
    (hz : z ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ))
    (hyz : y + z ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ)) :
    veroneseModuleFraction 𝒜 d ℳ ha n y hy + veroneseModuleFraction 𝒜 d ℳ ha n z hz =
      veroneseModuleFraction 𝒜 d ℳ ha n (y + z) hyz := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, coe_veroneseModuleFraction, coe_veroneseModuleFraction,
    coe_veroneseModuleFraction, LocalizedModule.mk_add_mk, ← smul_add,
    LocalizedModule.mk_cancel_common_left]

omit [GradedRing 𝒜] [DirectSum.Decomposition ℳ] in
/-- Multiplying numerator and denominator by `aᵏ` leaves a fraction unchanged. -/
public theorem veroneseModuleFraction_pow_smul (ha : a ∈ 𝒜 d) (n k : ℕ)
    {y : veroneseSubmodule 𝒜 ℳ d}
    (hy : y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ))
    (hky : veroneseOfDegree 𝒜 d ha ^ k • y ∈
      veroneseModuleGrading 𝒜 ℳ d (((n + k) * 1 : ℕ) : ℤ)) :
    veroneseModuleFraction 𝒜 d ℳ ha (n + k) (veroneseOfDegree 𝒜 d ha ^ k • y) hky =
      veroneseModuleFraction 𝒜 d ℳ ha n y hy := by
  refine Subtype.ext ?_
  rw [coe_veroneseModuleFraction, coe_veroneseModuleFraction, LocalizedModule.mk_eq]
  exact ⟨1, by
    simp only [one_smul, Submonoid.smul_def, ← mul_smul, ← pow_add,
      Nat.add_comm n k]⟩

omit [GradedRing 𝒜] [DirectSum.Decomposition ℳ] in
/-- **A fraction vanishes exactly when a power of the denominator kills its numerator.** -/
public theorem veroneseModuleFraction_eq_zero_iff (ha : a ∈ 𝒜 d) (n : ℕ)
    {y : veroneseSubmodule 𝒜 ℳ d}
    (hy : y ∈ veroneseModuleGrading 𝒜 ℳ d ((n * 1 : ℕ) : ℤ)) :
    veroneseModuleFraction 𝒜 d ℳ ha n y hy = 0 ↔
      ∃ k : ℕ, veroneseOfDegree 𝒜 d ha ^ k • y = 0 :=
  Stacks.SheafOfModules.eq_zero_iff_exists_pow_smul_eq_zero (veroneseGrading 𝒜 d)
    (veroneseModuleGrading 𝒜 ℳ d) (veroneseModuleFraction 𝒜 d ℳ ha n y hy) n y rfl

/-! #### The numerator family and the comparison -/

/-- **The numerator family**: a numerator of degree `n · d` is read as the fraction over `aⁿ` on
the Veronese side, where it is homogeneous of Veronese degree `n`. It is defined on all of `T`
through the homogeneous projection, so that it is additive. -/
public def veroneseModuleNumerator (ha : a ∈ 𝒜 d) (n : ℕ) :
    M →+ GradedModuleDegreeZeroLocalization (veroneseGrading 𝒜 d)
      (veroneseModuleGrading 𝒜 ℳ d) (veroneseOfDegree 𝒜 d ha) where
  toFun x := veroneseModuleFraction 𝒜 d ℳ ha n (veroneseModuleProj 𝒜 d ℳ n x)
    (veroneseModuleProj_mem 𝒜 d ℳ n x)
  map_zero' :=
    (veroneseModuleFraction_congr 𝒜 d ℳ ha n _ (zero_mem _)
      (map_zero (veroneseModuleProj 𝒜 d ℳ n))).trans
      (veroneseModuleFraction_zero 𝒜 d ℳ ha n (zero_mem _))
  map_add' x y :=
    (veroneseModuleFraction_congr 𝒜 d ℳ ha n _
      (add_mem (veroneseModuleProj_mem 𝒜 d ℳ n x) (veroneseModuleProj_mem 𝒜 d ℳ n y))
      (map_add (veroneseModuleProj 𝒜 d ℳ n) x y)).trans
      (veroneseModuleFraction_add 𝒜 d ℳ ha n _ _ _).symm

omit [GradedRing 𝒜] in
/-- On a numerator of the expected degree the projection does nothing: the numerator family is the
fraction `x / aⁿ`. Every statement below is proved through this lemma rather than through the
definition. -/
public theorem veroneseModuleNumerator_apply_of_mem (ha : a ∈ 𝒜 d) (n : ℕ) {x : M}
    (hx : x ∈ ℳ ((n * d : ℕ) : ℤ)) :
    veroneseModuleNumerator 𝒜 d ℳ ha n x =
      veroneseModuleFraction 𝒜 d ℳ ha n ⟨x, mem_veroneseSubmodule_of_mem_mul 𝒜 d ℳ hx⟩
        (mem_veroneseModuleGrading_mul_one 𝒜 d ℳ hx) :=
  veroneseModuleFraction_congr 𝒜 d ℳ ha n (veroneseModuleProj_mem 𝒜 d ℳ n x) _
    (veroneseModuleProj_of_mem 𝒜 d ℳ hx)

/-- The numerator family is compatible with multiplying numerator and denominator by `a`. -/
public theorem veroneseModuleNumerator_pow_smul (ha : a ∈ 𝒜 d) (n k : ℕ) (x : M)
    (hx : x ∈ ℳ ((n * d : ℕ) : ℤ)) :
    veroneseModuleNumerator 𝒜 d ℳ ha (n + k) (a ^ k • x) =
      veroneseModuleNumerator 𝒜 d ℳ ha n x := by
  have hpow : a ^ k ∈ 𝒜 (k * d) := by
    simpa [smul_eq_mul] using SetLike.pow_mem_graded k ha
  have hax : a ^ k • x ∈ ℳ (((n + k) * d : ℕ) : ℤ) := by
    have key := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) hpow hx
    rwa [natVAddInt_def, show ((k * d : ℕ) : ℤ) + ((n * d : ℕ) : ℤ) =
      (((n + k) * d : ℕ) : ℤ) by push_cast; ring] at key
  have hsmul : (⟨a ^ k • x, mem_veroneseSubmodule_of_mem_mul 𝒜 d ℳ hax⟩ :
      veroneseSubmodule 𝒜 ℳ d) =
      veroneseOfDegree 𝒜 d ha ^ k • ⟨x, mem_veroneseSubmodule_of_mem_mul 𝒜 d ℳ hx⟩ :=
    Subtype.ext rfl
  rw [veroneseModuleNumerator_apply_of_mem 𝒜 d ℳ ha (n + k) hax,
    veroneseModuleNumerator_apply_of_mem 𝒜 d ℳ ha n hx]
  exact (veroneseModuleFraction_congr 𝒜 d ℳ ha (n + k) _
    (hsmul ▸ mem_veroneseModuleGrading_mul_one 𝒜 d ℳ hax) hsmul).trans
    (veroneseModuleFraction_pow_smul 𝒜 d ℳ ha n k (mem_veroneseModuleGrading_mul_one 𝒜 d ℳ hx) _)

/-- **The comparison** `T₍a₎ →+ (T⁽ᵈ⁾)₍a₎`, for `a` homogeneous of degree `d` in `S` and hence of
degree one in `S⁽ᵈ⁾`. -/
public def veroneseModuleAwayDegreeOneHom (ha : a ∈ 𝒜 d) :
    GradedModuleDegreeZeroLocalization 𝒜 ℳ a →+
      GradedModuleDegreeZeroLocalization (veroneseGrading 𝒜 d) (veroneseModuleGrading 𝒜 ℳ d)
        (veroneseOfDegree 𝒜 d ha) :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree 𝒜 ℳ ha
    (veroneseModuleNumerator 𝒜 d ℳ ha)
    (fun n k x hx => veroneseModuleNumerator_pow_smul 𝒜 d ℳ ha n k x hx)

/-- **The comparison is the identity on fractions**: `x / aⁿ ↦ x / aⁿ`. -/
public theorem veroneseModuleAwayDegreeOneHom_mk (ha : a ∈ 𝒜 d) (n : ℕ) (x : M)
    (hx : x ∈ ℳ ((n * d : ℕ) : ℤ))
    (z : GradedModuleDegreeZeroLocalization 𝒜 ℳ a)
    (hz : (z : LocalizedModule.Away (R := A) a M) =
      LocalizedModule.mk (S := Submonoid.powers a) x ⟨a ^ n, by exact ⟨n, rfl⟩⟩) :
    veroneseModuleAwayDegreeOneHom 𝒜 d ℳ ha z =
      veroneseModuleFraction 𝒜 d ℳ ha n ⟨x, mem_veroneseSubmodule_of_mem_mul 𝒜 d ℳ hx⟩
        (mem_veroneseModuleGrading_mul_one 𝒜 d ℳ hx) :=
  (Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction 𝒜 ℳ ha
    (veroneseModuleNumerator 𝒜 d ℳ ha) _ z n x hx hz).trans
    (veroneseModuleNumerator_apply_of_mem 𝒜 d ℳ ha n hx)

/-- **The comparison is bijective.** Both sides are the fractions `x / aⁿ` with numerator
homogeneous of degree `n · d`, written with the same symbols. -/
public theorem veroneseModuleAwayDegreeOneHom_bijective (ha : a ∈ 𝒜 d) :
    Function.Bijective (veroneseModuleAwayDegreeOneHom 𝒜 d ℳ ha) := by
  refine Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degree 𝒜 ℳ ha
    (veroneseModuleNumerator 𝒜 d ℳ ha) _ (fun y => ?_) (fun n x hx hzero => ?_)
  · obtain ⟨n, c, hc, hfrac⟩ :=
      Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree
        (veroneseGrading 𝒜 d) (veroneseModuleGrading 𝒜 ℳ d) (veroneseOfDegree_mem 𝒜 d ha) y
    refine ⟨n, (c : M), coe_mem_of_mem_veroneseModuleGrading_mul_one 𝒜 d ℳ hc, ?_⟩
    rw [veroneseModuleNumerator_apply_of_mem 𝒜 d ℳ ha n
      (coe_mem_of_mem_veroneseModuleGrading_mul_one 𝒜 d ℳ hc)]
    exact Subtype.ext (by rw [coe_veroneseModuleFraction, hfrac])
  · rw [veroneseModuleNumerator_apply_of_mem 𝒜 d ℳ ha n hx] at hzero
    obtain ⟨k, hk⟩ := (veroneseModuleFraction_eq_zero_iff 𝒜 d ℳ ha n
      (mem_veroneseModuleGrading_mul_one 𝒜 d ℳ hx)).mp hzero
    exact ⟨k, by simpa using congrArg (fun w : veroneseSubmodule 𝒜 ℳ d => (w : M)) hk⟩

/-- **Localizing a graded module at a homogeneous element of degree `d` is the same as localizing
its `d`-th Veronese part, where that element has degree one**, as an additive isomorphism. -/
public def veroneseModuleAwayDegreeOneEquiv (ha : a ∈ 𝒜 d) :
    GradedModuleDegreeZeroLocalization 𝒜 ℳ a ≃+
      GradedModuleDegreeZeroLocalization (veroneseGrading 𝒜 d) (veroneseModuleGrading 𝒜 ℳ d)
        (veroneseOfDegree 𝒜 d ha) :=
  AddEquiv.ofBijective (veroneseModuleAwayDegreeOneHom 𝒜 d ℳ ha)
    (veroneseModuleAwayDegreeOneHom_bijective 𝒜 d ℳ ha)

/-- The additive isomorphism `veroneseModuleAwayDegreeOneEquiv` acts as the comparison map
`veroneseModuleAwayDegreeOneHom`. -/
@[simp]
public theorem veroneseModuleAwayDegreeOneEquiv_apply (ha : a ∈ 𝒜 d)
    (z : GradedModuleDegreeZeroLocalization 𝒜 ℳ a) :
    veroneseModuleAwayDegreeOneEquiv 𝒜 d ℳ ha z = veroneseModuleAwayDegreeOneHom 𝒜 d ℳ ha z :=
  rfl

end ModuleDegreeOne

end Stacks.Veronese

end

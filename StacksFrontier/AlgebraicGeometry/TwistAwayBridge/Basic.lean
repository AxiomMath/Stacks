module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.StandardOpenBaseChange
public import Mathlib.RingTheory.Localization.Module

/-!
# The two models of the degree-zero localization of a twist, identified

For a nonnegatively graded ring `A = ⨁_{i ≥ 0} 𝒜 i` and a homogeneous `f` of degree `d`, the
module `Γ(D₊(f), 𝒪(t))` of sections of the `t`-th twisting sheaf over the standard open `D₊(f)`
is spanned by the fractions `x / f ^ k` with `x` homogeneous of degree `k * d + t`. This library
carries **two unrelated spellings** of that module, and this file proves they agree.

* `GradedModuleDegreeZeroLocalization 𝒜 (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
  𝒜 t) f` is a submodule of the localized *module* `LocalizedModule.Away f A`, with the twist
  carried by the graded module `A(t)`. This is the spelling the sheaf side uses: it is what
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv` identifies
  the sections over `D₊(f)` with.
* `Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t` is a submodule of the localized *ring*
  `Localization (Submonoid.powers f)`, with the twist carried by an explicit degree condition on
  numerators. This is the spelling the base-change side uses: it is what
  `Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange` produces canonical base-change
  isomorphisms between.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistAwayBridge.localizedAwayEquiv`: the ambient comparison
  `LocalizedModule.Away f A ≃ₗ[Localization.Away f] Localization.Away f`, the localization of the
  regular module read as the localized ring.

## Main results

* `Stacks.AlgebraicGeometry.TwistAwayBridge.localizedAwayEquiv_mk`: the ambient comparison sends
  the fraction `x / f ^ k` to the fraction `x / f ^ k`. Everything below is this plus bookkeeping
  on degrees.
* `Stacks.AlgebraicGeometry.TwistAwayBridge.mem_twistAway_iff`: **the bridge.** For `f` of degree
  `d`, an element of `LocalizedModule.Away f A` lies in the first model of `Γ(D₊(f), 𝒪(t))` if
  and only if its image under the ambient comparison lies in the second.
* `Stacks.AlgebraicGeometry.TwistAwayBridge.twistAwayEquiv`: the two models are isomorphic as
  modules over the degree-zero localization `A₍f₎`, with the comparison acting as the identity on
  fractions.

## Implementation notes

The degree bookkeeping is where the two spellings genuinely differ, in three ways, and each
needs a step.

* The first model writes its degree condition in the extended-by-zero grading
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading`, so a numerator in a *negative*
  degree is permitted and is then forced to be zero; the second quantifies over a natural-number
  degree `e` with `(e : ℤ) = k * d + t` and so simply has no generator in that case. The two
  spanning sets therefore do not match element by element: the first has extra generators, all
  of them zero. `mk_mem_twistAway` is the resulting case split.
* The first model quantifies the degree of `f` **inside its spanning set**
  (`∃ (d n : ℕ) (hf : f ∈ 𝒜 d), …`) while the second takes it as an argument. For a graded ring
  two degrees of one element disagree only when the element is zero
  (`DirectSum.degree_eq_of_mem_mem`), and when `f = 0` every fraction with a positive power of
  `f` in the denominator vanishes, so the extra generators are again all zero. This is why the
  bridge needs no hypothesis `f ≠ 0`, and no positivity of `d`.
* The scalar ring is `HomogeneousLocalization.Away 𝒜 f` on both sides, but the first model's
  action on the ambient module is a `Module.compHom` written into the *type* of
  `GradedModuleDegreeZeroLocalization` under a `letI`. So no statement here mentions that action:
  the two directions of the bridge are stated as membership assertions, which need only the
  submodule terms, and the `letI` is reintroduced inside each proof and discharged by `change`.

`Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange` is `noncomputable opaque`, so nothing
below unfolds it or can; only `twistAway`, which is an ordinary exposed `def`, is used.

## What this does not prove

No assertion of any tag is proved here and **no project tag attribute is attached.** In
particular Tag 01N2's twist assertion — that the comparison maps `θ : r_ψ^* 𝒪_X(n) → 𝒪_Y(n)` are
isomorphisms for a base change `B = R' ⊗_R A` — does not follow: this file is a change of
spelling for one module, with no sheaf and no morphism in it. What it supplies is the second of
the two inputs recorded as missing in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/Basic.lean`, namely a bridge between the
chart-sections model and the base-change model of the same module.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
-/

@[expose] public noncomputable section

open HomogeneousLocalization AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace Stacks.AlgebraicGeometry.TwistAwayBridge

variable {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]

/-! ### The ambient comparison -/

/-- **The localization of the regular module is the localized ring.** The canonical comparison
`A[1/f]`-as-a-module with `A[1/f]`-as-a-ring, linear over the localized ring itself. -/
public def localizedAwayEquiv (f : A) :
    LocalizedModule.Away (R := A) f A ≃ₗ[Localization.Away f] Localization.Away f :=
  LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
    (IsLocalizedModule.iso (Submonoid.powers f) (Algebra.linearMap A (Localization.Away f)))

/-- The ambient comparison is the identity on fractions. -/
public theorem localizedAwayEquiv_mk (f x : A) (s : Submonoid.powers f) :
    localizedAwayEquiv f (LocalizedModule.mk x s) = Localization.mk x s := by
  have h : (IsLocalizedModule.iso (Submonoid.powers f)
      (Algebra.linearMap A (Localization.Away f))).symm (Localization.mk x s) =
      LocalizedModule.mk x s := by
    refine IsLocalizedModule.iso_symm_apply' _ _ _ x s ?_
    rw [Submonoid.smul_def, Localization.smul_mk]
    simp only [Algebra.linearMap_apply, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp⟩
  change (IsLocalizedModule.iso (Submonoid.powers f)
    (Algebra.linearMap A (Localization.Away f))) (LocalizedModule.mk x s) = _
  rw [← h, LinearEquiv.apply_symm_apply]

/-! ### Generators -/

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- A fraction with a positive power of `0` in its denominator is zero: the denominator is then
itself `0`, which lies in the monoid being inverted. -/
public theorem mk_eq_zero_of_den_eq_zero {f : A} (hf : f = 0) {n : ℕ} (hn : 0 < n) (x : A) :
    Localization.mk x (⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩ :
      Submonoid.powers f) = 0 := by
  have hfn : f ^ n = 0 := by rw [hf]; exact zero_pow hn.ne'
  rw [← Localization.mk_zero (1 : Submonoid.powers f), Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩, by simp [hfn]⟩

/-- **The generators of the first model land in the second**, in the shape in which the degree of
`f` is the one `twistAway` is formed with. A numerator in a negative degree is zero, and
contributes the zero element rather than a generator. -/
public theorem mk_mem_twistAway (f : A) (d : ℕ) (t : ℤ) (n : ℕ) (x : A)
    (hx : x ∈ integerGrading (S := A) 𝒜 (((n * d : ℕ) : ℤ) + t)) :
    Localization.mk x (⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩ :
      Submonoid.powers f) ∈ Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t := by
  by_cases h : 0 ≤ ((n * d : ℕ) : ℤ) + t
  · have heq : integerGrading (S := A) 𝒜 (((n * d : ℕ) : ℤ) + t) =
        homogeneousSubmodule (S := A) 𝒜 ((((n * d : ℕ) : ℤ) + t).toNat) := by
      rw [← integerGrading_natCast, Int.toNat_of_nonneg h]
    rw [heq, mem_homogeneousSubmodule] at hx
    exact Submodule.subset_span ⟨n, (((n * d : ℕ) : ℤ) + t).toNat, x,
      (Int.toNat_of_nonneg h), hx, rfl⟩
  · rw [integerGrading_neg (S := A) 𝒜 _ (not_le.mp h)] at hx
    have hx0 : x = 0 := Submodule.mem_bot ℤ |>.mp hx
    subst hx0
    rw [Localization.mk_zero]
    exact Submodule.zero_mem _

/-! ### The bridge -/

/-- The spanning set of the first model, as a set of fractions in `LocalizedModule.Away f A`. -/
private abbrev twistGenerators (f : A) (t : ℤ) : Set (LocalizedModule.Away (R := A) f A) :=
  {z | ∃ (e n : ℕ) (_ : f ∈ 𝒜 e) (x : A), x ∈ twistGrading (S := A) 𝒜 t (n • (e : ℤ)) ∧
    z = LocalizedModule.mk x ⟨f ^ n, by exact ⟨n, rfl⟩⟩}

/-- The first model's spanning set carries into the second. -/
public theorem localizedAwayEquiv_mem_twistAway {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (t : ℤ)
    {z : LocalizedModule.Away (R := A) f A}
    (hz : z ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f) :
    localizedAwayEquiv f z ∈ Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t := by
  let inst := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := A) f A)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  have hle : @Submodule.span (HomogeneousLocalization.Away 𝒜 f) _ _ _ inst
      (twistGenerators 𝒜 f t) ≤
      Submodule.comap ((localizedAwayEquiv f).restrictScalars
          (HomogeneousLocalization.Away 𝒜 f)).toLinearMap
        (Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t) := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨e, n, hfe, x, hx, rfl⟩
    have hxi : x ∈ integerGrading (S := A) 𝒜 ((n : ℤ) * (e : ℤ) + t) := by
      simpa [twistGrading, nsmul_eq_mul] using hx
    have hmem : localizedAwayEquiv f (LocalizedModule.mk x
        (⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩ : Submonoid.powers f)) ∈
        Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t := by
      rw [localizedAwayEquiv_mk]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · refine mk_mem_twistAway 𝒜 f d t 0 x ?_
        simpa using hxi
      · rcases eq_or_ne d e with rfl | hne
        · refine mk_mem_twistAway 𝒜 f d t n x ?_
          push_cast
          exact hxi
        · have hf0 : f = 0 := by
            by_contra hne0
            exact hne (DirectSum.degree_eq_of_mem_mem 𝒜 hfe hf hne0).symm
          rw [mk_eq_zero_of_den_eq_zero hf0 hn]
          exact Submodule.zero_mem _
    exact hmem
  exact hle hz

/-- The second model's spanning set is hit from the first. -/
public theorem exists_mem_of_mem_twistAway {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (t : ℤ)
    {y : Localization (Submonoid.powers f)}
    (hy : y ∈ Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t) :
    ∃ z : LocalizedModule.Away (R := A) f A,
      z ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f ∧
        localizedAwayEquiv f z = y := by
  let inst := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := A) f A)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  have hle : Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t ≤
      Submodule.map ((localizedAwayEquiv f).restrictScalars
          (HomogeneousLocalization.Away 𝒜 f)).toLinearMap
        (@Submodule.span (HomogeneousLocalization.Away 𝒜 f) _ _ _ inst
          (twistGenerators 𝒜 f t)) := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨k, e, x, he, hx, rfl⟩
    refine ⟨LocalizedModule.mk x ⟨f ^ k, ⟨k, rfl⟩⟩,
      Submodule.subset_span ⟨d, k, hf, x, ?_, rfl⟩, ?_⟩
    · have hdeg : (k : ℤ) * (d : ℤ) + t = (e : ℤ) := by rw [he]; push_cast; ring
      have : x ∈ integerGrading (S := A) 𝒜 ((e : ℤ)) := by simpa using hx
      simpa [twistGrading, nsmul_eq_mul, hdeg] using this
    · exact localizedAwayEquiv_mk f x _
  obtain ⟨z, hz, hzy⟩ := hle hy
  exact ⟨z, hz, hzy⟩

/-- **The bridge between the two models.** An element of `A[1/f]`, read as a localized module,
lies in the chart-sections model of `Γ(D₊(f), 𝒪(t))` exactly when its image in the localized ring
lies in the base-change model. No hypothesis on `f` beyond homogeneity of some degree `d`, and no
positivity of `d`. -/
public theorem mem_twistAway_iff {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (t : ℤ)
    (z : LocalizedModule.Away (R := A) f A) :
    localizedAwayEquiv f z ∈ Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t ↔
      z ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f := by
  refine ⟨fun h => ?_, localizedAwayEquiv_mem_twistAway 𝒜 hf t⟩
  obtain ⟨w, hw, hwz⟩ := exists_mem_of_mem_twistAway 𝒜 hf t h
  rwa [(localizedAwayEquiv f).injective hwz] at hw

/-- **The two models are isomorphic over the degree-zero localization `A₍f₎`**, by an isomorphism
that is the identity on fractions. -/
public def twistAwayEquiv {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (t : ℤ) :
    GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f ≃ₗ[Away 𝒜 f]
      Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t :=
  letI inst := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := A) f A)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  LinearEquiv.ofBijective
    (((localizedAwayEquiv f).restrictScalars (Away 𝒜 f)).toLinearMap.restrict
      (p := GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f)
      (q := Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t)
      fun _ hx => localizedAwayEquiv_mem_twistAway 𝒜 hf t hx)
    ⟨fun a b hab => Subtype.ext ((localizedAwayEquiv f).injective
        (congrArg Subtype.val hab)),
      fun b => by
        obtain ⟨z, hz, hzb⟩ := exists_mem_of_mem_twistAway 𝒜 hf t b.2
        exact ⟨⟨z, hz⟩, Subtype.ext hzb⟩⟩

/-- The isomorphism of the two models is the identity on fractions. -/
public theorem twistAwayEquiv_apply_val {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (t : ℤ)
    (z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f) :
    ((twistAwayEquiv 𝒜 hf t z : Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t) :
      Localization (Submonoid.powers f)) = localizedAwayEquiv f (z : LocalizedModule.Away f A) :=
  rfl

end Stacks.AlgebraicGeometry.TwistAwayBridge

end

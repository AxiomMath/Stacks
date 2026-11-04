module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.Basic
public import StacksFrontier.AlgebraicGeometry.UniformTwistBound.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialHighTwist
public import StacksCore.Tactic.StacksAttribute

/-!
# The Hilbert polynomial of a coherent sheaf on projective space at a high twist

Let `k` be a field, let `n ≥ 0` and let `ℱ` be a coherent sheaf on `ℙⁿ_k`. The Hilbert
polynomial of `ℱ` is the polynomial agreeing with `d ↦ χ(ℙⁿ_k, ℱ(d))`, and evaluated at a
sufficiently large integer it is `dim_k H⁰(ℙⁿ_k, ℱ(d))`: all the higher cohomology of `ℱ(d)`
vanishes once `d` is large, so the alternating sum defining the Euler characteristic collapses
to its degree-zero term. This is [Stacks, Tag 08AE].

## Which `ℙⁿ_k` this is

The statement below is for `ℙⁿ_k = Proj k[T₀, …, Tₙ]`, which is the model this directory works
on and the one carrying the vanishing theorem it needs.

The development also carries a second model, `AlgebraicGeometry.projectiveSpaceOverRing n R`,
the base change of `Proj (ULift ℤ)[T₀, …, Tₙ]` along `Spec R ⟶ Spec ℤ`, and it is *that* model
on which `AlgebraicGeometry.hilbertPolynomial` — the definition carrying `@[stacks 08AD]` — is
defined. The two models are isomorphic, by part (2) of [Stacks, Tag 01N2]
(`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`), but **their twisting sheaves are
not yet identified in Lean**: that is part (3) of the same tag, which this development does not
have. So no statement here mentions `AlgebraicGeometry.hilbertPolynomial`, and the Hilbert
polynomial enters instead as the hypothesis `hP` below — the defining property of
[Stacks, Tag 08AD], written out on this model. That is the source's own phrasing: 08AE is given
a coherent sheaf "with Hilbert polynomial `P ∈ ℚ[t]`", i.e. a `P` satisfying exactly `hP`.

No second Hilbert-polynomial constant is introduced.

## Main results

* `AlgebraicGeometry.exists_forall_isZero_cohomologyOverField_of_lt`: finitely many separate
  vanishing bounds, together with vanishing from a fixed degree on, give one bound valid in
  every positive degree at once. Stated for an arbitrary scheme over a field and an arbitrary
  family of modules, since nothing in it is about projective space.
* `Stacks.ProjectiveSpace.Cohomology.exists_eval_eq_finrank_cohomologyOverField_zero`:
  **[Stacks, Tag 08AE]** on `Proj k[T₀, …, Tₙ]`.

## Implementation notes

A single bound valid in *every* positive degree cannot be assembled from one bound per degree,
there being infinitely many degrees; what makes the supremum a finite one is a degree beyond
which the cohomology vanishes outright. Here that degree is `n + 1`, from
`Stacks.ProjectiveCohomology.isZero_Hgroup_proj_of_lt`, which needs only quasi-coherence of the
twists (`…Tag0B5QUniformTwistBound.isQuasicoherent_twistSheafOfModules`) and no hypothesis on
the twist degree. So [Stacks, Tag 01YS] clause (4) is consumed only in the finitely many degrees
`0 < i < n + 1`.

The vanishing input is stated for the abelian-group-valued cohomology `Hgroup` and the Euler
characteristic for the `k`-module-valued `AlgebraicGeometry.cohomologyOverField`; the two are
passed between by `AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup`, which is
already stated for an arbitrary scheme over `Spec k` and so needs no bridging here.

`Stacks.ProjectiveCohomology.projModelToSpec` is the structure morphism `Proj k[T₀, …, Tₙ] ⟶
Spec k` that `AlgebraicGeometry.cohomologyOverField` needs in order to say what the `k`-module
structure on the cohomology is.

## References

* [Stacks Project, Tag 08AE](https://stacks.math.columbia.edu/tag/08AE)
* [Stacks Project, Tag 08AD](https://stacks.math.columbia.edu/tag/08AD)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **One vanishing bound in every positive degree at once.** Let `T` be a family of modules on
a scheme over a field `k`. If in each positive degree below `N` the cohomology of the `T d`
vanishes from some degree `d₀ i` on, and from degree `N` on it vanishes for every member of the
family, then there is a single `d₀` beyond which every positive-degree cohomology group of `T d`
vanishes: the supremum of the finitely many `d₀ i`. -/
public theorem exists_forall_isZero_cohomologyOverField_of_lt (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (T : ℤ → X.Modules) (N : ℕ)
    (hlt : ∀ i : ℕ, 0 < i → i < N → ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (cohomologyOverField k f (T d) i))
    (hge : ∀ i : ℕ, N ≤ i → ∀ d : ℤ, IsZero (cohomologyOverField k f (T d) i)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ i : ℕ, 0 < i →
      IsZero (cohomologyOverField k f (T d) i) := by
  choose! b hb using hlt
  refine ⟨((Finset.Ico 1 N).sup fun i => (b i).toNat : ℕ), fun d hd i hi => ?_⟩
  by_cases hiN : i < N
  · refine hb i hi hiN d ((Int.self_le_toNat (b i)).trans (le_trans ?_ hd))
    exact_mod_cast Finset.le_sup (f := fun j : ℕ => (b j).toNat) (Finset.mem_Ico.2 ⟨hi, hiN⟩)
  · exact hge i (by omega) d

end AlgebraicGeometry

namespace Stacks.ProjectiveSpace.Cohomology

open Stacks.ProjectiveCohomology (polyGrading projModelToSpec isZero_Hgroup_proj_of_lt)

/-- **[Stacks, Tag 08AE].** Let `k` be a field, let `n ≥ 0`, let `ℱ` be a coherent sheaf on
`ℙⁿ_k = Proj k[T₀, …, Tₙ]` and let `P ∈ ℚ[t]` be its Hilbert polynomial, that is, a polynomial
agreeing at every integer `d` with the Euler characteristic `χ(ℙⁿ_k, ℱ(d))` of the `d`-th twist.
Then

`P(d) = dim_k H⁰(ℙⁿ_k, ℱ(d))`

for all `d` large enough.

The proof is the source's one sentence: the higher cohomology of a high enough twist vanishes
([Stacks, Tag 01YS] clause (4),
`Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent`), so the
alternating sum defining the Euler characteristic collapses to its degree-zero term. The
hypothesis `hP` is the definition of the Hilbert polynomial, [Stacks, Tag 08AD]; see the module
docstring for why it is written out here rather than cited as
`AlgebraicGeometry.hilbertPolynomial`. -/
@[stacks 08AE]
public theorem exists_eval_eq_finrank_cohomologyOverField_zero (k : Type u) [Field k] (n : ℕ)
    (F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (P : Polynomial ℚ)
    (hP : ∀ d : ℤ, P.eval (d : ℚ) = (((∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
      (Module.finrank k (cohomologyOverField k (projModelToSpec k n)
        (twistSheafOfModules (polyGrading k n) F d) i) : ℤ) : ℤ)) : ℚ)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      P.eval (d : ℚ) = (Module.finrank k (cohomologyOverField k (projModelToSpec k n)
        (twistSheafOfModules (polyGrading k n) F d) 0) : ℚ) := by
  obtain ⟨d₀, hd₀⟩ := AlgebraicGeometry.exists_forall_isZero_cohomologyOverField_of_lt k
    (projModelToSpec k n) (fun d => twistSheafOfModules (polyGrading k n) F d) (n + 1)
    (fun i hi _ => by
      obtain ⟨e, he⟩ :=
        Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent k n i hi
          F hF
      exact ⟨e, fun d hd =>
        (isZero_cohomologyOverField_iff_isZero_hgroup k _ _ i).2 (he d hd)⟩)
    (fun i hi d =>
      (isZero_cohomologyOverField_iff_isZero_hgroup k _ _ i).2
        (@isZero_Hgroup_proj_of_lt k _ n (twistSheafOfModules (polyGrading k n) F d)
          (Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistSheafOfModules
            (polyGrading k n) F (isQuasicoherent_of_isCoherent F) d) i (by omega)))
  refine ⟨d₀, fun d hd => ?_⟩
  rw [hP d, AlgebraicGeometry.finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero k
    (projModelToSpec k n) (twistSheafOfModules (polyGrading k n) F d) (hd₀ d hd)]
  norm_cast

end Stacks.ProjectiveSpace.Cohomology

end

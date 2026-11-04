module

public import StacksFrontier.RingTheory.TateMap.LocalTate
public import StacksFrontier.RingTheory.TateMap.UniversalNice

/-!
# The Tate map on the quasi-finite basic charts of the universal family

On a quasi-finite basic chart `B = univChart n d k` of the universal family of Example 0FK8
there is an isomorphism `c : det(NL_{B/A}) → ω_{B/A}` carrying `δ(NL_{B/A})` to the trace
element `τ_{B/A}` (Remark 0FKC and Lemma 0BWH), and, the chart being nice, it is the only one.
This is the first step of the proof of Proposition 0FKD: the problem is solved on the nice
charts.

## Main definitions

* `Stacks.TateMap.cUniv n d k F`: the isomorphism `det(NL_{B/A}) ≅ ω_{B/A}` of a quasi-finite
  basic universal chart carrying `δ` to `τ`.

## Main results

* `Stacks.TateMap.cUniv_deltaNL`: `cUniv` carries `δ(NL_{B/A})` to `τ_{B/A}`.
* `Stacks.TateMap.eq_cUniv`: it is the only isomorphism doing so.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open Stacks.Discriminant

universe u

namespace Stacks.TateMap

variable (n d : ℕ) (k : MvPolynomial (Fin n) (univBase.{u} n d))
  [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]

instance : Algebra.Syntomic (univBase.{u} n d) (univChart n d k) :=
  syntomic_of_algEquiv_localizedCompleteIntersection AlgEquiv.refl

/-- **The Tate map of a quasi-finite basic universal chart.** The isomorphism
`det(NL_{B/A}) ≅ ω_{B/A}` carrying `δ(NL_{B/A})` to the trace element, for
`A = univBase n d` and `B = univChart n d k`. -/
def cUniv (F : FiniteOpenFactorization.{u, u, u} (univBase.{u} n d) (univChart n d k)) :
    detNL (univBase.{u} n d) (univChart n d k) ≃ₗ[univChart n d k] dualizingModule F :=
  (exists_linearEquiv_detNL_dualizingModule_deltaNL
    (AlgEquiv.refl : univChart n d k ≃ₐ[univBase.{u} n d] univChart n d k) F).choose

/-- `cUniv` carries `δ(NL_{B/A})` to the trace element `τ_{B/A}`. -/
theorem cUniv_deltaNL
    (F : FiniteOpenFactorization.{u, u, u} (univBase.{u} n d) (univChart n d k)) :
    cUniv n d k F (deltaNL (univBase.{u} n d) (univChart n d k)) =
      dualizingModule.traceElement F :=
  (exists_linearEquiv_detNL_dualizingModule_deltaNL
    (AlgEquiv.refl : univChart n d k ≃ₐ[univBase.{u} n d] univChart n d k) F).choose_spec

/-- **Uniqueness of the Tate map on a quasi-finite basic universal chart.** For a positive degree
bound, every isomorphism `det(NL_{B/A}) ≅ ω_{B/A}` carrying `δ(NL_{B/A})` to `τ_{B/A}` is
`cUniv`: the chart is nice. -/
theorem eq_cUniv [NeZero d]
    (F : FiniteOpenFactorization.{u, u, u} (univBase.{u} n d) (univChart n d k))
    (e : detNL (univBase.{u} n d) (univChart n d k) ≃ₗ[univChart n d k] dualizingModule F)
    (he : e (deltaNL (univBase.{u} n d) (univChart n d k)) = dualizingModule.traceElement F) :
    e = cUniv n d k F :=
  (isNiceChart_univChart n d k).linearEquiv_ext F e (cUniv n d k F) _ he (cUniv_deltaNL n d k F)

end Stacks.TateMap

module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointIndivisibility

/-!
# A class of given dimension, read in a given codimension

Chapter 45 grades the Chow groups of a scheme `X` smooth over a field `k` by codimension,
`CH^c(X) = ∏_d CH_{d-c}(X_d)` (`Stacks.Chow.codimensionChowGroup`), `X_d` being the open and
closed part of `X` of dimension `d`. A class `α ∈ CH_m(X)` of dimension `m` restricts to
`α|_{X_d} ∈ CH_m(X_d)`, which has codimension `d - m` in `X_d`; its part of codimension `c` is
therefore the class whose component on `X_d` is `α|_{X_d}` when `m = d - c` and `0` otherwise
(`Stacks.WeilCohomology.chowGroupToCodimension`). When `X` has constant dimension `n` the only
component that can be nonzero is the one on `X_n = X`, and a class of dimension `m` is a class of
codimension `n - m`. This is how a pushforward `j_*β` along a closed immersion, computed in a
Chow group graded by dimension (Stacks 0FFE, Lemma 0FIH), is compared with classes graded by
codimension.

For `m = 0` this is `Stacks.WeilCohomology.zeroCycleToCodimension`
(`Stacks.WeilCohomology.chowGroupToCodimension_zero`).

## Main definitions

* `Stacks.WeilCohomology.chowGroupToCodimension`: `CH_m(X) ⟶ CH^c(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

/-- **A class of dimension `m`, read in codimension `c`**: `CH_m(X) = ∏_d CH_m(X_d)`, and
`CH_m(X_d) = CH_{d-c}(X_d)` is the part of `CH^c(X) = ∏_d CH_{d-c}(X_d)` on `X_d` when
`m = d - c`; on the other parts the class is `0`. -/
def chowGroupToCodimension (m c : ℤ) :
    chowGroup (fieldChowSituation k) sX m →+ codimensionChowGroup k sX c :=
  AddMonoidHom.pi fun d : ℕ ↦
    if h : m = d - c then
      (chowGroupDegreeEquiv _ _ h).toAddMonoidHom.comp
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m)
    else 0

/-- On a part `X_d` with `m = d - c`, the component of `chowGroupToCodimension` at `α` is the
restriction `α|_{X_d}`, transported along `CH_m(X_d) = CH_{d-c}(X_d)`. -/
theorem chowGroupToCodimension_apply_of_eq (m c : ℤ) (α : chowGroup (fieldChowSituation k) sX m)
    (d : ℕ) (h : m = d - c) :
    chowGroupToCodimension sX m c α d =
      chowGroupDegreeEquiv _ _ h
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m α) := by
  simp only [chowGroupToCodimension, AddMonoidHom.pi_apply, dif_pos h]
  rfl

/-- On a part `X_d` with `m ≠ d - c`, the component of `chowGroupToCodimension` is `0`. -/
theorem chowGroupToCodimension_apply_of_ne (m c : ℤ) (α : chowGroup (fieldChowSituation k) sX m)
    (d : ℕ) (h : m ≠ d - c) : chowGroupToCodimension sX m c α d = 0 := by
  simp only [chowGroupToCodimension, AddMonoidHom.pi_apply, dif_neg h]
  rfl

/-- The component of `chowGroupToCodimension` on a part where the degrees match is the restriction
of the class, as a heterogeneous equality. -/
theorem chowGroupToCodimension_apply_heq (m c : ℤ) (α : chowGroup (fieldChowSituation k) sX m)
    (d : ℕ) (h : m = d - c) :
    chowGroupToCodimension sX m c α d ≍
      chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m α := by
  rw [chowGroupToCodimension_apply_of_eq sX m c α d h]
  exact chowGroupDegreeEquiv_heq _ _ _ _

/-- **For `m = 0` this is `zeroCycleToCodimension`.** -/
theorem chowGroupToCodimension_zero (c : ℤ) :
    chowGroupToCodimension sX 0 c = zeroCycleToCodimension sX c :=
  rfl

/-- `chowGroupToCodimension` depends on the structure morphism, the degree and the class only up to
equality and heterogeneous equality. -/
theorem chowGroupToCodimension_congr {sX' : X ⟶ (fieldChowSituation k).S} [Smooth sX']
    (hs : sX = sX') {m m' : ℤ} (hm : m = m') (c : ℤ) {α : chowGroup (fieldChowSituation k) sX m}
    {α' : chowGroup (fieldChowSituation k) sX' m'} (hα : α ≍ α') :
    chowGroupToCodimension sX m c α ≍ chowGroupToCodimension sX' m' c α' := by
  subst hs hm
  cases hα
  rfl

/-- **The codimension-`c` part of a pushforward** depends on the structure morphism of the source,
the degree and the pushed-forward class only up to equality and heterogeneous equality: for
`j : E ⟶ X` proper and `β ≍ β'` over equal structure morphisms of `E`, the classes
`j_*β` and `j_*β'` read in codimension `c` agree. -/
theorem chowGroupToCodimension_properChowPushforward_congr {E : Scheme.{u}}
    {sE sE' : E ⟶ (fieldChowSituation k).S} [LocallyOfFiniteType sE] [LocallyOfFiniteType sE']
    (hs : sE = sE') (j : E ⟶ X) [IsProper j] (hj : j ≫ sX = sE) (hj' : j ≫ sX = sE')
    {m m' : ℤ} (hm : m = m') (c : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation k) sE sX j hj m)
    (hfac' :
      ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation k) sE' sX j hj' m')
    {β : chowGroup (fieldChowSituation k) sE m} {β' : chowGroup (fieldChowSituation k) sE' m'}
    (hβ : β ≍ β') :
    chowGroupToCodimension sX m c
        (properChowPushforward (fieldChowSituation k) sE sX j hj m hfac β) =
      chowGroupToCodimension sX m' c
        (properChowPushforward (fieldChowSituation k) sE' sX j hj' m' hfac' β') := by
  subst hs hm
  cases hβ
  rfl

end Stacks.WeilCohomology

end

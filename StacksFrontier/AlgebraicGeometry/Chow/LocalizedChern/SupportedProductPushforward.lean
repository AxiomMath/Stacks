module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCoverProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Modification

/-!
# The product of two classes supported on a closed subscheme, through the pushforward

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. The third multiplication of
Stacks 0FA0 sends `c ∈ A^p(Z ⟶ X)` and `c' ∈ A^q(Z ⟶ X)` to `res(c) ∘ c'`, where
`res : A^p(Z ⟶ X) ⟶ A^p(Z)` is the restriction map of Stacks 0FA1. Stacks 0FA1 computes
`res(c) ∩ α = c ∩ i_* α` for `α ∈ CH_*(Z)`; read on the classes, this says

  `res(c) ∘ c' = c ∘ (i_* ∘ c')`,

with `i_* ∘ c' ∈ A^q(X)` the pushforward of Stacks 0EPK and the right side the first
multiplication `A^p(Z ⟶ X) × A^q(X) ⟶ A^{p+q}(Z ⟶ X)` of Stacks 0FA0.

## Main results

* `Stacks.Chow.supportedMul_eq_supportedRightComp` — `res(c) ∘ c' = c ∘ (i_* ∘ c')`.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hf : f ≫ sX = sZ) {p q : ℤ}

/-- For a closed immersion `f : Z ⟶ X` and classes `c ∈ A^p(Z ⟶ X)`, `c' ∈ A^q(Z ⟶ X)`, the
third multiplication `res(c) ∘ c'` of Stacks 0FA0 is the first multiplication `c ∘ (f_* ∘ c')`
of `c` with the pushforward `f_* ∘ c' ∈ A^q(X)` of Stacks 0EPK. -/
theorem supportedMul_eq_supportedRightComp
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    supportedMul C sZ sX f hf c c' =
      supportedRightComp C sZ sX f hf c (properPushforwardChowCohomology C sX sZ f hf c') := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ eq_of_heq ?_
  refine (supportedLeftComp_cap C sZ sX f hf _ c' t k α).trans (HEq.trans ?_
    (supportedRightComp_cap C sZ sX f hf c _ t k α).symm)
  have hm : pullback.fst f t ≫ f = pullback.snd f t ≫ t := pullback.condition
  rw [BivariantClass.idRule_bivariantClassCongrBase,
    closedImmersionChowCohomologyRestriction_idRule]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  rw [idRule_properPushforwardChowCohomology]
  have hs : pullback.fst f t ≫ sZ = (pullback.snd f t ≫ t) ≫ sX := by
    rw [← hf, ← Category.assoc, hm, Category.assoc]
  have hpush : chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
      (pullbackSnd_comp_structureMorphism hf t) (k - q) (c'.cap t k α) =
      properChowPushforward C ((pullback.snd f t ≫ t) ≫ sX) (t ≫ sX) (pullback.snd f t)
        (by simp [Category.assoc]) (k - q) (properPushforwardDescends C _ _ _ _ _)
        (chowGroupCongr C hs (k - q) (c'.cap t k α)) :=
    eq_of_heq (properChowPushforward_heq_congr_base C (pullback.snd f t) hs rfl _ _ rfl
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _
      (chowGroupCongr_heq C hs (k - q) _).symm)
  have hnat := c.proper_naturality t (pullback.snd f t)
    (bivariantBaseChangeMap f t (pullback.snd f t))
    (isPullback_bivariantBaseChangeMap f t (pullback.snd f t))
    (bivariantBaseChangeMap_fst f t (pullback.snd f t)) (k - q)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (chowGroupCongr C hs (k - q) (c'.cap t k α))
  rw [hpush, hnat]
  have hB : pullback.fst f t ≫ f ≫ sX = pullback.fst f t ≫ sZ := by rw [hf]
  refine (properChowPushforward_heq_congr_base C (pullback.snd f (pullback.fst f t ≫ f)) rfl hB
    _ (by rw [← hB]; exact pullbackSnd_comp_comp_structureMorphism C sZ sX f hf _) rfl
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _
    HEq.rfl).trans ?_
  refine chowPush_pullback_heq_of_test_eq C f hm _ _ _ _ ?_ ((k - q) - p)
    (c.cap_heq_of_eq hm (k - q) ((chowGroupCongr_heq C _ (k - q) _).trans
      ((chowGroupCongr_heq C _ (k - q) _).trans (chowGroupCongr_heq C hs (k - q) _).symm)))
  refine pullback.hom_ext ?_ ?_
  · simp only [bivariantBaseChangeMap]
    refine (cancel_mono f).1 ?_
    simp [pullback.condition]
  · simp [bivariantBaseChangeMap]

end Stacks.Chow

end

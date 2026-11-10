module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# A functor acyclic on a bounded below complex preserves its homology

Let `G : 𝒞 ⥤ 𝒟` be a left exact additive functor between abelian categories, with `𝒞` having
enough injectives, and let `K` be a cochain complex of `𝒞` indexed by `ℤ` and concentrated in
degrees `≥ a`. If every term and every homology object of `K` is right acyclic for `G` —
[Stacks, Tag 0157] — then `G` preserves the homology of `K` in every degree, and the cycles of `K`
are right acyclic too.

This is `CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc` for a
`ℤ`-indexed complex which is strictly bounded below; the induction starts at the lowest degree,
where the incoming differential vanishes.

## Main results

* `CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc_of_isStrictlyGE`:
  the statement above.
* `CategoryTheory.Functor.homologyMapIsoOfRightAcyclic`: the resulting isomorphism
  `Hⁿ(G(K)) ≅ G(Hⁿ(K))`.

## References

* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]

/-- **A functor right acyclic on the terms and the homology of a strictly bounded below cochain
complex preserves its homology.** If `K` is concentrated in degrees `≥ a` and every `K.X n` and
every `K.homology n` is right acyclic for `G`, then in every degree `n ≥ a` the cycles of `K` are
right acyclic and `G` preserves the left homology of the degree-`n` short complex of `K`. -/
theorem rightAcyclic_cycles_and_preservesLeftHomologyOf_sc_of_isStrictlyGE
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hX : ∀ n, G.rightAcyclic (K.X n)) (hH : ∀ n, G.rightAcyclic (K.homology n))
    (n : ℤ) (hn : a ≤ n) :
    G.rightAcyclic (K.cycles n) ∧ G.PreservesLeftHomologyOf (K.sc n) := by
  induction n, hn using Int.leInduction with
  | base =>
    have hf : (K.sc a).f = 0 :=
      (K.isZero_of_isStrictlyGE a ((ComplexShape.up ℤ).prev a) (by simp)).eq_of_src _ _
    have : IsIso (K.homologyπ a) := by
      change IsIso (K.sc a).homologyπ
      exact ShortComplex.isIso_homologyπ _ hf
    refine ⟨G.rightAcyclic.prop_of_iso (asIso (K.homologyπ a)).symm (hH a), ?_⟩
    exact G.preservesLeftHomology_of_zero_f (K.sc a) hf
  | succ n hn ih =>
    have hp : (ComplexShape.up ℤ).prev (n + 1) = n := by simp
    have hn' : (ComplexShape.up ℤ).next n = n + 1 := by simp
    let k : K.cycles n ⟶ (K.sc (n + 1)).X₁ := K.iCycles n ≫ (K.XIsoOfEq hp).inv
    have wk : k ≫ (K.sc (n + 1)).f = 0 := by
      change (K.iCycles n ≫ (K.XIsoOfEq hp).inv) ≫ K.d _ (n + 1) = 0
      rw [Category.assoc, K.XIsoOfEq_inv_comp_d, K.iCycles_d]
    have w : k ≫ (K.sc (n + 1)).toCycles = 0 := by
      rw [← cancel_mono (K.sc (n + 1)).iCycles, Category.assoc,
        ShortComplex.toCycles_i, zero_comp, wk]
    have hk0 : IsLimit (KernelFork.ofι k wk) := by
      refine IsKernel.ofIso (K.d n (n + 1)) (K.cyclesIsKernel n (n + 1) hn')
        (KernelFork.ofι k wk) (K.XIsoOfEq hp).symm (Iso.refl _) (Iso.refl _) ?_ ?_
      · change (K.XIsoOfEq hp).inv ≫ K.d _ _ = K.d n _ ≫ 𝟙 _
        simp
      · simp [k]
    have hk : IsLimit (KernelFork.ofι k w) :=
      isKernelOfComp (K.sc (n + 1)).iCycles (K.sc (n + 1)).f hk0 w
        (K.sc (n + 1)).toCycles_i
    apply G.rightAcyclic_cycles_and_preservesLeftHomologyOf (K.sc (n + 1)) k w hk ih.1 _
      (hH (n + 1))
    simpa [HomologicalComplex.sc, hp] using hX n

/-- **`Hⁿ(G(K)) ≅ G(Hⁿ(K))`** for a strictly bounded below cochain complex `K` whose terms and
homology objects are right acyclic for `G`: in degrees `≥ a` this is the comparison of the left
homology preserved by `G`, and below `a` both sides vanish. -/
noncomputable def homologyMapIsoOfRightAcyclic
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hX : ∀ n, G.rightAcyclic (K.X n)) (hH : ∀ n, G.rightAcyclic (K.homology n)) (n : ℤ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n ≅ G.obj (K.homology n) := by
  by_cases hn : a ≤ n
  · have := (G.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc_of_isStrictlyGE K a hX hH n
      hn).2
    exact (K.sc n).mapHomologyIso G
  · have hK : IsZero (K.homology n) := by
      have : IsZero (K.X n) := K.isZero_of_isStrictlyGE a n (by omega)
      exact ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) this
    have hGK : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n) := by
      have : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X n) :=
        G.map_isZero (K.isZero_of_isStrictlyGE a n (by omega))
      exact ShortComplex.isZero_homology_of_isZero_X₂
        (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc n) this
    exact hGK.iso (G.map_isZero hK)

end CategoryTheory.Functor

end

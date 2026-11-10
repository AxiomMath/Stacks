module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# A functor acyclic on a complex preserves its homology

Let `G : 𝒞 ⥤ 𝒟` be a left exact additive functor between abelian categories, with `𝒞` having
enough injectives, and let `K` be a cochain complex of `𝒞` indexed by `ℕ`. If every term and
every homology object of `K` is right acyclic for `G` — [Stacks, Tag 0157] — then `G` preserves
the homology of `K` in every degree, and the cycles of `K` are right acyclic too.

## Main results

* `CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf`: for a short complex
  `S` and a kernel `A` of `S.toCycles`, if `A`, `S.X₁` and `S.homology` are right acyclic for
  `G`, then so is `S.cycles`, and `G` preserves the left homology of `S`.
* `CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc`: if the terms and
  the homology of `K` are right acyclic for `G`, then so are its cycles, and `G` preserves the
  left homology of every short complex `K.sc n`.
* `CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg`: the right derived functors of `G` vanish
  in negative degrees.

## References

* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]

/-- Let `S` be a short complex and let `k : A ⟶ S.X₁` be a kernel of `S.toCycles`. If `A`,
`S.X₁` and `S.homology` are right acyclic for `G`, then so is `S.cycles`, and `G` preserves the
left homology of `S`. -/
theorem rightAcyclic_cycles_and_preservesLeftHomologyOf (S : ShortComplex C) {A : C}
    (k : A ⟶ S.X₁) (w : k ≫ S.toCycles = 0) (hk : IsLimit (KernelFork.ofι k w))
    (hA : G.rightAcyclic A) (hX : G.rightAcyclic S.X₁) (hH : G.rightAcyclic S.homology) :
    G.rightAcyclic S.cycles ∧ G.PreservesLeftHomologyOf S := by
  have : Mono k := mono_of_isLimit_fork hk
  have hT : (ShortComplex.mk k (cokernel.π k) (cokernel.condition k)).ShortExact :=
    ⟨(ShortComplex.mk k (cokernel.π k) (cokernel.condition k)).exact_of_g_is_cokernel
      (cokernelIsCokernel k)⟩
  obtain ⟨hB, hGT⟩ := (G.rightAcyclic_and_shortExact_map_of_shortExact _ hT).2.1 hA hX
  have hb : Mono (cokernel.desc k S.toCycles w) :=
    (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk k S.toCycles w) hk).mono_cokernelDesc
  have wb : cokernel.desc k S.toCycles w ≫ S.homologyπ = 0 := by
    rw [← cancel_epi (cokernel.π k), cokernel.π_desc_assoc, comp_zero,
      S.toCycles_comp_homologyπ]
  have hU : (ShortComplex.mk _ S.homologyπ wb).ShortExact :=
    ⟨(ShortComplex.mk _ S.homologyπ wb).exact_of_g_is_cokernel
      (isCokernelOfComp (cokernel.π k) S.toCycles S.homologyIsCokernel wb (by simp))⟩
  obtain ⟨hZ, hGU⟩ := (G.rightAcyclic_and_shortExact_map_of_shortExact _ hU).1 hB hH
  refine ⟨hZ, ?_⟩
  have : Epi (G.map (cokernel.π k)) := hGT.epi_g
  have hπ : IsColimit (CokernelCofork.ofπ (G.map S.homologyπ)
      (by rw [← G.map_comp, S.toCycles_comp_homologyπ, G.map_zero])) :=
    isCokernelEpiComp hGU.gIsCokernel (G.map (cokernel.π k)) (by simp [← G.map_comp])
  have : S.leftHomologyData.IsPreservedBy G :=
    { g := inferInstance
      f' := preservesColimit_of_preserves_colimit_cocone S.homologyIsCokernel
        ((isColimitMapCoconeCoforkEquiv' G S.toCycles_comp_homologyπ).symm hπ) }
  exact Functor.PreservesLeftHomologyOf.mk' G S.leftHomologyData

/-- If every `K.X n` and every `K.homology n` is right acyclic for `G`, then every `K.cycles n`
is too, and `G` preserves the left homology of the degree-`n` short complex of `K` in every
degree. -/
theorem rightAcyclic_cycles_and_preservesLeftHomologyOf_sc (K : CochainComplex C ℕ)
    (hX : ∀ n, G.rightAcyclic (K.X n)) (hH : ∀ n, G.rightAcyclic (K.homology n)) (n : ℕ) :
    G.rightAcyclic (K.cycles n) ∧ G.PreservesLeftHomologyOf (K.sc n) := by
  induction n with
  | zero =>
    refine ⟨(G.rightAcyclic).prop_of_iso (asIso (K.homologyπ 0)).symm (hH 0), ?_⟩
    exact G.preservesLeftHomology_of_zero_f (K.sc 0) (by simp [HomologicalComplex.sc]; rfl)
  | succ n ih =>
    have hp : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
    have hn : (ComplexShape.up ℕ).next n = n + 1 := by simp
    let k : K.cycles n ⟶ (K.sc (n + 1)).X₁ := K.iCycles n ≫ (K.XIsoOfEq hp).inv
    have wk : k ≫ (K.sc (n + 1)).f = 0 := by
      change (K.iCycles n ≫ (K.XIsoOfEq hp).inv) ≫ K.d _ (n + 1) = 0
      rw [Category.assoc, K.XIsoOfEq_inv_comp_d, K.iCycles_d]
    have w : k ≫ (K.sc (n + 1)).toCycles = 0 := by
      rw [← cancel_mono (K.sc (n + 1)).iCycles, Category.assoc,
        ShortComplex.toCycles_i, zero_comp, wk]
    have hk0 : IsLimit (KernelFork.ofι k wk) := by
      refine IsKernel.ofIso (K.d n (n + 1)) (K.cyclesIsKernel n (n + 1) hn)
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

/-- For `G : C ⥤ D` additive between abelian categories with enough injectives in `C`, the
right derived functor `R^qG` is zero on every object for `q < 0`. -/
theorem isZero_rightDerivedPlus_of_neg {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (G : C ⥤ D) [G.Additive] (A : C) (q : ℤ) (hq : q < 0) :
    IsZero ((G.rightDerivedPlus q).obj A) :=
  ((G.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith).1 q hq).obj A

end CategoryTheory.Functor

end

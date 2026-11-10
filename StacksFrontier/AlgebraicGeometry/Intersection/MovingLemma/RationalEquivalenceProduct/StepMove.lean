/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepOpen

/-!
# The degeneration of the cone

Let `X̄ ⊆ P` be a closed subvariety of a nonsingular variety `P` of dimension `N`, let `Y ⊆ X̄`
be a nonsingular open subvariety, let `C ⊆ P` be a closed subvariety meeting `X̄` properly, and
let `C' ⊆ P × ℙ¹` be a family with `C'_0 = C` meeting `Y × ℙ¹` properly. Tag 0B1M, applied on the
open subscheme `U ⊆ P` in which `Y` is closed, writes the restriction to `Y` of `C · X̄` as
`∑ n_k [E_{k,0}]_s` for closed subvarieties `E_k ⊆ Y × ℙ¹` of dimension `s + 1` lying over
`C' ∩ (Y × ℙ¹)`. This file records that presentation together with where the fibres of the `E_k`
lie.

## Main results

* `Stacks.Intersection.RationalEquivalenceProduct.exists_zeroFiber_presentation`: the restriction
  to `Y` of `C · X̄` is `∑ b(e) [E_{e,0}]_s`, the zero fibre of each `E_e` lying over `C` and its
  infinity fibre over `C'_∞`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

open scoped Classical in
/-- **The degeneration of the cone.** In the situation above, the restriction to `Y`
of `C · X̄` is `∑_{e ∈ S} b(e) [E_{e,0}]_s` for points `e` of `Y × ℙ¹` of dimension `s + 1` whose
closures `E_e` are contained in neither `Y × 0` nor, by their position, outside `C'`: the zero
fibre of `E_e` lies over `C` and its infinity fibre over `C'_∞`. -/
theorem exists_zeroFiber_presentation (k : Type u) [Field k] [IsAlgClosed k] {P : Scheme.{u}}
    (sP : P ⟶ Spec (.of k)) [IsVariety k sP] [IsLocallyNoetherian P] (hP : IsRegular P) {N : ℕ}
    (hPd : topologicalKrullDim P = (N : WithBot ℕ∞)) {Xb : Scheme.{u}} (iX : Xb ⟶ P)
    [IsClosedImmersion iX] [IsVariety k (iX ≫ sP)] {n s : ℕ}
    (hn : topologicalKrullDim Xb = (n : WithBot ℕ∞))
    {Y : Scheme.{u}} (j₀ : Y ⟶ Xb) [IsOpenImmersion j₀] (p : Y ⟶ Spec (.of k)) [IsVariety k p]
    (hp : j₀ ≫ iX ≫ sP = p) (hY : IsRegular Y)
    (C : IrreducibleCloseds P)
    (hCprop : AlgebraicCycle.IntersectProperly
      (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
      (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) (1 : ℤ)))
    (hrdC : relativeDimension (fieldChowSituation k).dimensionFunction sP
      C.isIrreducible.genericPoint + (n : ℤ) = (N : ℤ) + s)
    (y₀ : Y) (hy₀ : iX.base (j₀.base y₀) ∈ (C : Set P))
    (Cfam : IrreducibleCloseds (projectiveLineProduct sP))
    (hzero : zeroFiber sP (integralComponentAt Cfam.isIrreducible.genericPoint) =
      integralComponentAt C.isIrreducible.genericPoint)
    (hfam : topologicalKrullDim ↥((Cfam : Set (projectiveLineProduct sP)) ∩
          (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹'
            Set.range (j₀ ≫ iX).base) +
        topologicalKrullDim (projectiveLineProduct sP) ≤
      topologicalKrullDim ↥(Cfam : Set (projectiveLineProduct sP)) +
        topologicalKrullDim ↥((pullback.fst sP
          (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹'
            Set.range (j₀ ≫ iX).base))
    (hrdfam : relativeDimension (fieldChowSituation k).dimensionFunction
        (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ sP)
        Cfam.isIrreducible.genericPoint =
      relativeDimension (fieldChowSituation k).dimensionFunction sP
        C.isIrreducible.genericPoint + 1) :
    ∃ (S : Finset (projectiveLineProduct p)) (b : projectiveLineProduct p → ℤ),
      cycleComap j₀ j₀.isOpenEmbedding.injective (cycleComap iX iX.isClosedEmbedding.injective
          (torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP (s : ℤ)
            (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint 1)
            (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) 1))) =
        ∑ e ∈ S, b e • (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (zeroFiber p (integralComponentAt e)).subschemeι (s : ℤ)).1 ∧
      ∀ e ∈ S, relativeDimension (fieldChowSituation k).dimensionFunction
          (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) e =
            (s : ℤ) + 1 ∧
        ¬ Set.range (integralComponentAt e).subschemeι.base ⊆ Set.range (zeroSection p).base ∧
        (∀ y ∈ ((zeroFiber p (integralComponentAt e)).support : Set Y),
          iX.base (j₀.base y) ∈ (C : Set P)) ∧
        (∀ y ∈ ((infinityFiber p (integralComponentAt e)).support : Set Y),
          (infinitySection sP).base (iX.base (j₀.base y)) ∈
            (Cfam : Set (projectiveLineProduct sP))) := by
  obtain ⟨U, ι, hιcl, hι⟩ : ∃ (U : P.Opens) (ι : Y ⟶ U.toScheme), IsClosedImmersion ι ∧
      ι ≫ U.ι = j₀ ≫ iX :=
    ⟨(j₀ ≫ iX).coborderRange, (j₀ ≫ iX).liftCoborder, inferInstance,
      Scheme.Hom.liftCoborder_ι _⟩
  have hp' : ι ≫ U.ι ≫ sP = p := by rw [← Category.assoc, hι, Category.assoc, hp]
  subst hp'
  have hyU : ∀ y : Y, U.ι.base (ι.base y) = iX.base (j₀.base y) := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hι, Scheme.Hom.comp_apply]
  have : Nonempty U.toScheme := ⟨ι.base y₀⟩
  have : IsVariety k (U.ι ≫ sP) := isVariety_opens_ι k sP U
  have hUreg : IsRegular U.toScheme := hP.restrict U
  have hdU : topologicalKrullDim U.toScheme = (N : WithBot ℕ∞) := by
    rw [← hPd]; exact topologicalKrullDim_opens k sP U
  have hdY : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
    have h := ProjectiveSpaceOfModule.topologicalKrullDim_closure_image_of_isOpenImmersion k
      (iX ≫ sP) j₀ isClosed_univ (IrreducibleSpace.isIrreducible_univ Y)
    have hdense : closure (j₀.base '' (Set.univ : Set Y)) = Set.univ := by
      rw [Set.image_univ]
      exact (j₀.isOpenEmbedding.isOpen_range.dense ⟨_, Set.mem_range_self y₀⟩).closure_eq
    rw [hdense, topologicalKrullDim_univ, topologicalKrullDim_univ, hn] at h
    exact h.symm
  have hgenY : U.ι.base (ι.base (genericPoint Y)) = iX.base (genericPoint Xb) := by
    rw [hyU, genericPoint_image_of_isOpenImmersion j₀]
  have hzsupp : ∀ x : P, (zeroSection sP).base x ∈ (Cfam : Set (projectiveLineProduct sP)) ↔
      x ∈ (C : Set P) := by
    intro x
    have h : x ∈ ((zeroFiber sP (integralComponentAt Cfam.isIrreducible.genericPoint)).support :
        Set P) ↔ x ∈ ((integralComponentAt C.isIrreducible.genericPoint).support : Set P) := by
      rw [hzero]
    rwa [coe_support_zeroFiber, coe_support_integralComponentAt, coe_support_integralComponentAt,
      Set.mem_preimage, Cfam.isIrreducible.closure_genericPoint Cfam.isClosed',
      C.isIrreducible.closure_genericPoint C.isClosed'] at h
  obtain ⟨c', hc'⟩ : ∃ c' : U.toScheme, U.ι.base c' = C.isIrreducible.genericPoint :=
    mem_of_isOpen_of_mem_closure U.ι.isOpenEmbedding.isOpen_range
      (by rw [C.isIrreducible.closure_genericPoint C.isClosed']; exact hy₀) ⟨ι.base y₀, hyU y₀⟩
  have hfstz : ∀ x : P,
      (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base
        ((zeroSection sP).base x) = x := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, zeroSection_comp_fst]; rfl
  obtain ⟨g', hg'⟩ : ∃ g' : projectiveLineProduct (U.ι ≫ sP),
      (familyBaseChange sP U.ι).base g' = Cfam.isIrreducible.genericPoint := by
    have hmem : (zeroSection sP).base C.isIrreducible.genericPoint ∈
        Set.range (familyBaseChange sP U.ι).base := by
      rw [range_familyBaseChange, Set.mem_preimage, hfstz]
      exact ⟨c', hc'⟩
    exact mem_of_isOpen_of_mem_closure (familyBaseChange sP U.ι).isOpenEmbedding.isOpen_range
      (by rw [Cfam.isIrreducible.closure_genericPoint Cfam.isClosed', hzsupp]
          exact (C.isIrreducible.isGenericPoint_genericPoint C.isClosed').mem) hmem
  have : IsIntegral (integralComponentAt g').subscheme := isIntegral_integralComponentAt g'
  have hC''comap : (integralComponentAt Cfam.isIrreducible.genericPoint).comap
      (familyBaseChange sP U.ι) = integralComponentAt g' := by
    rw [← hg']; exact comap_integralComponentAt_of_isOpenImmersion _ g'
  have hzero'' : zeroFiber (U.ι ≫ sP) (integralComponentAt g') = integralComponentAt c' := by
    rw [← hC''comap, zeroFiber_comap_familyBaseChange, hzero, ← hc',
      comap_integralComponentAt_of_isOpenImmersion]
  obtain ⟨c, hc⟩ : ∃ c : ℕ, relativeDimension (fieldChowSituation k).dimensionFunction sP
      C.isIrreducible.genericPoint = c :=
    ⟨_, (Int.toNat_of_nonneg (relativeDimension_fieldChowSituation_nonneg k sP _)).symm⟩
  have hrs : c + n = N + s := by
    rw [hc] at hrdC; exact_mod_cast hrdC
  have hdeg : ((c : ℤ) + n - N) = s := by omega
  have hdimc' : topologicalKrullDim (closure ({c'} : Set U.toScheme)) = (c : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq k (U.ι ≫ sP),
      relativeDimension_comp_isOpenImmersion, hc', hc, Int.toNat_natCast]
  have hdimC : topologicalKrullDim ↥(C : Set P) = (c : WithBot ℕ∞) := by
    rw [← C.isIrreducible.closure_genericPoint C.isClosed',
      topologicalKrullDim_closure_singleton_eq k sP, hc, Int.toNat_natCast]
  have hc1 : ((c : ℤ) + 1).toNat = c + 1 := by omega
  have hdimg' : topologicalKrullDim (closure ({g'} : Set (projectiveLineProduct (U.ι ≫ sP)))) =
      ((c + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq k
      (pullback.fst (U.ι ≫ sP) (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ U.ι ≫ sP),
      ← familyBaseChange_comp_structure k sP U.ι, relativeDimension_comp_isOpenImmersion, hg',
      hrdfam, hc, hc1]
  have hdimCfam : topologicalKrullDim ↥(Cfam : Set (projectiveLineProduct sP)) =
      ((c + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← Cfam.isIrreducible.closure_genericPoint Cfam.isClosed',
      topologicalKrullDim_closure_singleton_eq k
        (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ sP),
      hrdfam, hc, hc1]
  have hclosure_dim : ∀ {A B : Scheme.{u}} [IsIntegral A] (f : A ⟶ B) [IsClosedImmersion f]
      {d : WithBot ℕ∞}, topologicalKrullDim A = d →
      topologicalKrullDim (closure ({f.base (genericPoint A)} : Set B)) = d := by
    intro A B _ f _ d hd
    rw [← range_eq_closure_singleton f, ← Set.image_univ,
      topologicalKrullDim_image_eq_of_isEmbedding f.isClosedEmbedding.isEmbedding,
      topologicalKrullDim_univ, hd]
  have hdimw := hclosure_dim ι hdY
  have hC' : topologicalKrullDim ((integralComponentAt g').support :
      Set (projectiveLineProduct (U.ι ≫ sP))) = ((c + 1 : ℕ) : WithBot ℕ∞) := by
    rw [coe_support_integralComponentAt]; exact hdimg'
  have h1 : topologicalKrullDim ((zeroFiber (U.ι ≫ sP) (integralComponentAt g')).support :
      Set U.toScheme) = (c : WithBot ℕ∞) := by
    rw [hzero'', coe_support_integralComponentAt]; exact hdimc'
  have hcyc : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (U.ι ≫ sP)
      (zeroFiber (U.ι ≫ sP) (integralComponentAt g')).subschemeι (c : ℤ)).1 =
      Function.locallyFinsuppWithin.single c' 1 := by
    rw [hzero'']
    have := isIntegral_integralComponentAt c'
    have hgen : (integralComponentAt c').subschemeι.base
        (genericPoint (integralComponentAt c').subscheme) = c' :=
      genericPointOf_integralComponentAt c'
    rw [cycleAssociatedToClosedSubscheme_eq_single _ _ _ _
      (by rw [hgen, relativeDimension_comp_isOpenImmersion, hc', hc]), hgen]
  have hXd := hclosure_dim iX hn
  have hCX : topologicalKrullDim ↥((C : Set P) ∩ Set.range iX.base) + (N : WithBot ℕ∞) ≤
      ((c + n : ℕ) : WithBot ℕ∞) := by
    have h := intersectProperly_closure_of_single hCprop
    rwa [intersectProperly_closure_iff hPd
      (by rw [C.isIrreducible.closure_genericPoint C.isClosed']; exact hdimC) hXd,
      C.isIrreducible.closure_genericPoint C.isClosed', ← range_eq_closure_singleton iX] at h
  have h3 : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (U.ι ≫ sP)
        (zeroFiber (U.ι ≫ sP) (integralComponentAt g')).subschemeι (c : ℤ)).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint Y)) (1 : ℤ)) := by
    rw [hcyc]
    refine intersectProperly_single_single_of_closure ((intersectProperly_closure_iff hdU hdimc'
      hdimw).mpr ?_)
    refine le_trans (add_le_add_left ?_ _) hCX
    rw [← topologicalKrullDim_image_eq_of_isEmbedding U.ι.isOpenEmbedding.isEmbedding]
    refine topologicalKrullDim_le_of_subset ?_
    rintro _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have hsp := (specializes_iff_mem_closure.mpr hu1).map U.ι.continuous
      rwa [specializes_iff_mem_closure, hc',
        C.isIrreducible.closure_genericPoint C.isClosed'] at hsp
    · rw [← range_eq_closure_singleton ι] at hu2
      obtain ⟨y, rfl⟩ := hu2
      exact ⟨j₀.base y, (hyU y).symm⟩
  have hfst : ∀ {A B : Scheme.{u}} (f : B ⟶ Spec (.of k)) (i : A ⟶ B) w,
      (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base
        ((familyBaseChange f i).base w) = i.base ((pullback.fst (i ≫ f)
          (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base w) := fun f i w ↦ by
    rw [← Scheme.Hom.comp_apply, familyBaseChange_comp_fst, Scheme.Hom.comp_apply]
  have h2 : topologicalKrullDim ↥(((integralComponentAt g').support :
        Set (projectiveLineProduct (U.ι ≫ sP))) ∩
        Set.range (familyBaseChange (U.ι ≫ sP) ι).base) +
      topologicalKrullDim (projectiveLineProduct (U.ι ≫ sP)) ≤
      topologicalKrullDim ((integralComponentAt g').support :
        Set (projectiveLineProduct (U.ι ≫ sP))) +
      topologicalKrullDim (Set.range (familyBaseChange (U.ι ≫ sP) ι).base) := by
    rw [coe_support_integralComponentAt]
    have hQ' : topologicalKrullDim (projectiveLineProduct (U.ι ≫ sP)) =
        topologicalKrullDim (projectiveLineProduct sP) := by
      rw [topologicalKrullDim_projectiveLineProduct, topologicalKrullDim_projectiveLineProduct,
        hdU, hPd]
    have hA : topologicalKrullDim ↥(closure ({g'} : Set (projectiveLineProduct (U.ι ≫ sP))) ∩
        Set.range (familyBaseChange (U.ι ≫ sP) ι).base) ≤
        topologicalKrullDim ↥((Cfam : Set (projectiveLineProduct sP)) ∩
          (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹'
            Set.range (j₀ ≫ iX).base) := by
      rw [← topologicalKrullDim_image_eq_of_isEmbedding
        (familyBaseChange sP U.ι).isOpenEmbedding.isEmbedding]
      refine topologicalKrullDim_le_of_subset ?_
      rintro _ ⟨w, ⟨hw1, ⟨v, rfl⟩⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · have hsp := (specializes_iff_mem_closure.mpr hw1).map (familyBaseChange sP U.ι).continuous
        rwa [specializes_iff_mem_closure, hg',
          Cfam.isIrreducible.closure_genericPoint Cfam.isClosed'] at hsp
      · rw [Set.mem_preimage, hfst, hfst, hyU]
        exact ⟨_, rfl⟩
    have hB : topologicalKrullDim ↥((pullback.fst sP
        (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹'
          Set.range (j₀ ≫ iX).base) ≤
        topologicalKrullDim ↥(Set.range (familyBaseChange (U.ι ≫ sP) ι).base) := by
      rw [← topologicalKrullDim_image_eq_of_isEmbedding
        (familyBaseChange sP U.ι).isOpenEmbedding.isEmbedding]
      refine topologicalKrullDim_le_of_subset ?_
      intro q hq
      obtain ⟨y, hy⟩ := hq
      have hqU : q ∈ Set.range (familyBaseChange sP U.ι).base := by
        rw [range_familyBaseChange, Set.mem_preimage, ← hy]
        exact ⟨ι.base y, hyU y⟩
      obtain ⟨q', rfl⟩ := hqU
      refine ⟨q', ?_, rfl⟩
      rw [range_familyBaseChange, Set.mem_preimage]
      refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
      rw [hyU, ← hfst]
      exact hy
    calc _ ≤ topologicalKrullDim ↥((Cfam : Set (projectiveLineProduct sP)) ∩
          (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹'
            Set.range (j₀ ≫ iX).base) + topologicalKrullDim (projectiveLineProduct sP) :=
          add_le_add hA hQ'.le
      _ ≤ _ := hfam
      _ ≤ _ := by
          rw [hdimCfam, hdimg']
          exact add_le_add le_rfl hB
  obtain ⟨⟨α', hα'⟩, ⟨β', hβ'⟩, hall⟩ :=
    intersectionProduct_zeroFibre_eq_properPushforward_zeroSection k (U.ι ≫ sP) ι hY hUreg n N c
      hdY hdU (integralComponentAt g') hC' h1 h2 h3
  obtain ⟨hβprop, hαeq⟩ := hall α' β' hα' hβ'
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isRegular hUreg
  have hQ := isRegular_projectiveLineProduct (ι ≫ U.ι ≫ sP) hY
  have : IsLocallyNoetherian (projectiveLineProduct (ι ≫ U.ι ≫ sP)) :=
    isLocallyNoetherian_of_isRegular hQ
  have hQU := isRegular_projectiveLineProduct (U.ι ≫ sP) hUreg
  have : IsLocallyNoetherian (projectiveLineProduct (U.ι ≫ sP)) :=
    isLocallyNoetherian_of_isRegular hQU
  have h₀ := not_range_subset_zeroSection_of_intersectProperly k (ι ≫ U.ι ≫ sP) hdY _ β' hβprop
  have : IsVariety k
      ((ι ≫ U.ι ≫ sP) ≫ eqToHom (rfl : (fieldChowSituation k).S = Spec (.of k))) := by
    simpa using ‹IsVariety k (ι ≫ U.ι ≫ sP)›
  have hmemA := torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension
    (fieldChowSituation k) (ι ≫ U.ι ≫ sP) k rfl hQ ((c : ℤ) + n - N) β' (fun x hx ↦ h₀ x hx)
  obtain ⟨S, hS, hSne⟩ := exists_properPushforward_product_zeroSection_eq_sum k (ι ≫ U.ι ≫ sP) hQ
    _ β' h₀ ⟨_, hmemA⟩ rfl
  obtain ⟨a, ha⟩ : ∃ a : AlgebraicCycle Y ℤ, a = α'.1 := ⟨_, rfl⟩
  have e1 : a = cycleComap ι ι.isClosedEmbedding.injective
      (torFormulaCycleIntersectionProduct (fieldChowSituation k) (U.ι ≫ sP) hUreg
        ((c : ℤ) + n - N) (Function.locallyFinsuppWithin.single c' 1)
        (Function.locallyFinsuppWithin.single (ι.base (genericPoint Y)) 1)) := by
    rw [ha, ← cycleComap_properPushforward (fieldChowSituation k) (U.ι ≫ sP) (ι ≫ U.ι ≫ sP) ι rfl
      _ α', hα', hcyc]
  have e2 : a = ∑ e ∈ S, β'.1 e • (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
      (ι ≫ U.ι ≫ sP) (zeroFiber (ι ≫ U.ι ≫ sP) (integralComponentAt e)).subschemeι
        ((c : ℤ) + n - N)).1 := by
    rw [ha, hαeq]
    exact hS
  obtain ⟨b, hb⟩ : ∃ b : projectiveLineProduct (ι ≫ U.ι ≫ sP) → ℤ, b = fun e ↦ β'.1 e :=
    ⟨_, rfl⟩
  have e2' : a = ∑ e ∈ S, b e • (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
      (ι ≫ U.ι ≫ sP) (zeroFiber (ι ≫ U.ι ≫ sP) (integralComponentAt e)).subschemeι
        ((c : ℤ) + n - N)).1 := by
    rwa [hb]
  rw [hdeg] at e1 e2'
  have mem_cycles : ∀ (z : P) (d : ℕ), relativeDimension
      (fieldChowSituation k).dimensionFunction sP z = d →
      Function.locallyFinsuppWithin.single z (1 : ℤ) ∈
        cyclesOfDimension (fieldChowSituation k) sP (d : ℤ) := by
    intro z d hz
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro x hx
    have : x = z := by
      by_contra hne
      exact hx (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hne])
    rw [this, hz]
  have hrdX : relativeDimension (fieldChowSituation k).dimensionFunction sP
      (iX.base (genericPoint Xb)) = n := by
    have h := topologicalKrullDim_closure_singleton_eq k sP (iX.base (genericPoint Xb))
    rw [hXd] at h
    have h' : n = (relativeDimension (fieldChowSituation k).dimensionFunction sP
      (iX.base (genericPoint Xb))).toNat := by exact_mod_cast h
    have := relativeDimension_fieldChowSituation_nonneg k sP (iX.base (genericPoint Xb))
    omega
  have hres := cycleComap_torFormulaCycleIntersectionProduct_of_isOpenImmersion k sP (U.ι ≫ sP) hP
    hUreg U.ι rfl N c n s hPd (by rw [hdU, hPd]) hrs ⟨_, mem_cycles _ c hc⟩
    ⟨_, mem_cycles _ n hrdX⟩ hCprop
  dsimp only at hres
  have hsc : cycleComap U.ι U.ι.isOpenEmbedding.injective
      (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint 1) =
      Function.locallyFinsuppWithin.single c' 1 := by
    rw [← hc']; exact cycleComap_single _ _ _
  have hsw : cycleComap U.ι U.ι.isOpenEmbedding.injective
      (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) 1) =
      Function.locallyFinsuppWithin.single (ι.base (genericPoint Y)) 1 := by
    rw [← hgenY]; exact cycleComap_single _ _ _
  rw [hsc, hsw] at hres
  have hinj : Function.Injective (j₀ ≫ iX).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact iX.isClosedEmbedding.injective.comp j₀.isOpenEmbedding.injective
  have e3 : cycleComap j₀ j₀.isOpenEmbedding.injective (cycleComap iX iX.isClosedEmbedding.injective
      (torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP (s : ℤ)
        (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint 1)
        (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) 1))) = a := by
    rw [e1, ← hres, cycleComap_cycleComap ι _ U.ι _ (j₀ ≫ iX) hinj hι,
      cycleComap_cycleComap j₀ _ iX _ (j₀ ≫ iX) hinj rfl]
  refine ⟨S, b, e3.trans e2', fun e he ↦ ?_⟩
  have hbne : β'.1 e ≠ 0 := hSne e he
  have hdQ' : topologicalKrullDim (projectiveLineProduct (U.ι ≫ sP)) =
      ((N + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_projectiveLineProduct, hdU]; norm_cast
  have hψe : (familyBaseChange (U.ι ≫ sP) ι).base e ∈
      closure ({g'} : Set (projectiveLineProduct (U.ι ≫ sP))) := by
    have hval := congrArg (fun f : AlgebraicCycle (projectiveLineProduct (U.ι ≫ sP)) ℤ ↦
      f ((familyBaseChange (U.ι ≫ sP) ι).base e)) hβ'
    simp only at hval
    rw [properPushforward_apply_image_of_isClosedImmersion] at hval
    rw [hval] at hbne
    have hm := mem_inter_of_torFormula_single_single_ne_zero k
      (pullback.fst (U.ι ≫ sP) (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ U.ι ≫ sP)
      hQU hdQ' _ _ _ _ hbne
    have hgen : (integralComponentAt g').subschemeι.base
        (genericPoint (integralComponentAt g').subscheme) = g' :=
      genericPointOf_integralComponentAt g'
    rw [hgen] at hm
    exact hm.1.1
  have hspec : ∀ w ∈ closure ({e} : Set (projectiveLineProduct (ι ≫ U.ι ≫ sP))),
      (familyBaseChange sP U.ι).base ((familyBaseChange (U.ι ≫ sP) ι).base w) ∈
        (Cfam : Set (projectiveLineProduct sP)) := fun w hw ↦ by
    have hsp := (((specializes_iff_mem_closure.mpr hψe).trans
      ((specializes_iff_mem_closure.mpr hw).map
        (familyBaseChange (U.ι ≫ sP) ι).continuous)).map (familyBaseChange sP U.ι).continuous)
    rwa [hg', specializes_iff_mem_closure,
      Cfam.isIrreducible.closure_genericPoint Cfam.isClosed'] at hsp
  refine ⟨?_, h₀ e hbne, ?_, ?_⟩
  · have h := (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) _ _ β'.1).mp β'.2 e
      hbne
    rwa [hdeg] at h
  · intro y hy
    rw [coe_support_zeroFiber, Set.mem_preimage, coe_support_integralComponentAt] at hy
    have hz : ∀ {A B : Scheme.{u}} (f : B ⟶ Spec (.of k)) (i : A ⟶ B) a,
        (familyBaseChange f i).base ((zeroSection (i ≫ f)).base a) =
          (zeroSection f).base (i.base a) := fun f i a ↦ by
      rw [← Scheme.Hom.comp_apply, zeroSection_comp_familyBaseChange, Scheme.Hom.comp_apply]
    have hsp := hspec _ hy
    rw [hz, hz, hyU] at hsp
    exact (hzsupp _).mp hsp
  · intro y hy
    rw [coe_support_infinityFiber, Set.mem_preimage, coe_support_integralComponentAt] at hy
    have hz : ∀ {A B : Scheme.{u}} (f : B ⟶ Spec (.of k)) (i : A ⟶ B) a,
        (familyBaseChange f i).base ((infinitySection (i ≫ f)).base a) =
          (infinitySection f).base (i.base a) := fun f i a ↦ by
      rw [← Scheme.Hom.comp_apply, infinitySection_comp_familyBaseChange, Scheme.Hom.comp_apply]
    have hsp := hspec _ hy
    rwa [hz, hz, hyU] at hsp

end Stacks.Intersection.RationalEquivalenceProduct

end

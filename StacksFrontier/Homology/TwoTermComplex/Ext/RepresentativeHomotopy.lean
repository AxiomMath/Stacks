module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Order.SuccPred.Int
public import Mathlib.Tactic.LinearCombination
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.Homology.TwoTermComplex.Ext.DerivedHom
public import StacksFrontier.Homology.TwoTermComplex.ProjRes
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- `homologyMap_eq_of_Q_map_eq` closes with `simpa`, which has to identify the homology
-- functor's value at a complex with `HomologicalComplex.homology` itself.
set_option backward.isDefEq.respectTransparency false

/-
# Stacks 0ALN (4): two representatives of one derived morphism differ by a homotopy

This is part (4) of Stacks project Lemma 15.86.4, tag 0ALN ("Two term complexes",
section 15.86 of *More on Algebra*). The setting, the notation and the objects used here
are those of `StacksFrontier.Homology.TwoTermComplex.Ext.DerivedHom`, and the situation is
the one of part (3), `StacksFrontier.Homology.TwoTermComplex.Ext.ChainRepresentative`.

## Main Statements

Hypotheses common to all parts: `M` is a complex with `M^i = 0` for `i > 0`
and with `M^0` projective. `K` is a second complex.

* `exists_homotopy_components_of_Q_map_eq` is **(4)**: assume `K^i = 0` for `i ≤ -3` and let
  `a^•, (a')^• : M → K` both represent `α ∈ Hom_{D(R)}(M, K)` and agree with
  `a : M^{-2} → K^{-2}` in degree `-2`. Then there are `h^0 : M^0 → K^{-1}` and
  `h^{-1} : M^{-1} → K^{-2}` with `h^{-1} ∘ d_M^{-2} = 0`,
  `(a')^{-1} = a^{-1} + d_K^{-2} ∘ h^{-1} + h^0 ∘ d_M^{-1}` and
  `(a')^0 = a^0 + d_K^{-1} ∘ h^0`.

The two steps are to produce a homotopy and then to read off its components.
`nonempty_homotopy_of_Q_map_eq` produces one: over a projective resolution the two
representatives are homotopic because `F` is K-projective, and that homotopy descends by
`nonempty_homotopy_of_comp_projRes_homotopy`, whose hypothesis on cycles in degree `-2` is
`f_neg_two_apply_eq_of_Q_map_eq`. `exists_homotopy_components_of_homotopy` then rearranges
`Homotopy.comm` into the three displayed relations.
-/

open CategoryTheory Limits

namespace TwoTermComplexExt

universe u v

variable {R : Type u} [Ring R] [Small.{v} R]
  [HasDerivedCategory (ModuleCat.{v} R)]

variable (M K : CochainComplex (ModuleCat.{v} R) ℤ)

/-- The homotopy relation in degree `-2`, when the target vanishes in degree `-3`. -/
private lemma homotopy_comm_neg_two {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (H : Homotopy f g) (hL : IsZero (L.X (-3))) :
    f.f (-2) = K.d (-2) (-1) ≫ H.hom (-1) (-2) + g.f (-2) := by
  have c := H.comm (-2)
  rwa [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp [ComplexShape.up_Rel]),
    prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-3) (-2) by simp [ComplexShape.up_Rel]),
    hL.eq_zero_of_src (L.d (-3) (-2)), Limits.comp_zero, add_zero] at c

/-- The homotopy relation in degree `-1`. -/
private lemma homotopy_comm_neg_one {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (H : Homotopy f g) :
    f.f (-1) = K.d (-1) 0 ≫ H.hom 0 (-1) + H.hom (-1) (-2) ≫ L.d (-2) (-1) + g.f (-1) := by
  have c := H.comm (-1)
  rwa [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp [ComplexShape.up_Rel]),
    prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp [ComplexShape.up_Rel])] at c

/-- The homotopy relation in degree `0`, when the source has `d 0 1 = 0`. -/
private lemma homotopy_comm_zero {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (H : Homotopy f g) (hK : K.d 0 1 = 0) :
    f.f 0 = H.hom 0 (-1) ≫ L.d (-1) 0 + g.f 0 := by
  have c := H.comm 0
  rwa [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp [ComplexShape.up_Rel]),
    prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp [ComplexShape.up_Rel]),
    hK, Limits.zero_comp, zero_add] at c

omit [Small.{v, u} R] in
/-- If `Q.map ab = Q.map ab'` then they induce the same map on homology in each
degree (via `DerivedCategory.homologyFunctorFactors`). -/
private lemma homologyMap_eq_of_Q_map_eq (ab ab' : M ⟶ K) (n : ℤ)
    (h : DerivedCategory.Q.map ab = DerivedCategory.Q.map ab') :
    HomologicalComplex.homologyMap ab n = HomologicalComplex.homologyMap ab' n := by
  have e := DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n
  have key : (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).map ab
      = (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).map ab' := by
    have h1 := e.hom.naturality ab
    have h2 := e.hom.naturality ab'
    have hq : (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map ab
        = (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map ab' := by
      simp only [Functor.comp_map]; rw [h]
    rw [hq] at h1; rw [h1] at h2
    exact (cancel_epi (e.hom.app M)).mp h2
  simpa using key

omit [Small.{v, u} R] in
/-- For an `M`-cycle `m` at degree `-2`, two morphisms `ab, ab'` with
`Q.map ab = Q.map ab'` agree on `m` (using `K^{-3} = 0`). They induce the same map
on `H^{-2}`, so `ab^{-2}m - (ab')^{-2}m` is a boundary in `K`, which vanishes since
`K^{-3} = 0`. -/
private lemma f_neg_two_apply_eq_of_Q_map_eq (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i))
    (ab ab' : M ⟶ K) (h : DerivedCategory.Q.map ab = DerivedCategory.Q.map ab')
    (m : M.X (-2)) (hm : M.d (-2) (-1) m = 0) :
    (HomologicalComplex.Hom.f ab (-2)) m = (HomologicalComplex.Hom.f ab' (-2)) m := by
  classical
  have hMap : HomologicalComplex.homologyMap ab (-2) = HomologicalComplex.homologyMap ab' (-2) :=
    homologyMap_eq_of_Q_map_eq M K ab ab' (-2) h
  have hnext : (ComplexShape.up ℤ).next (-2) = (-1) := by simp
  have hm' : (ConcreteCategory.hom ((forget₂ (ModuleCat.{v} R) Ab).map (M.d (-2) (-1)))) m = 0 := hm
  let mc : M.cycles (-2) := M.cyclesMk m (-1) hnext hm'
  have hmc : M.iCycles (-2) mc = m := M.i_cyclesMk m (-1) hnext hm'
  have hcm : ∀ (g : M ⟶ K), K.iCycles (-2) (HomologicalComplex.cyclesMap g (-2) mc)
      = HomologicalComplex.Hom.f g (-2) (M.iCycles (-2) mc) := by
    intro g
    have hh := HomologicalComplex.cyclesMap_i g (-2)
    have h2 : (HomologicalComplex.cyclesMap g (-2) ≫ K.iCycles (-2)) mc
        = (M.iCycles (-2) ≫ HomologicalComplex.Hom.f g (-2)) mc := by rw [hh]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h2; exact h2
  have hnat : ∀ (g : M ⟶ K), K.homologyπ (-2) (HomologicalComplex.cyclesMap g (-2) mc)
      = HomologicalComplex.homologyMap g (-2) (M.homologyπ (-2) mc) := by
    intro g
    have hn := HomologicalComplex.homologyπ_naturality g (-2)
    have h2 : (M.homologyπ (-2) ≫ HomologicalComplex.homologyMap g (-2)) mc
        = (HomologicalComplex.cyclesMap g (-2) ≫ K.homologyπ (-2)) mc := by rw [hn]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h2; exact h2.symm
  have hsame : K.homologyπ (-2) (HomologicalComplex.cyclesMap ab (-2) mc)
      = K.homologyπ (-2) (HomologicalComplex.cyclesMap ab' (-2) mc) := by
    rw [hnat ab, hnat ab', hMap]
  have hprev : (ComplexShape.up ℤ).prev (-2) = (-3) := by simp
  have hdiff0 : K.homologyπ (-2) (HomologicalComplex.cyclesMap ab (-2) mc
      - HomologicalComplex.cyclesMap ab' (-2) mc) = 0 := by
    rw [map_sub, hsame, sub_self]
  obtain ⟨w, hw⟩ := exists_toCycles_eq_of_homologyπ_eq_zero K hprev _ hdiff0
  have hicyc : K.iCycles (-2) (K.toCycles (-3) (-2) w) = K.d (-3) (-2) w := by
    have h2 : (K.toCycles (-3) (-2) ≫ K.iCycles (-2)) w = K.d (-3) (-2) w := by
      rw [K.toCycles_i (-3) (-2)]
    rw [ModuleCat.comp_apply] at h2; exact h2
  have hKd : K.d (-3) (-2) = 0 := (hK (-3) le_rfl).eq_zero_of_src _
  have hdiffval : K.iCycles (-2) (HomologicalComplex.cyclesMap ab (-2) mc
        - HomologicalComplex.cyclesMap ab' (-2) mc)
      = (HomologicalComplex.Hom.f ab (-2)) m - (HomologicalComplex.Hom.f ab' (-2)) m := by
    rw [map_sub, hcm ab, hcm ab', hmc]
  rw [← hw] at hdiffval
  rw [hicyc, hKd] at hdiffval
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at hdiffval
  rw [← sub_eq_zero, ← hdiffval]

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- **Descent of the homotopy for (4).** Given a homotopy `H : Homotopy (P.p ≫ ab)
(P.p ≫ ab')` and the cycle-agreement of `ab, ab'`, descend `H` through the termwise
surjections `p^i` to a homotopy `ab ≃ ab'`. Two homotopy components survive:
`h^0 : M^0 → K^{-1}` (along `F^0 = M^0`) and `h^{-1} : M^{-1} → K^{-2}` (factoring
`H.hom (-1) (-2)` through the epi `p^{-1}`). -/
private lemma nonempty_homotopy_of_comp_projRes_homotopy (P : ProjRes M)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i)) (ab ab' : M ⟶ K)
    (abeq : ∀ (m : M.X (-2)), M.d (-2) (-1) m = 0 →
        (HomologicalComplex.Hom.f ab (-2)) m = (HomologicalComplex.Hom.f ab' (-2)) m)
    (H : Homotopy (P.p ≫ ab) (P.p ≫ ab')) :
    Nonempty (Homotopy ab ab') := by
  classical
  have := P.strictLE
  have := P.qis
  have hp0 : HomologicalComplex.Hom.f P.p 0 = eqToHom P.X0 := P.p0
  have hep1 : Epi (HomologicalComplex.Hom.f P.p (-1)) := P.epi (-1)
  have hiso : IsIso (HomologicalComplex.homologyMap P.p (-1)) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance
  have hpsurj : Function.Surjective (HomologicalComplex.Hom.f P.p (-1)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hrelm10 : (ComplexShape.up ℤ).Rel (-1) 0 := by simp [ComplexShape.up_Rel]
  have hrelm2m1 : (ComplexShape.up ℤ).Rel (-2) (-1) := by simp [ComplexShape.up_Rel]
  have hrelm3m2 : (ComplexShape.up ℤ).Rel (-3) (-2) := by simp [ComplexShape.up_Rel]
  have hrel01 : (ComplexShape.up ℤ).Rel 0 1 := by simp [ComplexShape.up_Rel]
  -- the descended component `h0 : M^0 → K^{-1}`.
  set h0 : M.X 0 ⟶ K.X (-1) := eqToHom P.X0.symm ≫ H.hom 0 (-1) with hh0def
  -- relation from `H.comm (-2)`.
  have hcomm2 : P.F.d (-2) (-1) ≫ H.hom (-1) (-2)
      = HomologicalComplex.Hom.f (P.p ≫ ab) (-2)
        - HomologicalComplex.Hom.f (P.p ≫ ab') (-2) := by
    rw [homotopy_comm_neg_two H (hK (-3) le_rfl)]; abel
  -- KILL PROPERTY: `H.hom (-1) (-2)` annihilates `ker (p.f (-1))`.
  have hkill : ∀ x : P.F.X (-1), (HomologicalComplex.Hom.f P.p (-1)) x = 0 →
      (H.hom (-1) (-2)) x = 0 := by
    intro x hx
    have hcyc : P.F.d (-1) 0 x = 0 := by
      have hmono : Function.Injective (HomologicalComplex.Hom.f P.p 0) := by
        have : IsIso (HomologicalComplex.Hom.f P.p 0) := by rw [hp0]; infer_instance
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      apply hmono
      have hcomm := HomologicalComplex.Hom.comm P.p (-1) 0
      have hcc : (HomologicalComplex.Hom.f P.p (-1) ≫ M.d (-1) 0) x
          = (P.F.d (-1) 0 ≫ HomologicalComplex.Hom.f P.p 0) x := by rw [hcomm]
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hcc
      rw [map_zero, ← hcc, hx, map_zero]
    obtain ⟨b, hb0⟩ := exists_d_apply_eq_of_isIso_homologyMap P.p (-1) x hcyc 0 (by rw [hx]; simp)
    have hb : P.F.d (-2) (-1) b = x := hb0
    set m := (HomologicalComplex.Hom.f P.p (-2)) b with hmdef
    have hmcyc : M.d (-2) (-1) m = 0 := by
      have hpc := HomologicalComplex.Hom.comm P.p (-2) (-1)
      have hcc : (HomologicalComplex.Hom.f P.p (-2) ≫ M.d (-2) (-1)) b
          = (P.F.d (-2) (-1) ≫ HomologicalComplex.Hom.f P.p (-1)) b := by rw [hpc]
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hcc
      rw [hmdef, hcc, hb, hx]
    rw [← hb]
    have e1 : (H.hom (-1) (-2)) (P.F.d (-2) (-1) b)
        = (P.F.d (-2) (-1) ≫ H.hom (-1) (-2)) b := by rw [ModuleCat.comp_apply]
    rw [e1, hcomm2, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ← hmdef,
        abeq m hmcyc, sub_self]
  -- the descended component `hm1 : M^{-1} → K^{-2}`.
  obtain ⟨hm1, hhm1⟩ := exists_comp_eq_of_apply_eq_zero (HomologicalComplex.Hom.f P.p (-1))
    (H.hom (-1) (-2)) hpsurj hkill
  -- the homotopy datum: nonzero only at `(0,-1)` and `(-1,-2)`.
  let homf : ∀ i j, M.X i ⟶ K.X j := fun i j =>
    if hi : i = 0 then (if hj : j = -1 then eqToHom (by rw [hi]) ≫ h0 ≫ eqToHom (by rw [hj])
      else 0)
    else if hi1 : i = -1 then (if hj : j = -2 then eqToHom (by rw [hi1]) ≫ hm1 ≫ eqToHom (by rw
        [hj])
      else 0)
    else 0
  have homf0 : homf 0 (-1) = h0 := by simp [homf]
  have homfm1 : homf (-1) (-2) = hm1 := by simp [homf]
  -- degree 0 relation.
  have hd0 : HomologicalComplex.Hom.f ab 0 = h0 ≫ K.d (-1) 0 + HomologicalComplex.Hom.f ab' 0 := by
    have hFX1 : IsZero (P.F.X 1) := CochainComplex.isZero_of_isStrictlyLE P.F 0 1 (by omega)
    have c := homotopy_comm_zero H (hFX1.eq_zero_of_tgt _)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hp0] at c
    have c2 := congrArg (fun t => eqToHom P.X0.symm ≫ t) c
    simp only [Preadditive.comp_add] at c2
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc] at c2
    simp only [eqToHom_trans, eqToHom_refl, Category.id_comp] at c2
    rw [hh0def]
    exact c2
  -- degree -1 relation.
  have hdm1 : HomologicalComplex.Hom.f ab (-1)
      = M.d (-1) 0 ≫ h0 + hm1 ≫ K.d (-2) (-1) + HomologicalComplex.Hom.f ab' (-1) := by
    apply (cancel_epi (HomologicalComplex.Hom.f P.p (-1))).mp
    have c := homotopy_comm_neg_one H
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at c
    -- c : p.f(-1) ≫ ab.f(-1) = F.d(-1)0 ≫ H.hom 0 (-1) + H.hom(-1)(-2) ≫ K.d(-2)(-1)
    --     + p.f(-1) ≫ ab'.f(-1)
    rw [Preadditive.comp_add, Preadditive.comp_add]
    rw [c]
    congr 1
    congr 1
    · -- p.f(-1) ≫ M.d(-1)0 ≫ h0 = F.d(-1)0 ≫ H.hom 0 (-1)
      have hpc := HomologicalComplex.Hom.comm P.p (-1) 0
      rw [← Category.assoc, hpc, Category.assoc, hh0def, hp0, ← Category.assoc,
          ← Category.assoc]
      simp
    · -- p.f(-1) ≫ hm1 ≫ K.d(-2)(-1) = H.hom(-1)(-2) ≫ K.d(-2)(-1)
      rw [← Category.assoc, hhm1]
  -- degree -2 relation.
  have hdm2 : HomologicalComplex.Hom.f ab (-2)
      = M.d (-2) (-1) ≫ hm1 + HomologicalComplex.Hom.f ab' (-2) := by
    have : Epi (HomologicalComplex.Hom.f P.p (-2)) := P.epi (-2)
    apply (cancel_epi (HomologicalComplex.Hom.f P.p (-2))).mp
    rw [Preadditive.comp_add]
    -- p.f(-2) ≫ ab.f(-2) - p.f(-2) ≫ ab'.f(-2) = F.d(-2)(-1) ≫ H.hom(-1)(-2)
    have hc2 : HomologicalComplex.Hom.f P.p (-2) ≫ HomologicalComplex.Hom.f ab (-2)
        = P.F.d (-2) (-1) ≫ H.hom (-1) (-2)
          + HomologicalComplex.Hom.f P.p (-2) ≫ HomologicalComplex.Hom.f ab' (-2) := by
      have := hcomm2
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at this
      rw [this]; abel
    rw [hc2]
    congr 1
    -- p.f(-2) ≫ M.d(-2)(-1) ≫ hm1 = F.d(-2)(-1) ≫ H.hom(-1)(-2)
    have hpc := HomologicalComplex.Hom.comm P.p (-2) (-1)
    rw [← Category.assoc, hpc, Category.assoc, hhm1]
  -- assemble the homotopy.
  refine ⟨{ hom := homf, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    simp only [homf]
    split <;> rename_i hi
    · split <;> rename_i hj
      · exfalso; apply hij; subst hi; subst hj; simp [ComplexShape.up_Rel]
      · rfl
    · split <;> rename_i hi1
      · split <;> rename_i hj
        · exfalso; apply hij; subst hi1; subst hj; simp [ComplexShape.up_Rel]
        · rfl
      · rfl
  · intro i
    by_cases hi0 : i = 0
    · subst hi0
      rw [dNext_eq homf hrel01, prevD_eq homf hrelm10, homf0]
      have hz : homf 1 0 = 0 := by simp [homf]
      rw [hz, Limits.comp_zero, zero_add, hd0]
    · by_cases him1 : i = -1
      · subst him1
        rw [dNext_eq homf hrelm10, prevD_eq homf hrelm2m1, homf0, homfm1]
        rw [hdm1]
      · by_cases him2 : i = -2
        · subst him2
          rw [dNext_eq homf hrelm2m1, prevD_eq homf hrelm3m2, homfm1]
          have hz : homf (-2) (-3) = 0 := by simp [homf]
          rw [hz, Limits.zero_comp, add_zero, hdm2]
        · rw [dNext_eq homf
                (show (ComplexShape.up ℤ).Rel i (i+1) from by simp [ComplexShape.up_Rel]),
              prevD_eq homf
                (show (ComplexShape.up ℤ).Rel (i-1) i from by simp [ComplexShape.up_Rel])]
          have hzd : homf (i+1) i = 0 := by
            simp only [homf]
            rw [dite_eq_right (by omega : ¬ i + 1 = 0), dite_eq_right (by omega : ¬ i + 1 = -1)]
          have hzp : homf i (i-1) = 0 := by
            simp only [homf]
            by_cases hi : i = 0
            · rw [dite_eq_left hi, dite_eq_right (by omega : ¬ i - 1 = -1)]
            · rw [dite_eq_right hi]
              by_cases hi1 : i = -1
              · rw [dite_eq_left hi1, dite_eq_right (by omega : ¬ i - 1 = -2)]
              · rw [dite_eq_right hi1]
          rw [hzd, hzp, Limits.comp_zero, Limits.zero_comp, zero_add, zero_add]
          by_cases hile : i ≤ -3
          · have hKi : IsZero (K.X i) := hK i hile
            rw [hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f ab i),
                hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f ab' i)]
          · have hMi : IsZero (M.X i) := hM_pos i (by omega)
            rw [hMi.eq_zero_of_src (HomologicalComplex.Hom.f ab i),
                hMi.eq_zero_of_src (HomologicalComplex.Hom.f ab' i)]

/-- **Sub-lemma for (4): the two representatives are homotopic.**
Under the hypotheses of (4), `ab` and `ab'` are chain-homotopic: there is a
`Homotopy ab ab'`.

INFORMAL ARGUMENT (Stacks 0ALN, proof of (4), hint): `Q.map ab = α = Q.map ab'`.
There is a projective resolution `p : F → M`; then `ab ∘ p` and `ab' ∘ p` both
represent `Q.map p ≫ α` and `F` is K-projective, so by
`CochainComplex.IsKProjective.Qh_map_bijective` (injectivity on homotopy classes)
`ab ∘ p` and `ab' ∘ p` are chain-homotopic. As in (1)/(3) this homotopy factors
through `p` (its components `F^i → K^{i-1}` descend along the surjections `p^i`,
using `F^0 = M^0`), yielding a homotopy between `ab` and `ab'` directly.
Equivalently: `M` itself need not be K-projective, but the homotopy descent gives
`Nonempty (Homotopy ab ab')`. -/
theorem nonempty_homotopy_of_Q_map_eq
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i))
    {α : HomD M K}
    (ab ab' : M ⟶ K)
    (hab : DerivedCategory.Q.map ab = α) (hab' : DerivedCategory.Q.map ab' = α) :
    Nonempty (Homotopy ab ab') := by
  -- `ab∘p ≃ ab'∘p` (K-projective F, injectivity of `Qh.map`); descend the homotopy
  -- through `p` to a homotopy `ab ≃ ab'`.
  obtain ⟨P⟩ := exists_projRes M hM_pos hM0
  have : P.F.IsKProjective := P.isKProjective
  have habab' : DerivedCategory.Q.map ab = DerivedCategory.Q.map ab' := by rw [hab, hab']
  -- the composites `P.p ≫ ab` and `P.p ≫ ab'` are equal in `D(R)`.
  have heqQ : DerivedCategory.Q.map (P.p ≫ ab) = DerivedCategory.Q.map (P.p ≫ ab') := by
    rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, habab']
  -- `F` is K-projective ⟹ `Qh.map` is injective; translate to equality of homotopy classes.
  have hbij : Function.Bijective (fun g : HomK P.F K => (toHomD g : HomD P.F K)) :=
    toHomD_bijective_of_Qh (CochainComplex.IsKProjective.Qh_map_bijective P.F
      ((HomotopyCategory.quotient _ _).obj K))
  have hcl : (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map (P.p ≫ ab)
      = (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map (P.p ≫ ab') :=
    hbij.injective ((toHomD_quotient_map (P.p ≫ ab)).trans
      (heqQ.trans (toHomD_quotient_map (P.p ≫ ab')).symm))
  have H : Homotopy (P.p ≫ ab) (P.p ≫ ab') := HomotopyCategory.homotopyOfEq _ _ hcl
  -- cycle-agreement of `ab, ab'` (using `K^{-3} = 0`), then descend the homotopy.
  have abeq : ∀ (m : M.X (-2)), M.d (-2) (-1) m = 0 →
      (HomologicalComplex.Hom.f ab (-2)) m = (HomologicalComplex.Hom.f ab' (-2)) m :=
    fun m hm => f_neg_two_apply_eq_of_Q_map_eq M K hK ab ab' habab' m hm
  exact nonempty_homotopy_of_comp_projRes_homotopy M K P hM_pos hK ab ab' abeq H

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- **Sub-lemma for (4): read off the homotopy data.**
Given a homotopy `H : Homotopy ab ab'` and `ab^{-2} = ab'^{-2} = a`, the homotopy
components `h^0 := H.hom 0 (-1)` and `h^{-1} := H.hom (-1) (-2)` satisfy the three
displayed relations.

INFORMAL ARGUMENT: The homotopy relation in degree `i` reads
`ab^i - ab'^i = d_M^i ∘ H.hom (i+1) i + H.hom i (i-1) ∘ d_K^{i-1}` (signs/orientation
per Mathlib's `Homotopy.comm`, with `dNext`/`prevD`). In degree `-2`,
`ab^{-2} = ab'^{-2}` forces `d_M^{-2} ∘ h^{-1} = 0` after using that the incoming
term `H.hom (-2) (-3) ∘ d_K^{-3} = 0` (since `K^{-3} = 0`). In degree `-1` and `0`,
unwinding `dNext`/`prevD` against the two-term shape of `M` (`M^i = 0` for `i > 0`)
and of `K` (`K^i = 0` for `i ≤ -3`) gives exactly
`(a')^{-1} = a^{-1} + d_K^{-2} ∘ h^{-1} + h^0 ∘ d_M^{-1}` and
`(a')^0 = a^0 + d_K^{-1} ∘ h^0`. (This is pure rearrangement of `Homotopy.comm`.) -/
theorem exists_homotopy_components_of_homotopy
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i))
    {a : M.X (-2) ⟶ K.X (-2)}
    (ab ab' : M ⟶ K)
    (hab_2 : HomologicalComplex.Hom.f ab (-2) = a)
    (hab'_2 : HomologicalComplex.Hom.f ab' (-2) = a)
    (H : Homotopy ab ab') :
    ∃ (h0 : M.X 0 ⟶ K.X (-1)) (hm1 : M.X (-1) ⟶ K.X (-2)),
      M.d (-2) (-1) ≫ hm1 = 0 ∧
      HomologicalComplex.Hom.f ab' (-1) =
        HomologicalComplex.Hom.f ab (-1) + hm1 ≫ K.d (-2) (-1) + M.d (-1) 0 ≫ h0 ∧
      HomologicalComplex.Hom.f ab' 0 =
        HomologicalComplex.Hom.f ab 0 + h0 ≫ K.d (-1) 0 := by
  refine ⟨-(H.hom 0 (-1)), -(H.hom (-1) (-2)), ?_, ?_, ?_⟩
  · -- conjunct 1: M.d (-2) (-1) ≫ hm1 = 0
    have c := homotopy_comm_neg_two H (hK (-3) le_rfl)
    rw [hab_2, hab'_2] at c
    -- c : a = M.d (-2) (-1) ≫ H.hom (-1) (-2) + a
    have hd : M.d (-2) (-1) ≫ H.hom (-1) (-2) = 0 :=
      add_right_cancel (b := a) (by rw [zero_add]; exact c.symm)
    rw [Preadditive.comp_neg, hd, neg_zero]
  · -- conjunct 2
    have c := homotopy_comm_neg_one H
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    linear_combination (norm := abel) -c
  · -- conjunct 3
    have c := homotopy_comm_zero H ((hM_pos 1 one_pos).eq_zero_of_tgt _)
    simp only [Preadditive.neg_comp]
    linear_combination (norm := abel) -c

/-- **(4)** In the situation of (3): given `α` and a representing morphism of complexes
`a^•` with `a^{-2} = a` (as produced in (3)), for any second representing morphism
of complexes `(a')^•` with `(a')^{-2} = a`, there exist `R`-module homomorphisms
`h^0 : M^0 → K^{-1}` and `h^{-1} : M^{-1} → K^{-2}` such that
`h^{-1} ∘ d_M^{-2} = 0`, `(a')^{-1} = a^{-1} + d_K^{-2} ∘ h^{-1} + h^0 ∘ d_M^{-1}`,
and `(a')^0 = a^0 + d_K^{-1} ∘ h^0`.

PROOF SKETCH (Stacks 0ALN, proof of (4)): `ab` and `ab'` both represent `α`, so by
`nonempty_homotopy_of_Q_map_eq` they are chain-homotopic; pick a homotopy `H`.
Feed `H` (and the degree-`-2` agreement) to
`exists_homotopy_components_of_homotopy` to obtain `h^0, h^{-1}` and the three
relations. -/
@[stacks 0ALN "(4)"]
theorem exists_homotopy_components_of_Q_map_eq
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i))
    (α : HomD M K)
    (a : M.X (-2) ⟶ K.X (-2))
    (ab ab' : M ⟶ K)
    (hab : DerivedCategory.Q.map ab = α) (hab' : DerivedCategory.Q.map ab' = α)
    (hab_2 : HomologicalComplex.Hom.f ab (-2) = a)
    (hab'_2 : HomologicalComplex.Hom.f ab' (-2) = a) :
    ∃ (h0 : M.X 0 ⟶ K.X (-1)) (hm1 : M.X (-1) ⟶ K.X (-2)),
      M.d (-2) (-1) ≫ hm1 = 0 ∧
      HomologicalComplex.Hom.f ab' (-1) =
        HomologicalComplex.Hom.f ab (-1) + hm1 ≫ K.d (-2) (-1) + M.d (-1) 0 ≫ h0 ∧
      HomologicalComplex.Hom.f ab' 0 =
        HomologicalComplex.Hom.f ab 0 + h0 ≫ K.d (-1) 0 := by
  obtain ⟨H⟩ := nonempty_homotopy_of_Q_map_eq M K hM_pos hM0 hK ab ab' hab hab'
  exact exists_homotopy_components_of_homotopy M K hM_pos hK ab ab' hab_2 hab'_2 H

end TwoTermComplexExt

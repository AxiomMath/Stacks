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

/-
# Stacks 0ALN (3): representing a derived morphism by a morphism of complexes

This is part (3) of Stacks project Lemma 15.86.4, tag 0ALN ("Two term complexes",
section 15.86 of *More on Algebra*). The setting, the notation and the objects used here
are those of `StacksFrontier.Homology.TwoTermComplex.Ext.DerivedHom`.

## Main Statements

Hypotheses common to all parts: `M` is a complex with `M^i = 0` for `i > 0`
and with `M^0` projective. `K` is a second complex.

* `exists_hom_Q_map_eq_of_comp_canonical` is **(3)**: assume `K^i = 0` for `i ≤ -3`, and let
  `α ∈ Hom_{D(R)}(M, K)` be such that its composite with the canonical map `K → K^{-2}[2]`
  comes from a module homomorphism `a : M^{-2} → K^{-2}` with `a ∘ d_M^{-3} = 0`. Then `α`
  is represented by a morphism of complexes `a^• : M → K` with `a^{-2} = a`.

The proof passes through a projective resolution `p : F → M` in two steps:
`exists_hom_from_projRes_Q_map_eq` lifts `α` to a morphism of complexes `b : F → K` whose
degree `-2` component is `a ∘ p^{-2}`, and `exists_hom_comp_projRes_eq` descends `b`
through `p`. The cycle-lifting lemma `exists_preimage_of_d_apply_eq_zero` provides the
input for that descent.
-/

open CategoryTheory Limits

namespace TwoTermComplexExt

universe u v

variable {R : Type u} [Ring R] [Small.{v} R]
  [HasDerivedCategory (ModuleCat.{v} R)]

variable (M K : CochainComplex (ModuleCat.{v} R) ℤ)

omit [Small.{v, u} R] in
/-- **Sub-lemma for (3): lift `α` to a chain map from the resolution.**
Under the hypotheses of (3), with `P` a projective resolution of `M`, there is a
morphism of complexes `b : F → K` with `Q.map b = Q.map p ≫ α` (i.e. `b`
represents `α` after the iso `Q.map p`) and `b^{-2} = a ∘ p^{-2}`.

INFORMAL ARGUMENT (Stacks 0ALN, proof of (3), first half): `F` is K-projective and
`Q.map p` is an iso, so `Q.map p ≫ α ∈ Hom_{D(R)}(F, K)` is `Q.map b` for a unique
homotopy class `b : F → K` (`CochainComplex.IsKProjective.Qh_map_bijective`). The
composite of `α` with `K → K^{-2}[2]` is represented by `b^{-2} : F^{-2} → K^{-2}`.
By the hypothesis `hα`, this composite equals (in `D(R)`) the class of `a ∘ p^{-2}`;
both are chain maps `F → K^{-2}[2]` out of the K-projective `F`, so they are
chain-homotopic: there is `h : F^{-1} → K^{-2}` with `b^{-2} = a ∘ p^{-2} +
h ∘ d_F^{-2}` (homotopy in degree `-2`; `K^{-2}[2]` is concentrated in degree `-2`
so the other homotopy term vanishes, using `K^i = 0` for `i ≤ -3`). Replacing `b`
by the homotopic chain map `b - (homotopy by h)` adjusts degree `-2` to exactly
`a ∘ p^{-2}` without changing the `D(R)`-class. -/
theorem exists_hom_from_projRes_Q_map_eq
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i))
    (α : HomD M K)
    (a : M.X (-2) ⟶ K.X (-2))
    (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : α ≫ DerivedCategory.Q.map (canonicalToSingleNegTwo K hK)
        = DerivedCategory.Q.map (mkHomToSingleNegTwo M a ha))
    (P : ProjRes M) :
    ∃ (b : P.F ⟶ K),
      DerivedCategory.Q.map b = DerivedCategory.Q.map P.p ≫ α ∧
      HomologicalComplex.Hom.f b (-2) = HomologicalComplex.Hom.f P.p (-2) ≫ a := by
  classical
  have : P.F.IsKProjective := P.isKProjective
  set Qq := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  -- (A) `Qh.map`, hence `toHomD`, is bijective out of the K-projective `F` into `K`.
  have hbijK : Function.Bijective (fun g : HomK P.F K => (toHomD g : HomD P.F K)) :=
    toHomD_bijective_of_Qh (CochainComplex.IsKProjective.Qh_map_bijective P.F (Qq.obj K))
  -- (1) lift `Q.map P.p ≫ α : HomD F K` to a chain map `b₀ : F → K`.
  obtain ⟨bcl, hbcl⟩ := hbijK.surjective (DerivedCategory.Q.map P.p ≫ α)
  obtain ⟨b0, hb0cl⟩ := Qq.map_surjective bcl
  have hb0Q : DerivedCategory.Q.map b0 = DerivedCategory.Q.map P.p ≫ α := by
    have h1 : toHomD (Qq.map b0) = DerivedCategory.Q.map P.p ≫ α := by
      rw [hb0cl]; exact hbcl
    exact (toHomD_quotient_map b0).symm.trans h1
  -- (2) the two chain maps `F → (single -2).obj (K.X -2)` agree after `Q`.
  set S := (HomologicalComplex.single (ModuleCat.{v} R) (ComplexShape.up ℤ) (-2)).obj (K.X (-2))
  set can := canonicalToSingleNegTwo K hK with hcan
  set mka := mkHomToSingleNegTwo M a ha with hmka
  set c1 : P.F ⟶ S := b0 ≫ can with hc1
  set c2 : P.F ⟶ S := P.p ≫ mka with hc2
  have hQc : DerivedCategory.Q.map c1 = DerivedCategory.Q.map c2 := by
    rw [hc1, hc2, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, hb0Q, hmka, hcan,
      Category.assoc, hα]
  -- (3) hence `c1` and `c2` are chain-homotopic (injectivity of `Qh.map` out of `F`).
  have hbijS : Function.Bijective (fun g : HomK P.F S => (toHomD g : HomD P.F S)) :=
    toHomD_bijective_of_Qh (CochainComplex.IsKProjective.Qh_map_bijective P.F (Qq.obj S))
  have hclEq : Qq.map c1 = Qq.map c2 :=
    hbijS.injective ((toHomD_quotient_map c1).trans (hQc.trans (toHomD_quotient_map c2).symm))
  obtain ⟨H⟩ : Nonempty (Homotopy c1 c2) := ⟨HomotopyCategory.homotopyOfEq _ _ hclEq⟩
  -- (4) extract the degree `-2` equation.
  set ι := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-2) (K.X (-2))).hom with hι
  set h' : P.F.X (-1) ⟶ K.X (-2) := H.hom (-1) (-2) ≫ ι with hh'
  have hrel21 : (ComplexShape.up ℤ).Rel (-3 : ℤ) (-2) := by simp [ComplexShape.up_Rel]
  have hrel10 : (ComplexShape.up ℤ).Rel (-2 : ℤ) (-1) := by simp [ComplexShape.up_Rel]
  have hcomm := H.comm (-2)
  rw [dNext_eq H.hom hrel10, prevD_eq H.hom hrel21] at hcomm
  -- single differential into degree -2 is zero
  have hSd : S.d (-3) (-2) = 0 := HomologicalComplex.single_obj_d _ _ _ _ _
  rw [hSd, Limits.comp_zero, add_zero] at hcomm
  -- compute components after composing with ι
  have hc1f : c1.f (-2) = b0.f (-2) ≫ (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) (-2) (K.X (-2))).inv := by
    rw [hc1, HomologicalComplex.comp_f, hcan, canonicalToSingleNegTwo_f_neg_two]
  have hc2f : c2.f (-2) = P.p.f (-2) ≫ a ≫ (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) (-2) (K.X (-2))).inv := by
    rw [hc2, HomologicalComplex.comp_f, hmka, mkHomToSingleNegTwo_f_neg_two]
  -- the key degree-(-2) identity in K.X(-2)
  have hkey : b0.f (-2) = P.F.d (-2) (-1) ≫ h' + P.p.f (-2) ≫ a := by
    have hcomm' := congrArg (· ≫ ι) hcomm
    rw [hc1f, hc2f] at hcomm'
    -- rewrite each term using ι ∘ inv = id
    have hinvhom : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-2) (K.X (-2))).inv ≫ ι
        = 𝟙 _ := by rw [hι]; exact Iso.inv_hom_id _
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, hinvhom, Category.comp_id,
      Category.assoc, Category.assoc, hinvhom, Category.comp_id] at hcomm'
    -- now hcomm' : b0.f(-2) = (F.d(-2)(-1) ≫ H.hom(-1)(-2)) ≫ ι + P.p.f(-2) ≫ a
    rw [hh', ← Category.assoc]
    exact hcomm'
  -- (5) subtract a null-homotopic map to fix degree -2.
  set hom : (i j : ℤ) → (ComplexShape.up ℤ).Rel j i → (P.F.X i ⟶ K.X j) :=
    fun i j _ => if hij : i = -1 ∧ j = -2 then
        (eqToHom (by rw [hij.left]) ≫ h' ≫ eqToHom (by rw [hij.right])) else 0 with hhom
  set b : P.F ⟶ K := b0 - Homotopy.nullHomotopicMap' hom with hb
  refine ⟨b, ?_, ?_⟩
  · -- Q.map b = Q.map P.p ≫ α
    have hnull : DerivedCategory.Q.map (Homotopy.nullHomotopicMap' hom) = 0 := by
      have hH0 : Qq.map (Homotopy.nullHomotopicMap' hom) = Qq.map 0 :=
        HomotopyCategory.eq_of_homotopy _ _ (Homotopy.nullHomotopy' hom)
      have heq : DerivedCategory.Q.map (Homotopy.nullHomotopicMap' hom)
          = toHomD (Qq.map (Homotopy.nullHomotopicMap' hom)) :=
        (toHomD_quotient_map (Homotopy.nullHomotopicMap' hom)).symm
      rw [heq, hH0, Functor.map_zero, toHomD_zero]
    rw [hb, Functor.map_sub, hnull, sub_zero, hb0Q]
  · -- b.f(-2) = P.p.f(-2) ≫ a
    rw [hb, HomologicalComplex.sub_f_apply]
    have hnf : (Homotopy.nullHomotopicMap' hom).f (-2) = P.F.d (-2) (-1) ≫ h' := by
      rw [Homotopy.nullHomotopicMap'_f hrel21 hrel10 hom]
      have e1 : hom (-1) (-2) hrel10 = h' := by
        rw [hhom]; simp
      have e2 : hom (-2) (-3) hrel21 = 0 := by
        rw [hhom]
        simp only [dite_eq_right (show ¬ ((-2 : ℤ) = -1 ∧ (-3 : ℤ) = -2) by
          rintro ⟨h1, _⟩; norm_num at h1)]
      rw [e1, e2, Limits.zero_comp, add_zero]
    rw [hnf, hkey]
    abel

/-- A morphism of complexes of modules commutes with the differentials elementwise. -/
private theorem d_apply_f_apply {S : Type*} [Ring S] {C D : CochainComplex (ModuleCat.{v} S) ℤ}
    (f : C ⟶ D)
    (i j : ℤ) (x : C.X i) : D.d i j (f.f i x) = f.f j (C.d i j x) :=
  ConcreteCategory.congr_hom (f.comm i j) x

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- **Cycle-lifting along the resolution.** A cycle `m ∈ ker(d_M^{-2})` lifts to a
genuine cycle `z ∈ ker(d_F^{-2})` of the resolving complex with `p^{-2} z = m`.
Proof: `homologyMap p (-2)` is an iso (as `p` is a quasi-iso), so the homology class
of `m` is hit by a class of `F`; lifting that class to a cycle `zc` and correcting by
a boundary `d_F^{-3}(u')` (using surjectivity of `p^{-3}`) produces the desired `z`. -/
private lemma exists_preimage_of_d_apply_eq_zero (P : ProjRes M) (m : M.X (-2))
    (hm : M.d (-2) (-1) m = 0) :
    ∃ z : P.F.X (-2), P.F.d (-2) (-1) z = 0 ∧ (HomologicalComplex.Hom.f P.p (-2)) z = m := by
  classical
  have := P.qis
  have hiso : IsIso (HomologicalComplex.homologyMap P.p (-2)) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance
  have hnext : (ComplexShape.up ℤ).next (-2) = (-1) := by simp
  have hm' : (ConcreteCategory.hom ((forget₂ (ModuleCat.{v} R) Ab).map (M.d (-2) (-1)))) m = 0 := hm
  let mc : M.cycles (-2) := M.cyclesMk m (-1) hnext hm'
  have hmc : M.iCycles (-2) mc = m := M.i_cyclesMk m (-1) hnext hm'
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap P.p (-2)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨h0, hh0⟩ := hsurj (M.homologyπ (-2) mc)
  have hπsurj : Function.Surjective (P.F.homologyπ (-2)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨zc, hzc⟩ := hπsurj h0
  have hnat : P.F.homologyπ (-2) ≫ HomologicalComplex.homologyMap P.p (-2)
      = HomologicalComplex.cyclesMap P.p (-2) ≫ M.homologyπ (-2) :=
    HomologicalComplex.homologyπ_naturality P.p (-2)
  have hclass : M.homologyπ (-2) (HomologicalComplex.cyclesMap P.p (-2) zc)
      = M.homologyπ (-2) mc := by
    have h2 : (P.F.homologyπ (-2) ≫ HomologicalComplex.homologyMap P.p (-2)) zc
        = (HomologicalComplex.cyclesMap P.p (-2) ≫ M.homologyπ (-2)) zc := by rw [hnat]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h2
    rw [← h2, hzc, hh0]
  have hprev : (ComplexShape.up ℤ).prev (-2) = (-3) := by simp
  have hdiff : M.homologyπ (-2) (HomologicalComplex.cyclesMap P.p (-2) zc - mc) = 0 := by
    rw [map_sub, hclass, sub_self]
  obtain ⟨u, hu⟩ := exists_toCycles_eq_of_homologyπ_eq_zero M hprev _ hdiff
  set m0 : P.F.X (-2) := P.F.iCycles (-2) zc with hm0def
  have hpm0 : (HomologicalComplex.Hom.f P.p (-2)) m0 = m + M.d (-3) (-2) u := by
    have hcm : M.iCycles (-2) (HomologicalComplex.cyclesMap P.p (-2) zc)
        = (HomologicalComplex.Hom.f P.p (-2)) (P.F.iCycles (-2) zc) := by
      have h := HomologicalComplex.cyclesMap_i P.p (-2)
      have h2 : (HomologicalComplex.cyclesMap P.p (-2) ≫ M.iCycles (-2)) zc
          = (P.F.iCycles (-2) ≫ HomologicalComplex.Hom.f P.p (-2)) zc := by rw [h]
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h2; exact h2
    have hceq : HomologicalComplex.cyclesMap P.p (-2) zc = mc + M.toCycles (-3) (-2) u := by
      rw [hu]; abel
    have hicyc : M.iCycles (-2) (M.toCycles (-3) (-2) u) = M.d (-3) (-2) u := by
      have h2 : (M.toCycles (-3) (-2) ≫ M.iCycles (-2)) u = M.d (-3) (-2) u := by
        rw [M.toCycles_i (-3) (-2)]
      rw [ModuleCat.comp_apply] at h2; exact h2
    rw [← hcm, hceq, map_add, hmc, hicyc]
  have : Epi (HomologicalComplex.Hom.f P.p (-3)) := P.epi (-3)
  have hp3surj : Function.Surjective (HomologicalComplex.Hom.f P.p (-3)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨u', hu'⟩ := hp3surj u
  refine ⟨m0 - P.F.d (-3) (-2) u', ?_, ?_⟩
  · rw [map_sub]
    have hm0cyc : P.F.d (-2) (-1) m0 = 0 := by
      have h2 : (P.F.iCycles (-2) ≫ P.F.d (-2) (-1)) zc
          = (0 : P.F.cycles (-2) ⟶ P.F.X (-1)) zc := by
        rw [P.F.iCycles_d (-2) (-1)]
      rw [ModuleCat.comp_apply] at h2; rw [hm0def]; rw [h2]; rfl
    rw [hm0cyc]
    have hdd : (P.F.d (-3) (-2) ≫ P.F.d (-2) (-1)) u' = (0 : P.F.X (-3) ⟶ P.F.X (-1)) u' := by
      rw [P.F.d_comp_d (-3) (-2) (-1)]
    rw [ModuleCat.comp_apply] at hdd
    rw [hdd]; simp
  · rw [map_sub, hpm0]
    rw [← d_apply_f_apply P.p, hu']
    abel

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- **Sub-lemma for (3): descend the lifted chain map through `p`.**
With `P`, `b` as produced by `exists_hom_from_projRes_Q_map_eq` (`b^{-2} = a ∘ p^{-2}`), there is a
morphism of complexes `ab : M → K` with `b = p ≫ ab` (chain-map equality) and
`ab^{-2} = a`.

INFORMAL ARGUMENT (Stacks 0ALN, proof of (3), second half): Since `b^{-2} =
a ∘ p^{-2}`, the map `b^{-2}` factors through the surjection `p^{-2}` (namely as
`a`). Because `F^0 = M^0` (so `ker p^0 = 0`) the kernel of `p^{-2}` surjects onto
the kernel of `p^{-1}` (the kernel of `p^•` is acyclic; equivalently a diagram
chase), forcing `b^{-1}` to factor through `p^{-1}` as some `ab^{-1} : M^{-1} →
K^{-1}`; and `b^0` factors through `p^0 = id` as `ab^0 = b^0`. These factorizations
assemble to a morphism of complexes `ab : M → K` (compatibility with differentials
follows from that of `b` and surjectivity of the `p^i`) with `p ≫ ab = b` and
`ab^{-2} = a`. -/
theorem exists_hom_comp_projRes_eq
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i))
    (a : M.X (-2) ⟶ K.X (-2))
    (P : ProjRes M) (b : P.F ⟶ K)
    (hb2 : HomologicalComplex.Hom.f b (-2) = HomologicalComplex.Hom.f P.p (-2) ≫ a) :
    ∃ (ab : M ⟶ K),
      P.p ≫ ab = b ∧ HomologicalComplex.Hom.f ab (-2) = a := by
  -- factor `b` through the termwise-epi `p`, using `F^0 = M^0` so kernels descend.
  classical
  have := P.qis
  have := P.strictLE
  have hp0 : HomologicalComplex.Hom.f P.p 0 = eqToHom P.X0 := P.p0
  have hiso : IsIso (HomologicalComplex.homologyMap P.p (-1)) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance
  have : Epi (HomologicalComplex.Hom.f P.p (-1)) := P.epi (-1)
  have hpsurj : Function.Surjective (HomologicalComplex.Hom.f P.p (-1)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  -- (★): K.d(-2)(-1) ∘ a kills cycles of M at -2.
  have hstar : ∀ m : M.X (-2), M.d (-2) (-1) m = 0 →
      K.d (-2) (-1) (a m) = 0 := by
    intro m hm
    obtain ⟨z, hzcyc, hpz⟩ := exists_preimage_of_d_apply_eq_zero M P m hm
    have e1 : a m = HomologicalComplex.Hom.f b (-2) z := by
      rw [hb2, ModuleCat.comp_apply, hpz]
    rw [e1, d_apply_f_apply b, hzcyc, map_zero]
  -- KILL PROPERTY for `b.f (-1)` on ker(p^{-1}).
  have hkill : ∀ x : P.F.X (-1), (HomologicalComplex.Hom.f P.p (-1)) x = 0 →
      (HomologicalComplex.Hom.f b (-1)) x = 0 := by
    intro x hx
    have hcyc : P.F.d (-1) 0 x = 0 := by
      have hmono : Function.Injective (HomologicalComplex.Hom.f P.p 0) := by
        have : IsIso (HomologicalComplex.Hom.f P.p 0) := by rw [hp0]; infer_instance
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      apply hmono
      rw [map_zero, ← d_apply_f_apply P.p, hx, map_zero]
    obtain ⟨y, hy⟩ := exists_d_apply_eq_of_isIso_homologyMap P.p (-1) x hcyc 0 (by
      rw [hx]; simp)
    -- y : P.F.X (-1-1).  Convert to degree -2.
    have hcast : (-1 - 1 : ℤ) = -2 := by norm_num
    obtain ⟨y2, hy2⟩ : ∃ y2 : P.F.X (-2), P.F.d (-2) (-1) y2 = x := by
      refine ⟨(eqToHom (congrArg P.F.X hcast)) y, ?_⟩
      rw [← hy, ← ModuleCat.comp_apply]
      congr 1
    -- now work at degree -2.
    rw [← hy2]
    rw [← d_apply_f_apply b]
    have hbf2 : HomologicalComplex.Hom.f b (-2) y2 = a (HomologicalComplex.Hom.f P.p (-2) y2) := by
      rw [hb2, ModuleCat.comp_apply]
    have hmcyc : M.d (-2) (-1) (HomologicalComplex.Hom.f P.p (-2) y2) = 0 := by
      rw [d_apply_f_apply P.p, hy2, hx]
    rw [hbf2]
    exact hstar _ hmcyc
  obtain ⟨abm1, habm1⟩ := exists_comp_eq_of_apply_eq_zero (HomologicalComplex.Hom.f P.p (-1))
    (HomologicalComplex.Hom.f b (-1)) hpsurj hkill
  set ab0 : M.X 0 ⟶ K.X 0 := eqToHom P.X0.symm ≫ HomologicalComplex.Hom.f b 0 with hab0def
  let abf : ∀ i, M.X i ⟶ K.X i := fun i =>
    if h0 : i = 0 then eqToHom (by rw [h0]) ≫ ab0 ≫ eqToHom (by rw [h0])
    else if h1 : i = -1 then eqToHom (by rw [h1]) ≫ abm1 ≫ eqToHom (by rw [h1])
    else if h2 : i = -2 then eqToHom (by rw [h2]) ≫ a ≫ eqToHom (by rw [h2])
    else 0
  have habf0 : abf 0 = ab0 := by simp [abf]
  have habfm1 : abf (-1) = abm1 := by simp [abf]
  have habfm2 : abf (-2) = a := by simp [abf]
  have hda : M.d (-3) (-2) ≫ a = 0 := by
    have : Epi (HomologicalComplex.Hom.f P.p (-3)) := P.epi (-3)
    apply (cancel_epi (HomologicalComplex.Hom.f P.p (-3))).mp
    rw [Limits.comp_zero]
    have hpc := HomologicalComplex.Hom.comm P.p (-3) (-2)
    rw [← Category.assoc, hpc, Category.assoc]
    rw [← hb2]
    have hbcomm := HomologicalComplex.Hom.comm b (-3) (-2)
    rw [← hbcomm]
    have hKm3 : IsZero (K.X (-3)) := hK (-3) (by norm_num)
    rw [hKm3.eq_zero_of_tgt (HomologicalComplex.Hom.f b (-3)), Limits.zero_comp]
  have hcomm' : ∀ i j, (ComplexShape.up ℤ).Rel i j → abf i ≫ K.d i j = M.d i j ≫ abf j := by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    by_cases hj0 : j = 0
    · subst hj0
      have hi : i = -1 := by omega
      subst hi
      rw [habf0, habfm1]
      apply (cancel_epi (HomologicalComplex.Hom.f P.p (-1))).mp
      calc HomologicalComplex.Hom.f P.p (-1) ≫ abm1 ≫ K.d (-1) 0
          = P.F.d (-1) 0 ≫ HomologicalComplex.Hom.f b 0 := by
              rw [← Category.assoc, habm1, HomologicalComplex.Hom.comm b (-1) 0]
        _ = P.F.d (-1) 0 ≫ HomologicalComplex.Hom.f P.p 0 ≫ ab0 := by
              rw [hab0def, hp0]
              simp
        _ = HomologicalComplex.Hom.f P.p (-1) ≫ M.d (-1) 0 ≫ ab0 := by
              rw [← Category.assoc, ← HomologicalComplex.Hom.comm P.p (-1) 0, Category.assoc]
    · by_cases hjm1 : j = -1
      · subst hjm1
        have hi : i = -2 := by omega
        subst hi
        rw [habfm1, habfm2]
        have : Epi (HomologicalComplex.Hom.f P.p (-2)) := P.epi (-2)
        apply (cancel_epi (HomologicalComplex.Hom.f P.p (-2))).mp
        have hpc := HomologicalComplex.Hom.comm P.p (-2) (-1)
        rw [← Category.assoc, ← hb2]
        have hbcomm := HomologicalComplex.Hom.comm b (-2) (-1)
        rw [hbcomm, ← Category.assoc, hpc, Category.assoc, habm1]
      · by_cases hjm2 : j = -2
        · subst hjm2
          have hi : i = -3 := by omega
          subst hi
          have habfi : abf (-3) = 0 := by simp [abf]
          rw [habfi, habfm2, Limits.zero_comp, hda]
        · by_cases hjle : j ≤ -3
          · have hKj : IsZero (K.X j) := hK j hjle
            have hKi : IsZero (K.X i) := hK i (by omega)
            have h1 : abf i ≫ K.d i j = 0 := by
              rw [hKi.eq_zero_of_tgt (abf i)]; simp
            have h2 : M.d i j ≫ abf j = 0 := by
              rw [hKj.eq_zero_of_tgt (abf j)]; simp
            rw [h1, h2]
          · have hjge : 1 ≤ j := by omega
            have hMj : IsZero (M.X j) := hM_pos j (by omega)
            by_cases hi0 : i = 0
            · subst hi0
              have hj1 : j = 1 := by omega
              subst hj1
              have h2 : M.d 0 1 ≫ abf 1 = 0 := by
                rw [hMj.eq_zero_of_tgt (M.d 0 1)]; simp
              rw [h2, habf0]
              have hFX1 : IsZero (P.F.X 1) :=
                CochainComplex.isZero_of_isStrictlyLE P.F 0 1 (by omega)
              have hFd : P.F.d 0 1 = 0 := hFX1.eq_zero_of_tgt _
              have hbcomm := HomologicalComplex.Hom.comm b 0 1
              rw [hFd, Limits.zero_comp] at hbcomm
              rw [hab0def, Category.assoc, hbcomm, Limits.comp_zero]
            · have hMi : IsZero (M.X i) := hM_pos i (by omega)
              have habfi : abf i = 0 := by rw [hMi.eq_zero_of_src (abf i)]
              have h1 : abf i ≫ K.d i j = 0 := by rw [habfi]; simp
              have h2 : M.d i j ≫ abf j = 0 := by
                rw [hMi.eq_zero_of_src (M.d i j)]; simp
              rw [h1, h2]
  refine ⟨{ f := abf, comm' := hcomm' }, ?_, habfm2⟩
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  change HomologicalComplex.Hom.f P.p i ≫ abf i = HomologicalComplex.Hom.f b i
  by_cases hi0 : i = 0
  · subst hi0
    rw [habf0, hp0, hab0def, ← Category.assoc]
    simp
  · by_cases him1 : i = -1
    · subst him1
      rw [habfm1, habm1]
    · by_cases him2 : i = -2
      · subst him2
        rw [habfm2, ← hb2]
      · by_cases hile : i ≤ -3
        · have hKi : IsZero (K.X i) := hK i hile
          rw [hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f b i)]
          rw [hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f P.p i ≫ abf i)]
        · have hFi : IsZero (P.F.X i) :=
            CochainComplex.isZero_of_isStrictlyLE P.F 0 i (by omega)
          rw [hFi.eq_zero_of_src (HomologicalComplex.Hom.f b i)]
          rw [hFi.eq_zero_of_src (HomologicalComplex.Hom.f P.p i)]
          simp

/-- **(3)** Assume `K^i = 0` for `i ≤ -3`. Let `α ∈ Hom_{D(R)}(M, K)`. Suppose the
composite of `α` with the canonical map `K → K^{-2}[2]`, viewed in
`Hom_{D(R)}(M, K^{-2}[2]) = Ext^2(M, K^{-2})`, comes from an `R`-module
homomorphism `a : M^{-2} → K^{-2}` with `a ∘ d_M^{-3} = 0` (i.e. equals the
`D(R)`-morphism induced by the chain map `M → (single (-2)).obj (K^{-2})`
determined by `a`). Then `α` is represented by a morphism of complexes
`a^• : M → K` with `a^{-2} = a`.

PROOF SKETCH (Stacks 0ALN, proof of (3)): take `P := exists_projRes`, lift `α`
to `b : F → K` with `b^{-2} = a ∘ p^{-2}` (`exists_hom_from_projRes_Q_map_eq`),
descend `b` through `p` to `ab : M → K` with `p ≫ ab = b` and `ab^{-2} = a`
(`exists_hom_comp_projRes_eq`). Then
`Q.map p ≫ Q.map ab = Q.map b = Q.map p ≫ α`, and `Q.map p` is an iso, so
`Q.map ab = α`. This `ab` is the required representative. -/
@[stacks 0ALN "(3)"]
theorem exists_hom_Q_map_eq_of_comp_canonical
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i))
    (α : HomD M K)
    (a : M.X (-2) ⟶ K.X (-2))
    (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : α ≫ DerivedCategory.Q.map (canonicalToSingleNegTwo K hK)
        = DerivedCategory.Q.map (HomologicalComplex.mkHomToSingle a (by
            intro i hi
            simp only [ComplexShape.up_Rel] at hi
            have hi3 : i = -3 := by omega
            subst hi3
            exact ha))) :
    ∃ (ab : M ⟶ K),
      DerivedCategory.Q.map ab = α ∧ HomologicalComplex.Hom.f ab (-2) = a := by
  obtain ⟨P⟩ := exists_projRes M hM_pos hM0
  obtain ⟨b, hbα, hb2⟩ := exists_hom_from_projRes_Q_map_eq M K hK α a ha hα P
  obtain ⟨ab, hpab, hab2⟩ := exists_hom_comp_projRes_eq M K hM_pos hK a P b hb2
  refine ⟨ab, ?_, hab2⟩
  -- `Q.map p ≫ Q.map ab = Q.map b = Q.map p ≫ α`; cancel the iso `Q.map p`.
  have hiso : IsIso (DerivedCategory.Q.map P.p) := P.isIso_Q_map_p
  have key : DerivedCategory.Q.map P.p ≫ DerivedCategory.Q.map ab
      = DerivedCategory.Q.map P.p ≫ α := by
    rw [← DerivedCategory.Q.map_comp, hpab, hbα]
  exact (cancel_epi (DerivedCategory.Q.map P.p)).mp key

end TwoTermComplexExt

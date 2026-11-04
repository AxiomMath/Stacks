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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Tactic.LinearCombination
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.Homology.TwoTermComplex.Ext.DerivedHom
public import StacksFrontier.Homology.TwoTermComplex.ProjRes
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Stacks 0ALN (1) and (2): homotopy classes versus morphisms of the derived category

This is parts (1) and (2) of Stacks project Lemma 15.86.4, tag 0ALN ("Two term
complexes", section 15.86 of *More on Algebra*). The setting, the notation and the objects
used here are those of `StacksFrontier.Homology.TwoTermComplex.Ext.DerivedHom`.

## Main Statements

Hypotheses common to all parts: `M` is a complex with `M^i = 0` for `i > 0`
and with `M^0` projective. `K` is a second complex.

* `toHomD_bijective` is **(1)**: if `K^i = 0` for `i ≤ -2` then the canonical map
  `Hom_{K(R)}(M, K) → Hom_{D(R)}(M, K)` is bijective. Its geometric content is
  `precomp_quotient_map_projRes_bijective`, that precomposition with a projective
  resolution `p : F → M` is a bijection already on `K(R)`; that in turn is the degreewise
  descent of chain maps (`exists_comp_eq_of_hom_projRes`) and of homotopies
  (`nonempty_homotopy_of_comp_projRes`) along the surjections `p^i`.
* `forall_Q_map_comp_eq_zero_iff` is **(2)**: if `K^i = 0` for `i ∉ {-1, 0}` and `K^0` is
  projective, then the vanishing of `Ext^1(a, N)` for every module `N` is equivalent to the
  existence of `h^0 : M^0 → K^{-1}` with `a^{-1} + h^0 ∘ d_M^{-1} = 0`. The two directions
  are `Q_map_comp_eq_zero_of_nullHomotopy` and `exists_nullHomotopy_of_Q_map_comp_eq_zero`,
  and both run through (1) with `N[1]` in the role of the target.

Note on part (2)(b): the Stacks source has a typographical error; the intended
relation is `a^{-1} + h^0 ∘ d_M^{-1} = 0` with `h^0 : M^0 → K^{-1}` and
`d_M^{-1} : M^{-1} → M^0`. We adopt this corrected formula.
-/

open CategoryTheory Limits

namespace TwoTermComplexExt

universe u v

variable {R : Type u} [Ring R] [Small.{v} R]
  [HasDerivedCategory (ModuleCat.{v} R)]

variable (M K : CochainComplex (ModuleCat.{v} R) ℤ)

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- **Surjectivity input for (1).** Every chain map `gF : F → K` descends along the
resolution `p` to a chain map `gm : M → K` with `p ≫ gm = gF` (on the nose), using
`K^i = 0` for `i ≤ -2` and the acyclicity of `p` at degree `-1`. -/
private lemma exists_comp_eq_of_hom_projRes (P : ProjRes M)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (hK : ∀ i ≤ (-2 : ℤ), IsZero (K.X i)) (gF : P.F ⟶ K) :
    ∃ gm : M ⟶ K, P.p ≫ gm = gF := by
  classical
  have := P.qis
  have := P.strictLE
  -- `p^0 = eqToHom`, an iso.
  have hp0 : HomologicalComplex.Hom.f P.p 0 = eqToHom P.X0 := P.p0
  -- homology iso at -1.
  have hiso : IsIso (HomologicalComplex.homologyMap P.p (-1)) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance
  -- vanishing of `K` below `-1`.
  have hKm2 : IsZero (K.X (-2)) := hK (-2) (by norm_num)
  -- `p.f (-1)` is surjective.
  have : Epi (HomologicalComplex.Hom.f P.p (-1)) := P.epi (-1)
  have hpsurj : Function.Surjective (HomologicalComplex.Hom.f P.p (-1)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  -- KILL PROPERTY: `gF.f (-1)` annihilates `ker (p.f (-1))`.
  have hkill : ∀ x : P.F.X (-1), (HomologicalComplex.Hom.f P.p (-1)) x = 0 →
      (HomologicalComplex.Hom.f gF (-1)) x = 0 := by
    intro x hx
    -- (1) `x` is a cycle: `F.d (-1) 0 x = 0`, since `p^0` is mono.
    have hcyc : P.F.d (-1) 0 x = 0 := by
      have hmono : Function.Injective (HomologicalComplex.Hom.f P.p 0) := by
        have : IsIso (HomologicalComplex.Hom.f P.p 0) := by rw [hp0]; infer_instance
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      apply hmono
      have hcomm := HomologicalComplex.Hom.comm P.p (-1) 0
      have : (HomologicalComplex.Hom.f P.p (-1) ≫ M.d (-1) 0) x
          = (P.F.d (-1) 0 ≫ HomologicalComplex.Hom.f P.p 0) x := by rw [hcomm]
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at this
      rw [map_zero]
      rw [← this, hx, map_zero]
    -- (2) `x` is a boundary in `F`: `p^{-1} x = 0` is a boundary in `M`.
    obtain ⟨b, hb⟩ := exists_d_apply_eq_of_isIso_homologyMap P.p (-1) x hcyc 0 (by
      rw [hx]; simp)
    -- (3) `gF.f (-1) x = K.d (-2) (-1) (gF.f (-2) b) = 0`.
    have hcomm := HomologicalComplex.Hom.comm gF (-1 - 1) (-1)
    have hKm2' : IsZero (K.X (-1 - 1)) := hK (-1 - 1) (by norm_num)
    have hgf2 : HomologicalComplex.Hom.f gF (-1 - 1) = 0 := hKm2'.eq_zero_of_tgt _
    rw [← hb]
    have hh : (P.F.d (-1 - 1) (-1) ≫ HomologicalComplex.Hom.f gF (-1)) b
        = (HomologicalComplex.Hom.f gF (-1 - 1) ≫ K.d (-1 - 1) (-1)) b := by rw [hcomm]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hh
    rw [hh, hgf2]
    simp
  -- the descended degree `-1` component.
  obtain ⟨gmm1, hgmm1⟩ := exists_comp_eq_of_apply_eq_zero (HomologicalComplex.Hom.f P.p (-1))
    (HomologicalComplex.Hom.f gF (-1)) hpsurj hkill
  -- the descended degree `0` component.
  set gm0 : M.X 0 ⟶ K.X 0 := eqToHom P.X0.symm ≫ HomologicalComplex.Hom.f gF 0 with hgm0def
  -- assemble the componentwise map.
  let gmf : ∀ i, M.X i ⟶ K.X i := fun i =>
    if h0 : i = 0 then eqToHom (by rw [h0]) ≫ gm0 ≫ eqToHom (by rw [h0])
    else if h1 : i = -1 then eqToHom (by rw [h1]) ≫ gmm1 ≫ eqToHom (by rw [h1])
    else 0
  have hgmf0 : gmf 0 = gm0 := by simp [gmf]
  have hgmfm1 : gmf (-1) = gmm1 := by simp [gmf]
  -- the chain condition `comm'`, only nontrivial at `(-1, 0)`.
  have hcomm' : ∀ i j, (ComplexShape.up ℤ).Rel i j → gmf i ≫ K.d i j = M.d i j ≫ gmf j := by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    -- the only relation with both endpoints possibly nonzero is `(-1, 0)`.
    by_cases hj0 : j = 0
    · subst hj0
      have hi : i = -1 := by omega
      subst hi
      rw [hgmf0, hgmfm1]
      -- cancel epi `p.f (-1)`.
      apply (cancel_epi (HomologicalComplex.Hom.f P.p (-1))).mp
      calc HomologicalComplex.Hom.f P.p (-1) ≫ gmm1 ≫ K.d (-1) 0
          = P.F.d (-1) 0 ≫ HomologicalComplex.Hom.f gF 0 := by
              rw [← Category.assoc, hgmm1, HomologicalComplex.Hom.comm gF (-1) 0]
        _ = P.F.d (-1) 0 ≫ HomologicalComplex.Hom.f P.p 0 ≫ gm0 := by
              rw [hgm0def, hp0]
              simp
        _ = HomologicalComplex.Hom.f P.p (-1) ≫ M.d (-1) 0 ≫ gm0 := by
              rw [← Category.assoc, ← HomologicalComplex.Hom.comm P.p (-1) 0, Category.assoc]
    · -- `j ≠ 0`, so `j ≤ -1` or `j ≥ 1`. In all such cases both sides vanish.
      have hjval : i + 1 = j := hij
      by_cases hjm1 : j = -1
      · -- `i = -2`: chain condition `gmf(-2) ≫ d = 0 = M.d(-2)(-1) ≫ gmf(-1)`.
        subst hjm1
        have hi : i = -2 := by omega
        subst hi
        have hgmfi : gmf (-2) = 0 := by simp [gmf]
        rw [hgmfi, hgmfm1, Limits.zero_comp]
        -- `M.d (-2) (-1) ≫ gmm1 = 0` via epi `p.f (-2)`.
        symm
        have : Epi (HomologicalComplex.Hom.f P.p (-2)) := P.epi (-2)
        apply (cancel_epi (HomologicalComplex.Hom.f P.p (-2))).mp
        rw [Limits.comp_zero]
        have hpc := HomologicalComplex.Hom.comm P.p (-2) (-1)
        rw [← Category.assoc, hpc, Category.assoc, hgmm1]
        have hgFc := HomologicalComplex.Hom.comm gF (-2) (-1)
        rw [← hgFc]
        have hgf2 : HomologicalComplex.Hom.f gF (-2) = 0 := hKm2.eq_zero_of_tgt _
        rw [hgf2, Limits.zero_comp]
      · -- neither `j = 0` nor `j = -1`.
        by_cases hjle : j ≤ -2
        · have hKj : IsZero (K.X j) := hK j hjle
          have hKi : IsZero (K.X i) := hK i (by omega)
          have h1 : gmf i ≫ K.d i j = 0 := by
            rw [hKi.eq_zero_of_tgt (gmf i)]; simp
          have h2 : M.d i j ≫ gmf j = 0 := by
            rw [hKj.eq_zero_of_tgt (gmf j)]; simp
          rw [h1, h2]
        · -- `j ≥ 1`, so `i ≥ 0`; `M.X i = 0` for `i ≥ 1` and at `i=0` `gmf 0 ≫ K.d 0 j`.
          have hjge : 1 ≤ j := by omega
          have hMj : IsZero (M.X j) := hM_pos j (by omega)
          by_cases hi0 : i = 0
          · -- `i = 0`, `j = 1`: use `F.X 1 = 0` and the chain condition for `gF`.
            subst hi0
            have hj1 : j = 1 := by omega
            subst hj1
            have h2 : M.d 0 1 ≫ gmf 1 = 0 := by
              rw [hMj.eq_zero_of_tgt (M.d 0 1)]; simp
            rw [h2, hgmf0]
            -- `gm0 ≫ K.d 0 1 = 0` because `gF.f 0 ≫ K.d 0 1 = F.d 0 1 ≫ gF.f 1 = 0`.
            have hFX1 : IsZero (P.F.X 1) :=
              CochainComplex.isZero_of_isStrictlyLE P.F 0 1 (by omega)
            have hFd : P.F.d 0 1 = 0 := hFX1.eq_zero_of_tgt _
            have hgFcomm := HomologicalComplex.Hom.comm gF 0 1
            rw [hFd, Limits.zero_comp] at hgFcomm
            rw [hgm0def, Category.assoc, hgFcomm, Limits.comp_zero]
          · -- `i ≥ 1`: `M.X i = 0`.
            have hMi : IsZero (M.X i) := hM_pos i (by omega)
            have hgmfi : gmf i = 0 := by
              rw [hMi.eq_zero_of_src (gmf i)]
            have h1 : gmf i ≫ K.d i j = 0 := by rw [hgmfi]; simp
            have h2 : M.d i j ≫ gmf j = 0 := by
              rw [hMi.eq_zero_of_src (M.d i j)]; simp
            rw [h1, h2]
  refine ⟨{ f := gmf, comm' := hcomm' }, ?_⟩
  -- `p ≫ gm = gF` degreewise.
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  show HomologicalComplex.Hom.f P.p i ≫ gmf i = HomologicalComplex.Hom.f gF i
  by_cases hi0 : i = 0
  · subst hi0
    rw [hgmf0, hp0, hgm0def, ← Category.assoc]
    simp
  · by_cases him1 : i = -1
    · subst him1
      rw [hgmfm1, hgmm1]
    · by_cases hile : i ≤ -2
      · have hKi : IsZero (K.X i) := hK i hile
        rw [hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f gF i)]
        rw [hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f P.p i ≫ gmf i)]
      · -- `i ≥ 1`: `F.X i = 0`.
        have hFi : IsZero (P.F.X i) :=
          CochainComplex.isZero_of_isStrictlyLE P.F 0 i (by omega)
        rw [hFi.eq_zero_of_src (HomologicalComplex.Hom.f gF i)]
        rw [hFi.eq_zero_of_src (HomologicalComplex.Hom.f P.p i)]
        simp

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- **Injectivity input for (1).** If `p ≫ gm₁` and `p ≫ gm₂` are chain-homotopic,
then `gm₁` and `gm₂` are chain-homotopic, by descending the (single surviving)
homotopy component `h^0 : F^0 → K^{-1}` along `F^0 = M^0`. Uses `K^i = 0` for
`i ≤ -2` and `M^i = 0` for `i > 0`. -/
private lemma nonempty_homotopy_of_comp_projRes (P : ProjRes M)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (hK : ∀ i ≤ (-2 : ℤ), IsZero (K.X i)) (gm₁ gm₂ : M ⟶ K)
    (H : Homotopy (P.p ≫ gm₁) (P.p ≫ gm₂)) :
    Nonempty (Homotopy gm₁ gm₂) := by
  classical
  have := P.strictLE
  have hp0 : HomologicalComplex.Hom.f P.p 0 = eqToHom P.X0 := P.p0
  have : Epi (HomologicalComplex.Hom.f P.p (-1)) := P.epi (-1)
  -- the descended homotopy component `h^0 : M^0 → K^{-1}`.
  set h0 : M.X 0 ⟶ K.X (-1) := eqToHom P.X0.symm ≫ H.hom 0 (-1) with hh0def
  -- the homotopy datum: only `(0, -1)` is nonzero.
  let homf : ∀ i j, M.X i ⟶ K.X j := fun i j =>
    if hi : i = 0 then (if hj : j = -1 then eqToHom (by rw [hi]) ≫ h0 ≫ eqToHom (by rw [hj])
      else 0) else 0
  have homf0 : homf 0 (-1) = h0 := by simp [homf]
  -- the key two relations from `H.comm`.
  have hrelm10 : (ComplexShape.up ℤ).Rel (-1) 0 := by simp [ComplexShape.up_Rel]
  have hrelm2m1 : (ComplexShape.up ℤ).Rel (-2) (-1) := by simp [ComplexShape.up_Rel]
  have hrel01 : (ComplexShape.up ℤ).Rel 0 1 := by simp [ComplexShape.up_Rel]
  -- degree 0 relation: `gm₁.f 0 - gm₂.f 0 = h0 ≫ K.d (-1) 0`.
  have hd0 : HomologicalComplex.Hom.f gm₁ 0 = h0 ≫ K.d (-1) 0 + HomologicalComplex.Hom.f gm₂ 0 := by
    have c := H.comm 0
    rw [dNext_eq H.hom hrel01, prevD_eq H.hom hrelm10] at c
    -- `dNext 0 = F.d 0 1 ≫ H.hom 1 0 = 0` since `F.X 1 = 0`.
    have hFX1 : IsZero (P.F.X 1) := CochainComplex.isZero_of_isStrictlyLE P.F 0 1 (by omega)
    have hFd : P.F.d 0 1 = 0 := hFX1.eq_zero_of_tgt _
    rw [hFd, Limits.zero_comp, zero_add] at c
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hp0] at c
    -- c : eqToHom ≫ gm₁.f 0 = H.hom 0 (-1) ≫ K.d (-1) 0 + eqToHom ≫ gm₂.f 0
    -- compose on the left by eqToHom P.X0.symm.
    have c2 := congrArg (fun t => eqToHom P.X0.symm ≫ t) c
    simp only [Preadditive.comp_add] at c2
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc] at c2
    simp only [eqToHom_trans, eqToHom_refl, Category.id_comp] at c2
    rw [hh0def]
    exact c2
  -- degree -1 relation: `gm₁.f (-1) = M.d (-1) 0 ≫ h0 + gm₂.f (-1)`.
  have hdm1 : HomologicalComplex.Hom.f gm₁ (-1)
      = M.d (-1) 0 ≫ h0 + HomologicalComplex.Hom.f gm₂ (-1) := by
    apply (cancel_epi (HomologicalComplex.Hom.f P.p (-1))).mp
    have c := H.comm (-1)
    rw [dNext_eq H.hom hrelm10, prevD_eq H.hom hrelm2m1] at c
    -- `prevD (-1) = H.hom (-1) (-2) ≫ K.d (-2) (-1) = 0` since `K.X (-2) = 0`.
    have hKm2 : IsZero (K.X (-2)) := hK (-2) (by norm_num)
    have hKd : K.d (-2) (-1) = 0 := hKm2.eq_zero_of_src _
    rw [hKd, Limits.comp_zero, add_zero] at c
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at c
    -- c : P.p.f (-1) ≫ gm₁.f (-1) = F.d (-1) 0 ≫ H.hom 0 (-1) + P.p.f (-1) ≫ gm₂.f (-1)
    rw [Preadditive.comp_add]
    rw [c]
    -- show `F.d (-1) 0 ≫ H.hom 0 (-1) = P.p.f (-1) ≫ M.d (-1) 0 ≫ h0`.
    congr 1
    have hpc := HomologicalComplex.Hom.comm P.p (-1) 0
    -- `P.p.f (-1) ≫ M.d (-1) 0 ≫ h0 = F.d (-1) 0 ≫ P.p.f 0 ≫ h0`.
    rw [← Category.assoc, hpc, Category.assoc, hh0def, hp0]
    rw [← Category.assoc, ← Category.assoc]
    simp
  refine ⟨{ hom := homf, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    simp only [homf]
    split <;> rename_i hi
    · split <;> rename_i hj
      · exfalso; apply hij; subst hi; subst hj; simp [ComplexShape.up_Rel]
      · rfl
    · rfl
  · intro i
    by_cases hi0 : i = 0
    · subst hi0
      -- `dNext 0 = F.d 0 1 ≫ homf 1 0 = 0`; `prevD 0 = homf 0 (-1) ≫ K.d (-1) 0`.
      rw [dNext_eq homf hrel01, prevD_eq homf hrelm10, homf0]
      have hz : homf 1 0 = 0 := by simp [homf]
      rw [hz, Limits.comp_zero, zero_add]
      rw [hd0]
    · by_cases him1 : i = -1
      · subst him1
        rw [dNext_eq homf hrelm10, prevD_eq homf hrelm2m1, homf0]
        have hz : homf (-1) (-2) = 0 := by simp [homf]
        rw [hz, Limits.zero_comp, add_zero]
        rw [hdm1]
      · -- `i ∉ {0, -1}`: `dNext` and `prevD` both vanish, and `gm₁.f i = gm₂.f i`.
        rw [dNext_eq homf (show (ComplexShape.up ℤ).Rel i (i+1) from by simp [ComplexShape.up_Rel]),
            prevD_eq homf (show (ComplexShape.up ℤ).Rel (i-1) i from by simp [ComplexShape.up_Rel])]
        have hzd : homf (i+1) i = 0 := by
          simp only [homf]
          rw [dite_eq_right (by omega : ¬ i + 1 = 0)]
        have hzp : homf i (i-1) = 0 := by
          simp only [homf]
          by_cases hi : i = 0
          · rw [dite_eq_left hi, dite_eq_right (by omega : ¬ i - 1 = -1)]
          · rw [dite_eq_right hi]
        rw [hzd, hzp, Limits.comp_zero, Limits.zero_comp, zero_add, zero_add]
        by_cases hile : i ≤ -2
        · have hKi : IsZero (K.X i) := hK i hile
          rw [hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f gm₁ i),
              hKi.eq_zero_of_tgt (HomologicalComplex.Hom.f gm₂ i)]
        · have hMi : IsZero (M.X i) := hM_pos i (by omega)
          rw [hMi.eq_zero_of_src (HomologicalComplex.Hom.f gm₁ i),
              hMi.eq_zero_of_src (HomologicalComplex.Hom.f gm₂ i)]

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- **Sub-lemma for (1): precomposition with the resolution is a bijection on `K(R)`.**
Let `P` be a projective resolution of `M` and assume `K^i = 0` for `i ≤ -2`. Then
precomposition with the image `[p]` of `p` in `K(R)` gives a bijection
`Hom_{K(R)}(M, K) → Hom_{K(R)}(F, K)`.

INFORMAL ARGUMENT (Stacks 0ALN, proof of (1), second paragraph): Because `K^i = 0`
for `i ≤ -2`, the only possibly nonzero degrees of `K` are `≥ -1`. A morphism of
complexes `g : F → K` is determined by `g^{-1}, g^0, …`; since `p^0 : F^0 → M^0` is
an isomorphism (indeed `p^0 = id`, `F^0 = M^0`) and `p^{-1} : F^{-1} → M^{-1}` is
surjective with kernel mapping onto `ker p^{-2}` etc., every such `g` factors
uniquely (up to homotopy) through `p`: i.e. `g = g' ∘ p` for some `g' : M → K`,
because the differential `d_F^{-2} : F^{-2} → F^{-1}` and the vanishing of `K` below
`-1` force `g^{-2} = 0` and make `g^{-1}, g^0` descend along the surjections `p^i`.
Likewise any homotopy `{h^i : F^i → K^{i-1}}` (note `K^{i-1} = 0` for `i ≤ -1`, so
only `h^0 : F^0 → K^{-1}` and `h^1 = 0` survive, and `F^0 = M^0`) factors through
`p`. Hence precomposition by `[p]` is both injective (homotopies descend) and
surjective (chain maps descend) on homotopy classes. This is the crux geometric
input of (1); proving it amounts to the explicit degreewise descent just described
using surjectivity of `p` and `K^{≤ -2} = 0`. -/
theorem precomp_quotient_map_projRes_bijective
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (hK : ∀ i ≤ (-2 : ℤ), IsZero (K.X i)) (P : ProjRes M) :
    Function.Bijective
      (fun g : HomK M K =>
        ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map P.p ≫ g
          : HomK P.F K)) := by
  -- Degreewise descent along the surjections `p^i`, using `K^i = 0` for `i ≤ -2`.
  set Q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  refine ⟨fun g₁ g₂ hg => ?_, fun φ => ?_⟩
  · obtain ⟨gm₁, hgm₁⟩ := Q.map_surjective g₁
    obtain ⟨gm₂, hgm₂⟩ := Q.map_surjective g₂
    have heq : Q.map (P.p ≫ gm₁) = Q.map (P.p ≫ gm₂) := by
      rwa [Q.map_comp, Q.map_comp, hgm₁, hgm₂]
    obtain ⟨H'⟩ :=
      nonempty_homotopy_of_comp_projRes M K P hM_pos hK gm₁ gm₂
        (HomotopyCategory.homotopyOfEq _ _ heq)
    rw [← hgm₁, ← hgm₂]
    exact HomotopyCategory.eq_of_homotopy _ _ H'
  · obtain ⟨gF, hgF⟩ := Q.map_surjective φ
    obtain ⟨gm, hgm⟩ := exists_comp_eq_of_hom_projRes M K P hM_pos hK gF
    exact ⟨Q.map gm, by simp only; rw [← Q.map_comp, hgm, hgF]⟩

/-- **(1)** Assume `K^i = 0` for `i ≤ -2`. Then the canonical map
`Hom_{K(R)}(M, K) → Hom_{D(R)}(M, K)` is an isomorphism (bijective).

PROOF SKETCH (Stacks 0ALN, proof of (1)): Pick a termwise-surjective projective
resolution `p : F → M` (`exists_projRes`); then `F` is K-projective. By
`CochainComplex.IsKProjective.Qh_map_bijective`, the localization map
`Qh.map : Hom_{K(R)}(F, K) → Hom_{D(R)}(F, K)` is bijective. Since `Q.map p` is an
isomorphism in `D(R)` (`p` a quasi-iso), postcomposition identifies
`Hom_{D(R)}(F, K) ≅ Hom_{D(R)}(M, K)`. By `precomp_quotient_map_projRes_bijective`, precomposition
with `[p]` is a bijection `Hom_{K(R)}(M, K) → Hom_{K(R)}(F, K)`. Chasing the square
(`Qh.map` is natural and `toHomD = Qh.map`), `toHomD : Hom_{K(R)}(M, K) →
Hom_{D(R)}(M, K)` is the composite of these three bijections, hence bijective. -/
@[stacks 0ALN "(1)"]
theorem toHomD_bijective
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i ≤ (-2 : ℤ), IsZero (K.X i)) :
    Function.Bijective (fun f : HomK M K => (toHomD f : HomD M K)) := by
  obtain ⟨P⟩ := exists_projRes M hM_pos hM0
  have hFKproj : P.F.IsKProjective := P.isKProjective
  -- (A) `Qh.map`, hence `toHomD`, is bijective out of the K-projective `F`.
  have hA : Function.Bijective (fun g : HomK P.F K => (toHomD g : HomD P.F K)) :=
    toHomD_bijective_of_Qh (CochainComplex.IsKProjective.Qh_map_bijective P.F
      ((HomotopyCategory.quotient _ _).obj K))
  -- (B) precomposition by `[p]` is bijective on `K(R)` (the geometric content).
  have hB := precomp_quotient_map_projRes_bijective M K hM_pos hK P
  -- (C) precomposition with the iso `Q.map p` is bijective on `HomD`.
  have hiso : IsIso (DerivedCategory.Q.map P.p) := P.isIso_Q_map_p
  have hpre : Function.Bijective
      (fun α : HomD M K => DerivedCategory.Q.map P.p ≫ α : HomD M K → HomD P.F K) := by
    refine ⟨fun a b h => ?_, fun c => ⟨inv (DerivedCategory.Q.map P.p) ≫ c, ?_⟩⟩
    · simpa using congrArg (inv (DerivedCategory.Q.map P.p) ≫ ·) h
    · simp
  -- naturality / functoriality: `Q.map p ≫ toHomD f = toHomD ([p] ≫ f)`.
  have hnat : (fun α : HomD M K => DerivedCategory.Q.map P.p ≫ α) ∘
      (fun f : HomK M K => (toHomD f : HomD M K)) =
      (fun g : HomK P.F K => (toHomD g : HomD P.F K)) ∘
        (fun g : HomK M K =>
          ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map P.p ≫ g
            : HomK P.F K)) := by
    funext f
    simp only [Function.comp_apply]
    exact Q_map_comp_toHomD P.p f
  -- the composite `hpre ∘ toHomD` equals `hA ∘ hB`, hence bijective.
  have hcomp : Function.Bijective
      ((fun α : HomD M K => DerivedCategory.Q.map P.p ≫ α) ∘
        (fun f : HomK M K => (toHomD f : HomD M K))) := by
    rw [hnat]
    exact hA.comp hB
  -- `hpre` injective + `hpre ∘ toHomD` bijective ⟹ `toHomD` bijective.
  set g : HomD M K → HomD P.F K := fun α => DerivedCategory.Q.map P.p ≫ α
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · apply hcomp.injective
    show g (toHomD a) = g (toHomD b)
    exact congrArg g hab
  · obtain ⟨a, ha⟩ := hcomp.surjective (g c)
    refine ⟨a, hpre.injective ?_⟩
    show g (toHomD a) = g c
    exact ha

/-- `toHomD` is bijective with target `N[1]`, which is concentrated in degree `-1`. -/
private theorem toHomD_shiftSingle_bijective (N : ModuleCat.{v} R)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0)) :
    Function.Bijective (fun f : HomK M (shiftSingle N 1) => (toHomD f : HomD M _)) :=
  toHomD_bijective M _ hM_pos hM0 fun _ hi => isZero_shiftSingle_X (by omega)

/-- **Sub-lemma for (2), direction (2b) ⇒ (2a).** Under the hypotheses of (2), if
there is `h^0 : M^0 → K^{-1}` with `a^{-1} + h^0 ∘ d_M^{-1} = 0`, then for every
`N` the induced map `Ext^1(a, N)` is zero.

INFORMAL ARGUMENT (Stacks 0ALN, proof of (2), "If (2)(b) holds … implies (2)(a)"):
The relation `a^{-1} + h^0 ∘ d_M^{-1} = 0` exhibits `h^0` as a homotopy from `a`
to a morphism of complexes `(a')^• : M → K` with `(a')^{-1} = 0` (degree `-1` of
the homotopy formula; in degrees `≠ -1` the homotopy term is `0` or absorbed since
`K^i = 0` for `i ∉ {-1,0}` and `M^i = 0` for `i > 0`). In `D(R)`, `Q.map a =
Q.map a'`, so it suffices to show `Ext^1(a', N) = 0`. Let `N → I^•` be an injective
resolution; by `CochainComplex.IsKInjective.Qh_map_bijective` (Stacks 05TG),
`Ext^1(K,N) = Hom_{D(R)}(K, I[1]) = Hom_{K(R)}(K, I[1])`. Any chain map
`b^• : K → I[1]` has `b^0 : K^0 → I^1` landing in `ker(I^1 → I^2) = im(I^0 → I^1)`
(as `K^1 = 0`); since `K^0` is projective, lift to `h : K^0 → I^0`, exhibiting `b`
as homotopic to `(b')^•` with `(b')^0 = 0`. Because `K^i = 0` for `i ∉ {-1,0}` and
`(a')^{-1} = 0`, the composite `(b')^• ∘ (a')^•` is zero as a map of complexes
(degree `-1`: factors through `(a')^{-1} = 0`; degree `0`: factors through
`(b')^0 = 0`). Hence pre-composition with `a` kills every class, i.e.
`Ext^1(a,N) = 0`. -/
theorem Q_map_comp_eq_zero_of_nullHomotopy
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) (hK0 : Projective (K.X 0))
    (a : M ⟶ K) (h0 : M.X 0 ⟶ K.X (-1))
    (hh0 : HomologicalComplex.Hom.f a (-1) + M.d (-1) 0 ≫ h0 = 0) :
    ∀ (N : ModuleCat.{v} R) (ξ : ExtMod K N 1),
        DerivedCategory.Q.map a ≫ ξ = 0 := by
  -- Strategy avoiding K-injectives: the target `T := N[1] = shiftSingle N 1` is
  -- concentrated in degree `-1`, so `T^i = 0` for `i ≤ -2`. Both `M` and `K`
  -- satisfy the hypotheses of `toHomD_bijective` (with `T` as target), so
  -- `toHomD : Hom_K(K,T) → Hom_D(K,T)` is bijective and
  -- `toHomD : Hom_K(M,T) → Hom_D(M,T)` is injective. Lift `ξ` to a chain map
  -- `b : K → T`, then show the chain map `a ≫ b : M → T` is null-homotopic using
  -- the homotopy `h0` (so its class is `0`), and conclude by injectivity.
  intro N ξ
  -- `K` satisfies the `toHomD_bijective` source hypotheses; lift `ξ`.
  obtain ⟨ξt, hξt⟩ := (toHomD_shiftSingle_bijective K N
    (fun i hi => hK i (by omega) (by omega)) hK0).surjective ξ
  -- `toHomD_bijective` for `(M, T)`: `toHomD` is injective.
  have hbijM := toHomD_shiftSingle_bijective M N hM_pos hM0
  set Qq := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  -- Naturality: `Q.map a ≫ ξ = toHomD (Qq.map a ≫ ξt)`.
  have hnat : DerivedCategory.Q.map a ≫ ξ = toHomD (Qq.map a ≫ ξt) := by
    rw [← hξt]
    exact Q_map_comp_toHomD a ξt
  -- Lift the homotopy class `ξt` to an honest chain map `b : K → T`.
  obtain ⟨b, hb⟩ := Qq.map_surjective ξt
  -- `Qq.map a ≫ ξt = Qq.map (a ≫ b)`.
  have hcompmap : Qq.map a ≫ ξt = Qq.map (a ≫ b) := by
    rw [← hb, Qq.map_comp]
  -- The chain map `a ≫ b : M → T` is null-homotopic.
  have hnull : Nonempty (Homotopy (a ≫ b) 0) := by
    set hom : (i j : ℤ) → (M.X i ⟶ (shiftSingle N 1).X j) := fun i j =>
      if hij : i = 0 ∧ j = -1 then
        eqToHom (by rw [hij.left] : M.X i = M.X 0) ≫ (-(h0 ≫ b.f (-1))) ≫
          eqToHom (by rw [hij.right] : (shiftSingle N 1).X (-1) = (shiftSingle N 1).X j)
      else 0 with hhom
    have e1 : hom 0 (-1) = -(h0 ≫ b.f (-1)) := by rw [hhom]; simp
    have e2 : hom (-1) (-2) = 0 := by
      rw [hhom]
      simp only [dite_eq_right (show ¬ ((-1:ℤ) = 0 ∧ (-2:ℤ) = -1) by rintro ⟨h1,_⟩; norm_num at h1)]
    have hzero : ∀ (i j : ℤ), ¬ (ComplexShape.up ℤ).Rel j i → hom i j = 0 := by
      intro i j hr
      rw [hhom]
      dsimp only
      rw [dite_eq_right]
      rintro ⟨hi, hj⟩
      subst hi hj
      exact hr (by simp [ComplexShape.up_Rel])
    have hcomm : ∀ (i : ℤ), (a ≫ b).f i =
        (dNext i) hom + (prevD i) hom + (0 : M ⟶ shiftSingle N 1).f i := by
      intro i
      by_cases hi : i = -1
      · subst hi
        have hrel : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 := by simp [ComplexShape.up_Rel]
        have hrel2 : (ComplexShape.up ℤ).Rel (-2 : ℤ) (-1) := by simp [ComplexShape.up_Rel]
        rw [dNext_eq hom hrel, prevD_eq hom hrel2, e1, e2]
        simp only [HomologicalComplex.zero_f, zero_comp, add_zero]
        rw [HomologicalComplex.comp_f]
        have ha : HomologicalComplex.Hom.f a (-1) = -(M.d (-1) 0 ≫ h0) := by
          rw [eq_neg_iff_add_eq_zero]; exact hh0
        rw [ha]
        simp [Category.assoc]
      · exact (isZero_shiftSingle_X (by omega)).eq_of_tgt _ _
    exact ⟨Homotopy.mk hom hzero hcomm⟩
  -- Hence the homotopy class of `a ≫ b` is `0`.
  have hzeroclass : Qq.map (a ≫ b) = 0 := by
    obtain ⟨H⟩ := hnull
    rw [HomotopyCategory.eq_of_homotopy _ _ H, Functor.map_zero]
  -- Conclude: `Q.map a ≫ ξ = toHomD 0 = 0`.
  rw [hnat, hcompmap, hzeroclass]
  exact toHomD_zero

/-- **Sub-lemma for (2), direction (2a) ⇒ (2b).** Under the hypotheses of (2), if
`Ext^1(a, N) = 0` for all `N`, then there exists `h^0 : M^0 → K^{-1}` with
`a^{-1} + h^0 ∘ d_M^{-1} = 0`.

INFORMAL ARGUMENT (Stacks 0ALN, proof of (2), "Conversely … (2)(a)"): Take
`N = K^{-1}`. There is a canonical class `κ ∈ Ext^1(K, K^{-1})` — the class of the
identity-in-degree-`-1` extension, equivalently the image under `Ext^1(K,K^{-1}) =
Hom_{K(R)}(K, K^{-1}[1])` of the chain map `K → K^{-1}[1]` that is `id` in degree
`-1`. By hypothesis (2a) its pre-composition with `a` vanishes in
`Ext^1(M, K^{-1})`. Now apply (1) (`toHomD_bijective`) with this `K^{-1}[1]` in the role of
the target: `Ext^1(M, K^{-1}) = Hom_{D(R)}(M, K^{-1}[1]) = Hom_{K(R)}(M, K^{-1}[1])`,
so the vanishing of the `D(R)`-class means the chain map `M → K^{-1}[1]` given by
`a^{-1}` (in degree `-1`) is null-homotopic. A null-homotopy is exactly a map
`h^0 : M^0 → K^{-1}` with `a^{-1} = - h^0 ∘ d_M^{-1}`, i.e. `a^{-1} + h^0 ∘
d_M^{-1} = 0`. -/
theorem exists_nullHomotopy_of_Q_map_comp_eq_zero
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (a : M ⟶ K)
    (h : ∀ (N : ModuleCat.{v} R) (ξ : ExtMod K N 1),
        DerivedCategory.Q.map a ≫ ξ = 0) :
    ∃ h0 : M.X 0 ⟶ K.X (-1),
        HomologicalComplex.Hom.f a (-1) + M.d (-1) 0 ≫ h0 = 0 := by
  -- feed the canonical class in `Ext^1(K, K^{-1})` to `h`, then use (1) to read off `h^0`.
  set N := K.X (-1)
  -- the iso identifying the degree -1 part of T with N = K.X(-1)
  have eN : N ≅ (shiftSingle N 1).X (-1) := (shiftSingleXSelf N 1).symm
  -- all differentials of T vanish.
  have hTd : ∀ i j, (shiftSingle N 1).d i j = 0 := shiftSingle_d_eq_zero N 1
  -- build the canonical chain map `κchain : K → T` (identity in degree -1).
  set kf : ∀ i, K.X i ⟶ (shiftSingle N 1).X i := fun i =>
    if hi : i = -1 then eqToHom (by rw [hi] : K.X i = N) ≫ eN.hom ≫
      eqToHom (by rw [hi] : (shiftSingle N 1).X (-1) = (shiftSingle N 1).X i)
    else 0 with hkf
  set κchain : K ⟶ shiftSingle N 1 := HomologicalComplex.Hom.mk kf (by
    intro i j hij
    rw [hTd]
    simp only [comp_zero]
    -- goal: K.d i j ≫ kf j = 0
    by_cases hj : j = -1
    · -- j = -1, so i = -2
      have hi : i = -2 := by
        simp only [ComplexShape.up_Rel] at hij; omega
      have hKi : IsZero (K.X i) := by rw [hi]; exact hK (-2) (by norm_num) (by norm_num)
      rw [hKi.eq_zero_of_src (K.d i j)]
      simp
    · -- j ≠ -1, kf j = 0
      have hzj : kf j = 0 := by rw [hkf]; simp [hj]
      rw [hzj]; simp) with hκchain
  -- the homotopy quotient functor.
  set Qq := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  -- the canonical class κ ∈ Ext^1(K, N).
  set κ : ExtMod K N 1 := toHomD (Qq.map κchain) with hκdef
  -- apply (2a) to κ.
  have hkill : DerivedCategory.Q.map a ≫ κ = 0 := h N κ
  -- identify the composite with `toHomD (Qq.map (a ≫ κchain))`.
  have hcomp : DerivedCategory.Q.map a ≫ κ = toHomD (Qq.map (a ≫ κchain)) := by
    have h1 : DerivedCategory.Q.map a ≫ κ = toHomD (Qq.map a ≫ Qq.map κchain) := by
      rw [hκdef]; exact Q_map_comp_toHomD a (Qq.map κchain)
    rw [h1, ← Functor.map_comp]
  -- so `toHomD (Qq.map (a ≫ κchain)) = 0`.
  have hzero : toHomD (Qq.map (a ≫ κchain)) = 0 := by rw [← hcomp]; exact hkill
  -- by toHomD_bijective (M, T) INJECTIVITY of toHomD, the class `Qq.map (a ≫ κchain)` is 0.
  have hclzero : Qq.map (a ≫ κchain) = 0 := by
    apply (toHomD_shiftSingle_bijective M N hM_pos hM0).injective
    show toHomD (Qq.map (a ≫ κchain)) = toHomD (0 : HomK M (shiftSingle N 1))
    rw [hzero, toHomD_zero]
  -- hence `a ≫ κchain` is null-homotopic.
  have hnull : Nonempty (Homotopy (a ≫ κchain) 0) := by
    refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
    rw [hclzero, Functor.map_zero]
  obtain ⟨H⟩ := hnull
  -- extract h0 from the null-homotopy.
  refine ⟨-(H.hom 0 (-1) ≫ eN.inv), ?_⟩
  have hrel : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 := by simp [ComplexShape.up_Rel]
  have hrel2 : (ComplexShape.up ℤ).Rel (-2 : ℤ) (-1) := by simp [ComplexShape.up_Rel]
  have hcomm := H.comm (-1)
  rw [dNext_eq H.hom hrel, prevD_eq H.hom hrel2, hTd] at hcomm
  simp only [comp_zero, add_zero, HomologicalComplex.zero_f] at hcomm
  -- hcomm : (a ≫ κchain).f (-1) = M.d (-1) 0 ≫ H.hom 0 (-1)
  rw [HomologicalComplex.comp_f] at hcomm
  -- κchain.f (-1) ≫ eN.inv = 𝟙 (K.X (-1))
  have hf1 : κchain.f (-1) ≫ eN.inv = 𝟙 (K.X (-1)) := by
    have he : κchain.f (-1) = kf (-1) := rfl
    rw [he, hkf]
    simp only [dite_eq_left, eqToHom_refl, Category.comp_id, Category.id_comp]
    rw [Iso.hom_inv_id]
  -- postcompose hcomm with eN.inv
  have key := congrArg (· ≫ eN.inv) hcomm
  simp only [Category.assoc] at key
  rw [hf1] at key
  -- key : a.f (-1) ≫ 𝟙 = M.d (-1) 0 ≫ (H.hom 0 (-1) ≫ eN.inv)
  rw [Category.comp_id] at key
  -- key : a.f (-1) = M.d (-1) 0 ≫ (H.hom 0 (-1) ≫ eN.inv)
  rw [key]
  rw [Preadditive.comp_neg, ← Category.assoc]
  abel

/-- **(2)** Assume `K^i = 0` for `i ∉ {-1, 0}` and that `K^0` is projective.
For a morphism of complexes `a : M → K`, condition (2a) — that for every module
`N` the induced map `Ext^1(a, N) : Ext^1(K, N) → Ext^1(M, N)`, given by
pre-composition with `Q.map a`, is the zero map — is equivalent to (2b) — the
existence of an `R`-module homomorphism `h^0 : M^0 → K^{-1}` with
`a^{-1} + h^0 ∘ d_M^{-1} = 0`.

PROOF SKETCH: the two implications are `Q_map_comp_eq_zero_of_nullHomotopy`
((2b)⇒(2a)) and `exists_nullHomotopy_of_Q_map_comp_eq_zero` ((2a)⇒(2b)); assemble
with `Iff.intro`. -/
@[stacks 0ALN "(2)"]
theorem forall_Q_map_comp_eq_zero_iff
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) (hK0 : Projective (K.X 0))
    (a : M ⟶ K) :
    (∀ (N : ModuleCat.{v} R) (ξ : ExtMod K N 1),
        DerivedCategory.Q.map a ≫ ξ = 0)
      ↔
    (∃ h0 : M.X 0 ⟶ K.X (-1),
        HomologicalComplex.Hom.f a (-1) + M.d (-1) 0 ≫ h0 = 0) :=
  ⟨exists_nullHomotopy_of_Q_map_comp_eq_zero M K hM_pos hM0 hK a,
   fun ⟨h0, hh0⟩ => Q_map_comp_eq_zero_of_nullHomotopy M K hM_pos hM0 hK hK0 a h0 hh0⟩

end TwoTermComplexExt

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeDegreeVanishing

/-!
# Vanishing of the bottom edge of the Grothendieck spectral sequence in one degree

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors of abelian categories with enough
injectives, `F` left exact and preserving injective objects. In the Grothendieck spectral
sequence `E₂^{s,p} = R^sG(R^pF(X)) ⟹ R^{s+p}(G ∘ F)(X)` the bottom row is `E₂^{n,0} = R^nG(F X)`,
and the differentials leaving it land in `E_r^{n+r, 1-r} = 0`, while those reaching it come from
`E_r^{n-r, r-1}`. So `R^nG(F X) = 0` as soon as the abutment `R^n(G ∘ F)(X)` vanishes and so do
the terms `R^sG(R^pF(X))` with `p ≥ 1` and `s + p = n - 1`.

This file proves that consequence directly, without a spectral sequence: the truncation triangle
`τ^{≤0}RF(X) ⟶ RF(X) ⟶ τ^{≥1}RF(X)` in `D⁺(ℬ)`, with `τ^{≤0}RF(X) = F(X)[0]` by left exactness,
has `Hⁿ⁻¹(RG(τ^{≥1}RF(X))) = 0` by the Postnikov induction
`Stacks.CompositeDegreeVanishing.isZero_homology_map_obj_of_isZero_single`.

For `F = j_*` and `G = Γ(X, -)` this is the form of the Leray spectral sequence used to bound
`H^q(X, j_*𝓖)` in the proof that `cd(X) ≤ 2 dim X`.

## Main results

* `Stacks.CompositeDegreeVanishing.isZero_rightDerived_obj_of_isZero_comp_of_isZero`.

## References

* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.CompositeDegreeVanishing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {A B E : Type*} [Category A] [Category B] [Category E]
  [Abelian A] [Abelian B] [Abelian E] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
  [F.PreservesInjectiveObjects] [PreservesFiniteLimits F]

/-- **The bottom edge of the Grothendieck spectral sequence vanishes in degree `n`** (Stacks
015N, read on the row `p = 0`). Let `F : 𝒜 ⥤ ℬ` be additive, left exact and preserving injective
objects, and `G : ℬ ⥤ 𝒞` additive. If `R^n(G ∘ F)(X) = 0` and `R^sG(R^pF(X)) = 0` whenever
`p ≥ 1` and `p + s + 1 = n`, then `R^nG(F X) = 0`. The derived categories used in the proof are
the standard models; the statement involves none. -/
theorem isZero_rightDerived_obj_of_isZero_comp_of_isZero (X : A) (n : ℕ)
    (h₀ : IsZero (((F ⋙ G).rightDerived n).obj X))
    (h : ∀ p s : ℕ, 1 ≤ p → p + s + 1 = n →
      IsZero ((G.rightDerived s).obj ((F.rightDerived p).obj X))) :
    IsZero ((G.rightDerived n).obj (F.obj X)) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard B
  let := HasDerivedCategory.standard E
  let t : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus B) :=
    DerivedCategory.Plus.TStructure.t
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  have hK0 : K.IsGE 0 := Functor.isGE_rightDerivedFunctorPlus_obj F _ 0
  let Gd := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  have hGE : ∀ (L : DerivedCategory.Plus B) (a : ℤ), L.IsGE a → (Gd.obj L).IsGE a := by
    intro L a hL
    have := Functor.isGE_rightDerivedFunctorPlus_obj G L a
    show (DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj L)).IsGE a
    infer_instance
  let T := (t.triangleLEGE 0 1 rfl).obj K
  have hT : T ∈ distTriang (DerivedCategory.Plus B) := t.triangleLEGE_distinguished 0 1 rfl K
  -- the abutment: `Hⁿ(RG(RF X)) = Rⁿ(G ∘ F)(X) = 0`
  have h₂ : IsZero ((DerivedCategory.homologyFunctor E n).obj (Gd.obj T.obj₂)) := by
    have h₀' := (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (F ⋙ G) n X).1 h₀
    exact h₀'.of_iso ((DerivedCategory.homologyFunctor E n).mapIso
      (DerivedCategory.Plus.ι.mapIso ((Stacks.DerivedIndexing.rightDerivedPlusCompIso F G).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X)))).symm
  -- the higher rows: `Hⁿ⁻¹(RG(τ^{≥1} RF X)) = 0`
  have h₃ : IsZero ((DerivedCategory.homologyFunctor E ((n : ℤ) - 1)).obj (Gd.obj T.obj₃)) := by
    have hT3 : T.obj₃.IsGE 1 := by
      show ((t.truncGE 1).obj K).IsGE 1
      infer_instance
    refine isZero_homology_map_obj_of_isZero_single Gd hGE T.obj₃ 1 ((n : ℤ) - 1)
      fun q hq => ?_
    refine (isZero_homology_rightDerivedFunctorPlus_single_iff G _ ((n : ℤ) - 1) q).2 ?_
    rcases lt_or_ge q 1 with hneg | hpos
    · exact Functor.map_isZero (DerivedCategory.Plus.singleFunctor B 0 ⋙
        G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor E ((n : ℤ) - 1 - q))
        (DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃ 1 q hneg)
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = p := ⟨q.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
      have hp1 : 1 ≤ p := by exact_mod_cast hpos
      obtain ⟨s, hs⟩ : ∃ s : ℕ, p + s + 1 = n := ⟨n - 1 - p, by omega⟩
      have hiso : IsIso ((DerivedCategory.Plus.homologyFunctor B p).map ((t.truncGEπ 1).app K)) :=
        DerivedCategory.Plus.isIso_homologyMap_truncGEπ_app 1 p (by omega) K
      have eH : (DerivedCategory.Plus.homologyFunctor B p).obj T.obj₃ ≅
          (F.rightDerived p).obj X :=
        (@asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor B p).map ((t.truncGEπ 1).app K))
          hiso).symm ≪≫ ((Stacks.DerivedIndexing.rightDerivedIso F p).app X).symm
      rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff G
        (show (n : ℤ) - 1 - p = (s : ℤ) by omega)]
      exact (h p s hp1 hs).of_iso ((G.rightDerived s).mapIso eH)
  -- hence `Hⁿ(RG(τ^{≤0} RF X)) = 0`
  have h₁ : IsZero ((DerivedCategory.homologyFunctor E n).obj (Gd.obj T.obj₁)) :=
    (DerivedCategory.HomologySequence.exact₁ (Gd.mapTriangle.obj T)
      (Gd.map_distinguished T hT) ((n : ℤ) - 1) n (by omega)).isZero_X₂
      (h₃.eq_of_src _ _) (h₂.eq_of_tgt _ _)
  -- and `τ^{≤0} RF X = (F X)[0]`
  have hT1GE : T.obj₁.IsGE 0 := by
    show ((t.truncLE 0).obj K).IsGE 0
    infer_instance
  have hT1LE : T.obj₁.IsLE 0 := by
    show ((t.truncLE 0).obj K).IsLE 0
    infer_instance
  obtain ⟨M, ⟨e⟩⟩ := Stacks.BoundedCohomologicalDimension.exists_iso_plus_singleFunctor_obj
    T.obj₁ 0
  have heH : (DerivedCategory.Plus.homologyFunctor B 0).obj T.obj₁ ≅ M :=
    (DerivedCategory.Plus.homologyFunctor B 0).mapIso e ≪≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := B) 0).app M
  have eM : M ≅ F.obj X :=
    heH.symm ≪≫ @asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor B 0).map
        ((t.truncLEι 0).app K))
      (Stacks.BoundedCohomologicalDimension.isIso_plus_homologyMap_truncLEι K 0 0 le_rfl) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso F 0).app X).symm ≪≫
      F.rightDerivedZeroIsoSelf.app X
  have h₁' : IsZero ((DerivedCategory.homologyFunctor E n).obj (Gd.obj
      ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)))) :=
    h₁.of_iso ((DerivedCategory.homologyFunctor E n).mapIso
      (Gd.mapIso (e ≪≫ (DerivedCategory.Plus.singleFunctor B 0).mapIso eM))).symm
  have h₁'' := (isZero_homology_rightDerivedFunctorPlus_single_iff G (F.obj X) n 0).1 h₁'
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff G
    (show (n : ℤ) - 0 = (n : ℤ) by omega)] at h₁''
  exact h₁''

end Stacks.CompositeDegreeVanishing

end

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeDegreeVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# The bottom edge of the Grothendieck spectral sequence, as a vanishing criterion

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors of abelian categories with enough
injectives, `F` left exact and preserving injective objects. In the Grothendieck spectral
sequence `E₂^{p,q} = R^pG(R^qF(X)) ⟹ R^{p+q}(G ∘ F)(X)` the bottom row `E₂^{n,0} = R^nG(F(X))`
only receives differentials from the terms `E₂^{n-1-q,q}` with `q ≥ 1`. So if these terms vanish,
the edge map `R^nG(F(X)) ⟶ R^n(G ∘ F)(X)` is injective, and `R^nG(F(X)) = 0` as soon as
`R^n(G ∘ F)(X) = 0`.

This file proves that consequence directly, without a spectral sequence, from the truncation
triangle `F(X)[0] ⟶ RF(X) ⟶ τ^{≥1}RF(X)` in `D⁺(ℬ)` and the Postnikov estimate
`Stacks.CompositeDegreeVanishing.isZero_homology_map_obj_of_isZero_single` applied to its third
vertex. It is the companion of
`Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero`, which reads the same
spectral sequence along an antidiagonal.

## Main results

* `Stacks.CompositeDegreeVanishing.isZero_rightDerived_obj_map_of_isZero`: if
  `R^n(G ∘ F)(X) = 0` and `R^{n-1-q}G(R^qF(X)) = 0` for every `1 ≤ q ≤ n - 1`, then
  `R^nG(F(X)) = 0`.

## References

* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.CompositeDegreeVanishing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {A B E : Type*} [Category A] [Category B] [Category E]
  [Abelian A] [Abelian B] [Abelian E] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive] [F.PreservesInjectiveObjects]

/-- **The bottom edge of the Grothendieck spectral sequence** (Stacks 015N). Let `F : 𝒜 ⥤ ℬ`
be left exact, additive and preserving injective objects, and `G : ℬ ⥤ 𝒞` additive, the
categories having enough injectives. If `R^n(G ∘ F)(X) = 0` and `R^{n-1-q}G(R^qF(X)) = 0` for
every `q` with `1 ≤ q ≤ n - 1`, then `R^nG(F(X)) = 0`. -/
theorem isZero_rightDerived_obj_map_of_isZero [PreservesFiniteLimits F] (X : A) (n : ℕ)
    (hc : IsZero (((F ⋙ G).rightDerived n).obj X))
    (h : ∀ q : ℕ, 1 ≤ q → q + 1 ≤ n →
      IsZero ((G.rightDerived (n - 1 - q)).obj ((F.rightDerived q).obj X))) :
    IsZero ((G.rightDerived n).obj (F.obj X)) := by
  let t : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus B) :=
    DerivedCategory.Plus.TStructure.t
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  have hK0 : K.IsGE 0 := Functor.isGE_rightDerivedFunctorPlus_obj F _ 0
  let Gd := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  have hGE : ∀ (L : DerivedCategory.Plus B) (a : ℤ), L.IsGE a → (Gd.obj L).IsGE a := by
    intro L a hL
    have := Functor.isGE_rightDerivedFunctorPlus_obj G L a
    change (DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj L)).IsGE a
    infer_instance
  let T := (t.triangleLEGE 0 1 rfl).obj K
  have h₂ : IsZero ((DerivedCategory.homologyFunctor E n).obj (Gd.obj T.obj₂)) := by
    rw [Stacks.DerivedIndexing.isZero_rightDerived_obj_iff] at hc
    exact hc.of_iso ((DerivedCategory.homologyFunctor E n).mapIso
      (DerivedCategory.Plus.ι.mapIso ((Stacks.DerivedIndexing.rightDerivedPlusCompIso F G).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X)))).symm
  have h₃ : IsZero ((DerivedCategory.homologyFunctor E ((n : ℤ) - 1)).obj (Gd.obj T.obj₃)) := by
    have hthird : T.obj₃.IsGE 1 := by
      change ((t.truncGE 1).obj K).IsGE 1
      infer_instance
    refine isZero_homology_map_obj_of_isZero_single Gd hGE T.obj₃ 1 ((n : ℤ) - 1)
      fun q hq => (isZero_homology_rightDerivedFunctorPlus_single_iff G _ _ q).2 ?_
    rcases lt_or_ge q 1 with hneg | hpos
    · exact Functor.map_isZero (DerivedCategory.Plus.singleFunctor B 0 ⋙
        G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor E _)
        (DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃ 1 q hneg)
    · obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
      have hIso : IsIso ((DerivedCategory.Plus.homologyFunctor B q').map T.mor₂) := by
        change IsIso ((DerivedCategory.Plus.homologyFunctor B q').map ((t.truncGEπ 1).app K))
        simpa [t] using DerivedCategory.Plus.isIso_homologyMap_truncGEπ_app 1 q' hpos K
      rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff G
        (show (n : ℤ) - 1 - q' = ((n - 1 - q' : ℕ) : ℤ) by omega)]
      exact (h q' (by omega) (by omega)).of_iso ((G.rightDerived (n - 1 - q')).mapIso
        (((Stacks.DerivedIndexing.rightDerivedIso F q').app X) ≪≫
          (@asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor B q').map T.mor₂) hIso))).symm
  have h₁ : IsZero ((DerivedCategory.homologyFunctor E n).obj (Gd.obj T.obj₁)) :=
    (DerivedCategory.HomologySequence.exact₁ (Gd.mapTriangle.obj T)
      (Gd.map_distinguished T (t.triangleLEGE_distinguished 0 1 rfl K)) ((n : ℤ) - 1) n
      (by omega)).isZero_X₂ (h₃.eq_of_src _ _) (h₂.eq_of_tgt _ _)
  have hfirstGE : T.obj₁.IsGE 0 := by
    change ((t.truncLE 0).obj K).IsGE 0
    infer_instance
  have hfirstLE : T.obj₁.IsLE 0 := by
    change ((t.truncLE 0).obj K).IsLE 0
    infer_instance
  obtain ⟨M, ⟨e⟩⟩ := Stacks.BoundedCohomologicalDimension.exists_iso_plus_singleFunctor_obj T.obj₁ 0
  have hM : IsZero ((G.rightDerivedPlus (n : ℤ)).obj M) := by
    simpa using (isZero_homology_rightDerivedFunctorPlus_single_iff G M n 0).1
      (h₁.of_iso ((DerivedCategory.homologyFunctor E n).mapIso (Gd.mapIso e)).symm)
  have heM : M ≅ F.obj X :=
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := B) 0).app M).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor B 0).mapIso e.symm ≪≫
      @asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor B 0).map
        ((t.truncLEι 0).app K))
        (Stacks.BoundedCohomologicalDimension.isIso_plus_homologyMap_truncLEι K 0 0 le_rfl) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso F 0).app X).symm ≪≫
      F.rightDerivedZeroIsoSelf.app X
  rw [Stacks.DerivedIndexing.isZero_rightDerived_obj_iff]
  exact hM.of_iso ((G.rightDerivedPlus _).mapIso heM).symm

end Stacks.CompositeDegreeVanishing

end

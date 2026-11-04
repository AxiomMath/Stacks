module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# Vanishing of the derived functor of a composite in one degree

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors of abelian categories with enough
injectives, `F` preserving injective objects. The Grothendieck spectral sequence
`E₂^{p,q} = R^pG(R^qF(X)) ⟹ R^{p+q}(G ∘ F)(X)` shows that `R^n(G ∘ F)(X) = 0` as soon as every
term `E₂^{n-q,q}` of the `n`-th antidiagonal vanishes. This file proves that consequence directly,
without a spectral sequence, by a finite Postnikov induction along the truncation triangles of
`RF(X)` in `D⁺(ℬ)`.

This is the form in which the Leray spectral sequence is used in the cohomological dimension
estimates of the chapter on étale cohomology (Stacks 0F0S, 0F0V, 0F0X): one bounds the terms
`H^p(Y, R^qf_*𝓕)` and concludes the vanishing of `H^n(X, 𝓕)`.

## Main results

* `Stacks.CompositeDegreeVanishing.isZero_homology_map_obj_of_isZero_single`: for a triangulated
  `G : D⁺(𝒞) ⥤ D(𝒟)` moving cohomology to the right, `Hʲ(G K) = 0` as soon as
  `Hʲ(G(H^q(K)[-q])) = 0` for every `q ≤ j`.
* `Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero`: if
  `R^{n-q}G(R^qF(X)) = 0` for every `q ≤ n`, then `R^n(G ∘ F)(X) = 0`, in Mathlib's `ℕ`-indexed
  right derived functors.

## References

* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.CompositeDegreeVanishing

section Postnikov

variable {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  (G : DerivedCategory.Plus C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]

/-- The vanishing of `Hʲ(G(H^q(K)[-q]))` only depends on `H^q(K)` up to isomorphism. -/
private theorem isZero_homology_single_of_iso (G : DerivedCategory.Plus C ⥤ DerivedCategory D)
    {K L : DerivedCategory.Plus C} (j q : ℤ)
    (e : (DerivedCategory.Plus.homologyFunctor C q).obj K ≅
      (DerivedCategory.Plus.homologyFunctor C q).obj L)
    (h : IsZero ((DerivedCategory.homologyFunctor D j).obj
      (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj
        ((DerivedCategory.Plus.homologyFunctor C q).obj K))))) :
    IsZero ((DerivedCategory.homologyFunctor D j).obj
      (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj
        ((DerivedCategory.Plus.homologyFunctor C q).obj L)))) :=
  h.of_iso ((DerivedCategory.homologyFunctor D j).mapIso
    (G.mapIso ((DerivedCategory.Plus.singleFunctor C q).mapIso e.symm)))

/-- If `K` is concentrated in degree `a` and `Hʲ(G(H^a(K)[-a])) = 0`, then `Hʲ(G K) = 0`. -/
private theorem isZero_homology_obj_of_isGE_of_isLE (G : DerivedCategory.Plus C ⥤ DerivedCategory D)
    (K : DerivedCategory.Plus C) (a j : ℤ) [K.IsGE a] [K.IsLE a]
    (h : IsZero ((DerivedCategory.homologyFunctor D j).obj
      (G.obj ((DerivedCategory.Plus.singleFunctor C a).obj
        ((DerivedCategory.Plus.homologyFunctor C a).obj K))))) :
    IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj K)) := by
  obtain ⟨M, ⟨e⟩⟩ := Stacks.BoundedCohomologicalDimension.exists_iso_plus_singleFunctor_obj K a
  have heH : (DerivedCategory.Plus.homologyFunctor C a).obj K ≅ M :=
    (DerivedCategory.Plus.homologyFunctor C a).mapIso e ≪≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) a).app M
  exact h.of_iso ((DerivedCategory.homologyFunctor D j).mapIso
    (G.mapIso (e ≪≫ (DerivedCategory.Plus.singleFunctor C a).mapIso heH.symm)))

/-- **Postnikov induction for one cohomology group.** Let `K` live in the degrees
`[a, a + n]`. If `Hʲ(G(H^q(K)[-q])) = 0` for every `q` in that window, then `Hʲ(G K) = 0`. -/
theorem isZero_homology_map_obj_of_bounded (j : ℤ) :
    ∀ (a : ℤ) (n : ℕ) (K : DerivedCategory.Plus C), K.IsGE a → K.IsLE (a + n) →
      (∀ q : ℤ, a ≤ q → q ≤ a + n → IsZero ((DerivedCategory.homologyFunctor D j).obj
        (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj
          ((DerivedCategory.Plus.homologyFunctor C q).obj K))))) →
      IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj K)) := by
  intro a n
  induction n with
  | zero =>
    intro K hGE hLE hq
    have : K.IsGE a := hGE
    have : K.IsLE a := by simpa using hLE
    exact isZero_homology_obj_of_isGE_of_isLE G K a j (hq a le_rfl (by simp))
  | succ n ih =>
    intro K hGE hLE hq
    let b := a + (n : ℤ) + 1
    let t : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus C) :=
      DerivedCategory.Plus.TStructure.t
    let T₀ := (t.triangleLEGE (b - 1) b (by omega)).obj K
    have hT : G.mapTriangle.obj T₀ ∈ distTriang (DerivedCategory D) :=
      G.map_distinguished T₀ (t.triangleLEGE_distinguished (b - 1) b (by omega) K)
    have h₁ : IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj T₀.obj₁)) := by
      have hτGE : T₀.obj₁.IsGE a := by
        have : K.IsGE a := hGE
        show ((t.truncLE (b - 1)).obj K).IsGE a
        infer_instance
      refine ih T₀.obj₁ hτGE (t.isLE_truncLE_obj K (b - 1) (a + n) (by omega)) fun q haq hqb => ?_
      exact isZero_homology_single_of_iso G j q
        (@asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor C q).map
          ((t.truncLEι (b - 1)).app K))
          (Stacks.BoundedCohomologicalDimension.isIso_plus_homologyMap_truncLEι K (b - 1) q
            (by omega))).symm (hq q haq (by push_cast; omega))
    have h₃ : IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj T₀.obj₃)) := by
      have : T₀.obj₃.IsGE b := by
        show ((t.truncGE b).obj K).IsGE b
        infer_instance
      have : T₀.obj₃.IsLE b := by
        have : K.IsLE b := by simpa [b, Nat.cast_succ, add_assoc] using hLE
        show ((t.truncGE b).obj K).IsLE b
        infer_instance
      have hIso : IsIso ((DerivedCategory.Plus.homologyFunctor C b).map T₀.mor₂) := by
        show IsIso ((DerivedCategory.Plus.homologyFunctor C b).map ((t.truncGEπ b).app K))
        simpa [t] using DerivedCategory.Plus.isIso_homologyMap_truncGEπ_app b b le_rfl K
      exact isZero_homology_obj_of_isGE_of_isLE G _ b j
        (isZero_homology_single_of_iso G j b (@asIso _ _ _ _ _ hIso)
          (hq b (by omega) (by push_cast; omega)))
    exact (DerivedCategory.HomologySequence.exact₂ (G.mapTriangle.obj T₀) hT j).isZero_X₂
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- **One cohomology group of the image vanishes when every contribution to it does.** Let
`G : D⁺(𝒞) ⥤ D(𝒟)` be triangulated and move cohomology to the right. If `K` is in `D⁺(𝒞)` and
`Hʲ(G(H^q(K)[-q])) = 0` for every `q ≤ j`, then `Hʲ(G K) = 0`. -/
theorem isZero_homology_map_obj_of_isZero_single
    (hGE : ∀ (K : DerivedCategory.Plus C) (a : ℤ), K.IsGE a → (G.obj K).IsGE a)
    (K : DerivedCategory.Plus C) (a : ℤ) [K.IsGE a] (j : ℤ)
    (hK : ∀ q : ℤ, q ≤ j → IsZero ((DerivedCategory.homologyFunctor D j).obj
      (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj
        ((DerivedCategory.Plus.homologyFunctor C q).obj K))))) :
    IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj K)) := by
  let t : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus C) :=
    DerivedCategory.Plus.TStructure.t
  let T := (t.triangleLEGE j (j + 1) rfl).obj K
  have hT : T ∈ distTriang (DerivedCategory.Plus C) := t.triangleLEGE_distinguished j (j + 1) rfl K
  have h₃ : IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj T.obj₃)) := by
    have : T.obj₃.IsGE (j + 1) := by
      show ((t.truncGE (j + 1)).obj K).IsGE _
      infer_instance
    have := hGE T.obj₃ (j + 1) this
    exact (G.obj T.obj₃).isZero_of_isGE (j + 1) j (by omega)
  have h₁ : IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj T.obj₁)) := by
    have : K.IsGE (min a j) := t.isGE_of_ge K (min a j) a (min_le_left _ _)
    have hGE₁ : T.obj₁.IsGE (min a j) := by
      show ((t.truncLE j).obj K).IsGE _
      infer_instance
    have hlen : min a j + ((j - min a j).toNat : ℤ) = j := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr (min_le_right _ _))]
      omega
    have hLE₁ : T.obj₁.IsLE (min a j + ((j - min a j).toNat : ℤ)) := by
      rw [hlen]
      show ((t.truncLE j).obj K).IsLE j
      infer_instance
    refine isZero_homology_map_obj_of_bounded G j (min a j) _ T.obj₁ hGE₁ hLE₁
      fun q _ hq => ?_
    have hqj : q ≤ j := by omega
    exact isZero_homology_single_of_iso G j q
      (@asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor C q).map ((t.truncLEι j).app K))
        (Stacks.BoundedCohomologicalDimension.isIso_plus_homologyMap_truncLEι K j q hqj)).symm
      (hK q hqj)
  exact (DerivedCategory.HomologySequence.exact₂ (G.mapTriangle.obj T)
    (G.map_distinguished T hT) j).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end Postnikov

section Composite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {A B E : Type*} [Category A] [Category B] [Category E]
  [Abelian A] [Abelian B] [Abelian E] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]

/-- `Hⁿ(RG(M[-q])) = R^{n-q}G(M)`: the cohomology of the derived functor at a single object
placed in degree `q`, read in the `ℤ`-indexed right derived functors. -/
theorem isZero_homology_rightDerivedFunctorPlus_single_iff (M : B) (n q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor E n).obj (DerivedCategory.Plus.ι.obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B q).obj M)))) ↔
      IsZero ((G.rightDerivedPlus (n - q)).obj M) := by
  let Gd := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  let M₀ := (DerivedCategory.Plus.singleFunctor B 0).obj M
  have eM : (DerivedCategory.Plus.singleFunctor B q).obj M ≅ M₀⟦-q⟧ :=
    (((DerivedCategory.Plus.singleFunctors B).shiftIso (-q) q 0 (by omega)).app M).symm
  let e : (DerivedCategory.homologyFunctor E n).obj (Gd.obj
      ((DerivedCategory.Plus.singleFunctor B q).obj M)) ≅
      (G.rightDerivedPlus (n - q)).obj M :=
    (DerivedCategory.homologyFunctor E n).mapIso (Gd.mapIso eM ≪≫ (Gd.commShiftIso (-q)).app M₀) ≪≫
      ((DerivedCategory.homologyFunctor E 0).shiftIso (-q) n (n - q) (by omega)).app (Gd.obj M₀)
  exact e.isZero_iff

variable [F.PreservesInjectiveObjects]

/-- **Vanishing of the derived functor of a composite in one degree** (the antidiagonal of the
Grothendieck spectral sequence, Stacks 015N). Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive
functors of abelian categories with enough injectives, `F` preserving injective objects. If
`R^{n-q}G(R^qF(X)) = 0` for every `q ≤ n`, then `R^n(G ∘ F)(X) = 0`. -/
theorem isZero_rightDerived_comp_obj_of_isZero (X : A) (n : ℕ)
    (h : ∀ q : ℕ, q ≤ n → IsZero ((G.rightDerived (n - q)).obj ((F.rightDerived q).obj X))) :
    IsZero (((F ⋙ G).rightDerived n).obj X) := by
  rw [Stacks.DerivedIndexing.isZero_rightDerived_obj_iff]
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  have : K.IsGE 0 := Functor.isGE_rightDerivedFunctorPlus_obj F _ 0
  let Gd := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  have hGE : ∀ (L : DerivedCategory.Plus B) (a : ℤ), L.IsGE a → (Gd.obj L).IsGE a := by
    intro L a hL
    have := Functor.isGE_rightDerivedFunctorPlus_obj G L a
    show (DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj L)).IsGE a
    infer_instance
  have key : IsZero ((DerivedCategory.homologyFunctor E n).obj (Gd.obj K)) := by
    refine isZero_homology_map_obj_of_isZero_single Gd hGE K 0 n fun q hq => ?_
    refine (isZero_homology_rightDerivedFunctorPlus_single_iff G _ n q).2 ?_
    rcases lt_or_ge q 0 with hneg | hnn
    · exact Functor.map_isZero (DerivedCategory.Plus.singleFunctor B 0 ⋙
        G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor E (n - q))
        (DerivedCategory.Plus.isZero_homology_of_isGE K 0 q hneg)
    · obtain ⟨q', rfl⟩ : ∃ q' : ℕ, q = q' := ⟨q.toNat, (Int.toNat_of_nonneg hnn).symm⟩
      have hq' : q' ≤ n := by exact_mod_cast hq
      rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff G
        (show (n : ℤ) - q' = ((n - q' : ℕ) : ℤ) by push_cast [hq']; ring)]
      exact (h q' hq').of_iso ((G.rightDerived (n - q')).mapIso
        ((Stacks.DerivedIndexing.rightDerivedIso F q').app X).symm)
  exact key.of_iso ((DerivedCategory.homologyFunctor E n).mapIso
    (DerivedCategory.Plus.ι.mapIso ((Stacks.DerivedIndexing.rightDerivedPlusCompIso F G).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj X))))

end Composite

end Stacks.CompositeDegreeVanishing

end

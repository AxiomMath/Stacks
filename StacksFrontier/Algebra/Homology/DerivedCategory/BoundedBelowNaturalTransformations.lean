module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory

/-!
# Invertibility of a natural transformation on bounded below objects

Let `η : H₁ ⟶ H₂` be a shift-compatible natural transformation between two exact functors
`D(C) ⥤ D(D)` of derived categories, each of which carries `D^{≥m}` into `D^{≥m}` ("way-out
right" functors), and let `K` be an object of `D(C)` which is bounded below. If `η` is invertible
on each cohomology object of `K`, placed in degree zero, then it is invertible on `K` itself.

## Main results

* `DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃`: in a distinguished triangle whose third
  vertex lies in `D^{≥n}`, the first morphism is invertible on `H^i` for every `i < n`.
* `CategoryTheory.ObjectProperty.prop_singleFunctor_obj`: a strictly full subcategory stable under
  the shift contains an object placed in any degree as soon as it contains it placed in degree
  zero.
* `CategoryTheory.ObjectProperty.prop_of_isGE_of_isLE`: **the bounded case**, for an arbitrary
  strictly full triangulated subcategory.
* `CategoryTheory.NatTrans.isIso_app_singleFunctor_obj` and
  `CategoryTheory.NatTrans.isIso_app_of_isGE_of_isLE`: the two statements above read at the
  objects where `η` is invertible.
* `CategoryTheory.NatTrans.isIso_app_of_isGE`: **the theorem**, the bounded below case.
* `CategoryTheory.NatTrans.DerivedTarget.isIso_app_of_isGE`: the same statement, in the
  namespace `CategoryTheory.NatTrans.DerivedTarget`.

## References

* [Stacks Project, Tag 0D7T](https://stacks.math.columbia.edu/tag/0D7T)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u v' u'

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- **In a distinguished triangle whose third vertex is bounded below by `n`, the first morphism
is invertible on cohomology in every degree below `n`.** -/
theorem isIso_homologyMap_mor₁_of_isGE₃ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (i n : ℤ) (hGE : T.obj₃.IsGE n) (hi : i < n) :
    IsIso ((homologyFunctor C i).map T.mor₁) := by
  have := hGE
  have hepi : Epi ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff _ hT i]
    exact (isZero_of_isGE T.obj₃ n i hi).eq_zero_of_tgt _
  have hmono : Mono ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff _ hT (i - 1) i (by omega)]
    exact (isZero_of_isGE T.obj₃ n (i - 1) (by omega)).eq_zero_of_src _
  exact isIso_of_mono_of_epi _

/-- **In a distinguished triangle whose first vertex is bounded above by `n`, the second morphism
is invertible on cohomology in every degree above `n`.** -/
theorem isIso_homologyMap_mor₂_of_isLE₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (i n : ℤ) (hLE : T.obj₁.IsLE n) (hi : n < i) :
    IsIso ((homologyFunctor C i).map T.mor₂) := by
  have := hLE
  have hepi : Epi ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) (by omega)]
    exact (isZero_of_isLE T.obj₁ n (i + 1) (by omega)).eq_zero_of_tgt _
  have hmono : Mono ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff _ hT i]
    exact (isZero_of_isLE T.obj₁ n i (by omega)).eq_zero_of_src _
  exact isIso_of_mono_of_epi _

end DerivedCategory

namespace CategoryTheory.ObjectProperty

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  (P : ObjectProperty (DerivedCategory C)) [P.IsClosedUnderIsomorphisms]
  [P.IsStableUnderShift ℤ]

/-- **A strictly full subcategory stable under the shift contains an object placed in any degree
as soon as it contains it placed in degree zero.** -/
theorem prop_singleFunctor_obj (M : C) (q : ℤ) (hM : P ((singleFunctor C 0).obj M)) :
    P ((singleFunctor C q).obj M) :=
  P.prop_of_iso (((singleFunctors C).shiftIso (-q) q 0 (by omega)).app M)
    (P.le_shift (-q) _ hM)

/-- An object whose cohomology is concentrated in the single degree `c` belongs to a strictly full
triangulated subcategory as soon as its cohomology there, placed in degree zero, does. -/
theorem prop_of_isGE_of_isLE_self (K : DerivedCategory C) (c : ℤ)
    (hGE : K.IsGE c) (hLE : K.IsLE c)
    (hH : P ((singleFunctor C 0).obj ((homologyFunctor C c).obj K))) :
    P K := by
  have := hGE
  have := hLE
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K c
  refine P.prop_of_iso e.symm (P.prop_singleFunctor_obj M c ?_)
  exact P.prop_of_iso ((singleFunctor C 0).mapIso
    ((homologyFunctor C c).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C c).app M)) hH

variable [P.IsTriangulatedClosed₂]

omit [P.IsStableUnderShift ℤ] in
/-- The truncation triangle of the canonical t-structure reads membership of `K` off membership of
`τ^{<c}K` and of `τ^{≥c}K`. -/
private theorem prop_of_truncLT_of_truncGE (K : DerivedCategory C) (c : ℤ)
    (hU : P ((TStructure.t.truncLT c).obj K)) (hV : P ((TStructure.t.truncGE c).obj K)) :
    P K :=
  P.ext_of_isTriangulatedClosed₂ _ (TStructure.t.triangleLTGE_distinguished c K) hU hV

/-- **The bounded case.** If `K` has no cohomology outside the window `[a, a + n]` and each
cohomology object of `K`, placed in degree zero, lies in a strictly full triangulated subcategory
`P`, then `K` itself lies in `P`. -/
theorem prop_of_isGE_of_isLE (a : ℤ) :
    ∀ (n : ℕ) (K : DerivedCategory C), K.IsGE a → K.IsLE (a + (n : ℤ)) →
      (∀ q : ℤ, a ≤ q → q ≤ a + (n : ℤ) →
        P ((singleFunctor C 0).obj ((homologyFunctor C q).obj K))) →
      P K := by
  intro n
  induction n with
  | zero =>
    intro K hGE hLE hH
    exact P.prop_of_isGE_of_isLE_self K a hGE (by simpa using hLE) (hH a le_rfl (by omega))
  | succ n ih =>
    intro K hGE hLE hH
    have hcast : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hLE
    simp only [hcast] at hH
    have := hGE
    have := hLE
    refine P.prop_of_truncLT_of_truncGE K (a + (n : ℤ) + 1) ?_ ?_
    · refine ih _ inferInstance
        (TStructure.t.isLE_truncLT_obj K (a + (n : ℤ) + 1) (a + (n : ℤ)) (by omega))
        fun q hq₁ hq₂ ↦ ?_
      have : IsIso ((homologyFunctor C q).map
          ((TStructure.t.truncLTι (a + (n : ℤ) + 1)).app K)) :=
        isIso_homologyMap_mor₁_of_isGE₃ _
          (TStructure.t.triangleLTGE_distinguished (a + (n : ℤ) + 1) K) q
          (a + (n : ℤ) + 1) inferInstance (by omega)
      exact (P.prop_iff_of_isIso ((singleFunctor C 0).map ((homologyFunctor C q).map
        ((TStructure.t.truncLTι (a + (n : ℤ) + 1)).app K)))).mpr (hH q hq₁ (by omega))
    · refine P.prop_of_isGE_of_isLE_self _ (a + (n : ℤ) + 1) inferInstance inferInstance ?_
      have hπ : IsIso ((homologyFunctor C (a + (n : ℤ) + 1)).map
          ((TStructure.t.truncGEπ (a + (n : ℤ) + 1)).app K)) :=
        isIso_homologyMap_mor₂_of_isLE₁ _
          (TStructure.t.triangleLTGE_distinguished (a + (n : ℤ) + 1) K)
          (a + (n : ℤ) + 1) (a + (n : ℤ))
          (TStructure.t.isLE_truncLT_obj K (a + (n : ℤ) + 1) (a + (n : ℤ)) (by omega))
          (by omega)
      exact (P.prop_iff_of_isIso ((singleFunctor C 0).map
        ((homologyFunctor C (a + (n : ℤ) + 1)).map
          ((TStructure.t.truncGEπ (a + (n : ℤ) + 1)).app K)))).mp
        (hH (a + (n : ℤ) + 1) (by omega) (by omega))

end CategoryTheory.ObjectProperty

/-! ### Transformations between functors to a second derived category -/

namespace CategoryTheory.NatTrans.DerivedTarget

open DerivedCategory ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  {H₁ H₂ : DerivedCategory C ⥤ DerivedCategory D}
  [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  (η : H₁ ⟶ H₂) [NatTrans.CommShift η ℤ]

/-- The objects of `D(C)` at which `η` is invertible. -/
private abbrev isoLocus : ObjectProperty (DerivedCategory C) := fun K ↦ IsIso (η.app K)

private instance isoLocus_isTriangulated : (isoLocus η).IsTriangulated :=
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated H₁ H₂ η

private instance isoLocus_isClosedUnderIsomorphisms :
    (isoLocus η).IsClosedUnderIsomorphisms :=
  Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms η

/-- **The bounded case.** If `K` has no cohomology outside the window `[a, a + n]` and `η` is
invertible on each cohomology object of `K` placed in degree zero, then `η` is invertible at
`K`. -/
theorem isIso_app_of_isGE_of_isLE (a : ℤ) :
    ∀ (n : ℕ) (K : DerivedCategory C), K.IsGE a → K.IsLE (a + (n : ℤ)) →
      (∀ q : ℤ, a ≤ q → q ≤ a + (n : ℤ) →
        IsIso (η.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)))) →
      IsIso (η.app K) :=
  (isoLocus η).prop_of_isGE_of_isLE a

omit [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  [NatTrans.CommShift η ℤ] in
/-- The naturality square of `η` at a morphism `g`, read on cohomology in a fixed degree: if `η`
is invertible on `H^q` at the source of `g` and both `H₁` and `H₂` of `g` are invertible on
`H^q`, then `η` is invertible on `H^q` at the target of `g`. -/
private theorem isIso_homologyMap_app_of_isIso {A B : DerivedCategory C} (g : A ⟶ B) (q : ℤ)
    (h₁ : IsIso ((homologyFunctor D q).map (H₁.map g)))
    (h₂ : IsIso ((homologyFunctor D q).map (H₂.map g)))
    (hA : IsIso ((homologyFunctor D q).map (η.app A))) :
    IsIso ((homologyFunctor D q).map (η.app B)) := by
  have hcomm : (homologyFunctor D q).map (H₁.map g) ≫ (homologyFunctor D q).map (η.app B) =
      (homologyFunctor D q).map (η.app A) ≫ (homologyFunctor D q).map (H₂.map g) := by
    simpa only [Functor.map_comp] using
      congrArg (fun m ↦ (homologyFunctor D q).map m) (η.naturality g)
  have hcomp : IsIso ((homologyFunctor D q).map (H₁.map g) ≫
      (homologyFunctor D q).map (η.app B)) := by
    rw [hcomm]; infer_instance
  rwa [isIso_comp_left_iff] at hcomp

/-- **Invertibility on a bounded below object, from invertibility on its cohomology.** Let
`η : H₁ ⟶ H₂` be a shift-compatible natural transformation between exact functors
`D(C) ⥤ D(D)`, each of which carries `D^{≥m}` into `D^{≥m}`, and let `K` be an object of
`D^{≥a}`. If `η` is invertible on every cohomology object of `K` placed in degree zero, then `η`
is invertible at `K`. -/
theorem isIso_app_of_isGE
    (hH₁ : ∀ (L : DerivedCategory C) (m : ℤ), L.IsGE m → (H₁.obj L).IsGE m)
    (hH₂ : ∀ (L : DerivedCategory C) (m : ℤ), L.IsGE m → (H₂.obj L).IsGE m)
    (K : DerivedCategory C) (a : ℤ) (hGE : K.IsGE a)
    (hH : ∀ q : ℤ, IsIso (η.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)))) :
    IsIso (η.app K) := by
  have := hGE
  rw [isIso_iff]
  intro q
  by_cases haq : a ≤ q
  · have hn : ((q - a).toNat : ℤ) = q - a := Int.toNat_of_nonneg (by omega)
    have hT := TStructure.t.triangleLTGE_distinguished (q + 1) K
    have hU : IsIso (η.app ((TStructure.t.truncLT (q + 1)).obj K)) := by
      refine isIso_app_of_isGE_of_isLE η a (q - a).toNat _ inferInstance ?_ fun p hp₁ hp₂ ↦ ?_
      · rw [hn]
        exact TStructure.t.isLE_truncLT_obj K (q + 1) (a + (q - a)) (by omega)
      · rw [hn] at hp₂
        have : IsIso ((homologyFunctor C p).map ((TStructure.t.truncLTι (q + 1)).app K)) :=
          isIso_homologyMap_mor₁_of_isGE₃ _ hT p (q + 1) inferInstance (by omega)
        exact (isIso_app_iff_of_iso η ((singleFunctor C 0).mapIso
          (asIso ((homologyFunctor C p).map
            ((TStructure.t.truncLTι (q + 1)).app K))))).mpr (hH p)
    have hV : ((TStructure.t.truncGE (q + 1)).obj K).IsGE (q + 1) := inferInstance
    have h₁ : IsIso ((homologyFunctor D q).map
        (H₁.map ((TStructure.t.truncLTι (q + 1)).app K))) :=
      isIso_homologyMap_mor₁_of_isGE₃ _ (H₁.map_distinguished _ hT) q (q + 1)
        (hH₁ _ (q + 1) hV) (by omega)
    have h₂ : IsIso ((homologyFunctor D q).map
        (H₂.map ((TStructure.t.truncLTι (q + 1)).app K))) :=
      isIso_homologyMap_mor₁_of_isGE₃ _ (H₂.map_distinguished _ hT) q (q + 1)
        (hH₂ _ (q + 1) hV) (by omega)
    have hUq : IsIso ((homologyFunctor D q).map
        (η.app ((TStructure.t.truncLT (q + 1)).obj K))) := inferInstance
    exact isIso_homologyMap_app_of_isIso η ((TStructure.t.truncLTι (q + 1)).app K) q h₁ h₂ hUq
  · have := hH₁ K a hGE
    have := hH₂ K a hGE
    exact IsZero.isIso (isZero_of_isGE (H₁.obj K) a q (by omega))
      (isZero_of_isGE (H₂.obj K) a q (by omega)) _

end CategoryTheory.NatTrans.DerivedTarget

namespace CategoryTheory.NatTrans

open DerivedCategory ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  {H₁ H₂ : DerivedCategory C ⥤ DerivedCategory D}
  [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  (η : H₁ ⟶ H₂) [NatTrans.CommShift η ℤ]

/-- **Invertibility on an object placed in degree zero gives invertibility on it placed in any
degree.** -/
theorem isIso_app_singleFunctor_obj (M : C) (q : ℤ)
    (hM : IsIso (η.app ((singleFunctor C 0).obj M))) :
    IsIso (η.app ((singleFunctor C q).obj M)) :=
  (DerivedTarget.isoLocus η).prop_singleFunctor_obj M q hM

/-- **The bounded case.** If `K` has no cohomology outside the window `[a, a + n]` and `η` is
invertible on each cohomology object of `K` placed in degree zero, then `η` is invertible at
`K`. -/
alias isIso_app_of_isGE_of_isLE :=
  CategoryTheory.NatTrans.DerivedTarget.isIso_app_of_isGE_of_isLE

/-- The naturality square of `η` at a morphism `g`, read on cohomology in a fixed degree. -/
private alias isIso_homologyMap_app_of_isIso :=
  CategoryTheory.NatTrans.DerivedTarget.isIso_homologyMap_app_of_isIso

/-- **Invertibility on a bounded below object, from invertibility on its cohomology.** -/
alias isIso_app_of_isGE := CategoryTheory.NatTrans.DerivedTarget.isIso_app_of_isGE

end CategoryTheory.NatTrans

end

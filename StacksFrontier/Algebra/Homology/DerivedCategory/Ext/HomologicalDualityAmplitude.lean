module

public import StacksFrontier.CategoryTheory.Triangulated.HomologicalDualityPairing
public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExt
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Duality for a complex with cohomology in two adjacent degrees

Let `ℬ` be an abelian category and `K` an object of `D⁺(ℬ)` with cohomology only in the degrees
`a` and `a + 1`. The truncation triangle `τ_{≤ a} K → K → τ_{≥ a + 1} K → (τ_{≤ a} K)[1]` of the
canonical t-structure lives in `D⁺(ℬ)` (`Stacks.HomologicalDuality.plusTriangleLTGE`), and its
outer terms are `Hᵃ(K)[-a]` and `Hᵃ⁺¹(K)[-a-1]` (`Stacks.HomologicalDuality.plusTruncLTIso`,
`Stacks.HomologicalDuality.plusTruncGEIso`, from the top-degree projections, which are
isomorphisms for objects living in one degree, `Stacks.TopTruncationExt.isIso_topProj_of_isGE`).
So for a homological functor `H` on `D⁺(ℬ)`, duality at `Hᵃ(K)[0]` and at `Hᵃ⁺¹(K)[0]` gives
duality at `K` by the five lemma (`Stacks.HomologicalDuality.isPerfect_of_isGE_of_isLE`).

For the complex `Rf_! Λ` of an elementary fibration `f`, with cohomology `R¹f_! Λ` (locally
constant) and `R²f_! Λ ≅ Λ`, this reduces Poincaré duality for `Rf_! Λ` on the base to duality for
locally constant sheaves, in the fibration step of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.HomologicalDuality.plusTriangleLTGE`.

## Main results

* `Stacks.TopTruncationExt.isIso_topProj_of_isGE`.
* `Stacks.HomologicalDuality.plusTriangleLTGE_distinguished`.
* `Stacks.HomologicalDuality.isPerfect_of_isGE_of_isLE`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w

namespace Stacks.TopTruncationExt

/-- **The top-degree projection of an object living in degree `n` only is an isomorphism.** -/
theorem isIso_topProj_of_isGE {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (K : DerivedCategory B) (n : ℤ) (hK : K.IsLE n) [K.IsGE n] : IsIso (topProj K n hK) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  by_cases hi : i = n
  · subst hi
    have h := homologyFunctor_map_topProj K i hK
    have : IsIso ((DerivedCategory.homologyFunctor B i).map (topProj K i hK) ≫
        (singleShiftHomologyIso i).hom.app _) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((singleShiftHomologyIso i).hom.app _)
  · have : K.IsLE n := hK
    have : (((DerivedCategory.singleFunctor B 0).obj
        ((DerivedCategory.homologyFunctor B n).obj K))⟦-n⟧).IsLE n :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 (-n) n (by omega)
    rcases lt_or_gt_of_ne hi with h | h
    · exact isIso_of_source_target_iso_zero _
        (DerivedCategory.isZero_of_isGE K n i h).isoZero
        (DerivedCategory.isZero_of_isGE _ n i h).isoZero
    · exact isIso_of_source_target_iso_zero _
        (DerivedCategory.isZero_of_isLE K n i h).isoZero
        (DerivedCategory.isZero_of_isLE _ n i h).isoZero

end Stacks.TopTruncationExt

namespace Stacks.HomologicalDuality

open Stacks.TopTruncationExt DerivedCategory.TStructure

variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]

/-- `τ_{< b} X` is in degrees `≥ n` when `X` is. -/
theorem isGE_truncLT (X : DerivedCategory B) (b n : ℤ) [X.IsGE n] :
    ((t.truncLT b).obj X).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  rcases lt_or_ge i b with hb | hb
  · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι b i hb X
    exact (DerivedCategory.isZero_of_isGE X n i hi).of_iso
      (asIso ((DerivedCategory.homologyFunctor B i).map ((t.truncLTι b).app X)))
  · have : ((t.truncLT b).obj X).IsLE (b - 1) := inferInstance
    exact DerivedCategory.isZero_of_isLE _ (b - 1) i (by omega)

/-- `τ_{≥ b} X` is in degrees `≤ n` when `X` is and `b ≤ n`. -/
theorem isLE_truncGE (X : DerivedCategory B) (b n : ℤ) (hb : b ≤ n) [X.IsLE n] :
    ((t.truncGE b).obj X).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ b i (by omega) X
  exact (DerivedCategory.isZero_of_isLE X n i hi).of_iso
    (asIso ((DerivedCategory.homologyFunctor B i).map ((t.truncGEπ b).app X))).symm

variable (K : DerivedCategory.Plus B) (a : ℤ)

/-- `τ_{≤ a} K` for `K` in `D⁺(ℬ)`, as an object of `D⁺(ℬ)`. -/
def plusTruncLT : DerivedCategory.Plus B :=
  ⟨(t.truncLT (a + 1)).obj (DerivedCategory.Plus.ι.obj K), by
    obtain ⟨n, hn⟩ := K.2
    have : (DerivedCategory.Plus.ι.obj K).IsGE n := hn
    exact ⟨n, isGE_truncLT _ (a + 1) n⟩⟩

/-- `τ_{≥ a + 1} K` for `K` in `D⁺(ℬ)`, as an object of `D⁺(ℬ)`. -/
def plusTruncGE : DerivedCategory.Plus B :=
  ⟨(t.truncGE (a + 1)).obj (DerivedCategory.Plus.ι.obj K), ⟨a + 1, inferInstance⟩⟩

/-- **The truncation triangle `τ_{≤ a} K → K → τ_{≥ a + 1} K → (τ_{≤ a} K)[1]` in `D⁺(ℬ)`.** -/
def plusTriangleLTGE : Triangle (DerivedCategory.Plus B) :=
  Triangle.mk
    (t.plus.fullyFaithfulι.preimage ((t.truncLTι (a + 1)).app (DerivedCategory.Plus.ι.obj K)) :
      plusTruncLT K a ⟶ K)
    (t.plus.fullyFaithfulι.preimage ((t.truncGEπ (a + 1)).app (DerivedCategory.Plus.ι.obj K)) :
      K ⟶ plusTruncGE K a)
    (t.plus.fullyFaithfulι.preimage ((t.truncGEδLT (a + 1)).app (DerivedCategory.Plus.ι.obj K) ≫
      (t.plus.ι.commShiftIso (1 : ℤ)).inv.app (plusTruncLT K a)) :
      plusTruncGE K a ⟶ (plusTruncLT K a)⟦(1 : ℤ)⟧)

/-- The truncation triangle `τ_{≤ a} K → K → τ_{≥ a + 1} K → (τ_{≤ a} K)[1]` is distinguished in
`D⁺(ℬ)`. -/
theorem plusTriangleLTGE_distinguished : plusTriangleLTGE K a ∈ distTriang _ := by
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished (a + 1)
    (DerivedCategory.Plus.ι.obj K)) _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · dsimp [Functor.mapTriangle, Triangle.functorMk, plusTriangleLTGE]
    refine (congrArg (fun z => _ ≫ z) (CategoryTheory.Functor.map_id _ _)).trans ?_
    refine (Category.comp_id _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (CategoryStruct.comp ((t.truncGEδLT (a + 1)).app
      (DerivedCategory.Plus.ι.obj K))) (Iso.inv_hom_id_app (t.plus.ι.commShiftIso (1 : ℤ))
        (plusTruncLT K a))).trans ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- `τ_{≤ a} K ≅ Hᵃ(K)[0][-a]` when `K` is in degrees `≥ a`. -/
def plusTruncLTIso [(DerivedCategory.Plus.ι.obj K).IsGE a] :
    plusTruncLT K a ≅ ((DerivedCategory.Plus.singleFunctor B 0).obj
      ((DerivedCategory.Plus.homologyFunctor B a).obj K))⟦-a⟧ :=
  haveI : (t.plus.ι.obj (plusTruncLT K a)).IsGE a := isGE_truncLT _ (a + 1) a
  haveI : (t.plus.ι.obj (plusTruncLT K a)).IsLE a :=
    (inferInstance : ((t.truncLT (a + 1)).obj (DerivedCategory.Plus.ι.obj K)).IsLE a)
  have hI := DerivedCategory.isIso_homologyFunctor_map_truncLTι (a + 1) a (by omega)
    (DerivedCategory.Plus.ι.obj K)
  t.plus.ι.preimageIso
    (@asIso _ _ _ _ (topProj (t.plus.ι.obj (plusTruncLT K a)) a inferInstance)
      (isIso_topProj_of_isGE _ a inferInstance) ≪≫
      (shiftFunctor (DerivedCategory B) (-a)).mapIso ((DerivedCategory.singleFunctor B 0).mapIso
        (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor B a).map
          ((t.truncLTι (a + 1)).app (DerivedCategory.Plus.ι.obj K))) hI)) ≪≫
      ((t.plus.ι.commShiftIso (-a)).app ((DerivedCategory.Plus.singleFunctor B 0).obj
        ((DerivedCategory.Plus.homologyFunctor B a).obj K))).symm)

/-- `τ_{≥ a + 1} K ≅ Hᵃ⁺¹(K)[0][-(a + 1)]` when `K` is in degrees `≤ a + 1`. -/
def plusTruncGEIso [(DerivedCategory.Plus.ι.obj K).IsLE (a + 1)] :
    plusTruncGE K a ≅ ((DerivedCategory.Plus.singleFunctor B 0).obj
      ((DerivedCategory.Plus.homologyFunctor B (a + 1)).obj K))⟦-(a + 1)⟧ :=
  have hI := DerivedCategory.isIso_homologyFunctor_map_truncGEπ (a + 1) (a + 1) le_rfl
    (DerivedCategory.Plus.ι.obj K)
  haveI : (t.plus.ι.obj (plusTruncGE K a)).IsGE (a + 1) :=
    (inferInstance : ((t.truncGE (a + 1)).obj (DerivedCategory.Plus.ι.obj K)).IsGE (a + 1))
  t.plus.ι.preimageIso
    (@asIso _ _ _ _ (topProj (t.plus.ι.obj (plusTruncGE K a)) (a + 1)
        (isLE_truncGE _ (a + 1) (a + 1) le_rfl))
      (isIso_topProj_of_isGE _ (a + 1) _) ≪≫
      (shiftFunctor (DerivedCategory B) (-(a + 1))).mapIso
        ((DerivedCategory.singleFunctor B 0).mapIso
          (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor B (a + 1)).map
            ((t.truncGEπ (a + 1)).app (DerivedCategory.Plus.ι.obj K))) hI).symm) ≪≫
      ((t.plus.ι.commShiftIso (-(a + 1))).app ((DerivedCategory.Plus.singleFunctor B 0).obj
        ((DerivedCategory.Plus.homologyFunctor B (a + 1)).obj K))).symm)

variable {H : DerivedCategory.Plus B ⥤ AddCommGrpCat.{w}} [H.IsHomological]
  {D : DerivedCategory.Plus B} {N : ℤ} {A : Type*} [AddCommGroup A]
  {τ : H.obj (D⟦N⟧) →+ A}

/-- **Duality for a complex with cohomology in two adjacent degrees.** For `K` in `D⁺(ℬ)` living in
the degrees `a` and `a + 1` and a homological functor `H` on `D⁺(ℬ)`, duality at `Hᵃ(K)[0]` and
at `Hᵃ⁺¹(K)[0]` gives duality at `K`, when `A` has the extension property for subgroups of the
groups `Hom(M, D[j])`. -/
theorem isPerfect_of_isGE_of_isLE [(DerivedCategory.Plus.ι.obj K).IsGE a]
    [(DerivedCategory.Plus.ι.obj K).IsLE (a + 1)]
    (hA : ∀ (M : DerivedCategory.Plus B) (j : ℤ) (Hs : AddSubgroup (M ⟶ D⟦j⟧)) (φ : Hs →+ A),
      ∃ ψ : (M ⟶ D⟦j⟧) →+ A, ∀ x : Hs, ψ x = φ x)
    (h₁ : IsPerfect H D N τ ((DerivedCategory.Plus.singleFunctor B 0).obj
      ((DerivedCategory.Plus.homologyFunctor B a).obj K)))
    (h₂ : IsPerfect H D N τ ((DerivedCategory.Plus.singleFunctor B 0).obj
      ((DerivedCategory.Plus.homologyFunctor B (a + 1)).obj K))) :
    IsPerfect H D N τ K :=
  isPerfect_obj₂ (plusTriangleLTGE K a) (plusTriangleLTGE_distinguished K a) hA
    (isPerfect_of_iso (plusTruncLTIso K a).symm (isPerfect_shift (-a) h₁))
    (isPerfect_of_iso (plusTruncGEIso K a).symm (isPerfect_shift (-(a + 1)) h₂))

end Stacks.HomologicalDuality

end

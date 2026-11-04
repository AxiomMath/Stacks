module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.QCohDerived
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Truncations `τ_{≥ a}` in `D(𝒪_X)`, for [Stacks, Tag 08IF] (B)

For a scheme `X` and a morphism `g : A ⟶ B` of `D(𝒪_X)` (at the standard model):

* `τ_{≥ a}(g)` is an isomorphism exactly when `g` induces isomorphisms on cohomology in degrees
  `≥ a`;
* if `τ_{≥ a}(g)` is an isomorphism, composition with `g` is a bijection on maps into objects in
  degrees `≥ a`;
* conversely, if composition with `g` is a bijection on maps into every object of a class `P` in
  degrees `≥ a`, and `P` contains `τ_{≥ a} A` and `τ_{≥ a} B`, then `τ_{≥ a}(g)` is an
  isomorphism (Yoneda in `D^{≥ a}`).

## Main results

* `Stacks.Cohomology.RelativeExt.isIso_truncGE_map_iff_isIso_homology`
* `Stacks.Cohomology.RelativeExt.bijective_comp_of_isIso_truncGE`
* `Stacks.Cohomology.RelativeExt.isIso_truncGE_of_bijective_comp`
* `Stacks.Cohomology.RelativeExt.qcohDerived_truncGE`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- `K ⟶ τ_{≥ a} K` induces isomorphisms on cohomology in degrees `j ≥ a`. -/
theorem isIso_homology_map_truncGEπ_std (K : DStd X) (a j : ℤ) (hj : a ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app K)) := by
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let T := (t.triangleLEGE (a - 1) a (by omega)).obj K
  have hT := t.triangleLEGE_distinguished (a - 1) a (by omega) K
  have hEpi : Epi ((DerivedCategory.homologyFunctor _ j).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT j (j + 1) (by omega)).2
      ((DerivedCategory.isZero_of_isLE ((t.truncLE (a - 1)).obj K) (a - 1) (j + 1)
        (by omega)).eq_of_tgt _ _)
  have hMono : Mono ((DerivedCategory.homologyFunctor _ j).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT j).2
      ((DerivedCategory.isZero_of_isLE ((t.truncLE (a - 1)).obj K) (a - 1) j
        (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ j).map T.mor₂)

/-- **`τ_{≥ a}(f)` is invertible exactly when `f` is an isomorphism on cohomology in degrees
`≥ a`.** -/
theorem isIso_truncGE_map_iff_isIso_homology {A K : DStd X} (f : A ⟶ K) (a : ℤ) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map f) ↔
      ∀ i : ℤ, a ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map f) := by
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  have hsq : ∀ i : ℤ, (DerivedCategory.homologyFunctor _ i).map f ≫
      (DerivedCategory.homologyFunctor _ i).map ((t.truncGEπ a).app K) =
      (DerivedCategory.homologyFunctor _ i).map ((t.truncGEπ a).app A) ≫
        (DerivedCategory.homologyFunctor _ i).map ((t.truncGE a).map f) := fun i => by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg _ (by simp)
  have key : ∀ i : ℤ, a ≤ i → (IsIso ((DerivedCategory.homologyFunctor _ i).map f) ↔
      IsIso ((DerivedCategory.homologyFunctor _ i).map ((t.truncGE a).map f))) := fun i hi => by
    have := isIso_homology_map_truncGEπ_std A a i hi
    have := isIso_homology_map_truncGEπ_std K a i hi
    rw [← isIso_comp_right_iff _ ((DerivedCategory.homologyFunctor _ i).map
      ((t.truncGEπ a).app K)), hsq, isIso_comp_left_iff]
  constructor
  · intro h i hi
    exact (key i hi).2 inferInstance
  · intro h
    rw [DerivedCategory.isIso_iff]
    intro i
    by_cases hi : a ≤ i
    · exact (key i hi).1 (h i hi)
    · exact (DerivedCategory.isZero_of_isGE ((t.truncGE a).obj A) a i (by omega)).isIso
        (DerivedCategory.isZero_of_isGE ((t.truncGE a).obj K) a i (by omega)) _

/-- **A map invertible after `τ_{≥ a}` is invertible after `τ_{≥ b}` for `b ≥ a`.** -/
theorem isIso_truncGE_map_of_le {A K : DStd X} (f : A ⟶ K) {a b : ℤ} (hab : a ≤ b)
    (h : IsIso ((DerivedCategory.TStructure.t.truncGE a).map f)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE b).map f) :=
  (isIso_truncGE_map_iff_isIso_homology f b).2 fun i hi =>
    (isIso_truncGE_map_iff_isIso_homology f a).1 h i (by omega)

/-- **A map invertible after `τ_{≥ a}` induces a bijection on maps into objects in degrees
`≥ a`.** -/
theorem bijective_comp_of_isIso_truncGE {A' A : DStd X} (f : A' ⟶ A) (a : ℤ)
    (hf : IsIso ((DerivedCategory.TStructure.t.truncGE a).map f)) (N : DStd X) (hN : N.IsGE a) :
    Function.Bijective (fun x : A ⟶ N ↦ f ≫ x) := by
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  have : t.IsGE N a := hN
  have hπ : f ≫ (t.truncGEπ a).app A = (t.truncGEπ a).app A' ≫ (t.truncGE a).map f := by
    simp
  constructor
  · intro x y hxy
    simp only at hxy
    rw [← t.π_descTruncGE x a, ← t.π_descTruncGE y a, ← Category.assoc, ← Category.assoc,
      hπ, Category.assoc, Category.assoc] at hxy
    rw [← t.π_descTruncGE x a, ← t.π_descTruncGE y a,
      (cancel_epi _).1 (t.from_truncGE_obj_ext hxy)]
  · intro z
    refine ⟨(t.truncGEπ a).app A ≫ inv ((t.truncGE a).map f) ≫ t.descTruncGE z a, ?_⟩
    simp only
    rw [← Category.assoc, hπ, Category.assoc, IsIso.hom_inv_id_assoc, t.π_descTruncGE]

/-- **Yoneda in `D^{≥ a}`.** If composition with `g : A ⟶ B` is a bijection
`Hom(B, N) ⟶ Hom(A, N)` for every `N` in degrees `≥ a` satisfying `P`, and `τ_{≥ a} A`,
`τ_{≥ a} B` satisfy `P`, then `τ_{≥ a}(g)` is an isomorphism. -/
theorem isIso_truncGE_of_bijective_comp {A B : DStd X} (g : A ⟶ B) (a : ℤ)
    (P : ObjectProperty (DStd X))
    (hA : P ((DerivedCategory.TStructure.t.truncGE a).obj A))
    (hB : P ((DerivedCategory.TStructure.t.truncGE a).obj B))
    (h : ∀ N : DStd X, P N → N.IsGE a → Function.Bijective (fun x : B ⟶ N ↦ g ≫ x)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map g) := by
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  have hGA : ((t.truncGE a).obj A).IsGE a := t.isGE_truncGE_obj A a a
  have hGB : ((t.truncGE a).obj B).IsGE a := t.isGE_truncGE_obj B a a
  have : t.IsGE ((t.truncGE a).obj A) a := hGA
  have : t.IsGE ((t.truncGE a).obj B) a := hGB
  have hπ : g ≫ (t.truncGEπ a).app B = (t.truncGEπ a).app A ≫ (t.truncGE a).map g := by
    simp
  obtain ⟨y, hy⟩ := (h _ hA hGA).2 ((t.truncGEπ a).app A)
  simp only at hy
  let v := t.descTruncGE y a
  have hv : (t.truncGEπ a).app B ≫ v = y := t.π_descTruncGE y a
  refine ⟨v, ?_, ?_⟩
  · refine t.from_truncGE_obj_ext ?_
    rw [← Category.assoc, ← hπ, Category.assoc, hv, hy, Category.comp_id]
  · refine t.from_truncGE_obj_ext ?_
    apply (h _ hB hGB).1
    simp only
    rw [reassoc_of% hv, reassoc_of% hy, ← hπ, Category.comp_id]

/-- **Truncations of objects of `D_QCoh(𝒪_X)` lie in `D_QCoh(𝒪_X)`.** -/
theorem qcohDerived_truncGE (A : DStd X) (hA : qcohDerived X A) (a : ℤ) :
    qcohDerived X ((DerivedCategory.TStructure.t.truncGE a).obj A) := fun i => by
  by_cases hi : a ≤ i
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).map
        ((DerivedCategory.TStructure.t.truncGEπ a).app A))
          (isIso_homology_map_truncGEπ_std A a i hi)) (hA i)
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isGE _ a i (by omega)
        (hX := DerivedCategory.TStructure.t.isGE_truncGE_obj A a a))

end Stacks.Cohomology.RelativeExt

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverComplex

/-!
# Reindexing the Čech complex of a family of objects

Let `D : ι → C` be a family of objects whose finite nonempty products exist, and `e : ι' ≃ ι` an
equivalence, possibly between index types of different universes.  The Čech complex
`Stacks.CechSite.FinalCover.complexFunctor` of a presheaf along `D` and along the reindexed
family `D ∘ e` are isomorphic (`Stacks.CechSite.FinalCover.reindexIso`): the degree `n` terms are
the products over the tuples `Fin (n + 1) → ι` and `Fin (n + 1) → ι'` of the same sections, and
`e` matches the tuples.

## Main definitions

* `Stacks.CechSite.FinalCover.reindexIso`: the isomorphism of Čech complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v v' u u'

namespace Stacks.CechSite.FinalCover

variable {C : Type u} [Category.{v} C] {ι : Type w} {ι' : Type w'} (D : ι → C) (e : ι' ≃ ι)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  [∀ (n : ℕ) (x : Fin (n + 1) → ι'), HasProduct (fun a ↦ D (e (x a)))]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasProducts.{w'} A] [Preadditive A]
  (P : Cᵒᵖ ⥤ A)

omit [HasProducts.{w'} A] in
/-- Projections onto factors indexed by equal tuples agree, up to the identification of the
sections over the two (equal) products. -/
theorem π_comp_eqToHom {n : ℕ} {x y : Fin (n + 1) → ι} (h : x = y) :
    π D P n x ≫ P.map (eqToHom (congrArg (fun z ↦ op (inter D z)) h)) = π D P n y := by
  subst h
  simp

/-- The degree `n` component of the reindexing, `D` to `D ∘ e`: on the factor indexed by `x'`, the
projection onto the factor indexed by `e ∘ x'`. -/
def reindexHom (n : ℕ) :
    ((complexFunctor D A).obj P).X n ⟶ ((complexFunctor (fun i ↦ D (e i)) A).obj P).X n :=
  lift (fun i ↦ D (e i)) P fun x' ↦ π D P n (e ∘ x')

/-- The degree `n` component of the reindexing, `D ∘ e` to `D`. -/
def reindexInv (n : ℕ) :
    ((complexFunctor (fun i ↦ D (e i)) A).obj P).X n ⟶ ((complexFunctor D A).obj P).X n :=
  lift D P fun x ↦ π (fun i ↦ D (e i)) P n (e.symm ∘ x) ≫
    P.map (eqToHom (congrArg (fun z ↦ op (inter D z)) (funext fun a ↦ e.apply_symm_apply (x a))))

/-- The components of `reindexHom`. -/
private theorem reindexHom_comp_π (n : ℕ) (x' : Fin (n + 1) → ι') :
    reindexHom D e P n ≫ π (fun i ↦ D (e i)) P n x' = π D P n (e ∘ x') :=
  lift_comp_π (fun i ↦ D (e i)) P _ x'

/-- The components of `reindexInv`. -/
private theorem reindexInv_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    reindexInv D e P n ≫ π D P n x = π (fun i ↦ D (e i)) P n (e.symm ∘ x) ≫
      P.map (eqToHom (congrArg (fun z ↦ op (inter D z))
        (funext fun a ↦ e.apply_symm_apply (x a)))) :=
  lift_comp_π D P _ x

/-- `reindexInv` is a left inverse of `reindexHom`. -/
theorem reindexHom_comp_reindexInv (n : ℕ) :
    reindexHom D e P n ≫ reindexInv D e P n = 𝟙 _ := by
  refine hom_ext D P fun x ↦ ?_
  rw [Category.assoc, reindexInv_comp_π, ← Category.assoc]
  erw [reindexHom_comp_π]
  exact (π_comp_eqToHom D P (funext fun a ↦ e.apply_symm_apply (x a))).trans
    (Category.id_comp _).symm

/-- `reindexInv` is a right inverse of `reindexHom`. -/
theorem reindexInv_comp_reindexHom (n : ℕ) :
    reindexInv D e P n ≫ reindexHom D e P n = 𝟙 _ := by
  refine hom_ext (fun i ↦ D (e i)) P fun x' ↦ ?_
  rw [Category.assoc, reindexHom_comp_π]
  erw [reindexInv_comp_π]
  exact (π_comp_eqToHom (fun i ↦ D (e i)) P (funext fun a ↦ e.symm_apply_apply (x' a))).trans
    (Category.id_comp _).symm

/-- `reindexHom` commutes with the Čech differentials. -/
theorem reindexHom_comm_d (n : ℕ) :
    reindexHom D e P n ≫ ((complexFunctor (fun i ↦ D (e i)) A).obj P).d n (n + 1) =
      ((complexFunctor D A).obj P).d n (n + 1) ≫ reindexHom D e P (n + 1) := by
  refine hom_ext (fun i ↦ D (e i)) P fun x' ↦ ?_
  rw [Category.assoc, d_comp_π, Preadditive.comp_sum, Category.assoc, reindexHom_comp_π]
  erw [d_comp_π D P n (e ∘ x')]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, ← Category.assoc, reindexHom_comp_π]
  rfl

/-- **The Čech complexes of a presheaf along a family and along a reindexing of it are
isomorphic.** -/
def reindexIso :
    (complexFunctor D A).obj P ≅ (complexFunctor (fun i ↦ D (e i)) A).obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ⟨reindexHom D e P n, reindexInv D e P n, reindexHom_comp_reindexInv D e P n,
      reindexInv_comp_reindexHom D e P n⟩)
    fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      exact reindexHom_comm_d D e P i

end Stacks.CechSite.FinalCover

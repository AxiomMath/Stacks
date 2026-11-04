module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotal
public import StacksFrontier.CategoryTheory.Sites.CechComplexSliceBase
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Transporting the elementwise total Čech complex

All names are in the namespace `Stacks.CategoryTheory.CechComplex`.

Two changes of the data of the elementwise total Čech complex `cechTot` leave it unchanged up to
isomorphism.

* **Slice versus lattice.** For a family `U` of elements below `V` in a complete lattice and a
  complex `P` of presheaves on the lattice, the total Čech complex of the family viewed in the
  slice `Over V`, with coefficients `P` restricted along the forgetful functor, is the total
  Čech complex of `U` itself: the Čech intersections have the same underlying elements
  (`interOver_left_eq`) and the lattice is thin.
* **Restriction of scalars.** Restricting the scalars of every value of `P` along a ring map
  restricts the scalars of the total complex.

## Main definitions

* `overComplex`: a complex of presheaves on the lattice, restricted to the slice.
* `cechTotOverIso`: slice versus lattice.
* `restrictComplex`: a complex of presheaves with restricted scalars.
* `cechTotRestrictIso`: restriction of scalars.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u u' r r'

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

/-! ### Isomorphic coefficients -/

/-- The total Čech complexes of isomorphic complexes of presheaves are isomorphic. -/
def cechTotMapIso {C : Type u} [Category.{u'} C] [HasFiniteProducts C] {ι : Type w} (W : ι → C)
    {R : Type r} [Ring R] {P Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (e : P ≅ Q) :
    cechTot W P ≅ cechTot W Q where
  hom := cechTotMap W P e.hom
  inv := cechTotMap W Q e.inv
  hom_inv_id := by rw [← cechTotMap_comp, e.hom_inv_id, cechTotMap_id]
  inv_hom_id := by rw [← cechTotMap_comp, e.inv_hom_id, cechTotMap_id]

/-! ### Slice versus lattice -/

section Slice

variable {L : Type u} [CompleteLattice L] [HasFiniteProducts L] {V : L}
  [HasFiniteProducts (Over V)] {ι : Type w} (U : ι → L) (hU : ∀ i, U i ≤ V)
  {R : Type r} [Ring R] (P : CochainComplex (Lᵒᵖ ⥤ ModuleCat.{w} R) ℕ)

/-- A complex of presheaves on the lattice, restricted to the slice over `V`. -/
def overComplex : CochainComplex ((Over V)ᵒᵖ ⥤ ModuleCat.{w} R) ℕ where
  X b := (Over.forget V).op ⋙ P.X b
  d i j := Functor.whiskerLeft (Over.forget V).op (P.d i j)
  shape i j h := by
    ext W : 2
    exact congrArg (fun φ => φ.app (op (unop W).left)) (P.shape i j h)
  d_comp_d' i j k _ _ := by
    ext W : 2
    exact congrArg (fun φ => φ.app (op (unop W).left)) (P.d_comp_d i j k)

/-- The comparison of cochains, lattice to slice: restriction along the equality of the two
intersections. -/
def overCochain (b p : ℕ) :
    Cochain U (P.X b) p →ₗ[R] Cochain (overFamily U hU) ((overComplex P).X b) p :=
  LinearMap.pi fun t => (interRestrictUp U hU (P.X b) t).hom ∘ₗ LinearMap.proj t

/-- The comparison of cochains, slice to lattice. -/
def overCochainInv (b p : ℕ) :
    Cochain (overFamily U hU) ((overComplex P).X b) p →ₗ[R] Cochain U (P.X b) p :=
  LinearMap.pi fun t => (interRestrictDown U hU (P.X b) t).hom ∘ₗ LinearMap.proj t

/-- `overCochainInv` is a left inverse of `overCochain`. -/
theorem overCochainInv_overCochain (b p : ℕ) (c : Cochain U (P.X b) p) :
    overCochainInv U hU P b p (overCochain U hU P b p c) = c := by
  funext t
  exact ConcreteCategory.congr_hom (interRestrictUp_comp_interRestrictDown U hU (P.X b) t) (c t)

/-- `overCochainInv` is a right inverse of `overCochain`. -/
theorem overCochain_overCochainInv (b p : ℕ)
    (c : Cochain (overFamily U hU) ((overComplex P).X b) p) :
    overCochain U hU P b p (overCochainInv U hU P b p c) = c := by
  funext t
  exact ConcreteCategory.congr_hom (interRestrictDown_comp_interRestrictUp U hU (P.X b) t) (c t)

/-- `overCochain` commutes with the Čech differentials. -/
theorem overCochain_cechD (b p : ℕ) (c : Cochain U (P.X b) p) :
    overCochain U hU P b (p + 1) (cechD U (P.X b) p c) =
      cechD (overFamily U hU) ((overComplex P).X b) p (overCochain U hU P b p c) := by
  funext t
  show (interRestrictUp U hU (P.X b) t).hom (cechD U (P.X b) p c t) =
    cechD (overFamily U hU) ((overComplex P).X b) p (overCochain U hU P b p c) t
  rw [cechD_apply, cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  show ((P.X b).map (interMap U t j.succAbove).op ≫ interRestrictUp U hU (P.X b) t).hom _ =
    (interRestrictUp U hU (P.X b) (t ∘ j.succAbove) ≫
      (P.X b).map (interMap (overFamily U hU) t j.succAbove).left.op).hom _
  dsimp only [interRestrictUp]
  rw [← (P.X b).map_comp, ← (P.X b).map_comp, ← op_comp, ← op_comp]
  exact congrArg
    (fun g : (inter (overFamily U hU) t).left ⟶ inter U (t ∘ j.succAbove) =>
      (ModuleCat.Hom.hom ((P.X b).map g.op)) (c (t ∘ j.succAbove)))
    (Subsingleton.elim _ _)

/-- `overCochain` commutes with the maps of cochains induced by the differentials of `P`. -/
theorem overCochain_cochainMap (b b' p : ℕ) (c : Cochain U (P.X b) p) :
    overCochain U hU P b' p (cochainMap U (P.d b b') p c) =
      cochainMap (overFamily U hU) ((overComplex P).d b b') p (overCochain U hU P b p c) := by
  funext t
  exact (ConcreteCategory.congr_hom ((P.d b b').naturality _) (c t)).symm

/-- The comparison on the total complexes, lattice to slice. -/
def overTot (n : ℤ) : TotX U P n →ₗ[R] TotX (overFamily U hU) (overComplex P) n :=
  LinearMap.pi fun i => overCochain U hU P i.1.2 i.1.1 ∘ₗ LinearMap.proj i

/-- The comparison on the total complexes, slice to lattice. -/
def overTotInv (n : ℤ) : TotX (overFamily U hU) (overComplex P) n →ₗ[R] TotX U P n :=
  LinearMap.pi fun i => overCochainInv U hU P i.1.2 i.1.1 ∘ₗ LinearMap.proj i

/-- `overTot` commutes with the differentials of the total complexes. -/
theorem overTot_totDTo (n m : ℤ) (hm : n + 1 = m) (x : TotX U P n) :
    overTot U hU P m (totDTo U P n m hm x) =
      totDTo (overFamily U hU) (overComplex P) n m hm (overTot U hU P n x) := by
  funext ⟨⟨p, a⟩, h⟩
  rcases p with _ | q <;> rcases a with _ | b <;>
    simp only [overTot, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      totDTo_apply, totDCech_zero, totDCech_succ, totDCoef_zero, totDCoef_succ, map_add,
      map_zsmul, add_zero, zero_add, map_zero, overCochain_cechD, overCochain_cochainMap]

/-- **The total Čech complex in the slice is the total Čech complex in the lattice.** -/
def cechTotOverIso : cechTot U P ≅ cechTot (overFamily U hU) (overComplex P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LinearEquiv.toModuleIso
      { overTot U hU P n with
        invFun := overTotInv U hU P n
        left_inv := fun x => funext fun i => overCochainInv_overCochain U hU P _ _ (x i)
        right_inv := fun x => funext fun i => overCochain_overCochainInv U hU P _ _ (x i) })
    (by
      rintro n _ rfl
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro (x : TotX U P n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [cechTot_d_apply, cechTot_d_apply]
      exact (overTot_totDTo U hU P n (n + 1) rfl x).symm)

/-- The components of `cechTotOverIso` are `overTot`. -/
@[simp]
theorem cechTotOverIso_hom_f_apply (n : ℤ) (x : TotX U P n) :
    ((cechTotOverIso U hU P).hom.f n).hom x = overTot U hU P n x :=
  rfl

end Slice

/-! ### Restriction of scalars -/

section Restrict

variable {C : Type u} [Category.{u'} C] [HasFiniteProducts C] {ι : Type w} (W : ι → C)
  {R : Type r} [Ring R] {R' : Type r'} [Ring R'] (φ : R →+* R')
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R') ℕ)

/-- A complex of presheaves of `R'`-modules, with the scalars of every value restricted to `R`
along `φ`. -/
def restrictComplex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ where
  X b := P.X b ⋙ ModuleCat.restrictScalars φ
  d i j := Functor.whiskerRight (P.d i j) (ModuleCat.restrictScalars φ)
  shape i j h := by
    ext T : 2
    rw [Functor.whiskerRight_app, P.shape i j h, NatTrans.app_zero, Functor.map_zero]
    rfl
  d_comp_d' i j k _ _ := by
    ext T : 2
    rw [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerRight_app,
      ← Functor.map_comp, ← NatTrans.comp_app, P.d_comp_d, NatTrans.app_zero, Functor.map_zero]
    rfl

/-- **Restricting the scalars of the coefficients restricts the scalars of the total Čech
complex.** The two terms in each degree are the same additive group. -/
def cechTotRestrictIso :
    cechTot W (restrictComplex φ P) ≅
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj (cechTot W P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LinearEquiv.toModuleIso (show TotX W (restrictComplex φ P) n ≃ₗ[R]
        ↑((ModuleCat.restrictScalars φ).obj (ModuleCat.of R' (TotX W P n))) from
      { toFun := fun x => (x : TotX W P n)
        invFun := fun x => (x : TotX W (restrictComplex φ P) n)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }))
    (by
      rintro n _ rfl
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro (x : TotX W (restrictComplex φ P) n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [cechTot_d_apply]
      exact (cechTot_d_apply W P n (show TotX W P n from x)).trans rfl)

end Restrict

end

end Stacks.CategoryTheory.CechComplex

end

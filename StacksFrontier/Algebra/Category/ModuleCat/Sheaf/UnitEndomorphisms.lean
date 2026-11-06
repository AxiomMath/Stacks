module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Preadditive.RetractsOfFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism

/-!
# Endomorphisms of the structure sheaf on a site with a terminal object

Let `O` be a sheaf of commutative rings on a site with a terminal object `T`. An endomorphism of
`O` as a module over itself is determined by the image of `1` over `T`, so evaluation at `1`
identifies `End(O)` with the ring `O(T)` of global sections. The free module `O^{⊕n}` is the
biproduct of `n` copies of `O`, so a direct summand of a finite free module is a retract of a
finite biproduct of copies of `O`.

## Main definitions

* `Stacks.SheafOfModules.unitEndRingEquiv`: `End(O) ≃+* O(T)`, `f ↦ f(1)` over `T`.
* `Stacks.SheafOfModules.freeULiftFinIsoBiproduct`: `O^{⊕n} ≅ ⨁_{Fin n} O`.

## Main results

* `Stacks.SheafOfModules.isRetractOfFiniteFree_of_isDirectSummandOfFiniteFree`: a direct summand
  of a finite free module is a retract of a finite biproduct of copies of `O`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Sheaves of modules have finite biproducts. -/
instance (R : Sheaf J RingCat.{u}) : HasFiniteBiproducts (_root_.SheafOfModules.{u} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable (O : Sheaf J CommRingCat.{u}) [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable {T : C} (hT : IsTerminal T)

/-- The sections of the structure sheaf over `T`, as a module over itself, are `O(T)`. -/
def unitObjEquiv :
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val.obj (op T) ≃
      O.obj.obj (op T) :=
  Equiv.refl _

/-- Evaluation at `1` over the terminal object, `End(O) → O(T)`. -/
def unitEndEval
    (f : End (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    O.obj.obj (op T) :=
  unitObjEquiv O ((f.asHom.val.app (op T)).hom ((unitObjEquiv O).symm 1))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- An endomorphism of the structure sheaf acts over `T` as multiplication by its value at `1`. -/
lemma unit_app_eq
    (f : End (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (x : O.obj.obj (op T)) :
    unitObjEquiv O ((f.asHom.val.app (op T)).hom ((unitObjEquiv O).symm x)) = x * unitEndEval O f := by
  have h := (f.asHom.val.app (op T)).hom.map_smul
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op T) from x)
    ((unitObjEquiv O).symm 1)
  have h1 : (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op T)
      from x) • (unitObjEquiv O).symm 1 = (unitObjEquiv O).symm x :=
    mul_one (show O.obj.obj (op T) from x)
  rw [h1] at h
  rw [h]
  rfl

/-- The endomorphisms of the structure sheaf are its global sections: `f ↦ f(1)` over the
terminal object is a ring isomorphism `End(O) ≃+* O(T)`. -/
def unitEndRingEquiv :
    End (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≃+*
      O.obj.obj (op T) where
  toFun := unitEndEval O (T := T)
  invFun a := End.of <|
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).unitHomEquiv.symm
      ((FiniteTypeKernel.sectionsEquivOfTerminal
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) hT).symm
          ((unitObjEquiv O).symm a))
  left_inv f := by
    change End.of ((_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).unitHomEquiv.symm
      ((FiniteTypeKernel.sectionsEquivOfTerminal
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) hT).symm
        (FiniteTypeKernel.sectionsEquivOfTerminal
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) hT
          ((_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf O)).unitHomEquiv f.asHom)))) = f
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv a := by
    change unitObjEquiv O (FiniteTypeKernel.sectionsEquivOfTerminal
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) hT
      ((_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).unitHomEquiv
        ((_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).unitHomEquiv.symm
        ((FiniteTypeKernel.sectionsEquivOfTerminal
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) hT).symm
            ((unitObjEquiv O).symm a))))) = a
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_mul' f g := by
    change unitObjEquiv O ((f.asHom.val.app (op T)).hom
      ((unitObjEquiv O).symm
        (unitObjEquiv O ((g.asHom.val.app (op T)).hom ((unitObjEquiv O).symm 1))))) =
        unitEndEval O f * unitEndEval O g
    exact (unit_app_eq O f _).trans (mul_comm _ _)
  map_add' f g := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `Stacks.SheafOfModules.unitEndRingEquiv` is evaluation at `1` over `T`. -/
lemma unitEndRingEquiv_apply
    (f : End (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    unitEndRingEquiv O hT f = unitEndEval O f :=
  rfl

/-- `ρ : O(T) → End(O)`, the inverse of evaluation at `1`, as a ring homomorphism. -/
abbrev unitEndRingHom :
    O.obj.obj (op T) →+*
      End (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (unitEndRingEquiv O hT).symm.toRingHom

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The ring homomorphism `O(T) → End(O)` is bijective. -/
lemma bijective_unitEndRingHom : Function.Bijective (unitEndRingHom O hT) :=
  (unitEndRingEquiv O hT).symm.bijective

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free module `O^{⊕n}` on `n` generators is the biproduct of `n` copies of `O`. -/
def freeULiftFinIsoBiproduct (n : ℕ) :
    _root_.SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (ULift.{u} (Fin n)) ≅
      ⨁ fun _ : Fin n => _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) =>
    _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).symm ≪≫
      (biproduct.isoCoproduct _).symm

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- A direct summand of a finite free module is a retract of a finite biproduct of copies of the
structure sheaf. -/
lemma isRetractOfFiniteFree_of_isDirectSummandOfFiniteFree
    {M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (hM : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf O) M) :
    IsRetractOfFiniteFree (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
      M := by
  obtain ⟨n, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free (Stacks.SheafOfModules.Tensor.ringSheaf O) M).1 hM
  exact ⟨n, i ≫ (freeULiftFinIsoBiproduct O n).hom, (freeULiftFinIsoBiproduct O n).inv ≫ r,
    by simp [hir]⟩

end Stacks.SheafOfModules

end

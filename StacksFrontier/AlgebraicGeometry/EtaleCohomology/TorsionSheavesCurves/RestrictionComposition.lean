module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors

/-!
# Restriction on étale cohomology along a composite morphism

For morphisms of schemes `b : Z ⟶ Y` and `a : Y ⟶ X`, restricting a class of `H^q(X, F)` first
along `a` and then along `b` is restricting it along the composite, read through the comparison
`(b ≫ a)⁻¹ F ≅ b⁻¹ a⁻¹ F` of inverse images. As a consequence, for a commutative square of
schemes, bijectivity or surjectivity of restriction along one side can be read off from the other
three sides.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_eq_comp_mk₀`: restriction along a
  composite.
* `Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_of_comm` and
  `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_comm`: transfer of
  injectivity and surjectivity of restriction across a commutative square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

section Composition

variable {X Y Z : Scheme.{u}}
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction along a composite.** Restricting along `a` and then along `b` is restricting
along `ba = b ≫ a`, followed by the comparison of inverse images
`(ba)⁻¹ F ≅ b⁻¹ a⁻¹ F`. -/
theorem etaleCohomologyRestrictionMap_comp_eq_comp_mk₀ (a : Y ⟶ X) (b : Z ⟶ Y) (ba : Z ⟶ X)
    (hba : ba = b ≫ a) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    etaleCohomologyRestrictionMap.{u, v, w} b ((etaleAbelianInverseImage.{u, v} a).obj F) q
        (etaleCohomologyRestrictionMap.{u, v, w} a F q x) =
      (etaleCohomologyRestrictionMap.{u, v, w} ba F q x).comp
        (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).hom.app F))
        (add_zero q) := by
  set A := AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)
  have hc := etaleAbelianInverseImageConstantIso_comp.{u, v} a b ba hba A
  have hc' : ((etaleAbelianInverseImageConstantIso.{u, v} b).app A).inv ≫
      (etaleAbelianInverseImage.{u, v} b).map
        ((etaleAbelianInverseImageConstantIso.{u, v} a).app A).inv =
      ((etaleAbelianInverseImageConstantIso.{u, v} ba).app A).inv ≫
        (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).hom.app
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) := by
    have e : (etaleAbelianInverseImage.{u, v} b).mapIso
          ((etaleAbelianInverseImageConstantIso.{u, v} a).app A) ≪≫
          (etaleAbelianInverseImageConstantIso.{u, v} b).app A =
        ((etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).app
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)).symm ≪≫
          (etaleAbelianInverseImageConstantIso.{u, v} ba).app A :=
      Iso.ext (by simpa using hc)
    simpa using congrArg Iso.inv e
  have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
    (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).hom
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) q x
  rw [etaleCohomologyRestrictionMap_apply.{u, v, w}, etaleCohomologyRestrictionMap_apply.{u, v, w},
    etaleCohomologyRestrictionMap_apply.{u, v, w}, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero,
    ← hnat, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  simp only [Iso.app_inv] at hc' ⊢
  rw [hc']

end Composition

section Square

variable {X Y Y' Z : Scheme.{u}}
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Postcomposition with `Ext.mk₀` of an isomorphism is bijective. -/
theorem bijective_comp_mk₀_of_isIso {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    {A M N : C} (e : M ⟶ N) [IsIso e] (q : ℕ) :
    Function.Bijective (fun x : Ext.{w} A M q => x.comp (Ext.mk₀ e) (add_zero q)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => y.comp (Ext.mk₀ (inv e)) (add_zero q), fun x => ?_, fun y => ?_⟩ <;>
    simp [Ext.mk₀_comp_mk₀]

/-- The two ways around a commutative square of restriction maps agree up to bijections. -/
theorem exists_bijective_restriction_square (a : Y' ⟶ X) (b : Y ⟶ X) (a' : Z ⟶ Y)
    (b' : Z ⟶ Y') (h : b' ≫ a = a' ≫ b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    ∃ e : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} b').obj
          ((etaleAbelianInverseImage.{u, v} a).obj F)) q →
        Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} a').obj
          ((etaleAbelianInverseImage.{u, v} b).obj F)) q,
      Function.Bijective e ∧ ∀ x : Sheaf.H.{w} F q,
        e (etaleCohomologyRestrictionMap.{u, v, w} b' _ q
            (etaleCohomologyRestrictionMap.{u, v, w} a F q x)) =
          etaleCohomologyRestrictionMap.{u, v, w} a' _ q
            (etaleCohomologyRestrictionMap.{u, v, w} b F q x) := by
  set c := a' ≫ b
  let φ₁ := (etaleAbelianInverseImageCompIso'.{u, v} b' a c h.symm).hom.app F
  let φ₂ := (etaleAbelianInverseImageCompIso'.{u, v} a' b c rfl).hom.app F
  refine ⟨fun y => y.comp (Ext.mk₀ (inv φ₁ ≫ φ₂)) (add_zero q),
    bijective_comp_mk₀_of_isIso _ q, fun x => ?_⟩
  change Ext.comp _ _ _ = _
  rw [etaleCohomologyRestrictionMap_comp_eq_comp_mk₀.{u, v, w} a b' c h.symm,
    etaleCohomologyRestrictionMap_comp_eq_comp_mk₀.{u, v, w} b a' c rfl,
    Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]
  simp [φ₁, φ₂]

/-- **Injectivity across a square.** In a commutative square `b' ≫ a = a' ≫ b`, if restriction
along `b` and then along `a'` is injective, so is restriction along `a`. -/
theorem injective_etaleCohomologyRestrictionMap_of_comm (a : Y' ⟶ X) (b : Y ⟶ X) (a' : Z ⟶ Y)
    (b' : Z ⟶ Y') (h : b' ≫ a = a' ≫ b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (hb : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} b F q))
    (ha' : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} a'
      ((etaleAbelianInverseImage.{u, v} b).obj F) q)) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} a F q) := by
  obtain ⟨e, -, he⟩ := exists_bijective_restriction_square.{u, v, w} a b a' b' h F q
  intro x y hxy
  apply hb
  apply ha'
  rw [← he, ← he, hxy]

/-- **Surjectivity across a square.** In a commutative square `b' ≫ a = a' ≫ b`, if restriction
along `b` and along `a'` is surjective and restriction along `b'` is injective, then restriction
along `a` is surjective. -/
theorem surjective_etaleCohomologyRestrictionMap_of_comm (a : Y' ⟶ X) (b : Y ⟶ X) (a' : Z ⟶ Y)
    (b' : Z ⟶ Y') (h : b' ≫ a = a' ≫ b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (hb : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} b F q))
    (ha' : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} a'
      ((etaleAbelianInverseImage.{u, v} b).obj F) q))
    (hb' : Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} b'
      ((etaleAbelianInverseImage.{u, v} a).obj F) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} a F q) := by
  obtain ⟨e, he, hcomm⟩ := exists_bijective_restriction_square.{u, v, w} a b a' b' h F q
  intro y
  obtain ⟨z, hz⟩ := ha' (e (etaleCohomologyRestrictionMap.{u, v, w} b' _ q y))
  obtain ⟨x, rfl⟩ := hb z
  refine ⟨x, hb'.1 (he.1 ?_)⟩
  rw [hcomm, hz]

/-- **Bijectivity across a square.** -/
theorem bijective_etaleCohomologyRestrictionMap_of_comm (a : Y' ⟶ X) (b : Y ⟶ X) (a' : Z ⟶ Y)
    (b' : Z ⟶ Y') (h : b' ≫ a = a' ≫ b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (hb : Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} b F q))
    (ha' : Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} a'
      ((etaleAbelianInverseImage.{u, v} b).obj F) q))
    (hb' : Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} b'
      ((etaleAbelianInverseImage.{u, v} a).obj F) q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} a F q) :=
  ⟨injective_etaleCohomologyRestrictionMap_of_comm.{u, v, w} a b a' b' h F q hb.1 ha'.1,
    surjective_etaleCohomologyRestrictionMap_of_comm.{u, v, w} a b a' b' h F q hb.2 ha'.2 hb'⟩

end Square

end Stacks.EtaleCohomology

end

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Cocycles of Hom complexes along an additive functor

An additive functor `Φ : C ⥤ D` maps a cochain `z` of the Hom complex `Hom^•(K, L)` to the
cochain `Φ z` of `Hom^•(Φ K, Φ L)` (Mathlib's `CochainComplex.HomComplex.Cochain.map`), and it
commutes with the differential, so it maps cocycles to cocycles. Under the identification of
degree-`n` cocycles with morphisms `K ⟶ L⟦n⟧` (`CochainComplex.HomComplex.Cocycle.equivHomShift`),
this is `Φ` applied to the morphism, followed by the commutation of `Φ` with the shift.

## Main definitions

* `CochainComplex.HomComplex.Cocycle.map`: the image of a cocycle under `Φ`.

## Main results

* `CochainComplex.HomComplex.Cocycle.equivHomShift_symm_map`: the morphism `Φ K ⟶ (Φ L)⟦n⟧`
  attached to `Φ z` is `Φ` of the morphism `K ⟶ L⟦n⟧` attached to `z`, followed by the shift
  commutation isomorphism of `Φ`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex.Cocycle

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
  (Φ : C ⥤ D) [Φ.Additive] {K L : CochainComplex C ℤ} {n : ℤ}

/-- **The image of a cocycle under an additive functor.** -/
def map (z : Cocycle K L n) :
    Cocycle ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cocycle.mk ((z : Cochain K L n).map Φ) (n + 1) rfl (by
    rw [δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])

/-- The underlying cochain of `map Φ z` is the image under `Φ` of the underlying cochain of `z`. -/
@[simp]
lemma map_coe (z : Cocycle K L n) : ((map Φ z : Cocycle _ _ n) : Cochain _ _ n) =
    (z : Cochain K L n).map Φ := rfl

/-- The image of cocycles under `Φ` is additive. -/
lemma map_add (z z' : Cocycle K L n) : map Φ (z + z') = map Φ z + map Φ z' := by
  ext p q hpq
  simp [map]

/-- **The morphism attached to `Φ z`** is `Φ` of the morphism attached to `z`, followed by the
commutation of `Φ` with the shift. -/
lemma equivHomShift_symm_map (z : Cocycle K L n) :
    equivHomShift.symm (map Φ z) =
      (Φ.mapHomologicalComplex _).map (equivHomShift.symm z) ≫
        ((Φ.mapHomologicalComplex _).commShiftIso n).hom.app L := by
  ext p
  simp only [Functor.mapHomologicalComplex_obj_X, shiftFunctor_obj_X', map,
    equivHomShift_symm_apply, homOf_f, rightShift_coe, mk_coe, Functor.comp_obj,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.comp_id]
  simp only [Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

end CochainComplex.HomComplex.Cocycle

end

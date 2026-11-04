module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Single

/-!
# A two-term complex as the mapping cone of a map of single complexes

Mathlib's `HomologicalComplex.double f h` places `f : X₀ ⟶ X₁` in two adjacent degrees and zero
elsewhere. A complex vanishing outside those two degrees whose differential between them is `f`
is therefore isomorphic to it, and `doubleIsoOfIsZero` is that recognition.

The mapping cone of `(single C (ComplexShape.up ℤ) 0).map f` is such a complex, carrying the
source of `f` in degree `-1` and its target in degree `0`; `singleConeDoubleIso` identifies it
with the two-term complex on `f` in that cochain presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

/-- A complex vanishing outside two adjacent degrees `i₀`, `i₁`, together with isomorphisms of
its terms there onto the source and target of `f : X₀ ⟶ X₁` commuting with its differential, is
the two-term complex on `f`. -/
public def doubleIsoOfIsZero {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι}
    {X₀ X₁ : C} (f : X₀ ⟶ X₁) (h : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (K : HomologicalComplex C c) (e₀ : X₀ ≅ K.X i₀) (e₁ : X₁ ≅ K.X i₁)
    (hcomm : e₀.hom ≫ K.d i₀ i₁ = f ≫ e₁.hom)
    (hout : ∀ j, c.Rel i₁ j → e₁.hom ≫ K.d i₁ j = 0)
    (hsupport : ∀ j, j ≠ i₀ → j ≠ i₁ → IsZero (K.X j)) :
    HomologicalComplex.double f h ≅ K := by
  let g := HomologicalComplex.mkHomFromDouble h hne e₀.hom e₁.hom hcomm hout
  haveI : ∀ j, IsIso (g.f j) := by
    intro j
    by_cases h₀ : j = i₀
    · subst j
      dsimp only [g]
      rw [HomologicalComplex.mkHomFromDouble_f₀]
      infer_instance
    · by_cases h₁ : j = i₁
      · subst j
        dsimp only [g]
        rw [HomologicalComplex.mkHomFromDouble_f₁]
        infer_instance
      · let e := (HomologicalComplex.isZero_double_X f h j h₀ h₁).iso (hsupport j h₀ h₁)
        have he : g.f j = e.hom :=
          (HomologicalComplex.isZero_double_X f h j h₀ h₁).eq_of_src _ _
        rw [he]
        infer_instance
  haveI := HomologicalComplex.Hom.isIso_of_components g
  exact asIso g

section ConeDouble

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {X Y : C} (f : X ⟶ Y)

-- The three isomorphisms below are stated against `(CochainComplex.mappingCone _).X _`, whose
-- objects are only reached, and whose `simp` lemmas are only type-correct, once the mapping cone
-- unfolds to `HomologicalComplex.homotopyCofiber`.
attribute [local implicit_reducible] CochainComplex.mappingCone

/-- The morphism `f` read as a map of complexes concentrated in degree `0`. -/
public abbrev singleMap :=
  (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f

/-- Degree `-1` of the mapping cone of `singleMap f` is the source of `f`. -/
public def singleConeNegOneIso : X ≅ (CochainComplex.mappingCone (singleMap f)).X (-1) where
  hom := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫
    HomologicalComplex.homotopyCofiber.inlX (singleMap f) 0 (-1) (by decide)
  inv := HomologicalComplex.homotopyCofiber.fstX (singleMap f) (-1) 0 (by decide) ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom
  hom_inv_id := by simp [CochainComplex.mappingCone]
  inv_hom_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply HomologicalComplex.homotopyCofiber.ext_from_X (singleMap f) 0 (-1) (by decide)
    · simp [CochainComplex.mappingCone]
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Y (-1)
        (by decide)).eq_of_src _ _

/-- Degree `0` of the mapping cone of `singleMap f` is the target of `f`. -/
public def singleConeZeroIso : Y ≅ (CochainComplex.mappingCone (singleMap f)).X 0 where
  hom := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv ≫
    HomologicalComplex.homotopyCofiber.inrX (singleMap f) 0
  inv := HomologicalComplex.homotopyCofiber.sndX (singleMap f) 0 ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom
  hom_inv_id := by simp [CochainComplex.mappingCone]
  inv_hom_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply HomologicalComplex.homotopyCofiber.ext_from_X (singleMap f) 1 0 (by decide)
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X 1
        (by decide)).eq_of_src _ _
    · simp [CochainComplex.mappingCone]

/-- The only differential of the mapping cone of `singleMap f` is `f`, read through the two
identifications of its terms. -/
public theorem singleCone_d :
    (singleConeNegOneIso f).hom ≫ (CochainComplex.mappingCone (singleMap f)).d (-1) 0 =
      f ≫ (singleConeZeroIso f).hom := by
  dsimp only [singleConeNegOneIso, singleConeZeroIso, CochainComplex.mappingCone,
    HomologicalComplex.homotopyCofiber_d]
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.inlX_d (singleMap f) (-1) 0 1
    (by decide) (by decide)]
  simp [singleMap, HomologicalComplex.single_map_f_self]

/-- The mapping cone of `singleMap f` is the two-term complex on `f`, placed in degrees `-1`
and `0`. -/
public def singleConeDoubleIso :
    HomologicalComplex.double f (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) ≅
      CochainComplex.mappingCone (singleMap f) :=
  doubleIsoOfIsZero f rfl (by decide) _ (singleConeNegOneIso f) (singleConeZeroIso f)
    (singleCone_d f)
    (fun j hj ↦ by
      dsimp only [singleConeZeroIso]
      rw [Category.assoc]
      change _ ≫ (HomologicalComplex.homotopyCofiber.inrX (singleMap f) 0 ≫
        HomologicalComplex.homotopyCofiber.d (singleMap f) 0 j) = 0
      rw [HomologicalComplex.homotopyCofiber.inrX_d]
      simp)
    (fun j hj₀ hj₁ ↦ by
      apply HomologicalComplex.homotopyCofiber.isZero_X (singleMap f) j
      · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Y j hj₁
      · intro k hk
        apply HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X k
        change j + 1 = k at hk
        omega)

end ConeDouble

end HomologicalComplex

end

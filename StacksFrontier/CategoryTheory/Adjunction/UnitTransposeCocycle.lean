module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Whiskering

/-!
# Transposed units along a comparison of right adjoints, and their cocycle law

Let `a : L ⊣ R` and `a' : L' ⊣ R'` be adjunctions out of a common category `C₀`, and let
`e : M ⋙ R ≅ R'` identify a further functor `M` followed by `R` with `R'`.  The unit of `a'`,
read through `e`, is a morphism `A ⟶ R (M (L' A))`, and its transpose along `a` is a morphism

`L A ⟶ M (L' A)`.

For the pullback functors of a pseudofunctor of ringed topoi — `L = f^*`, `L' = (φ ≫ f)^*`,
`M = φ_*` and `e` the comparison of direct images along a composite — this is the restriction
map `f^*𝒜 ⟶ φ_*((φ ≫ f)^*𝒜)` of pulled-back sheaves.  This file proves that these morphisms
satisfy the cocycle law as soon as the comparisons of right adjoints satisfy the associativity
law.

## Main definitions

* `CategoryTheory.Adjunction.unitTranspose`: the transpose of the unit of `a'` read through `e`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_unitTranspose`: its defining property.
* `CategoryTheory.Adjunction.unitTranspose_comp`: **the cocycle law**.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

/-- The transpose along `a` of the unit of `a'`, read through `e : M ⋙ R ≅ R'`. -/
def unitTranspose {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : C₀ ⥤ C₂} {R' : C₂ ⥤ C₀} (a : L ⊣ R)
    (a' : L' ⊣ R') (M : C₂ ⥤ C₁) (e : M ⋙ R ≅ R') (A : C₀) :
    L.obj A ⟶ M.obj (L'.obj A) :=
  (a.homEquiv _ _).symm (a'.unit.app A ≫ e.inv.app _)

/-- The unit of `a` followed by the image under `R` of the transposed unit is the unit of `a'`
followed by the component of `e.inv`. -/
@[reassoc]
theorem unit_comp_map_unitTranspose {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : C₀ ⥤ C₂}
    {R' : C₂ ⥤ C₀} (a : L ⊣ R) (a' : L' ⊣ R') (M : C₂ ⥤ C₁) (e : M ⋙ R ≅ R') (A : C₀) :
    a.unit.app A ≫ R.map (unitTranspose a a' M e A) = a'.unit.app A ≫ e.inv.app _ :=
  (a.homEquiv_unit _ _ _).symm.trans ((a.homEquiv _ _).apply_symm_apply _)

/-- Naturality of `e.inv`, with the composite functor's `map` unfolded. -/
private theorem map_comp_inv_app {R : C₁ ⥤ C₀} {R' : C₂ ⥤ C₀} {M : C₂ ⥤ C₁} (e : M ⋙ R ≅ R')
    {X Y : C₂} (f : X ⟶ Y) : R'.map f ≫ e.inv.app Y = e.inv.app X ≫ R.map (M.map f) :=
  e.inv.naturality f

/-- The transposed unit is natural in the object. -/
theorem unitTranspose_naturality {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : C₀ ⥤ C₂}
    {R' : C₂ ⥤ C₀} (a : L ⊣ R) (a' : L' ⊣ R') (M : C₂ ⥤ C₁) (e : M ⋙ R ≅ R') {A A' : C₀}
    (g : A ⟶ A') :
    L.map g ≫ unitTranspose a a' M e A' = unitTranspose a a' M e A ≫ M.map (L'.map g) := by
  apply (a.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, a.unit_naturality, Category.assoc,
    unit_comp_map_unitTranspose, unit_comp_map_unitTranspose_assoc]
  rw [← map_comp_inv_app, ← Category.assoc, ← Category.assoc, a'.unit_naturality]

/-- **The cocycle law of the transposed units.**  If the comparisons of right adjoints satisfy
the associativity law, the transposed unit for the composite comparison is the transposed unit
for the first comparison followed by the image of the transposed unit for the second. -/
theorem unitTranspose_comp {L₁ : C₀ ⥤ C₁} {L₂ : C₀ ⥤ C₂} {L₃ : C₀ ⥤ C₃} {R₁₀ : C₁ ⥤ C₀}
    {R₂₀ : C₂ ⥤ C₀} {R₃₀ : C₃ ⥤ C₀} (R₂₁ : C₂ ⥤ C₁) (R₃₂ : C₃ ⥤ C₂) (R₃₁ : C₃ ⥤ C₁)
    (a₁ : L₁ ⊣ R₁₀) (a₂ : L₂ ⊣ R₂₀) (a₃ : L₃ ⊣ R₃₀)
    (e₀₁₂ : R₂₁ ⋙ R₁₀ ≅ R₂₀) (e₁₂₃ : R₃₂ ⋙ R₂₁ ≅ R₃₁)
    (e₀₁₃ : R₃₁ ⋙ R₁₀ ≅ R₃₀) (e₀₂₃ : R₃₂ ⋙ R₂₀ ≅ R₃₀)
    (h : isoWhiskerLeft R₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃) (A : C₀) :
    unitTranspose a₁ a₃ R₃₁ e₀₁₃ A ≫ e₁₂₃.inv.app _ =
      unitTranspose a₁ a₂ R₂₁ e₀₁₂ A ≫ R₂₁.map (unitTranspose a₂ a₃ R₃₂ e₀₂₃ A) := by
  apply (a₁.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, Functor.map_comp,
    unit_comp_map_unitTranspose_assoc a₁ a₃, unit_comp_map_unitTranspose_assoc a₁ a₂]
  rw [← map_comp_inv_app, unit_comp_map_unitTranspose_assoc a₂ a₃]
  congr 1
  have h' := congrArg (fun i => i.inv.app (L₃.obj A)) h
  simp only [Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv,
    Iso.symm_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at h'
  rw [h']

/-- **The transposed unit, transposed again, is the comparison of left adjoints.**  Transposing
the transposed unit along the adjunction of `M` gives the component of
`CategoryTheory.Adjunction.leftAdjointCompIso`. -/
theorem homEquiv_symm_unitTranspose {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : C₀ ⥤ C₂}
    {R' : C₂ ⥤ C₀} {LM : C₁ ⥤ C₂} {M : C₂ ⥤ C₁} (a : L ⊣ R) (a' : L' ⊣ R') (aM : LM ⊣ M)
    (e : M ⋙ R ≅ R') (A : C₀) :
    (aM.homEquiv _ _).symm (unitTranspose a a' M e A) =
      (leftAdjointCompIso a aM a' e).hom.app A := by
  rw [Equiv.symm_apply_eq]
  apply (a.homEquiv _ _).injective
  rw [unitTranspose, Equiv.apply_symm_apply]
  have hc := unit_conjugateEquiv (a.comp aM) a' (leftAdjointCompIso a aM a' e).inv A
  rw [conjugateEquiv_leftAdjointCompIso_inv] at hc
  have hu : (a.comp aM).unit.app A = a'.unit.app A ≫
      R'.map ((leftAdjointCompIso a aM a' e).inv.app A) ≫ e.inv.app _ := by
    rw [← reassoc_of% hc]
    exact (Category.comp_id _).symm.trans (congrArg _ (e.hom_inv_id_app _).symm)
  have hh : a.homEquiv _ _ (aM.homEquiv _ _ ((leftAdjointCompIso a aM a' e).hom.app A)) =
      (a.comp aM).unit.app A ≫ R.map (M.map ((leftAdjointCompIso a aM a' e).hom.app A)) := by
    rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, comp_unit_app, Category.assoc]
  rw [hh, hu, Category.assoc, Category.assoc]
  congr 1
  rw [← map_comp_inv_app, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  exact (Category.id_comp _).symm

end CategoryTheory.Adjunction

module

public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaDualizable
import all StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaDualizable
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.Functor
import StacksFrontier.CategoryTheory.Adjunction.CounitHomExt
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# The comparison map of a projection formula

Declarations built on
`StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaDualizable`.

## Main results

* `map_projectionMap_comp_counit`
* `projectionMap_whiskerRight`
* `whiskerLeft_projectionMap`
* `projectionMap_unit`
* `projectionMap_assoc`
* `comparisonMap`
* `map_whiskerRight_comp_inv_projectionMap`
* `comparisonMap_naturality_left`
* `comparisonNatTrans`
* `projectionTwoSquare`
* `projectionTwoSquare_natTrans_app`
* `instance (K : C) : IsIso (adj.projectionTwoSquare K).natTrans := by
  have : ∀ M, IsIso ((adj.projectionTwoSquare K).natTrans.app M) := fun M =>
    inferInstanceAs (IsIso (adj.projectionMap K M))
  exact NatIso.isIso_of_isIso_app _`
* `projectionInvTwoSquare`
* `projectionInvTwoSquare_natTrans_app`
* `comparisonTwoSquare`
* `comparisonTwoSquare_natTrans_app`
* `adjunctionTensorMap_eq_projectionMap`
* `isIso_projectionMap_iff`
* `homEquiv_inv_adjunctionTensorMap_eq_comparisonMap`
* `tensorLeftAdjunction_counit_app`
* `whiskerLeft_projectionMap_comp_projectionMap_comp_counit`
* `mateEquiv_projectionTwoSquare`
* `isIso_comparisonTwoSquare_of_exactPairing`
* `isIso_comparisonMap_of_exactPairing`
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

namespace Adjunction

section Oplax

variable [F.OplaxMonoidal]

/-- **The projection map** `K ⊗ G M ⟶ G (F K ⊗ M)`: the adjoint transpose of the oplax
structure `F (K ⊗ G M) ⟶ F K ⊗ F G M` followed by `F K` tensored with the counit. -/
def projectionMap (K : C) (M : D) : K ⊗ G.obj M ⟶ G.obj (F.obj K ⊗ M) :=
  adj.homEquiv _ _ (δ F K (G.obj M) ≫ F.obj K ◁ adj.counit.app M)

/-- The defining equation of the projection map. -/
@[reassoc]
lemma map_projectionMap_comp_counit (K : C) (M : D) :
    F.map (adj.projectionMap K M) ≫ adj.counit.app (F.obj K ⊗ M) =
      δ F K (G.obj M) ≫ F.obj K ◁ adj.counit.app M := by
  have h := (adj.homEquiv _ _).symm_apply_apply
    (δ F K (G.obj M) ≫ F.obj K ◁ adj.counit.app M)
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- The projection map is natural in the first variable. -/
@[reassoc]
lemma projectionMap_whiskerRight {K K' : C} (f : K ⟶ K') (M : D) :
    f ▷ G.obj M ≫ adj.projectionMap K' M =
      adj.projectionMap K M ≫ G.map (F.map f ▷ M) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj
  simp only [Functor.id_obj, Functor.map_comp, assoc, map_projectionMap_comp_counit,
    counit_naturality, map_projectionMap_comp_counit_assoc]
  rw [whisker_exchange, ← δ_natural_left_assoc]

/-- The projection map is natural in the second variable. -/
@[reassoc]
lemma whiskerLeft_projectionMap (K : C) {M M' : D} (g : M ⟶ M') :
    K ◁ G.map g ≫ adj.projectionMap K M' =
      adj.projectionMap K M ≫ G.map (F.obj K ◁ g) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj
  simp only [Functor.id_obj, Functor.map_comp, assoc, map_projectionMap_comp_counit,
    counit_naturality, map_projectionMap_comp_counit_assoc]
  rw [← δ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, Adjunction.counit_naturality]

/-- The projection map at the unit object is the left unitor. -/
lemma projectionMap_unit (M : D) :
    adj.projectionMap (𝟙_ C) M ≫ G.map (η F ▷ M ≫ (λ_ M).hom) = (λ_ (G.obj M)).hom := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj
  simp only [Functor.id_obj, Functor.map_comp, assoc, counit_naturality, counit_naturality_assoc,
    map_projectionMap_comp_counit_assoc]
  rw [← left_unitality_hom, assoc, assoc, whisker_exchange_assoc, leftUnitor_naturality]

/-- The projection map is compatible with the associators. -/
lemma projectionMap_assoc (K K' : C) (M : D) :
    K' ◁ adj.projectionMap K M ≫ adj.projectionMap K' (F.obj K ⊗ M) ≫
        G.map (α_ (F.obj K') (F.obj K) M).inv =
      (α_ K' K (G.obj M)).inv ≫ adj.projectionMap (K' ⊗ K) M ≫ G.map (δ F K' K ▷ M) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj
  simp only [Functor.id_obj, Functor.map_comp, assoc, counit_naturality,
    map_projectionMap_comp_counit_assoc]
  rw [← δ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    map_projectionMap_comp_counit, MonoidalCategory.whiskerLeft_comp_assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [associator_inv_naturality_right, Functor.OplaxMonoidal.associativity_inv_assoc,
    whisker_exchange]

end Oplax

/-! ### The comparison map -/

section Comparison

variable [F.OplaxMonoidal] [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)]
  {a : C ⥤ D} (adj₂ : G ⊣ a)

/-- **The comparison map** `F K ⊗ a L ⟶ a (K ⊗ L)`: the adjoint transpose of the inverse
projection map followed by `K` tensored with the counit of `G ⊣ a`. -/
def comparisonMap (K L : C) : F.obj K ⊗ a.obj L ⟶ a.obj (K ⊗ L) :=
  adj₂.homEquiv _ _ (inv (adj.projectionMap K (a.obj L)) ≫ K ◁ adj₂.counit.app L)

/-- The inverse projection map is natural in the first variable. -/
@[reassoc]
lemma map_whiskerRight_comp_inv_projectionMap {K K' : C} (h : K ⟶ K') (M : D) :
    G.map (F.map h ▷ M) ≫ inv (adj.projectionMap K' M) =
      inv (adj.projectionMap K M) ≫ h ▷ G.obj M := by
  rw [IsIso.comp_inv_eq, assoc, adj.projectionMap_whiskerRight, IsIso.inv_hom_id_assoc]

/-- The comparison map is natural in the first variable. -/
@[reassoc]
lemma comparisonMap_naturality_left {K K' : C} (h : K ⟶ K') (L : C) :
    F.map h ▷ a.obj L ≫ adj.comparisonMap adj₂ K' L =
      adj.comparisonMap adj₂ K L ≫ a.map (h ▷ L) := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    comparisonMap, comparisonMap, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    map_whiskerRight_comp_inv_projectionMap_assoc, assoc, whisker_exchange]

/-- The comparison map as a natural transformation in the first variable,
`F (-) ⊗ a L ⟶ a ((-) ⊗ L)`. -/
@[simps]
def comparisonNatTrans (L : C) : F ⋙ tensorRight (a.obj L) ⟶ tensorRight L ⋙ a where
  app K := adj.comparisonMap adj₂ K L
  naturality _ _ h := adj.comparisonMap_naturality_left adj₂ h L

/-- The projection map as a 2-square `G ⋙ (K ⊗ -) ⟶ (F K ⊗ -) ⋙ G`. -/
def projectionTwoSquare (K : C) :
    TwoSquare G (tensorLeft (F.obj K)) (tensorLeft K) G :=
  TwoSquare.mk _ _ _ _
    { app := fun M => adj.projectionMap K M
      naturality := fun _ _ g => adj.whiskerLeft_projectionMap K g }

omit [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] in
/-- The component at `M` of the 2-square `projectionTwoSquare K` is the projection map
`projectionMap K M`. -/
@[simp]
lemma projectionTwoSquare_natTrans_app (K : C) (M : D) :
    (adj.projectionTwoSquare K).app M = adj.projectionMap K M :=
  rfl

/-- The natural transformation of the 2-square `projectionTwoSquare K` is an isomorphism. -/
instance (K : C) : IsIso (adj.projectionTwoSquare K) := by
  have : ∀ M, IsIso ((adj.projectionTwoSquare K).app M) := fun M =>
    inferInstanceAs (IsIso (adj.projectionMap K M))
  exact NatIso.isIso_of_isIso_app _

/-- The inverse projection map as a 2-square `(F K ⊗ -) ⋙ G ⟶ G ⋙ (K ⊗ -)`. -/
def projectionInvTwoSquare (K : C) :
    TwoSquare (tensorLeft (F.obj K)) G G (tensorLeft K) :=
  TwoSquare.mk _ _ _ _ (inv (adj.projectionTwoSquare K))

/-- The component at `M` of the 2-square `projectionInvTwoSquare K` is the inverse of the
projection map `projectionMap K M`. -/
lemma projectionInvTwoSquare_natTrans_app (K : C) (M : D) :
    (adj.projectionInvTwoSquare K).app M = inv (adj.projectionMap K M) := by
  simp [projectionInvTwoSquare]

/-- The comparison map as a 2-square `a ⋙ (F K ⊗ -) ⟶ (K ⊗ -) ⋙ a`. -/
def comparisonTwoSquare (K : C) : TwoSquare a (tensorLeft K) (tensorLeft (F.obj K)) a :=
  mateEquiv adj₂ adj₂ (adj.projectionInvTwoSquare K)

/-- The component at `L` of the 2-square `comparisonTwoSquare adj₂ K` is the comparison map
`comparisonMap adj₂ K L`. -/
lemma comparisonTwoSquare_natTrans_app (K L : C) :
    (adj.comparisonTwoSquare adj₂ K).app L = adj.comparisonMap adj₂ K L := by
  simp [comparisonTwoSquare, comparisonMap, projectionInvTwoSquare_natTrans_app,
    Adjunction.homEquiv_unit]

end Comparison

/-! ### Comparison with the projection map of a bifunctor isomorphic to the tensor product -/

section Bifunctor

variable [F.OplaxMonoidal]

open scoped CategoryTheory.Prod

variable (TC : C ⥤ C ⥤ C) (ψC : TC ≅ curriedTensor C) (TD : D ⥤ D ⥤ D)
  (ψD : TD ≅ curriedTensor D)
  (α : Prod.swap C C ⋙ Functor.uncurry.obj TC ⋙ F ⟶
    F.prod F ⋙ Prod.swap D D ⋙ Functor.uncurry.obj TD)

/-- **The projection-formula map of a bifunctor isomorphic to the tensor product.** If the
comparison `α : F (TC Q P) ⟶ TD (F Q) (F P)` is the oplax structure of `F` transported along
isomorphisms `TC ≅ - ⊗ -` and `TD ≅ - ⊗ -`, the projection-formula map
`CategoryTheory.adjunctionTensorMap` built from `TC`, `TD` and `α` is the projection map
`Adjunction.projectionMap`, transported along the same isomorphisms. -/
lemma adjunctionTensorMap_eq_projectionMap
    (hα : ∀ P Q : C, α.app (P, Q) = F.map ((ψC.hom.app Q).app P) ≫ δ F Q P ≫
      (ψD.inv.app (F.obj Q)).app (F.obj P)) (E : D) (K : C) :
    adjunctionTensorMap adj (Prod.swap C C ⋙ Functor.uncurry.obj TC)
        (Prod.swap D D ⋙ Functor.uncurry.obj TD) α E K =
      (ψC.hom.app K).app (G.obj E) ≫ adj.projectionMap K E ≫
        G.map ((ψD.inv.app (F.obj K)).app E) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj
  rw [map_adjunctionTensorMap_comp_counit, hα, Functor.map_comp, Functor.map_comp, assoc, assoc,
    assoc, assoc]
  have hc := adj.counit.naturality ((ψD.inv.app (F.obj K)).app E)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
    curriedTensor_obj_obj] at hc
  dsimp only [Functor.comp_obj, Functor.uncurry_obj_obj, Prod.swap_obj]
  rw [hc, map_projectionMap_comp_counit_assoc]
  have h := (ψD.inv.app (F.obj K)).naturality (adj.counit.app E)
  dsimp at h ⊢
  simp [h]

/-- Invertibility of the projection-formula map of `TC`, `TD`, `α` is invertibility of the
projection map. -/
lemma isIso_projectionMap_iff
    (hα : ∀ P Q : C, α.app (P, Q) = F.map ((ψC.hom.app Q).app P) ≫ δ F Q P ≫
      (ψD.inv.app (F.obj Q)).app (F.obj P)) (E : D) (K : C) :
    IsIso (adjunctionTensorMap adj (Prod.swap C C ⋙ Functor.uncurry.obj TC)
        (Prod.swap D D ⋙ Functor.uncurry.obj TD) α E K) ↔ IsIso (adj.projectionMap K E) := by
  rw [adj.adjunctionTensorMap_eq_projectionMap TC ψC TD ψD α hα, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- **The comparison map of `TC`, `TD`, `α` is the comparison map**, transported along the
isomorphisms `TC ≅ - ⊗ -` and `TD ≅ - ⊗ -`. -/
lemma homEquiv_inv_adjunctionTensorMap_eq_comparisonMap
    (hα : ∀ P Q : C, α.app (P, Q) = F.map ((ψC.hom.app Q).app P) ≫ δ F Q P ≫
      (ψD.inv.app (F.obj Q)).app (F.obj P))
    [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)]
    [∀ (E : D) (K : C), IsIso (adjunctionTensorMap adj (Prod.swap C C ⋙ Functor.uncurry.obj TC)
        (Prod.swap D D ⋙ Functor.uncurry.obj TD) α E K)]
    {a : C ⥤ D} (adj₂ : G ⊣ a) (K L : C) :
    adj₂.homEquiv _ _ (inv (adjunctionTensorMap adj (Prod.swap C C ⋙ Functor.uncurry.obj TC)
        (Prod.swap D D ⋙ Functor.uncurry.obj TD) α (a.obj L) K) ≫
        (TC.obj K).map (adj₂.counit.app L)) =
      (ψD.hom.app (F.obj K)).app (a.obj L) ≫ adj.comparisonMap adj₂ K L ≫
        a.map ((ψC.inv.app K).app L) := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, comparisonMap]
  dsimp only [curriedTensor_obj_obj]
  rw [Equiv.symm_apply_apply]
  simp only [adj.adjunctionTensorMap_eq_projectionMap TC ψC TD ψD α hα, IsIso.inv_comp, assoc]
  have e₁ : inv (G.map ((ψD.inv.app (F.obj K)).app (a.obj L))) =
      G.map ((ψD.hom.app (F.obj K)).app (a.obj L)) :=
    IsIso.inv_eq_of_hom_inv_id (by
      rw [← G.map_comp, ← NatTrans.comp_app, Iso.inv_hom_id_app, NatTrans.id_app, G.map_id])
  have e₂ : inv ((ψC.hom.app K).app (G.obj (a.obj L))) =
      (ψC.inv.app K).app (G.obj (a.obj L)) :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← NatTrans.comp_app, Iso.hom_inv_id_app, NatTrans.id_app])
  have h₂ := (ψC.inv.app K).naturality (adj₂.counit.app L)
  dsimp only [curriedTensor_obj_map, Functor.id_obj, Functor.comp_obj] at h₂
  rw [e₁, e₂, h₂]

end Bifunctor


end Adjunction

/-! ### The comparison map at a dualizable object -/

namespace Adjunction

/-- The counit of the adjunction `tensorLeft Y' ⊣ tensorLeft Y` of an exact pairing. -/
lemma tensorLeftAdjunction_counit_app (Y Y' : C) [ExactPairing Y Y'] (Z : C) :
    (tensorLeftAdjunction Y Y').counit.app Z = (α_ Y' Y Z).inv ≫ ε_ Y Y' ▷ Z ≫ (λ_ Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

section Dualizable

variable [F.Monoidal]

/-- The projection maps for `K` and for a left dual `K'` of `K`, followed by the evaluation of
the image pairing, give the evaluation of `(K, K')`. -/
lemma whiskerLeft_projectionMap_comp_projectionMap_comp_counit (K K' : C) [ExactPairing K K']
    (M : D) :
    letI := ExactPairing.map F K K'
    K' ◁ adj.projectionMap K M ≫ adj.projectionMap K' (F.obj K ⊗ M) ≫
        G.map ((tensorLeftAdjunction (F.obj K) (F.obj K')).counit.app M) =
      (tensorLeftAdjunction K K').counit.app (G.obj M) := by
  let := ExactPairing.map F K K'
  rw [tensorLeftAdjunction_counit_app, tensorLeftAdjunction_counit_app,
    ExactPairing.map_evaluation, G.map_comp, reassoc_of% (adj.projectionMap_assoc K K' M),
    ← G.map_comp]
  simp only [comp_whiskerRight, assoc, Functor.Monoidal.whiskerRight_δ_μ_assoc, G.map_comp]
  rw [← adj.projectionMap_whiskerRight_assoc (ε_ K K') M, ← G.map_comp, adj.projectionMap_unit]

variable [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] {a : C ⥤ D} (adj₂ : G ⊣ a)

/-- The inverse projection map for `K` is the mate of the projection map for a left dual `K'`,
for the adjunctions `(K' ⊗ -) ⊣ (K ⊗ -)` and `(F K' ⊗ -) ⊣ (F K ⊗ -)`. -/
lemma mateEquiv_projectionTwoSquare (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    mateEquiv (tensorLeftAdjunction (F.obj K) (F.obj K')) (tensorLeftAdjunction K K')
        (adj.projectionTwoSquare K') = adj.projectionInvTwoSquare K := by
  let := ExactPairing.map F K K'
  ext M
  apply ((tensorLeftAdjunction K K').homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit,
    projectionInvTwoSquare_natTrans_app, projectionTwoSquare_natTrans_app,
    ← adj.whiskerLeft_projectionMap_comp_projectionMap_comp_counit K K' M]
  simp

/-- **The comparison map is invertible at an object with a left dual.** For a strong monoidal
`F` with right adjoint `G`, invertible projection maps, and a right adjoint `a` of `G`, the
comparison map `F K ⊗ a L ⟶ a (K ⊗ L)` is invertible whenever `K` is part of an exact pairing
`(K, K')`: it is the conjugate of the projection map for `K'`. -/
theorem isIso_comparisonTwoSquare_of_exactPairing (K K' : C) [ExactPairing K K'] :
    IsIso (adj.comparisonTwoSquare adj₂ K) := by
  let := ExactPairing.map F K K'
  have key := iterated_mateEquiv_conjugateEquiv
    (tensorLeftAdjunction (F.obj K) (F.obj K')) (tensorLeftAdjunction K K') adj₂ adj₂
    (adj.projectionTwoSquare K')
  rw [adj.mateEquiv_projectionTwoSquare K K'] at key
  have : IsIso (conjugateEquiv ((tensorLeftAdjunction (F.obj K) (F.obj K')).comp adj₂)
      (adj₂.comp (tensorLeftAdjunction K K')) (adj.projectionTwoSquare K')) :=
    inferInstance
  rw [comparisonTwoSquare, key]
  exact this

/-- **The comparison map is invertible at an object with a left dual**, componentwise. -/
theorem isIso_comparisonMap_of_exactPairing (K K' : C) [ExactPairing K K'] (L : C) :
    IsIso (adj.comparisonMap adj₂ K L) := by
  have := adj.isIso_comparisonTwoSquare_of_exactPairing adj₂ K K'
  rw [← comparisonTwoSquare_natTrans_app]
  infer_instance

end Dualizable

end Adjunction

end CategoryTheory

end

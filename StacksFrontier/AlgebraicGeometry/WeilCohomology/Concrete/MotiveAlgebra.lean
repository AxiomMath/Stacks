module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProdTensorBridge
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointSummands
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorGraph
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Graphs, the diagonal, and the motive of a smooth projective scheme

Tools for the realization of Chow motives (Stacks 0FH1, 0FHK) in terms of the functor
`h : X ↦ (X, 1, 0)`, over an arbitrary field `k`.

* The tensor product of the graphs of two arbitrary morphisms of smooth projective schemes is the
  graph of their product (`Stacks.WeilCohomology.CorrespondenceCategory.tensorHom_graphHom_of_hom`,
  from `Stacks.WeilCohomology.tensor_graphCorr`), and its whiskered forms.
* The diagonal `X ⟶ X × X` and the structure morphism `X ⟶ Spec k` satisfy the comonoid
  identities: coassociativity, cocommutativity, counitality and naturality
  (`Stacks.WeilCohomology.SmoothProjectiveScheme.diag_whiskerRight_associator`, ...).
* `Stacks.WeilCohomology.ChowMotiveCat.mot X`: the motive `h(X)` as the triple `(X, 1, 0)`, with
  `gmap f = [Γ_f] : h(X) ⟶ h(Y)` for `f : Y ⟶ X` (`gmap_comp`) and the identity correspondence
  `tensorIsoHom X Y : h(X) ⊗ h(Y) ⟶ h(X × Y)`.

## Implementation notes

The motive `h(X)` is spelled `mot X = (X, 1, 0)` rather than `(h k).obj (op X)`: the two are
equal by `rfl` (`mot_eq`), but comparing hom-types or composites across the two spellings, or
across `h(X) ⊗ h(Y)` and `h(X × Y)`, makes `isDefEq` unfold scheme fibre products and limit
cones. Identities between correspondences are therefore proved on `TwistedKaroubi.Hom.val` with
the graph classes written as `homOf 0 (graphCorrespondenceSP f)` and rewritten to `graphHom` by
`homOf_graphCorrespondenceSP`.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public noncomputable section


open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The diagonal and the structure morphism of a smooth projective scheme -/

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The structure morphism `X ⟶ Spec k` as a morphism to the unit. -/
abbrev toUnit (X : (SmoothProjectiveScheme k).FullSubcategory) :
    X ⟶ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) :=
  toPoint X

/-- The diagonal `X ⟶ X ⊗ X`, with its target written as a tensor product. -/
abbrev tensorDiag (X : (SmoothProjectiveScheme k).FullSubcategory) : X ⟶ X ⊗ X := diag X

/-- There is a unique morphism to `Spec k`. -/
theorem toUnit_unique {X : (SmoothProjectiveScheme k).FullSubcategory}
    (f g : X ⟶ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) : f = g :=
  hom_ext_left (by
    have hf := Over.w f.hom
    have hg := Over.w g.hom
    simp only [tensorUnit_hom] at hf hg
    rw [← Category.comp_id f.hom.left, ← Category.comp_id g.hom.left]
    exact hf.trans hg.symm)

/-- The first projection of `X × W` composed with `f : X ⟶ Z` is `(f ▷ W)` followed by the first
projection of `Z × W`. -/
@[reassoc]
theorem whiskerRight_fst {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z)
    (W : (SmoothProjectiveScheme k).FullSubcategory) :
    (f ▷ W) ≫ fst Z W = fst X W ≫ f :=
  prodMapLeft_fst f W

/-- The morphism `f ▷ W` commutes with the second projections to `W`. -/
@[reassoc]
theorem whiskerRight_snd {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z)
    (W : (SmoothProjectiveScheme k).FullSubcategory) :
    (f ▷ W) ≫ snd Z W = snd X W :=
  prodMapLeft_snd f W

/-- The first projection of `f ⊗ₘ g` is `f` after the first projection. -/
@[reassoc]
theorem tensorHom_fst {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X)
    (g : Y' ⟶ Y) :
    (f ⊗ₘ g) ≫ fst X Y = fst X' Y' ≫ f :=
  prodMap_fst f g

/-- The second projection of `f ⊗ₘ g` is `g` after the second projection. -/
@[reassoc]
theorem tensorHom_snd {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X)
    (g : Y' ⟶ Y) :
    (f ⊗ₘ g) ≫ snd X Y = snd X' Y' ≫ g :=
  prodMap_snd f g

/-- The morphism `W ◁ f` commutes with the first projections to `W`. -/
@[reassoc]
theorem whiskerLeft_fst (W : (SmoothProjectiveScheme k).FullSubcategory)
    {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z) :
    (W ◁ f) ≫ fst W Z = fst W X := by
  rw [← MonoidalCategory.id_tensorHom, tensorHom_fst, Category.comp_id]

/-- The second projection of `W ◁ f` is `f` after the second projection. -/
@[reassoc]
theorem whiskerLeft_snd (W : (SmoothProjectiveScheme k).FullSubcategory)
    {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z) :
    (W ◁ f) ≫ snd W Z = snd W X ≫ f := by
  rw [← MonoidalCategory.id_tensorHom, tensorHom_snd]

/-- Coassociativity of the diagonal. -/
theorem diag_whiskerRight_associator (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (tensorDiag X ▷ X) ≫ (α_ X X X).hom = tensorDiag X ≫ (X ◁ tensorDiag X) := by
  have h : diag X ≫ prodMapLeft (diag X) X ≫ prodLift (fst (prod X X) X ≫ fst X X)
      (prodLift (fst (prod X X) X ≫ snd X X) (snd (prod X X) X)) =
      diag X ≫ prodMap (𝟙 X) (diag X) := by
    refine prod_hom_ext ?_ (prod_hom_ext ?_ ?_) <;> simp [diag_fst, diag_snd]
  rw [← MonoidalCategory.id_tensorHom]
  exact h

/-- Cocommutativity of the diagonal. -/
theorem diag_braiding (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (β_ X X).hom = tensorDiag X := by
  have h : diag X ≫ prodLift (snd X X) (fst X X) = diag X := by
    refine prod_hom_ext ?_ ?_ <;> simp [diag_fst, diag_snd]
  exact h

/-- Counit for the diagonal, on the left. -/
theorem diag_toUnit_whiskerRight (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (toUnit X ▷ X) ≫ (λ_ X).hom = 𝟙 X := by
  have h : diag X ≫ prodMapLeft (toPoint X) X ≫ snd (point k) X = 𝟙 X := by
    simp [diag_snd]
  exact h

/-- Counit for the diagonal, on the right. -/
theorem diag_whiskerLeft_toUnit (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (X ◁ toUnit X) ≫ (ρ_ X).hom = 𝟙 X := by
  have h : diag X ≫ prodMap (𝟙 X) (toPoint X) ≫ fst X (point k) = 𝟙 X := by
    simp [diag_fst]
  rw [← MonoidalCategory.id_tensorHom]
  exact h

/-- The diagonal is natural. -/
theorem diag_naturality {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    f ≫ tensorDiag Y = tensorDiag X ≫ (f ⊗ₘ f) := by
  have h : f ≫ diag Y = diag X ≫ prodMap f f := by
    refine prod_hom_ext ?_ ?_ <;> simp [diag_fst, diag_snd]
  exact h

/-- The diagonal of a product followed by the product of the projections is the identity. -/
theorem diag_tensorHom_fst_snd (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    diag (X ⊗ Y) ≫ (fst X Y ⊗ₘ snd X Y) = 𝟙 (X ⊗ Y) := by
  have h : diag (prod X Y) ≫ prodMap (fst X Y) (snd X Y) = 𝟙 (prod X Y) := by
    refine prod_hom_ext ?_ ?_ <;> simp [diag_fst_assoc, diag_snd_assoc]
  exact h

end SmoothProjectiveScheme

namespace CorrespondenceCategory

variable {k : Type u} [Field k]

/-- **The tensor product of two graphs is the graph of the tensor product**, for arbitrary
morphisms of smooth projective schemes. -/
theorem tensorHom_graphHom_of_hom {P Q P' Q' : (SmoothProjectiveScheme k).FullSubcategory}
    (u : Q ⟶ P) (v : Q' ⟶ P') :
    tensorHom (X₁ := GradedCompositionData.Obj.mk P) (Y₁ := GradedCompositionData.Obj.mk Q)
        (X₂ := GradedCompositionData.Obj.mk P') (Y₂ := GradedCompositionData.Obj.mk Q')
        (graphHom u) (graphHom v) = graphHom (u ⊗ₘ v) := by
  rw [graphHom, graphHom, graphHom, tensorHom_of_of]
  refine of_eq_of_heq (add_zero 0) ?_
  dsimp only
  refine (tensorCorr_heq _ _).trans ?_
  have t : tensor k P.obj.hom P'.obj.hom Q.obj.hom Q'.obj.hom (canonicalDiagonalClassFamily k) 0 0
      (graphCorrespondenceSP u) (graphCorrespondenceSP v) =
      corrCongr k (prodBase P.obj.hom P'.obj.hom) (prodBase Q.obj.hom Q'.obj.hom) (add_zero 0).symm
        (graphCorr k (prodBase P.obj.hom P'.obj.hom) (prodBase Q.obj.hom Q'.obj.hom)
          (prodHom P.obj.hom P'.obj.hom Q.obj.hom Q'.obj.hom u.hom.left v.hom.left (Over.w u.hom)
            (Over.w v.hom)) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) :=
    tensor_graphCorr k P.obj.hom P'.obj.hom Q.obj.hom Q'.obj.hom
      u.hom.left (Over.w u.hom) v.hom.left (Over.w v.hom)
  refine (heq_of_eq t).trans ?_
  refine (corrCongr_heq k _ _ _ _).trans ?_
  refine (graphCorr_heq k _ (P ⊗ P').obj.hom _ (Q ⊗ Q').obj.hom rfl HEq.rfl rfl HEq.rfl _
    (u ⊗ₘ v).hom.left _ (Over.w (u ⊗ₘ v).hom) HEq.rfl).trans ?_
  exact heq_of_eq (graphCorrespondenceSP_eq (u ⊗ₘ v)).symm

end CorrespondenceCategory

section GraphFunctor

variable (k : Type u) [Field k]

/-- The graph functor sends a morphism `f` to the graph class of `f.unop`. -/
theorem canonicalGraphFunctor_map {P Q : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ}
    (f : P ⟶ Q) :
    (canonicalGraphFunctor k).map f = graphHom f.unop :=
  rfl

/-- The graph functor sends `P` to `P.unop`, viewed as an object of the correspondence category. -/
theorem canonicalGraphFunctor_obj (P : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ) :
    (canonicalGraphFunctor k).obj P = GradedCompositionData.Obj.mk P.unop :=
  rfl

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme k) →
    CorrespondenceCategory k)

/-- Right whiskering the graph of `u` by `W` gives the graph of `u ▷ W`. -/
theorem graphHom_whiskerRight {P Q : (SmoothProjectiveScheme k).FullSubcategory} (u : Q ⟶ P)
    (W : (SmoothProjectiveScheme k).FullSubcategory) :
    (graphHom u : 𝐎 P ⟶ 𝐎 Q) ▷ 𝐎 W = graphHom (u ▷ W) := by
  rw [CorrespondenceCategory.whiskerRight_eq, CorrespondenceCategory.id_eq_graphHom,
    CorrespondenceCategory.tensorHom_graphHom_of_hom, MonoidalCategory.tensorHom_id]

/-- Left whiskering the graph of `u` by `W` gives the graph of `W ◁ u`. -/
theorem whiskerLeft_graphHom (W : (SmoothProjectiveScheme k).FullSubcategory)
    {P Q : (SmoothProjectiveScheme k).FullSubcategory} (u : Q ⟶ P) :
    𝐎 W ◁ (graphHom u : 𝐎 P ⟶ 𝐎 Q) = graphHom (W ◁ u) := by
  rw [CorrespondenceCategory.whiskerLeft_eq, CorrespondenceCategory.id_eq_graphHom,
    CorrespondenceCategory.tensorHom_graphHom_of_hom, MonoidalCategory.id_tensorHom]

/-- The graph functor commutes with right whiskering. -/
theorem canonicalGraphFunctor_whiskerRight {X Y : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ}
    (f : X ⟶ Y) (X' : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ) :
    (canonicalGraphFunctor k).map f ▷ (canonicalGraphFunctor k).obj X' =
      (canonicalGraphFunctor k).map (f ▷ X') :=
  graphHom_whiskerRight k f.unop X'.unop

/-- The graph functor commutes with left whiskering. -/
theorem canonicalGraphFunctor_whiskerLeft (X' : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ)
    {X Y : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ} (f : X ⟶ Y) :
    (canonicalGraphFunctor k).obj X' ◁ (canonicalGraphFunctor k).map f =
      (canonicalGraphFunctor k).map (X' ◁ f) :=
  whiskerLeft_graphHom k X'.unop f.unop

end GraphFunctor

/-! ### The motive of a smooth projective scheme is a commutative monoid -/

namespace ChowMotiveCat

variable {k : Type u} [Field k]

open CategoryTheory.GradedCategory SmoothProjectiveScheme

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme k) →
    CorrespondenceCategory k)

/-- The motive `h(X) = (X, 1, 0)` of a smooth projective scheme, as a triple; it is
`(h k).obj (op X)` (`Stacks.WeilCohomology.ChowMotiveCat.mot_eq`). -/
abbrev mot (X : (SmoothProjectiveScheme k).FullSubcategory) : ChowMotiveCat k :=
  TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)

/-- The motive `mot X` is the image of `X` under the functor `h`. -/
theorem mot_eq (X : (SmoothProjectiveScheme k).FullSubcategory) : mot X = (h k).obj (op X) := rfl

/-- The idempotent of `mot X` is the identity of `X`. -/
theorem mot_p (X : (SmoothProjectiveScheme k).FullSubcategory) : (mot X).p = 𝟙 (𝐎 X) := rfl

/-- The twist of `mot X` is zero. -/
theorem mot_twist (X : (SmoothProjectiveScheme k).FullSubcategory) : (mot X).twist = 0 := rfl

/-- The idempotent of `mot X ⊗ mot Y` is the identity. -/
theorem mot_tensor_p (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (mot X ⊗ mot Y).p = 𝟙 (mot X ⊗ mot Y).X :=
  MonoidalCategory.id_tensorHom_id _ _

/-- The unit motive is the motive of `Spec k`. -/
theorem tensorUnit_eq_mot :
    𝟙_ (ChowMotiveCat k) = mot (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) := rfl

/-- The morphism `h(f) = [Γ_f] : h(X) ⟶ h(Y)` of `f : Y ⟶ X`. -/
def gmap {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) : mot X ⟶ mot Y :=
  ⟨homOf 0 (graphCorrespondenceSP f), homOf_mem_grade _, Category.id_comp _, Category.comp_id _⟩

/-- The underlying correspondence of `gmap f` is the graph class of `f` in degree `0`. -/
theorem gmap_val {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) :
    (gmap f).val = homOf (X := X) (Y := Y) 0 (graphCorrespondenceSP f) := rfl

/-- Functoriality of `gmap`: `h(f) ≫ h(g) = h(g ≫ f)`. -/
theorem gmap_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) (g : Z ⟶ Y) :
    gmap f ≫ gmap g = gmap (g ≫ f) := by
  apply TwistedKaroubi.hom_ext
  simp only [TwistedKaroubi.comp_val, gmap_val, homOf_graphCorrespondenceSP]
  exact graphHom_comp f g

/-- The identity correspondence `h(X) ⊗ h(Y) ⟶ h(X × Y)`. -/
def tensorIsoHom (X Y : (SmoothProjectiveScheme k).FullSubcategory) : mot X ⊗ mot Y ⟶ mot (X ⊗ Y) :=
  ⟨𝟙 (mot X ⊗ mot Y).X, TwistedKaroubi.grade_cast (id_mem _) (by
      simp only [TwistedKaroubi.tensorObj_twist, mot_twist]; rfl),
    by rw [mot_tensor_p]; exact Category.id_comp _, Category.comp_id _⟩

/-- The identity correspondence `h(X × Y) ⟶ h(X) ⊗ h(Y)`. -/
def tensorIsoInv (X Y : (SmoothProjectiveScheme k).FullSubcategory) : mot (X ⊗ Y) ⟶ mot X ⊗ mot Y :=
  ⟨𝟙 (mot X ⊗ mot Y).X, TwistedKaroubi.grade_cast (id_mem _) (by
      simp only [TwistedKaroubi.tensorObj_twist, mot_twist]; rfl),
    Category.id_comp _, by rw [mot_tensor_p]; exact Category.comp_id _⟩

/-- The underlying correspondence of `tensorIsoHom X Y` is the identity. -/
theorem tensorIsoHom_val (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (tensorIsoHom X Y).val = 𝟙 (mot X ⊗ mot Y).X := rfl

/-- The underlying correspondence of `tensorIsoInv X Y` is the identity. -/
theorem tensorIsoInv_val (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (tensorIsoInv X Y).val = 𝟙 (mot X ⊗ mot Y).X := rfl

end ChowMotiveCat

end Stacks.WeilCohomology

end

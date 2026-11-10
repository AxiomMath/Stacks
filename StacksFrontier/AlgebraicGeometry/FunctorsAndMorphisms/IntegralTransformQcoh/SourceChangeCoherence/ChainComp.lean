module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence.ProjectionFormulaComp
import all StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence

/-!
# Vertical pasting of base-change squares, and the five-fold chain along a composite

Let `R` be a commutative ring, let `X` be an affine scheme over `R`, let `f : X' ⟶ X` be a
morphism of schemes over `R` whose underlying morphism of schemes is affine and let `Y` be a
scheme over `R`.  For a quasi-coherent kernel `K` on `X ×_R Y` the integral transform of `K`
precomposed with the direct image along `f` is the integral transform of the inverse image of
`K` on `X' ×_R Y`.  This file studies the compatibility of the ingredients of this identification
with composition of the morphism `f`.

## Main results

* `AlgebraicGeometry.baseChangeNatTrans_vpaste` and
  `AlgebraicGeometry.pushforwardSquareIso_vpaste`: the base-change morphism of Tag 02KG and the
  identification of the two composite direct images are compatible with stacking two commutative
  squares of schemes one above the other, so that the two vertical morphisms compose.
* `AlgebraicGeometry.mateEquiv_whiskerTop_eq`, `AlgebraicGeometry.mateEquiv_whiskerBottom_eq`,
  `AlgebraicGeometry.mateEquiv_hComp_eq` and `AlgebraicGeometry.mateEquiv_vpaste`: the mates
  bijection carries whiskerings of the top and the bottom edge of a 2-square to whiskerings by
  the two right adjoints, and a horizontal composite to a vertical composite.
* `AlgebraicGeometry.projectionFormulaSourceNatTrans_comp'`: the projection-formula morphism of
  Tag 0FZE along a composite, in the form in which the morphism is a composite up to a given
  equality and the comparison of the two iterated inverse images of the module on the target is
  prescribed, and `AlgebraicGeometry.pushforwardSourceChangeIso_comp'` is the same shape for the
  normalisation of the two composite direct images.
* `AlgebraicGeometry.projectionChain_comp` and `AlgebraicGeometry.sourceChangeChain_comp`: the
  chain of a base-change morphism, a braiding, a projection-formula morphism, the inverse
  braiding and a normalisation is compatible with composition, granted the composition laws of
  its four ingredients.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.IntegralTransformQcoh
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Scheme.Modules CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.Modules.Hom

/-! ### Whiskering identities -/

/-- Whiskering on the right after whiskering on the left is whiskering on the left after
whiskering on the right. -/
theorem whiskerRight_whiskerLeft_eq' {C D E E' : Type*} [Category C] [Category D]
    [Category E] [Category E'] (P : C ⥤ D) {F G : D ⥤ E} (α : F ⟶ G) (H : E ⥤ E') :
    Functor.whiskerRight (Functor.whiskerLeft P α) H =
      Functor.whiskerLeft P (Functor.whiskerRight α H) := rfl

/-- Whiskering on the left by a composite of two functors is whiskering on the left twice. -/
private theorem whiskerLeft_whiskerLeft_eq' {C D E E' : Type*} [Category C] [Category D]
    [Category E] [Category E'] (P : C ⥤ D) (G : D ⥤ E) {H J : E ⥤ E'} (x : H ⟶ J) :
    Functor.whiskerLeft P (Functor.whiskerLeft G x) = Functor.whiskerLeft (P ⋙ G) x := rfl

/-- Whiskering on the right by a composite of two functors is whiskering on the right twice. -/
private theorem whiskerRight_whiskerRight_eq {C D E E' : Type*} [Category C] [Category D]
    [Category E] [Category E'] {F G : C ⥤ D} (α : F ⟶ G) (H : D ⥤ E) (I : E ⥤ E') :
    Functor.whiskerRight (Functor.whiskerRight α H) I =
      Functor.whiskerRight α (H ⋙ I) := rfl

/-- Whiskering an identity on the right is an identity. -/
theorem whiskerRight_eq_id {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} (x : F ⟶ F) (W : D ⥤ E) (h : x = 𝟙 F) :
    Functor.whiskerRight x W = 𝟙 (F ⋙ W) :=
  (congrArg (fun z => Functor.whiskerRight z W) h).trans (Functor.whiskerRight_id' W)

/-- Whiskering an identity on the left is an identity. -/
private theorem whiskerLeft_eq_id {C D E : Type*} [Category C] [Category D] [Category E]
    (W : C ⥤ D) {F : D ⥤ E} (x : F ⟶ F) (h : x = 𝟙 F) :
    Functor.whiskerLeft W x = 𝟙 (W ⋙ F) :=
  (congrArg (Functor.whiskerLeft W) h).trans (Functor.whiskerLeft_id' W)

/-- An identity may be prefixed to a morphism. -/
private theorem id_head {E : Type*} [Category E] {A B : E} (e : A ⟶ A) (he : e = 𝟙 A)
    (x y : A ⟶ B) (h : x = y) : x = e ≫ y := by
  subst he h
  simp

/-- A whiskered isomorphism may be moved to the other side of an equation. -/
private theorem whiskerRight_iso_cancel {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (e : F ≅ G) (W : D ⥤ E) {T : C ⥤ E} (x : G ⋙ W ⟶ T) (y : F ⋙ W ⟶ T)
    (h : Functor.whiskerRight e.hom W ≫ x = y) :
    x = Functor.whiskerRight e.inv W ≫ y := by
  subst h
  rw [← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id, Functor.whiskerRight_id',
    Category.id_comp]

/-! ### Comparisons of direct and inverse images along equal morphisms -/

/-- The comparison of the direct images along two equal morphisms is the identity when the
equality is reflexive. -/
private theorem pushforwardCongr_rfl_hom {A B : Scheme.{u}} {f : A ⟶ B} (hf : f = f) :
    (Scheme.Modules.pushforwardCongr hf).hom = 𝟙 _ := by
  ext : 3
  simp

/-- The inverse comparison of the direct images along two equal morphisms is the identity when
the equality is reflexive. -/
theorem pushforwardCongr_rfl_inv {A B : Scheme.{u}} {f : A ⟶ B} (hf : f = f) :
    (Scheme.Modules.pushforwardCongr hf).inv = 𝟙 _ := by
  ext : 3
  simp

/-- The comparison of the inverse images along two equal morphisms is the identity when the
equality is reflexive. -/
theorem pullbackCongr_rfl_hom {A B : Scheme.{u}} {f : A ⟶ B} (hf : f = f) :
    (Scheme.Modules.pullbackCongr hf).hom = 𝟙 _ := rfl

/-- The comparison of the direct images along two equal morphisms, taken along the symmetric
equality, is the inverse comparison. -/
private theorem pushforwardCongr_symm_hom {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) :
    (Scheme.Modules.pushforwardCongr h.symm).hom =
      (Scheme.Modules.pushforwardCongr h).inv := by
  subst h
  rw [pushforwardCongr_rfl_hom, pushforwardCongr_rfl_inv]

/-! ### Identities among the comparisons of direct and inverse images -/

/-- The identification of the direct images along a composite of morphisms of schemes with the
composite of the direct images is the identity. -/
theorem pushforwardComp_hom_eq_id {A B C : Scheme.{u}} (g : A ⟶ B) (k : B ⟶ C) :
    (Scheme.Modules.pushforwardComp g k).hom = 𝟙 _ := rfl

/-- The inverse of the identification of the direct images along a composite of morphisms of
schemes with the composite of the direct images is the identity. -/
theorem pushforwardComp_inv_eq_id {A B C : Scheme.{u}} (g : A ⟶ B) (k : B ⟶ C) :
    (Scheme.Modules.pushforwardComp g k).inv = 𝟙 _ := rfl

/-- `AlgebraicGeometry.pushforwardComp_inv_eq_id` with the identity taken at the composite of
the two direct images. -/
theorem pushforwardComp_inv_eq_id' {A B C : Scheme.{u}} (g : A ⟶ B) (k : B ⟶ C) :
    (Scheme.Modules.pushforwardComp g k).inv =
      𝟙 (Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward k) := rfl

/-! ### Vertical pasting of base-change squares -/

section VerticalPaste

open Stacks.AlgebraicGeometry.AffinePushforward


/-- The associator of three functors is the identity. -/
private theorem associator_hom_eq_id {C D E E' : Type*} [Category C] [Category D] [Category E]
    [Category E'] {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} :
    (Functor.associator F G H).hom = 𝟙 _ := rfl

/-- The inverse associator of three functors is the identity. -/
private theorem associator_inv_eq_id {C D E E' : Type*} [Category C] [Category D] [Category E]
    [Category E'] {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} :
    (Functor.associator F G H).inv = 𝟙 _ := rfl

/-- The horizontal composite of two 2-squares, with the associators written out. -/
private theorem hComp_eq {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Category C₄] [Category C₅] [Category C₆] {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆}
    (x : TwoSquare T L R B) (y : TwoSquare T' R R' B') :
    TwoSquare.hComp x y =
      Functor.whiskerLeft T y ≫ Functor.whiskerRight x B' := by
  simp [TwoSquare.hComp, associator_hom_eq_id, associator_inv_eq_id]

/-- The vertical composite of two 2-squares, with the associators written out. -/
private theorem vComp_eq {C₁ C₂ C₃ C₄ C₇ C₈ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Category C₄] [Category C₇] [Category C₈] {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}
    (x : TwoSquare T L R B) (y : TwoSquare B L' R'' B'') :
    TwoSquare.vComp x y =
      Functor.whiskerRight x R'' ≫ Functor.whiskerLeft L y := by
  simp [TwoSquare.vComp, associator_hom_eq_id, associator_inv_eq_id]

section Mates

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The component of the mate of a 2-square, in the form in which the 2-square is a bare
natural transformation. -/
private theorem mateEquiv_app' {G : C ⥤ E} {H : D ⥤ F} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (d : D) :
    (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv]

/-- **The mate of a 2-square precomposed with a natural transformation of its top edge** is the
mate whiskered by the right adjoint on the left. -/
theorem mateEquiv_whiskerTop_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G G' : C ⥤ E} {H : D ⥤ F}
    (w : G' ⋙ L₂ ⟶ L₁ ⋙ H) (α : G ⟶ G') :
    mateEquiv adj₁ adj₂ (Functor.whiskerRight α L₂ ≫ w) =
      Functor.whiskerLeft R₁ α ≫ mateEquiv adj₁ adj₂ w := by
  refine NatTrans.ext (funext fun d => ?_)
  rw [mateEquiv_app']
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    mateEquiv_app', Category.assoc, Functor.map_comp]
  have hn := adj₂.unit.naturality (α.app (R₁.obj d))
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← reassoc_of% hn]

/-- **The mate of a 2-square postcomposed with a natural transformation of its bottom edge** is
the mate whiskered by the right adjoint on the right. -/
theorem mateEquiv_whiskerBottom_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C ⥤ E}
    {H H' : D ⥤ F} (w : G ⋙ L₂ ⟶ L₁ ⋙ H) (α : H ⟶ H') :
    mateEquiv adj₁ adj₂ (w ≫ Functor.whiskerLeft L₁ α) =
      mateEquiv adj₁ adj₂ w ≫ Functor.whiskerRight α R₂ := by
  refine NatTrans.ext (funext fun d => ?_)
  rw [mateEquiv_app']
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    mateEquiv_app', Category.assoc, ← Functor.map_comp]
  exact congrArg
    (fun t => adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (w.app (R₁.obj d) ≫ t))
    (α.naturality (adj₁.counit.app d)).symm

end Mates

section MateComp

variable {A₁ B₁ C₁ D₁ E₁ F₁ : Type*} [Category A₁] [Category B₁] [Category C₁] [Category D₁]
  [Category E₁] [Category F₁] {G₁ : A₁ ⥤ C₁} {G₂ : C₁ ⥤ E₁} {H₁ : B₁ ⥤ D₁} {H₂ : D₁ ⥤ F₁}
  {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : C₁ ⥤ D₁} {R₂ : D₁ ⥤ C₁} {L₃ : E₁ ⥤ F₁} {R₃ : F₁ ⥤ E₁}

/-- **The mate of a horizontal composite of 2-squares is the vertical composite of the two
mates**, with the composites written out as whiskerings. -/
theorem mateEquiv_hComp_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) :
    mateEquiv adj₁ adj₃ ((Functor.whiskerLeft G₁ β ≫ Functor.whiskerRight α H₂ :
        (G₁ ⋙ G₂) ⋙ L₃ ⟶ L₁ ⋙ H₁ ⋙ H₂)) =
      Functor.whiskerRight (mateEquiv adj₁ adj₂ α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) G₂ ≫
        Functor.whiskerLeft H₁ (mateEquiv adj₂ adj₃ β : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃) := by
  rw [← hComp_eq (TwoSquare.mk G₁ L₁ L₂ H₁ α) (TwoSquare.mk G₂ L₂ L₃ H₂ β),
    mateEquiv_vcomp adj₁ adj₂ adj₃ (TwoSquare.mk G₁ L₁ L₂ H₁ α) (TwoSquare.mk G₂ L₂ L₃ H₂ β),
    vComp_eq]

/-- **The mate of a horizontal composite of 2-squares whose top and bottom edges are corrected
by two natural transformations**: the corrections pass to the two outer whiskerings of the
vertical composite of the mates. -/
theorem mateEquiv_vpaste (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    {G : A₁ ⥤ E₁} {H : B₁ ⥤ F₁} (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂)
    (u : G ⟶ G₁ ⋙ G₂) (v : H₁ ⋙ H₂ ⟶ H) :
    mateEquiv adj₁ adj₃ ((Functor.whiskerRight u L₃ ≫
        ((Functor.whiskerLeft G₁ β ≫ Functor.whiskerRight α H₂ :
          (G₁ ⋙ G₂) ⋙ L₃ ⟶ L₁ ⋙ H₁ ⋙ H₂)) ≫
        Functor.whiskerLeft L₁ v : G ⋙ L₃ ⟶ L₁ ⋙ H)) =
      Functor.whiskerLeft R₁ u ≫
        (Functor.whiskerRight (mateEquiv adj₁ adj₂ α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) G₂ ≫
          Functor.whiskerLeft H₁ (mateEquiv adj₂ adj₃ β : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃)) ≫
        Functor.whiskerRight v R₃ := by
  rw [mateEquiv_whiskerTop_eq adj₁ adj₃, mateEquiv_whiskerBottom_eq adj₁ adj₃,
    mateEquiv_hComp_eq adj₁ adj₂ adj₃]

end MateComp

variable {X₂ X₁ X₀ S₂ S₁ S₀ : Scheme.{u}}
  {p₂ : S₂ ⟶ X₂} {p₁ : S₁ ⟶ X₁} {p₀ : S₀ ⟶ X₀}
  {a₂ : X₂ ⟶ X₁} {a₁ : X₁ ⟶ X₀} {b₂ : S₂ ⟶ S₁} {b₁ : S₁ ⟶ S₀}

/-- **The identification of the two composite direct images around a commutative square of
schemes is compatible with stacking two squares one above the other**: the identification for the
stacked square is the vertical composite of the two identifications, the direct images along the
two composite vertical morphisms being identified with the composites of the direct images. -/
theorem pushforwardSquareIso_vpaste {a : X₂ ⟶ X₀} {b : S₂ ⟶ S₀}
    (w₁ : p₁ ≫ a₁ = b₁ ≫ p₀) (w₂ : p₂ ≫ a₂ = b₂ ≫ p₁) (w : p₂ ≫ a = b ≫ p₀)
    (ha : a₂ ≫ a₁ = a) (hb : b₂ ≫ b₁ = b) :
    (pushforwardSquareIso w).hom =
      Functor.whiskerLeft (Scheme.Modules.pushforward p₂)
          ((Scheme.Modules.pushforwardCongr ha).inv ≫
            (Scheme.Modules.pushforwardComp a₂ a₁).inv) ≫
        (Functor.whiskerRight (pushforwardSquareIso w₂).hom
            (Scheme.Modules.pushforward a₁) ≫
          Functor.whiskerLeft (Scheme.Modules.pushforward b₂)
            (pushforwardSquareIso w₁).hom) ≫
        Functor.whiskerRight ((Scheme.Modules.pushforwardComp b₂ b₁).hom ≫
          (Scheme.Modules.pushforwardCongr hb).hom) (Scheme.Modules.pushforward p₀) := by
  refine NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun U => ?_)
  simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom]
  simp [← Functor.map_comp, ← op_comp]
  rfl

/-- The base-change morphism of Tag 02KG is the mate of the identification of the two composite
direct images around the square. -/
theorem mateEquiv_baseChangeNatTrans {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) :
    mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g')
        (Scheme.Modules.pullbackPushforwardAdjunction g) (baseChangeNatTrans w) =
      (pushforwardSquareIso w).hom := by
  rw [baseChangeNatTrans_eq]
  exact Equiv.apply_symm_apply _ _

/-- **The base-change morphism of a square stacked from two commutative squares of schemes is the
horizontal composite of the two base-change morphisms**, the direct images along the two composite
vertical morphisms being identified with the composites of the direct images. -/
theorem baseChangeNatTrans_vpaste {a : X₂ ⟶ X₀} {b : S₂ ⟶ S₀}
    (w₁ : p₁ ≫ a₁ = b₁ ≫ p₀) (w₂ : p₂ ≫ a₂ = b₂ ≫ p₁) (w : p₂ ≫ a = b ≫ p₀)
    (ha : a₂ ≫ a₁ = a) (hb : b₂ ≫ b₁ = b) :
    baseChangeNatTrans w =
      Functor.whiskerRight ((Scheme.Modules.pushforwardCongr ha).inv ≫
          (Scheme.Modules.pushforwardComp a₂ a₁).inv) (Scheme.Modules.pullback p₀) ≫
        (Functor.whiskerLeft (Scheme.Modules.pushforward a₂) (baseChangeNatTrans w₁) ≫
          Functor.whiskerRight (baseChangeNatTrans w₂) (Scheme.Modules.pushforward b₁)) ≫
        Functor.whiskerLeft (Scheme.Modules.pullback p₂)
          ((Scheme.Modules.pushforwardComp b₂ b₁).hom ≫
            (Scheme.Modules.pushforwardCongr hb).hom) := by
  rw [baseChangeNatTrans_eq]
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [mateEquiv_vpaste (Scheme.Modules.pullbackPushforwardAdjunction p₂)
      (Scheme.Modules.pullbackPushforwardAdjunction p₁)
      (Scheme.Modules.pullbackPushforwardAdjunction p₀)
      (baseChangeNatTrans w₂) (baseChangeNatTrans w₁) _ _,
    mateEquiv_baseChangeNatTrans, mateEquiv_baseChangeNatTrans,
    pushforwardSquareIso_vpaste w₁ w₂ w ha hb]

/-- `AlgebraicGeometry.baseChangeNatTrans_vpaste` for the composite of the two vertical
morphisms written out, so that only the comparison of the direct images along that composite
appears. -/
theorem baseChangeNatTrans_vpaste' {b : S₂ ⟶ S₀}
    (w₁ : p₁ ≫ a₁ = b₁ ≫ p₀) (w₂ : p₂ ≫ a₂ = b₂ ≫ p₁)
    (w : p₂ ≫ (a₂ ≫ a₁) = b ≫ p₀) (hb : b₂ ≫ b₁ = b) :
    baseChangeNatTrans w =
      Functor.whiskerRight (Scheme.Modules.pushforwardComp a₂ a₁).inv
          (Scheme.Modules.pullback p₀) ≫
        (Functor.whiskerLeft (Scheme.Modules.pushforward a₂) (baseChangeNatTrans w₁) ≫
          Functor.whiskerRight (baseChangeNatTrans w₂) (Scheme.Modules.pushforward b₁)) ≫
        Functor.whiskerLeft (Scheme.Modules.pullback p₂)
          ((Scheme.Modules.pushforwardComp b₂ b₁).hom ≫
            (Scheme.Modules.pushforwardCongr hb).hom) := by
  rw [baseChangeNatTrans_vpaste w₁ w₂ w rfl hb, pushforwardCongr_rfl_inv, Category.id_comp]

end VerticalPaste

/-! ### The projection formula along a composite, in whiskered form -/

section ProjectionComp


/-- A chain of morphisms whose middle factor is cancelled by two whiskerings of an isomorphism
of functors. -/
private theorem whisker_cancel {C₀ C D : Type*} [Category C₀] [Category C] [Category D]
    {R R' : C₀ ⥤ C} (σ : R ⟶ R') {F G : C ⥤ D} (e : F ≅ G) :
    Functor.whiskerLeft R e.hom ≫ Functor.whiskerRight σ G ≫
        Functor.whiskerLeft R' e.inv =
      Functor.whiskerRight σ F := by
  rw [Functor.whiskerLeft_comp_whiskerRight_assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.comp_id]

/-- **The projection-formula morphism of Tag 0FZE along a composite**, with the associators and
the identifications of the direct images along the composite written out as whiskerings. -/
theorem projectionFormulaSourceNatTrans_comp_norm {X₂ X₁ X₀ : Scheme.{u}} (g : X₂ ⟶ X₁)
    (k : X₁ ⟶ X₀) (H : X₀.Modules) :
    projectionFormulaSourceNatTrans (g ≫ k) H =
      Functor.whiskerRight (Scheme.Modules.pushforwardComp g k).inv
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (X₀.toRingedSpace).sheaf).flip.obj (H))) ≫
        Functor.whiskerLeft (Scheme.Modules.pushforward g)
          (projectionFormulaSourceNatTrans k H) ≫
        Functor.whiskerRight (projectionFormulaSourceNatTrans g
            ((Scheme.Modules.pullback k).obj H)) (Scheme.Modules.pushforward k) ≫
        Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X₂.toRingedSpace).sheaf).flip.obj (((Scheme.Modules.pullback g).obj
            ((Scheme.Modules.pullback k).obj H)))))
          (Scheme.Modules.pushforwardComp g k).hom ≫
        Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X₂.toRingedSpace).sheaf).flip.map
            ((Scheme.Modules.pullbackComp g k).hom.app H))
          (Scheme.Modules.pushforward (g ≫ k)) := by
  rw [projectionFormulaSourceNatTrans_comp g k H]
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp, pushforwardCompNatIso,
    pullbackCompNatIso, Iso.symm_inv, Category.assoc]
  rfl

/-- The projection-formula morphism of Tag 0FZE along a composite, with the identification of the
direct images along the composite moved to the two ends of the chain. -/
theorem projectionFormulaSourceNatTrans_comp_whisker {X₂ X₁ X₀ : Scheme.{u}} (g : X₂ ⟶ X₁)
    (k : X₁ ⟶ X₀) (H : X₀.Modules) :
    Functor.whiskerRight (Scheme.Modules.pushforwardComp g k).inv
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X₀.toRingedSpace).sheaf).flip.obj (H))) ≫
      Functor.whiskerLeft (Scheme.Modules.pushforward g)
        (projectionFormulaSourceNatTrans k H) ≫
      Functor.whiskerRight (projectionFormulaSourceNatTrans g
        ((Scheme.Modules.pullback k).obj H)) (Scheme.Modules.pushforward k) ≫
      Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X₂.toRingedSpace).sheaf).flip.map
          ((Scheme.Modules.pullbackComp g k).hom.app H))
        (Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward k) =
    projectionFormulaSourceNatTrans (g ≫ k) H ≫
      Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X₂.toRingedSpace).sheaf).flip.obj (((Scheme.Modules.pullback (g ≫ k)).obj H))))
        (Scheme.Modules.pushforwardComp g k).inv := by
  rw [projectionFormulaSourceNatTrans_comp_norm g k H]
  have cancellation := whisker_cancel
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X₂.toRingedSpace.sheaf).flip.map ((Scheme.Modules.pullbackComp g k).hom.app H))
    (Scheme.Modules.pushforwardComp g k)
  exact (congrArg (fun morphism => _ ≫ _ ≫ _ ≫ morphism) cancellation).symm.trans
    (Category.assoc _ _ _).symm

/-- **The projection-formula morphism of Tag 0FZE is compatible with composition of the
morphism**, in the form in which the morphism is a composite up to a given equality and the
comparison of the two iterated inverse images of the module on the target is prescribed. -/
theorem projectionFormulaSourceNatTrans_comp' {X₂ X₁ X₀ : Scheme.{u}} (g : X₂ ⟶ X₁)
    (k : X₁ ⟶ X₀) {m : X₂ ⟶ X₀} (hm : g ≫ k = m) (H : X₀.Modules)
    {ψ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback k).obj H) ⟶
      (Scheme.Modules.pullback m).obj H}
    (hψ : ψ = (Scheme.Modules.pullbackComp g k).hom.app H ≫
      (Scheme.Modules.pullbackCongr hm).hom.app H) :
    Functor.whiskerRight ((Scheme.Modules.pushforwardCongr hm).inv ≫
          (Scheme.Modules.pushforwardComp g k).inv)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X₀.toRingedSpace).sheaf).flip.obj (H))) ≫
      Functor.whiskerLeft (Scheme.Modules.pushforward g)
        (projectionFormulaSourceNatTrans k H) ≫
      Functor.whiskerRight (projectionFormulaSourceNatTrans g
        ((Scheme.Modules.pullback k).obj H)) (Scheme.Modules.pushforward k) ≫
      Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X₂.toRingedSpace).sheaf).flip.map ψ)
        (Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward k) =
    projectionFormulaSourceNatTrans m H ≫
      Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (X₂.toRingedSpace).sheaf).flip.obj (((Scheme.Modules.pullback m).obj H))))
        ((Scheme.Modules.pushforwardCongr hm).inv ≫
          (Scheme.Modules.pushforwardComp g k).inv) := by
  cases hm
  obtain rfl : ψ = (Scheme.Modules.pullbackComp g k).hom.app H := by
    simpa only [pullbackCongr_rfl_hom, NatTrans.id_app, Category.comp_id] using hψ
  rw [pushforwardCongr_rfl_inv (rfl : g ≫ k = g ≫ k),
    Category.id_comp ((Scheme.Modules.pushforwardComp g k).inv)]
  exact projectionFormulaSourceNatTrans_comp_whisker g k H

end ProjectionComp

/-! ### The normalisation of the two composite direct images along a composite -/

section PushforwardSourceChangeComp

variable (R : Type u) [CommRing R] (X X' X'' Y : Over (Spec (.of R)))
  (f' : X' ⟶ X) (f'' : X'' ⟶ X')

/-- **The normalisation of the two composite direct images of Tag 0FZB is compatible with
composition of the morphism**, with the comparison of the direct images along the two composites
moved to the front of the chain. -/
theorem pushforwardSourceChangeIso_comp' :
    (Scheme.Modules.pushforwardComp (sourceChangeMap R X X'' Y (f'' ≫ f'))
          (pullback.snd X.hom Y.hom) ≪≫
        Scheme.Modules.pushforwardCongr
          (sourceChangeMap_comp_snd R X X'' Y (f'' ≫ f'))).hom =
      Functor.whiskerRight ((Scheme.Modules.pushforwardCongr
            (sourceChangeMap_comp R X X' X'' Y f' f'')).inv ≫
          (Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'')
            (sourceChangeMap R X X' Y f')).inv)
          (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≫
        Functor.whiskerLeft (Scheme.Modules.pushforward (sourceChangeMap R X' X'' Y f''))
          (Scheme.Modules.pushforwardComp (sourceChangeMap R X X' Y f')
              (pullback.snd X.hom Y.hom) ≪≫
            Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X X' Y f')).hom ≫
        (Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'')
            (pullback.snd X'.hom Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X' X'' Y f'')).hom := by
  rw [pushforwardSourceChangeIso_comp R X X' X'' Y f' f'']
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, associator_hom_eq_id, Functor.whiskerRight_comp, Category.id_comp,
    Category.assoc]
  rw [pushforwardCongr_symm_hom (sourceChangeMap_comp R X X' X'' Y f' f'')]

end PushforwardSourceChangeComp

/-! ### The five-fold chain along a composite -/

section Chain

/-- Whiskering on the left by a composite of two functors is whiskering on the left twice. -/
private alias whiskerLeft_whiskerLeft_eq := whiskerLeft_whiskerLeft_eq'

/-- A natural transformation conjugated by an isomorphism of functors and its inverse, whiskered
on the two sides, is the transformation itself whiskered on the other side. -/
private theorem whisker_cancel₂ {C D : Type*} [Category C] [Category D] {F G : C ⥤ C}
    (e : F ≅ G) {H J : C ⥤ D} (x : H ⟶ J) :
    Functor.whiskerRight e.inv H ≫ Functor.whiskerLeft F x ≫ Functor.whiskerRight e.hom J =
      Functor.whiskerLeft G x := by
  rw [Functor.whiskerLeft_comp_whiskerRight, ← Category.assoc, ← Functor.whiskerRight_comp,
    Iso.inv_hom_id, Functor.whiskerRight_id', Category.id_comp]

/-- The middle of the chain: the two projection-formula morphisms and the inverse braiding
compose to the projection-formula morphism of the composite and the inverse braiding. -/
private theorem inner_id {A₁ B₁ C₁ : Type*} [Category A₁] [Category B₁] [Category C₁]
    {A : A₁ ⥤ B₁} {B : B₁ ⥤ C₁} {S : A₁ ⥤ C₁} {Rr : C₁ ⥤ C₁} {R' : B₁ ⥤ B₁}
    {L'' R'' Ls Rs : A₁ ⥤ A₁} (β'' : L'' ≅ R'') (βs : Ls ≅ Rs)
    (π' : B ⋙ Rr ⟶ R' ⋙ B) (π'' : A ⋙ R' ⟶ R'' ⋙ A) (πs : S ⋙ Rr ⟶ Rs ⋙ S)
    (κ : S ≅ A ⋙ B) (τ : L'' ⟶ Ls) (σ : R'' ⟶ Rs)
    (Hβ : β''.inv ≫ τ = σ ≫ βs.inv)
    (Hπ : Functor.whiskerRight κ.hom Rr ≫ Functor.whiskerLeft A π' ≫
        Functor.whiskerRight π'' B ≫ Functor.whiskerRight σ (A ⋙ B) =
      πs ≫ Functor.whiskerLeft Rs κ.hom) :
    Functor.whiskerRight κ.hom Rr ≫
        (Functor.whiskerLeft A π' ≫ Functor.whiskerRight π'' B ≫
          Functor.whiskerRight β''.inv (A ⋙ B)) ≫ Functor.whiskerRight τ (A ⋙ B) =
      πs ≫ Functor.whiskerRight βs.inv S ≫ Functor.whiskerLeft Ls κ.hom := by
  simp only [Category.assoc]
  rw [← Functor.whiskerRight_comp, Hβ, Functor.whiskerRight_comp]
  simp only [← Category.assoc] at Hπ ⊢
  rw [Hπ, Category.assoc, Category.assoc,
    Functor.whiskerLeft_comp_whiskerRight βs.inv κ.hom]

/-- The outer part of the chain: given the identity `hX` for its middle part and the composition
law `Hε` of the normalisations, the braiding at the front and the two normalisations at the back
assemble into the chain for the composite. -/
private theorem outer_assembly {A₁ B₁ C₁ Y₁ : Type*} [Category A₁] [Category B₁] [Category C₁]
    [Category Y₁] {A : A₁ ⥤ B₁} {B : B₁ ⥤ C₁} {S : A₁ ⥤ C₁} {Q : C₁ ⥤ Y₁} {Q' : B₁ ⥤ Y₁}
    {Q'' : A₁ ⥤ Y₁} {L Rr : C₁ ⥤ C₁} {L'' Ls Rs : A₁ ⥤ A₁}
    (β : L ≅ Rr) (βs : Ls ≅ Rs) (πs : S ⋙ Rr ⟶ Rs ⋙ S)
    (ε' : B ⋙ Q ⟶ Q') (ε'' : A ⋙ Q' ⟶ Q'') (εs : S ⋙ Q ⟶ Q'')
    (κ : S ≅ A ⋙ B) (τ : L'' ⟶ Ls) (X : (A ⋙ B) ⋙ Rr ⟶ L'' ⋙ A ⋙ B)
    (hX : Functor.whiskerRight κ.hom Rr ≫ X ≫ Functor.whiskerRight τ (A ⋙ B) =
      πs ≫ Functor.whiskerRight βs.inv S ≫ Functor.whiskerLeft Ls κ.hom)
    (Hε : εs = Functor.whiskerRight κ.hom Q ≫ Functor.whiskerLeft A ε' ≫ ε'') :
    Functor.whiskerRight κ.hom (L ⋙ Q) ≫
        Functor.whiskerLeft (A ⋙ B) (Functor.whiskerRight β.hom Q) ≫
        Functor.whiskerRight X Q ≫
        Functor.whiskerLeft L'' (Functor.whiskerLeft A ε' ≫ ε'') ≫
        Functor.whiskerRight τ Q'' =
      Functor.whiskerLeft S (Functor.whiskerRight β.hom Q) ≫
        Functor.whiskerRight πs Q ≫
        Functor.whiskerRight βs.inv (S ⋙ Q) ≫ Functor.whiskerLeft Ls εs := by
  have hb : Functor.whiskerRight κ.hom (Rr ⋙ Q) ≫ Functor.whiskerRight X Q ≫
        Functor.whiskerRight τ (A ⋙ B ⋙ Q) =
      Functor.whiskerRight πs Q ≫ Functor.whiskerRight βs.inv (S ⋙ Q) ≫
        Functor.whiskerLeft Ls (Functor.whiskerRight κ.hom Q) := by
    have h := congrArg (fun z : S ⋙ Rr ⟶ Ls ⋙ A ⋙ B => Functor.whiskerRight z Q) hX
    simp only [Functor.whiskerRight_comp] at h
    exact h
  rw [Hε, ← Functor.whiskerLeft_comp_whiskerRight_assoc κ.hom (Functor.whiskerRight β.hom Q),
    Functor.whiskerLeft_comp_whiskerRight τ (Functor.whiskerLeft A ε' ≫ ε''),
    reassoc_of% hb, ← Functor.whiskerLeft_comp]

/-- **The five-fold chain of a braiding, a projection-formula morphism, the inverse braiding and
a normalisation is compatible with composition**, granted the composition laws of the braiding,
of the projection-formula morphism and of the normalisation. -/
theorem projectionChain_comp {A₁ B₁ C₁ Y₁ : Type*} [Category A₁] [Category B₁] [Category C₁]
    [Category Y₁] {A : A₁ ⥤ B₁} {B : B₁ ⥤ C₁} {S : A₁ ⥤ C₁} {Q : C₁ ⥤ Y₁} {Q' : B₁ ⥤ Y₁}
    {Q'' : A₁ ⥤ Y₁} {L Rr : C₁ ⥤ C₁} {L' R' : B₁ ⥤ B₁} {L'' R'' Ls Rs : A₁ ⥤ A₁}
    (β : L ≅ Rr) (β' : L' ≅ R') (β'' : L'' ≅ R'') (βs : Ls ≅ Rs)
    (π' : B ⋙ Rr ⟶ R' ⋙ B) (π'' : A ⋙ R' ⟶ R'' ⋙ A) (πs : S ⋙ Rr ⟶ Rs ⋙ S)
    (ε' : B ⋙ Q ⟶ Q') (ε'' : A ⋙ Q' ⟶ Q'') (εs : S ⋙ Q ⟶ Q'')
    (κ : S ≅ A ⋙ B) (τ : L'' ⟶ Ls) (σ : R'' ⟶ Rs)
    (Hβ : β''.inv ≫ τ = σ ≫ βs.inv)
    (Hπ : Functor.whiskerRight κ.hom Rr ≫ Functor.whiskerLeft A π' ≫
        Functor.whiskerRight π'' B ≫ Functor.whiskerRight σ (A ⋙ B) =
      πs ≫ Functor.whiskerLeft Rs κ.hom)
    (Hε : εs = Functor.whiskerRight κ.hom Q ≫ Functor.whiskerLeft A ε' ≫ ε'') :
    Functor.whiskerRight κ.hom (L ⋙ Q) ≫
        Functor.whiskerLeft A (Functor.whiskerLeft B (Functor.whiskerRight β.hom Q) ≫
          Functor.whiskerRight π' Q ≫ Functor.whiskerRight β'.inv (B ⋙ Q) ≫
          Functor.whiskerLeft L' ε') ≫
        Functor.whiskerLeft A (Functor.whiskerRight β'.hom Q') ≫
        Functor.whiskerRight π'' Q' ≫
        Functor.whiskerRight β''.inv (A ⋙ Q') ≫
        Functor.whiskerLeft L'' ε'' ≫
        Functor.whiskerRight τ Q'' =
      Functor.whiskerLeft S (Functor.whiskerRight β.hom Q) ≫
        Functor.whiskerRight πs Q ≫
        Functor.whiskerRight βs.inv (S ⋙ Q) ≫ Functor.whiskerLeft Ls εs := by
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← Functor.whiskerLeft_comp_assoc A (Functor.whiskerLeft L' ε'),
    ← Functor.whiskerLeft_comp_assoc A (Functor.whiskerRight β'.inv (B ⋙ Q)),
    whisker_cancel₂ β' ε', whiskerLeft_whiskerLeft_eq A R' ε',
    Functor.whiskerLeft_comp_whiskerRight_assoc π'' ε',
    ← whiskerLeft_whiskerLeft_eq R'' A ε',
    Functor.whiskerLeft_comp_whiskerRight_assoc β''.inv (Functor.whiskerLeft A ε'),
    ← reassoc_of% (Functor.whiskerLeft_comp L'' (Functor.whiskerLeft A ε') ε'')]
  rw [reassoc_of% (show Functor.whiskerLeft A (Functor.whiskerRight π' Q) ≫
      Functor.whiskerRight π'' (B ⋙ Q) ≫ Functor.whiskerRight β''.inv (A ⋙ B ⋙ Q) =
    Functor.whiskerRight (Functor.whiskerLeft A π' ≫ Functor.whiskerRight π'' B ≫
      Functor.whiskerRight β''.inv (A ⋙ B)) Q from by
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp]
    rfl)]
  exact outer_assembly β βs πs ε' ε'' εs κ τ _ (inner_id β'' βs π' π'' πs κ τ σ Hβ Hπ) Hε

end Chain

section SourceChangeComp

open Stacks.AlgebraicGeometry.AffinePushforward

/-- **The chain of a base-change morphism, a braiding, a projection-formula morphism, the
inverse braiding and a normalisation is compatible with composition**, granted the composition
laws of the base-change morphism, of the braiding, of the projection-formula morphism and of the
normalisation. -/
theorem sourceChangeChain_comp {D₂ D₁ D₀ A₁ B₁ C₁ Y₁ : Type*} [Category D₂] [Category D₁]
    [Category D₀] [Category A₁] [Category B₁] [Category C₁] [Category Y₁]
    {Pf' : D₁ ⥤ D₀} {Pf'' : D₂ ⥤ D₁} {P : D₀ ⥤ C₁} {P' : D₁ ⥤ B₁} {P'' : D₂ ⥤ A₁}
    {A : A₁ ⥤ B₁} {B : B₁ ⥤ C₁} {S : A₁ ⥤ C₁} {Q : C₁ ⥤ Y₁} {Q' : B₁ ⥤ Y₁} {Q'' : A₁ ⥤ Y₁}
    {L Rr : C₁ ⥤ C₁} {L' R' : B₁ ⥤ B₁} {L'' R'' Ls Rs : A₁ ⥤ A₁}
    (β : L ≅ Rr) (β' : L' ≅ R') (β'' : L'' ≅ R'') (βs : Ls ≅ Rs)
    (π' : B ⋙ Rr ⟶ R' ⋙ B) (π'' : A ⋙ R' ⟶ R'' ⋙ A) (πs : S ⋙ Rr ⟶ Rs ⋙ S)
    (ε' : B ⋙ Q ⟶ Q') (ε'' : A ⋙ Q' ⟶ Q'') (εs : S ⋙ Q ⟶ Q'')
    (κ : S ≅ A ⋙ B) (τ : L'' ⟶ Ls) (σ : R'' ⟶ Rs)
    (bc' : Pf' ⋙ P ⟶ P' ⋙ B) (bc'' : Pf'' ⋙ P' ⟶ P'' ⋙ A)
    (bcs : (Pf'' ⋙ Pf') ⋙ P ⟶ P'' ⋙ S)
    (u : Pf'' ⋙ Pf' ⟶ Pf'' ⋙ Pf') (hu : u = 𝟙 _)
    (Hbc : bcs = Functor.whiskerRight u P ≫
      (Functor.whiskerLeft Pf'' bc' ≫ Functor.whiskerRight bc'' B) ≫
      Functor.whiskerLeft P'' κ.inv)
    (Hβ : β''.inv ≫ τ = σ ≫ βs.inv)
    (Hπ : Functor.whiskerRight κ.hom Rr ≫ Functor.whiskerLeft A π' ≫
        Functor.whiskerRight π'' B ≫ Functor.whiskerRight σ (A ⋙ B) =
      πs ≫ Functor.whiskerLeft Rs κ.hom)
    (Hε : εs = Functor.whiskerRight κ.hom Q ≫ Functor.whiskerLeft A ε' ≫ ε'')
    (γ : B ⋙ L ⋙ Q ⟶ L' ⋙ Q')
    (hγ : γ = Functor.whiskerLeft B (Functor.whiskerRight β.hom Q) ≫
      Functor.whiskerRight π' Q ≫ Functor.whiskerRight β'.inv (B ⋙ Q) ≫
      Functor.whiskerLeft L' ε')
    (t : P'' ⋙ L'' ⋙ Q'' ⟶ P'' ⋙ Ls ⋙ Q'')
    (ht : t = Functor.whiskerLeft P'' (Functor.whiskerRight τ Q'')) :
    Functor.whiskerLeft Pf'' (Functor.whiskerRight bc' (L ⋙ Q)) ≫
        Functor.whiskerLeft (Pf'' ⋙ P') γ ≫
        Functor.whiskerRight bc'' (L' ⋙ Q') ≫
        Functor.whiskerLeft P'' (Functor.whiskerLeft A (Functor.whiskerRight β'.hom Q') ≫
          Functor.whiskerRight π'' Q' ≫ Functor.whiskerRight β''.inv (A ⋙ Q') ≫
          Functor.whiskerLeft L'' ε'') ≫ t =
      Functor.whiskerRight bcs (L ⋙ Q) ≫
        Functor.whiskerLeft P'' (Functor.whiskerLeft S (Functor.whiskerRight β.hom Q) ≫
          Functor.whiskerRight πs Q ≫ Functor.whiskerRight βs.inv (S ⋙ Q) ≫
          Functor.whiskerLeft Ls εs) := by
  subst ht
  have hinner := whiskerRight_iso_cancel κ (L ⋙ Q) _ _
    (projectionChain_comp β β' β'' βs π' π'' πs ε' ε'' εs κ τ σ Hβ Hπ Hε)
  rw [Functor.whiskerLeft_comp_whiskerRight_assoc bc'' γ, Hbc]
  simp only [Functor.whiskerRight_comp, whiskerRight_whiskerLeft_eq',
    whiskerRight_whiskerRight_eq, Category.assoc]
  refine id_head _ (whiskerRight_eq_id u (P ⋙ L ⋙ Q) hu) _ _ ?_
  rw [← whiskerLeft_whiskerLeft_eq' P'' A γ]
  simp only [← Functor.whiskerLeft_comp, Category.assoc]
  rw [hγ, hinner]

end SourceChangeComp

end AlgebraicGeometry

end

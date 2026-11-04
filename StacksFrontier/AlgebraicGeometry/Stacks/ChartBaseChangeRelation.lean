module

public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFibrewisePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoid
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverMapCorners

/-!
# The relation of a base-changed chart (proof of Stacks 0DUQ)

Let `h : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S`, let `x : 𝒮_U ⟶ 𝒳` be a 1-morphism
from the algebraic stack of an object `U` of the big fppf site, and let `𝒰'` be a category fibred
in groupoids equivalent over the site to the 2-fibre product `𝒳' ×_𝒳 𝒮_U`, so that `𝒰'` carries a
chart `x' : 𝒰' ⟶ 𝒳'` and a 1-morphism `f : 𝒰' ⟶ 𝒮_U` with `h ∘ x' ≅ x ∘ f`. Write
`R = 𝒮_U ×_𝒳 𝒮_U` and `R' = 𝒰' ×_{𝒳'} 𝒰'` for the two self-intersections (Stacks 04T4). This file
constructs the induced 1-morphism `R' ⟶ R` and proves, in the source's words, that

    R' --f--> R          R' --f--> R
    |s'       |s         |t'       |t
    v         v          v         v
    U' --f--> U          U' --f--> U

are cartesian ("this follows for the first two by transitivity of fibre products"), as squares of
the presheaves representing the six categories. It also proves the pointwise content of the third
square of the source — that `G' = G ×_U U'` for the stabilizers — from the surjectivity of the maps
`Aut(a) ⟶ Aut(h a)` of automorphism groups: an arrow of `R'` whose image in `R` is an automorphism
is itself an automorphism.

## Main definitions

* `AlgebraicGeometry.Stack.ChartBaseChange.relationMap`: the 1-morphism `R' ⟶ R`.

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.isPullback_relationSource`: the source square is
  cartesian.
* `AlgebraicGeometry.Stack.ChartBaseChange.isPullback_relationTarget`: the target square is
  cartesian.
* `AlgebraicGeometry.Stack.ChartBaseChange.relationTarget_eq_relationSource`: the stabilizer
  property.

## Implementation notes

All three statements are checked over one object `W` of the site at a time through
`AlgebraicGeometry.Stack.isPullback_representingMap_of_fibrewise`: a section of a representing
presheaf over `W` is an isomorphism class of the fibre over `W`. The fibrewise arguments are the
source's "transitivity of fibre products", made explicit on the objects
`(W, a, u, α : h a ≅ x u)` of `𝒳' ×_𝒳 𝒮_U`.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

/-! ### Two facts about morphisms lying over identities -/

/-- An identity lies over the identity of any object its source lies over. -/
theorem isHomLift_id_of_obj_eq {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞) {a : 𝒜}
    {W : 𝒞} (h : p.obj a = W) : p.IsHomLift (𝟙 W) (𝟙 a) := by
  subst h
  infer_instance

/-- A morphism whose image under a functor over the base lies over `f` itself lies over `f`. -/
theorem isHomLift_of_isHomLift_map {𝒞 𝒜 𝒜' : Type*} [Category 𝒞] [Category 𝒜] [Category 𝒜']
    {p : 𝒜 ⥤ 𝒞} {q : 𝒜' ⥤ 𝒞} {K : 𝒜 ⥤ 𝒜'} (hK : K ⋙ q = p) {R T : 𝒞} (f : R ⟶ T) {a b : 𝒜}
    (φ : a ⟶ b) (h : q.IsHomLift f (K.map φ)) : p.IsHomLift f φ := by
  have ha : p.obj a = R := (Functor.congr_obj hK a).symm.trans (IsHomLift.domain_eq q f (K.map φ))
  have hb : p.obj b = T :=
    (Functor.congr_obj hK b).symm.trans (IsHomLift.codomain_eq q f (K.map φ))
  refine IsHomLift.of_fac' p f φ ha hb ?_
  have h1 : p.map φ = eqToHom (Functor.congr_obj hK a).symm ≫ q.map (K.map φ) ≫
      eqToHom (Functor.congr_obj hK b) := by
    have := Functor.congr_hom hK φ
    simp only [Functor.comp_map] at this
    rw [this]
    simp
  rw [h1, IsHomLift.fac' q f (K.map φ)]
  simp

/-- Both components of a morphism of a 2-fibre product lying over `f` lie over `f`. -/
private theorem isHomLift_a_and_b {𝒞 𝒳₁ 𝒴₁ 𝒮₁ : Type*} [Category 𝒞] [Category 𝒳₁] [Category 𝒴₁]
    [Category 𝒮₁] {p𝒳 : 𝒳₁ ⥤ 𝒞} {p𝒴 : 𝒴₁ ⥤ 𝒞} {p𝒮 : 𝒮₁ ⥤ 𝒞} {F : 𝒳₁ ⥤ 𝒮₁} {G : 𝒴₁ ⥤ 𝒮₁}
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (φ : P ⟶ Q) {R T : 𝒞} (f : R ⟶ T)
    [hφ : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift f φ] :
    p𝒳.IsHomLift f φ.a ∧ p𝒴.IsHomLift f φ.b := by
  obtain rfl : P.base = R :=
    IsHomLift.domain_eq (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G) f φ
  obtain rfl : Q.base = T :=
    IsHomLift.codomain_eq (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G) f φ
  have h : f = φ.hbase := by
    have hφ' : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift
        (R := (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G).obj P)
        (S := (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G).obj Q) f φ := hφ
    exact IsHomLift.eq_of_isHomLift (p := TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G) f φ
  subst h
  exact ⟨φ.ha, φ.hb⟩

/-- The `𝒳`-component of a morphism of a 2-fibre product lying over `f` lies over `f`. -/
theorem isHomLift_a {𝒞 𝒳₁ 𝒴₁ 𝒮₁ : Type*} [Category 𝒞] [Category 𝒳₁] [Category 𝒴₁]
    [Category 𝒮₁] {p𝒳 : 𝒳₁ ⥤ 𝒞} {p𝒴 : 𝒴₁ ⥤ 𝒞} {p𝒮 : 𝒮₁ ⥤ 𝒞} {F : 𝒳₁ ⥤ 𝒮₁} {G : 𝒴₁ ⥤ 𝒮₁}
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (φ : P ⟶ Q) {R T : 𝒞} (f : R ⟶ T)
    [hφ : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift f φ] :
    p𝒳.IsHomLift f φ.a :=
  (isHomLift_a_and_b φ f).1

/-- The `𝒴`-component of a morphism of a 2-fibre product lying over `f` lies over `f`. -/
theorem isHomLift_b {𝒞 𝒳₁ 𝒴₁ 𝒮₁ : Type*} [Category 𝒞] [Category 𝒳₁] [Category 𝒴₁]
    [Category 𝒮₁] {p𝒳 : 𝒳₁ ⥤ 𝒞} {p𝒴 : 𝒴₁ ⥤ 𝒞} {p𝒮 : 𝒮₁ ⥤ 𝒞} {F : 𝒳₁ ⥤ 𝒮₁} {G : 𝒴₁ ⥤ 𝒮₁}
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (φ : P ⟶ Q) {R T : 𝒞} (f : R ⟶ T)
    [hφ : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift f φ] :
    p𝒴.IsHomLift f φ.b :=
  (isHomLift_a_and_b φ f).2

/-- A composite of three morphisms lying over one identity lies over it. -/
theorem isHomLift_comp₃ {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞) {R : 𝒞}
    {a b c d : 𝒜} (f : a ⟶ b) (g : b ⟶ c) (k : c ⟶ d) (hf : p.IsHomLift (𝟙 R) f)
    (hg : p.IsHomLift (𝟙 R) g) (hk : p.IsHomLift (𝟙 R) k) : p.IsHomLift (𝟙 R) (f ≫ g ≫ k) :=
  inferInstance

/-- A composite of two morphisms lying over one identity lies over it. -/
theorem isHomLift_comp₂ {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞) {R : 𝒞}
    {a b c : 𝒜} (f : a ⟶ b) (g : b ⟶ c) (hf : p.IsHomLift (𝟙 R) f)
    (hg : p.IsHomLift (𝟙 R) g) : p.IsHomLift (𝟙 R) (f ≫ g) :=
  inferInstance

/-- An automorphism lying over an identity of the base is a vertical automorphism. -/
theorem mem_verticalAut_of_isHomLift {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R : 𝒞} {a : 𝒜} (τ : Aut a) (h : p.IsHomLift (𝟙 R) τ.hom) : τ ∈ p.verticalAut a := by
  rw [Functor.mem_verticalAut_iff, IsHomLift.fac' p (𝟙 R) τ.hom]
  simp

/-- A vertical automorphism lies over the identity of any object its object lies over. -/
theorem isHomLift_of_mem_verticalAut {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R : 𝒞} {a : 𝒜} (ha : p.obj a = R) (σ : p.verticalAut a) :
    p.IsHomLift (𝟙 R) (σ : Aut a).hom := by
  subst ha
  refine IsHomLift.of_fac' p _ _ rfl rfl ?_
  rw [Functor.verticalAut.cond σ]
  simp

/-- A morphism lying over `𝟙 W` lies over `𝟙 W` conjugated by two `eqToHom`s. -/
theorem isHomLift_eqToHom_conj {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R R' W : 𝒞} (e₁ : R = W) (e₂ : R' = W) {a b : 𝒜} (φ : a ⟶ b) (h : p.IsHomLift (𝟙 W) φ) :
    p.IsHomLift (eqToHom e₁ ≫ 𝟙 W ≫ eqToHom e₂.symm) φ := by
  subst e₁ e₂
  simpa using h

/-- A morphism of a category fibred in groupoids lying over an identity is an isomorphism. -/
theorem isIso_of_isHomLift_id {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) {R : 𝒞} {a b : 𝒜} (φ : a ⟶ b) (h : p.IsHomLift (𝟙 R) φ) :
    IsIso φ := by
  have := hp.isStronglyCartesian_homLift (𝟙 R) φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 R) φ

/-- A morphism of a category fibred in groupoids lying over an identity underlies an
isomorphism. -/
theorem exists_iso_of_isHomLift_id {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) {R : 𝒞} {a b : 𝒜} (φ : a ⟶ b) (h : p.IsHomLift (𝟙 R) φ) :
    ∃ e : a ≅ b, e.hom = φ := by
  have := isIso_of_isHomLift_id p hp φ h
  exact ⟨asIso φ, rfl⟩

/-! ### Identities of composites of morphisms -/

section Algebra

variable {C D : Type*} [Category C] [Category D]

/-- If `g ≫ k₁ ≫ k₂ ≫ ρ.inv = α.hom ≫ u` for isomorphisms `α` and `ρ`, then
`u ≫ ρ.hom = (α.inv ≫ g ≫ k₁) ≫ k₂`. -/
theorem algebra₁ {P Q T T' Y Z : C} (α : P ≅ Q) (u : Q ⟶ Y) (ρ : Y ≅ Z) (g : P ⟶ T)
    (k₁ : T ⟶ T') (k₂ : T' ⟶ Z) (hw : g ≫ k₁ ≫ k₂ ≫ ρ.inv = α.hom ≫ u) :
    u ≫ ρ.hom = (α.inv ≫ g ≫ k₁) ≫ k₂ := by
  rw [← cancel_epi α.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hw]
  simp

/-- Write `γᵢ = αᵢ.inv ≫ F.map ρᵢ.hom ≫ βᵢ.hom`. If `F.map χa ≫ β₂.hom = β₁.hom ≫ χb` and
`ψa ≫ γ₂ = γ₁ ≫ χb`, then `F.map (ρ₁.hom ≫ χa ≫ ρ₂.inv) ≫ α₂.hom = α₁.hom ≫ ψa`. -/
theorem algebra₂ (F : D ⥤ C) {a₁ b₁ a₂ b₂ : D} (ρ₁ : a₁ ≅ b₁) (ρ₂ : a₂ ≅ b₂) (χa : b₁ ⟶ b₂)
    {X₁ X₂ Y₁ Y₂ : C} (α₁ : F.obj a₁ ≅ X₁) (α₂ : F.obj a₂ ≅ X₂) (β₁ : F.obj b₁ ≅ Y₁)
    (β₂ : F.obj b₂ ≅ Y₂) (χb : Y₁ ⟶ Y₂) (ψa : X₁ ⟶ X₂)
    (hK : F.map χa ≫ β₂.hom = β₁.hom ≫ χb)
    (hψ : ψa ≫ (α₂.inv ≫ F.map ρ₂.hom ≫ β₂.hom) = (α₁.inv ≫ F.map ρ₁.hom ≫ β₁.hom) ≫ χb) :
    F.map (ρ₁.hom ≫ χa ≫ ρ₂.inv) ≫ α₂.hom = α₁.hom ≫ ψa := by
  have hψ' : ψa = (α₁.inv ≫ F.map ρ₁.hom ≫ β₁.hom) ≫ χb ≫ β₂.inv ≫ F.map ρ₂.inv ≫ α₂.hom := by
    rw [← cancel_mono (α₂.inv ≫ F.map ρ₂.hom ≫ β₂.hom), hψ]
    simp [← F.map_comp_assoc]
  rw [hψ']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [← reassoc_of% hK]
  simp

/-- If `t = s₁ ≫ s₂ ≫ ρ.inv`, then `t ≫ ρ.hom = s₁ ≫ s₂`. -/
theorem algebra₃ {X Y Z W : C} (t : X ⟶ Z) (s₁ : X ⟶ Y) (s₂ : Y ⟶ W) (ρ : Z ≅ W)
    (h : t = s₁ ≫ s₂ ≫ ρ.inv) : t ≫ ρ.hom = s₁ ≫ s₂ := by
  rw [h]; simp

/-- If `F.map σ.hom ≫ α₁.hom ≫ k ≫ ρ.hom = α₂.hom ≫ b`, then
`k ≫ ρ.hom = (α₁.inv ≫ F.map σ.inv ≫ α₂.hom) ≫ b`. -/
theorem algebra₄ (F : D ⥤ C) {a₁ a₂ : D} (σ : a₂ ≅ a₁) {Q₁ Q₂ Y Z : C} (α₁ : F.obj a₁ ≅ Q₁)
    (α₂ : F.obj a₂ ≅ Q₂) (k : Q₁ ⟶ Y) (ρ : Y ≅ Z) (b : Q₂ ⟶ Z)
    (hw : F.map σ.hom ≫ α₁.hom ≫ k ≫ ρ.hom = α₂.hom ≫ b) :
    k ≫ ρ.hom = (α₁.inv ≫ F.map σ.inv ≫ α₂.hom) ≫ b := by
  rw [Category.assoc, Category.assoc, ← hw]
  simp [← F.map_comp_assoc]

/-- Write `γᵢ = αᵢ.inv ≫ F.map ρᵢ.hom ≫ βᵢ.hom`. If `F.map χa ≫ α₂.hom = α₁.hom ≫ χb` and
`χb ≫ γ₂ = γ₁ ≫ ψb`, then `F.map (ρ₁.inv ≫ χa ≫ ρ₂.hom) ≫ β₂.hom = β₁.hom ≫ ψb`. -/
theorem algebra₅ (F : D ⥤ C) {a₁ b₁ a₂ b₂ : D} (ρ₁ : a₁ ≅ b₁) (ρ₂ : a₂ ≅ b₂) (χa : a₁ ⟶ a₂)
    {X₁ X₂ Y₁ Y₂ : C} (α₁ : F.obj a₁ ≅ X₁) (α₂ : F.obj a₂ ≅ X₂) (β₁ : F.obj b₁ ≅ Y₁)
    (β₂ : F.obj b₂ ≅ Y₂) (χb : X₁ ⟶ X₂) (ψb : Y₁ ⟶ Y₂)
    (hK : F.map χa ≫ α₂.hom = α₁.hom ≫ χb)
    (hψ : χb ≫ (α₂.inv ≫ F.map ρ₂.hom ≫ β₂.hom) = (α₁.inv ≫ F.map ρ₁.hom ≫ β₁.hom) ≫ ψb) :
    F.map (ρ₁.inv ≫ χa ≫ ρ₂.hom) ≫ β₂.hom = β₁.hom ≫ ψb := by
  have hψ' : ψb = β₁.inv ≫ F.map ρ₁.inv ≫ α₁.hom ≫ χb ≫ α₂.inv ≫ F.map ρ₂.hom ≫ β₂.hom := by
    rw [hψ]
    simp [← F.map_comp_assoc]
  rw [hψ']
  simp only [Iso.hom_inv_id_assoc, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hK]
  simp

/-- If `t = ρ.inv ≫ s₁ ≫ s₂`, then `s₁ ≫ s₂ = ρ.hom ≫ t`. -/
theorem algebra₆ {X Y Z W : C} (t : Y ⟶ W) (s₁ : X ⟶ Z) (s₂ : Z ⟶ W) (ρ : X ≅ Y)
    (h : t = ρ.inv ≫ s₁ ≫ s₂) : s₁ ≫ s₂ = ρ.hom ≫ t := by
  rw [h]; simp

/-- If `F.map σ = α.hom ≫ ε ≫ β.inv ≫ F.map ρ.inv`, then
`F.map (σ ≫ ρ.hom) ≫ β.hom = α.hom ≫ ε`. -/
theorem algebra₇ (F : D ⥤ C) {a b : D} (ρ : a ≅ b) (σ : a ⟶ a) {X Y : C} (α : F.obj a ≅ X)
    (β : F.obj b ≅ Y) (ε : X ⟶ Y) (hσ : F.map σ = α.hom ≫ ε ≫ β.inv ≫ F.map ρ.inv) :
    F.map (σ ≫ ρ.hom) ≫ β.hom = α.hom ≫ ε := by
  rw [Functor.map_comp, hσ]
  simp [← F.map_comp]

end Algebra

/-! ### The base-changed chart and the induced morphism of relations -/

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  {𝒰' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (eK : StacksRepresentableCFG.EquivalenceOver 𝒰'.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)

/-- The comparison `𝒰' ⟶ 𝒳' ×_𝒳 𝒮_U`, as a 1-morphism of categories fibred in groupoids. -/
noncomputable abbrev comparison : 𝒰' ⟶ (chartBaseChangeSquare h x).pt.val :=
  Bicategory.InducedBicategory.mkHom ⟨eK.hom.functor, eK.hom.w⟩

/-- The chart `x' : 𝒰' ⟶ 𝒳'`. -/
noncomputable abbrev chart' : 𝒰' ⟶ 𝒳'.val := comparison h x eK ≫ (chartBaseChangeSquare h x).fst.hom

/-- The 1-morphism `f : 𝒰' ⟶ 𝒮_U`. -/
noncomputable abbrev chartMap : 𝒰' ⟶ (schemeStack.{u, w} B S hS U).val :=
  comparison h x eK ≫ (chartBaseChangeSquare h x).snd.hom

/-- The 2-isomorphism `h ∘ x' ≅ x ∘ f`, read off the comparison isomorphisms of the objects of
`𝒳' ×_𝒳 𝒮_U`. -/
noncomputable def chartIso : CatFiberedInGroupoids.homFunctor (chart' h x eK) ⋙
      CatFiberedInGroupoids.homFunctor h.hom ≅
    CatFiberedInGroupoids.homFunctor (chartMap h x eK) ⋙ CatFiberedInGroupoids.homFunctor x.hom :=
  NatIso.ofComponents (fun w => (eK.hom.functor.obj w).iso)
    (fun m => (eK.hom.functor.map m).w)

/-- The component of `chartIso` at `w` is the comparison isomorphism of the image of `w` in
`𝒳' ×_𝒳 𝒮_U`. -/
@[simp]
theorem chartIso_hom_app (w : 𝒰'.val.obj) :
    (chartIso h x eK).hom.app w = (eK.hom.functor.obj w).iso.hom := rfl

/-- The inverse of the component of `chartIso` at `w` is the inverse of the comparison isomorphism
of the image of `w` in `𝒳' ×_𝒳 𝒮_U`. -/
@[simp]
theorem chartIso_inv_app (w : 𝒰'.val.obj) :
    (chartIso h x eK).inv.app w = (eK.hom.functor.obj w).iso.inv := rfl

/-- The base object of the image of an object of `𝒰'` is the base object of that object. -/
theorem comparison_base (w : 𝒰'.val.obj) :
    (eK.hom.functor.obj w).base = 𝒰'.val.p.obj w :=
  Functor.congr_obj eK.hom.w w

/-- The components of `chartIso` lie over identities. -/
theorem isHomLift_chartIso (w : 𝒰'.val.obj) :
    𝒳.val.val.p.IsHomLift
      (𝟙 (𝒳.val.val.p.obj ((CatFiberedInGroupoids.homFunctor h.hom).obj
        ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj w))))
      ((chartIso h x eK).hom.app w) := by
  have e : 𝒳.val.val.p.obj ((CatFiberedInGroupoids.homFunctor h.hom).obj
      ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj w)) =
      (eK.hom.functor.obj w).base :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p h.hom) _).trans
      (eK.hom.functor.obj w).hx
  rw [e]
  exact (eK.hom.functor.obj w).vertical

/-- The self-intersection `R = 𝒮_U ×_𝒳 𝒮_U`. -/
noncomputable abbrev rel : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val x.hom.hom

/-- The self-intersection `R' = 𝒰' ×_{𝒳'} 𝒰'`. -/
noncomputable abbrev rel' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  SelfIntersection.relation B S hS 𝒰' 𝒳'.val (chart' h x eK).hom

/-- **The induced 1-morphism `R' ⟶ R`**: an arrow `(W, w₁, w₂, ψ)` of `R'` goes to
`(W, f w₁, f w₂, (h ψ)` conjugated by the comparison isomorphisms of `w₁` and `w₂`). -/
noncomputable def relationMap : rel' h x eK ⟶ rel x :=
  Bicategory.InducedBicategory.mkHom
    ⟨TwoFibreProductOver.mapCorners
      (CatFiberedInGroupoids.homFunctor_comp_p (chartMap h x eK))
      (CatFiberedInGroupoids.homFunctor_comp_p (chartMap h x eK))
      (CatFiberedInGroupoids.homFunctor_comp_p h.hom) (chartIso h x eK) (chartIso h x eK)
      (isHomLift_chartIso h x eK) (isHomLift_chartIso h x eK),
      TwoFibreProductOver.mapCorners_comp_structureFunctor _ _ _ _ _ _ _⟩

/-- The source projection of a self-intersection, as a 1-morphism. -/
noncomputable abbrev relSnd {𝒰 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒰.val ⥤ᵇ 𝒴.val) : SelfIntersection.relation B S hS 𝒰 𝒴 f ⟶ 𝒰 :=
  Bicategory.InducedBicategory.mkHom
    ⟨TwoFibreProductOver.snd 𝒰.val.p 𝒰.val.p 𝒴.val.p f.toFunctor f.toFunctor,
      TwoFibreProductOver.snd_comp_eq⟩

/-- The target projection of a self-intersection, as a 1-morphism. -/
noncomputable abbrev relFst {𝒰 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒰.val ⥤ᵇ 𝒴.val) : SelfIntersection.relation B S hS 𝒰 𝒴 f ⟶ 𝒰 :=
  Bicategory.InducedBicategory.mkHom
    ⟨TwoFibreProductOver.fst 𝒰.val.p 𝒰.val.p 𝒴.val.p f.toFunctor f.toFunctor,
      TwoFibreProductOver.fst_comp_eq⟩

/-! ### Helpers for the fibrewise arguments -/

/-- The image of a morphism lying over `g` under the functor of a 1-morphism lies over `g`. -/
private theorem isHomLift_homFunctor_map
    {𝒳₁ 𝒴₁ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳₁ ⟶ 𝒴₁)
    {R T : BigFppfOver B S hS} (g : R ⟶ T) {a b : 𝒳₁.val.obj} (φ : a ⟶ b)
    [𝒳₁.val.p.IsHomLift g φ] : 𝒴₁.val.p.IsHomLift g ((CatFiberedInGroupoids.homFunctor f).map φ) :=
  Functor.isHomLift_map_of_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p f) g φ

/-- Over a category fibred in setoids, a morphism over `𝟙 W` is the image of any morphism over
`𝟙 W`. -/
private theorem eq_homFunctor_map_of_isHomLift_id
    {𝒳₁ 𝒴₁ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    [𝒴₁.val.p.IsFiberedInSetoids] (f : 𝒳₁ ⟶ 𝒴₁) {W : BigFppfOver B S hS} {a b : 𝒳₁.val.obj}
    (χ : a ⟶ b) [𝒳₁.val.p.IsHomLift (𝟙 W) χ]
    (θ : (CatFiberedInGroupoids.homFunctor f).obj a ⟶ (CatFiberedInGroupoids.homFunctor f).obj b)
    (hθ : 𝒴₁.val.p.IsHomLift (𝟙 W) θ) : θ = (CatFiberedInGroupoids.homFunctor f).map χ :=
  Functor.hom_unique_of_isFiberedInSetoids (𝟙 W) _ _ hθ (isHomLift_homFunctor_map f _ χ)

/-- If `R = W` and `e.hom` lies over `𝟙 R`, then `e.inv` lies over `𝟙 W`. -/
private theorem isHomLift_inv_of_eq {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R W : 𝒞} (hRW : R = W) {a b : 𝒜} (e : a ≅ b) (h : p.IsHomLift (𝟙 R) e.hom) :
    p.IsHomLift (𝟙 W) e.inv := by
  subst hRW
  infer_instance

/-- A morphism of a category fibred in groupoids lying over an identity underlies an isomorphism
whose hom and inverse both lie over that identity. -/
private theorem exists_iso_isHomLift_id {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) {R : 𝒞} {a b : 𝒜} (φ : a ⟶ b) (h : p.IsHomLift (𝟙 R) φ) :
    ∃ e : a ≅ b, p.IsHomLift (𝟙 R) e.hom ∧ p.IsHomLift (𝟙 R) e.inv := by
  obtain ⟨e, rfl⟩ := exists_iso_of_isHomLift_id p hp φ h
  exact ⟨e, h, isHomLift_inv_of_eq p rfl e h⟩

/-- A morphism lying over `𝟙 W` between images of objects under a full functor over the base is
the image of a morphism lying over `𝟙 W`. -/
private theorem exists_preimage_isHomLift {𝒞 𝒜 𝒜' : Type*} [Category 𝒞] [Category 𝒜]
    [Category 𝒜'] {p : 𝒜 ⥤ 𝒞} {q : 𝒜' ⥤ 𝒞} {K : 𝒜 ⥤ 𝒜'} [K.Full] (hK : K ⋙ q = p) {W : 𝒞}
    {a b : 𝒜} (m : K.obj a ⟶ K.obj b) (hm : q.IsHomLift (𝟙 W) m) :
    ∃ θ : a ⟶ b, K.map θ = m ∧ p.IsHomLift (𝟙 W) θ := by
  refine ⟨K.preimage m, K.map_preimage m, isHomLift_of_isHomLift_map hK _ _ ?_⟩
  rwa [K.map_preimage m]

/-! ### The source square -/

variable {U₀ U₀' R₀ R₀' : AlgebraicSpaces B S hS}
  (eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS U).val.val.p
    (presheafOfCategories (U₀.obj ⋙ typeToCat)).p)
  (eU' : StacksRepresentableCFG.EquivalenceOver 𝒰'.val.p
    (presheafOfCategories (U₀'.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver (rel x).val.p
    (presheafOfCategories (R₀.obj ⋙ typeToCat)).p)
  (eR' : StacksRepresentableCFG.EquivalenceOver (rel' h x eK).val.p
    (presheafOfCategories (R₀'.obj ⋙ typeToCat)).p)

include eU in
/-- If `𝒮_U` is equivalent over the site to a presheaf of sets, then it is fibred in setoids. -/
theorem isFiberedInSetoids_U : (schemeStack.{u, w} B S hS U).val.val.p.IsFiberedInSetoids :=
  SelfIntersection.isFiberedInSetoids_source eU

/-- **The source square is cartesian.** `R' = R ×_{s, U, f} U'`. -/
theorem isPullback_relationSource :
    IsPullback
      (representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK))
      (SelfIntersection.relationSourceMap eU' eR')
      (SelfIntersection.relationSourceMap eU eR)
      (representingMap B S hS _ _ U₀'.obj U₀.obj eU' eU (chartMap h x eK)) := by
  have hset := isFiberedInSetoids_U eU
  refine isPullback_representingMap_of_fibrewise eR' eR eU' eU (relationMap h x eK)
    (relSnd (chart' h x eK).hom) (relSnd x.hom.hom) (chartMap h x eK) ?_ ?_ ?_
  · intro z W hz
    exact ⟨𝟙 _, isHomLift_id_of_obj_eq _
      ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (chartMap h x eK)) z.y).trans
        (z.hy.trans hz))⟩
  · intro W r w₂ hr hw₂ φ hφ
    have hr' : r.base = W := hr
    subst hr'
    obtain ⟨ε, -, hε⟩ := exists_iso_isHomLift_id _
      (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids φ hφ
    have hq₂ : (eK.hom.functor.obj w₂).base = r.base := (comparison_base h x eK w₂).trans hw₂
    let q₁ : (chartBaseChangeSquare h x).pt.val.val.obj :=
      { base := r.base
        x := (eK.hom.functor.obj w₂).x
        y := r.x
        hx := (eK.hom.functor.obj w₂).hx.trans hq₂
        hy := r.hx
        iso := (eK.hom.functor.obj w₂).iso ≪≫
          (CatFiberedInGroupoids.homFunctor x.hom).mapIso ε.symm ≪≫ r.iso.symm
        vertical := by
          have h₁ : 𝒳.val.val.p.IsHomLift (𝟙 r.base) (eK.hom.functor.obj w₂).iso.hom := by
            rw [← hq₂]; exact (eK.hom.functor.obj w₂).vertical
          exact isHomLift_comp₃ _ _ _ _ h₁ (isHomLift_homFunctor_map x.hom (𝟙 r.base) ε.inv)
            (isHomLift_inv_of_eq _ rfl r.iso r.vertical) }
    let w₁ := eK.inv.functor.obj q₁
    let e₁ := eK.counitIso.app q₁
    have he₁ : (chartBaseChangeSquare h x).pt.val.val.p.IsHomLift (𝟙 r.base) e₁.hom :=
      eK.isHomLift_counitIso_hom_app q₁
    have he₁a : 𝒳'.val.val.p.IsHomLift (𝟙 r.base) e₁.hom.a :=
      isHomLift_a e₁.hom (𝟙 r.base) (hφ := he₁)
    have he₁b : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift (𝟙 r.base) e₁.hom.b :=
      isHomLift_b e₁.hom (𝟙 r.base) (hφ := he₁)
    have hw₁ : 𝒰'.val.p.obj w₁ = r.base := Functor.congr_obj eK.inv.w q₁
    let ψ' := (TwoFibreProductOver.fst (𝒳'.val.val.p) (schemeStack.{u, w} B S hS U).val.val.p
      𝒳.val.val.p h.hom.hom.toFunctor x.hom.hom.toFunctor).mapIso e₁
    let r' : (rel' h x eK).val.obj :=
      { base := r.base
        x := w₁
        y := w₂
        hx := hw₁
        hy := hw₂
        iso := ψ'
        vertical := he₁a }
    let ψ₀ : (CatFiberedInGroupoids.homFunctor (relationMap h x eK)).obj r' ⟶ r :=
      { hbase := 𝟙 r.base
        a := e₁.hom.b
        b := ε.inv
        ha := he₁b
        hb := hε
        w := algebra₁ (eK.hom.functor.obj w₁).iso
          ((CatFiberedInGroupoids.homFunctor x.hom).map e₁.hom.b) r.iso
          ((CatFiberedInGroupoids.homFunctor h.hom).map e₁.hom.a)
          (eK.hom.functor.obj w₂).iso.hom ((CatFiberedInGroupoids.homFunctor x.hom).map ε.inv)
          e₁.hom.w }
    exact ⟨r', rfl, ψ₀, 𝟙 w₂, IsHomLift.map (p := (rel x).val.p) ψ₀,
      isHomLift_id_of_obj_eq _ hw₂⟩
  · intro W r₁ r₂ hr₁ hr₂ ψ χ hψ hχ
    have hb₁ : r₁.base = W := hr₁
    have hb₂ : r₂.base = W := hr₂
    have hψb : ψ.b = (CatFiberedInGroupoids.homFunctor (chartMap h x eK)).map χ :=
      eq_homFunctor_map_of_isHomLift_id (chartMap h x eK) χ _ (isHomLift_b ψ (𝟙 W) (hφ := hψ))
    let K := eK.hom.functor
    have e₁ : (K.obj r₁.x).base = W := (comparison_base h x eK r₁.x).trans (r₁.hx.trans hb₁)
    have e₂ : (K.obj r₂.x).base = W := (comparison_base h x eK r₂.x).trans (r₂.hx.trans hb₂)
    have hma : 𝒳'.val.val.p.IsHomLift (𝟙 W) (r₁.iso.hom ≫
        (CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ ≫ r₂.iso.inv) := by
      have h₁ : 𝒳'.val.val.p.IsHomLift (𝟙 W) r₁.iso.hom := by rw [← hb₁]; exact r₁.vertical
      exact isHomLift_comp₃ _ _ _ _ h₁ (isHomLift_homFunctor_map (chart' h x eK) (𝟙 W) χ)
        (isHomLift_inv_of_eq _ hb₂ r₂.iso r₂.vertical)
    have hmb : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift (𝟙 W) ψ.a :=
      isHomLift_a ψ (𝟙 W) (hφ := hψ)
    have hψw : (CatFiberedInGroupoids.homFunctor x.hom).map ψ.a ≫
        ((K.obj r₂.x).iso.inv ≫ (CatFiberedInGroupoids.homFunctor h.hom).map r₂.iso.hom ≫
          (K.obj r₂.y).iso.hom) =
        ((K.obj r₁.x).iso.inv ≫ (CatFiberedInGroupoids.homFunctor h.hom).map r₁.iso.hom ≫
          (K.obj r₁.y).iso.hom) ≫ (CatFiberedInGroupoids.homFunctor x.hom).map (K.map χ).b := by
      have := ψ.w
      rwa [hψb] at this
    let m : K.obj r₁.x ⟶ K.obj r₂.x :=
      { hbase := eqToHom e₁ ≫ 𝟙 W ≫ eqToHom e₂.symm
        a := r₁.iso.hom ≫ (CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ ≫
          r₂.iso.inv
        b := ψ.a
        ha := isHomLift_eqToHom_conj _ e₁ e₂ _ hma
        hb := isHomLift_eqToHom_conj _ e₁ e₂ _ hmb
        w := algebra₂ (CatFiberedInGroupoids.homFunctor h.hom) r₁.iso r₂.iso (K.map χ).a
          (K.obj r₁.x).iso (K.obj r₂.x).iso (K.obj r₁.y).iso (K.obj r₂.y).iso
          ((CatFiberedInGroupoids.homFunctor x.hom).map (K.map χ).b)
          ((CatFiberedInGroupoids.homFunctor x.hom).map ψ.a) (K.map χ).w hψw }
    have : K.Full := eK.toEquivalence.full_functor
    obtain ⟨θa, hθa, hθaLift⟩ := exists_preimage_isHomLift eK.hom.w m
      (IsHomLift.of_fac' _ _ _ e₁ e₂ rfl)
    have hθaa : (K.map θa).a = r₁.iso.hom ≫
        (CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ ≫ r₂.iso.inv := by
      rw [hθa]; rfl
    let θ : r₁ ⟶ r₂ :=
      { hbase := eqToHom hr₁ ≫ 𝟙 W ≫ eqToHom hr₂.symm
        a := θa
        b := χ
        ha := isHomLift_eqToHom_conj _ hr₁ hr₂ _ hθaLift
        hb := isHomLift_eqToHom_conj _ hr₁ hr₂ _ hχ
        w := algebra₃ (K.map θa).a r₁.iso.hom
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ) r₂.iso hθaa }
    exact ⟨θ, IsHomLift.of_fac' _ _ θ hr₁ hr₂ rfl⟩

/-! ### The target square -/

/-- **The target square is cartesian.** `R' = R ×_{t, U, f} U'`. -/
theorem isPullback_relationTarget :
    IsPullback
      (representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK))
      (SelfIntersection.relationTargetMap eU' eR')
      (SelfIntersection.relationTargetMap eU eR)
      (representingMap B S hS _ _ U₀'.obj U₀.obj eU' eU (chartMap h x eK)) := by
  have hset := isFiberedInSetoids_U eU
  refine isPullback_representingMap_of_fibrewise eR' eR eU' eU (relationMap h x eK)
    (relFst (chart' h x eK).hom) (relFst x.hom.hom) (chartMap h x eK) ?_ ?_ ?_
  · intro z W hz
    exact ⟨𝟙 _, isHomLift_id_of_obj_eq _
      ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (chartMap h x eK)) z.x).trans
        (z.hx.trans hz))⟩
  · intro W r w₁ hr hw₁ φ hφ
    have hr' : r.base = W := hr
    subst hr'
    obtain ⟨ε, -, hε⟩ := exists_iso_isHomLift_id _
      (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids φ hφ
    have hq₁ : (eK.hom.functor.obj w₁).base = r.base := (comparison_base h x eK w₁).trans hw₁
    let q₂ : (chartBaseChangeSquare h x).pt.val.val.obj :=
      { base := r.base
        x := (eK.hom.functor.obj w₁).x
        y := r.y
        hx := (eK.hom.functor.obj w₁).hx.trans hq₁
        hy := r.hy
        iso := (eK.hom.functor.obj w₁).iso ≪≫
          (CatFiberedInGroupoids.homFunctor x.hom).mapIso ε.symm ≪≫ r.iso
        vertical := by
          have h₁ : 𝒳.val.val.p.IsHomLift (𝟙 r.base) (eK.hom.functor.obj w₁).iso.hom := by
            rw [← hq₁]; exact (eK.hom.functor.obj w₁).vertical
          exact isHomLift_comp₃ _ _ _ _ h₁ (isHomLift_homFunctor_map x.hom (𝟙 r.base) ε.inv)
            r.vertical }
    let w₂ := eK.inv.functor.obj q₂
    let e₂ := eK.counitIso.app q₂
    have he₂ : (chartBaseChangeSquare h x).pt.val.val.p.IsHomLift (𝟙 r.base) e₂.hom :=
      eK.isHomLift_counitIso_hom_app q₂
    have he₂a : 𝒳'.val.val.p.IsHomLift (𝟙 r.base) e₂.hom.a :=
      isHomLift_a e₂.hom (𝟙 r.base) (hφ := he₂)
    have he₂b : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift (𝟙 r.base) e₂.hom.b :=
      isHomLift_b e₂.hom (𝟙 r.base) (hφ := he₂)
    have hw₂ : 𝒰'.val.p.obj w₂ = r.base := Functor.congr_obj eK.inv.w q₂
    let σ := (TwoFibreProductOver.fst (𝒳'.val.val.p) (schemeStack.{u, w} B S hS U).val.val.p
      𝒳.val.val.p h.hom.hom.toFunctor x.hom.hom.toFunctor).mapIso e₂
    let r' : (rel' h x eK).val.obj :=
      { base := r.base
        x := w₁
        y := w₂
        hx := hw₁
        hy := hw₂
        iso := σ.symm
        vertical := @IsHomLift.lift_id_inv _ _ _ _ _ _ _ _ σ he₂a }
    let ψ₀ : (CatFiberedInGroupoids.homFunctor (relationMap h x eK)).obj r' ⟶ r :=
      { hbase := 𝟙 r.base
        a := ε.inv
        b := e₂.hom.b
        ha := hε
        hb := he₂b
        w := algebra₄ (CatFiberedInGroupoids.homFunctor h.hom) σ
          (eK.hom.functor.obj w₁).iso (eK.hom.functor.obj w₂).iso
          ((CatFiberedInGroupoids.homFunctor x.hom).map ε.inv) r.iso
          ((CatFiberedInGroupoids.homFunctor x.hom).map e₂.hom.b) e₂.hom.w }
    exact ⟨r', rfl, ψ₀, 𝟙 w₁, IsHomLift.map (p := (rel x).val.p) ψ₀,
      isHomLift_id_of_obj_eq _ hw₁⟩
  · intro W r₁ r₂ hr₁ hr₂ ψ χ hψ hχ
    have hb₁ : r₁.base = W := hr₁
    have hb₂ : r₂.base = W := hr₂
    have hψa : ψ.a = (CatFiberedInGroupoids.homFunctor (chartMap h x eK)).map χ :=
      eq_homFunctor_map_of_isHomLift_id (chartMap h x eK) χ _ (isHomLift_a ψ (𝟙 W) (hφ := hψ))
    let K := eK.hom.functor
    have e₁ : (K.obj r₁.y).base = W := (comparison_base h x eK r₁.y).trans (r₁.hy.trans hb₁)
    have e₂ : (K.obj r₂.y).base = W := (comparison_base h x eK r₂.y).trans (r₂.hy.trans hb₂)
    have hma : 𝒳'.val.val.p.IsHomLift (𝟙 W) (r₁.iso.inv ≫
        (CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ ≫ r₂.iso.hom) := by
      have h₃ : 𝒳'.val.val.p.IsHomLift (𝟙 W) r₂.iso.hom := by rw [← hb₂]; exact r₂.vertical
      exact isHomLift_comp₃ _ _ _ _ (isHomLift_inv_of_eq _ hb₁ r₁.iso r₁.vertical)
        (isHomLift_homFunctor_map (chart' h x eK) (𝟙 W) χ) h₃
    have hmb : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift (𝟙 W) ψ.b :=
      isHomLift_b ψ (𝟙 W) (hφ := hψ)
    have hψw : (CatFiberedInGroupoids.homFunctor x.hom).map (K.map χ).b ≫
        ((K.obj r₂.x).iso.inv ≫ (CatFiberedInGroupoids.homFunctor h.hom).map r₂.iso.hom ≫
          (K.obj r₂.y).iso.hom) =
        ((K.obj r₁.x).iso.inv ≫ (CatFiberedInGroupoids.homFunctor h.hom).map r₁.iso.hom ≫
          (K.obj r₁.y).iso.hom) ≫ (CatFiberedInGroupoids.homFunctor x.hom).map ψ.b := by
      have := ψ.w
      rwa [hψa] at this
    let m : K.obj r₁.y ⟶ K.obj r₂.y :=
      { hbase := eqToHom e₁ ≫ 𝟙 W ≫ eqToHom e₂.symm
        a := r₁.iso.inv ≫ (CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ ≫
          r₂.iso.hom
        b := ψ.b
        ha := isHomLift_eqToHom_conj _ e₁ e₂ _ hma
        hb := isHomLift_eqToHom_conj _ e₁ e₂ _ hmb
        w := algebra₅ (CatFiberedInGroupoids.homFunctor h.hom) r₁.iso r₂.iso (K.map χ).a
          (K.obj r₁.x).iso (K.obj r₂.x).iso (K.obj r₁.y).iso (K.obj r₂.y).iso
          ((CatFiberedInGroupoids.homFunctor x.hom).map (K.map χ).b)
          ((CatFiberedInGroupoids.homFunctor x.hom).map ψ.b) (K.map χ).w hψw }
    have : K.Full := eK.toEquivalence.full_functor
    obtain ⟨θb, hθb, hθbLift⟩ := exists_preimage_isHomLift eK.hom.w m
      (IsHomLift.of_fac' _ _ _ e₁ e₂ rfl)
    have hθba : (K.map θb).a = r₁.iso.inv ≫
        (CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ ≫ r₂.iso.hom := by
      rw [hθb]; rfl
    let θ : r₁ ⟶ r₂ :=
      { hbase := eqToHom hr₁ ≫ 𝟙 W ≫ eqToHom hr₂.symm
        a := χ
        b := θb
        ha := isHomLift_eqToHom_conj _ hr₁ hr₂ _ hχ
        hb := isHomLift_eqToHom_conj _ hr₁ hr₂ _ hθbLift
        w := algebra₆ (K.map θb).a ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).map χ)
          r₂.iso.hom r₁.iso hθba }
    exact ⟨θ, IsHomLift.of_fac' _ _ θ hr₁ hr₂ rfl⟩

/-! ### The stabilizer -/

/-- **The stabilizer property.** If `h` is surjective on the automorphism groups of objects, an
arrow of `R'` whose image in `R` has equal source and target has equal source and target. On
sections: `G' = G ×_U U'`, where `G` and `G'` are the stabilizers. -/
theorem relationTarget_eq_relationSource
    (hAut : ∀ a : 𝒳'.val.val.obj, Function.Surjective (automorphismGroupMap B S hS h a))
    (W : BigFppfOver B S hS) (v : R₀'.obj.obj (op W))
    (hv : (SelfIntersection.relationTargetMap eU eR).app (op W)
        ((representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W) v) =
      (SelfIntersection.relationSourceMap eU eR).app (op W)
        ((representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W) v)) :
    (SelfIntersection.relationTargetMap eU' eR').app (op W) v =
      (SelfIntersection.relationSourceMap eU' eR').app (op W) v := by
  obtain ⟨r, hr, rfl⟩ := PresheafOfCategories.exists_sectionOfObj eR' (W := W) v
  have hb : r.base = W := hr
  change (representingMap B S hS _ _ R₀.obj U₀.obj eR eU (relFst x.hom.hom)).app (op W)
      ((representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W)
        (PresheafOfCategories.sectionOfObj eR' r hr)) =
    (representingMap B S hS _ _ R₀.obj U₀.obj eR eU (relSnd x.hom.hom)).app (op W)
      ((representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W)
        (PresheafOfCategories.sectionOfObj eR' r hr)) at hv
  show (representingMap B S hS _ _ R₀'.obj U₀'.obj eR' eU' (relFst (chart' h x eK).hom)).app
      (op W) (PresheafOfCategories.sectionOfObj eR' r hr) =
    (representingMap B S hS _ _ R₀'.obj U₀'.obj eR' eU' (relSnd (chart' h x eK).hom)).app
      (op W) (PresheafOfCategories.sectionOfObj eR' r hr)
  simp only [representingMap_app_sectionOfObj] at hv ⊢
  let K := eK.hom.functor
  let εf := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eU _ _ hv
  have hεh : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift (𝟙 W) εf.hom.1 := εf.hom.2
  obtain ⟨ε, hεW, -⟩ := exists_iso_isHomLift_id _
    (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids εf.hom.1 hεh
  have e₁ : (K.obj r.x).base = W := (comparison_base h x eK r.x).trans (r.hx.trans hb)
  have e₂ : (K.obj r.y).base = W := (comparison_base h x eK r.y).trans (r.hy.trans hb)
  let τ : (CatFiberedInGroupoids.homFunctor h.hom).obj (K.obj r.x).x ≅
      (CatFiberedInGroupoids.homFunctor h.hom).obj (K.obj r.x).x :=
    (K.obj r.x).iso ≪≫ (CatFiberedInGroupoids.homFunctor x.hom).mapIso ε ≪≫ (K.obj r.y).iso.symm ≪≫
      (CatFiberedInGroupoids.homFunctor h.hom).mapIso r.iso.symm
  have hτ : 𝒳.val.val.p.IsHomLift (𝟙 W) τ.hom := by
    have h₁ : 𝒳.val.val.p.IsHomLift (𝟙 W) (K.obj r.x).iso.hom := by
      rw [← e₁]; exact (K.obj r.x).vertical
    have hri : 𝒳'.val.val.p.IsHomLift (𝟙 W) r.iso.inv := isHomLift_inv_of_eq _ hb r.iso r.vertical
    exact isHomLift_comp₃ _ _ _ _ h₁ (isHomLift_homFunctor_map x.hom (𝟙 W) ε.hom)
      (isHomLift_comp₂ _ _ _ (isHomLift_inv_of_eq _ e₂ (K.obj r.y).iso (K.obj r.y).vertical)
        (isHomLift_homFunctor_map h.hom (𝟙 W) r.iso.inv))
  obtain ⟨σ, hσ⟩ := hAut (K.obj r.x).x ⟨τ, mem_verticalAut_of_isHomLift _ τ hτ⟩
  have hσh : (CatFiberedInGroupoids.homFunctor h.hom).map (σ : Aut (K.obj r.x).x).hom =
      (K.obj r.x).iso.hom ≫ (CatFiberedInGroupoids.homFunctor x.hom).map ε.hom ≫
        (K.obj r.y).iso.inv ≫ (CatFiberedInGroupoids.homFunctor h.hom).map r.iso.inv :=
    congrArg (fun g : 𝒳.val.val.p.verticalAut _ => g.1.hom) hσ
  have hσL : 𝒳'.val.val.p.IsHomLift (𝟙 W) (σ : Aut (K.obj r.x).x).hom :=
    isHomLift_of_mem_verticalAut _ ((K.obj r.x).hx.trans e₁) σ
  have hrh : 𝒳'.val.val.p.IsHomLift (𝟙 W) r.iso.hom := by rw [← hb]; exact r.vertical
  let m : K.obj r.x ⟶ K.obj r.y :=
    { hbase := eqToHom e₁ ≫ 𝟙 W ≫ eqToHom e₂.symm
      a := (σ : Aut (K.obj r.x).x).hom ≫ r.iso.hom
      b := ε.hom
      ha := isHomLift_eqToHom_conj _ e₁ e₂ _ (isHomLift_comp₂ _ _ _ hσL hrh)
      hb := isHomLift_eqToHom_conj _ e₁ e₂ _ hεW
      w := algebra₇ (CatFiberedInGroupoids.homFunctor h.hom) r.iso (σ : Aut (K.obj r.x).x).hom
        (K.obj r.x).iso (K.obj r.y).iso ((CatFiberedInGroupoids.homFunctor x.hom).map ε.hom) hσh }
  have : K.Full := eK.toEquivalence.full_functor
  obtain ⟨θ, -, hθL⟩ := exists_preimage_isHomLift eK.hom.w m (IsHomLift.of_fac' _ _ _ e₁ e₂ rfl)
  exact PresheafOfCategories.sectionOfObj_eq_of_hom eU' _ _ θ hθL

end ChartBaseChange

end AlgebraicGeometry.Stack

end

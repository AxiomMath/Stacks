module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFiniteTypeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldRelocalize

/-!
# The change of base scheme for `Complexes`, the spaces

Let `g : T ⟶ S` be a morphism of the big fppf site, `D` a situation of Stacks 0DLE over `T`
whose base `D.Y` is final, and `D₁` a situation over `S` whose base is identified with the
representable presheaf of `g` by `eY`, and whose source is identified over it with the
lower-shriek extension `Λ_g D.X` of the source of `D` by `eX` (Stacks 04SG). This is the
situation of `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison`, collected in
`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum`.

A test scheme `A` over `D.Y` is a scheme `U` over `T`; it is matched with a test scheme `A₁` over
`D₁.Y` by an identification `β` of `U`, read over `S`, with the scheme of `A₁`, such that the
structural morphism of `A₁` reads `U ⟶ T`
(`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.Match`).
For a matched pair, the lower-shriek extension of the base change `X_A` is the base change
`X₁_{A₁}` (`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.Match.spaceIso`): both are
fibre products, and `Λ_g` preserves fibre products. These identifications are compatible with the
morphisms of base changes and with the projections to the test schemes.

Nothing here is registered: it is internal to the change-of-base comparison that the proof of
Stacks 0DLN uses.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum`: the data.
* `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.testScheme`: a test scheme over
  `D.Y`, read over `D₁.Y`.
* `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.Match.spaceIso`:
  `Λ_g X_A ≅ X₁_{A₁}`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04X4](https://stacks.math.columbia.edu/tag/04X4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {T S : Scheme.{u}} {hT : B.Contains T} {hS : B.Contains S}

/-- **The data of the change-of-base comparison for `Complexes`**: a morphism `g : T ⟶ S` of the
big fppf site, a situation `D` of Stacks 0DLE over `T` whose base is final, and a situation `D₁`
over `S` whose base is identified with the representable presheaf of `g` by `eY` and whose source,
over that presheaf, with the image of the source of `D` under the forward functor of Stacks 04SG
by `eX`. -/
structure ChangeOfBaseDatum (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T)
    (hS : B.Contains S) (g : B.obj hT ⟶ B.obj hS) where
  /-- The situation over the smaller base `T`. -/
  D : ComplexesSituation B T hT
  /-- Its base is final. -/
  isTerminal : IsTerminal D.Y
  /-- The situation over `S`. -/
  D₁ : ComplexesSituation B S hS
  /-- The base of `D₁` is the representable presheaf of `g`. -/
  eY : D₁.Y.obj ≅ yoneda.obj (Over.mk g)
  /-- The source of `D₁`, over the representable presheaf of `g`, is the image of the source
  of `D` under the forward functor of Stacks 04SG. -/
  eX : ((spacesOverSmallerBaseFunctor B T S hT hS g).obj D.X).1 ≅ Over.mk (D₁.f.hom ≫ eY.hom)

/-- The morphism of base changes of a situation commutes with the projections to the source. -/
private theorem relativeMap_hom_comp_baseChangeProjection {T' : Scheme.{u}} {hT' : B.Contains T'}
    (D : ComplexesSituation B T' hT') {A A' : SchemesOver D.Y} (k : A ⟶ A') :
    (D.relativeMap k).hom ≫ (baseChangeProjection D.f A').hom =
      (baseChangeProjection D.f A).hom :=
  congrArg (fun t => t.hom) (baseChangeMap_comp_projection D.f k)

/-- The morphism of base changes of a situation commutes with the projections to the test
schemes. -/
private theorem relativeMap_hom_comp_projection {T' : Scheme.{u}} {hT' : B.Contains T'}
    (D : ComplexesSituation B T' hT') {A A' : SchemesOver D.Y} (k : A ⟶ A') :
    (D.relativeMap k).hom ≫ (D.projection A').hom =
      (D.projection A).hom ≫ ((schemeSpaceFunctor B T' hT').map k.left).hom :=
  congrArg (fun t => t.hom) (baseChangeMap_comp_inclusion D.f k)

namespace ChangeOfBaseDatum

variable {g : B.obj hT ⟶ B.obj hS} (C : ChangeOfBaseDatum B hT hS g)

/-- The lower-shriek extension `Λ_g` along `g`, on presheaves. -/
local notation "Λg" => OverShriek.relocalizePresheafFunctor g

/-! ### The identifications of the source and of the base -/

/-- The representable presheaf of `g`, as the presheaf of the scheme `g` over `S`. -/
abbrev yonedaG : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  ((schemeSpaceFunctor B S hS).obj (Over.mk g)).obj

/-- `eY`, with its target spelled as the presheaf of the scheme `g` over `S`. -/
def eY' : C.D₁.Y.obj ≅ yonedaG (g := g) := C.eY

/-- The structural morphism `Λ_g F ⟶ h_g` of a lower-shriek extension. -/
def toPoint (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) : (Λg).obj F ⟶ yonedaG (g := g) :=
  OverShriek.relocalizeToYoneda g F

/-- The structural morphisms `Λ_g F ⟶ h_g` are natural in `F`. -/
@[reassoc]
theorem map_toPoint {F G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (k : F ⟶ G) :
    (Λg).map k ≫ toPoint G = toPoint (g := g) F :=
  relocalizeToYoneda_naturality B T S hT hS g k

/-- `Λ_g X ≅ X₁`. -/
def sourceIso : (Λg).obj C.D.X.obj ≅ C.D₁.X.obj :=
  ((spacesOverSmallerBaseFunctorForgetIso B T S hT hS g).app C.D.X).symm ≪≫
    (Over.forget _).mapIso C.eX

/-- Along `Λ_g X ≅ X₁`, the morphism `X₁ ⟶ Y₁ ≅ h_g` is the structural morphism of `Λ_g X`. -/
theorem sourceIso_hom_comp : C.sourceIso.hom ≫ C.D₁.f.hom ≫ C.eY'.hom = toPoint C.D.X.obj := by
  have h := relocalizeToYoneda_eq B T S hT hS g C.D.X
  have h2 := Over.w C.eX.hom
  exact (congrArg (fun k => ((spacesOverSmallerBaseFunctorForgetIso B T S hT hS g).inv.app C.D.X)
    ≫ k) h2).trans h

/-- `Λ_g Y ≅ Y₁`, through the identification of the final `Y` with the representable presheaf of
the identity of `T`. -/
def baseIso : (Λg).obj C.D.Y.obj ≅ C.D₁.Y.obj :=
  (Λg).mapIso (yonedaIsoOfIsTerminal C.isTerminal) ≪≫
    asIso (OverShriek.relocalizeToYoneda g (yoneda.obj (Over.mk (𝟙 (B.obj hT))))) ≪≫ C.eY.symm

/-- Along `Λ_g Y ≅ Y₁`, the identification `Y₁ ≅ h_g` is the structural morphism of `Λ_g Y`. -/
theorem baseIso_hom_comp : C.baseIso.hom ≫ C.eY'.hom = toPoint C.D.Y.obj := by
  have h := map_toPoint (g := g) (yonedaIsoOfIsTerminal C.isTerminal).hom
  refine Eq.trans ?_ h
  change (((Λg).map (yonedaIsoOfIsTerminal C.isTerminal).hom ≫
    OverShriek.relocalizeToYoneda g (yoneda.obj (Over.mk (𝟙 (B.obj hT))))) ≫ C.eY.inv) ≫
      C.eY.hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- `Λ_g f` is `f₁`, through the identifications of the sources and of the bases. -/
theorem map_f_comp_baseIso :
    (Λg).map C.D.f.hom ≫ C.baseIso.hom = C.sourceIso.hom ≫ C.D₁.f.hom := by
  rw [← cancel_mono C.eY'.hom, Category.assoc, Category.assoc, baseIso_hom_comp,
    sourceIso_hom_comp]
  exact map_toPoint _

/-! ### Test schemes -/

/-- The factorization through `T` of a scheme over `T`, read over `S`. -/
def point (U : BigFppfOver B T hT) : (Over.map g).obj U ⟶ Over.mk g :=
  Over.homMk U.hom

/-- A morphism of schemes over `T`, read over `S`, commutes with the factorizations through
`T`. -/
@[reassoc]
theorem map_comp_point {U U' : BigFppfOver B T hT} (k : U ⟶ U') :
    (Over.map g).map k ≫ point (g := g) U' = point U :=
  Over.OverMorphism.ext (Over.w k)

/-- The point of a scheme over `T`, as a morphism of presheaves to `h_g`. -/
abbrev pointHom (U : BigFppfOver B T hT) :
    ((schemeSpaceFunctor B S hS).obj ((Over.map g).obj U)).obj ⟶ yonedaG (g := g) :=
  ((schemeSpaceFunctor B S hS).map (point U)).hom

/-- The factorization through `T` that the structural morphism of a test scheme over `D₁.Y`
reads. -/
def targetPoint (A₁ : SchemesOver C.D₁.Y) : A₁.left ⟶ Over.mk g :=
  Yoneda.fullyFaithful.preimage (A₁.hom.hom ≫ C.eY'.hom)

/-- The factorization through `T` of a test scheme over `D₁.Y` induces, on presheaves, its
structural morphism followed by `Y₁ ≅ h_g`. -/
theorem targetPoint_spec (A₁ : SchemesOver C.D₁.Y) :
    ((schemeSpaceFunctor B S hS).map (C.targetPoint A₁)).hom = A₁.hom.hom ≫ C.eY'.hom :=
  Yoneda.fullyFaithful.map_preimage _

/-- A morphism of schemes over `S` between test schemes over `D₁.Y` that respects the
factorizations through `T` is a morphism of test schemes. -/
theorem w_of_targetPoint {A₁ A₁' : SchemesOver C.D₁.Y} (q : A₁.left ⟶ A₁'.left)
    (hq : q ≫ C.targetPoint A₁' = C.targetPoint A₁) :
    (schemeSpaceFunctor B S hS).map q ≫ A₁'.hom = A₁.hom := by
  apply ObjectProperty.hom_ext
  rw [← cancel_mono C.eY'.hom, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    ← targetPoint_spec, ← targetPoint_spec, ← ObjectProperty.FullSubcategory.comp_hom,
    ← CategoryTheory.Functor.map_comp, hq]

/-- A morphism of schemes over `S` between test schemes over `D₁.Y` that respects the
factorizations through `T`, as a morphism of test schemes. -/
def homMkOfTargetPoint {A₁ A₁' : SchemesOver C.D₁.Y} (q : A₁.left ⟶ A₁'.left)
    (hq : q ≫ C.targetPoint A₁' = C.targetPoint A₁) : A₁ ⟶ A₁' :=
  CostructuredArrow.homMk q (C.w_of_targetPoint q hq)

/-- A morphism of test schemes over `D₁.Y` respects the factorizations through `T`. -/
@[reassoc]
theorem left_comp_targetPoint {A₁ A₁' : SchemesOver C.D₁.Y} (y₁ : A₁ ⟶ A₁') :
    y₁.left ≫ C.targetPoint A₁' = C.targetPoint A₁ := by
  apply Yoneda.fullyFaithful.map_injective
  change ((schemeSpaceFunctor B S hS).map (y₁.left ≫ C.targetPoint A₁')).hom =
    ((schemeSpaceFunctor B S hS).map (C.targetPoint A₁)).hom
  rw [CategoryTheory.Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, targetPoint_spec,
    targetPoint_spec, ← Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    CostructuredArrow.w y₁]

/-- **A test scheme over `D.Y`, read over `D₁.Y`**: the scheme over `T`, read over `S`, with the
morphism to `D₁.Y` that its factorization through `T` defines. -/
abbrev testScheme (A : SchemesOver C.D.Y) : SchemesOver C.D₁.Y where
  left := (Over.map g).obj A.left
  right := ⟨⟨⟩⟩
  hom := (ObjectProperty.homMk (pointHom A.left ≫ C.eY'.inv) :
      (schemeSpaceFunctor B S hS).obj ((Over.map g).obj A.left) ⟶ C.D₁.Y)

/-- The factorization through `T` read by a test scheme over `D.Y`, read over `D₁.Y`, is its own
factorization through `T`. -/
theorem targetPoint_testScheme (A : SchemesOver C.D.Y) :
    C.targetPoint (C.testScheme A) = point A.left := by
  apply Yoneda.fullyFaithful.map_injective
  change ((schemeSpaceFunctor B S hS).map (C.targetPoint (C.testScheme A))).hom = pointHom A.left
  rw [targetPoint_spec]
  change (pointHom A.left ≫ C.eY'.inv) ≫ C.eY'.hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A morphism of test schemes over `D.Y`, read over `D₁.Y`. -/
def testSchemeMap {A A' : SchemesOver C.D.Y} (k : A ⟶ A') : C.testScheme A ⟶ C.testScheme A' :=
  C.homMkOfTargetPoint ((Over.map g).map k.left) (by
    rw [targetPoint_testScheme, targetPoint_testScheme, map_comp_point])

/-- The underlying morphism of `testSchemeMap k` is `k` read over `S`. -/
@[simp]
theorem testSchemeMap_left {A A' : SchemesOver C.D.Y} (k : A ⟶ A') :
    (C.testSchemeMap k).left = (Over.map g).map k.left :=
  rfl

/-- A morphism of test schemes over the final `D.Y` is a morphism of schemes over `T`. -/
def homOfLeft {A A' : SchemesOver C.D.Y} (k : A.left ⟶ A'.left) : A ⟶ A' :=
  CostructuredArrow.homMk k (C.isTerminal.hom_ext _ _)

/-- **A test scheme over `D.Y` matched with a test scheme over `D₁.Y`**: an identification `β` of
the first, read over `S`, with the second, along which the structural morphism of the second
reads the factorization of the first through `T`. -/
structure Match (A : SchemesOver C.D.Y) (A₁ : SchemesOver C.D₁.Y) where
  /-- The identification of the schemes over `S`. -/
  β : (Over.map g).obj A.left ≅ A₁.left
  /-- The structural morphism of `A₁` reads the factorization of `A` through `T`. -/
  w : β.hom ≫ C.targetPoint A₁ = point A.left

/-- A test scheme over `D.Y` is matched with itself read over `D₁.Y`. -/
def Match.refl (A : SchemesOver C.D.Y) : C.Match A (C.testScheme A) where
  β := Iso.refl _
  w := (Category.id_comp _).trans (C.targetPoint_testScheme A)

variable {C} in
/-- Two matched pairs, and morphisms of test schemes over `D.Y` and over `D₁.Y` that the
identifications carry to each other. -/
def Match.Compatible {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    (m : C.Match A A₁) (m' : C.Match A' A₁') (k : A ⟶ A') (k₁ : A₁ ⟶ A₁') : Prop :=
  m.β.hom ≫ k₁.left = (Over.map g).map k.left ≫ m'.β.hom

/-- A morphism of test schemes over `D.Y` and the same morphism read over `D₁.Y` are compatible
with the matches `Match.refl`. -/
theorem Match.compatible_refl {A A' : SchemesOver C.D.Y} (k : A ⟶ A') :
    (Match.refl C A).Compatible (Match.refl C A') k (C.testSchemeMap k) := by
  change (Iso.refl ((Over.map g).obj A.left)).hom ≫ (Over.map g).map k.left =
    (Over.map g).map k.left ≫ (Iso.refl ((Over.map g).obj A'.left)).hom
  simp

variable {C} in
/-- For a match `m`, the factorization through `T` that `A₁` reads is `m.β⁻¹` followed by the
factorization of `A` through `T`. -/
theorem Match.targetPoint_eq {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y}
    (m : C.Match A A₁) : C.targetPoint A₁ = m.β.inv ≫ point A.left := by
  rw [← m.w, Iso.inv_hom_id_assoc]

variable {C} in
/-- **A morphism of test schemes over `D.Y`, carried to the matched test schemes over `D₁.Y`.** -/
def Match.homOfSource {T₀ A : SchemesOver C.D.Y} {T₀₁ A₁ : SchemesOver C.D₁.Y}
    (m₀ : C.Match T₀ T₀₁) (m : C.Match A A₁) (y : T₀ ⟶ A) : T₀₁ ⟶ A₁ :=
  C.homMkOfTargetPoint (m₀.β.inv ≫ (Over.map g).map y.left ≫ m.β.hom) (by
    rw [Category.assoc, Category.assoc, m.w, map_comp_point, m₀.targetPoint_eq])

variable {C} in
/-- A morphism of test schemes over `D.Y` and its image `Match.homOfSource` are compatible. -/
theorem Match.compatible_homOfSource {T₀ A : SchemesOver C.D.Y} {T₀₁ A₁ : SchemesOver C.D₁.Y}
    (m₀ : C.Match T₀ T₀₁) (m : C.Match A A₁) (y : T₀ ⟶ A) :
    m₀.Compatible m y (m₀.homOfSource m y) := by
  change m₀.β.hom ≫ m₀.β.inv ≫ (Over.map g).map y.left ≫ m.β.hom = _
  rw [Iso.hom_inv_id_assoc]

variable {C} in
/-- For a morphism `y₁` of test schemes over `D₁.Y`, the morphism `β₀ ≫ y₁ ≫ β⁻¹` respects the
factorizations through `T`. -/
theorem Match.comp_point_eq {T₀ A : SchemesOver C.D.Y} {T₀₁ A₁ : SchemesOver C.D₁.Y}
    (m₀ : C.Match T₀ T₀₁) (m : C.Match A A₁) (y₁ : T₀₁ ⟶ A₁) :
    (m₀.β.hom ≫ y₁.left ≫ m.β.inv) ≫ point A.left = point T₀.left := by
  rw [Category.assoc, Category.assoc, ← m.targetPoint_eq, C.left_comp_targetPoint, m₀.w]

variable {C} in
/-- **A morphism of test schemes over `D₁.Y`, carried back to the matched test schemes over
`D.Y`.** It exists because the structural morphisms to `D₁.Y` read the factorizations through
`T`. -/
def Match.homOfTarget {T₀ A : SchemesOver C.D.Y} {T₀₁ A₁ : SchemesOver C.D₁.Y}
    (m₀ : C.Match T₀ T₀₁) (m : C.Match A A₁) (y₁ : T₀₁ ⟶ A₁) : T₀ ⟶ A :=
  C.homOfLeft (Over.homMk (m₀.β.hom ≫ y₁.left ≫ m.β.inv).left
    (congrArg (fun t => t.left) (m₀.comp_point_eq m y₁)))

variable {C} in
/-- A morphism of test schemes over `D₁.Y` and its image `Match.homOfTarget` are compatible. -/
theorem Match.compatible_homOfTarget {T₀ A : SchemesOver C.D.Y} {T₀₁ A₁ : SchemesOver C.D₁.Y}
    (m₀ : C.Match T₀ T₀₁) (m : C.Match A A₁) (y₁ : T₀₁ ⟶ A₁) :
    m₀.Compatible m (m₀.homOfTarget m y₁) y₁ := by
  have h : (Over.map g).map (m₀.homOfTarget m y₁).left = m₀.β.hom ≫ y₁.left ≫ m.β.inv :=
    Over.OverMorphism.ext rfl
  change _ = (Over.map g).map (m₀.homOfTarget m y₁).left ≫ m.β.hom
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **A test scheme over `D₁.Y`, read over `D.Y`**: its scheme, over `T` by the factorization
its structural morphism reads. -/
abbrev ofTarget (A₁ : SchemesOver C.D₁.Y) : SchemesOver C.D.Y where
  left := Over.mk (C.targetPoint A₁).left
  right := ⟨⟨⟩⟩
  hom := C.isTerminal.from _

/-- `A₁`, read over `D.Y` and back over `S`, is `A₁`. -/
def ofTargetIso (A₁ : SchemesOver C.D₁.Y) : (Over.map g).obj (C.ofTarget A₁).left ≅ A₁.left :=
  Over.isoMk (Iso.refl A₁.left.left) (by
    change 𝟙 _ ≫ A₁.left.hom = (C.targetPoint A₁).left ≫ g
    rw [Category.id_comp]
    exact (Over.w (C.targetPoint A₁)).symm)

/-- A test scheme over `D₁.Y` is matched with itself read over `D.Y`. -/
def Match.ofTarget (A₁ : SchemesOver C.D₁.Y) : C.Match (C.ofTarget A₁) A₁ where
  β := C.ofTargetIso A₁
  w := Over.OverMorphism.ext (Category.id_comp _)

/-! ### The base changes -/

/-- `Λ_g` of the representable presheaf of `U` is the representable presheaf of `U` read over
`S`. -/
def representedIso (U : BigFppfOver B T hT) :
    (Λg).obj ((schemeSpaceFunctor B T hT).obj U).obj ≅
      ((schemeSpaceFunctor B S hS).obj ((Over.map g).obj U)).obj :=
  relocalizedYonedaIso B (B.obj hT) (B.obj hS) g U

/-- Along `representedIso U`, the point of `U` is the structural morphism of `Λ_g h_U`. -/
theorem representedIso_hom_comp_pointHom (U : BigFppfOver B T hT) :
    (representedIso (g := g) U).hom ≫ pointHom U =
      toPoint ((schemeSpaceFunctor B T hT).obj U).obj := by
  ext W x
  rcases x with ⟨⟨ψ, f⟩, hψ⟩
  exact Over.OverMorphism.ext (Over.w f)

/-- The identifications `representedIso U` are natural in `U`. -/
@[reassoc]
theorem representedIso_naturality {U U' : BigFppfOver B T hT} (k : U ⟶ U') :
    (Λg).map ((schemeSpaceFunctor B T hT).map k).hom ≫ (representedIso (g := g) U').hom =
      (representedIso U).hom ≫ ((schemeSpaceFunctor B S hS).map ((Over.map g).map k)).hom :=
  relocalizedYonedaIso_naturality B (B.obj hT) (B.obj hS) g k

variable {C}

/-- `Λ_g` of the representable presheaf of `A`, identified with the representable presheaf of
`A₁` along a match. -/
def Match.testIso {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y} (m : C.Match A A₁) :
    (Λg).obj ((schemeSpaceFunctor B T hT).obj A.left).obj ≅
      ((schemeSpaceFunctor B S hS).obj A₁.left).obj :=
  representedIso A.left ≪≫ (ObjectProperty.ι _).mapIso ((schemeSpaceFunctor B S hS).mapIso m.β)

/-- The morphism of `m.testIso` is that of `representedIso` followed by the one induced by
`m.β`. -/
theorem Match.testIso_hom {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y} (m : C.Match A A₁) :
    m.testIso.hom = (representedIso A.left).hom ≫ ((schemeSpaceFunctor B S hS).map m.β.hom).hom :=
  rfl

/-- Along `Λ_g Y ≅ Y₁` and `m.testIso`, `Λ_g` of the structural morphism of `A` is the
structural morphism of `A₁`. -/
theorem Match.map_hom_comp_baseIso {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y}
    (m : C.Match A A₁) :
    (Λg).map A.hom.hom ≫ C.baseIso.hom = m.testIso.hom ≫ A₁.hom.hom := by
  rw [← cancel_mono C.eY'.hom, Category.assoc, Category.assoc, baseIso_hom_comp, map_toPoint,
    Match.testIso_hom, Category.assoc, ← targetPoint_spec,
    ← ObjectProperty.FullSubcategory.comp_hom,
    ← CategoryTheory.Functor.map_comp, m.w, representedIso_hom_comp_pointHom]

/-- The cartesian square of `X_A`, extended along `Λ_g` and read through the identifications of
the source, the base and the test scheme. -/
theorem Match.isPullback_relocalize {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y}
    (m : C.Match A A₁) :
    IsPullback ((Λg).map (baseChangeProjection C.D.f A).hom ≫ C.sourceIso.hom)
      ((Λg).map (C.D.projection A).hom ≫ m.testIso.hom) C.D₁.f.hom A₁.hom.hom := by
  have _ : PreservesLimitsOfShape WalkingCospan (Λg) :=
    relocalizePresheaf_preservesConnectedLimits g
  exact ((AlgebraicSpaces.isPullback_hom B T hT
      (AlgebraicSpaces.isPullback_fiberProduct B T hT C.D.f A.hom)).map (Λg)).of_iso
    (Iso.refl _) C.sourceIso m.testIso C.baseIso (Category.id_comp _).symm
    (Category.id_comp _).symm C.map_f_comp_baseIso
    m.map_hom_comp_baseIso

/-- **`Λ_g X_A ≅ X₁_{A₁}`** for a matched pair: both are fibre products of the same cospan. -/
def Match.spaceIso {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y} (m : C.Match A A₁) :
    (Λg).obj (C.D.space A).obj ≅ (C.D₁.space A₁).obj :=
  m.isPullback_relocalize.isoIsPullback _ _
    (AlgebraicSpaces.isPullback_hom B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS C.D₁.f A₁.hom))

/-- Along `m.spaceIso`, the projection of `X₁_{A₁}` to `A₁` is `Λ_g` of the projection of `X_A`
to `A`, followed by `m.testIso`. -/
@[reassoc]
theorem Match.spaceIso_hom_projection {A : SchemesOver C.D.Y} {A₁ : SchemesOver C.D₁.Y}
    (m : C.Match A A₁) :
    m.spaceIso.hom ≫ (C.D₁.projection A₁).hom =
      (Λg).map (C.D.projection A).hom ≫ m.testIso.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- Along `m.spaceIso`, the projection of `X₁_{A₁}` to `X₁` is `Λ_g` of the projection of `X_A`
to `X`, followed by `Λ_g X ≅ X₁`. -/
@[reassoc]
theorem Match.spaceIso_hom_baseChangeProjection {A : SchemesOver C.D.Y}
    {A₁ : SchemesOver C.D₁.Y} (m : C.Match A A₁) :
    m.spaceIso.hom ≫ (baseChangeProjection C.D₁.f A₁).hom =
      (Λg).map (baseChangeProjection C.D.f A).hom ≫ C.sourceIso.hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The identifications `Λ_g X_A ≅ X₁_{A₁}` carry the morphisms of base changes to each
other.** -/
theorem Match.spaceIso_hom_relativeMap {A A' : SchemesOver C.D.Y} {A₁ A₁' : SchemesOver C.D₁.Y}
    {m : C.Match A A₁} {m' : C.Match A' A₁'} {k : A ⟶ A'} {k₁ : A₁ ⟶ A₁'}
    (hk : m.Compatible m' k k₁) :
    m.spaceIso.hom ≫ (C.D₁.relativeMap k₁).hom =
      (Λg).map (C.D.relativeMap k).hom ≫ m'.spaceIso.hom := by
  have hβ : ((schemeSpaceFunctor B S hS).map m.β.hom).hom ≫
      ((schemeSpaceFunctor B S hS).map k₁.left).hom =
      ((schemeSpaceFunctor B S hS).map ((Over.map g).map k.left)).hom ≫
        ((schemeSpaceFunctor B S hS).map m'.β.hom).hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp, hk, Functor.map_comp,
      ObjectProperty.FullSubcategory.comp_hom]
  refine (AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS C.D₁.f A₁'.hom)).hom_ext ?_ ?_
  · change _ ≫ (baseChangeProjection C.D₁.f A₁').hom = _ ≫ (baseChangeProjection C.D₁.f A₁').hom
    rw [Category.assoc, Category.assoc, relativeMap_hom_comp_baseChangeProjection,
      Match.spaceIso_hom_baseChangeProjection, Match.spaceIso_hom_baseChangeProjection,
      ← Functor.map_comp_assoc, relativeMap_hom_comp_baseChangeProjection]
  · change _ ≫ (C.D₁.projection A₁').hom = _ ≫ (C.D₁.projection A₁').hom
    rw [Category.assoc, Category.assoc, relativeMap_hom_comp_projection,
      Match.spaceIso_hom_projection_assoc, Match.spaceIso_hom_projection,
      ← Functor.map_comp_assoc, relativeMap_hom_comp_projection, Functor.map_comp,
      Category.assoc, Match.testIso_hom, Match.testIso_hom, Category.assoc, hβ,
      representedIso_naturality_assoc]

end ChangeOfBaseDatum

end AlgebraicGeometry.Space.ComplexesSituation

end

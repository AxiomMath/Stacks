module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import StacksFrontier.AlgebraicGeometry.Quot.PointsOverBaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Quot.SpacePointsOverBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentableLimits

/-!
# Products and equations of algebraic spaces affine and of finite presentation over a base

Let `Y` be an algebraic space.  The functors on the test schemes over `Y` which are algebraic
spaces affine and of finite presentation over `Y` are stable under

* the pointwise product of two of them (the fibre product over `Y` of the two spaces), and
* cutting out, inside one of them `R`, the points `x` with `φ x = σ` for a morphism `φ : R ⟶ R'`
  to another one and a section `σ` of `R'` (the fibre product `H ×_{H'} Y` along the section).

These are the two fibre-product steps of the proof of Stacks 08K9.  For the second, a section
`s : Y ⟶ H'` of an affine morphism of finite presentation is a closed immersion (Stacks 03KP,
part (3)), hence affine (Stacks 07U2) and of finite presentation (Stacks 05WT), and its base
change `H ×_{H'} Y ⟶ H` is so too.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_and_isFinitePresentation_of_section`: a section of an
  affine morphism of finite presentation is affine and of finite presentation.
* `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.prod`: products.
* `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.sectionEqualizer`: the
  points of `R₁` carried by `φ : R₁ ⟶ R₂` to a section of `R₂`.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Sections of affine morphisms of finite presentation -/

/-- **A section of an affine morphism of finite presentation is affine and of finite
presentation.**  An affine morphism is separated, so the section is a closed immersion
(Stacks 03KP, part (3)), hence affine (Stacks 07U2), quasi-compact and quasi-separated; it is
locally of finite presentation by Stacks 05WT, its composite with `p` being the identity. -/
theorem isAffineHom_and_isFinitePresentation_of_section {H Y : AlgebraicSpaces B S hS}
    (p : H ⟶ Y) (hp : IsAffineHom B S hS p.hom) (hfp : IsFinitePresentation B S hS p.hom)
    (s : Y ⟶ H) (hs : s ≫ p = 𝟙 Y) :
    IsAffineHom B S hS s.hom ∧ IsFinitePresentation B S hS s.hom := by
  have hs' : s.hom ≫ p.hom = 𝟙 Y.1 := congrArg (fun k => k.hom) hs
  have hci : IsClosedImmersion B S hS s.hom :=
    isClosedImmersion_of_isSeparated_of_section B S hS p.hom
      (isSeparated_of_isAffineHom B S hS p.hom H.2 Y.2 hp) s.hom hs'
  refine ⟨isAffineHom_of_isClosedImmersion B S hS s.hom hci, ?_, ?_, ?_⟩
  · refine isLocallyOfFinitePresentation_of_comp B S hS Y.2 H.2 Y.2 s.hom p.hom ?_
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1)
    rw [hs']
    exact isLocallyOfFinitePresentation_id B S hS Y.2
  · exact isQuasiCompact_of_isClosedImmersion B S hS s.hom Y.2 H.2 hci
  · exact isQuasiSeparated_of_isClosedImmersion B S hS hci

/-! ### Products -/

section Product

variable {Y H₁ H₂ P : AlgebraicSpaces B S hS} {p₁ : H₁ ⟶ Y} {p₂ : H₂ ⟶ Y} {a₁ : P ⟶ H₁}
  {a₂ : P ⟶ H₂}

/-- The morphism of presheaves to the fibre product attached to two points over `Y`. -/
def spacePointsOverProdLift (sq : IsPullback a₁.hom a₂.hom p₁.hom p₂.hom) (T : SchemesOver Y)
    (x₁ : spacePointsOverObj p₁ T) (x₂ : spacePointsOverObj p₂ T) : yoneda.obj T.left ⟶ P.1 :=
  sq.lift (yonedaEquiv.symm x₁.1) (yonedaEquiv.symm x₂.1) (yonedaEquiv.injective (by
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      x₁.2, x₂.2]))

/-- The lift of a pair of points, followed by the first projection, is the first point. -/
@[reassoc (attr := simp)]
theorem spacePointsOverProdLift_fst (sq : IsPullback a₁.hom a₂.hom p₁.hom p₂.hom)
    (T : SchemesOver Y) (x₁ : spacePointsOverObj p₁ T) (x₂ : spacePointsOverObj p₂ T) :
    spacePointsOverProdLift sq T x₁ x₂ ≫ a₁.hom = yonedaEquiv.symm x₁.1 :=
  sq.lift_fst _ _ _

/-- The lift of a pair of points, followed by the second projection, is the second point. -/
@[reassoc (attr := simp)]
theorem spacePointsOverProdLift_snd (sq : IsPullback a₁.hom a₂.hom p₁.hom p₂.hom)
    (T : SchemesOver Y) (x₁ : spacePointsOverObj p₁ T) (x₂ : spacePointsOverObj p₂ T) :
    spacePointsOverProdLift sq T x₁ x₂ ≫ a₂.hom = yonedaEquiv.symm x₂.1 :=
  sq.lift_snd _ _ _

/-- **The points over `Y` of a fibre product `H₁ ×_Y H₂` are the pairs of points of `H₁` and of
`H₂` over `Y`.** -/
def spacePointsOverProdIso (sq : IsPullback a₁.hom a₂.hom p₁.hom p₂.hom) :
    spacePointsOver (a₁ ≫ p₁) ≅
      FunctorToTypes.prod (spacePointsOver p₁) (spacePointsOver p₂) :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun (x : spacePointsOverObj (a₁ ≫ p₁) T.unop) =>
          (⟨a₁.hom.app (op T.unop.left) x.1, x.2⟩,
            ⟨a₂.hom.app (op T.unop.left) x.1,
              ((congrArg (fun k => k.app (op T.unop.left) x.1) sq.w).symm).trans x.2⟩)
        invFun := fun (y : spacePointsOverObj p₁ T.unop × spacePointsOverObj p₂ T.unop) =>
          ⟨yonedaEquiv (spacePointsOverProdLift sq T.unop y.1 y.2), by
            change (a₁.hom ≫ p₁.hom).app _ _ = _
            rw [← yonedaEquiv_comp, ← Category.assoc, spacePointsOverProdLift_fst,
              yonedaEquiv_comp, Equiv.apply_symm_apply]
            exact y.1.2⟩
        left_inv := fun (x : spacePointsOverObj (a₁ ≫ p₁) T.unop) => Subtype.ext (by
          change yonedaEquiv (spacePointsOverProdLift sq T.unop _ _) = x.1
          refine (congrArg yonedaEquiv (sq.hom_ext (l := yonedaEquiv.symm x.1) ?_ ?_)).trans
            (yonedaEquiv.apply_symm_apply x.1)
          · rw [spacePointsOverProdLift_fst, yonedaEquiv_symm_naturality_right]
          · rw [spacePointsOverProdLift_snd, yonedaEquiv_symm_naturality_right])
        right_inv := fun (y : spacePointsOverObj p₁ T.unop × spacePointsOverObj p₂ T.unop) =>
          Prod.ext
          (Subtype.ext (by
            change a₁.hom.app _ (yonedaEquiv (spacePointsOverProdLift sq T.unop y.1 y.2)) = y.1.1
            rw [← yonedaEquiv_comp, spacePointsOverProdLift_fst, Equiv.apply_symm_apply]))
          (Subtype.ext (by
            change a₂.hom.app _ (yonedaEquiv (spacePointsOverProdLift sq T.unop y.1 y.2)) = y.2.1
            rw [← yonedaEquiv_comp, spacePointsOverProdLift_snd, Equiv.apply_symm_apply])) })
    (fun {T T'} g => ConcreteCategory.hom_ext _ _
      fun (x : spacePointsOverObj (a₁ ≫ p₁) T.unop) =>
        Prod.ext (α := spacePointsOverObj p₁ T'.unop) (β := spacePointsOverObj p₂ T'.unop)
          (Subtype.ext (NatTrans.naturality_apply a₁.hom g.unop.left.op x.1))
          (Subtype.ext (NatTrans.naturality_apply a₂.hom g.unop.left.op x.1)))

end Product

/-- The product of two functors to types, transported along isomorphisms of the factors. -/
def _root_.CategoryTheory.FunctorToTypes.prodMapIso {C : Type*} [Category* C]
    {F F' G G' : C ⥤ Type w} (e : F ≅ F') (e' : G ≅ G') :
    FunctorToTypes.prod F G ≅ FunctorToTypes.prod F' G' :=
  NatIso.ofComponents
    (fun X => Equiv.toIso ((e.app X).toEquiv.prodCongr (e'.app X).toEquiv))
    (fun {X X'} f => ConcreteCategory.hom_ext _ _ fun (x : F.obj X × G.obj X) =>
      Prod.ext (α := F'.obj X') (β := G'.obj X')
        (NatTrans.naturality_apply e.hom f x.1) (NatTrans.naturality_apply e'.hom f x.2))

/-- The universe lift of a product of functors to types is the product of the universe lifts. -/
def _root_.CategoryTheory.FunctorToTypes.prodCompUliftFunctorIso {C : Type*} [Category* C]
    (F G : C ⥤ Type u) :
    FunctorToTypes.prod F G ⋙ uliftFunctor.{u + 1, u} ≅
      FunctorToTypes.prod (F ⋙ uliftFunctor.{u + 1, u}) (G ⋙ uliftFunctor.{u + 1, u}) :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso (Equiv.ulift.trans (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)))
    (fun _ => rfl)

/-! ### Equations along a section -/

section Equation

variable {Y H H' : AlgebraicSpaces B S hS} {p : H ⟶ Y} {p' : H' ⟶ Y} (Φ : H ⟶ H') (s : Y ⟶ H')

/-- The points of `H` over `Y` at a test scheme `T` which `Φ : H ⟶ H'` carries to the point of
`H'` that the section `s : Y ⟶ H'` takes at `T`. -/
abbrev SpacePointsOverEqObj (p : H ⟶ Y) (T : SchemesOver Y) : Type u :=
  {x : spacePointsOverObj p T // Φ.hom.app (op T.left) x.1 = s.hom.app (op T.left) (testPoint T)}

/-- Restricting the section `s` at the point `testPoint T` along `g : U ⟶ T` gives its point at
`U`. -/
private theorem map_section_testPoint {Y H' : AlgebraicSpaces B S hS} (s : Y ⟶ H')
    {U T : SchemesOver Y} (g : U ⟶ T) :
    H'.1.map g.left.op (s.hom.app (op T.left) (testPoint T)) =
      s.hom.app (op U.left) (testPoint U) :=
  (NatTrans.naturality_apply s.hom ..).symm.trans (congrArg _ (testPoint_naturality g))

/-- A point of `H` over `Y` carried by `Φ` to the section `s`, restricted along a morphism of
test schemes, is still carried to the section. -/
theorem spacePointsOverEq_restrict {U T : SchemesOver Y} (g : U ⟶ T)
    (x : SpacePointsOverEqObj Φ s p T) :
    Φ.hom.app (op U.left) (H.1.map g.left.op x.1.1) =
      s.hom.app (op U.left) (testPoint U) := by
  rw [NatTrans.naturality_apply, x.2, map_section_testPoint]

/-- **The points of `H` over `Y` carried by `Φ : H ⟶ H'` to a section `s : Y ⟶ H'`**, as a
functor on the test schemes over `Y`. -/
def spacePointsOverEq (p : H ⟶ Y) : (SchemesOver Y)ᵒᵖ ⥤ Type u where
  obj T := SpacePointsOverEqObj Φ s p T.unop
  map {T T'} g := ↾fun x ↦
    ⟨⟨H.1.map g.unop.left.op x.1.1, spacePointsOver_restrict g.unop x.1⟩,
      spacePointsOverEq_restrict Φ s g.unop x⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext (Subtype.ext ?_)
    exact H.1.map_id_apply _ x.1.1
  map_comp g h := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext (Subtype.ext ?_)
    exact H.1.map_comp_apply g.unop.left.op h.unop.left.op x.1.1

variable {E : AlgebraicSpaces B S hS} {b₁ : E ⟶ H} {b₂ : E ⟶ Y}

/-- The morphism of presheaves to the fibre product `H ×_{H'} Y` attached to a point of `H`
carried to the section. -/
def spacePointsOverEqLift (sq : IsPullback b₁.hom b₂.hom Φ.hom s.hom) (T : SchemesOver Y)
    (x : SpacePointsOverEqObj Φ s p T) : yoneda.obj T.left ⟶ E.1 :=
  sq.lift (yonedaEquiv.symm x.1.1) T.hom.hom (yonedaEquiv.injective (by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact x.2.trans (yonedaEquiv_comp T.hom.hom s.hom).symm))

/-- The lift of a point carried to the section, followed by the projection to `H`, is that
point. -/
@[reassoc (attr := simp)]
theorem spacePointsOverEqLift_fst (sq : IsPullback b₁.hom b₂.hom Φ.hom s.hom)
    (T : SchemesOver Y) (x : SpacePointsOverEqObj Φ s p T) :
    spacePointsOverEqLift Φ s sq T x ≫ b₁.hom = yonedaEquiv.symm x.1.1 :=
  sq.lift_fst _ _ _

/-- The lift of a point carried to the section, followed by the projection to `Y`, is the
structure morphism of the test scheme. -/
@[reassoc (attr := simp)]
theorem spacePointsOverEqLift_snd (sq : IsPullback b₁.hom b₂.hom Φ.hom s.hom)
    (T : SchemesOver Y) (x : SpacePointsOverEqObj Φ s p T) :
    spacePointsOverEqLift Φ s sq T x ≫ b₂.hom = T.hom.hom :=
  sq.lift_snd _ _ _

variable {Φ s}

/-- The second coordinate of a point over `Y` of `H ×_{H'} Y` is the section of `Y` that the
test scheme is. -/
theorem spacePointsOverEq_snd (hΦ : Φ ≫ p' = p) (hs : s ≫ p' = 𝟙 Y)
    (sq : IsPullback b₁.hom b₂.hom Φ.hom s.hom) (T : SchemesOver Y)
    (x : spacePointsOverObj (b₁ ≫ p) T) :
    b₂.hom.app (op T.left) x.1 = testPoint T := by
  have e₁ : b₂.hom.app (op T.left) x.1 =
      p'.hom.app _ (s.hom.app _ (b₂.hom.app (op T.left) x.1)) :=
    (congrArg (fun k => k.hom.app (op T.left) (b₂.hom.app (op T.left) x.1)) hs).symm
  have e₂ : s.hom.app _ (b₂.hom.app (op T.left) x.1) = Φ.hom.app _ (b₁.hom.app (op T.left) x.1) :=
    (congrArg (fun k => k.app (op T.left) x.1) sq.w).symm
  have e₃ : p'.hom.app _ (Φ.hom.app _ (b₁.hom.app (op T.left) x.1)) =
      p.hom.app _ (b₁.hom.app (op T.left) x.1) :=
    congrArg (fun k => k.hom.app (op T.left) (b₁.hom.app (op T.left) x.1)) hΦ
  rw [e₁, e₂, e₃]
  exact x.2

/-- **The points over `Y` of the fibre product `H ×_{H'} Y` along `Φ : H ⟶ H'` and a section
`s : Y ⟶ H'` are the points of `H` over `Y` carried by `Φ` to the section.** -/
def spacePointsOverEqIso (hΦ : Φ ≫ p' = p) (hs : s ≫ p' = 𝟙 Y)
    (sq : IsPullback b₁.hom b₂.hom Φ.hom s.hom) :
    spacePointsOver (b₁ ≫ p) ≅ spacePointsOverEq Φ s p :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun (x : spacePointsOverObj (b₁ ≫ p) T.unop) =>
          ⟨⟨b₁.hom.app (op T.unop.left) x.1, x.2⟩, by
            refine ((congrArg (fun k => k.app (op T.unop.left) x.1) sq.w).trans ?_)
            exact congrArg (s.hom.app _) (spacePointsOverEq_snd hΦ hs sq T.unop x)⟩
        invFun := fun (y : SpacePointsOverEqObj Φ s p T.unop) =>
          ⟨yonedaEquiv (spacePointsOverEqLift Φ s sq T.unop y), by
            change (b₁.hom ≫ p.hom).app _ _ = _
            rw [← yonedaEquiv_comp, ← Category.assoc, spacePointsOverEqLift_fst,
              yonedaEquiv_comp, Equiv.apply_symm_apply]
            exact y.1.2⟩
        left_inv := fun (x : spacePointsOverObj (b₁ ≫ p) T.unop) => Subtype.ext (by
          change yonedaEquiv (spacePointsOverEqLift Φ s sq T.unop _) = x.1
          refine (congrArg yonedaEquiv (sq.hom_ext (l := yonedaEquiv.symm x.1) ?_ ?_)).trans
            (yonedaEquiv.apply_symm_apply x.1)
          · rw [spacePointsOverEqLift_fst, yonedaEquiv_symm_naturality_right]
          · rw [spacePointsOverEqLift_snd, yonedaEquiv_symm_naturality_right,
              spacePointsOverEq_snd hΦ hs sq T.unop x, yonedaEquiv_symm_testPoint])
        right_inv := fun (y : SpacePointsOverEqObj Φ s p T.unop) => Subtype.ext (Subtype.ext (by
          change b₁.hom.app _ (yonedaEquiv (spacePointsOverEqLift Φ s sq T.unop y)) = y.1.1
          rw [← yonedaEquiv_comp, spacePointsOverEqLift_fst, Equiv.apply_symm_apply])) })
    (fun {T T'} g => ConcreteCategory.hom_ext _ _
      fun (x : spacePointsOverObj (b₁ ≫ p) T.unop) =>
        Subtype.ext (Subtype.ext (NatTrans.naturality_apply b₁.hom g.unop.left.op x.1)))

/-- **The points of an algebraic space affine and of finite presentation over `Y` carried by a
morphism over `Y` to a section of another one form an algebraic space affine and of finite
presentation over `Y`.**  It is the fibre product `H ×_{H'} Y` along the section, whose
projection to `H` is a base change of the section, which is affine and of finite presentation
(`AlgebraicGeometry.Space.isAffineHom_and_isFinitePresentation_of_section`). -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_spacePointsOverEq
    (hp : IsAffineHom B S hS p.hom) (hfp : IsFinitePresentation B S hS p.hom)
    (hp' : IsAffineHom B S hS p'.hom) (hfp' : IsFinitePresentation B S hS p'.hom)
    (hΦ : Φ ≫ p' = p) (hs : s ≫ p' = 𝟙 Y) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y
      (spacePointsOverEq Φ s p ⋙ uliftFunctor.{u + 1, u}) := by
  obtain ⟨hsa, hsfp⟩ := isAffineHom_and_isFinitePresentation_of_section p' hp' hfp' s hs
  have sq' := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS Φ s)
  let E := AlgebraicSpaces.fiberProduct B S hS Φ s
  let b₁ : E ⟶ H := ObjectProperty.homMk (pullback.fst Φ.hom s.hom)
  exact ⟨E, b₁ ≫ p,
    isAffineHom_comp B S hS b₁.hom p.hom (IsAffineHom.of_isPullback sq'.flip hsa) hp,
    isFinitePresentation_comp B S hS E.2 H.2 Y.2 b₁.hom p.hom
      (IsFinitePresentation.of_isPullback B S hS E.2 Y.2 H.2 H'.2 sq'.flip hsfp) hfp,
    ⟨Functor.isoWhiskerRight (spacePointsOverEqIso hΦ hs sq') _⟩⟩

end Equation

/-! ### The points of a functor carried to a section -/

section SectionEqualizer

variable {C : Type*} [Category* C] (R₁ R₂ : C ⥤ Type w) (φ : R₁ ⟶ R₂) (σ : ∀ X, R₂.obj X)
  (hσ : ∀ {X X' : C} (f : X ⟶ X'), R₂.map f (σ X) = σ X')

/-- **The points of `R₁` carried by `φ : R₁ ⟶ R₂` to a section `σ` of `R₂`**, as a functor:
the fibre product `R₁ ×_{φ, R₂, σ} *`. -/
def sectionEqualizerFunctor : C ⥤ Type w where
  obj X := {x : R₁.obj X // φ.app X x = σ X}
  map {X X'} f := ↾fun x ↦ ⟨R₁.map f x.1, by rw [NatTrans.naturality_apply, x.2, hσ]⟩
  map_id X := ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext (R₁.map_id_apply (X := X) x.1)
  map_comp f g := ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext (R₁.map_comp_apply f g x.1)

/-- The points of `sectionEqualizerFunctor` at `X` are the points of `R₁` carried to `σ X`. -/
theorem sectionEqualizerFunctor_obj (X : C) :
    (sectionEqualizerFunctor R₁ R₂ φ σ hσ).obj X = {x : R₁.obj X // φ.app X x = σ X} :=
  rfl

/-- `sectionEqualizerFunctor` acts on a point through `R₁`. -/
theorem sectionEqualizerFunctor_map_coe {X X' : C} (f : X ⟶ X')
    (x : (sectionEqualizerFunctor R₁ R₂ φ σ hσ).obj X) :
    ((sectionEqualizerFunctor R₁ R₂ φ σ hσ).map f x).1 = R₁.map f x.1 :=
  rfl

variable {R₁ R₂} {R₁' R₂' : C ⥤ Type w} {φ σ} {φ' : R₁' ⟶ R₂'} {σ' : ∀ X, R₂'.obj X}
  (hσ' : ∀ {X X' : C} (f : X ⟶ X'), R₂'.map f (σ' X) = σ' X')

/-- **The points carried to a section, transported along isomorphisms** of the two functors
compatible with the morphisms and the sections. -/
def sectionEqualizerFunctorIsoOfIso (e₁ : R₁ ≅ R₁') (e₂ : R₂ ≅ R₂')
    (hφ : ∀ X x, e₂.hom.app X (φ.app X x) = φ'.app X (e₁.hom.app X x))
    (he : ∀ X, e₂.hom.app X (σ X) = σ' X) :
    sectionEqualizerFunctor R₁ R₂ φ σ hσ ≅ sectionEqualizerFunctor R₁' R₂' φ' σ' hσ' :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := fun x => ⟨e₁.hom.app X x.1, by rw [← hφ, x.2, he]⟩
        invFun := fun y => ⟨e₁.inv.app X y.1, (e₂.app X).toEquiv.injective ((hφ X _).trans
          (((congrArg (φ'.app X) ((e₁.app X).inv_hom_id_apply y.1)).trans y.2).trans
            (he X).symm))⟩
        left_inv := fun x => Subtype.ext ((e₁.app X).hom_inv_id_apply x.1)
        right_inv := fun y => Subtype.ext ((e₁.app X).inv_hom_id_apply y.1) })
    (fun {X X'} f => ConcreteCategory.hom_ext _ _ fun x =>
      Subtype.ext (NatTrans.naturality_apply e₁.hom f x.1))

end SectionEqualizer

/-! ### The points carried to a section, read on the functors of points -/

section EquationPoints

variable {Y H H' : AlgebraicSpaces B S hS} {p : H ⟶ Y} {p' : H' ⟶ Y} (Φ : H ⟶ H') (s : Y ⟶ H')

/-- The point of `H'` over `Y` that a section `s : Y ⟶ H'` of `p'` takes at a test scheme. -/
def sectionPointSE (hs : s ≫ p' = 𝟙 Y) (T : SchemesOver Y) : spacePointsOverObj p' T :=
  ⟨s.hom.app (op T.left) (testPoint T),
    congrArg (fun k => k.hom.app (op T.left) (testPoint T)) hs⟩

/-- The points that a section takes are compatible with restriction. -/
theorem sectionPoint_naturality (hs : s ≫ p' = 𝟙 Y) {U T : SchemesOver Y} (g : U ⟶ T) :
    (spacePointsOver p').map g.op (sectionPointSE s hs T) = sectionPointSE s hs U :=
  Subtype.ext ((spacePointsOver_map_coe p' g _).trans (map_section_testPoint s g))

/-- **The points of `H` over `Y` carried by `Φ` to a section `s` are the points carried to the
section `sectionPointSE s` by any morphism of functors of points acting as `Φ`.** -/
def spacePointsOverEqIsoSectionEqualizer (hs : s ≫ p' = 𝟙 Y)
    (φ₀ : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ⟶
      spacePointsOver p' ⋙ uliftFunctor.{u + 1, u})
    (hφ₀ : ∀ (T : (SchemesOver Y)ᵒᵖ) (x : spacePointsOverObj p T.unop),
      (φ₀.app T ⟨x⟩).down.1 = Φ.hom.app (op T.unop.left) x.1) :
    spacePointsOverEq Φ s p ⋙ uliftFunctor.{u + 1, u} ≅
      sectionEqualizerFunctor _ _ φ₀ (fun T => ⟨sectionPointSE s hs T.unop⟩)
        (fun g => congrArg ULift.up (sectionPoint_naturality s hs g.unop)) :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun x => ⟨⟨x.down.1⟩,
          ULift.ext _ _ (Subtype.ext ((hφ₀ T x.down.1).trans x.down.2))⟩
        invFun := fun y => ⟨⟨y.1.down, (hφ₀ T y.1.down).symm.trans
          (congrArg (fun z => z.down.1) y.2)⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

end EquationPoints

/-- The morphism of functors of points over `Y` out of `Y` itself that a section of a functor
of points over `Y` is. -/
def sectionPointsOverHom {Y H : AlgebraicSpaces B S hS} {p : H ⟶ Y}
    (σ : ∀ T : (SchemesOver Y)ᵒᵖ, spacePointsOverObj p T.unop)
    (hσ : ∀ {T T' : (SchemesOver Y)ᵒᵖ} (g : T ⟶ T'), (spacePointsOver p).map g (σ T) = σ T') :
    spacePointsOver (𝟙 Y) ⟶ spacePointsOver p where
  app T := ↾fun _ => σ T
  naturality _ _ g := ConcreteCategory.hom_ext _ _ fun _ => (hσ g).symm

/-- **The points of an algebraic space affine and of finite presentation over `Y` carried by a
morphism to another one onto a section of it form an algebraic space affine and of finite
presentation over `Y`**: the fibre product `R₁ ×_{φ, R₂, σ} Y` (the second fibre-product step of
the proof of Stacks 08K9).  The morphism and the section come from morphisms of the representing
spaces over `Y` by the Yoneda lemma, and
`AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_spacePointsOverEq`
applies. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.sectionEqualizer {Y : AlgebraicSpaces B S hS}
    {R₁ R₂ : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}
    (h₁ : IsAffineFinitePresentationAlgebraicSpaceOver Y R₁)
    (h₂ : IsAffineFinitePresentationAlgebraicSpaceOver Y R₂) (φ : R₁ ⟶ R₂)
    (σ : ∀ T, R₂.obj T) (hσ : ∀ {T T' : (SchemesOver Y)ᵒᵖ} (g : T ⟶ T'), R₂.map g (σ T) = σ T') :
    IsAffineFinitePresentationAlgebraicSpaceOver Y (sectionEqualizerFunctor R₁ R₂ φ σ hσ) := by
  obtain ⟨H₁, p₁, hp₁, hfp₁, ⟨c₁⟩⟩ := h₁
  obtain ⟨H₂, p₂, hp₂, hfp₂, ⟨c₂⟩⟩ := h₂
  let φ₀ := c₁.hom ≫ φ ≫ c₂.inv
  let ψ := stripUlift φ₀
  let Φ := spacePointsOverInv ψ
  have hΦ : Φ ≫ p₂ = p₁ := spacePointsOverInv_comp ψ
  have hτ : ∀ {T T' : (SchemesOver Y)ᵒᵖ} (g : T ⟶ T'),
      (spacePointsOver p₂).map g (c₂.inv.app T (σ T)).down = (c₂.inv.app T' (σ T')).down :=
    fun {T T'} g => (congrArg ULift.down (NatTrans.naturality_apply c₂.inv g (σ T))).symm.trans
      (congrArg (fun z => (c₂.inv.app T' z).down) (hσ g))
  let α := sectionPointsOverHom (fun T => (c₂.inv.app T (σ T)).down) hτ
  let s := spacePointsOverInv α
  have hs : s ≫ p₂ = 𝟙 Y := spacePointsOverInv_comp α
  have hφ₀ : ∀ (T : (SchemesOver Y)ᵒᵖ) (x : spacePointsOverObj p₁ T.unop),
      (φ₀.app T ⟨x⟩).down.1 = Φ.hom.app (op T.unop.left) x.1 :=
    fun T x => (spacePointsOverInvApp_eq ψ x).symm
  have hsec : ∀ T : (SchemesOver Y)ᵒᵖ, sectionPointSE s hs T.unop = (c₂.inv.app T (σ T)).down :=
    fun T => Subtype.ext (spacePointsOverInvApp_eq α (T := T.unop) ⟨testPoint T.unop, rfl⟩)
  refine (isAffineFinitePresentationAlgebraicSpaceOver_spacePointsOverEq hp₁ hfp₁ hp₂ hfp₂
    hΦ hs).of_iso (spacePointsOverEqIsoSectionEqualizer Φ s hs φ₀ hφ₀ ≪≫
      sectionEqualizerFunctorIsoOfIso _ hσ c₁ c₂
        (fun T x => (c₂.app T).inv_hom_id_apply _) (fun T => ?_))
  rw [hsec T]
  exact (c₂.app T).inv_hom_id_apply _

end AlgebraicGeometry.Space

end

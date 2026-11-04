module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleDescentBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleFppfComparisonMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonSquare

/-!
# The commutative square of Stacks 0DH5

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`. Stacks 0DH5
asserts that the diagram of topoi
```
Sh((Spaces/U)_{fppf,total}) --h--> Sh(U_étale)
          | a_fppf                    | a
Sh((Spaces/X)_fppf)       --h₋₁--> Sh(X_étale)
```
commutes, where `a` is the augmentation of Section 0DE7, `a_fppf` the augmentation of the fppf
total site (Section 09X8), `h₋₁ = a_X` the comparison of Section 0DGE and `h` the comparison
morphism of `AlgebraicGeometry.Space.etaleFppfComparisonMorphism`. This file proves it, on direct
images and on inverse images of sheaves of sets.

## The proof

The direct image `a_* h_* G` is the limit of the cosimplicial sheaf
`k ↦ (V ↦ G(V ×_X U_k / U_k))`, and `a_{fppf,*} G` is the right Kan extension of `G` along
`V/U_n ↦ V/X`, whose sections over `V/X` are the limit of `G` over all objects of the fppf total
site over `V/X`. Among those the objects `V ×_X U_k / U_k`, with their projections to `V`, form
an initial cosimplicial family (`AlgebraicGeometry.Space.fppfBaseArrows_initial`): an object
`W/U_n` over `V/X` factors through `V ×_X U_n / U_n`, and every factorization through some
`V ×_X U_k / U_k` comes from that one by a transition. So the two limits agree, which is the
source's computation `(h₋₁,* a_{fppf,*} G)(V) = G(V ×_X U / U)`, written as a limit over the
simplicial degrees.

## Main definitions

* `AlgebraicGeometry.Space.fppfAugmentationTypesMorphism`: the augmentation `a_fppf` on sheaves
  of sets, for the fppf topology of `(Spaces/X)_fppf`.
* `AlgebraicGeometry.Space.fppfAugmentationCone`: the cone exhibiting `h₋₁,* a_{fppf,*} G` over
  the cosimplicial sheaf computing `a_* h_* G`.
* `AlgebraicGeometry.Space.fppfComparisonSquarePushforwardIso`: **Stacks 0DH5**, on direct
  images, `h₋₁,* a_{fppf,*} ≅ a_* h_*`.
* `AlgebraicGeometry.Space.fppfComparisonSquareInverseImageIso`: **Stacks 0DH5**, on inverse
  images, `h⁻¹ a⁻¹ ≅ a_fppf⁻¹ h₋₁⁻¹`.

## Main results

* `AlgebraicGeometry.Space.fppfBaseArrows_initial`: the objects `V ×_X U_k / U_k` are initial
  among the objects of the fppf total site over `V/X`.
* `AlgebraicGeometry.Space.fppfAugmentationConeIsLimit`: the cone is a limit cone.

## References

* [Stacks Project, Tag 0DH5](https://stacks.math.columbia.edu/tag/0DH5)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Section 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor (CoGrothendieck)
open Stacks.CategoryTheory.Hypercovering

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent

/-- The localization functor of the fppf total site, after the comparison of the two
presentations of that site, computes underlying morphisms of algebraic spaces. -/
theorem totalForget_map_toAssociatedTotal_left {X Y : Grothendieck (SimplicialOver.slices A.left)}
    (g : X ⟶ Y) :
    ((SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map
      ((SimplicialOver.toAssociatedTotal A.left A.hom).map g)).left = g.fiber.left := by
  have h := Functor.congr_hom (SimplicialOver.toAssociatedTotal_comp_totalForget A.left A.hom) g
  have h' := congrArg Over.Hom.left h
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
    augmentationFunctor_map_left] at h'
  exact h'.trans ((Category.id_comp _).trans (Category.comp_id _))

/-- The comparison functor `u`, followed by the localization functor of the fppf total site,
computes the underlying morphism of algebraic spaces of a morphism of `U_étale`. -/
theorem totalForget_map_etaleToFppfTotal_left
    {X Y : CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor} (f : X ⟶ Y) :
    ((SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map
      ((etaleToFppfTotal A).map f)).left = etaleTotalHomLeft A f :=
  totalForget_map_toAssociatedTotal_left A ((etaleToSlicesTotal A).map f)

/-! ### The objects `V ×_X U_k / U_k` of the fppf total site -/

variable {A}

/-- The object `(k, V ×_X U_k)` of `U_étale` attached to an object `V` étale over `X`. -/
abbrev etaleBaseTotal (k : SimplexCategory) (V : SpacesEtale B S hS A.right) :
    (etaleSimplicialSite A).situation.totalCategory :=
  (SimplicialSiteSituation.componentFunctor (etaleSimplicialSite A).situation k).obj
    (EtaleComponent.baseObj k V)

/-- Its image `V ×_X U_k / U_k` in the fppf total site. -/
abbrev fppfBaseTotal (k : SimplexCategory) (V : SpacesEtale B S hS A.right) :
    (fppfTotalSituation A).totalCategory :=
  (etaleToFppfTotal A).obj (etaleBaseTotal k V)

/-- The projection `V ×_X U_k ⟶ V`, over `X`. -/
def fppfBaseProjection (k : SimplexCategory) (V : SpacesEtale B S hS A.right) :
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).obj (fppfBaseTotal k V) ⟶
      (SpacesEtale.inclusion B S hS A.right).obj V :=
  Over.homMk ((spacesBaseChange B S hS (A.hom.app (op k))).projection.app V)
    ((spacesBaseChange B S hS (A.hom.app (op k))).isPullback V).w

/-- A morphism of the fppf total site from an object `c`, over a simplex map `β`, into
`V ×_X U_k / U_k`, induced by a morphism `c ⟶ V` over `X`: the factorization through the fibre
product. -/
def fppfToBaseHom (c : (fppfTotalSituation A).totalCategory) {k : SimplexCategory}
    (β : c.base ⟶ op k) (V : SpacesEtale B S hS A.right)
    (f : (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).obj c ⟶
      (SpacesEtale.inclusion B S hS A.right).obj V) :
    c ⟶ fppfBaseTotal k V := by
  let pb := (spacesBaseChange B S hS (A.hom.app (op k))).isPullback V
  have hnat : A.left.map β ≫ A.hom.app (op k) = A.hom.app c.base :=
    (A.hom.naturality β).trans (Category.comp_id _)
  have hw : f.left ≫ V.obj.hom = (c.fiber.2.hom.left ≫ A.left.map β) ≫ A.hom.app (op k) :=
    (Over.w f).trans ((Over.w c.fiber.2.hom).symm.trans
      ((congrArg (fun t ↦ c.fiber.2.hom.left ≫ t) hnat.symm).trans (Category.assoc _ _ _).symm))
  let ℓ := pb.lift f.left (c.fiber.2.hom.left ≫ A.left.map β) hw
  refine ⟨β, CategoryTheory.Sigma.SigmaHom.mk (Over.homMk (Over.homMk ℓ ?_) ?_)⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ A.hom.app (op k))
      (pb.lift_snd _ _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (fun t ↦ c.fiber.2.hom.left ≫ t) hnat).trans (Over.w c.fiber.2.hom))))
  · exact Over.OverMorphism.ext (pb.lift_snd _ _ _)

attribute [local implicit_reducible] associatedSimplicialObject FormalCoproduct.incl

/-- The localization functor of the fppf total site on a morphism given by its fibre component:
the underlying morphism of algebraic spaces of the fibre component. -/
theorem totalForget_map_mk_left {b b' : SimplexCategoryᵒᵖ}
    {W : Over ((fppfHypercover A).obj b |>.obj PUnit.unit)}
    {W' : Over ((fppfHypercover A).obj b' |>.obj PUnit.unit)} (β : b ⟶ b')
    (α : (Over.map (((fppfHypercover A).map β).φ PUnit.unit)).obj W ⟶ W') :
    ((SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map
      (⟨β, CategoryTheory.Sigma.SigmaHom.mk α⟩ :
        (⟨b, ⟨PUnit.unit, W⟩⟩ : (fppfTotalSituation A).totalCategory) ⟶
          ⟨b', ⟨PUnit.unit, W'⟩⟩)).left =
      α.left.left := by
  simp only [SimplicialSemiRepresentable.totalForget, Grothendieck.functorFromOfEq, Over.comp_left]
  exact (congrArg (fun t ↦ Over.Hom.left t ≫ α.left.left)
    (eqToHom_app (SimplicialSemiRepresentable.totalForget_fib_eq (fppfHypercover A) β)
      ⟨PUnit.unit, W⟩)).trans (Category.id_comp _)

/-- The localization functor on a morphism into `V ×_X U_k / U_k` given by its fibre component,
followed by the projection to `V`, is the fibre component followed by the projection. -/
private theorem totalForget_map_mk_comp_projection_left {b : SimplexCategoryᵒᵖ}
    {k : SimplexCategory} {V : SpacesEtale B S hS A.right}
    {W : Over ((fppfHypercover A).obj b |>.obj PUnit.unit)} (β : b ⟶ op k)
    (α : (Over.map (((fppfHypercover A).map β).φ PUnit.unit)).obj W ⟶
      (fppfBaseTotal k V).fiber.2) :
    ((SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map
        (⟨β, CategoryTheory.Sigma.SigmaHom.mk α⟩ :
          (⟨b, ⟨PUnit.unit, W⟩⟩ : (fppfTotalSituation A).totalCategory) ⟶ fppfBaseTotal k V) ≫
      fppfBaseProjection k V).left = α.left.left ≫ (fppfBaseProjection k V).left :=
  congrArg (· ≫ (fppfBaseProjection k V).left) (totalForget_map_mk_left β α)

/-- The localization functor `fppfToBaseHom` against the projection is the given morphism. -/
theorem totalForget_map_fppfToBaseHom_comp (c : (fppfTotalSituation A).totalCategory)
    {k : SimplexCategory} (β : c.base ⟶ op k) (V : SpacesEtale B S hS A.right)
    (f : (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).obj c ⟶
      (SpacesEtale.inclusion B S hS A.right).obj V) :
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map (fppfToBaseHom c β V f) ≫
      fppfBaseProjection k V = f := by
  obtain ⟨b, ⟨⟨⟩, W⟩⟩ := c
  refine Over.OverMorphism.ext ?_
  exact (totalForget_map_mk_comp_projection_left β _).trans
    (((spacesBaseChange B S hS (A.hom.app (op k))).isPullback V).lift_fst _ _ _)

/-- **Morphisms into `V ×_X U_k / U_k` are determined by their simplex map and their composite
with the projection to `V`**: they are factorizations through a fibre product. -/
theorem fppfToBase_hom_ext {c : (fppfTotalSituation A).totalCategory} {k : SimplexCategory}
    {V : SpacesEtale B S hS A.right} (g g' : c ⟶ fppfBaseTotal k V) (hb : g.base = g'.base)
    (hl : (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map g ≫
        fppfBaseProjection k V =
      (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map g' ≫
        fppfBaseProjection k V) : g = g' := by
  obtain ⟨b, ⟨⟨⟩, W⟩⟩ := c
  obtain ⟨β, φ⟩ := g
  obtain ⟨β', φ'⟩ := g'
  dsimp only at hb
  subst hb
  obtain ⟨α⟩ := φ
  obtain ⟨α'⟩ := φ'
  have h₁ : α.left.left ≫ (fppfBaseProjection k V).left =
      α'.left.left ≫ (fppfBaseProjection k V).left :=
    (totalForget_map_mk_comp_projection_left β α).symm.trans
      ((congrArg Over.Hom.left hl).trans (totalForget_map_mk_comp_projection_left β α'))
  have h₂ : α.left.left = α'.left.left :=
    ((spacesBaseChange B S hS (A.hom.app (op k))).isPullback V).hom_ext h₁
      ((congrArg Over.Hom.left (Over.w α)).trans (congrArg Over.Hom.left (Over.w α')).symm)
  have : α = α' := Over.OverMorphism.ext (Over.OverMorphism.ext h₂)
  subst this
  rfl

/-- The image of the Cartesian arrow `(m, V ×_X U_m) ⟶ (k, V ×_X U_k)` of `U_étale` over a simplex
map `ψ : [k] ⟶ [m]` is compatible with the projections to `V`. -/
theorem totalForget_map_cart_comp_projection {k m : SimplexCategory} (ψ : k ⟶ m)
    (V : SpacesEtale B S hS A.right) :
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map ((etaleToFppfTotal A).map
        ((SimplicialSiteSituation.continuousInclusionTransition (etaleSimplicialSite A) ψ).app
          (EtaleComponent.baseObj k V))) ≫ fppfBaseProjection k V = fppfBaseProjection m V :=
  Over.OverMorphism.ext ((congrArg (· ≫ (fppfBaseProjection k V).left)
    (totalForget_map_etaleToFppfTotal_left A _)).trans
      ((congrArg (· ≫ (fppfBaseProjection k V).left) (Category.id_comp _)).trans
        (comparison_inl_fst ψ V)))

/-- The image of a morphism `(k, V' ×_X U_k) ⟶ (k, V ×_X U_k)` of degree `k` of `U_étale` lying
over a morphism `f : V' ⟶ V` is compatible with the projections. -/
theorem totalForget_map_ι_comp_projection {k : SimplexCategory}
    {V V' : SpacesEtale B S hS A.right} (f : V' ⟶ V)
    (g : (EtaleComponent.baseObj k V' : EtaleComponent A k) ⟶ EtaleComponent.baseObj k V)
    (hg : g.hom.hom.left ≫ (spacesBaseChange B S hS (A.hom.app (op k))).projection.app V =
      (spacesBaseChange B S hS (A.hom.app (op k))).projection.app V' ≫ f.hom.left) :
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map ((etaleToFppfTotal A).map
        ((SimplicialSiteSituation.componentFunctor (etaleSimplicialSite A).situation k).map g)) ≫
      fppfBaseProjection k V =
    fppfBaseProjection k V' ≫ (SpacesEtale.inclusion B S hS A.right).map f :=
  Over.OverMorphism.ext ((congrArg (· ≫ (fppfBaseProjection k V).left)
    ((totalForget_map_etaleToFppfTotal_left A _).trans (etaleTotalHomLeft_ι_map A g))).trans hg)

/-- Restricting a section of a right Kan extension along two arrows into it and reading it on the
source, compatibly with an arrow of the source. -/
theorem ranObj_map_comp_counit {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (L : C ⥤ D) (F : Cᵒᵖ ⥤ H) [∀ G : Cᵒᵖ ⥤ H, L.op.HasRightKanExtension G]
    {c₁ c₂ : C} {Y₁ Y₂ : D} (p₁ : L.obj c₁ ⟶ Y₁) (p₂ : L.obj c₂ ⟶ Y₂) (g : Y₂ ⟶ Y₁)
    (m : c₂ ⟶ c₁) (h : L.map m ≫ p₁ = p₂ ≫ g) :
    (L.op.ran.obj F).map g.op ≫ (L.op.ran.obj F).map p₂.op ≫ (L.op.ranCounit.app F).app (op c₂) =
      ((L.op.ran.obj F).map p₁.op ≫ (L.op.ranCounit.app F).app (op c₁)) ≫ F.map m.op := by
  have hn : (L.op.ran.obj F).map (L.map m).op ≫ (L.op.ranCounit.app F).app (op c₂) =
      (L.op.ranCounit.app F).app (op c₁) ≫ F.map m.op :=
    (L.op.ranCounit.app F).naturality m.op
  rw [Category.assoc, ← hn, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, h]

/-! ### The augmentation of the fppf total site on sheaves of sets -/

variable (A)

/-- The localization functor `V/U_n ↦ V/X` from the fppf total site to `(Spaces/X)_fppf` is
continuous. -/
instance totalForget_isContinuous_fppfTopology :
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).IsContinuous
      (fppfTotalSituation A).totalTopology ((fppfTopology B S hS).over A.right) := by
  rw [← fppfPretopology_toGrothendieck B S hS]
  exact SimplicialSemiRepresentable.totalForget_isContinuous
    ((fppfPretopology B S hS).toGrothendieck.over A.right) (fppfHypercover A)

/-- The localization functor `V/U_n ↦ V/X` from the fppf total site to `(Spaces/X)_fppf` is
cocontinuous. -/
instance totalForget_isCocontinuous_fppfTopology :
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).IsCocontinuous
      (fppfTotalSituation A).totalTopology ((fppfTopology B S hS).over A.right) := by
  rw [← fppfPretopology_toGrothendieck B S hS]
  exact SimplicialSemiRepresentable.totalForget_isCocontinuous
    ((fppfPretopology B S hS).toGrothendieck.over A.right) (fppfHypercover A)

/-- **The augmentation `a_fppf : Sh((Spaces/U)_{fppf,total}) → Sh((Spaces/X)_fppf)`** of
Section 09X8, on sheaves of sets: the morphism of topoi of the localization functor
`V/U_n ↦ V/X`, which is continuous and cocontinuous. -/
def fppfAugmentationTypesMorphism :
    MorphismOfTopoi (Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1)))
      (Sheaf ((fppfTopology B S hS).over A.right) (Type (u + 1))) where
  pushforward :=
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).sheafPushforwardCocontinuous
      (Type (u + 1)) (fppfTotalSituation A).totalTopology ((fppfTopology B S hS).over A.right)
  inverseImage :=
    (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).sheafPushforwardContinuous
      (Type (u + 1)) (fppfTotalSituation A).totalTopology ((fppfTopology B S hS).over A.right)
  adj := (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).sheafAdjunctionCocontinuous
    (Type (u + 1)) (fppfTotalSituation A).totalTopology ((fppfTopology B S hS).over A.right)
  preservesFiniteLimits :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _
      (SimplicialSemiRepresentable.totalForget (fppfHypercover A)) (Type (u + 1))

/-! ### The square of Stacks 0DH5 on direct images -/

/-- The cosimplicial sheaf on `X_étale` whose limit is the direct image along `a` of a sheaf on
`U_étale`. -/
abbrev etaleAugmentationDiagram
    (F : Sheaf (etaleSimplicialSite A).situation.totalTopology (Type (u + 1))) :=
  SimplicialSiteSituation.Augmentation.pushforwardDiagram (etaleSimplicialSite A).situation
    (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
    (etaleAugmentation A) F

/-- The direct image of a sheaf on the fppf total site along `h₋₁ ∘ a_fppf`. -/
abbrev fppfAugmentationComposite (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1))) :=
  (fppfSpacesEtaleMorphism A.right).pushforward.obj
    ((fppfAugmentationTypesMorphism A).pushforward.obj G)

variable {A}

/-- The leg in simplicial degree `k` of the cone exhibiting `h₋₁,* a_{fppf,*} G` as `a_* h_* G`:
its section over `V` is the restriction along the projection `V ×_X U_k ⟶ V`, read on the
right Kan extension of `G` along `V/U_n ↦ V/X`. -/
def fppfAugmentationConeLeg (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1)))
    (k : SimplexCategory) :
    fppfAugmentationComposite A G ⟶
      (etaleAugmentationDiagram A ((etaleFppfComparisonMorphism A).pushforward.obj G)).obj k :=
  ⟨{ app := fun V ↦
        ((SimplicialSemiRepresentable.totalForget (fppfHypercover A)).op.ran.obj G.obj).map
            (fppfBaseProjection k V.unop).op ≫
          ((SimplicialSemiRepresentable.totalForget (fppfHypercover A)).op.ranCounit.app
            G.obj).app (op (fppfBaseTotal k V.unop))
     naturality := fun V₁ V₂ f ↦ by
        have hg := transition_map_augmentationFunctor (A := A)
          (SimplexCategory.const (SimplexCategory.mk 0) k 0) f.unop
        have key := totalForget_map_ι_comp_projection f.unop
          ((EtaleComponent.transition (SimplexCategory.const (SimplexCategory.mk 0) k 0)).map
            (EtaleComponent.augmentationFunctor.map f.unop))
          (by
            rw [hg]
            exact (spacesBaseChange B S hS (A.hom.app (op k))).projection.naturality f.unop)
        change ((SimplicialSemiRepresentable.totalForget (fppfHypercover A)).op.ran.obj G.obj).map
            ((SpacesEtale.inclusion B S hS A.right).map f.unop).op ≫ _ =
          _ ≫ G.obj.map ((etaleToFppfTotal A).map
            ((SimplicialSiteSituation.componentFunctor (etaleSimplicialSite A).situation k).map
              ((EtaleComponent.transition (SimplexCategory.const (SimplexCategory.mk 0) k 0)).map
                (EtaleComponent.augmentationFunctor.map f.unop)))).op
        exact ranObj_map_comp_counit _ _ _ _ _ _ key }⟩

variable (A) in
/-- **The transitions of the cosimplicial sheaf computing `a_*` on sections**: over `V`, the
transition along `φ : [m] ⟶ [n]` is restriction along the Cartesian arrow
`(n, V ×_X U_n) ⟶ (m, V ×_X U_m)` of `U_étale`. -/
theorem etaleAugmentationDiagram_map_hom_app
    (F : Sheaf (etaleSimplicialSite A).situation.totalTopology (Type (u + 1)))
    {m n : SimplexCategory} (φ : m ⟶ n) (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    ((etaleAugmentationDiagram A F).map φ).hom.app V =
      F.obj.map ((SimplicialSiteSituation.continuousInclusionTransition (etaleSimplicialSite A)
        φ).app (EtaleComponent.baseObj m V.unop)).op := by
  have hinv :=
    SimplicialSite.ContinuousAugmentation.transitionPushforwardIso_inv_app_hom_app_eq_eqToHom
      (etaleAugmentation A) φ
      ((SimplicialSiteSituation.restrict (etaleSimplicialSite A).situation n).obj F) V rfl
  have hhi := congrArg (fun t ↦ t.hom.app V)
    ((SimplicialSiteSituation.Augmentation.transitionPushforwardIso
      (etaleSimplicialSite A).situation _ _ (etaleAugmentation A) φ).hom_inv_id_app
        ((SimplicialSiteSituation.restrict (etaleSimplicialSite A).situation n).obj F))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hhi
  rw [hinv] at hhi
  have h₂ := (Category.comp_id _).symm.trans hhi
  refine Eq.trans ?_ ((congrArg (fun t ↦ F.obj.map
      ((SimplicialSiteSituation.continuousInclusionTransition
        (etaleSimplicialSite A) φ).app (EtaleComponent.baseObj m V.unop)).op ≫ t) h₂).trans
      (Category.comp_id _))
  rfl

variable (A) in
/-- The transitions of the cosimplicial sheaf computing `a_* h_* G`, on sections. -/
theorem etaleAugmentationDiagram_comparison_map_hom_app
    (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1))) {m n : SimplexCategory}
    (φ : m ⟶ n) (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    ((etaleAugmentationDiagram A ((etaleFppfComparisonMorphism A).pushforward.obj G)).map
        φ).hom.app V =
      ((etaleFppfComparisonMorphism A).pushforward.obj G).obj.map
        ((SimplicialSiteSituation.continuousInclusionTransition (etaleSimplicialSite A) φ).app
          (EtaleComponent.baseObj m V.unop)).op :=
  etaleAugmentationDiagram_map_hom_app A ((etaleFppfComparisonMorphism A).pushforward.obj G) φ V

/-- The legs of the cone are compatible with the transitions of the cosimplicial sheaf, on
sections. -/
theorem fppfAugmentationConeLeg_comp_app
    (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1))) {m n : SimplexCategory}
    (φ : m ⟶ n) (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    (fppfAugmentationConeLeg G m).hom.app V ≫
        ((etaleAugmentationDiagram A ((etaleFppfComparisonMorphism A).pushforward.obj G)).map
          φ).hom.app V =
      (fppfAugmentationConeLeg G n).hom.app V := by
  rw [etaleAugmentationDiagram_comparison_map_hom_app A G φ V]
  have key : (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map
      ((etaleToFppfTotal A).map
        ((SimplicialSiteSituation.continuousInclusionTransition (etaleSimplicialSite A) φ).app
          (EtaleComponent.baseObj m V.unop))) ≫ fppfBaseProjection m V.unop =
      fppfBaseProjection n V.unop ≫ 𝟙 _ :=
    (totalForget_map_cart_comp_projection φ V.unop).trans (Category.comp_id _).symm
  exact (ranObj_map_comp_counit _ _ _ _ _ _ key).symm.trans
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _))

/-- The legs of the cone are compatible with the transitions of the cosimplicial sheaf. -/
theorem fppfAugmentationConeLeg_comp
    (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1))) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    fppfAugmentationConeLeg G m ≫
        (etaleAugmentationDiagram A ((etaleFppfComparisonMorphism A).pushforward.obj G)).map φ =
      fppfAugmentationConeLeg G n := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  exact fppfAugmentationConeLeg_comp_app G φ V

/-- **The cone exhibiting `h₋₁,* a_{fppf,*} G` over the cosimplicial sheaf computing
`a_* h_* G`.** -/
def fppfAugmentationCone (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1))) :
    Cone (etaleAugmentationDiagram A ((etaleFppfComparisonMorphism A).pushforward.obj G)) where
  pt := fppfAugmentationComposite A G
  π :=
    { app := fun k ↦ fppfAugmentationConeLeg G k
      naturality := fun m n φ ↦ (Category.id_comp _).trans (fppfAugmentationConeLeg_comp G φ).symm }

/-- The objects `V ×_X U_k / U_k` of the fppf total site with their projections to `V`, as a
cosimplicial object of the category of objects of the fppf total site over `V/X`; the
transitions are the images of the Cartesian arrows of `U_étale`. -/
def fppfBaseArrows (V : SpacesEtale B S hS A.right) :
    SimplexCategory ⥤ StructuredArrow (op ((SpacesEtale.inclusion B S hS A.right).obj V))
      (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).op where
  obj k := StructuredArrow.mk (fppfBaseProjection k V).op
  map {k m} ψ := StructuredArrow.homMk ((etaleToFppfTotal A).map
      ((SimplicialSiteSituation.continuousInclusionTransition (etaleSimplicialSite A) ψ).app
        (EtaleComponent.baseObj k V))).op
      (congrArg Quiver.Hom.op (totalForget_map_cart_comp_projection ψ V))
  map_id k := by
    refine StructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (fppfToBase_hom_ext _ _ rfl ?_))
    exact (totalForget_map_cart_comp_projection (𝟙 k) V).trans
      ((congrArg (· ≫ fppfBaseProjection k V)
        (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)).symm
  map_comp {k m n} ψ ψ' := by
    refine StructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (fppfToBase_hom_ext _ _ rfl ?_))
    refine (totalForget_map_cart_comp_projection (ψ ≫ ψ') V).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ fppfBaseProjection k V)
      (CategoryTheory.Functor.map_comp _ _ _)).symm
    exact ((congrArg (fun t ↦ _ ≫ t) (totalForget_map_cart_comp_projection ψ V)).trans
      (totalForget_map_cart_comp_projection ψ' V)).symm.trans (Category.assoc _ _ _).symm

/-- The object of the comma category of `fppfBaseArrows V` attached to an object `c` of the fppf
total site over `V/X`, in the simplicial degree of `c`: the factorization of `c` through
`V ×_X U_n / U_n`. -/
abbrev fppfBaseArrowsFactor {V : SpacesEtale B S hS A.right}
    (j : StructuredArrow (op ((SpacesEtale.inclusion B S hS A.right).obj V))
      (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).op) :
    CostructuredArrow (fppfBaseArrows V) j :=
  CostructuredArrow.mk (Y := j.right.unop.base.unop)
    (StructuredArrow.homMk (fppfToBaseHom j.right.unop (𝟙 _) V j.hom.unop).op
      (congrArg Quiver.Hom.op (totalForget_map_fppfToBaseHom_comp j.right.unop (𝟙 _) V
        j.hom.unop)))

/-- Every object of the comma category of `fppfBaseArrows V` maps to the factorization through
the base change in the simplicial degree of the object. -/
theorem nonempty_hom_fppfBaseArrowsFactor {V : SpacesEtale B S hS A.right}
    {j : StructuredArrow (op ((SpacesEtale.inclusion B S hS A.right).obj V))
      (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).op}
    (Q : CostructuredArrow (fppfBaseArrows V) j) : Nonempty (Q ⟶ fppfBaseArrowsFactor j) := by
  have hw : (SimplicialSemiRepresentable.totalForget (fppfHypercover A)).map Q.hom.right.unop ≫
      fppfBaseProjection Q.left V = j.hom.unop :=
    congrArg Quiver.Hom.unop (StructuredArrow.w Q.hom)
  refine ⟨CostructuredArrow.homMk Q.hom.right.unop.base.unop ?_⟩
  refine StructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (fppfToBase_hom_ext _ _ ?_ ?_))
  · exact Category.id_comp _
  · refine ((congrArg (· ≫ fppfBaseProjection Q.left V)
      (CategoryTheory.Functor.map_comp _ _ _)).trans ?_).trans hw.symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun t ↦ _ ≫ t) (totalForget_map_cart_comp_projection _ V)).trans ?_
    exact totalForget_map_fppfToBaseHom_comp _ _ V _

/-- **The cosimplicial object `k ↦ V ×_X U_k / U_k` is initial among the objects of the fppf total
site over `V/X`**: an object `c` of degree `n` over `V/X` factors through `V ×_X U_n / U_n`, and
every factorization through some `V ×_X U_k / U_k` comes from that one by a transition. -/
instance fppfBaseArrows_initial (V : SpacesEtale B S hS A.right) :
    (fppfBaseArrows V).Initial where
  out j := by
    haveI : Nonempty (CostructuredArrow (fppfBaseArrows V) j) := ⟨fppfBaseArrowsFactor j⟩
    refine zigzag_isConnected fun Q₁ Q₂ ↦ ?_
    obtain ⟨f₁⟩ := nonempty_hom_fppfBaseArrowsFactor Q₁
    obtain ⟨f₂⟩ := nonempty_hom_fppfBaseArrowsFactor Q₂
    exact (Zigzag.of_hom f₁).trans (Zigzag.of_inv f₂)

/-- The cosimplicial set of sections over `V` of the cosimplicial sheaf computing `a_* h_* G` is
the restriction of `G` to the objects `V ×_X U_k / U_k`. -/
def fppfBaseArrowsDiagramIso (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1)))
    (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    fppfBaseArrows V.unop ⋙ StructuredArrow.proj _ _ ⋙ G.obj ≅
      (etaleAugmentationDiagram A ((etaleFppfComparisonMorphism A).pushforward.obj G) ⋙
        sheafToPresheaf _ _) ⋙ (evaluation _ _).obj V :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {m n} φ ↦
    (Category.comp_id _).trans
      ((etaleAugmentationDiagram_comparison_map_hom_app A G φ V).symm.trans
        (Category.id_comp _).symm)

/-- **The sections over `V` of `h₋₁,* a_{fppf,*} G` are those of `a_* h_* G`.** The sections of the
right Kan extension `a_{fppf,*} G` over `V/X` are the limit of `G` over the objects of the fppf
total site over `V/X`, and the objects `V ×_X U_k / U_k` are initial among them. -/
def fppfAugmentationConeIsLimitApp
    (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1)))
    (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    IsLimit (((evaluation _ _).obj V).mapCone
      ((sheafToPresheaf _ _).mapCone (fppfAugmentationCone G))) :=
  IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv (fppfBaseArrowsDiagramIso G V) _).symm
    ((Functor.Initial.isLimitWhiskerEquiv (fppfBaseArrows V.unop) _).symm
      ((SimplicialSemiRepresentable.totalForget
          (fppfHypercover A)).op.isPointwiseRightKanExtensionRanCounit
        G.obj (op ((SpacesEtale.inclusion B S hS A.right).obj V.unop)))))
    (Cones.ext (Iso.refl _) fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The cone exhibiting `h₋₁,* a_{fppf,*} G` as `a_* h_* G` is a limit cone. -/
def fppfAugmentationConeIsLimit (G : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1))) :
    IsLimit (fppfAugmentationCone G) :=
  isLimitOfReflects (sheafToPresheaf _ _)
    (evaluationJointlyReflectsLimits _ fun V ↦ fppfAugmentationConeIsLimitApp G V)

/-- The legs of the cone are natural in the sheaf on the fppf total site. -/
theorem fppfAugmentationConeLeg_naturality
    {G G' : Sheaf (fppfTotalSituation A).totalTopology (Type (u + 1))} (f : G ⟶ G')
    (k : SimplexCategory) :
    (fppfSpacesEtaleMorphism A.right).pushforward.map
        ((fppfAugmentationTypesMorphism A).pushforward.map f) ≫ fppfAugmentationConeLeg G' k =
      fppfAugmentationConeLeg G k ≫
        (SimplicialSiteSituation.Augmentation.componentPushforward
          (etaleSimplicialSite A).situation (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) k).map
          ((etaleFppfComparisonMorphism A).pushforward.map f) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))
  let L := SimplicialSemiRepresentable.totalForget (fppfHypercover A)
  have h₁ := (L.op.ran.map f.hom).naturality (fppfBaseProjection k V.unop).op
  have h₂ := NatTrans.congr_app (L.op.ranCounit.naturality f.hom) (op (fppfBaseTotal k V.unop))
  show (L.op.ran.map f.hom).app _ ≫ (L.op.ran.obj G'.obj).map (fppfBaseProjection k V.unop).op ≫
      (L.op.ranCounit.app G'.obj).app (op (fppfBaseTotal k V.unop)) =
    ((L.op.ran.obj G.obj).map (fppfBaseProjection k V.unop).op ≫
      (L.op.ranCounit.app G.obj).app (op (fppfBaseTotal k V.unop))) ≫
      f.hom.app (op (fppfBaseTotal k V.unop))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun t ↦ _ ≫ t)
      ((NatTrans.comp_app _ _ _).symm.trans (h₂.trans (NatTrans.comp_app _ _ _)))).trans
        (Category.assoc _ _ _).symm)))

variable (A) in
/-- **Stacks 0DH5, on direct images**: the square
```
Sh((Spaces/U)_{fppf,total}) --h--> Sh(U_étale)
          | a_fppf                    | a
Sh((Spaces/X)_fppf)       --h₋₁--> Sh(X_étale)
```
commutes, `h₋₁,* a_{fppf,*} ≅ a_* h_*`, on sheaves of sets. -/
def fppfComparisonSquarePushforwardIso :
    (fppfAugmentationTypesMorphism A).pushforward ⋙ (fppfSpacesEtaleMorphism A.right).pushforward ≅
      (etaleFppfComparisonMorphism A).pushforward ⋙ (etaleAugmentationMorphism A).pushforward :=
  NatIso.ofComponents
    (fun G ↦ (fppfAugmentationConeIsLimit G).conePointUniqueUpToIso (limit.isLimit _))
    fun {G G'} f ↦ limit.hom_ext fun k ↦ by
      have e₁ := (fppfAugmentationConeIsLimit G').conePointUniqueUpToIso_hom_comp
        (limit.isLimit _) k
      have e₂ := (fppfAugmentationConeIsLimit G).conePointUniqueUpToIso_hom_comp
        (limit.isLimit _) k
      have e₃ := SimplicialSiteSituation.Augmentation.pushforward_map_comp_projection
        (etaleSimplicialSite A).situation (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)
        ((etaleFppfComparisonMorphism A).pushforward.map f) k
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun t ↦ _ ≫ t) e₁).trans ?_
      refine (fppfAugmentationConeLeg_naturality f k).trans ?_
      refine (congrArg (· ≫ _) e₂.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (fun t ↦ _ ≫ t) e₃.symm).trans (Category.assoc _ _ _).symm

variable (A) in
/-- **Stacks 0DH5, on inverse images**: `h⁻¹ a⁻¹ ≅ a_fppf⁻¹ h₋₁⁻¹` on sheaves of sets, the
conjugate of `fppfComparisonSquarePushforwardIso`. -/
def fppfComparisonSquareInverseImageIso :
    (etaleAugmentationMorphism A).inverseImage ⋙ (etaleFppfComparisonMorphism A).inverseImage ≅
      (fppfSpacesEtaleMorphism A.right).inverseImage ⋙
        (fppfAugmentationTypesMorphism A).inverseImage :=
  (conjugateIsoEquiv
    ((fppfSpacesEtaleMorphism A.right).adj.comp (fppfAugmentationTypesMorphism A).adj)
    ((etaleAugmentationMorphism A).adj.comp (etaleFppfComparisonMorphism A).adj)).symm
      (fppfComparisonSquarePushforwardIso A)

end AlgebraicGeometry.Space

end

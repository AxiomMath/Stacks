module

public import Mathlib.Algebra.BigOperators.Fin
public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionGroupoidPointwisePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentationFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RelativeCechComplex
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionReindex
public import StacksFrontier.AlgebraicGeometry.Stacks.FibredComparisonTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Resolution

/-!
# The relative Čech nerve of the atlas of a classifying stack

Let `G` be a smooth group algebraic space over a scheme `S` of a big fppf site, let
`BG = [S/G]` be its classifying stack (`AlgebraicGeometry.Stack.classifyingAlgebraicStack`) and
let `π : S ⟶ BG` be its atlas (`AlgebraicGeometry.Stack.classifyingAtlas`). This file describes
the relative Čech nerve of `π` (`Stacks.RelativeCech.Tuple`) over the trivial torsors: it is the
nerve of the group `G`, for an arbitrary (not necessarily commutative) `G`.

## Main definitions

* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.atlasObj`: the unique object of the stack of `S`
  over a test object `T`.
* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.atlasHomEquiv`: the morphisms
  `π(T') ⟶ π(T)` of `BG` over `m : T' ⟶ T` are the `T'`-points of `G`.
* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.atlasAut`: the automorphism of the trivial
  torsor `π(T)` given by a `T`-point of `G`.
* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.canonicalTuple`: the tuple of the relative Čech
  nerve attached to `n` points of `G`.
* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.barMap`: the simplicial structure of the nerve of
  `G`.
* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.canonicalTupleReindexIso`: reindexing a canonical
  tuple gives the canonical tuple of the reindexed points.
* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.canonicalTuplePullback`: pullback of canonical
  tuples along a morphism of test objects.
* `AlgebraicGeometry.Stack.ClassifyingAtlasCech.isTerminalCanonicalTuple`: a canonical tuple over
  an object representing `n`-tuples of points of `G` is terminal among tuples over a fixed test
  object.

## Conventions

The automorphisms compose as `(atlasAut T g).hom ≫ (atlasAut T h).hom = (atlasAut T (h * g)).hom`
(`AlgebraicGeometry.Stack.ClassifyingAtlasCech.atlasAut_hom_comp`): this is the composition law of
the action groupoid, where the composite of `g` followed by `h` has group component `h * g`. The
canonical tuple of `g : Fin n → G(T)` has comparison isomorphisms `atlasAut T (h i)` where
`h = Fin.partialProd g`, so `h 0 = 1` and `h (i + 1) = h i * g i`; reindexing along
`φ : [m] ⟶ [n]` gives the points `(h (φ j))⁻¹ * h (φ (j + 1))`.

## Implementation notes

The atlas is the inclusion of the object points into the pointwise groupoid fibration of the
trivial action groupoid, followed by the stackification map and the model equivalence. The last
two together are fully faithful (`AlgebraicGeometry.Stack.fullyFaithfulPointwiseToQuotientStack`)
and strictly over the site, so every statement about morphisms between images of trivial torsors
is a statement about the pointwise groupoid fibration, where a morphism is determined by its base
morphism and its group component (`AlgebraicGeometry.Space.actionPointwiseMorphism_ext`), and the
group component of a composite is computed by
`AlgebraicGeometry.Space.actionPointwiseGroupElement_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc CategoryTheory.Grpd.forgetToCat CategoryTheory.Grpd.of
  CategoryTheory.Bicategory.InducedBicategory AlgebraicGeometry.Stack.fibredCategory

universe u w

namespace AlgebraicGeometry.Stack.ClassifyingAtlasCech

open Space.GroupAlgebraicSpace

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### Points of the final algebraic space -/

/-- The unique point of the final algebraic space over a test object `T`. -/
def basePoint (T : BigFppfOver C S hS) : (Space.terminalSpace C S hS).obj.obj (op T) :=
  (Over.mkIdTerminal : IsTerminal (Space.baseTerminal C S hS)).from T

/-- Every point of the final algebraic space is the base point. -/
theorem eq_basePoint {T : BigFppfOver C S hS} (x : (Space.terminalSpace C S hS).obj.obj (op T)) :
    x = basePoint T :=
  (Over.mkIdTerminal : IsTerminal (Space.baseTerminal C S hS)).hom_ext _ _

variable (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property)

/-! ### The pointwise groupoid fibration of the trivial action -/

/-- The pointwise groupoid fibration of the trivial action groupoid of `G`. -/
abbrev pointwise : BasedCategory (BigFppfOver C S hS) :=
  Space.actionPointwiseCategory (Space.terminalSpace C S hS).property G
    (𝟙_ (Over (Space.terminalSpace C S hS).obj)) (Space.terminalSpace C S hS).property

/-- The object of the pointwise groupoid fibration over `T` given by the base point. -/
def pointwiseObj (T : BigFppfOver C S hS) : (pointwise G).obj :=
  ⟨T, basePoint T⟩

/-- The group component of a morphism of the pointwise groupoid fibration, as a point of `G`
with values in the base of its source. -/
def groupPoint {A A' : (pointwise G).obj} (f : A ⟶ A') : G.SitePoint A.base :=
  Over.homMk (Space.actionPointwiseGroupElement (Space.terminalSpace C S hS).property G
      (𝟙_ (Over (Space.terminalSpace C S hS).obj)) (Space.terminalSpace C S hS).property f)
    ((Space.baseTerminal_yonedaIsTerminal C S hS).hom_ext _ _)

/-- The underlying morphism of presheaves of the group component of a morphism. -/
theorem groupPoint_left {A A' : (pointwise G).obj} (f : A ⟶ A') :
    (groupPoint G f).left = Space.actionPointwiseGroupElement (Space.terminalSpace C S hS).property
      G (𝟙_ (Over (Space.terminalSpace C S hS).obj)) (Space.terminalSpace C S hS).property f :=
  rfl

/-- A morphism of the pointwise groupoid fibration is determined by its base and its group
component. -/
theorem pointwise_hom_ext {A A' : (pointwise G).obj} (f g : A ⟶ A') (hb : f.base = g.base)
    (hg : groupPoint G f = groupPoint G g) : f = g :=
  Space.actionPointwiseMorphism_ext _ G _ _ f g hb (congrArg Over.Hom.left hg)

/-- **The group component of a composite** is the pullback of the group component of the second
factor times the group component of the first. -/
theorem groupPoint_comp {A A' A'' : (pointwise G).obj} (f : A ⟶ A') (g : A' ⟶ A'') :
    groupPoint G (f ≫ g) = SitePoint.pullback G f.base (groupPoint G g) * groupPoint G f := by
  ext1
  exact Space.actionPointwiseGroupElement_comp _ G _ _ f g

/-- The group component of an identity morphism is the unit. -/
theorem groupPoint_id (A : (pointwise G).obj) : groupPoint G (𝟙 A) = 1 := by
  ext1
  rw [groupPoint_left, Space.actionPointwiseGroupElement_id, ← Category.assoc]
  exact congrArg (· ≫ (η[G.obj.X]).left)
    ((Space.baseTerminal_yonedaIsTerminal C S hS).hom_ext _ (toBase A.base))

/-- The groupoid in presheaves underlying the trivial action groupoid, in the form in which the
pointwise groupoid fibration is built from it. -/
abbrev pointwiseGroupoid : Deformation.GroupoidInFunctors (BigFppfOver C S hS)ᵒᵖ :=
  (Space.groupoidOfAction ⟨(Space.terminalSpace C S hS).obj, (Space.terminalSpace C S hS).property⟩
    G.obj.X (𝟙_ (Over (Space.terminalSpace C S hS).obj)) G.property
    (Space.terminalSpace C S hS).property).groupoid.toGroupoidInFunctors

/-- The point of the arrow space `G ×_S S` of the trivial action groupoid given by a point of
`G`. -/
def arrowPoint {T : BigFppfOver C S hS} (g : G.SitePoint T) :
    (G.obj.X ⊗ 𝟙_ (Over (Space.terminalSpace C S hS).obj)).left.obj (op T) :=
  yonedaEquiv (lift g (toUnit _)).left

/-- **The morphism of the pointwise groupoid fibration over `m` with group component `g`.** -/
def pointwiseHom {T T' : BigFppfOver C S hS} (m : T' ⟶ T) (g : G.SitePoint T') :
    pointwiseObj G T' ⟶ pointwiseObj G T where
  base := m
  fiber := ((pointwiseGroupoid G).evaluationArrowEquiv (op T') (basePoint T')
    ((pointwiseGroupoid G).objects.map m.op (basePoint T))).symm
      ⟨arrowPoint G g, eq_basePoint _, (eq_basePoint _).trans (eq_basePoint _).symm⟩

/-- The base of `pointwiseHom m g` is `m`. -/
@[simp]
theorem pointwiseHom_base {T T' : BigFppfOver C S hS} (m : T' ⟶ T) (g : G.SitePoint T') :
    (pointwiseHom G m g).base = m :=
  rfl

/-- The arrow of the action groupoid underlying `pointwiseHom m g`. -/
theorem actionPointwiseArrow_pointwiseHom {T T' : BigFppfOver C S hS} (m : T' ⟶ T)
    (g : G.SitePoint T') :
    Space.actionPointwiseArrow (Space.terminalSpace C S hS).property G
      (𝟙_ (Over (Space.terminalSpace C S hS).obj)) (Space.terminalSpace C S hS).property
      (pointwiseHom G m g) = arrowPoint G g :=
  congrArg Subtype.val (Equiv.apply_symm_apply ((pointwiseGroupoid G).evaluationArrowEquiv
    (op T') (basePoint T') ((pointwiseGroupoid G).objects.map m.op (basePoint T)))
      ⟨arrowPoint G g, eq_basePoint _, (eq_basePoint _).trans (eq_basePoint _).symm⟩)

/-- The group component of `pointwiseHom m g` is `g`. -/
@[simp]
theorem groupPoint_pointwiseHom {T T' : BigFppfOver C S hS} (m : T' ⟶ T) (g : G.SitePoint T') :
    groupPoint G (pointwiseHom G m g) = g := by
  ext1
  rw [groupPoint_left]
  unfold Space.actionPointwiseGroupElement
  rw [actionPointwiseArrow_pointwiseHom, arrowPoint]
  exact (congrArg yonedaEquiv.symm (yonedaEquiv_comp _ _).symm).trans
    ((Equiv.symm_apply_apply _ _).trans (congrArg Over.Hom.left (lift_fst g (toUnit _))))

/-- Every morphism of the pointwise groupoid fibration between base points is `pointwiseHom` of
its base and its group component. -/
theorem pointwiseHom_groupPoint {T T' : BigFppfOver C S hS}
    (f : pointwiseObj G T' ⟶ pointwiseObj G T) : pointwiseHom G f.base (groupPoint G f) = f :=
  pointwise_hom_ext G _ _ rfl (groupPoint_pointwiseHom G _ _)

/-- Composition of the morphisms `pointwiseHom`. -/
theorem pointwiseHom_comp {T T' T'' : BigFppfOver C S hS} (m : T'' ⟶ T') (m' : T' ⟶ T)
    (g : G.SitePoint T'') (g' : G.SitePoint T') :
    pointwiseHom G m g ≫ pointwiseHom G m' g' =
      pointwiseHom G (m ≫ m') (SitePoint.pullback G m g' * g) := by
  refine pointwise_hom_ext G _ _ rfl ?_
  rw [groupPoint_comp, groupPoint_pointwiseHom, groupPoint_pointwiseHom, groupPoint_pointwiseHom,
    pointwiseHom_base]
  rfl

/-! ### The stack of the base and its objects -/

/-- **The object of the stack of `S` over a test object `T`**: the pair of `T` and its unique
point of the final algebraic space. -/
def atlasObj (T : BigFppfOver C S hS) :
    (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.obj :=
  ⟨T, Discrete.mk (basePoint T)⟩

/-- The object `atlasObj T` lies over `T`. -/
@[simp]
theorem atlasObj_base (T : BigFppfOver C S hS) : (atlasObj T).base = T :=
  rfl

/-- **The canonical morphism `atlasObj T' ⟶ atlasObj T` over `m : T' ⟶ T`.** -/
def atlasCanonical {T T' : BigFppfOver C S hS} (m : T' ⟶ T) :
    (atlasObj T' : (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.obj) ⟶
      atlasObj T :=
  ⟨m, Discrete.eqToHom ((eq_basePoint _).trans (eq_basePoint _).symm)⟩

/-- The canonical morphism over an identity is the identity. -/
@[simp]
theorem atlasCanonical_id (T : BigFppfOver C S hS) : atlasCanonical (𝟙 T) = 𝟙 (atlasObj T) :=
  fibredCategory_hom_ext _ _ rfl

/-- Canonical morphisms compose. -/
theorem atlasCanonical_comp {T T' T'' : BigFppfOver C S hS} (m : T'' ⟶ T') (m' : T' ⟶ T) :
    atlasCanonical m ≫ atlasCanonical m' = atlasCanonical (m ≫ m') :=
  fibredCategory_hom_ext _ _ rfl

/-- The inclusion of object points sends the canonical morphism over `m` to the morphism of the
pointwise groupoid fibration over `m` whose fibre component is an identification. -/
def pointwiseCanonical {T T' : BigFppfOver C S hS} (m : T' ⟶ T) :
    pointwiseObj G T' ⟶ pointwiseObj G T :=
  (pointwiseObjectInclusion (trivialActionGroupoid G)).map (atlasCanonical m)

/-- The arrow of the action groupoid underlying `pointwiseCanonical m` is the identity arrow of
the base point, whatever `m` is. -/
theorem actionPointwiseArrow_pointwiseCanonical {T T' : BigFppfOver C S hS} (m : T' ⟶ T) :
    Space.actionPointwiseArrow (Space.terminalSpace C S hS).property G
      (𝟙_ (Over (Space.terminalSpace C S hS).obj)) (Space.terminalSpace C S hS).property
      (pointwiseCanonical G m) = (pointwiseGroupoid G).identity (op T') (basePoint T') :=
  evaluationArrow_eqToHom_identity (pointwiseGroupoid G) (op T')
    ((eq_basePoint _).trans (eq_basePoint _).symm)

/-- The group component of a canonical morphism is the unit. -/
@[simp]
theorem groupPoint_pointwiseCanonical {T T' : BigFppfOver C S hS} (m : T' ⟶ T) :
    groupPoint G (pointwiseCanonical G m) = 1 := by
  have h : groupPoint G (pointwiseCanonical G m) = groupPoint G (pointwiseCanonical G (𝟙 T')) := by
    ext1
    rw [groupPoint_left, groupPoint_left]
    unfold Space.actionPointwiseGroupElement
    rw [actionPointwiseArrow_pointwiseCanonical, actionPointwiseArrow_pointwiseCanonical]
  rw [h, pointwiseCanonical, atlasCanonical_id]
  exact (congrArg (groupPoint G)
    ((pointwiseObjectInclusion (trivialActionGroupoid G)).map_id _)).trans (groupPoint_id G _)

/-- The canonical morphism over `m` is `pointwiseHom m 1`. -/
theorem pointwiseCanonical_eq {T T' : BigFppfOver C S hS} (m : T' ⟶ T) :
    pointwiseCanonical G m = pointwiseHom G m 1 :=
  pointwise_hom_ext G _ _ rfl
    ((groupPoint_pointwiseCanonical G m).trans (groupPoint_pointwiseHom G m 1).symm)

/-! ### The atlas of the classifying stack -/

variable (hG : Space.IsSmooth C S hS G.obj.X.hom)

/-- The functor underlying the atlas `S ⟶ BG` of the classifying stack. -/
abbrev atlasFunctor :
    (algebraicSpaceStack.{u, w} C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property).val.val.obj ⥤
      (classifyingAlgebraicStack.{u, w} G hG).val.val.obj :=
  CatFiberedInGroupoids.homFunctor (classifyingAtlas.{u, w} G hG).hom

/-- The structure functor of the classifying stack. -/
abbrev stackProj :
    (classifyingAlgebraicStack.{u, w} G hG).val.val.obj ⥤ BigFppfOver C S hS :=
  (classifyingAlgebraicStack.{u, w} G hG).val.val.p

/-- The stackification map followed by the model equivalence: a fully faithful functor from the
pointwise groupoid fibration of the trivial action groupoid to the classifying stack. -/
abbrev pointwiseToStack : (pointwise G).obj ⥤ (classifyingAlgebraicStack.{u, w} G hG).val.val.obj :=
  pointwiseToQuotientStack (trivialActionGroupoid G) ⋙
    (classifyingAlgebraicStackEquivalenceOver.{u, w} G hG).hom.functor

/-- `pointwiseToStack` is fully faithful. -/
def fullyFaithfulPointwiseToStack : (pointwiseToStack.{u, w} G hG).FullyFaithful :=
  (fullyFaithfulPointwiseToQuotientStack (trivialActionGroupoid G)).comp
    (classifyingAlgebraicStackEquivalenceOver.{u, w} G hG).toEquivalence.fullyFaithfulFunctor

/-- `pointwiseToStack` lies strictly over the site. -/
theorem pointwiseToStack_comp :
    pointwiseToStack.{u, w} G hG ⋙ stackProj.{u, w} G hG = (pointwise G).p :=
  (Functor.assoc _ _ _).trans
    ((congrArg (pointwiseToQuotientStack (trivialActionGroupoid G) ⋙ ·)
      (classifyingAlgebraicStackEquivalenceOver.{u, w} G hG).hom.w).trans
      (isFibredOneMorphism_pointwiseToQuotientStack (trivialActionGroupoid G)).comp_eq)

/-- The atlas is the inclusion of object points followed by `pointwiseToStack`. -/
theorem atlasFunctor_eq :
    atlasFunctor.{u, w} G hG =
      pointwiseObjectInclusion (trivialActionGroupoid G) ⋙ pointwiseToStack.{u, w} G hG :=
  rfl

/-- The image under the atlas of `atlasObj T`. -/
theorem atlasFunctor_obj (T : BigFppfOver C S hS) :
    (atlasFunctor.{u, w} G hG).obj (atlasObj T) = (pointwiseToStack.{u, w} G hG).obj
      (pointwiseObj G T) :=
  rfl

/-- **The object `atlasObj T` lies over `T` in the stack of `S`.** -/
theorem proj_atlasObj (T : BigFppfOver C S hS) :
    (algebraicSpaceStack.{u, w} C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property).val.val.p.obj (atlasObj T) = T :=
  rfl

/-- **The image of `atlasObj T` in the classifying stack lies over `T`.** -/
theorem stackProj_atlasFunctor_obj (T : BigFppfOver C S hS) :
    (stackProj.{u, w} G hG).obj ((atlasFunctor.{u, w} G hG).obj (atlasObj T)) = T :=
  Functor.congr_obj (pointwiseToStack_comp.{u, w} G hG) (pointwiseObj G T)

/-- A morphism between images of a functor strictly over the base lies over `f` if and only if
its preimage does. -/
theorem isHomLift_map_iff {𝒜 ℬ 𝒮 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒮]
    (F : 𝒜 ⥤ ℬ) {p : 𝒜 ⥤ 𝒮} {q : ℬ ⥤ 𝒮} (h : F ⋙ q = p) {R R' : 𝒮} (f : R ⟶ R') {a b : 𝒜}
    (φ : a ⟶ b) : q.IsHomLift f (F.map φ) ↔ p.IsHomLift f φ := by
  subst h
  exact (Functor.isHomLift_comp_iff F q f φ).symm

/-- A morphism of the pointwise groupoid fibration between base points lies over `m` if and only
if its base is `m`. -/
theorem pointwise_isHomLift_iff {T T' : BigFppfOver C S hS} (m : T' ⟶ T)
    (f : pointwiseObj G T' ⟶ pointwiseObj G T) : (pointwise G).p.IsHomLift m f ↔ f.base = m :=
  ⟨fun h => by
    have h' : (pointwise G).p.IsHomLift (show (pointwise G).p.obj (pointwiseObj G T') ⟶
        (pointwise G).p.obj (pointwiseObj G T) from m) f := h
    exact (IsHomLift.eq_of_isHomLift (p := (pointwise G).p) _ f).symm,
    fun h => by subst h; exact IsHomLift.map (p := (pointwise G).p) f⟩

/-- The images in the classifying stack of the morphisms `pointwiseHom m g`. -/
abbrev atlasHom {T T' : BigFppfOver C S hS} (m : T' ⟶ T) (g : G.SitePoint T') :
    (atlasFunctor.{u, w} G hG).obj (atlasObj T') ⟶ (atlasFunctor.{u, w} G hG).obj (atlasObj T) :=
  (pointwiseToStack.{u, w} G hG).map (pointwiseHom G m g)

/-- `atlasHom m g` lies over `m`. -/
instance isHomLift_atlasHom {T T' : BigFppfOver C S hS} (m : T' ⟶ T) (g : G.SitePoint T') :
    (stackProj.{u, w} G hG).IsHomLift m (atlasHom.{u, w} G hG m g) :=
  (isHomLift_map_iff _ (pointwiseToStack_comp.{u, w} G hG) m _).2
    ((pointwise_isHomLift_iff G m _).2 rfl)

/-- The group component of the preimage of `atlasHom m g` is `g`. -/
theorem groupPoint_preimage_atlasHom {T T' : BigFppfOver C S hS} (m : T' ⟶ T)
    (g : G.SitePoint T') :
    groupPoint G ((fullyFaithfulPointwiseToStack.{u, w} G hG).preimage
      (X := pointwiseObj G T') (Y := pointwiseObj G T) (atlasHom.{u, w} G hG m g)) = g := by
  change groupPoint G ((fullyFaithfulPointwiseToStack.{u, w} G hG).preimage
    ((pointwiseToStack.{u, w} G hG).map (pointwiseHom G m g))) = g
  rw [Functor.FullyFaithful.preimage_map, groupPoint_pointwiseHom]

/-- A morphism between trivial torsors over `m` is `atlasHom m` of the group component of its
preimage. -/
theorem atlasHom_groupPoint_preimage {T T' : BigFppfOver C S hS} (m : T' ⟶ T)
    (φ : (pointwiseToStack.{u, w} G hG).obj (pointwiseObj G T') ⟶
      (pointwiseToStack.{u, w} G hG).obj (pointwiseObj G T))
    (hφ : (stackProj.{u, w} G hG).IsHomLift m φ) :
    atlasHom.{u, w} G hG m
      (groupPoint G ((fullyFaithfulPointwiseToStack.{u, w} G hG).preimage φ)) = φ := by
  have hb : ((fullyFaithfulPointwiseToStack.{u, w} G hG).preimage φ).base = m := by
    refine (pointwise_isHomLift_iff G m _).1 ((isHomLift_map_iff _
      (pointwiseToStack_comp.{u, w} G hG) m _).1 ?_)
    rw [Functor.FullyFaithful.map_preimage]
    exact hφ
  change (pointwiseToStack.{u, w} G hG).map (pointwiseHom G m _) = φ
  conv_rhs => rw [← (fullyFaithfulPointwiseToStack.{u, w} G hG).map_preimage φ]
  congr 1
  conv_lhs => rw [← hb]
  exact pointwiseHom_groupPoint G _

/-- The point of `G` given by a morphism between trivial torsors: the group component of its
preimage in the pointwise groupoid fibration. -/
def atlasHomInv {T T' : BigFppfOver C S hS}
    (φ : (atlasFunctor.{u, w} G hG).obj (atlasObj T') ⟶
      (atlasFunctor.{u, w} G hG).obj (atlasObj T)) :
    G.SitePoint T' :=
  groupPoint G ((fullyFaithfulPointwiseToStack.{u, w} G hG).preimage
    (X := pointwiseObj G T') (Y := pointwiseObj G T) φ)

/-- `atlasHomInv` is a left inverse of `atlasHom m`. -/
theorem atlasHomInv_atlasHom {T T' : BigFppfOver C S hS} (m : T' ⟶ T) (g : G.SitePoint T') :
    atlasHomInv.{u, w} G hG (atlasHom.{u, w} G hG m g) = g :=
  groupPoint_preimage_atlasHom.{u, w} G hG m g

/-- `atlasHomInv` is a right inverse of `atlasHom m` on the morphisms lying over `m`. -/
theorem atlasHom_atlasHomInv {T T' : BigFppfOver C S hS} (m : T' ⟶ T)
    (φ : (atlasFunctor.{u, w} G hG).obj (atlasObj T') ⟶ (atlasFunctor.{u, w} G hG).obj (atlasObj T))
    (hφ : (stackProj.{u, w} G hG).IsHomLift m φ) :
    atlasHom.{u, w} G hG m (atlasHomInv.{u, w} G hG φ) = φ :=
  atlasHom_groupPoint_preimage.{u, w} G hG m φ hφ

/-- **The morphisms of the classifying stack between trivial torsors over `m : T' ⟶ T` are the
`T'`-points of `G`.** -/
def atlasHomEquiv {T T' : BigFppfOver C S hS} (m : T' ⟶ T) :
    G.SitePoint T' ≃ {φ : (atlasFunctor.{u, w} G hG).obj (atlasObj T') ⟶
      (atlasFunctor.{u, w} G hG).obj (atlasObj T) // (stackProj.{u, w} G hG).IsHomLift m φ} where
  toFun g := ⟨atlasHom.{u, w} G hG m g, isHomLift_atlasHom.{u, w} G hG m g⟩
  invFun φ := atlasHomInv.{u, w} G hG φ.1
  left_inv g := atlasHomInv_atlasHom.{u, w} G hG m g
  right_inv φ := Subtype.ext (atlasHom_atlasHomInv.{u, w} G hG m φ.1 φ.2)

/-- The value of `atlasHomEquiv m` at a point. -/
@[simp]
theorem atlasHomEquiv_apply {T T' : BigFppfOver C S hS} (m : T' ⟶ T) (g : G.SitePoint T') :
    (atlasHomEquiv.{u, w} G hG m g).1 = atlasHom.{u, w} G hG m g :=
  rfl

/-- **Composition of morphisms between trivial torsors**: the composite of the morphism over
`m` given by `g` with the morphism over `m'` given by `g'` is the morphism over `m ≫ m'` given by
the pullback of `g'` along `m` times `g`. -/
theorem atlasHom_comp {T T' T'' : BigFppfOver C S hS} (m : T'' ⟶ T') (m' : T' ⟶ T)
    (g : G.SitePoint T'') (g' : G.SitePoint T') :
    atlasHom.{u, w} G hG m g ≫ atlasHom.{u, w} G hG m' g' =
      atlasHom.{u, w} G hG (m ≫ m') (SitePoint.pullback G m g' * g) :=
  ((pointwiseToStack.{u, w} G hG).map_comp _ _).symm.trans
    (congrArg (pointwiseToStack.{u, w} G hG).map (pointwiseHom_comp G m m' g g'))

/-- `atlasHom_comp` with the composite base morphism named. -/
theorem atlasHom_comp' {T T' T'' : BigFppfOver C S hS} (m : T'' ⟶ T') (m' : T' ⟶ T)
    (m'' : T'' ⟶ T) (hm : m ≫ m' = m'') (g : G.SitePoint T'') (g' : G.SitePoint T') :
    atlasHom.{u, w} G hG m g ≫ atlasHom.{u, w} G hG m' g' =
      atlasHom.{u, w} G hG m'' (SitePoint.pullback G m g' * g) := by
  subst hm
  exact atlasHom_comp.{u, w} G hG m m' g g'

/-- **The image of the canonical morphism over `m` is the morphism given by the unit.** -/
theorem atlasFunctor_map_atlasCanonical {T T' : BigFppfOver C S hS} (m : T' ⟶ T) :
    (atlasFunctor.{u, w} G hG).map (atlasCanonical m) = atlasHom.{u, w} G hG m 1 := by
  change (pointwiseToStack.{u, w} G hG).map (pointwiseCanonical G m) = _
  exact congrArg (pointwiseToStack.{u, w} G hG).map (pointwiseCanonical_eq G m)

/-- Over an identity, the morphism given by the unit is the identity. -/
@[simp]
theorem atlasHom_id_one (T : BigFppfOver C S hS) :
    atlasHom.{u, w} G hG (𝟙 T) 1 = 𝟙 _ :=
  (atlasFunctor_map_atlasCanonical.{u, w} G hG (𝟙 T)).symm.trans
    ((congrArg (atlasFunctor.{u, w} G hG).map (atlasCanonical_id T)).trans
      ((atlasFunctor.{u, w} G hG).map_id _))

/-! ### Automorphisms of the trivial torsors -/

/-- **The automorphism of the trivial torsor over `T` given by a `T`-point `g` of `G`.** -/
def atlasAut (T : BigFppfOver C S hS) (g : G.SitePoint T) :
    (atlasFunctor.{u, w} G hG).obj (atlasObj T) ≅ (atlasFunctor.{u, w} G hG).obj (atlasObj T) where
  hom := atlasHom.{u, w} G hG (𝟙 T) g
  inv := atlasHom.{u, w} G hG (𝟙 T) g⁻¹
  hom_inv_id := by
    rw [atlasHom_comp' _ _ _ _ (𝟙 T) (Category.comp_id _), SitePoint.pullback_id,
      inv_mul_cancel, atlasHom_id_one]
  inv_hom_id := by
    rw [atlasHom_comp' _ _ _ _ (𝟙 T) (Category.comp_id _), SitePoint.pullback_id,
      mul_inv_cancel, atlasHom_id_one]

/-- The forward morphism of `atlasAut T g`. -/
@[simp]
theorem atlasAut_hom (T : BigFppfOver C S hS) (g : G.SitePoint T) :
    (atlasAut.{u, w} G hG T g).hom = atlasHom.{u, w} G hG (𝟙 T) g :=
  rfl

/-- The inverse of `atlasAut T g` is `atlasAut T g⁻¹`. -/
theorem atlasAut_inv (T : BigFppfOver C S hS) (g : G.SitePoint T) :
    (atlasAut.{u, w} G hG T g).inv = (atlasAut.{u, w} G hG T g⁻¹).hom :=
  rfl

/-- `atlasAut T g` lies over the identity of `T`. -/
instance isHomLift_atlasAut (T : BigFppfOver C S hS) (g : G.SitePoint T) :
    (stackProj.{u, w} G hG).IsHomLift (𝟙 T) (atlasAut.{u, w} G hG T g).hom :=
  isHomLift_atlasHom.{u, w} G hG _ _

/-- **The automorphism given by the unit is the identity.** -/
@[simp]
theorem atlasAut_one (T : BigFppfOver C S hS) :
    atlasAut.{u, w} G hG T 1 = Iso.refl _ := by
  ext1
  exact atlasHom_id_one.{u, w} G hG T

/-- **Multiplicativity of the automorphisms**: `g` followed by `h` is `h * g`. -/
theorem atlasAut_hom_comp (T : BigFppfOver C S hS) (g h : G.SitePoint T) :
    (atlasAut.{u, w} G hG T g).hom ≫ (atlasAut.{u, w} G hG T h).hom =
      (atlasAut.{u, w} G hG T (h * g)).hom := by
  rw [atlasAut_hom, atlasAut_hom, atlasHom_comp' _ _ _ _ (𝟙 T) (Category.comp_id _),
    SitePoint.pullback_id, atlasAut_hom]

/-- **Every endomorphism of the trivial torsor over the identity of `T` is `atlasAut` of a unique
`T`-point.** -/
theorem existsUnique_atlasAut_hom (T : BigFppfOver C S hS)
    (φ : (atlasFunctor.{u, w} G hG).obj (atlasObj T) ⟶ (atlasFunctor.{u, w} G hG).obj (atlasObj T))
    (hφ : (stackProj.{u, w} G hG).IsHomLift (𝟙 T) φ) :
    ∃! g : G.SitePoint T, (atlasAut.{u, w} G hG T g).hom = φ := by
  refine ⟨atlasHomInv.{u, w} G hG φ, atlasHom_atlasHomInv.{u, w} G hG (𝟙 T) φ hφ,
    fun g hg => ?_⟩
  exact (atlasHomInv_atlasHom.{u, w} G hG (𝟙 T) g).symm.trans
    (congrArg (atlasHomInv.{u, w} G hG) hg)

/-- **Every automorphism of the trivial torsor over the identity of `T` is `atlasAut` of a unique
`T`-point.** -/
theorem existsUnique_atlasAut (T : BigFppfOver C S hS)
    (φ : (atlasFunctor.{u, w} G hG).obj (atlasObj T) ≅ (atlasFunctor.{u, w} G hG).obj (atlasObj T))
    (hφ : (stackProj.{u, w} G hG).IsHomLift (𝟙 T) φ.hom) :
    ∃! g : G.SitePoint T, atlasAut.{u, w} G hG T g = φ := by
  obtain ⟨g, hg, hu⟩ := existsUnique_atlasAut_hom.{u, w} G hG T φ.hom hφ
  exact ⟨g, Iso.ext hg, fun g' hg' => hu g' (congrArg Iso.hom hg')⟩

/-- **Naturality of the automorphisms**: transporting `atlasAut T g` along the canonical morphism
over `m : T' ⟶ T` gives `atlasAut T' (g pulled back along m)`. -/
theorem atlasFunctor_map_atlasCanonical_comp_atlasAut {T T' : BigFppfOver C S hS} (m : T' ⟶ T)
    (g : G.SitePoint T) :
    (atlasFunctor.{u, w} G hG).map (atlasCanonical m) ≫ (atlasAut.{u, w} G hG T g).hom =
      (atlasAut.{u, w} G hG T' (SitePoint.pullback G m g)).hom ≫
        (atlasFunctor.{u, w} G hG).map (atlasCanonical m) := by
  rw [atlasFunctor_map_atlasCanonical, atlasAut_hom, atlasAut_hom,
    atlasHom_comp' _ _ _ _ m (Category.comp_id m),
    atlasHom_comp' _ _ _ _ m (Category.id_comp m), map_one, one_mul, mul_one]

/-- Two morphisms `atlasHom` between the same objects are equal only if their base morphisms and
their points are. -/
theorem atlasHom_injective {T T' : BigFppfOver C S hS} {m m' : T' ⟶ T} {g g' : G.SitePoint T'}
    (h : atlasHom.{u, w} G hG m g = atlasHom.{u, w} G hG m' g') : m = m' ∧ g = g' := by
  have h' := (fullyFaithfulPointwiseToStack.{u, w} G hG).map_injective h
  refine ⟨congrArg Pseudofunctor.CoGrothendieck.Hom.base h', ?_⟩
  exact (groupPoint_pointwiseHom G m g).symm.trans
    ((congrArg (groupPoint G) h').trans (groupPoint_pointwiseHom G m' g'))

/-- Every morphism of the stack of `S` between two objects `atlasObj` is canonical. -/
theorem eq_atlasCanonical {T T' : BigFppfOver C S hS} (f : atlasObj T' ⟶ atlasObj T) :
    f = atlasCanonical f.base :=
  fibredCategory_hom_ext _ _ rfl

/-! ### The canonical tuples -/

/-- The tuples of the relative Čech nerve of the atlas of the classifying stack. -/
abbrev CechTuple (n : ℕ) : Type _ :=
  Stacks.RelativeCech.Tuple (stackProj.{u, w} G hG) (atlasFunctor.{u, w} G hG) n

/-- **The canonical tuple attached to `n` points of `G` over `T`**: all entries are `atlasObj T`,
the common target is the trivial torsor over `T`, and the `i`-th comparison isomorphism is the
automorphism given by the `i`-th partial product of the points. -/
abbrev canonicalTuple (T : BigFppfOver C S hS) {n : ℕ} (g : Fin n → G.SitePoint T) :
    CechTuple.{u, w} G hG n where
  target := (atlasFunctor.{u, w} G hG).obj (atlasObj T)
  source _ := atlasObj T
  comparison i := atlasAut.{u, w} G hG T (Fin.partialProd g i)
  comparison_lift _ := isHomLift_id_of_eq (stackProj_atlasFunctor_obj.{u, w} G hG T).symm _
    (isHomLift_atlasAut.{u, w} G hG T _)

/-- The common target of a canonical tuple. -/
@[simp]
theorem canonicalTuple_target (T : BigFppfOver C S hS) {n : ℕ} (g : Fin n → G.SitePoint T) :
    (canonicalTuple.{u, w} G hG T g).target = (atlasFunctor.{u, w} G hG).obj (atlasObj T) :=
  rfl

/-- The entries of a canonical tuple. -/
@[simp]
theorem canonicalTuple_source (T : BigFppfOver C S hS) {n : ℕ} (g : Fin n → G.SitePoint T)
    (i : Fin (n + 1)) : (canonicalTuple.{u, w} G hG T g).source i = atlasObj T :=
  rfl

/-- The comparison isomorphisms of a canonical tuple. -/
@[simp]
theorem canonicalTuple_comparison (T : BigFppfOver C S hS) {n : ℕ} (g : Fin n → G.SitePoint T)
    (i : Fin (n + 1)) :
    (canonicalTuple.{u, w} G hG T g).comparison i =
      atlasAut.{u, w} G hG T (Fin.partialProd g i) :=
  rfl

/-- The target component of a composite of morphisms of tuples. -/
@[simp]
theorem tupleComp_target {n : ℕ} {a b c : CechTuple.{u, w} G hG n} (f : a ⟶ b) (f' : b ⟶ c) :
    (f ≫ f').target = f.target ≫ f'.target :=
  rfl

/-- The entry components of a composite of morphisms of tuples. -/
@[simp]
theorem tupleComp_source {n : ℕ} {a b c : CechTuple.{u, w} G hG n} (f : a ⟶ b) (f' : b ⟶ c)
    (i : Fin (n + 1)) : (f ≫ f').source i = f.source i ≫ f'.source i :=
  rfl

/-- The target component of an identity morphism of tuples. -/
@[simp]
theorem tupleId_target {n : ℕ} (a : CechTuple.{u, w} G hG n) : (𝟙 a : a ⟶ a).target = 𝟙 _ :=
  rfl

/-- The entry components of an identity morphism of tuples. -/
@[simp]
theorem tupleId_source {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    (𝟙 a : a ⟶ a).source i = 𝟙 _ :=
  rfl

/-! ### The simplicial structure of the nerve of `G` -/

/-- **The simplicial structure of the nerve of `G`**: along `φ : [m] ⟶ [n]`, the `n` points `g`
go to the `m` points `(h (φ j))⁻¹ * h (φ (j + 1))`, where `h` are the partial products of `g`. -/
def barMap {T : BigFppfOver C S hS} {m n : ℕ} (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (g : Fin n → G.SitePoint T) : Fin m → G.SitePoint T :=
  fun j => (Fin.partialProd g (φ.toOrderHom j.castSucc))⁻¹ * Fin.partialProd g (φ.toOrderHom j.succ)

/-- The partial products of the points `barMap φ g`. -/
theorem partialProd_barMap {T : BigFppfOver C S hS} {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (g : Fin n → G.SitePoint T)
    (i : Fin (m + 1)) :
    Fin.partialProd (barMap G φ g) i =
      (Fin.partialProd g (φ.toOrderHom 0))⁻¹ * Fin.partialProd g (φ.toOrderHom i) := by
  induction i using Fin.induction with
  | zero => rw [Fin.partialProd_zero, inv_mul_cancel]
  | succ j ih => rw [Fin.partialProd_succ, ih, barMap, mul_assoc, mul_inv_cancel_left]

/-- A homomorphism of groups commutes with partial products. -/
theorem map_partialProd {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {n : ℕ} (g : Fin n → M)
    (i : Fin (n + 1)) : f (Fin.partialProd g i) = Fin.partialProd (fun j => f (g j)) i := by
  induction i using Fin.induction with
  | zero => rw [Fin.partialProd_zero, Fin.partialProd_zero, map_one]
  | succ j ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, map_mul, ih]

/-- **`barMap` is natural in the test object.** -/
theorem pullback_barMap {T T' : BigFppfOver C S hS} (k : T' ⟶ T) {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (g : Fin n → G.SitePoint T) (j : Fin m) :
    SitePoint.pullback G k (barMap G φ g j) =
      barMap G φ (fun i => SitePoint.pullback G k (g i)) j := by
  unfold barMap
  rw [map_mul, map_inv, map_partialProd, map_partialProd]

/-- `barMap` along the identity is the identity. -/
@[simp]
theorem barMap_id {T : BigFppfOver C S hS} {n : ℕ} (g : Fin n → G.SitePoint T) :
    barMap G (𝟙 (SimplexCategory.mk n)) g = g := by
  funext j
  exact Fin.partialProd_right_inv g j

/-- `barMap` is functorial. -/
theorem barMap_comp {T : BigFppfOver C S hS} {l m n : ℕ}
    (φ : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (g : Fin n → G.SitePoint T) :
    barMap G (φ ≫ ψ) g = barMap G φ (barMap G ψ g) := by
  funext j
  change _ = (Fin.partialProd (barMap G ψ g) (φ.toOrderHom j.castSucc))⁻¹ *
    Fin.partialProd (barMap G ψ g) (φ.toOrderHom j.succ)
  rw [partialProd_barMap, partialProd_barMap]
  simp only [barMap, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]

/-- **Reindexing a canonical tuple** along `φ : [m] ⟶ [n]` gives the canonical tuple of
`barMap φ g`; the isomorphism is `atlasAut T (h (φ 0))⁻¹` on targets, `h` being the partial
products of `g`, and the identity on entries. -/
def canonicalTupleReindexIso {T : BigFppfOver C S hS} {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (g : Fin n → G.SitePoint T) :
    (Stacks.RelativeCech.Tuple.reindex (stackProj.{u, w} G hG) (atlasFunctor.{u, w} G hG)
        φ.toOrderHom).obj (canonicalTuple.{u, w} G hG T g) ≅
      canonicalTuple.{u, w} G hG T (barMap G φ g) where
  hom :=
    { target := (atlasAut.{u, w} G hG T (Fin.partialProd g (φ.toOrderHom 0))⁻¹).hom
      source := fun _ => 𝟙 _
      comparison_naturality := fun i => by
        change _ ≫ (atlasAut.{u, w} G hG T (Fin.partialProd (barMap G φ g) i)).hom =
          (atlasAut.{u, w} G hG T (Fin.partialProd g (φ.toOrderHom i))).hom ≫ _
        exact (congrArg (· ≫ _) ((atlasFunctor.{u, w} G hG).map_id _)).trans
          ((Category.id_comp _).trans
            ((congrArg (fun x => (atlasAut.{u, w} G hG T x).hom)
              (partialProd_barMap G φ g i)).trans (atlasAut_hom_comp.{u, w} G hG T _ _).symm)) }
  inv :=
    { target := (atlasAut.{u, w} G hG T (Fin.partialProd g (φ.toOrderHom 0))).hom
      source := fun _ => 𝟙 _
      comparison_naturality := fun i => by
        change _ ≫ (atlasAut.{u, w} G hG T (Fin.partialProd g (φ.toOrderHom i))).hom =
          (atlasAut.{u, w} G hG T (Fin.partialProd (barMap G φ g) i)).hom ≫ _
        exact (congrArg (· ≫ _) ((atlasFunctor.{u, w} G hG).map_id _)).trans
          ((Category.id_comp _).trans
            ((congrArg (fun x => (atlasAut.{u, w} G hG T x).hom)
              ((congrArg (Fin.partialProd g (φ.toOrderHom 0) * ·)
                (partialProd_barMap G φ g i)).trans (mul_inv_cancel_left _ _))).symm.trans
              (atlasAut_hom_comp.{u, w} G hG T _ _).symm)) }
  hom_inv_id := by
    refine Stacks.RelativeCech.tuple_hom_ext _ _ ?_ (funext fun i => Category.comp_id _)
    exact (atlasAut_hom_comp.{u, w} G hG T _ _).trans
      ((congrArg (fun x => (atlasAut.{u, w} G hG T x).hom) (mul_inv_cancel _)).trans
        (congrArg Iso.hom (atlasAut_one.{u, w} G hG T)))
  inv_hom_id := by
    refine Stacks.RelativeCech.tuple_hom_ext _ _ ?_ (funext fun i => Category.comp_id _)
    exact (atlasAut_hom_comp.{u, w} G hG T _ _).trans
      ((congrArg (fun x => (atlasAut.{u, w} G hG T x).hom) (inv_mul_cancel _)).trans
        (congrArg Iso.hom (atlasAut_one.{u, w} G hG T)))

/-- The target component of `canonicalTupleReindexIso` lies over the identity of `T`. -/
instance isHomLift_canonicalTupleReindexIso_hom_target {T : BigFppfOver C S hS} {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (g : Fin n → G.SitePoint T) :
    (stackProj.{u, w} G hG).IsHomLift (𝟙 T)
      (canonicalTupleReindexIso.{u, w} G hG φ g).hom.target :=
  isHomLift_atlasAut.{u, w} G hG T (Fin.partialProd g (φ.toOrderHom 0))⁻¹

/-- The target component of the inverse of `canonicalTupleReindexIso` lies over the identity of
`T`. -/
instance isHomLift_canonicalTupleReindexIso_inv_target {T : BigFppfOver C S hS} {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (g : Fin n → G.SitePoint T) :
    (stackProj.{u, w} G hG).IsHomLift (𝟙 T)
      (canonicalTupleReindexIso.{u, w} G hG φ g).inv.target :=
  isHomLift_atlasAut.{u, w} G hG T (Fin.partialProd g (φ.toOrderHom 0))

/-! ### Pullback of canonical tuples -/

/-- **The morphism of canonical tuples over `k : T' ⟶ T`** from the tuple of points `g'` over
`T'` to the tuple of points `g` over `T`, when `g'` is the pullback of `g` along `k`: the
canonical morphisms over `k` in every component. -/
def canonicalTupleHom {T T' : BigFppfOver C S hS} (k : T' ⟶ T) {n : ℕ}
    (g : Fin n → G.SitePoint T) (g' : Fin n → G.SitePoint T')
    (hg : ∀ i, SitePoint.pullback G k (g i) = g' i) :
    canonicalTuple.{u, w} G hG T' g' ⟶ canonicalTuple.{u, w} G hG T g where
  target := (atlasFunctor.{u, w} G hG).map (atlasCanonical k)
  source _ := atlasCanonical k
  comparison_naturality i := by
    change _ ≫ (atlasAut.{u, w} G hG T (Fin.partialProd g i)).hom =
      (atlasAut.{u, w} G hG T' (Fin.partialProd g' i)).hom ≫ _
    exact (atlasFunctor_map_atlasCanonical_comp_atlasAut.{u, w} G hG k _).trans
      (congrArg (fun x => (atlasAut.{u, w} G hG T' x).hom ≫
          (atlasFunctor.{u, w} G hG).map (atlasCanonical k))
        ((map_partialProd (SitePoint.pullback G k) g i).trans
          (congrArg (fun g'' => Fin.partialProd g'' i) (funext hg))))

/-- The target component of `canonicalTupleHom`. -/
@[simp]
theorem canonicalTupleHom_target {T T' : BigFppfOver C S hS} (k : T' ⟶ T) {n : ℕ}
    (g : Fin n → G.SitePoint T) (g' : Fin n → G.SitePoint T')
    (hg : ∀ i, SitePoint.pullback G k (g i) = g' i) :
    (canonicalTupleHom.{u, w} G hG k g g' hg).target = atlasHom.{u, w} G hG k 1 :=
  atlasFunctor_map_atlasCanonical.{u, w} G hG k

/-- The target component of `canonicalTupleHom k` lies over `k`. -/
instance isHomLift_canonicalTupleHom_target {T T' : BigFppfOver C S hS} (k : T' ⟶ T) {n : ℕ}
    (g : Fin n → G.SitePoint T) (g' : Fin n → G.SitePoint T')
    (hg : ∀ i, SitePoint.pullback G k (g i) = g' i) :
    (stackProj.{u, w} G hG).IsHomLift k (canonicalTupleHom.{u, w} G hG k g g' hg).target :=
  (canonicalTupleHom_target.{u, w} G hG k g g' hg).symm ▸ isHomLift_atlasHom.{u, w} G hG k 1

/-- **Pullback of a canonical tuple along `k : T' ⟶ T`.** -/
abbrev canonicalTuplePullback {T T' : BigFppfOver C S hS} (k : T' ⟶ T) {n : ℕ}
    (g : Fin n → G.SitePoint T) :
    canonicalTuple.{u, w} G hG T' (fun i => SitePoint.pullback G k (g i)) ⟶
      canonicalTuple.{u, w} G hG T g :=
  canonicalTupleHom.{u, w} G hG k g _ fun _ => rfl

/-! ### Morphisms between canonical tuples -/

/-- The base morphism `T ⟶ T'` of a morphism from a canonical tuple over `T` to one over `T'`,
read through the identifications of the objects under the trivial torsors with `T` and `T'`. -/
def canonicalTupleHomBase {T T' : BigFppfOver C S hS} {n : ℕ} {g : Fin n → G.SitePoint T}
    {g' : Fin n → G.SitePoint T'}
    (ψ : canonicalTuple.{u, w} G hG T g ⟶ canonicalTuple.{u, w} G hG T' g') : T ⟶ T' :=
  eqToHom (stackProj_atlasFunctor_obj.{u, w} G hG T).symm ≫ (stackProj.{u, w} G hG).map ψ.target ≫
    eqToHom (stackProj_atlasFunctor_obj.{u, w} G hG T')

/-- The target component of a morphism of canonical tuples lies over its base morphism. -/
instance isHomLift_canonicalTupleHomBase {T T' : BigFppfOver C S hS} {n : ℕ}
    {g : Fin n → G.SitePoint T} {g' : Fin n → G.SitePoint T'}
    (ψ : canonicalTuple.{u, w} G hG T g ⟶ canonicalTuple.{u, w} G hG T' g') :
    (stackProj.{u, w} G hG).IsHomLift (canonicalTupleHomBase.{u, w} G hG ψ) ψ.target :=
  IsHomLift.of_fac _ _ _ (stackProj_atlasFunctor_obj.{u, w} G hG T)
    (stackProj_atlasFunctor_obj.{u, w} G hG T') rfl

/-- **A morphism of canonical tuples is canonical**: with `k` its base morphism, its target
component is the image of the canonical morphism over `k`, its entry components are the
canonical morphism over `k`, and the points of the source tuple are the pullbacks along `k` of
those of the target tuple. -/
theorem canonicalTupleHom_spec {T T' : BigFppfOver C S hS} {n : ℕ} {g : Fin n → G.SitePoint T}
    {g' : Fin n → G.SitePoint T'}
    (ψ : canonicalTuple.{u, w} G hG T g ⟶ canonicalTuple.{u, w} G hG T' g') :
    ψ.target = atlasHom.{u, w} G hG (canonicalTupleHomBase.{u, w} G hG ψ) 1 ∧
      (∀ i, ψ.source i = atlasCanonical (canonicalTupleHomBase.{u, w} G hG ψ)) ∧
      ∀ j, SitePoint.pullback G (canonicalTupleHomBase.{u, w} G hG ψ) (g' j) = g j := by
  set κ := canonicalTupleHomBase.{u, w} G hG ψ
  let e := atlasHomInv.{u, w} G hG ψ.target
  have he : ψ.target = atlasHom.{u, w} G hG κ e :=
    (atlasHom_atlasHomInv.{u, w} G hG κ ψ.target inferInstance).symm
  have key : ∀ i, (ψ.source i).base = κ ∧
      SitePoint.pullback G (ψ.source i).base (Fin.partialProd g' i) = e * Fin.partialProd g i := by
    intro i
    have hn := ψ.comparison_naturality i
    change (atlasFunctor.{u, w} G hG).map (ψ.source i) ≫
        (atlasAut.{u, w} G hG T' (Fin.partialProd g' i)).hom =
      (atlasAut.{u, w} G hG T (Fin.partialProd g i)).hom ≫ ψ.target at hn
    have h1 : (atlasFunctor.{u, w} G hG).map (ψ.source i) =
        atlasHom.{u, w} G hG (ψ.source i).base 1 :=
      (congrArg (atlasFunctor.{u, w} G hG).map (eq_atlasCanonical (ψ.source i))).trans
        (atlasFunctor_map_atlasCanonical.{u, w} G hG _)
    have h3 := (atlasHom_comp'.{u, w} G hG (ψ.source i).base (𝟙 T') _ (Category.comp_id _) 1
        (Fin.partialProd g' i)).symm.trans
      (((congrArg (· ≫ (atlasAut.{u, w} G hG T' (Fin.partialProd g' i)).hom) h1).symm.trans
        hn).trans ((congrArg ((atlasAut.{u, w} G hG T (Fin.partialProd g i)).hom ≫ ·) he).trans
          (atlasHom_comp'.{u, w} G hG (𝟙 T) κ _ (Category.id_comp _) (Fin.partialProd g i) e)))
    obtain ⟨hb, hgp⟩ := atlasHom_injective.{u, w} G hG h3
    exact ⟨hb, (mul_one _).symm.trans (hgp.trans (congrArg (· * _) (SitePoint.pullback_id G e)))⟩
  have he1 : e = 1 := by
    have := (key 0).2
    exact (mul_one e).symm.trans ((congrArg (e * ·) (Fin.partialProd_zero g).symm).trans
      (this.symm.trans ((congrArg (SitePoint.pullback G (ψ.source 0).base)
        (Fin.partialProd_zero g')).trans (map_one _))))
  have hk : ∀ i, SitePoint.pullback G κ (Fin.partialProd g' i) = Fin.partialProd g i := by
    intro i
    have := (key i).2
    exact ((congrArg (fun m => SitePoint.pullback G m (Fin.partialProd g' i)) (key i).1).symm.trans
      this).trans ((congrArg (· * _) he1).trans (one_mul _))
  refine ⟨he.trans (congrArg (atlasHom.{u, w} G hG κ) he1),
    fun i => (eq_atlasCanonical _).trans (congrArg atlasCanonical (key i).1), fun j => ?_⟩
  rw [← Fin.partialProd_right_inv g' j, map_mul, map_inv, hk, hk, Fin.partialProd_right_inv]

/-- A morphism of canonical tuples is determined by its base morphism. -/
theorem canonicalTupleHom_ext {T T' : BigFppfOver C S hS} {n : ℕ} {g : Fin n → G.SitePoint T}
    {g' : Fin n → G.SitePoint T'}
    (ψ ψ' : canonicalTuple.{u, w} G hG T g ⟶ canonicalTuple.{u, w} G hG T' g')
    (h : canonicalTupleHomBase.{u, w} G hG ψ = canonicalTupleHomBase.{u, w} G hG ψ') :
    ψ = ψ' :=
  Stacks.RelativeCech.tuple_hom_ext _ _
    (by rw [(canonicalTupleHom_spec.{u, w} G hG ψ).1, (canonicalTupleHom_spec.{u, w} G hG ψ').1, h])
    (funext fun i => by
      rw [(canonicalTupleHom_spec.{u, w} G hG ψ).2.1,
        (canonicalTupleHom_spec.{u, w} G hG ψ').2.1, h])

/-! ### Normalising an arbitrary tuple -/

/-- The morphism of the stack of `S` from `atlasObj T` to an object `x` over `T`. -/
def fromAtlasObj (x : (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.obj)
    {T : BigFppfOver C S hS} (h : x.base = T) : atlasObj T ⟶ x :=
  ⟨eqToHom h.symm, Discrete.eqToHom (by exact (eq_basePoint _).trans (eq_basePoint _).symm)⟩

/-- The morphism of the stack of `S` from an object `x` over `T` to `atlasObj T`. -/
def toAtlasObj (x : (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.obj)
    {T : BigFppfOver C S hS} (h : x.base = T) : x ⟶ atlasObj T :=
  ⟨eqToHom h, Discrete.eqToHom (by exact (eq_basePoint _).trans (eq_basePoint _).symm)⟩

/-- **An object of the stack of `S` over `T` is isomorphic to `atlasObj T`.** -/
def atlasObjIso (x : (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.obj)
    {T : BigFppfOver C S hS} (h : x.base = T) : atlasObj T ≅ x where
  hom := fromAtlasObj x h
  inv := toAtlasObj x h
  hom_inv_id := fibredCategory_hom_ext _ _ (by
    change eqToHom h.symm ≫ eqToHom h = 𝟙 T
    simp)
  inv_hom_id := fibredCategory_hom_ext _ _ (by
    change eqToHom h ≫ eqToHom h.symm = 𝟙 x.base
    simp)

/-- The morphism `fromAtlasObj x h` lies over the identity of `T`. -/
instance isHomLift_fromAtlasObj
    (x : (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.obj)
    {T : BigFppfOver C S hS} (h : x.base = T) :
    (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.p.IsHomLift (𝟙 T)
      (fromAtlasObj x h) :=
  IsHomLift.of_fac _ _ _ rfl h (by
    change 𝟙 T = eqToHom rfl ≫ eqToHom h.symm ≫ eqToHom h
    simp)

/-- An object of the stack of `S` and its image in the classifying stack lie over the same
object. -/
theorem stackProj_atlasFunctor_obj' (x : (fibredCategory C S hS
    (Space.terminalSpace C S hS).obj).val.obj) :
    (stackProj.{u, w} G hG).obj ((atlasFunctor.{u, w} G hG).obj x) = x.base :=
  Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (classifyingAtlas.{u, w} G hG).hom) x

variable {G hG}

/-- The object of the site a tuple lies over. -/
abbrev tupleBase {n : ℕ} (a : CechTuple.{u, w} G hG n) : BigFppfOver C S hS :=
  (stackProj.{u, w} G hG).obj a.target

/-- The entries of a tuple lie over the object the tuple lies over. -/
theorem source_base {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    (a.source i).base = tupleBase a := by
  have := a.comparison_lift i
  exact (stackProj_atlasFunctor_obj'.{u, w} G hG _).symm.trans
    (IsHomLift.domain_eq (stackProj.{u, w} G hG) (𝟙 (tupleBase a)) (a.comparison i).hom)

/-- The isomorphism from the trivial torsor over the base of a tuple to its target, through its
`i`-th entry. -/
def tupleIso {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    (atlasFunctor.{u, w} G hG).obj (atlasObj (tupleBase a)) ≅ a.target :=
  (atlasFunctor.{u, w} G hG).mapIso (atlasObjIso (a.source i) (source_base a i)) ≪≫ a.comparison i

/-- `tupleIso a i` lies over the identity. -/
instance isHomLift_tupleIso {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    (stackProj.{u, w} G hG).IsHomLift (𝟙 (tupleBase a)) (tupleIso a i).hom := by
  have h1 : (stackProj.{u, w} G hG).IsHomLift (𝟙 (tupleBase a))
      ((atlasFunctor.{u, w} G hG).map (fromAtlasObj (a.source i) (source_base a i))) :=
    (isHomLift_map_iff _ (CatFiberedInGroupoids.homFunctor_comp_p
      (classifyingAtlas.{u, w} G hG).hom) _ _).2 inferInstance
  have := a.comparison_lift i
  change (stackProj.{u, w} G hG).IsHomLift (𝟙 (tupleBase a))
    ((atlasFunctor.{u, w} G hG).map (fromAtlasObj (a.source i) (source_base a i)) ≫
      (a.comparison i).hom)
  infer_instance

/-- The automorphism of the trivial torsor over the base of a tuple comparing its `i`-th and its
`0`-th entries. -/
def tupleAut {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    (atlasFunctor.{u, w} G hG).obj (atlasObj (tupleBase a)) ≅
      (atlasFunctor.{u, w} G hG).obj (atlasObj (tupleBase a)) :=
  tupleIso a i ≪≫ (tupleIso a 0).symm

/-- `tupleAut a i` lies over the identity. -/
instance isHomLift_tupleAut {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    (stackProj.{u, w} G hG).IsHomLift (𝟙 (tupleBase a)) (tupleAut a i).hom := by
  change (stackProj.{u, w} G hG).IsHomLift (𝟙 (tupleBase a))
    ((tupleIso a i).hom ≫ (tupleIso a 0).inv)
  infer_instance

/-- The point of `G` given by `tupleAut a i`. -/
def tuplePoint {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    G.SitePoint (tupleBase a) :=
  (existsUnique_atlasAut.{u, w} G hG _ (tupleAut a i) inferInstance).exists.choose

/-- `tupleAut a i` is the automorphism given by `tuplePoint a i`. -/
theorem atlasAut_tuplePoint {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    atlasAut.{u, w} G hG _ (tuplePoint a i) = tupleAut a i :=
  (existsUnique_atlasAut.{u, w} G hG _ (tupleAut a i) inferInstance).exists.choose_spec

/-- The `0`-th point of a tuple is the unit. -/
theorem tuplePoint_zero {n : ℕ} (a : CechTuple.{u, w} G hG n) : tuplePoint a 0 = 1 :=
  (existsUnique_atlasAut.{u, w} G hG _ (tupleAut a 0) inferInstance).unique
    (atlasAut_tuplePoint a 0) (by rw [atlasAut_one]; exact (Iso.self_symm_id _).symm)

/-- **The `n` points of `G` read off a tuple**: the ratios of consecutive points
`tuplePoint a i`. -/
def tuplePoints {n : ℕ} (a : CechTuple.{u, w} G hG n) : Fin n → G.SitePoint (tupleBase a) :=
  fun j => (tuplePoint a j.castSucc)⁻¹ * tuplePoint a j.succ

/-- The partial products of the points read off a tuple are the points `tuplePoint a i`. -/
theorem partialProd_tuplePoints {n : ℕ} (a : CechTuple.{u, w} G hG n) (i : Fin (n + 1)) :
    Fin.partialProd (tuplePoints a) i = tuplePoint a i := by
  induction i using Fin.induction with
  | zero => rw [Fin.partialProd_zero, tuplePoint_zero]
  | succ j ih => rw [Fin.partialProd_succ, ih, tuplePoints, mul_inv_cancel_left]

/-- `toAtlasObj` followed by `fromAtlasObj` is the identity. -/
theorem toAtlasObj_fromAtlasObj
    (x : (fibredCategory C S hS (Space.terminalSpace C S hS).obj).val.obj)
    {T : BigFppfOver C S hS} (h : x.base = T) : toAtlasObj x h ≫ fromAtlasObj x h = 𝟙 x :=
  (atlasObjIso x h).inv_hom_id

/-- **Every tuple is isomorphic to the canonical tuple of the points read off it.** -/
def normalIso {n : ℕ} (a : CechTuple.{u, w} G hG n) :
    a ≅ canonicalTuple.{u, w} G hG (tupleBase a) (tuplePoints a) where
  hom :=
    { target := (tupleIso a 0).inv
      source := fun i => toAtlasObj (a.source i) (source_base a i)
      comparison_naturality := fun i => by
        change _ ≫ (atlasAut.{u, w} G hG _ (Fin.partialProd (tuplePoints a) i)).hom = _
        rw [partialProd_tuplePoints, atlasAut_tuplePoint]
        change _ ≫ ((atlasFunctor.{u, w} G hG).map (fromAtlasObj (a.source i) (source_base a i)) ≫
          (a.comparison i).hom) ≫ (tupleIso a 0).inv = _
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (tupleIso a 0).inv)
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (a.comparison i).hom)
            (((atlasFunctor.{u, w} G hG).map_comp _ _).symm.trans
              ((congrArg (atlasFunctor.{u, w} G hG).map (toAtlasObj_fromAtlasObj _ _)).trans
                ((atlasFunctor.{u, w} G hG).map_id _)))).trans (Category.id_comp _)))) }
  inv :=
    { target := (tupleIso a 0).hom
      source := fun i => fromAtlasObj (a.source i) (source_base a i)
      comparison_naturality := fun i => by
        change _ = (atlasAut.{u, w} G hG _ (Fin.partialProd (tuplePoints a) i)).hom ≫ _
        rw [partialProd_tuplePoints, atlasAut_tuplePoint]
        change _ = ((tupleIso a i).hom ≫ (tupleIso a 0).inv) ≫ (tupleIso a 0).hom
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl }
  hom_inv_id := Stacks.RelativeCech.tuple_hom_ext _ _ (Iso.inv_hom_id _)
    (funext fun i => toAtlasObj_fromAtlasObj _ _)
  inv_hom_id := Stacks.RelativeCech.tuple_hom_ext _ _ (Iso.hom_inv_id _)
    (funext fun i => (atlasObjIso _ _).hom_inv_id)

/-- The target component of the inverse of `normalIso a` lies over the identity. -/
instance isHomLift_normalIso_inv_target {n : ℕ} (a : CechTuple.{u, w} G hG n) :
    (stackProj.{u, w} G hG).IsHomLift (𝟙 (tupleBase a)) (normalIso a).inv.target :=
  isHomLift_tupleIso a 0

/-! ### Terminality -/

variable (G hG)

variable {T₀ Γ : BigFppfOver C S hS} (q : Γ ⟶ T₀) {n : ℕ} (pts : Fin n → G.SitePoint Γ)

/-- The functor from tuples to the site under which the terminality statement is made. -/
abbrev tupleProj (n : ℕ) : CechTuple.{u, w} G hG n ⥤ BigFppfOver C S hS :=
  Stacks.RelativeCech.Tuple.projection (stackProj.{u, w} G hG) (atlasFunctor.{u, w} G hG) n ⋙
    stackProj.{u, w} G hG

/-- **The candidate terminal object**: the canonical tuple of `pts` over `Γ`, mapping to `T₀`
through `q`. -/
abbrev terminalObj : CostructuredArrow (tupleProj.{u, w} G hG n) T₀ :=
  CostructuredArrow.mk (Y := canonicalTuple.{u, w} G hG Γ pts)
    (eqToHom (stackProj_atlasFunctor_obj.{u, w} G hG Γ) ≫ q)

/-- The universal property of `Γ`, `q`, `pts`: `Γ` represents `n`-tuples of points of `G` over
`T₀`. -/
abbrev IsUniversalPoints : Prop :=
  ∀ (T : BigFppfOver C S hS) (m : T ⟶ T₀) (g : Fin n → G.SitePoint T),
    ∃! k : T ⟶ Γ, k ≫ q = m ∧ ∀ i, SitePoint.pullback G k (pts i) = g i

variable {q pts}

/-- **The classifying morphism** `T ⟶ Γ` of points `g` over `T` and `m : T ⟶ T₀`. -/
def classifyingHom (hΓ : IsUniversalPoints G q pts) {T : BigFppfOver C S hS} (m : T ⟶ T₀)
    (g : Fin n → G.SitePoint T) : T ⟶ Γ :=
  (hΓ T m g).exists.choose

/-- The defining property of `classifyingHom`. -/
theorem classifyingHom_spec (hΓ : IsUniversalPoints G q pts) {T : BigFppfOver C S hS}
    (m : T ⟶ T₀) (g : Fin n → G.SitePoint T) :
    classifyingHom G hΓ m g ≫ q = m ∧
      ∀ i, SitePoint.pullback G (classifyingHom G hΓ m g) (pts i) = g i :=
  (hΓ T m g).exists.choose_spec

/-- `classifyingHom` is the unique morphism with its defining property. -/
theorem eq_classifyingHom (hΓ : IsUniversalPoints G q pts) {T : BigFppfOver C S hS}
    (m : T ⟶ T₀) (g : Fin n → G.SitePoint T) (k : T ⟶ Γ) (hk : k ≫ q = m)
    (hg : ∀ i, SitePoint.pullback G k (pts i) = g i) : k = classifyingHom G hΓ m g :=
  (hΓ T m g).unique ⟨hk, hg⟩ (classifyingHom_spec G hΓ m g)

/-- The base morphism of the morphism to the terminal object obtained by normalising. -/
theorem canonicalTupleHomBase_normalIso_inv_comp
    {X : CostructuredArrow (tupleProj.{u, w} G hG n) T₀}
    (f : X ⟶ terminalObj.{u, w} G hG q pts) :
    canonicalTupleHomBase.{u, w} G hG ((normalIso X.left).inv ≫ f.left) ≫ q = X.hom := by
  have hw := CostructuredArrow.w f
  change (stackProj.{u, w} G hG).map f.left.target ≫
    eqToHom (stackProj_atlasFunctor_obj.{u, w} G hG Γ) ≫ q = X.hom at hw
  have hfac := IsHomLift.fac' (stackProj.{u, w} G hG) (𝟙 (tupleBase X.left))
    (normalIso X.left).inv.target
  unfold canonicalTupleHomBase
  rw [tupleComp_target, CategoryTheory.Functor.map_comp, hfac]
  simp only [Category.assoc, eqToHom_trans_assoc, Category.id_comp, eqToHom_refl]
  exact hw

/-- **Two morphisms to the canonical tuple of universal points are equal.** -/
theorem terminalObj_hom_ext (hΓ : IsUniversalPoints G q pts)
    {X : CostructuredArrow (tupleProj.{u, w} G hG n) T₀}
    (f f' : X ⟶ terminalObj.{u, w} G hG q pts) : f = f' := by
  have key : ∀ f'' : X ⟶ terminalObj.{u, w} G hG q pts,
      canonicalTupleHomBase.{u, w} G hG ((normalIso X.left).inv ≫ f''.left) =
        classifyingHom G hΓ X.hom (tuplePoints X.left) := fun f'' =>
    eq_classifyingHom G hΓ _ _ _ (canonicalTupleHomBase_normalIso_inv_comp.{u, w} G hG f'')
      (canonicalTupleHom_spec.{u, w} G hG _).2.2
  have h : (normalIso X.left).inv ≫ f.left = (normalIso X.left).inv ≫ f'.left :=
    canonicalTupleHom_ext.{u, w} G hG _ _ ((key f).trans (key f').symm)
  refine CostructuredArrow.hom_ext f f' ?_
  rw [← Iso.hom_inv_id_assoc (normalIso X.left) f.left, h, Iso.hom_inv_id_assoc]

/-- The morphism of tuples underlying the morphism to the terminal object: normalise, then pull
back along the classifying morphism. -/
abbrev terminalFromLeft (hΓ : IsUniversalPoints G q pts)
    (X : CostructuredArrow (tupleProj.{u, w} G hG n) T₀) :
    X.left ⟶ canonicalTuple.{u, w} G hG Γ pts :=
  (normalIso X.left).hom ≫
    canonicalTupleHom.{u, w} G hG (classifyingHom G hΓ X.hom (tuplePoints X.left)) pts
      (tuplePoints X.left) (classifyingHom_spec G hΓ X.hom (tuplePoints X.left)).2

/-- `terminalFromLeft` lies over the structure morphisms to `T₀`. -/
theorem terminalFromLeft_w (hΓ : IsUniversalPoints G q pts)
    (X : CostructuredArrow (tupleProj.{u, w} G hG n) T₀) :
    (tupleProj.{u, w} G hG n).map (terminalFromLeft.{u, w} G hG hΓ X) ≫
      (terminalObj.{u, w} G hG q pts).hom = X.hom := by
  change (stackProj.{u, w} G hG).map ((tupleIso X.left 0).inv ≫
    (canonicalTupleHom.{u, w} G hG (classifyingHom G hΓ X.hom (tuplePoints X.left)) pts
      (tuplePoints X.left) (classifyingHom_spec G hΓ X.hom (tuplePoints X.left)).2).target) ≫
      eqToHom (stackProj_atlasFunctor_obj.{u, w} G hG Γ) ≫ q = X.hom
  have h1 := IsHomLift.fac' (stackProj.{u, w} G hG) (𝟙 (tupleBase X.left))
    (tupleIso X.left 0).inv
  have h2 := IsHomLift.fac' (stackProj.{u, w} G hG)
    (classifyingHom G hΓ X.hom (tuplePoints X.left))
    (atlasHom.{u, w} G hG (classifyingHom G hΓ X.hom (tuplePoints X.left)) 1)
  rw [canonicalTupleHom_target, CategoryTheory.Functor.map_comp, h1, h2]
  simp only [Category.assoc, eqToHom_trans_assoc, Category.id_comp, eqToHom_refl]
  exact (classifyingHom_spec G hΓ X.hom (tuplePoints X.left)).1

/-- The morphism to the terminal object: normalise, then pull back along the classifying
morphism. -/
def terminalFrom (hΓ : IsUniversalPoints G q pts)
    (X : CostructuredArrow (tupleProj.{u, w} G hG n) T₀) : X ⟶ terminalObj.{u, w} G hG q pts :=
  CostructuredArrow.homMk (terminalFromLeft.{u, w} G hG hΓ X) (terminalFromLeft_w.{u, w} G hG hΓ X)

/-- **Terminality.** If `q : Γ ⟶ T₀` and `pts : Fin n → G(Γ)` represent `n`-tuples of points of `G`
over `T₀`, then the canonical tuple of `pts`, mapping to `T₀` through `q`, is a terminal object of
the category of tuples of the relative Čech nerve of the atlas over `T₀`. -/
def isTerminalCanonicalTuple (hΓ : IsUniversalPoints G q pts) :
    IsTerminal (terminalObj.{u, w} G hG q pts) :=
  IsTerminal.ofUniqueHom (terminalFrom G hG hΓ) fun _ f =>
    terminalObj_hom_ext.{u, w} G hG hΓ f _

end AlgebraicGeometry.Stack.ClassifyingAtlasCech

end

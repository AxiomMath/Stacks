module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackHom
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveGeometricTwoArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.PresentedFibreArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonFullness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal injectivity of the map of classifying stacks

Let `φ : G₁ ⟶ G₂` be a homomorphism of smooth group algebraic spaces over a scheme `S` of a big
fppf site, and let `BG₁ ⟶ BG₂` be the induced 1-morphism of classifying stacks
`AlgebraicGeometry.Stack.classifyingMap`. This file proves that `BG₁ ⟶ BG₂` is universally
injective as soon as `φ` is surjective on points with values in algebraically closed fields. This
is the generic step of the counterexample to the first version of Stacks 0CPQ (with `G₁` the
constant group `ℤ/2`, `G₂` the affine line with doubled origin and `φ` the quotient map): there
`BG₁ ⟶ BG₂` is universally injective without its diagonal being separated.

## Main results

* `AlgebraicGeometry.Stack.exists_section_of_isAlgClosed`: a surjective morphism locally of
  finite presentation onto the spectrum of an algebraically closed field has a section.
* `AlgebraicGeometry.Stack.exists_presented_of_isAlgClosed`: every object of a quotient stack
  `[U/R]` over the spectrum of an algebraically closed field is presented by a point of `U`.
* `AlgebraicGeometry.Stack.exists_lift_quotientStackMap`: the 1-morphism of quotient stacks of
  Stacks 046Q lifts vertical arrows over a test object where every object is presented and the
  map of groupoids of points is full.
* `AlgebraicGeometry.Stack.full_evaluation_trivialActionGroupoidHom`: the map of groupoids of
  `V`-points of the trivial action groupoids is full when `φ` is surjective on `V`-points.
* `AlgebraicGeometry.Stack.liftsTwoArrowsAtGeometricPoints_classifyingMap`: condition (3) of
  Stacks 0CPN for `classifyingMap φ`.
* `AlgebraicGeometry.Stack.universallyInjective_classifyingMap`: `classifyingMap φ` is
  universally injective.

## Implementation notes

The proof is the implication (3) `⟹` (1) of Stacks 0CPN
(`AlgebraicGeometry.Stack.universallyInjective_of_liftsTwoArrowsAtGeometricPoints`). Condition
(3) is transported along the two model equivalences `BGᵢ ≃ [S/Gᵢ]`, which are fully faithful and
strictly over the site, so preimages of vertical arrows are vertical. On the quotient stacks, an
object over `V = Spec k` becomes presented by a point after pullback along an fppf morphism
`W ⟶ V` (Stacks 044X (1), in the form
`AlgebraicGeometry.Stack.exists_single_cover_presented_pair`); since `k` is algebraically closed,
`W` has a closed point with residue field `k` (Mathlib's `AlgebraicGeometry.pointOfClosedPoint`),
that is a section of `W ⟶ V`, and pulling back along it presents the object itself. A vertical
arrow between the images of two presented objects is then, after conjugation by the
2-isomorphism of Stacks 046Q, an arrow of the groupoid of `V`-points of the trivial action
groupoid of `G₂` (Stacks 044X (2), `AlgebraicGeometry.Stack.exists_evaluationArrow`), that is a
`V`-point of `G₂ ×_S S`. It lifts through `φ × id` by hypothesis, and the naturality of the
2-isomorphism of Stacks 046Q shows that the image of the lift is the given arrow.

A point of `G` with values in a site object `V` is recorded as a morphism
`yoneda.obj V ⟶ G.obj.X.left` of presheaves; every such morphism lies over the final algebraic
space, so no compatibility with the structure morphism needs to be stated.

## References

* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0CPQ](https://stacks.math.columbia.edu/tag/0CPQ)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open CategoryTheory.Pseudofunctor

universe u w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### Generic helpers -/

section Generic

variable {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳] {𝒴 : Type*} [Category* 𝒴]

/-- A morphism lies over `f` as soon as its image under a functor strictly over the base does. -/
private theorem isHomLift_of_isHomLift_map {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p)
    {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳} (φ : a ⟶ b) (h : q.IsHomLift f (F.map φ)) :
    p.IsHomLift f φ := by
  subst hF
  exact (Functor.isHomLift_comp_iff F q f φ).2 h

/-- **A fully faithful functor strictly over the base lifts vertical arrows to vertical arrows.**
The preimage of a vertical arrow is vertical, since its image under the structure functor of the
source is that of the arrow under the structure functor of the target. -/
private theorem exists_isHomLift_preimage {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p)
    (hff : F.FullyFaithful) {V : 𝒞} {x₁ x₂ : 𝒳} (β : F.obj x₁ ⟶ F.obj x₂)
    (hβ : q.IsHomLift (𝟙 V) β) : ∃ α : x₁ ⟶ x₂, p.IsHomLift (𝟙 V) α ∧ F.map α = β :=
  ⟨hff.preimage β, isHomLift_of_isHomLift_map hF _ _ (by rwa [hff.map_preimage]),
    hff.map_preimage β⟩

/-- Two vertical morphisms compose to a vertical morphism. -/
private theorem isHomLift_id_comp_id (p : 𝒳 ⥤ 𝒞) {U : 𝒞} {a b c : 𝒳} (g : a ⟶ b) (h : b ⟶ c)
    (hg : p.IsHomLift (𝟙 U) g) (hh : p.IsHomLift (𝟙 U) h) : p.IsHomLift (𝟙 U) (g ≫ h) := by
  have := hg
  have := hh
  simpa using (inferInstance : p.IsHomLift (𝟙 U ≫ 𝟙 U) (g ≫ h))

/-- A functor preserves a threefold composite. -/
private theorem map_comp₃ {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E) {a b c d : D}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) : F.map (x ≫ y ≫ z) = F.map x ≫ F.map y ≫ F.map z := by
  simp

/-- The cancellation underlying `AlgebraicGeometry.Stack.exists_lift_quotientStackMap`, over plain
variables: if `A ≫ c₂ = c₁ ≫ N` and `A = c₁ ≫ J₁ ≫ β ≫ J₂' ≫ c₂'`, with `c₁`, `c₂`, `J₁`, `J₂`
invertible with the indicated inverses, then `J₁' ≫ N ≫ J₂ = β`. -/
private theorem cancel_conj_aux {D : Type*} [Category* D] {Q₁ Q₂ N₁ N₂ Y₁ Y₂ : D}
    (c₁ : Q₁ ⟶ N₁) (c₁' : N₁ ⟶ Q₁) (c₂ : Q₂ ⟶ N₂) (c₂' : N₂ ⟶ Q₂)
    (J₁ : N₁ ⟶ Y₁) (J₁' : Y₁ ⟶ N₁) (J₂ : N₂ ⟶ Y₂) (J₂' : Y₂ ⟶ N₂)
    (A : Q₁ ⟶ Q₂) (N : N₁ ⟶ N₂) (β : Y₁ ⟶ Y₂)
    (hnat : A ≫ c₂ = c₁ ≫ N) (hA : A = c₁ ≫ J₁ ≫ β ≫ J₂' ≫ c₂')
    (hc₁ : c₁' ≫ c₁ = 𝟙 N₁) (hc₂ : c₂' ≫ c₂ = 𝟙 N₂)
    (hJ₁ : J₁' ≫ J₁ = 𝟙 Y₁) (hJ₂ : J₂' ≫ J₂ = 𝟙 Y₂) :
    J₁' ≫ N ≫ J₂ = β := by
  have hN : N = J₁ ≫ β ≫ J₂' := by
    calc N = (c₁' ≫ c₁) ≫ N := by rw [hc₁, Category.id_comp]
      _ = c₁' ≫ A ≫ c₂ := by rw [Category.assoc, ← hnat]
      _ = (c₁' ≫ c₁) ≫ J₁ ≫ β ≫ J₂' ≫ (c₂' ≫ c₂) := by
        rw [hA]
        simp only [Category.assoc]
      _ = J₁ ≫ β ≫ J₂' := by rw [hc₁, hc₂, Category.id_comp, Category.comp_id]
  rw [hN]
  calc J₁' ≫ (J₁ ≫ β ≫ J₂') ≫ J₂ = (J₁' ≫ J₁) ≫ β ≫ (J₂' ≫ J₂) := by
        simp only [Category.assoc]
    _ = β := by rw [hJ₁, hJ₂, Category.id_comp, Category.comp_id]

end Generic

/-! ### Objects of a quotient stack over an algebraically closed field are presented -/

section Presented

/-- **A surjective morphism locally of finite presentation onto the spectrum of an algebraically
closed field has a section.** For `V` with underlying scheme `Spec k`, `k` algebraically closed,
and `f : W ⟶ V` surjective and locally of finite presentation, `W` is nonempty and Jacobson, so it
has a closed point, whose residue field is `k` by the Nullstellensatz; that point is a section. -/
@[ega "IV 1.3.7" "special case"]
theorem exists_section_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    {V W : BigFppfOver C S hS} (e : (BigFppfOver.toScheme C S hS).obj V ≅ Spec (.of k))
    (f : W ⟶ V) (hlfp : LocallyOfFinitePresentation (C.inclusion.map f.left))
    (hsurj : Surjective (C.inclusion.map f.left)) :
    ∃ σ : V ⟶ W, σ ≫ f = 𝟙 V := by
  let g : C.inclusion.obj W.left ⟶ C.inclusion.obj V.left := C.inclusion.map f.left
  let h : C.inclusion.obj W.left ⟶ Spec (.of k) := g ≫ e.hom
  have : LocallyOfFiniteType h := inferInstance
  have : JacobsonSpace (C.inclusion.obj W.left) := LocallyOfFiniteType.jacobsonSpace h
  obtain ⟨w₀, -⟩ := hsurj.surj (e.inv (IsLocalRing.closedPoint k))
  obtain ⟨w, -, hw⟩ := nonempty_inter_closedPoints (X := C.inclusion.obj W.left)
    (Z := Set.univ) ⟨w₀, trivial⟩ isClosed_univ.isLocallyClosed
  let s₀ := pointOfClosedPoint h w hw
  have hs₀ : s₀ ≫ g = e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, Iso.inv_hom_id]
    exact pointOfClosedPoint_comp h w hw
  let σl : V.left ⟶ W.left := C.inclusion.preimage (e.hom ≫ s₀)
  have hσl : σl ≫ f.left = 𝟙 V.left := by
    apply C.inclusion.map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_preimage, Category.assoc]
    show e.hom ≫ s₀ ≫ g = _
    rw [hs₀, Iso.hom_inv_id]
    rfl
  refine ⟨Over.homMk σl ?_, Over.OverMorphism.ext hσl⟩
  rw [← Over.w f, ← Category.assoc, hσl, Category.id_comp]

/-- **Every object of a quotient stack over the spectrum of an algebraically closed field is
presented by a point of the object space.** An object `x` over `V` becomes presented after
pullback along a surjective, flat morphism `f : W ⟶ V` locally of finite presentation
(`AlgebraicGeometry.Stack.exists_single_cover_presented_pair`); such an `f` has a section `σ`
(`AlgebraicGeometry.Stack.exists_section_of_isAlgClosed`), and the pullback along `σ` of a
presented object is presented. -/
theorem exists_presented_of_isAlgClosed {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (k : Type u) [Field k] [IsAlgClosed k]
    (V : BigFppfOver C S hS) (e : (BigFppfOver.toScheme C S hS).obj V ≅ Spec (.of k))
    (x : (quotientStack G).p.Fiber V) :
    ∃ a : G.objects.obj.obj (op V),
      Nonempty ((pointwiseToQuotientStackFiber G V).obj a ≅ x) := by
  obtain ⟨W, f, -, hlfp, hsurj, a, -, ⟨ea⟩, -⟩ :=
    exists_single_cover_presented_pair C S hS G V x x
  obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed k e f hlfp hsurj
  exact ⟨G.objects.obj.map σ.op a,
    ⟨(presentedPullbackIso G W a _ rfl (Over.mk σ)).symm ≪≫
      Functor.pullbackFiberIso ea σ ≪≫ Functor.pullbackFiberCompIso' x f σ (𝟙 V) hσ ≪≫
      Functor.pullbackFiberIdIso x⟩⟩

end Presented

/-! ### Lifting vertical arrows through the induced map of quotient stacks -/

section LiftQuotient

variable {B : AlgebraicSpaces C S hS} {G H : GroupoidInAlgebraicSpaces C S hS B}

/-- **The induced map of quotient stacks is full on a fibre where every object is presented and
the evaluated groupoid map is full.** Let `f : G ⟶ H` be a morphism of groupoids in algebraic
spaces and `V` a test object such that every object of `[U/R]` over `V` is isomorphic to one
presented by a `V`-point, and such that the functor `G(V) ⥤ H(V)` of groupoids of `V`-points is
full. Then every vertical arrow `[f](y₁) ⟶ [f](y₂)` between objects over `V` is `[f](α)` for a
vertical `α : y₁ ⟶ y₂`.

After replacing `y₁, y₂` by presented objects and conjugating by the 2-isomorphism of Stacks 046Q,
the arrow is a vertical arrow between objects of `[U'/R']` presented by `V`-points, hence an arrow
of `H(V)` by Stacks 044X (2); it lifts to `G(V)` by fullness, and its image in `[U/R]` is `α`. -/
theorem exists_lift_quotientStackMap (f : GroupoidInAlgebraicSpaces.Hom G H)
    (V : BigFppfOver C S hS)
    (hpres : ∀ x : (quotientStack G).p.Fiber V, ∃ a : G.objects.obj.obj (op V),
      Nonempty ((pointwiseToQuotientStackFiber G V).obj a ≅ x))
    (hfull : (f.toGroupoidHom.evaluation (op V)).Full)
    {y₁ y₂ : (quotientStack G).obj} (h₁ : (quotientStack G).p.obj y₁ = V)
    (h₂ : (quotientStack G).p.obj y₂ = V)
    (β : (quotientStackMap f).obj y₁ ⟶ (quotientStackMap f).obj y₂)
    (hβ : (quotientStack H).p.IsHomLift (𝟙 V) β) :
    ∃ α : y₁ ⟶ y₂, (quotientStack G).p.IsHomLift (𝟙 V) α ∧ (quotientStackMap f).map α = β := by
  obtain ⟨a₁, ⟨ι₁⟩⟩ := hpres ⟨y₁, h₁⟩
  obtain ⟨a₂, ⟨ι₂⟩⟩ := hpres ⟨y₂, h₂⟩
  let M := quotientStackMap f
  let j₁ := Functor.Fiber.fiberInclusion.mapIso ι₁
  let j₂ := Functor.Fiber.fiberInclusion.mapIso ι₂
  let c₁ := (quotientStackMap_commutes f).hom.toNatTrans.app ⟨V, a₁⟩
  let c₁' := (quotientStackMap_commutes f).inv.toNatTrans.app ⟨V, a₁⟩
  let c₂ := (quotientStackMap_commutes f).hom.toNatTrans.app ⟨V, a₂⟩
  let c₂' := (quotientStackMap_commutes f).inv.toNatTrans.app ⟨V, a₂⟩
  let m : (pointwiseToQuotientStack H).obj ⟨V, (f.toGroupoidHom.evaluation (op V)).obj a₁⟩ ⟶
      (pointwiseToQuotientStack H).obj ⟨V, (f.toGroupoidHom.evaluation (op V)).obj a₂⟩ :=
    c₁ ≫ (M.mapIso j₁).hom ≫ β ≫ (M.mapIso j₂).inv ≫ c₂'
  have hm : (quotientStack H).p.IsHomLift (𝟙 V) m := by
    have hc₁ : (quotientStack H).p.IsHomLift (𝟙 V) c₁ :=
      (quotientStackMap_commutes f).hom.isHomLift rfl
    have hc₂ : (quotientStack H).p.IsHomLift (𝟙 V) c₂' :=
      (quotientStackMap_commutes f).inv.isHomLift rfl
    have hj : ∀ {y y' : (quotientStack G).obj} (u : y ⟶ y'),
        (quotientStack G).p.IsHomLift (𝟙 V) u → (quotientStack H).p.IsHomLift (𝟙 V) (M.map u) :=
      fun u hu => by
        have := hu
        exact Functor.isHomLift_map_of_comp_eq M.w (𝟙 V) u
    exact isHomLift_id_comp_id _ _ _ hc₁ (isHomLift_id_comp_id _ _ _ (hj _ ι₁.hom.2)
      (isHomLift_id_comp_id _ _ _ hβ (isHomLift_id_comp_id _ _ _ (hj _ ι₂.inv.2) hc₂)))
  obtain ⟨arr, harr⟩ := exists_evaluationArrow H V _ _ m hm
  obtain ⟨ε, rfl⟩ := hfull.map_surjective arr
  refine ⟨Functor.Fiber.fiberInclusion.map
    (ι₁.inv ≫ (pointwiseToQuotientStackFiber G V).map ε ≫ ι₂.hom),
    (ι₁.inv ≫ (pointwiseToQuotientStackFiber G V).map ε ≫ ι₂.hom).2, ?_⟩
  have hnat := quotientStackMap_commutes_naturality f
    ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor' V).map ε)
  have hnat' : m ≫ c₂ = c₁ ≫ M.map ((pointwiseToQuotientStack G).map
      ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' V).map ε)) := by
    rw [← harr]
    exact (congrArg (fun k => (pointwiseToQuotientStack H).map k ≫ c₂)
      (quotientPointwiseMap_map_ι f V ε)).symm.trans hnat
  show M.map (j₁.inv ≫ (pointwiseToQuotientStack G).map
      ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' V).map ε) ≫ j₂.hom) = β
  have hcc := NatTrans.congr_app (congrArg (fun α => BasedNatTrans.toNatTrans α)
    (quotientStackMap_commutes f).inv_hom_id)
  refine (map_comp₃ M.toFunctor j₁.inv _ j₂.hom).trans ?_
  exact cancel_conj_aux c₁ c₁' c₂ c₂' (M.mapIso j₁).hom (M.mapIso j₁).inv (M.mapIso j₂).hom
    (M.mapIso j₂).inv m _ β hnat' rfl
    (hcc _) (hcc _)
    (M.mapIso j₁).inv_hom_id (M.mapIso j₂).inv_hom_id

end LiftQuotient

/-! ### The trivial action groupoids -/

section TrivialAction

/-- The final algebraic space has at most one point over every test object. -/
instance subsingleton_terminalSpace_obj (T : (BigFppfOver C S hS)ᵒᵖ) :
    Subsingleton ((Space.terminalSpace C S hS).obj.obj T) := by
  change Subsingleton (T.unop ⟶ Over.mk (𝟙 (C.obj hS)))
  exact ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩

variable {G₁ G₂ : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property}

/-- **The groupoid map of a homomorphism surjective on `V`-points is full at `V`.** If every
`V`-point of `G₂` lifts through `φ : G₁ ⟶ G₂`, then the functor between the groupoids of
`V`-points of the two trivial action groupoids is full: an arrow of the second is a `V`-point
`(g, *)` of `G₂ ×_S S`, and `(g', *)` with `φ(g') = g` is an arrow of the first mapping to it, the
object space being the final one. -/
theorem full_evaluation_trivialActionGroupoidHom (φ : G₁ ⟶ G₂) (V : BigFppfOver C S hS)
    (hV : ∀ x : yoneda.obj V ⟶ G₂.obj.X.left, ∃ z : yoneda.obj V ⟶ G₁.obj.X.left,
      z ≫ φ.hom.hom.hom.left = x) :
    ((trivialActionGroupoidHom φ).toGroupoidHom.evaluation (op V)).Full := by
  refine ⟨fun {a b} γ => ?_⟩
  have hsub : ∀ a b : (Space.terminalSpace C S hS).obj.obj (op V), a = b := fun _ _ =>
    @Subsingleton.elim _ (subsingleton_terminalSpace_obj (op V)) _ _
  let X := 𝟙_ (Over (Space.terminalSpace C S hS).obj)
  let r₂ := ((trivialActionGroupoid G₂).toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _ γ).1
  obtain ⟨z, hz⟩ := hV (yonedaEquiv.symm ((fst G₂.obj.X X).left.app (op V) r₂))
  let Z : Over (Space.terminalSpace C S hS).obj := Over.mk (z ≫ G₁.obj.X.hom)
  let l : Z ⟶ G₁.obj.X ⊗ X := lift (Over.homMk z) (toUnit Z)
  let r₁ : (trivialActionGroupoid G₁).arrows.obj.obj (op V) := yonedaEquiv l.left
  have hfst : (fst G₁.obj.X X).left.app (op V) r₁ = yonedaEquiv z :=
    (yonedaEquiv_comp l.left (fst G₁.obj.X X).left).symm.trans
      (congrArg yonedaEquiv (by rw [← Over.comp_left, lift_fst]; rfl))
  have hmap : (trivialActionArrowsMap φ).app (op V) r₁ = r₂ := by
    refine pullback_app_ext G₂.obj.X.hom X.hom (T := V) ?_ (hsub _ _)
    refine (trivialActionArrowsMap_fst_app φ (op V) r₁).trans ?_
    show φ.hom.hom.hom.left.app (op V) ((fst G₁.obj.X X).left.app (op V) r₁) = _
    rw [hfst, ← yonedaEquiv_comp, hz, Equiv.apply_symm_apply]
    rfl
  refine ⟨((trivialActionGroupoid G₁).toGroupoidInFunctors.evaluationArrowEquiv (op V) a b).symm
    ⟨r₁, hsub _ _, hsub _ _⟩, ?_⟩
  apply ((trivialActionGroupoid G₂).toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _).injective
  apply Subtype.ext
  rw [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow, Equiv.apply_symm_apply]
  exact hmap

end TrivialAction

/-! ### Universal injectivity of the map of classifying stacks -/

section ClassifyingMap

variable {G₁ G₂ : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property}
  (h₁ : Space.IsSmooth C S hS G₁.obj.X.hom) (h₂ : Space.IsSmooth C S hS G₂.obj.X.hom)

/-- **`classifyingMap φ` lifts 2-arrows at geometric points** (condition (3) of Stacks 0CPN) when
every point of `G₂` with values in an algebraically closed field lifts through `φ`.

Through the two model equivalences, which are fully faithful and strictly over the site, this is
the same statement for the 1-morphism `[S/G₁] ⟶ [S/G₂]` of quotient stacks of Stacks 046Q. There
every object over `Spec k` is presented by a point of the object space
(`AlgebraicGeometry.Stack.exists_presented_of_isAlgClosed`), and the functor between the groupoids
of `Spec k`-points is full by the lifting hypothesis
(`AlgebraicGeometry.Stack.full_evaluation_trivialActionGroupoidHom`), so
`AlgebraicGeometry.Stack.exists_lift_quotientStackMap` applies. -/
theorem liftsTwoArrowsAtGeometricPoints_classifyingMap (φ : G₁ ⟶ G₂)
    (hlift : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver C S hS),
      ((BigFppfOver.toScheme C S hS).obj V ≅ Spec (.of k)) →
        ∀ x : yoneda.obj V ⟶ G₂.obj.X.left, ∃ z : yoneda.obj V ⟶ G₁.obj.X.left,
          z ≫ φ.hom.hom.hom.left = x) :
    LiftsTwoArrowsAtGeometricPoints C S hS (classifyingMap.{u, w} h₁ h₂ φ) := by
  intro k _ _ V eV x₁ x₂ hx₁ hx₂ β hβ
  let e₁ := classifyingAlgebraicStackEquivalenceOver.{u, w} G₁ h₁
  let e₂ := classifyingAlgebraicStackEquivalenceOver.{u, w} G₂ h₂
  obtain ⟨β', hβ', hβ'eq⟩ := exists_isHomLift_preimage e₂.hom.w
    e₂.toEquivalence.fullyFaithfulFunctor (V := V) (x₁ := (quotientStackMap
      (trivialActionGroupoidHom φ)).obj (e₁.inv.functor.obj x₁))
    (x₂ := (quotientStackMap (trivialActionGroupoidHom φ)).obj (e₁.inv.functor.obj x₂)) β hβ
  obtain ⟨α', hα', hα'eq⟩ := exists_lift_quotientStackMap (trivialActionGroupoidHom φ) V
    (exists_presented_of_isAlgClosed _ k V eV)
    (full_evaluation_trivialActionGroupoidHom φ V (hlift k V eV))
    ((Functor.congr_obj e₁.inv.w x₁).trans hx₁) ((Functor.congr_obj e₁.inv.w x₂).trans hx₂)
    β' hβ'
  obtain ⟨α, hα, hαeq⟩ := exists_isHomLift_preimage e₁.inv.w
    e₁.toEquivalence.fullyFaithfulInverse α' hα'
  refine ⟨α, hα, ?_⟩
  show e₂.hom.functor.map ((quotientStackMap (trivialActionGroupoidHom φ)).map
    (e₁.inv.functor.map α)) = β
  rw [hαeq, hα'eq, hβ'eq]

/-- **The map of classifying stacks induced by a homomorphism surjective on geometric points is
universally injective.** Let `φ : G₁ ⟶ G₂` be a homomorphism of smooth group algebraic spaces over
`S` such that every point of `G₂` with values in an algebraically closed field `k` — a morphism
`yoneda V ⟶ G₂` from a site object `V` with underlying scheme `Spec k` — lifts through `φ`. Then
`classifyingMap φ : BG₁ ⟶ BG₂` is universally injective: it lifts 2-arrows at geometric points
(`AlgebraicGeometry.Stack.liftsTwoArrowsAtGeometricPoints_classifyingMap`), which is condition (3)
of Stacks 0CPN. -/
theorem universallyInjective_classifyingMap (φ : G₁ ⟶ G₂)
    (hlift : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver C S hS),
      ((BigFppfOver.toScheme C S hS).obj V ≅ Spec (.of k)) →
        ∀ x : yoneda.obj V ⟶ G₂.obj.X.left, ∃ z : yoneda.obj V ⟶ G₁.obj.X.left,
          z ≫ φ.hom.hom.hom.left = x) :
    UniversallyInjective C S hS (classifyingMap.{u, w} h₁ h₂ φ) :=
  universallyInjective_of_liftsTwoArrowsAtGeometricPoints C S hS _
    (liftsTwoArrowsAtGeometricPoints_classifyingMap.{u, w} h₁ h₂ φ hlift)

end ClassifyingMap

end AlgebraicGeometry.Stack

end

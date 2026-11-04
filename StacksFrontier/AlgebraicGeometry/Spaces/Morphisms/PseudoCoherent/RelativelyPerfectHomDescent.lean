module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback

/-!
# Descent of derived homomorphisms in a relative descent situation of algebraic spaces

In a relative descent situation — a directed inverse system of quasi-compact quasi-separated
algebraic spaces with affine transitions, a flat finitely presented space `X₀` over one stage
`Y₀`, and its base changes `Xᵢ` and `X` — an object of `D(𝒪_{X₀})` pulls back to every `Xᵢ` and
to `X`. For `Kᵢ = Lf_{i0}^*K₀` and `Lᵢ = Lf_{i0}^*L₀` the derived homomorphism sets
`Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ)` form a system over the stages, with a canonical map from its colimit
to `Hom_{D(𝒪_X)}(K, L)`. This file constructs that system and its colimit comparison, and the
restriction of the situation along a flat finitely presented morphism onto `X₀`.

## Main definitions

* `AlgebraicGeometry.Space.DerivedPullbackComposition`: the pseudofunctoriality of the derived
  pullback on the small étale ringed topoi of algebraic spaces, as a datum.
* `AlgebraicGeometry.Space.RelativeDescentSituation.restrict`: the situation restricted along a
  flat morphism of finite presentation `g : U₀ ⟶ X₀`: the inverse system and its limit are
  unchanged, `U₀` replaces `X₀` with structure morphism `g ≫ p₀`, and the base changes are the
  fibre products `Xᵢ ×_{X₀} U₀` and `X ×_{X₀} U₀`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homFunctor` and `homCocone`: the system of
  derived homomorphism sets over the stages and the cocone on it with vertex
  `Hom_{D(𝒪_X)}(K, L)`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent`: every homomorphism at the limit
  comes from a stage, and two homomorphisms at a stage with the same image agree at a later
  stage.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.transition_self`,
  `transition_comp_transition` and `projection_comp_transition`: the transitions and projections
  of the base changes compose as a system.
* `AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom_comp` and `factorHom_id`: the
  maps on derived homomorphism sets induced by a factorisation compose, and a factorisation
  through an identity induces the identity.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_iff_nonempty_isColimit` and
  `homDescent_iff_isIso_colimitDesc`: `HomDescent` says exactly that the cocone is colimiting,
  equivalently that the canonical map out of the colimit is an isomorphism.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v

attribute [local instance 10000] HasDerivedCategory.standard

section Composition

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y)]

/-- The pseudofunctoriality of the derived pullback of modules on the small étale ringed topoi of
algebraic spaces: the identification `Lg^* ⋙ Lf^* ≅ L(f ∘ g)^*` attached to a factorisation, the
identification `L(𝟙)^* ≅ 𝟭`, and their associativity and unit coherences. -/
structure DerivedPullbackComposition where
  /-- The identification `Lg^* ⋙ Lf^* ≅ Lk^*` attached to a factorisation `f ≫ g = k`. -/
  iso : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z), f ≫ g = k →
    (smallEtaleDerivedModulePullback B S hS g ⋙ smallEtaleDerivedModulePullback B S hS f ≅
      smallEtaleDerivedModulePullback B S hS k)
  /-- The identification `L(𝟙)^* ≅ 𝟭`. -/
  idIso : ∀ X : AlgebraicSpaces B S hS,
    smallEtaleDerivedModulePullback B S hS (𝟙 X) ≅ 𝟭 _
  /-- The identifications of the factorisations of a threefold composite agree. -/
  iso_assoc : ∀ {V W Y Z : AlgebraicSpaces B S hS} (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z)
    (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c)
    (hpb : p ≫ b = c) (M : DerivedCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))),
    (iso p t q hq).app ((smallEtaleDerivedModulePullback B S hS a).obj M) ≪≫
        (iso q a c hc).app M =
      (smallEtaleDerivedModulePullback B S hS p).mapIso ((iso t a b hb).app M) ≪≫
        (iso p b c hpb).app M
  /-- The identification of a factorisation through an identity is the one `idIso` gives. -/
  iso_id : ∀ {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z) (h : 𝟙 X ≫ a = a),
    iso (𝟙 X) a a h =
      Functor.isoWhiskerLeft (smallEtaleDerivedModulePullback B S hS a) (idIso X) ≪≫
        (smallEtaleDerivedModulePullback B S hS a).rightUnitor

namespace DerivedPullbackComposition

variable {B S hS} (P : DerivedPullbackComposition B S hS)

/-- The map `Hom(Lg^*K, Lg^*L) ⟶ Hom(Lk^*K, Lk^*L)` induced by a factorisation `f ≫ g = k`:
apply `Lf^*` and transport along the identification of `Lg^* ⋙ Lf^*` with `Lk^*`. -/
def factorHom {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (φ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    (smallEtaleDerivedModulePullback B S hS k).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS k).obj L :=
  ((P.iso f g k h).app K).homCongr ((P.iso f g k h).app L)
    ((smallEtaleDerivedModulePullback B S hS f).map φ)

/-- The maps on derived homomorphisms induced by the factorisations of `c = p ≫ t ≫ a`
compose. -/
theorem factorHom_comp {V W Y Z : AlgebraicSpaces B S hS} (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z)
    (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c)
    (hpb : p ≫ b = c)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (φ : (smallEtaleDerivedModulePullback B S hS a).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS a).obj L) :
    P.factorHom p b c hpb K L (P.factorHom t a b hb K L φ) = P.factorHom q a c hc K L φ := by
  have hK := congrArg Iso.inv (P.iso_assoc p t a b q c hb hq hc hpb K)
  have hL := congrArg Iso.hom (P.iso_assoc p t a b q c hb hq hc hpb L)
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv] at hK hL
  have nat : ((P.iso p t q hq).app ((smallEtaleDerivedModulePullback B S hS a).obj K)).inv ≫
      (smallEtaleDerivedModulePullback B S hS p).map
          ((smallEtaleDerivedModulePullback B S hS t).map φ) ≫
        ((P.iso p t q hq).app ((smallEtaleDerivedModulePullback B S hS a).obj L)).hom =
      (smallEtaleDerivedModulePullback B S hS q).map φ := by
    rw [Iso.inv_comp_eq]
    exact (P.iso p t q hq).hom.naturality φ
  simp only [factorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc]
  rw [← hL, ← Category.assoc, ← Category.assoc, ← hK]
  simp only [Category.assoc]
  rw [reassoc_of% nat]

/-- A three-factor composite followed by an identity collapses to `φ` when its last two factors
factor through `φ` and the first two cancel. -/
private theorem comp_three_comp_id {E : Type*} [Category E] {A A' C C' : E} {s : A ⟶ A'}
    {t : A' ⟶ C} {r : C ⟶ C'} {s' : A' ⟶ A} {φ : A ⟶ C'} (h1 : t ≫ r = s' ≫ φ)
    (h2 : s ≫ s' = 𝟙 A) : s ≫ t ≫ r ≫ 𝟙 C' = φ := by
  rw [Category.comp_id, h1, ← Category.assoc, h2, Category.id_comp]

/-- The map on derived homomorphisms induced by a factorisation through an identity is the
identity. -/
theorem factorHom_id {X Z : AlgebraicSpaces B S hS} {f : X ⟶ X} (hf : f = 𝟙 X) (a : X ⟶ Z)
    (h : f ≫ a = a)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (φ : (smallEtaleDerivedModulePullback B S hS a).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS a).obj L) :
    P.factorHom f a a h K L φ = φ := by
  subst hf
  rw [factorHom, P.iso_id a h]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app, Category.id_comp,
    Iso.homCongr_apply]
  exact comp_three_comp_id ((P.idIso X).hom.naturality φ) ((P.idIso X).inv_hom_id_app _)

end DerivedPullbackComposition

end Composition

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- The stages of the inverse system at or beyond the stage carrying the chosen flat space. -/
abbrev LaterIndex := {i : I // D.i₀ ≤ i}

/-- The chosen stage is a stage at or beyond itself. -/
theorem nonempty_laterIndex : Nonempty D.LaterIndex :=
  ⟨⟨D.i₀, le_refl _⟩⟩

/-- The stages at or beyond the chosen one are directed. -/
theorem isDirected_laterIndex : IsDirected D.LaterIndex (· ≤ ·) := by
  refine ⟨fun i j ↦ ?_⟩
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
  exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

/-- The transition morphism of a stage to itself is the identity. -/
theorem transition_self (i : I) (hi : D.i₀ ≤ i) :
    D.fᵢⱼ i i hi hi (le_refl i) = 𝟙 (D.Xᵢ i hi) := by
  refine (D.stage_isPullback i hi).hom_ext ?_ ?_
  · rw [D.fᵢⱼ_toYᵢ i i hi hi (le_refl i), Category.id_comp,
      show (homOfLE (le_refl i)).op = 𝟙 (op i) from Subsingleton.elim _ _, D.Y.map_id,
      Category.comp_id]
  · rw [D.fᵢⱼ_toX₀ i i hi hi (le_refl i), Category.id_comp]

/-- The transition morphisms between the base changes compose. -/
theorem transition_comp_transition {i j k : I} (hi : D.i₀ ≤ i) (hj : D.i₀ ≤ j)
    (hk : D.i₀ ≤ k) (hij : i ≤ j) (hjk : j ≤ k) :
    D.fᵢⱼ j k hj hk hjk ≫ D.fᵢⱼ i j hi hj hij = D.fᵢⱼ i k hi hk (hij.trans hjk) := by
  refine (D.stage_isPullback i hi).hom_ext ?_ ?_
  · rw [Category.assoc, D.fᵢⱼ_toYᵢ i j hi hj hij, ← Category.assoc,
      D.fᵢⱼ_toYᵢ j k hj hk hjk, Category.assoc, ← D.Y.map_comp,
      D.fᵢⱼ_toYᵢ i k hi hk (hij.trans hjk)]
    exact congrArg (fun m ↦ D.toYᵢ k hk ≫ D.Y.map m) (Subsingleton.elim _ _)
  · rw [Category.assoc, D.fᵢⱼ_toX₀ i j hi hj hij, D.fᵢⱼ_toX₀ j k hj hk hjk,
      D.fᵢⱼ_toX₀ i k hi hk (hij.trans hjk)]

/-- The projections from the limit base change are compatible with the transition morphisms. -/
theorem projection_comp_transition {i j : I} (hi : D.i₀ ≤ i) (hj : D.i₀ ≤ j) (hij : i ≤ j) :
    D.fᵢ j hj ≫ D.fᵢⱼ i j hi hj hij = D.fᵢ i hi := by
  refine (D.stage_isPullback i hi).hom_ext ?_ ?_
  · rw [Category.assoc, D.fᵢⱼ_toYᵢ i j hi hj hij, ← Category.assoc, D.fᵢ_toYᵢ j hj,
      Category.assoc, D.limitCone.w (homOfLE hij).op, D.fᵢ_toYᵢ i hi]
  · rw [Category.assoc, D.fᵢⱼ_toX₀ i j hi hj hij, D.fᵢ_toX₀ j hj, D.fᵢ_toX₀ i hi]

/-! ### The spaces of the situation as objects of the category of algebraic spaces -/

/-- The space `X₀` over the chosen stage, as an object of the category of algebraic spaces. -/
abbrev initialSource : AlgebraicSpaces B S hS := ⟨D.X₀, D.initial_isAlgebraicSpace⟩

/-- The base change `Xᵢ` at a later stage, as an object of the category of algebraic spaces. -/
abbrev stageSource (i : D.LaterIndex) : AlgebraicSpaces B S hS :=
  ⟨D.Xᵢ i.1 i.2, D.stageX_isAlgebraicSpace i.1 i.2⟩

/-- The base change `X` at the limit, as an object of the category of algebraic spaces. -/
abbrev limitSource : AlgebraicSpaces B S hS := ⟨D.X, D.X_isAlgebraicSpace⟩

/-- The stage of the inverse system over which the chosen flat space lives, as an object of the
category of algebraic spaces. -/
abbrev initialTarget : AlgebraicSpaces B S hS :=
  ⟨D.Y.obj (op D.i₀), D.stage_isAlgebraicSpace D.i₀⟩

/-- The chosen flat morphism of finite presentation `X₀ ⟶ Y₀`, as a morphism of algebraic
spaces. -/
abbrev initialStructure : D.initialSource ⟶ D.initialTarget := ObjectProperty.homMk D.p₀

/-- The projection `f_{i0} : Xᵢ ⟶ X₀`. -/
abbrev stageToInitial (i : D.LaterIndex) : D.stageSource i ⟶ D.initialSource :=
  ObjectProperty.homMk (D.toX₀ i.1 i.2)

/-- The projection `f_0 : X ⟶ X₀`. -/
abbrev limitToInitial : D.limitSource ⟶ D.initialSource :=
  ObjectProperty.homMk D.toInitial

/-- The transition morphism `f_{ji} : Xⱼ ⟶ Xᵢ` of the base changes, for `i ≤ j`. -/
abbrev sourceTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.stageSource j ⟶ D.stageSource i :=
  ObjectProperty.homMk (D.fᵢⱼ i.1 j.1 i.2 j.2 h)

/-- The projection `fᵢ : X ⟶ Xᵢ` from the limit base change. -/
abbrev sourceProjection (i : D.LaterIndex) : D.limitSource ⟶ D.stageSource i :=
  ObjectProperty.homMk (D.fᵢ i.1 i.2)

/-- The transition morphism of a stage to itself is the identity. -/
theorem sourceTransition_self (i : D.LaterIndex) :
    D.sourceTransition (le_refl i.1) = 𝟙 (D.stageSource i) :=
  ObjectProperty.hom_ext _ (D.transition_self i.1 i.2)

/-- The transition morphisms of the base changes compose. -/
theorem sourceTransition_comp_sourceTransition {i j k : D.LaterIndex} (hij : i.1 ≤ j.1)
    (hjk : j.1 ≤ k.1) :
    D.sourceTransition hjk ≫ D.sourceTransition hij = D.sourceTransition (hij.trans hjk) :=
  ObjectProperty.hom_ext _ (D.transition_comp_transition i.2 j.2 k.2 hij hjk)

/-- The projections from the limit base change are compatible with the transitions. -/
theorem sourceProjection_comp_sourceTransition {i j : D.LaterIndex} (hij : i.1 ≤ j.1) :
    D.sourceProjection j ≫ D.sourceTransition hij = D.sourceProjection i :=
  ObjectProperty.hom_ext _ (D.projection_comp_transition i.2 j.2 hij)

/-- A transition morphism of the base changes lies over the projection to `X₀`. -/
theorem sourceTransition_comp_stageToInitial {i j : D.LaterIndex} (hij : i.1 ≤ j.1) :
    D.sourceTransition hij ≫ D.stageToInitial i = D.stageToInitial j :=
  ObjectProperty.hom_ext _ (D.fᵢⱼ_toX₀ i.1 j.1 i.2 j.2 hij)

/-- A projection from the limit base change lies over the projection to `X₀`. -/
theorem sourceProjection_comp_stageToInitial (i : D.LaterIndex) :
    D.sourceProjection i ≫ D.stageToInitial i = D.limitToInitial :=
  ObjectProperty.hom_ext _ (D.fᵢ_toX₀ i.1 i.2)

/-! ### Restriction of the situation along a morphism onto `X₀` -/

/-- The restriction of a relative descent situation along a flat finitely presented morphism
`g : U₀ ⟶ X₀`: the inverse system, its limit and the chosen stage are unchanged, `U₀` replaces
`X₀` with structure morphism `g ≫ p₀`, and the base changes are the fibre products
`Xᵢ ×_{X₀} U₀` and `X ×_{X₀} U₀`. -/
@[stacks 0DKV "the restriction of Situation 0DKU along a flat morphism of finite presentation, \
  a step the tag's proof needs and which this development lacked; stated for flat plus finite \
  presentation rather than étale, which is strictly more general. The tag's own conclusion is not \
  proved here"]
def restrict {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAlgebraicSpace B S hS U₀)
    (g : U₀ ⟶ D.X₀) (hgflat : IsFlat B S hS g)
    (hgfp : IsFinitePresentation B S hS g) : RelativeDescentSituation B S hS hZ I where
  Y := D.Y
  limitCone := D.limitCone
  isLimit := D.isLimit
  stage_isAlgebraicSpace := D.stage_isAlgebraicSpace
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  stage_isQuasiCompact := D.stage_isQuasiCompact
  stage_isQuasiSeparated := D.stage_isQuasiSeparated
  transition_isAffine := D.transition_isAffine
  i₀ := D.i₀
  X₀ := U₀
  p₀ := g ≫ D.p₀
  initial_isAlgebraicSpace := hU₀
  initial_isFlat := isFlat_comp B S hS hU₀ D.initial_isAlgebraicSpace
    (D.stage_isAlgebraicSpace D.i₀) g D.p₀ hgflat D.initial_isFlat
  initial_isFinitePresentation := isFinitePresentation_comp B S hS hU₀
    D.initial_isAlgebraicSpace (D.stage_isAlgebraicSpace D.i₀) g D.p₀ hgfp
    D.initial_isFinitePresentation
  Xᵢ i hi := pullback (D.toX₀ i hi) g
  stageX_isAlgebraicSpace i hi := isAlgebraicSpace_pullback B S hS (D.toX₀ i hi) g
    (D.stageX_isAlgebraicSpace i hi) hU₀ D.initial_isAlgebraicSpace
  toX₀ i hi := pullback.snd (D.toX₀ i hi) g
  toYᵢ i hi := pullback.fst (D.toX₀ i hi) g ≫ D.toYᵢ i hi
  stage_isPullback i hi :=
    (IsPullback.of_hasPullback (D.toX₀ i hi) g).paste_horiz (D.stage_isPullback i hi)
  fᵢⱼ i j hi hj hij :=
    pullback.lift (pullback.fst (D.toX₀ j hj) g ≫ D.fᵢⱼ i j hi hj hij)
      (pullback.snd (D.toX₀ j hj) g)
      (by rw [Category.assoc, D.fᵢⱼ_toX₀ i j hi hj hij]; exact pullback.condition)
  fᵢⱼ_toYᵢ i j hi hj hij := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, D.fᵢⱼ_toYᵢ i j hi hj hij,
      Category.assoc]
  fᵢⱼ_toX₀ i j hi hj hij := pullback.lift_snd _ _ _
  X := pullback D.toInitial g
  X_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS D.toInitial g D.X_isAlgebraicSpace hU₀
    D.initial_isAlgebraicSpace
  toInitial := pullback.snd D.toInitial g
  toLimit := pullback.fst D.toInitial g ≫ D.toLimit
  limit_isPullback :=
    (IsPullback.of_hasPullback D.toInitial g).paste_horiz D.limit_isPullback
  fᵢ i hi :=
    pullback.lift (pullback.fst D.toInitial g ≫ D.fᵢ i hi) (pullback.snd D.toInitial g)
      (by rw [Category.assoc, D.fᵢ_toX₀ i hi]; exact pullback.condition)
  fᵢ_toYᵢ i hi := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, D.fᵢ_toYᵢ i hi, Category.assoc]
  fᵢ_toX₀ i hi := pullback.lift_snd _ _ _

/-- The restricted situation has the same inverse system, limit and chosen stage, hence the same
stages at or beyond it. -/
theorem restrict_laterIndex {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀) (hgflat : IsFlat B S hS g)
    (hgfp : IsFinitePresentation B S hS g) :
    (D.restrict hU₀ g hgflat hgfp).LaterIndex = D.LaterIndex :=
  rfl

/-- The space over the chosen stage of the restricted situation is `U₀`. -/
theorem restrict_initialSource {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀) (hgflat : IsFlat B S hS g)
    (hgfp : IsFinitePresentation B S hS g) :
    (D.restrict hU₀ g hgflat hgfp).initialSource = ⟨U₀, hU₀⟩ :=
  rfl

/-! ### The system of derived homomorphism sets -/

section HomSystem

variable [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y)]
  (P : DerivedPullbackComposition B S hS)
  (K₀ L₀ : DerivedCategory (Modules.{u, u} B S hS D.X₀ D.initial_isAlgebraicSpace))

/-- The transition map `Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_{Xⱼ})}(Kⱼ, Lⱼ)` for `i ≤ j`, given
by applying `Lf_{ji}^*`. -/
def homTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj K₀ ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L₀) :
    (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj K₀ ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial j)).obj L₀ :=
  P.factorHom (D.sourceTransition h) (D.stageToInitial i) (D.stageToInitial j)
    (D.sourceTransition_comp_stageToInitial h) K₀ L₀ φ

/-- The comparison map `Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_X)}(K, L)`, given by applying
`Lfᵢ^*`. -/
def homComparison (i : D.LaterIndex)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj K₀ ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L₀) :
    (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj K₀ ⟶
      (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj L₀ :=
  P.factorHom (D.sourceProjection i) (D.stageToInitial i) D.limitToInitial
    (D.sourceProjection_comp_stageToInitial i) K₀ L₀ φ

/-- The transition map of the system of derived homomorphism sets at a stage to itself is the
identity. -/
theorem homTransition_refl (i : D.LaterIndex) :
    D.homTransition P K₀ L₀ (le_refl i.1) = id :=
  funext fun φ ↦ P.factorHom_id (D.sourceTransition_self i) (D.stageToInitial i)
    (D.sourceTransition_comp_stageToInitial (le_refl i.1)) K₀ L₀ φ

/-- The transition maps of the system of derived homomorphism sets compose. -/
theorem homTransition_homTransition {i j k : D.LaterIndex} (hij : i.1 ≤ j.1) (hjk : j.1 ≤ k.1)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj K₀ ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L₀) :
    D.homTransition P K₀ L₀ hjk (D.homTransition P K₀ L₀ hij φ) =
      D.homTransition P K₀ L₀ (hij.trans hjk) φ :=
  P.factorHom_comp (D.sourceTransition hjk) (D.sourceTransition hij) (D.stageToInitial i)
    (D.stageToInitial j) (D.sourceTransition (hij.trans hjk)) (D.stageToInitial k)
    (D.sourceTransition_comp_stageToInitial hij)
    (D.sourceTransition_comp_sourceTransition hij hjk)
    (D.sourceTransition_comp_stageToInitial (hij.trans hjk))
    (D.sourceTransition_comp_stageToInitial hjk) K₀ L₀ φ

/-- The comparison maps are compatible with the transition maps. -/
theorem homComparison_homTransition {i j : D.LaterIndex} (hij : i.1 ≤ j.1)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj K₀ ⟶
      (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L₀) :
    D.homComparison P K₀ L₀ j (D.homTransition P K₀ L₀ hij φ) =
      D.homComparison P K₀ L₀ i φ :=
  P.factorHom_comp (D.sourceProjection j) (D.sourceTransition hij) (D.stageToInitial i)
    (D.stageToInitial j) (D.sourceProjection i) D.limitToInitial
    (D.sourceTransition_comp_stageToInitial hij)
    (D.sourceProjection_comp_sourceTransition hij)
    (D.sourceProjection_comp_stageToInitial i)
    (D.sourceProjection_comp_stageToInitial j) K₀ L₀ φ

/-- The system `i ↦ Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ)` of derived homomorphism sets over the stages at or
beyond the chosen one, with transition maps `homTransition`. -/
def homFunctor : D.LaterIndex ⥤ Type (u + 1) where
  obj i := (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj K₀ ⟶
    (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L₀
  map h := TypeCat.ofHom (D.homTransition P K₀ L₀ (leOfHom h))
  map_id i := by
    ext φ
    exact congrFun (D.homTransition_refl P K₀ L₀ i) φ
  map_comp f g := by
    ext φ
    exact (D.homTransition_homTransition P K₀ L₀ (leOfHom f) (leOfHom g) φ).symm

/-- The cocone on `homFunctor` with vertex `Hom_{D(𝒪_X)}(K, L)` whose leg at a stage is the
comparison map `homComparison`. -/
def homCocone : Cocone (D.homFunctor P K₀ L₀) where
  pt := (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj K₀ ⟶
    (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj L₀
  ι :=
    { app i := TypeCat.ofHom (D.homComparison P K₀ L₀ i)
      naturality := fun i j h ↦ by
        ext φ
        exact D.homComparison_homTransition P K₀ L₀ (leOfHom h) φ }

/-- Descent of derived homomorphisms, in elementary form: every morphism `K ⟶ L` on the limit
base change is the image of a morphism at some stage, and two morphisms at a stage with the same
image agree at some later stage. -/
def HomDescent : Prop :=
  (∀ ψ : (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj K₀ ⟶
        (smallEtaleDerivedModulePullback B S hS D.limitToInitial).obj L₀,
      ∃ (i : D.LaterIndex)
        (φ : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj K₀ ⟶
          (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L₀),
        D.homComparison P K₀ L₀ i φ = ψ) ∧
    ∀ (i : D.LaterIndex)
      (φ φ' : (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj K₀ ⟶
        (smallEtaleDerivedModulePullback B S hS (D.stageToInitial i)).obj L₀),
      D.homComparison P K₀ L₀ i φ = D.homComparison P K₀ L₀ i φ' →
        ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1),
          D.homTransition P K₀ L₀ h φ = D.homTransition P K₀ L₀ h φ'

/-- `HomDescent` holds exactly when the comparison maps exhibit `Hom_{D(𝒪_X)}(K, L)` as the
colimit of the system of derived homomorphism sets over the stages. -/
theorem homDescent_iff_nonempty_isColimit :
    D.HomDescent P K₀ L₀ ↔ Nonempty (IsColimit (D.homCocone P K₀ L₀)) := by
  have _ : Nonempty D.LaterIndex := D.nonempty_laterIndex
  have _ : IsDirected D.LaterIndex (· ≤ ·) := D.isDirected_laterIndex
  refine ⟨fun ⟨hsurj, hinj⟩ ↦ ⟨Types.FilteredColimit.isColimitOf' _ _
      (fun ψ ↦ let ⟨i, φ, hφ⟩ := hsurj ψ; ⟨i, φ, hφ.symm⟩)
      fun i φ φ' hφ ↦ let ⟨j, hij, hj⟩ := hinj i φ φ' hφ; ⟨j, homOfLE hij, hj⟩⟩,
    fun ⟨hc⟩ ↦ ⟨Types.jointly_surjective_of_isColimit hc, fun i φ φ' hφ ↦
      let ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc φ φ').1 hφ
      ⟨j, leOfHom f, hf⟩⟩⟩

/-- `HomDescent` holds exactly when the canonical map from the colimit of the system of derived
homomorphism sets to `Hom_{D(𝒪_X)}(K, L)` is an isomorphism. -/
@[stacks 0DKV "the tag's conclusion reformulated: the elementary descent statement holds exactly \
when the canonical colimit comparison map is invertible"]
theorem homDescent_iff_isIso_colimitDesc [HasColimit (D.homFunctor P K₀ L₀)] :
    D.HomDescent P K₀ L₀ ↔
      IsIso (colimit.desc (D.homFunctor P K₀ L₀) (D.homCocone P K₀ L₀)) :=
  (D.homDescent_iff_nonempty_isColimit P K₀ L₀).trans
    (colimit.isColimit (D.homFunctor P K₀ L₀)).nonempty_isColimit_iff_isIso_desc

end HomSystem

end RelativeDescentSituation

end AlgebraicGeometry.Space

end

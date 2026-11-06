module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent

/-!
# Direct image of a quasi-coherent module along a morphism of groupoids in algebraic spaces

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over `A` with `f : U ⟶ U'` quasi-compact and quasi-separated, with the square formed by
`R ⟶ R'` over `t`, `t'` and `U ⟶ U'` cartesian, and with `s'` and `t'` flat.  **Stacks 0GPM**
asserts that `(ℱ, α) ↦ (f_*ℱ, f_*α)` is a functor from the quasi-coherent modules on
`(U, R, s, t, c)` to those on `(U', R', s', t', c')`, right adjoint to the inverse image.

This file builds the transition morphism `f_*α : (t')^*f_*ℱ ⟶ (s')^*f_*ℱ`, proves that it is an
isomorphism and that it is natural in `(ℱ, α)`.  The base change maps of the two squares of the
morphism are invertible at a quasi-coherent module by the degree-zero flat base change
`AlgebraicGeometry.Space.flatBaseChangeZero` (Stacks 073K, part (1) at `i = 0`).  The cocycle and
unit laws, the functor and the adjunction are in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentPushforwardFunctor.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentPushforwardAdjunction.lean`.  The
sibling statement for groupoid *schemes* is **Stacks 09VH**, in
`StacksFrontier/AlgebraicGeometry/Groupoids/Equivariant/PushforwardDescent.lean`.

## Main definitions

* `AlgebraicGeometry.Space.moduleBaseChangeApp` is the base change map
  `AlgebraicGeometry.Space.moduleBaseChangeMap` of a commutative square at one module, with its
  type written with the inverse and direct images applied one after the other.
* `AlgebraicGeometry.Space.baseChangeTransition` transports a morphism `g'^*ℱ ⟶ h'^*ℱ` through
  the base change maps of two squares over the same vertical morphisms.
* `AlgebraicGeometry.Space.groupoidSourceBaseChangeIso` is the base change isomorphism
  `(s')^*f_*ℱ ≅ f_*s^*ℱ` of the square over the source morphisms, at a quasi-coherent module.
* `AlgebraicGeometry.Space.groupoidModulePushforwardTransition` is the transition morphism
  `f_*α` of the direct image.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_arrowsMap_source`: the square
  formed by `R ⟶ R'` over `s`, `s'` and `U ⟶ U'` is cartesian as soon as the one over `t`, `t'`
  is.  This is the step the source performs when it says that the analogous `s`-square is
  cartesian;  it is obtained by pasting the given square between the two cartesian squares of
  the inverse morphisms of the two groupoids.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.inverseArrow_comp_arrowsMap`: a morphism of
  groupoids in algebraic spaces commutes with the inversion of arrows.  The structure of a
  morphism of groupoids carries no such field, so this is proved from uniqueness of inverses of
  generalized arrows.
* `AlgebraicGeometry.Space.isIso_groupoidSourceBaseChange_app` and
  `AlgebraicGeometry.Space.isIso_groupoidTargetBaseChange_app`: the two base change maps are
  isomorphisms at a quasi-coherent module.
* `AlgebraicGeometry.Space.isIso_groupoidModulePushforwardTransition`: the transition morphism
  of the direct image is an isomorphism.
* `AlgebraicGeometry.Space.groupoidModulePushforwardTransition_naturality`: it is natural in the
  quasi-coherent module.

## Implementation notes

Every morphism below is written with the base change map in the spelling of
`AlgebraicGeometry.Space.moduleBaseChangeApp`, and the transition morphism is the general
`AlgebraicGeometry.Space.baseChangeTransition` applied to the data of the morphism of groupoids,
so that a consumer meets it as an instance of a general declaration and never has to identify
the composite and the uncomposed spellings of the same module, an identification the kernel can
only make by unfolding `AlgebraicGeometry.Space.modulePullback`.

## References

* [Stacks Project, Tag 0GPM](https://stacks.math.columbia.edu/tag/0GPM)
* [Stacks Project, Tag 09VH](https://stacks.math.columbia.edu/tag/09VH)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS A}

namespace GroupoidInAlgebraicSpaces

/-- **A morphism of groupoids in algebraic spaces commutes with composition of generalized
arrows.**  At every point of every test object this is the compatibility of the morphism with
the composition laws of the two evaluated groupoids. -/
theorem Hom.groupoidCompose_comp_arrowsMap (φ : Hom G G')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ G.arrows.obj)
    (w : a ≫ G.source.hom = b ≫ G.target.hom)
    (w' : (a ≫ φ.arrowsMap.hom) ≫ G'.source.hom =
      (b ≫ φ.arrowsMap.hom) ≫ G'.target.hom) :
    groupoidCompose G a b w ≫ φ.arrowsMap.hom =
      groupoidCompose G' (a ≫ φ.arrowsMap.hom) (b ≫ φ.arrowsMap.hom) w' := by
  ext V t
  have hw : G.source.hom.app V (a.app V t) = G.target.hom.app V (b.app V t) :=
    congrArg (fun k => (k.app V) t) w
  show φ.arrowsMap.hom.app V ((groupoidCompose G a b w).app V t) =
    (groupoidCompose G' (a ≫ φ.arrowsMap.hom) (b ≫ φ.arrowsMap.hom) w').app V t
  rw [groupoidCompose_eval G a b w V t,
    groupoidCompose_eval G' (a ≫ φ.arrowsMap.hom) (b ≫ φ.arrowsMap.hom) w' V t]
  exact (φ.toGroupoidHom.map_comp V (a.app V t) (b.app V t) hw).symm

/-- A variant of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.groupoidCompose_comp_arrowsMap` whose two
image arrows are given separately, together with equations identifying them. -/
theorem Hom.groupoidCompose_comp_arrowsMap' (φ : Hom G G')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ G.arrows.obj)
    (w : a ≫ G.source.hom = b ≫ G.target.hom) (a' b' : T ⟶ G'.arrows.obj)
    (ha : a ≫ φ.arrowsMap.hom = a') (hb : b ≫ φ.arrowsMap.hom = b')
    (w' : a' ≫ G'.source.hom = b' ≫ G'.target.hom) :
    groupoidCompose G a b w ≫ φ.arrowsMap.hom = groupoidCompose G' a' b' w' := by
  subst ha
  subst hb
  exact Hom.groupoidCompose_comp_arrowsMap φ a b w w'

/-- **Uniqueness of inverses of generalized arrows.**  If a generalized arrow `b` composed
before `a` gives the identity at the target of `a`, then `b` is the inverse of `a`.  This is the
usual argument: `b` equals the identity at its target composed with `b`, which is the inverse of
`a` composed with `a` and then with `b`, and associativity collapses the last two factors. -/
theorem groupoidCompose_eq_inverse (G : GroupoidInAlgebraicSpaces B S hS A)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ G.arrows.obj)
    (w : a ≫ G.source.hom = b ≫ G.target.hom)
    (h : groupoidCompose G a b w = identityAfterTarget G a) :
    b = a ≫ groupoidInverse G := by
  have wIA : (a ≫ groupoidInverse G) ≫ G.source.hom = a ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  have hIAT : identityAfterTarget G b = identityAfterSource G a := by
    simp only [identityAfterTarget, identityAfterSource, ← Category.assoc, w]
  have hinvR : groupoidCompose G (a ≫ groupoidInverse G) a wIA = identityAfterSource G a :=
    groupoidCompose_inverseRight G a
  have k0 : identityAfterSource G (a ≫ groupoidInverse G) = identityAfterTarget G a := by
    simp only [identityAfterSource, identityAfterTarget, Category.assoc]
    rw [← Category.assoc (groupoidInverse G) G.source.hom, groupoidInverse_source]
  have W2 : identityAfterSource G a ≫ G.source.hom = b ≫ G.target.hom := by
    rw [identityAfterSource, Category.assoc, Category.assoc,
      identityArrow_hom_comp_source, Category.comp_id]
    exact w
  have W3 : groupoidCompose G (a ≫ groupoidInverse G) a wIA ≫ G.source.hom =
      b ≫ G.target.hom := by
    rw [hinvR]; exact W2
  have WR : (a ≫ groupoidInverse G) ≫ G.source.hom =
      groupoidCompose G a b w ≫ G.target.hom := by
    rw [groupoidCompose_target, wIA]
  calc b = groupoidCompose G (identityAfterTarget G b) b
            (identityAfterTarget_composable G b) :=
        (groupoidCompose_leftIdentity G b).symm
    _ = groupoidCompose G (groupoidCompose G (a ≫ groupoidInverse G) a wIA) b W3 :=
        groupoidCompose_congr G _ _ (hIAT.trans hinvR.symm) rfl
    _ = groupoidCompose G (a ≫ groupoidInverse G) (groupoidCompose G a b w) WR :=
        groupoidCompose_assoc G (a ≫ groupoidInverse G) a b wIA w W3 WR
    _ = groupoidCompose G (a ≫ groupoidInverse G)
            (identityAfterSource G (a ≫ groupoidInverse G))
            (identityAfterSource_composable G (a ≫ groupoidInverse G)) :=
        groupoidCompose_congr G _ _ rfl (h.trans k0.symm)
    _ = a ≫ groupoidInverse G := groupoidCompose_rightIdentity G _

/-- **A morphism of groupoids in algebraic spaces commutes with the inversion of arrows**, on
underlying presheaves.  The image of the inverse of an arrow is an inverse of its image, since
the morphism commutes with composition and with the unit, and inverses are unique. -/
theorem Hom.groupoidInverse_comp_arrowsMap (φ : Hom G G') :
    groupoidInverse G ≫ φ.arrowsMap.hom = φ.arrowsMap.hom ≫ groupoidInverse G' := by
  have hsource : φ.arrowsMap.hom ≫ G'.source.hom =
      G.source.hom ≫ φ.objectsMap.hom :=
    congrArg (fun ψ => ψ.hom) φ.arrowsMap_comp_source
  have htarget : φ.arrowsMap.hom ≫ G'.target.hom =
      G.target.hom ≫ φ.objectsMap.hom :=
    congrArg (fun ψ => ψ.hom) φ.arrowsMap_comp_target
  have hunit : (identityArrow G).hom ≫ φ.arrowsMap.hom =
      φ.objectsMap.hom ≫ (identityArrow G').hom :=
    congrArg (fun ψ => ψ.hom) φ.identityArrow_comp_arrowsMap
  have w₀ : (𝟙 G.arrows.obj) ≫ G.source.hom = groupoidInverse G ≫ G.target.hom := by
    rw [Category.id_comp, groupoidInverse_target]
  have w' : φ.arrowsMap.hom ≫ G'.source.hom =
      (groupoidInverse G ≫ φ.arrowsMap.hom) ≫ G'.target.hom := by
    rw [hsource, Category.assoc, htarget, ← Category.assoc, groupoidInverse_target]
  have hleft : groupoidCompose G (𝟙 G.arrows.obj) (groupoidInverse G) w₀ =
      G.target.hom ≫ (identityArrow G).hom := by
    simpa only [identityAfterTarget, Category.id_comp] using
      groupoidCompose_inverseLeft G (𝟙 G.arrows.obj)
  have key : groupoidCompose G' (φ.arrowsMap.hom) (groupoidInverse G ≫ φ.arrowsMap.hom) w' =
      identityAfterTarget G' (φ.arrowsMap.hom) := by
    rw [← Hom.groupoidCompose_comp_arrowsMap' φ (𝟙 G.arrows.obj) (groupoidInverse G) w₀
      (φ.arrowsMap.hom) (groupoidInverse G ≫ φ.arrowsMap.hom) (Category.id_comp _) rfl w',
      hleft, identityAfterTarget, Category.assoc, hunit, ← Category.assoc, ← htarget,
      Category.assoc]
  exact groupoidCompose_eq_inverse G' (φ.arrowsMap.hom)
    (groupoidInverse G ≫ φ.arrowsMap.hom) w' key

/-- **A morphism of groupoids in algebraic spaces commutes with the inversion of arrows.** -/
theorem Hom.inverseArrow_comp_arrowsMap (φ : Hom G G') :
    inverseArrow G ≫ φ.arrowsMap = φ.arrowsMap ≫ inverseArrow G' :=
  ObjectProperty.hom_ext _ (Hom.groupoidInverse_comp_arrowsMap φ)

/-- **The inversion of arrows is an involution**, again by uniqueness of inverses: an arrow is
an inverse of its inverse. -/
theorem inverseArrow_comp_inverseArrow (G : GroupoidInAlgebraicSpaces B S hS A) :
    inverseArrow G ≫ inverseArrow G = 𝟙 G.arrows := by
  refine ObjectProperty.hom_ext _ ?_
  have w₀ : groupoidInverse G ≫ G.source.hom = (𝟙 G.arrows.obj) ≫ G.target.hom := by
    rw [Category.id_comp, groupoidInverse_source]
  have key : groupoidCompose G (groupoidInverse G) (𝟙 G.arrows.obj) w₀ =
      identityAfterTarget G (groupoidInverse G) := by
    rw [identityAfterTarget, ← Category.assoc, groupoidInverse_target]
    simpa only [identityAfterSource, Category.id_comp, Category.comp_id] using
      groupoidCompose_inverseRight G (𝟙 G.arrows.obj)
  have h := groupoidCompose_eq_inverse G (groupoidInverse G) (𝟙 G.arrows.obj) w₀ key
  exact h.symm

/-- The inversion of arrows of a groupoid in algebraic spaces is an isomorphism. -/
instance isIso_inverseArrow (G : GroupoidInAlgebraicSpaces B S hS A) :
    IsIso (inverseArrow G) :=
  ⟨inverseArrow G, inverseArrow_comp_inverseArrow G, inverseArrow_comp_inverseArrow G⟩

/-- The square formed by the inversion of arrows, the source and the target morphisms and the
identity of the space of objects is cartesian:  the inversion is an isomorphism exchanging the
source and the target. -/
theorem isPullback_inverseArrow_source_target (G : GroupoidInAlgebraicSpaces B S hS A) :
    IsPullback (inverseArrow G) G.source G.target (𝟙 G.objects) :=
  IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, inverseArrow_comp_target]⟩

/-- The square formed by the inversion of arrows, the target and the source morphisms and the
identity of the space of objects is cartesian. -/
theorem isPullback_inverseArrow_target_source (G : GroupoidInAlgebraicSpaces B S hS A) :
    IsPullback (inverseArrow G) G.target G.source (𝟙 G.objects) :=
  IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, inverseArrow_comp_source]⟩

/-- **The square over the source morphisms of a morphism of groupoids in algebraic spaces is
cartesian as soon as the square over the target morphisms is.**  This is the step of the proof
of Stacks 0GPM which says that the analogous `s`-square is cartesian:  the `s`-square is the
`t`-square pasted between the two cartesian squares of the inversions of arrows, which exchange
source and target. -/
theorem Hom.isPullback_arrowsMap_source (φ : Hom G G')
    (h : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap) :
    IsPullback φ.arrowsMap G.source G'.source φ.objectsMap := by
  have key := ((isPullback_inverseArrow_source_target G).paste_horiz h).paste_horiz
    (isPullback_inverseArrow_target_source G')
  have e₁ : (inverseArrow G ≫ φ.arrowsMap) ≫ inverseArrow G' = φ.arrowsMap := by
    rw [Hom.inverseArrow_comp_arrowsMap φ, Category.assoc, inverseArrow_comp_inverseArrow,
      Category.comp_id]
  have e₂ : (𝟙 G.objects ≫ φ.objectsMap) ≫ 𝟙 G'.objects = φ.objectsMap := by
    rw [Category.id_comp, Category.comp_id]
  rw [e₁, e₂] at key
  exact key

end GroupoidInAlgebraicSpaces

namespace Space

open GroupoidInAlgebraicSpaces

variable (B S hS)

section BaseChangeApp

variable {B S hS} {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- The base change map `g^*f_*ℱ ⟶ f'_*(g')^*ℱ` of
`AlgebraicGeometry.Space.moduleBaseChangeMap` at a single module, with its type written with
the inverse and direct images applied one after the other rather than as a composite functor. -/
def moduleBaseChangeApp {g : Y' ⟶ Y} {g' : X' ⟶ X} (comm : g' ≫ f = f' ≫ g)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F) ⟶
      (modulePushforward B S hS f').obj ((modulePullback B S hS g').obj F) :=
  (moduleBaseChangeMap f g f' g' comm).app F

/-- `AlgebraicGeometry.Space.moduleBaseChangeApp` is the component of the base change map. -/
theorem moduleBaseChangeApp_eq {g : Y' ⟶ Y} {g' : X' ⟶ X} (comm : g' ≫ f = f' ≫ g)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleBaseChangeApp f f' comm F = (moduleBaseChangeMap f g f' g' comm).app F :=
  rfl

/-- The base change map at a module is natural in the module. -/
@[reassoc]
theorem moduleBaseChangeApp_naturality {g : Y' ⟶ Y} {g' : X' ⟶ X} (comm : g' ≫ f = f' ≫ g)
    {F N : Modules.{u, u} B S hS X.1 X.2} (ψ : F ⟶ N) :
    (modulePullback B S hS g).map ((modulePushforward B S hS f).map ψ) ≫
        moduleBaseChangeApp f f' comm N =
      moduleBaseChangeApp f f' comm F ≫
        (modulePushforward B S hS f').map ((modulePullback B S hS g').map ψ) :=
  (moduleBaseChangeMap f g f' g' comm).naturality ψ

variable {g h : Y' ⟶ Y} {g' h' : X' ⟶ X} (wg : g' ≫ f = f' ≫ g)

/-- **The transport of a morphism `g'^*ℱ ⟶ h'^*ℱ` through two base change maps.**  For two
commutative squares over `f` and `f'`, with horizontal morphisms `g, g'` and `h, h'`, and an
isomorphism `e` inverting the base change map of the second square at `ℱ`, the direct image of
`β : g'^*ℱ ⟶ h'^*ℱ` read as a morphism `g^*f_*ℱ ⟶ h^*f_*ℱ`. -/
def baseChangeTransition (F : Modules.{u, u} B S hS X.1 X.2)
    (β : (modulePullback B S hS g').obj F ⟶ (modulePullback B S hS h').obj F)
    (e : (modulePullback B S hS h).obj ((modulePushforward B S hS f).obj F) ≅
      (modulePushforward B S hS f').obj ((modulePullback B S hS h').obj F)) :
    (modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F) ⟶
      (modulePullback B S hS h).obj ((modulePushforward B S hS f).obj F) :=
  moduleBaseChangeApp f f' wg F ≫ (modulePushforward B S hS f').map β ≫ e.inv

/-- **The defining property of `AlgebraicGeometry.Space.baseChangeTransition`**: followed by the
isomorphism `e` it is the direct image of the given morphism after the first base change map. -/
@[reassoc]
theorem baseChangeTransition_comp (F : Modules.{u, u} B S hS X.1 X.2)
    (β : (modulePullback B S hS g').obj F ⟶ (modulePullback B S hS h').obj F)
    (e : (modulePullback B S hS h).obj ((modulePushforward B S hS f).obj F) ≅
      (modulePushforward B S hS f').obj ((modulePullback B S hS h').obj F)) :
    baseChangeTransition f f' wg F β e ≫ e.hom =
      moduleBaseChangeApp f f' wg F ≫ (modulePushforward B S hS f').map β := by
  rw [baseChangeTransition, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `AlgebraicGeometry.Space.baseChangeTransition` is natural in the module: a morphism of
modules intertwining two morphisms `β` and `β'` intertwines their transports, as soon as the
two isomorphisms are the base change map of the second square. -/
theorem baseChangeTransition_naturality (wh : h' ≫ f = f' ≫ h)
    {F N : Modules.{u, u} B S hS X.1 X.2}
    (β : (modulePullback B S hS g').obj F ⟶ (modulePullback B S hS h').obj F)
    (β' : (modulePullback B S hS g').obj N ⟶ (modulePullback B S hS h').obj N)
    (e : (modulePullback B S hS h).obj ((modulePushforward B S hS f).obj F) ≅
      (modulePushforward B S hS f').obj ((modulePullback B S hS h').obj F))
    (e' : (modulePullback B S hS h).obj ((modulePushforward B S hS f).obj N) ≅
      (modulePushforward B S hS f').obj ((modulePullback B S hS h').obj N))
    (he : e.hom = moduleBaseChangeApp f f' wh F) (he' : e'.hom = moduleBaseChangeApp f f' wh N)
    (ψ : F ⟶ N)
    (hψ : β ≫ (modulePullback B S hS h').map ψ = (modulePullback B S hS g').map ψ ≫ β') :
    baseChangeTransition f f' wg F β e ≫
        (modulePullback B S hS h).map ((modulePushforward B S hS f).map ψ) =
      (modulePullback B S hS g).map ((modulePushforward B S hS f).map ψ) ≫
        baseChangeTransition f f' wg N β' e' := by
  rw [← Iso.cancel_iso_hom_right _ _ e', Category.assoc, Category.assoc,
    baseChangeTransition_comp, he',
    moduleBaseChangeApp_naturality, ← he, baseChangeTransition_comp_assoc, ← Functor.map_comp,
    hψ, Functor.map_comp, moduleBaseChangeApp_naturality_assoc]

end BaseChangeApp

section BaseChange

variable (φ : Hom G G')

/-- At a quasi-coherent module the base change map of the square over the target morphisms is
an isomorphism:  that square is cartesian by hypothesis and `t'` is flat. -/
theorem isIso_groupoidTargetBaseChange_app (hqc : IsQuasiCompact B S hS φ.objectsMap.hom)
    (hqs : IsQuasiSeparated B S hS φ.objectsMap.hom)
    (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap)
    (htflat : IsFlat B S hS G'.target.hom)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite) :
    IsIso (moduleBaseChangeApp φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm F) :=
  flatBaseChangeZero B S hS φ.objectsMap hqc hqs G'.target φ.arrowsMap G.target
    φ.arrowsMap_comp_target.symm hpb.flip htflat F hF

/-- At a quasi-coherent module the base change map of the square over the source morphisms is
an isomorphism:  that square is cartesian by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_arrowsMap_source` and `s'` is
flat. -/
theorem isIso_groupoidSourceBaseChange_app (hqc : IsQuasiCompact B S hS φ.objectsMap.hom)
    (hqs : IsQuasiSeparated B S hS φ.objectsMap.hom)
    (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap)
    (hsflat : IsFlat B S hS G'.source.hom)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite) :
    IsIso (moduleBaseChangeApp φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_source.symm F) :=
  flatBaseChangeZero B S hS φ.objectsMap hqc hqs G'.source φ.arrowsMap G.source
    φ.arrowsMap_comp_source.symm (φ.isPullback_arrowsMap_source hpb).flip hsflat F hF

end BaseChange

section Descent

variable (φ : Hom G G')
  (hqc : IsQuasiCompact B S hS φ.objectsMap.hom)
  (hqs : IsQuasiSeparated B S hS φ.objectsMap.hom)
  (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap)
  (hsflat : IsFlat B S hS G'.source.hom)

/-- **The base change isomorphism `(s')^*f_*ℱ ≅ f_*s^*ℱ`** of the square of a morphism of
groupoids over the source morphisms, at a quasi-coherent module. -/
def groupoidSourceBaseChangeIso (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (hF : F.IsQuasicoherentOnSite) :
    (modulePullback B S hS G'.source).obj ((modulePushforward B S hS φ.objectsMap).obj F) ≅
      (modulePushforward B S hS φ.arrowsMap).obj ((modulePullback B S hS G.source).obj F) :=
  @asIso _ _ _ _ (moduleBaseChangeApp φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_source.symm F)
    (isIso_groupoidSourceBaseChange_app B S hS φ hqc hqs hpb hsflat F hF)

/-- The base change isomorphism of the source square is the base change map. -/
theorem groupoidSourceBaseChangeIso_hom (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (hF : F.IsQuasicoherentOnSite) :
    (groupoidSourceBaseChangeIso B S hS φ hqc hqs hpb hsflat F hF).hom =
      moduleBaseChangeApp φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_source.symm F :=
  @asIso_hom _ _ _ _ _ (isIso_groupoidSourceBaseChange_app B S hS φ hqc hqs hpb hsflat F hF)

/-- **The transition morphism `f_*α` of the direct image of a quasi-coherent module on a
groupoid in algebraic spaces.**  The direct image along the map on arrows of the transition
morphism `α`, conjugated by the base change isomorphisms of the squares over the target and the
source morphisms:  it is a morphism `(t')^*f_*ℱ ⟶ (s')^*f_*ℱ`, and not merely a morphism of the
two direct images over the arrow space, exactly because the base change map of the source square
is invertible. -/
def groupoidModulePushforwardTransition
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F) :
    (modulePullback B S hS G'.target).obj ((modulePushforward B S hS φ.objectsMap).obj F) ⟶
      (modulePullback B S hS G'.source).obj ((modulePushforward B S hS φ.objectsMap).obj F) :=
  baseChangeTransition φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm F α
    (groupoidSourceBaseChangeIso B S hS φ hqc hqs hpb hsflat F hF)

/-- The transition morphism of the direct image is the transport of the given transition
morphism through the two base change maps.  This is its definition, read as an equation. -/
theorem groupoidModulePushforwardTransition_eq
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F) :
    groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat F hF α =
      baseChangeTransition φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm F α
        (groupoidSourceBaseChangeIso B S hS φ hqc hqs hpb hsflat F hF) :=
  rfl

/-- **The defining property of the transition morphism of the direct image**:  composed with the
base change map of the source square it is the direct image of the given transition morphism
after the base change map of the target square. -/
theorem groupoidModulePushforwardTransition_comp_baseChange
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F) :
    groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat F hF α ≫
        moduleBaseChangeApp φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_source.symm F =
      moduleBaseChangeApp φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm F ≫
        (modulePushforward B S hS φ.arrowsMap).map α := by
  rw [groupoidModulePushforwardTransition_eq,
    ← groupoidSourceBaseChangeIso_hom B S hS φ hqc hqs hpb hsflat F hF]
  exact baseChangeTransition_comp φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm F α
    (groupoidSourceBaseChangeIso B S hS φ hqc hqs hpb hsflat F hF)

/-- **The transition morphism of the direct image is an isomorphism** as soon as the given
transition morphism is:  it is a composite of three isomorphisms.  For a quasi-coherent module
on a groupoid in algebraic spaces the given transition morphism is invertible by
**Stacks 077W**. -/
theorem isIso_groupoidModulePushforwardTransition (htflat : IsFlat B S hS G'.target.hom)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    (hα : IsIso α) :
    IsIso (groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat F hF α) := by
  have := isIso_groupoidTargetBaseChange_app B S hS φ hqc hqs hpb htflat F hF
  have := hα
  rw [groupoidModulePushforwardTransition_eq, baseChangeTransition]
  infer_instance

/-- **The transition morphism of the direct image is natural in the module.**  A morphism of
modules on the space of objects which intertwines two transition morphisms intertwines their
direct images;  this is the compatibility condition required of a morphism of quasi-coherent
modules on the target groupoid. -/
theorem groupoidModulePushforwardTransition_naturality
    (F N : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    (β : (modulePullback B S hS G.target).obj N ⟶ (modulePullback B S hS G.source).obj N)
    (ψ : F ⟶ N)
    (hψ : α ≫ (modulePullback B S hS G.source).map ψ =
      (modulePullback B S hS G.target).map ψ ≫ β) :
    groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat F hF α ≫
        (modulePullback B S hS G'.source).map
          ((modulePushforward B S hS φ.objectsMap).map ψ) =
      (modulePullback B S hS G'.target).map
          ((modulePushforward B S hS φ.objectsMap).map ψ) ≫
        groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat N hN β := by
  rw [groupoidModulePushforwardTransition_eq, groupoidModulePushforwardTransition_eq]
  exact baseChangeTransition_naturality φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm
    φ.arrowsMap_comp_source.symm α β
    (groupoidSourceBaseChangeIso B S hS φ hqc hqs hpb hsflat F hF)
    (groupoidSourceBaseChangeIso B S hS φ hqc hqs hpb hsflat N hN)
    (groupoidSourceBaseChangeIso_hom B S hS φ hqc hqs hpb hsflat F hF)
    (groupoidSourceBaseChangeIso_hom B S hS φ hqc hqs hpb hsflat N hN) ψ hψ

end Descent

end Space

end AlgebraicGeometry

end

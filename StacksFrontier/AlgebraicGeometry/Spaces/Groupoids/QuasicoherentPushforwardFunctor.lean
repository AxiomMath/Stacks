module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidQuasicoherentPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangePaste
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image functor on quasi-coherent modules on a groupoid in algebraic spaces

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over `A` with `f : U ⟶ U'` quasi-compact and quasi-separated, with the square formed by
`R ⟶ R'` over `t`, `t'` and `U ⟶ U'` cartesian, and with `s'` flat.  The transition morphism
`f_*α` of `AlgebraicGeometry.Space.groupoidModulePushforwardTransition` satisfies the cocycle and
the unit law of Stacks 0441, and the direct image `(ℱ, α) ↦ (f_*ℱ, f_*α)` is a functor between the
categories of quasi-coherent modules on the two groupoids, the functor of **Stacks 0GPM**.

## Main results

* `AlgebraicGeometry.Space.modulePullbackReindex_baseChangeTransition`: the reindexing law for
  a transition morphism transported through two base change maps.
* `AlgebraicGeometry.Space.baseChangeTransition_cocycle` and
  `AlgebraicGeometry.Space.baseChangeTransition_unit`: a cocycle law and a unit law transport
  through two base change maps.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_comp_source_compPairsMap`: the
  rectangle formed by the composition laws and the source morphisms is cartesian.
* `AlgebraicGeometry.Space.groupoidModulePushforwardTransition_cocycle` and
  `AlgebraicGeometry.Space.groupoidModulePushforwardTransition_unit`: **the cocycle and the
  unit law for `f_*α`**.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPushforwardObj`: the direct image
  `(f_*ℱ, f_*α)` of a quasi-coherent module, quasi-coherent by Stacks 03M9.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPushforward`: **the direct image functor**
  `QCoh(U, R, s, t, c) ⥤ QCoh(U', R', s', t', c')`.

## Implementation notes

Every identity is proved for variable squares and instantiated once at the groupoid data, so that
no proof has to identify the composite and the uncomposed spellings of an inverse image, an
identification the kernel can only make by unfolding `AlgebraicGeometry.Space.modulePullback`.
For the same reason the morphisms of quasi-coherent modules are built with
`AlgebraicGeometry.Space.QuasicoherentModule.homMk`.

## References

* [Stacks Project, Tag 0GPM](https://stacks.math.columbia.edu/tag/0GPM)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans transportNatTrans_app)


universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section BaseChange

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- **The base change map is compatible with equalities of its two horizontal morphisms**:
replacing them by equal ones conjugates it by the canonical identifications of the inverse
images along equal morphisms. -/
@[reassoc]
theorem pullbackTransport_comp_moduleBaseChangeApp {g₁ g₂ : Y' ⟶ Y} {g₁' g₂' : X' ⟶ X}
    (p : g₁ = g₂) (p' : g₁' = g₂') (w₁ : g₁' ≫ f = f' ≫ g₁) (w₂ : g₂' ≫ f = f' ≫ g₂)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    pullbackTransport ((modulePushforward B S hS f).obj F) p ≫ moduleBaseChangeApp f f' w₂ F =
      moduleBaseChangeApp f f' w₁ F ≫
        (modulePushforward B S hS f').map (pullbackTransport F p') := by
  subst p p'
  simp [pullbackTransport]

/-- **The pasting law for the base change map**, in the spelling of
`AlgebraicGeometry.Space.moduleBaseChangeApp`: the base change map of a rectangle obtained by
stacking a square with horizontal morphisms `k, k'` under a square with horizontal morphisms
`g, g'` is the inverse image along `k` of the base change map of the second square followed by
the base change map of the first, read through the comparisons of Stacks 03LU for the two
composite horizontal morphisms. -/
theorem moduleBaseChangeApp_paste {g : Y' ⟶ Y} {g' : X' ⟶ X} (w₁ : g' ≫ f = f' ≫ g)
    {W W' : AlgebraicSpaces B S hS} (k : W ⟶ Y') (q : W' ⟶ W) (k' : W' ⟶ X')
    (w₂ : k' ≫ f' = q ≫ k) (w : (k' ≫ g') ≫ f = q ≫ (k ≫ g))
    (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleBaseChangeApp f q w F =
      (modulePullbackCompIso B S hS k g).inv.app ((modulePushforward B S hS f).obj F) ≫
        (modulePullback B S hS k).map (moduleBaseChangeApp f f' w₁ F) ≫
        moduleBaseChangeApp f' q w₂ ((modulePullback B S hS g').obj F) ≫
        (modulePushforward B S hS q).map ((modulePullbackCompIso B S hS k' g').hom.app F) := by
  simp only [moduleBaseChangeApp]
  rw [moduleBaseChangeMap_paste f g f' g' k q k' w₁ w₂ w F]

/-- **Reindexing a transition morphism built from two base change maps.**  Let `α : g'^*ℱ ⟶
h'^*ℱ` be a morphism of `𝒪_{X'}`-modules for two commutative squares over `f` and `f'` with
horizontal morphisms `g, g'` and `h, h'`, and let `k : W ⟶ Y'` lift to `k' : W' ⟶ X'` over
`q : W' ⟶ W`.  Then the reindexing along `k` of the transport
`AlgebraicGeometry.Space.baseChangeTransition` of `α` is, against the base change maps of the
two rectangles obtained by stacking the square of `k` under the squares of `g` and `h`, the
direct image along `q` of the reindexing of `α` along `k'`. -/
@[reassoc]
theorem modulePullbackReindex_baseChangeTransition {g h : Y' ⟶ Y} {g' h' : X' ⟶ X}
    (wg : g' ≫ f = f' ≫ g) (wh : h' ≫ f = f' ≫ h) (F : Modules.{u, u} B S hS X.1 X.2)
    (α : (modulePullback B S hS g').obj F ⟶ (modulePullback B S hS h').obj F)
    (e : (modulePullback B S hS h).obj ((modulePushforward B S hS f).obj F) ≅
      (modulePushforward B S hS f').obj ((modulePullback B S hS h').obj F))
    (he : e.hom = moduleBaseChangeApp f f' wh F)
    {W W' : AlgebraicSpaces B S hS} (k : W ⟶ Y') (q : W' ⟶ W) (k' : W' ⟶ X')
    (wk : k' ≫ f' = q ≫ k) (wrg : (k' ≫ g') ≫ f = q ≫ (k ≫ g))
    (wrh : (k' ≫ h') ≫ f = q ≫ (k ≫ h)) :
    modulePullbackReindex k (baseChangeTransition f f' wg F α e) ≫
        moduleBaseChangeApp f q wrh F =
      moduleBaseChangeApp f q wrg F ≫
        (modulePushforward B S hS q).map (modulePullbackReindex k' α) := by
  have hnat := moduleBaseChangeApp_naturality f' q wk α
  have h1 : (modulePullback B S hS k).map (baseChangeTransition f f' wg F α e) ≫
      (modulePullback B S hS k).map e.hom =
      (modulePullback B S hS k).map (moduleBaseChangeApp f f' wg F) ≫
        (modulePullback B S hS k).map ((modulePushforward B S hS f').map α) := by
    rw [← Functor.map_comp, baseChangeTransition_comp, Functor.map_comp]
  have h2 : (modulePushforward B S hS q).map ((modulePullbackCompIso B S hS k' g').hom.app F) ≫
      (modulePushforward B S hS q).map (modulePullbackReindex k' α) =
      (modulePushforward B S hS q).map ((modulePullback B S hS k').map α) ≫
        (modulePushforward B S hS q).map ((modulePullbackCompIso B S hS k' h').hom.app F) := by
    rw [← Functor.map_comp, ← Functor.map_comp, modulePullbackReindex,
      Iso.hom_inv_id_app_assoc]
  rw [moduleBaseChangeApp_paste f f' wh k q k' wk wrh F,
    moduleBaseChangeApp_paste f f' wg k q k' wk wrg F, ← he, modulePullbackReindex]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, reassoc_of% h1, reassoc_of% hnat, h2]

section Laws

variable {X Y V V' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f₁ : V ⟶ V')
  {t s : V ⟶ X} {t' s' : V' ⟶ Y} (wt : t ≫ f = f₁ ≫ t') (ws : s ≫ f = f₁ ≫ s')
  (F : Modules.{u, u} B S hS X.1 X.2)
  (α : (modulePullback B S hS t).obj F ⟶ (modulePullback B S hS s).obj F)
  (e : (modulePullback B S hS s').obj ((modulePushforward B S hS f).obj F) ≅
    (modulePushforward B S hS f₁).obj ((modulePullback B S hS s).obj F))
  (he : e.hom = moduleBaseChangeApp f f₁ ws F)

include he

/-- **A cocycle law transports through two base change maps.**  If `α : t^*ℱ ⟶ s^*ℱ` satisfies
the cocycle law at a triple `c, p₀, p₁ : P ⟶ V`, then its transport
`AlgebraicGeometry.Space.baseChangeTransition` satisfies the cocycle law at any triple
`c', p₀', p₁' : P' ⟶ V'` lying under it along `q : P ⟶ P'`, as soon as the base change map of
the rectangle formed by `c`, `s` over `c'`, `s'` is a monomorphism at `ℱ`. -/
theorem baseChangeTransition_cocycle {P P' : AlgebraicSpaces B S hS} (q : P ⟶ P')
    (c p₀ p₁ : P ⟶ V) (c' p₀' p₁' : P' ⟶ V')
    (wc : c ≫ f₁ = q ≫ c') (w₀ : p₀ ≫ f₁ = q ≫ p₀') (w₁ : p₁ ≫ f₁ = q ≫ p₁')
    (ht : c ≫ t = p₀ ≫ t) (hm : p₀ ≫ s = p₁ ≫ t) (hs : c ≫ s = p₁ ≫ s)
    (ht' : c' ≫ t' = p₀' ≫ t') (hm' : p₀' ≫ s' = p₁' ≫ t') (hs' : c' ≫ s' = p₁' ≫ s')
    (wcs : (c ≫ s) ≫ f = q ≫ (c' ≫ s')) [Mono (moduleBaseChangeApp f q wcs F)]
    (hcoc : modulePullbackReindex c α =
      pullbackTransport F ht ≫
        (modulePullbackReindex p₀ α ≫ pullbackTransport F hm ≫ modulePullbackReindex p₁ α) ≫
        pullbackTransport F hs.symm) :
    modulePullbackReindex c' (baseChangeTransition f f₁ wt F α e) =
      pullbackTransport ((modulePushforward B S hS f).obj F) ht' ≫
        (modulePullbackReindex p₀' (baseChangeTransition f f₁ wt F α e) ≫
          pullbackTransport ((modulePushforward B S hS f).obj F) hm' ≫
          modulePullbackReindex p₁' (baseChangeTransition f f₁ wt F α e)) ≫
        pullbackTransport ((modulePushforward B S hS f).obj F) hs'.symm := by
  rw [← cancel_mono (moduleBaseChangeApp f q wcs F),
    modulePullbackReindex_baseChangeTransition f f₁ wt ws F α e he c' q c wc
    (pasteBaseComm _ _ _ _ _ _ _ wt wc) wcs]
  simp only [Category.assoc]
  rw [pullbackTransport_comp_moduleBaseChangeApp f q hs'.symm hs.symm
      (pasteBaseComm _ _ _ _ _ _ _ ws w₁) wcs F,
    modulePullbackReindex_baseChangeTransition_assoc f f₁ wt ws F α e he p₁' q p₁ w₁
      (pasteBaseComm _ _ _ _ _ _ _ wt w₁) (pasteBaseComm _ _ _ _ _ _ _ ws w₁),
    pullbackTransport_comp_moduleBaseChangeApp_assoc f q hm' hm
      (pasteBaseComm _ _ _ _ _ _ _ ws w₀) (pasteBaseComm _ _ _ _ _ _ _ wt w₁) F,
    modulePullbackReindex_baseChangeTransition_assoc f f₁ wt ws F α e he p₀' q p₀ w₀
      (pasteBaseComm _ _ _ _ _ _ _ wt w₀) (pasteBaseComm _ _ _ _ _ _ _ ws w₀),
    pullbackTransport_comp_moduleBaseChangeApp_assoc f q ht' ht
      (pasteBaseComm _ _ _ _ _ _ _ wt wc) (pasteBaseComm _ _ _ _ _ _ _ wt w₀) F, hcoc]
  simp only [Functor.map_comp, Category.assoc]

/-- **A unit law transports through two base change maps.**  If `α : t^*ℱ ⟶ s^*ℱ` restricts
along `u : X ⟶ V` to the canonical identification, then its transport
`AlgebraicGeometry.Space.baseChangeTransition` restricts along any `u' : Y ⟶ V'` lying under
`u` along `f` to the canonical identification, as soon as the base change map of the rectangle
formed by `u`, `s` over `u'`, `s'` is a monomorphism at `ℱ`. -/
theorem baseChangeTransition_unit (u : X ⟶ V) (u' : Y ⟶ V') (wu : u ≫ f₁ = f ≫ u')
    (hu : u ≫ t = u ≫ s) (hu' : u' ≫ t' = u' ≫ s')
    (wus : (u ≫ s) ≫ f = f ≫ (u' ≫ s')) [Mono (moduleBaseChangeApp f f wus F)]
    (hunit : modulePullbackReindex u α = pullbackTransport F hu) :
    modulePullbackReindex u' (baseChangeTransition f f₁ wt F α e) =
      pullbackTransport ((modulePushforward B S hS f).obj F) hu' := by
  rw [← cancel_mono (moduleBaseChangeApp f f wus F),
    modulePullbackReindex_baseChangeTransition f f₁ wt ws F α e he u' f u wu
      (pasteBaseComm _ _ _ _ _ _ _ wt wu) wus, hunit,
    pullbackTransport_comp_moduleBaseChangeApp f f hu' hu
      (pasteBaseComm _ _ _ _ _ _ _ wt wu) wus F]

end Laws

end BaseChange

section Adjunction

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- **The adjoint characterization of the base change map**, in the spelling of
`AlgebraicGeometry.Space.moduleBaseChangeApp`: under the adjunction of the vertical morphism
`f'`, the base change map is the comparison of the two composite inverse images around the
square followed by the inverse image along `g'` of the counit of `f^* ⊣ f_*`. -/
theorem homEquiv_symm_moduleBaseChangeApp {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (wg : g' ≫ f = f' ≫ g) (M : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullbackAdjunction B S hS f').homEquiv _ _).symm (moduleBaseChangeApp f f' wg M) =
      ((modulePullbackCompIso B S hS f' g).hom.app ((modulePushforward B S hS f).obj M) ≫
          (transportNatTrans
            (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) wg).symm).app
            ((modulePushforward B S hS f).obj M) ≫
          (modulePullbackCompIso B S hS g' f).inv.app
            ((modulePushforward B S hS f).obj M)) ≫
        (modulePullback B S hS g').map ((modulePullbackAdjunction B S hS f).counit.app M) :=
  moduleBaseChangeMap_adjoint_split' f g f' g' wg M

end Adjunction

section Groupoid

variable {A : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS A}

open GroupoidInAlgebraicSpaces

/-- **The square of a morphism of groupoids over the second projections of the spaces of
composable pairs is cartesian**, as soon as the square over the target morphisms is. -/
theorem _root_.AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_secondArrow_compPairsMap
    (φ : Hom G G') (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap) :
    IsPullback (secondArrow G) φ.compPairsMap φ.arrowsMap (secondArrow G') := by
  have houter := (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).paste_horiz
    (φ.isPullback_arrowsMap_source hpb)
  rw [← φ.compPairsMap_comp_firstArrow, ← φ.arrowsMap_comp_target] at houter
  exact (IsPullback.of_right houter φ.compPairsMap_comp_secondArrow
    (AlgebraicSpaces.isPullback_fiberProduct B S hS G'.source G'.target)).flip

/-- The rectangle formed by the composition laws followed by the source morphisms of a morphism
of groupoids is cartesian as soon as the square over the target morphisms is. -/
theorem _root_.AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_comp_source_compPairsMap
    (φ : Hom G G') (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap) :
    IsPullback (G.comp ≫ G.source) φ.compPairsMap φ.objectsMap (G'.comp ≫ G'.source) := by
  rw [comp_comp_source G, comp_comp_source G']
  exact (φ.isPullback_secondArrow_compPairsMap hpb).paste_horiz
    (φ.isPullback_arrowsMap_source hpb).flip

/-- The composition law of a groupoid in algebraic spaces followed by its source morphism is
flat as soon as the source morphism is. -/
theorem isFlat_comp_comp_source (G : GroupoidInAlgebraicSpaces B S hS A)
    (hsflat : IsFlat B S hS G.source.hom) : IsFlat B S hS (G.comp ≫ G.source).hom := by
  rw [comp_comp_source G]
  exact isFlat_comp B S hS
    (AlgebraicSpaces.fiberProduct B S hS G.source G.target).2 G.arrows.2 G.objects.2
    (secondArrow G).hom G.source.hom
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target) hsflat) hsflat

/-- The base change map of a cartesian square with flat `g` is a monomorphism on a
quasi-coherent module, when the vertical morphism is quasi-compact and quasi-separated. -/
private theorem mono_moduleBaseChangeApp_of_isPullback {X Y V V' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    {g : V' ⟶ Y} {g' : V ⟶ X} {f' : V ⟶ V'} (w : g' ≫ f = f' ≫ g) (hpb : IsPullback g' f' f g)
    (hg : IsFlat B S hS g.hom) (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    Mono (moduleBaseChangeApp f f' w F) :=
  @IsIso.mono_of_iso _ _ _ _ _ (flatBaseChangeZero B S hS f hqc hqs g f' g' w hpb hg F hF)

variable (B S hS)

variable (φ : Hom G G')
  (hqc : IsQuasiCompact B S hS φ.objectsMap.hom)
  (hqs : IsQuasiSeparated B S hS φ.objectsMap.hom)
  (hpb : IsPullback φ.arrowsMap G.target G'.target φ.objectsMap)
  (hsflat : IsFlat B S hS G'.source.hom)

/-- **The cocycle law for the transition morphism of the direct image.**  If the transition
morphism `α` of a quasi-coherent module on `(U, R, s, t, c)` satisfies the cocycle law on the
space of composable pairs of arrows, then so does `f_*α` on the space of composable pairs of
arrows of `(U', R', s', t', c')`. -/
theorem groupoidModulePushforwardTransition_cocycle
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    (hcocycle : groupoidPullbackTransition B S hS G F α G.comp =
      groupoidTransitionComposite B S hS G F α) :
    groupoidPullbackTransition B S hS G' ((modulePushforward B S hS φ.objectsMap).obj F)
        (groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat F hF α) G'.comp =
      groupoidTransitionComposite B S hS G' ((modulePushforward B S hS φ.objectsMap).obj F)
        (groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat F hF α) := by
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex, groupoidTransitionComposite_eq,
    transitionComposite_eq_comp] at hcocycle ⊢
  rw [groupoidModulePushforwardTransition_eq]
  have wcs := pasteBaseComm φ.objectsMap G'.source φ.arrowsMap G.source G'.comp
    φ.compPairsMap G.comp φ.arrowsMap_comp_source.symm φ.comp_comp_arrowsMap
  have := mono_moduleBaseChangeApp_of_isPullback φ.objectsMap hqc hqs wcs
    (φ.isPullback_comp_source_compPairsMap hpb) (isFlat_comp_comp_source G' hsflat) F hF
  exact baseChangeTransition_cocycle φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm
    φ.arrowsMap_comp_source.symm F α _
    (groupoidSourceBaseChangeIso_hom B S hS φ hqc hqs hpb hsflat F hF) φ.compPairsMap
    G.comp (firstArrow G) (secondArrow G) G'.comp (firstArrow G') (secondArrow G')
    φ.comp_comp_arrowsMap φ.compPairsMap_comp_firstArrow.symm
    φ.compPairsMap_comp_secondArrow.symm (comp_comp_target G) (firstArrow_comp_source G)
    (comp_comp_source G) (comp_comp_target G') (firstArrow_comp_source G')
    (comp_comp_source G') wcs hcocycle

/-- The rectangle formed by the unit arrows followed by the source morphisms of a morphism of
groupoids is cartesian. -/
theorem _root_.AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_identityArrow_source
    (φ : Hom G G') :
    IsPullback (identityArrow G ≫ G.source) φ.objectsMap φ.objectsMap
      (identityArrow G' ≫ G'.source) := by
  rw [identityArrow_comp_source, identityArrow_comp_source]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

/-- **The unit law for the transition morphism of the direct image.**  If the transition
morphism `α` of a quasi-coherent module on `(U, R, s, t, c)` restricts along the unit arrow to
the canonical identification, then so does `f_*α` along the unit arrow of
`(U', R', s', t', c')`. -/
theorem groupoidModulePushforwardTransition_unit
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2) (hF : F.IsQuasicoherentOnSite)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    (hunit : groupoidPullbackTransition B S hS G F α (identityArrow G) =
      pullbackTransport F ((identityArrow_comp_target G).trans
        (identityArrow_comp_source G).symm)) :
    groupoidPullbackTransition B S hS G' ((modulePushforward B S hS φ.objectsMap).obj F)
        (groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat F hF α)
        (identityArrow G') =
      pullbackTransport ((modulePushforward B S hS φ.objectsMap).obj F)
        ((identityArrow_comp_target G').trans (identityArrow_comp_source G').symm) := by
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex] at hunit ⊢
  rw [groupoidModulePushforwardTransition_eq]
  have wus := pasteBaseComm φ.objectsMap G'.source φ.arrowsMap G.source (identityArrow G')
    φ.objectsMap (identityArrow G) φ.arrowsMap_comp_source.symm
    φ.identityArrow_comp_arrowsMap
  have hflat : IsFlat B S hS (identityArrow G' ≫ G'.source).hom := by
    rw [identityArrow_comp_source]
    exact isFlat_id B S hS G'.objects.2
  have := mono_moduleBaseChangeApp_of_isPullback φ.objectsMap hqc hqs wus
    φ.isPullback_identityArrow_source hflat F hF
  exact baseChangeTransition_unit φ.objectsMap φ.arrowsMap φ.arrowsMap_comp_target.symm
    φ.arrowsMap_comp_source.symm F α _
    (groupoidSourceBaseChangeIso_hom B S hS φ hqc hqs hpb hsflat F hF) (identityArrow G)
    (identityArrow G') φ.identityArrow_comp_arrowsMap _ _ wus hunit

/-- **The direct image of a quasi-coherent module on `(U, R, s, t, c)`**: the direct image
`f_*ℱ` of the underlying module, quasi-coherent since `f : U ⟶ U'` is quasi-compact and
quasi-separated (Stacks 03M9), together with the transition morphism `f_*α`. -/
def groupoidQuasicoherentPushforwardObj (M : QuasicoherentModule B S hS G) :
    QuasicoherentModule B S hS G' where
  F := ⟨(modulePushforward B S hS φ.objectsMap).obj M.F.obj,
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS φ.objectsMap hqc hqs M.F.obj
      M.F.property⟩
  alpha := groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat M.F.obj M.F.property
    M.alpha
  cocycle := groupoidModulePushforwardTransition_cocycle B S hS φ hqc hqs hpb hsflat M.F.obj
    M.F.property M.alpha M.cocycle
  unit := groupoidModulePushforwardTransition_unit B S hS φ hqc hqs hpb hsflat M.F.obj
    M.F.property M.alpha M.unit

/-- The underlying module of the direct image of a quasi-coherent module on a groupoid in
algebraic spaces is the direct image of its underlying module. -/
@[simp]
theorem groupoidQuasicoherentPushforwardObj_F_obj (M : QuasicoherentModule B S hS G) :
    (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).F.obj =
      (modulePushforward B S hS φ.objectsMap).obj M.F.obj :=
  rfl

/-- **The transition morphism of the direct image, as an equation**: it is `f_*α`. -/
@[simp]
theorem groupoidQuasicoherentPushforwardObj_alpha (M : QuasicoherentModule B S hS G) :
    (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).alpha =
      groupoidModulePushforwardTransition B S hS φ hqc hqs hpb hsflat M.F.obj M.F.property
        M.alpha := by
  simp only [groupoidQuasicoherentPushforwardObj]

/-- **The direct image of a morphism of quasi-coherent modules on the source groupoid**, read as
a morphism of the underlying modules of the two direct images. -/
def groupoidQuasicoherentPushforwardMap {M N : QuasicoherentModule B S hS G} (g : M ⟶ N) :
    (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M).F.obj ⟶
      (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat N).F.obj :=
  (modulePushforward B S hS φ.objectsMap).map g.hom

/-- `AlgebraicGeometry.Space.groupoidQuasicoherentPushforwardMap` is the direct image of the
underlying morphism of modules. -/
theorem groupoidQuasicoherentPushforwardMap_eq {M N : QuasicoherentModule B S hS G}
    (g : M ⟶ N) :
    groupoidQuasicoherentPushforwardMap B S hS φ hqc hqs hpb hsflat g =
      (modulePushforward B S hS φ.objectsMap).map g.hom :=
  rfl

/-- **The direct image of a morphism is compatible with the two transition morphisms**. -/
theorem groupoidQuasicoherentPushforwardMap_compatible {M N : QuasicoherentModule B S hS G}
    (g : M ⟶ N) :
    QuasicoherentModule.Compatible (groupoidQuasicoherentPushforwardMap B S hS φ hqc hqs hpb
      hsflat g) := by
  unfold QuasicoherentModule.Compatible
  rw [groupoidQuasicoherentPushforwardMap_eq, groupoidQuasicoherentPushforwardObj_alpha,
    groupoidQuasicoherentPushforwardObj_alpha]
  exact groupoidModulePushforwardTransition_naturality B S hS φ hqc hqs hpb hsflat M.F.obj
    N.F.obj M.F.property N.F.property M.alpha N.alpha g.hom g.comm

/-- **The direct image of a morphism of quasi-coherent modules on the source groupoid, as a
morphism of quasi-coherent modules on the target groupoid.** -/
def groupoidQuasicoherentPushforwardHom {M N : QuasicoherentModule B S hS G} (g : M ⟶ N) :
    groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M ⟶
      groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat N :=
  QuasicoherentModule.homMk (groupoidQuasicoherentPushforwardMap B S hS φ hqc hqs hpb hsflat g)
    (groupoidQuasicoherentPushforwardMap_compatible B S hS φ hqc hqs hpb hsflat g)

/-- The underlying morphism of modules of the direct image of a morphism is the direct image of
the underlying morphism. -/
@[simp]
theorem groupoidQuasicoherentPushforwardHom_hom {M N : QuasicoherentModule B S hS G}
    (g : M ⟶ N) :
    (groupoidQuasicoherentPushforwardHom B S hS φ hqc hqs hpb hsflat g).hom =
      (modulePushforward B S hS φ.objectsMap).map g.hom :=
  rfl

/-- The direct image of an identity is an identity. -/
theorem groupoidQuasicoherentPushforwardHom_id (M : QuasicoherentModule B S hS G) :
    groupoidQuasicoherentPushforwardHom B S hS φ hqc hqs hpb hsflat (𝟙 M) =
      𝟙 (groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M) := by
  refine QuasicoherentModule.Hom.ext ?_
  rw [groupoidQuasicoherentPushforwardHom_hom, QuasicoherentModule.id_hom,
    QuasicoherentModule.id_hom]
  exact (modulePushforward B S hS φ.objectsMap).map_id M.F.obj

/-- The direct image of a composite is the composite of the direct images. -/
theorem groupoidQuasicoherentPushforwardHom_comp {M N P : QuasicoherentModule B S hS G}
    (g : M ⟶ N) (g' : N ⟶ P) :
    groupoidQuasicoherentPushforwardHom B S hS φ hqc hqs hpb hsflat (g ≫ g') =
      groupoidQuasicoherentPushforwardHom B S hS φ hqc hqs hpb hsflat g ≫
        groupoidQuasicoherentPushforwardHom B S hS φ hqc hqs hpb hsflat g' := by
  refine QuasicoherentModule.Hom.ext ?_
  rw [groupoidQuasicoherentPushforwardHom_hom, QuasicoherentModule.comp_hom,
    QuasicoherentModule.comp_hom, groupoidQuasicoherentPushforwardHom_hom,
    groupoidQuasicoherentPushforwardHom_hom]
  exact (modulePushforward B S hS φ.objectsMap).map_comp g.hom g'.hom

/-- **The direct image functor** `QCoh(U, R, s, t, c) ⥤ QCoh(U', R', s', t', c')` along a
morphism `f` of groupoids in algebraic spaces whose map on objects is quasi-compact and
quasi-separated, whose square over the target morphisms is cartesian and whose source morphism
`s'` is flat: it sends `(ℱ, α)` to `(f_*ℱ, f_*α)` and a morphism to the direct image of the
underlying morphism of modules. -/
def groupoidQuasicoherentPushforward :
    QuasicoherentModule B S hS G ⥤ QuasicoherentModule B S hS G' where
  obj M := groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M
  map g := groupoidQuasicoherentPushforwardHom B S hS φ hqc hqs hpb hsflat g
  map_id M := groupoidQuasicoherentPushforwardHom_id B S hS φ hqc hqs hpb hsflat M
  map_comp g g' := groupoidQuasicoherentPushforwardHom_comp B S hS φ hqc hqs hpb hsflat g g'

/-- The object map of the direct image functor is
`AlgebraicGeometry.Space.groupoidQuasicoherentPushforwardObj`. -/
@[simp]
theorem groupoidQuasicoherentPushforward_obj (M : QuasicoherentModule B S hS G) :
    (groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).obj M =
      groupoidQuasicoherentPushforwardObj B S hS φ hqc hqs hpb hsflat M :=
  rfl

/-- The morphism map of the direct image functor is
`AlgebraicGeometry.Space.groupoidQuasicoherentPushforwardHom`. -/
@[simp]
theorem groupoidQuasicoherentPushforward_map {M N : QuasicoherentModule B S hS G} (g : M ⟶ N) :
    (groupoidQuasicoherentPushforward B S hS φ hqc hqs hpb hsflat).map g =
      groupoidQuasicoherentPushforwardHom B S hS φ hqc hqs hpb hsflat g :=
  rfl

end Groupoid

end AlgebraicGeometry.Space

end

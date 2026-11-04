module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TargetPairsGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidQuasicoherentPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentTransition

/-!
# The inverse image of a quasi-coherent module to the groupoid of pairs with a common target

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let
`f : (R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂) ⟶ (U, R, s, t, c)` be the morphism given by `s` on
objects and by `(r₀, r₁) ↦ r₀⁻¹ ∘ r₁` on arrows.  For a quasi-coherent module `(ℱ, β)` on
`(U, R, s, t, c)` the proof of Stacks 0GPP identifies the inverse image `f^*(ℱ, β) = (s^*ℱ, f^*β)`
with the module `t^*ℱ` endowed with its canonical descent datum relative to `t`: the
isomorphism is `β⁻¹ : s^*ℱ ⟶ t^*ℱ`, and its compatibility with the two transition morphisms is the
cocycle condition of `β` pulled back along `(pr₀, c ∘ (i, 1)) : R ×_{t, U, t} R ⟶ R ×_{s, U, t} R`.

## Main results

* `AlgebraicGeometry.Space.groupoidModulePullbackTransition_targetPairsHom`: **the transition
  morphism of `f^*(ℱ, β)` is `pr₀^*β⁻¹`, the canonical descent datum, and `pr₁^*β`**, in the form
  of the compatibility of `β⁻¹` with the two transition morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- **The cocycle condition of a transition morphism, pulled back to the pairs with a common
target**: for `(r₀, r₁)` with a common target, `β` at `r₁` is `β` at `r₀` followed by `β` at
`r₀⁻¹ ∘ r₁`, read through the canonical identifications of the inverse images.  The three
morphisms `r₀`, `r₀⁻¹ ∘ r₁` and `r₁` are given with equations identifying them, so that a caller
can name them as it pleases. -/
theorem modulePullbackReindex_targetPairs_cocycle
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (β : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    (hcocycle : groupoidPullbackTransition B S hS G F β G.comp =
      groupoidTransitionComposite B S hS G F β)
    (P Q R : (targetPairsGroupoid G).arrows ⟶ G.arrows)
    (hP : ((commonTargetPairsIso G).hom : (targetPairsGroupoid G).arrows ⟶ _) ≫ firstArrow G = P)
    (hQ : ((commonTargetPairsIso G).hom : (targetPairsGroupoid G).arrows ⟶ _) ≫
      secondArrow G = Q)
    (hR : ((commonTargetPairsIso G).hom : (targetPairsGroupoid G).arrows ⟶ _) ≫ G.comp = R)
    (ht : R ≫ G.target = P ≫ G.target) (hm : P ≫ G.source = Q ≫ G.target)
    (hs : R ≫ G.source = Q ≫ G.source) :
    modulePullbackReindex R β =
      pullbackTransport F ht ≫
        (modulePullbackReindex P β ≫ pullbackTransport F hm ≫ modulePullbackReindex Q β) ≫
        pullbackTransport F hs.symm := by
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex, groupoidTransitionComposite_eq,
    transitionComposite_eq_comp] at hcocycle
  exact modulePullbackReindex_cocycle_comp B S hS (W := (targetPairsGroupoid G).arrows) F β
    (firstArrow G) (secondArrow G) G.comp (commonTargetPairsIso G).hom P Q R hP hQ hR
    (ht₀ := comp_comp_target G) (hm₀ := firstArrow_comp_source G)
    (hs₀ := comp_comp_source G) hcocycle ht hm hs

section Abstract

/-! ### The comparison for an abstract inverse-image calculus

The comparison of the transition morphism of the inverse image along the morphism to the groupoid
of pairs with a common target with the canonical descent datum is a formal manipulation of
comparisons of iterated inverse images.  It is carried out here for a *variable* family `P` of
inverse images with comparisons `cmp`, and instantiated below at the inverse image of modules:
for the inverse image of modules the several spellings of one object that the manipulation
produces are identified only by unfolding `AlgebraicGeometry.Space.modulePullback`, which is
expensive, whereas for a variable family the identification is immediate. -/

variable
  (P : ∀ (X Y : AlgebraicSpaces B S hS), (X ⟶ Y) →
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
  (cmp : ∀ (X Y Z : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y ⟶ Z),
    P Y Z g ⋙ P X Y f ≅ P X Z (f ≫ g))

/-- `AlgebraicGeometry.Space.modulePullbackFlatten` for an abstract inverse-image calculus. -/
def absFlatten {X Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z) {a b : X ⟶ Y}
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (P _ _ a).obj ((P _ _ f).obj M) ⟶ (P _ _ b).obj ((P _ _ f).obj M)) :
    (P _ _ (a ≫ f)).obj M ⟶ (P _ _ (b ≫ f)).obj M :=
  (cmp _ _ _ a f).inv.app M ≫ α ≫ (cmp _ _ _ b f).hom.app M

/-- `AlgebraicGeometry.Space.modulePullbackReindex` for an abstract inverse-image calculus. -/
def absReindex {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) {a b : Y ⟶ Z}
    {M : Modules.{u, u} B S hS Z.1 Z.2} (α : (P _ _ a).obj M ⟶ (P _ _ b).obj M) :
    (P _ _ (f ≫ a)).obj M ⟶ (P _ _ (f ≫ b)).obj M :=
  (cmp _ _ _ f a).inv.app M ≫ (P _ _ f).map α ≫ (cmp _ _ _ f b).hom.app M

/-- `AlgebraicGeometry.Space.pullbackTransport` for an abstract inverse-image calculus. -/
def absTransport {T X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    {f g : T ⟶ X} (h : f = g) : (P _ _ f).obj M ⟶ (P _ _ g).obj M :=
  (eqToIso (congrArg (fun k : T ⟶ X => (P _ _ k).obj M) h)).hom

omit G in
/-- **The comparison of a transition morphism with a descent datum, from their flattenings**,
for an abstract inverse-image calculus.  Let `A : a^*s^*ℱ ⟶ b^*s^*ℱ` and
`D : a^*t^*ℱ ⟶ b^*t^*ℱ` be two morphisms and `β : t^*ℱ ⟶ s^*ℱ` an isomorphism with inverse `β'`.
If `A` flattens to `β` reindexed along `f` between two canonical identifications, `D` flattens to
a canonical identification, and the reindexing of `β` along `b` is that along `a` followed by
that along `f`, then `β'` intertwines `A` and `D`. -/
theorem abs_comp_map_inv_eq {V U X : AlgebraicSpaces B S hS} (a b f : V ⟶ U)
    (s t : U ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2)
    (β : (P _ _ t).obj F ⟶ (P _ _ s).obj F) (β' : (P _ _ s).obj F ⟶ (P _ _ t).obj F)
    (hββ' : β ≫ β' = 𝟙 _) (hβ'β : β' ≫ β = 𝟙 _)
    (A : (P _ _ a).obj ((P _ _ s).obj F) ⟶ (P _ _ b).obj ((P _ _ s).obj F))
    (D : (P _ _ a).obj ((P _ _ t).obj F) ⟶ (P _ _ b).obj ((P _ _ t).obj F))
    (hφ : a ≫ t = b ≫ t) (ht : b ≫ t = a ≫ t) (e₁ : a ≫ s = f ≫ t) (e₂ : f ≫ s = b ≫ s)
    (hs : b ≫ s = f ≫ s)
    (hflat : absFlatten P cmp s A =
      absTransport P F e₁ ≫ absReindex P cmp f β ≫ absTransport P F e₂)
    (hcan : absFlatten P cmp t D = absTransport P F hφ)
    (hcoc : absReindex P cmp b β =
      absTransport P F ht ≫
        (absReindex P cmp a β ≫ absTransport P F e₁ ≫ absReindex P cmp f β) ≫
        absTransport P F hs.symm) :
    A ≫ (P _ _ b).map β' = (P _ _ a).map β' ≫ D := by
  have hre : ∀ (c : V ⟶ U) {x y : U ⟶ X} (α : (P _ _ x).obj F ⟶ (P _ _ y).obj F),
      (P _ _ c).map α = (cmp _ _ _ c x).hom.app F ≫ absReindex P cmp c α ≫
        (cmp _ _ _ c y).inv.app F := by
    intros; simp [absReindex]
  have hbβ : (P _ _ b).map β ≫ (P _ _ b).map β' = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hββ', CategoryTheory.Functor.map_id]
  have haβ : (P _ _ a).map β' ≫ (P _ _ a).map β = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hβ'β, CategoryTheory.Functor.map_id]
  have hA : A = (cmp _ _ _ a s).hom.app F ≫
      (absTransport P F e₁ ≫ absReindex P cmp f β ≫ absTransport P F e₂) ≫
      (cmp _ _ _ b s).inv.app F := by
    rw [← hflat]; simp [absFlatten]
  have hD : D = (cmp _ _ _ a t).hom.app F ≫ absTransport P F hφ ≫ (cmp _ _ _ b t).inv.app F := by
    rw [← hcan]; simp [absFlatten]
  have key : A = (P _ _ a).map β' ≫ D ≫ (P _ _ b).map β := by
    rw [hA, hD, hre b β, hcoc]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc, absReindex,
      absTransport, eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      reassoc_of% haβ]
  rw [key]
  simp only [Category.assoc, hbβ, Category.comp_id]

omit G in
/-- `AlgebraicGeometry.Space.abs_comp_map_inv_eq` with the arrows and the transition morphism
given in two typings over two equal spaces, so that every hypothesis can be supplied in the
typing in which it is natively stated: the transition morphism of an inverse image and the
descent datum over `U₁`, the cocycle condition over `U₂`. -/
theorem abs_comp_map_inv_eq₂ {V U₁ U₂ X : AlgebraicSpaces B S hS} (hU : U₁ = U₂)
    (a₁ b₁ : V ⟶ U₁) (s₁ t₁ : U₁ ⟶ X) (a₂ b₂ f : V ⟶ U₂) (s₂ t₂ : U₂ ⟶ X)
    (ha : HEq a₁ a₂) (hb : HEq b₁ b₂) (hsX : HEq s₁ s₂) (htX : HEq t₁ t₂)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (β₂ : (P _ _ t₂).obj F ⟶ (P _ _ s₂).obj F) (β₁ : (P _ _ t₁).obj F ⟶ (P _ _ s₁).obj F)
    (hβ : HEq β₁ β₂) (β' : (P _ _ s₁).obj F ⟶ (P _ _ t₁).obj F)
    (hββ' : β₁ ≫ β' = 𝟙 _) (hβ'β : β' ≫ β₁ = 𝟙 _)
    (A : (P _ _ a₁).obj ((P _ _ s₁).obj F) ⟶ (P _ _ b₁).obj ((P _ _ s₁).obj F))
    (D : (P _ _ a₁).obj ((P _ _ t₁).obj F) ⟶ (P _ _ b₁).obj ((P _ _ t₁).obj F))
    (hφ : a₁ ≫ t₁ = b₁ ≫ t₁) (ht : b₂ ≫ t₂ = a₂ ≫ t₂) (e₁ : a₁ ≫ s₁ = f ≫ t₂)
    (e₂ : f ≫ s₂ = b₁ ≫ s₁) (e₁' : a₂ ≫ s₂ = f ≫ t₂) (hs : b₂ ≫ s₂ = f ≫ s₂)
    (hflat : absFlatten P cmp s₁ A =
      absTransport P F e₁ ≫ absReindex P cmp f β₂ ≫ absTransport P F e₂)
    (hcan : absFlatten P cmp t₁ D = absTransport P F hφ)
    (hcoc : absReindex P cmp b₂ β₂ =
      absTransport P F ht ≫
        (absReindex P cmp a₂ β₂ ≫ absTransport P F e₁' ≫ absReindex P cmp f β₂) ≫
        absTransport P F hs.symm) :
    A ≫ (P _ _ b₁).map β' = (P _ _ a₁).map β' ≫ D := by
  subst hU
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  obtain rfl := eq_of_heq hsX
  obtain rfl := eq_of_heq htX
  obtain rfl := eq_of_heq hβ
  exact abs_comp_map_inv_eq P cmp a₁ b₁ f s₁ t₁ F β₁ β' hββ' hβ'β A D hφ ht e₁ e₂ hs hflat
    hcan hcoc

end Abstract

/-- `AlgebraicGeometry.Space.modulePullbackFlatten` is the flattening of the abstract calculus at
the inverse image of modules. -/
theorem modulePullbackFlatten_eq_absFlatten {X Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    {a b : X ⟶ Y} {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M)) :
    modulePullbackFlatten f α =
      absFlatten (@modulePullback B S hS) (@modulePullbackCompIso B S hS) f α := rfl

/-- `AlgebraicGeometry.Space.modulePullbackReindex` is the reindexing of the abstract calculus at
the inverse image of modules. -/
theorem modulePullbackReindex_eq_absReindex {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {a b : Y ⟶ Z} {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) :
    modulePullbackReindex f α =
      absReindex (@modulePullback B S hS) (@modulePullbackCompIso B S hS) f α := rfl

/-- `AlgebraicGeometry.Space.pullbackTransport` is the transport of the abstract calculus at the
inverse image of modules. -/
theorem pullbackTransport_eq_absTransport {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) {f g : T ⟶ X} (h : f = g) :
    pullbackTransport M h = absTransport (@modulePullback B S hS) M h := rfl

variable (M : QuasicoherentModule B S hS G)

attribute [local instance] QuasicoherentModule.isIso_alpha

/-- The transition morphism `β : t^*ℱ ⟶ s^*ℱ` of a quasi-coherent module on a groupoid in
algebraic spaces, read on the space of objects of the groupoid of pairs with a common target:
there it is a morphism between the inverse images of `ℱ` along the target and along the map on
objects of the morphism to the groupoid. -/
abbrev targetPairsAlpha :
    (@modulePullback B S hS (targetPairsGroupoid G).objects G.objects G.target).obj M.F.obj ⟶
      (modulePullback B S hS (targetPairsHom G).objectsMap).obj M.F.obj :=
  M.alpha

/-- The transition morphism `β`, read on the space of objects of the groupoid of pairs with a
common target, is an isomorphism. -/
instance isIso_targetPairsAlpha : IsIso (targetPairsAlpha G M) :=
  QuasicoherentModule.isIso_alpha M

/-- The inverse `β⁻¹ : s^*ℱ ⟶ t^*ℱ` of the transition morphism, which exists by Stacks 077W,
read on the space of objects of the groupoid of pairs with a common target. -/
abbrev targetPairsAlphaInv :
    (modulePullback B S hS (targetPairsHom G).objectsMap).obj M.F.obj ⟶
      (@modulePullback B S hS (targetPairsGroupoid G).objects G.objects G.target).obj
        M.F.obj :=
  inv (targetPairsAlpha G M)

/-- **The transition morphism of the inverse image of `(ℱ, β)` along
`f : (R, R ×_{t, U, t} R, pr₁, pr₀, pr₀₂) ⟶ (U, R, s, t, c)` is `pr₀^*β⁻¹`, the canonical descent
datum of `t^*ℱ`, and `pr₁^*β`**: the isomorphism `β⁻¹ : s^*ℱ ⟶ t^*ℱ` intertwines `f^*β` with the
canonical descent datum.  This is the cocycle condition of `β`, pulled back to the pairs with a
common target. -/
theorem groupoidModulePullbackTransition_targetPairsHom :
    groupoidModulePullbackTransition B S hS (targetPairsHom G) M.F.obj M.alpha ≫
        (modulePullback B S hS (targetPairsGroupoid G).source).map (targetPairsAlphaInv G M) =
      (modulePullback B S hS (targetPairsGroupoid G).target).map (targetPairsAlphaInv G M) ≫
        spaceBaseDescent B S hS (targetPairsGroupoid G) G.target
          (targetPairsFst_comp_target G) M.F.obj := by
  have ht : ((targetPairsGroupoid G).source : (targetPairsGroupoid G).arrows ⟶ G.arrows) ≫
      G.target = ((targetPairsGroupoid G).target : (targetPairsGroupoid G).arrows ⟶ G.arrows) ≫
        G.target := (targetPairsFst_comp_target G).symm
  have hm : ((targetPairsGroupoid G).target : (targetPairsGroupoid G).arrows ⟶ G.arrows) ≫
      G.source = (targetPairsHom G).arrowsMap ≫ G.target :=
    (targetPairsArrowsMap_comp_target G).symm
  have hs : ((targetPairsGroupoid G).source : (targetPairsGroupoid G).arrows ⟶ G.arrows) ≫
      G.source = (targetPairsHom G).arrowsMap ≫ G.source :=
    (targetPairsArrowsMap_comp_source G).symm
  have hcoc := modulePullbackReindex_targetPairs_cocycle G M.F.obj M.alpha M.cocycle
    (targetPairsGroupoid G).target (targetPairsHom G).arrowsMap (targetPairsGroupoid G).source
    (commonTargetPairsIso_hom_fst G) rfl (commonTargetPairsIso_hom_comp G) ht hm hs
  have hflat := modulePullbackFlatten_groupoidModulePullbackTransition B S hS (targetPairsHom G)
    M.F.obj M.alpha
  have hcan := modulePullbackFlatten_spaceBaseDescent B S hS (targetPairsGroupoid G) G.target
    (targetPairsFst_comp_target G) M.F.obj
  rw [modulePullbackFlatten_eq_absFlatten, modulePullbackReindex_eq_absReindex,
    pullbackTransport_eq_absTransport, pullbackTransport_eq_absTransport] at hflat
  rw [modulePullbackFlatten_eq_absFlatten, pullbackTransport_eq_absTransport] at hcan
  rw [modulePullbackReindex_eq_absReindex, modulePullbackReindex_eq_absReindex,
    modulePullbackReindex_eq_absReindex, pullbackTransport_eq_absTransport,
    pullbackTransport_eq_absTransport, pullbackTransport_eq_absTransport] at hcoc
  exact abs_comp_map_inv_eq₂ (@modulePullback B S hS) (@modulePullbackCompIso B S hS)
    (U₁ := (targetPairsGroupoid G).objects) (U₂ := G.arrows) rfl
    (targetPairsGroupoid G).target (targetPairsGroupoid G).source (targetPairsHom G).objectsMap
    (G.target : (targetPairsGroupoid G).objects ⟶ G.objects)
    ((targetPairsGroupoid G).target : (targetPairsGroupoid G).arrows ⟶ G.arrows)
    ((targetPairsGroupoid G).source : (targetPairsGroupoid G).arrows ⟶ G.arrows)
    (targetPairsHom G).arrowsMap G.source G.target HEq.rfl HEq.rfl HEq.rfl HEq.rfl M.F.obj
    M.alpha (targetPairsAlpha G M) HEq.rfl (targetPairsAlphaInv G M) (IsIso.hom_inv_id _)
    (IsIso.inv_hom_id _) _ _ (targetPairsFst_comp_target G) ht
    (targetPairsHom G).arrowsMap_comp_target.symm (targetPairsHom G).arrowsMap_comp_source hm hs
    hflat hcan hcoc

end AlgebraicGeometry.Space

end

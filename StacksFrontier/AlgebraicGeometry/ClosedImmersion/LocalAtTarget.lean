module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.Topology.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafUniqueness
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# Closed immersions are local on the target

A morphism of ringed spaces is a closed immersion as soon as its restrictions over the members
of an open covering of the target are closed immersions.

## Main definitions

* `Stacks.SheafOfModules.pushforwardBaseChange`: a square of continuous functors of sites,
  commuting up to a natural isomorphism and compatibly with maps of sheaves of rings, induces a
  natural isomorphism between the two composite pushforward functors on sheaves of modules.
* `Stacks.ClosedImmersion.openPreimageOpensIso`: the two descriptions of the opens of the
  preimage of an open subset of the target.
* `Stacks.ClosedImmersion.pushforwardRestrictionBaseChangeIso`: pushforward commutes with
  restriction to an open subset of the target and its preimage.
* `Stacks.ClosedImmersion.pullbackRestrictPreimageIso`: the pullback of the open immersion of an
  open subset of the target along a morphism is the restriction of the source to the preimage.

## Main results

* `Stacks.SheafOfModules.epi_of_epi_over_coversTop`: a morphism of sheaves of modules whose
  restrictions to the members of a covering family of the terminal object are epimorphisms is
  an epimorphism.
* `Stacks.ClosedImmersion.isClosedImmersion_of_iSup_eq_top`: being a closed immersion of ringed
  spaces can be checked on an open covering of the target.
* `Stacks.ClosedImmersion.isClosedImmersion_toShHom_of_iSup_eq_top`: the same statement for a
  morphism of locally ringed spaces, which is the form the Stacks Project gives.

## Implementation notes

The inverse image of an open subset of the target is presented in two ways. The hypothesis uses
the pullback of the canonical open immersion of the open subset, which is the shape a consumer
writes down; the proof uses the restriction of the source to the preimage open subset, which is
the shape the sheaf machinery computes with. `pullbackRestrictPreimageIso` identifies the two,
and `closedImmersion_of_precomp_iso` transports the hypothesis across that isomorphism.

The three conditions are then checked separately. Closed embeddings are local on the target
already (`Topology.IsOpenCover.isClosedEmbedding_iff_restrictPreimage`). Surjectivity of the
structure-sheaf map is detected from the covering by `epi_of_epi_over_coversTop`, after
`unit_map_siteRestrict_baseChange` identifies the restriction to an open subset of the
structure-sheaf map of `f` with the structure-sheaf map of the restricted morphism. Local
generation of the kernel is glued by `Stacks.SheafOfModules.bindLocalGeneratorsData`, after the
kernel of the restricted map is identified with the restriction of the kernel.

The base change of pushforwards is proved first for a commuting square of arbitrary sites
(`Stacks.SheafOfModules.pushforwardBaseChange`) and only then specialised to the restriction
square of a morphism of ringed spaces. Stating it in that generality is not decoration: the
continuity hypotheses of the four functors become hypotheses of the general statement, so they
are supplied once at the point of use, where the carrier of a restricted ringed space and the
open subspace it restricts to are visibly the same space. Done directly on the ringed spaces,
each of the ten or so pushforward functors involved asks for its own continuity instance and
finds none, because deciding the two carriers agree needs more unfolding than instance
resolution performs.

The result is stated for ringed spaces, which is more general than the source's formulation for
locally ringed spaces; locality of the rings is never used.

The covering is indexed by an arbitrary type `ι`, but the site of opens lives in the universe of
the space, so the covering is reindexed by `Set.range U` before any sheaf datum is built.

## References

* [Stacks Project, Tag 01HL](https://stacks.math.columbia.edu/tag/01HL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe v u

namespace Stacks.SheafOfModules

/-- A morphism of sheaves of modules is an epimorphism as soon as its restrictions to the
members of a covering family of the terminal object are epimorphisms.

This is the converse of `Stacks.SheafOfModules.over_epi`, and unlike that direction it is not
formal: it is proved by testing a pair of maps out of the target on sections, where the covering
family lets the sheaf condition glue the local agreements. -/
theorem epi_of_epi_over_coversTop {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} (p : M ⟶ N)
    {I : Type u} (X : I → C) (hX : J.CoversTop X)
    (hp : ∀ i, Epi (p.over (X i))) : Epi p := by
  constructor
  intro Q g h e
  let F := PresheafOfModules.toPresheaf R.obj
  have hg : F.map g.val = F.map h.val := by
    apply NatTrans.ext
    funext W
    apply Q.isSheaf.hom_ext (hX.cover W.unop)
    intro A
    obtain ⟨i, ⟨k⟩⟩ := A.hf
    have hi : g.over (X i) = h.over (X i) := by
      have := hp i
      apply (cancel_epi (p.over (X i))).mp
      simpa only [← Functor.map_comp] using
        congrArg (fun q ↦ (_root_.SheafOfModules.overFunctor R (X i)).map q) e
    let F' := PresheafOfModules.toPresheaf (R.over (X i)).obj
    have hi' := congrArg (fun q ↦ (F'.map q.val).app (Opposite.op (Over.mk k))) hi
    change (F.map g.val).app W ≫ (F.obj Q.val).map A.f.op =
      (F.map h.val).app W ≫ (F.obj Q.val).map A.f.op
    rw [← (F.map g.val).naturality A.f.op, ← (F.map h.val).naturality A.f.op]
    exact congrArg (fun q ↦ (F.obj N.val).map A.f.op ≫ q) hi'
  exact _root_.SheafOfModules.hom_ext (F.map_injective hg)

/-- Two morphisms of sheaves of modules are equal if they agree on every section. -/
private theorem hom_ext_of_apply_eq {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} {f g : M ⟶ N}
    (h : ∀ V x, (f.val.app V).hom x = (g.val.app V).hom x) : f = g :=
  _root_.SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext <| LinearMap.ext (h V)

section BaseChange

variable {C₁ C₂ C₃ C₄ : Type u} [Category.{u} C₁] [Category.{u} C₂] [Category.{u} C₃]
  [Category.{u} C₄]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  {J₃ : GrothendieckTopology C₃} {J₄ : GrothendieckTopology C₄}
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃} {K : C₃ ⥤ C₄}
  [instF : F.IsContinuous J₁ J₂] [instG : G.IsContinuous J₂ J₄]
  [instH : H.IsContinuous J₁ J₃] [instK : K.IsContinuous J₃ J₄]
  {T : Sheaf J₁ RingCat.{u}} {R₂ : Sheaf J₂ RingCat.{u}} {R₃ : Sheaf J₃ RingCat.{u}}
  {R₄ : Sheaf J₄ RingCat.{u}}

/-- **Base change for pushforwards of sheaves of modules.** A square of continuous functors of
sites that commutes up to a natural isomorphism `e`, together with maps of sheaves of rings
along its four sides that are compatible with `e`, induces an isomorphism between the two
composite pushforward functors on sheaves of modules. -/
noncomputable def pushforwardBaseChange
    (φ₁ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).obj R₂)
    (φ₂ : R₂ ⟶ (G.sheafPushforwardContinuous RingCat.{u} J₂ J₄).obj R₄)
    (ψ₁ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} J₁ J₃).obj R₃)
    (ψ₂ : R₃ ⟶ (K.sheafPushforwardContinuous RingCat.{u} J₃ J₄).obj R₄)
    (e : F ⋙ G ≅ H ⋙ K)
    (he : haveI := Functor.isContinuous_comp F G J₁ J₂ J₄
          haveI := Functor.isContinuous_comp H K J₁ J₃ J₄
          (φ₁ ≫ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).map φ₂) ≫
            (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u} J₁ J₄).app R₄ =
          ψ₁ ≫ (H.sheafPushforwardContinuous RingCat.{u} J₁ J₃).map ψ₂) :
    _root_.SheafOfModules.pushforward.{u} φ₂ ⋙ _root_.SheafOfModules.pushforward.{u} φ₁ ≅
      _root_.SheafOfModules.pushforward.{u} ψ₂ ⋙ _root_.SheafOfModules.pushforward.{u} ψ₁ :=
  haveI := Functor.isContinuous_comp F G J₁ J₂ J₄
  haveI := Functor.isContinuous_comp H K J₁ J₃ J₄
  _root_.SheafOfModules.pushforwardComp φ₁ φ₂ ≪≫
    _root_.SheafOfModules.pushforwardCongr₂ _ e.symm he ≪≫
      (_root_.SheafOfModules.pushforwardComp ψ₁ ψ₂).symm

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Transporting the structure map `R ⟶ φ_* R'` of a pushforward along a natural isomorphism of
the underlying functors of sites carries the canonical map on unit objects to the canonical map
on unit objects. -/
theorem unitToPushforwardObjUnit_congr₂
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [F.IsContinuous J K] [G.IsContinuous J K]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom _ _ _).app S = ψ) :
    _root_.SheafOfModules.unitToPushforwardObjUnit φ ≫
      (_root_.SheafOfModules.pushforwardCongr₂ φ e he).hom.app
        (_root_.SheafOfModules.unit S) =
      _root_.SheafOfModules.unitToPushforwardObjUnit ψ := by
  refine hom_ext_of_apply_eq fun V x => ?_
  exact congrArg (fun q => q.hom.app V x) he

/-- The base-change isomorphism of `pushforwardBaseChange` is compatible with the canonical
maps from the unit object: going along the top of the square and then across is the same as
going along the bottom. -/
theorem unitToPushforwardObjUnit_pushforwardBaseChange
    [J₁.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [J₄.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (φ₁ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).obj R₂)
    (φ₂ : R₂ ⟶ (G.sheafPushforwardContinuous RingCat.{u} J₂ J₄).obj R₄)
    (ψ₁ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} J₁ J₃).obj R₃)
    (ψ₂ : R₃ ⟶ (K.sheafPushforwardContinuous RingCat.{u} J₃ J₄).obj R₄)
    (e : F ⋙ G ≅ H ⋙ K)
    (he : haveI := Functor.isContinuous_comp F G J₁ J₂ J₄
          haveI := Functor.isContinuous_comp H K J₁ J₃ J₄
          (φ₁ ≫ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).map φ₂) ≫
            (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u} J₁ J₄).app R₄ =
          ψ₁ ≫ (H.sheafPushforwardContinuous RingCat.{u} J₁ J₃).map ψ₂) :
    haveI := Functor.isContinuous_comp F G J₁ J₂ J₄
    haveI := Functor.isContinuous_comp H K J₁ J₃ J₄
    _root_.SheafOfModules.unitToPushforwardObjUnit
        (φ₁ ≫ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).map φ₂) ≫
      (pushforwardBaseChange φ₁ φ₂ ψ₁ ψ₂ e he).hom.app (_root_.SheafOfModules.unit R₄) =
    _root_.SheafOfModules.unitToPushforwardObjUnit
        (ψ₁ ≫ (H.sheafPushforwardContinuous RingCat.{u} J₁ J₃).map ψ₂) := by
  have := Functor.isContinuous_comp F G J₁ J₂ J₄
  have := Functor.isContinuous_comp H K J₁ J₃ J₄
  refine Eq.trans ?_ (unitToPushforwardObjUnit_congr₂ (J := J₁) (K := J₄) (F := H ⋙ K)
    (G := F ⋙ G) (T := T) (S := R₄)
    (φ₁ ≫ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).map φ₂) e.symm he)
  exact congrArg (fun z => _root_.SheafOfModules.unitToPushforwardObjUnit
      (φ₁ ≫ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).map φ₂) ≫ z)
    ((Category.id_comp _).trans (Category.comp_id _))

end BaseChange

/-- Local generators transported along the restriction of sheaves of modules induced by an
equivalence of sites.

This is `Stacks.SheafOfModules.Site.localGeneratorsDataPushforward` with its
colimit-preservation hypothesis discharged from the assumption that `G` is an equivalence and
`φ` an isomorphism, exactly as in `Stacks.SheafOfModules.Site.isFiniteType_pushforward`. -/
noncomputable def localGeneratorsDataPushforwardOfIsIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
    [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ Y : D, HasSheafify (K.over Y) AddCommGrpCat.{u}]
    [∀ Y : D, (K.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasPullbacks C] [HasPullbacks D]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J] [G.IsLeftAdjoint]
    [G.IsEquivalence]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R) [instφ : IsIso φ]
    (η : (_root_.SheafOfModules.pushforward φ).obj (_root_.SheafOfModules.unit R) ≅
      _root_.SheafOfModules.unit S)
    {M : _root_.SheafOfModules.{u} R} (P : M.LocalGeneratorsData) :
    ((_root_.SheafOfModules.pushforward φ).obj M).LocalGeneratorsData := by
  have hpost (Y : D) : (Over.post (X := Y) G).IsContinuous (K.over Y) (J.over _) :=
    (Functor.isContinuous_iff_coverPreserving).2
      ((CoverPreserving.of_isContinuous G K J).overPost Y)
  have h : ∀ (Y : D) (Z : C) (f : G.obj Y ⟶ Z),
      PreservesColimitsOfSize.{u, u} <|
      _root_.SheafOfModules.pushforward.{u} (R := R.over Z)
        (F := Over.post (X := Y) G ⋙ Over.map f)
        (((Over.forget Y).sheafPushforwardContinuous RingCat.{u} (K.over Y) K).map φ) := by
    intro Y Z f
    let G' := Over.post (X := Y) G ⋙ Over.map f
    have : G'.IsContinuous (K.over Y) (J.over Z) :=
      Functor.isContinuous_comp _ _ _ (J.over _) _
    have : G'.IsCocontinuous (K.over Y) (J.over Z) := isCocontinuous_comp _ _ _ (J.over _)
    let a : S.over Y ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over Y) (J.over Z)).obj (R.over Z) :=
      ((Over.forget Y).sheafPushforwardContinuous RingCat.{u} (K.over Y) K).map φ
    have : IsIso a := by
      dsimp only [a]
      apply Functor.map_isIso
    have : G'.IsLeftAdjoint := by
      dsimp [G']
      infer_instance
    have : (_root_.SheafOfModules.pushforward a).IsLeftAdjoint :=
      _root_.SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
    infer_instance
  exact Stacks.SheafOfModules.Site.localGeneratorsDataPushforward G φ η h P

end Stacks.SheafOfModules

namespace Stacks.ClosedImmersion

/-- Two morphisms of opens with the same source and target induce the same map on sections:
there is at most one morphism between two opens. -/
theorem presheaf_map_eq_of_le {T : TopCat} (P : TopCat.Presheaf CommRingCat.{u} T)
    {A B : (Opens T)ᵒᵖ} (a b : A ⟶ B) : P.map a = P.map b :=
  congrArg P.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The opens of the preimage of an open subset `U` of the target, described in two ways: as the
opens of `X` contained in the image of `U` pulled back along `f`, and as the opens of the
restriction of `X` to `U` pulled back along the restricted morphism and then included into
`Z`. -/
noncomputable def openPreimageOpensIso
    {X Z : RingedSpace.{u, u}} (f : Z ⟶ X) (U : Opens (X : TopCat))
    (g : Z.restrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding)
    (hfac : Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ≫ f =
      g ≫ X.ofRestrict U.isOpenEmbedding) :
    U.isOpenEmbedding.functor ⋙ Opens.map f.hom.base ≅
      Opens.map g.hom.base ⋙ ((Opens.map f.hom.base).obj U).isOpenEmbedding.functor := by
  let V := (Opens.map f.hom.base).obj U
  let jU := X.ofRestrict U.isOpenEmbedding
  let jV := Z.ofRestrict V.isOpenEmbedding
  let hU := U.isOpenEmbedding
  let hV := V.isOpenEmbedding
  exact NatIso.ofComponents
    (fun W => eqToIso (by
      apply Opens.ext
      ext z
      change f.hom.base z ∈ hU.functor.obj W ↔
        z ∈ hV.functor.obj ((Opens.map g.hom.base).obj W)
      constructor
      · rintro ⟨x, hx, hzx⟩
        have hz : z ∈ V := by
          change f.hom.base z ∈ U
          rw [← hzx]
          exact x.2
        let z' : Z.restrict V.isOpenEmbedding := ⟨z, hz⟩
        have hb := congrFun (congrArg (fun q => q.hom.base) hfac) z'
        have hxEq : g.hom.base z' = x := by
          apply hU.injective
          calc
            jU.hom.base (g.hom.base z') = f.hom.base z := hb.symm
            _ = jU.hom.base x := hzx.symm
        refine ⟨z', ?_, rfl⟩
        change g.hom.base z' ∈ W
        exact hxEq ▸ hx
      · rintro ⟨z', hz', hzz'⟩
        refine ⟨g.hom.base z', hz', ?_⟩
        calc
          jU.hom.base (g.hom.base z') = f.hom.base (jV.hom.base z') :=
            (congrFun (congrArg (fun q => q.hom.base) hfac) z').symm
          _ = f.hom.base z := congrArg f.hom.base hzz'))
    (fun _ => Subsingleton.elim _ _)

/-- The structure-sheaf component of the inclusion of an open subspace over the image of an open
`W`, followed by restriction along the unit `W ⟶ (image of W)` pulled back, is the identity. -/
theorem ofRestrict_c_app_comp_presheaf_map_unit {X : RingedSpace.{u, u}}
    (U : Opens (X : TopCat)) (W : Opens (X.restrict U.isOpenEmbedding : TopCat)) :
    (X.ofRestrict U.isOpenEmbedding).hom.c.app
        (Opposite.op (U.isOpenEmbedding.functor.obj W)) ≫
      (X.restrict U.isOpenEmbedding).presheaf.map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W).op =
      𝟙 (X.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj W))) :=
  ((Functor.map_comp X.presheaf
        (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
          (U.isOpenEmbedding.functor.obj W)).op
        (U.isOpenEmbedding.functor.map (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W)).op
      ).symm.trans (presheaf_map_eq_of_le X.presheaf _ (𝟙 _))).trans (X.presheaf.map_id _)

/-- The structure-sheaf component of the restricted morphism `g : f⁻¹ U ⟶ U` over an open subset
`W` of `U` is the structure-sheaf component of `f` over the image of `W` in `X`, followed by the
identification of the two descriptions of its preimage. -/
theorem restrict_structureMap_eq
    {X Z : RingedSpace.{u, u}} (f : Z ⟶ X) (U : Opens (X : TopCat))
    (g : Z.restrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding)
    (hfac : Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ≫ f =
      g ≫ X.ofRestrict U.isOpenEmbedding)
    (e : U.isOpenEmbedding.functor ⋙ Opens.map f.hom.base ≅
      Opens.map g.hom.base ⋙ ((Opens.map f.hom.base).obj U).isOpenEmbedding.functor)
    (W : Opens (X.restrict U.isOpenEmbedding : TopCat)) :
    f.hom.c.app (Opposite.op (U.isOpenEmbedding.functor.obj W)) ≫
      Z.presheaf.map (e.inv.app W).op = g.hom.c.app (Opposite.op W) := by
  let V := (Opens.map f.hom.base).obj U
  let jU := X.ofRestrict U.isOpenEmbedding
  let jV := Z.ofRestrict V.isOpenEmbedding
  let hU := U.isOpenEmbedding
  let hV := V.isOpenEmbedding
  let PX := (X.restrict U.isOpenEmbedding).presheaf
  let PZ := (Z.restrict V.isOpenEmbedding).presheaf
  let H := Opens.map g.hom.base
  let A := hU.functor.obj W
  let i : W ⟶ (Opens.map jU.hom.base).obj A := hU.isOpenMap.adjunction.unit.app W
  let cV := hV.isOpenMap.adjunction.counit.app ((Opens.map f.hom.base).obj A)
  -- `g⁻¹ W` sits inside the preimage under `jV ≫ f` of the image `A` of `W`.
  let k : H.obj W ⟶ (Opens.map jV.hom.base).obj ((Opens.map f.hom.base).obj A) :=
    homOfLE (by
      intro z hz
      change f.hom.base (jV.hom.base z) ∈ A
      have hb := congrArg (fun q : Z.restrict V.isOpenEmbedding ⟶ X => q.hom.base z) hfac
      change f.hom.base (jV.hom.base z) = jU.hom.base (g.hom.base z) at hb
      rw [hb]
      exact ⟨g.hom.base z, hz, rfl⟩)
  have hstep : ∀ (t : Opposite.op ((Opens.map (g ≫ jU).hom.base).obj A) ⟶
        Opposite.op (H.obj W)),
      (g ≫ jU).hom.c.app (Opposite.op A) ≫ PZ.map t = g.hom.c.app (Opposite.op W) := fun t =>
    ((((congrArg (fun z => (g ≫ jU).hom.c.app (Opposite.op A) ≫ z)
                (presheaf_map_eq_of_le PZ t (H.map i).op)).trans
            (Category.assoc (jU.hom.c.app (Opposite.op A))
              (g.hom.c.app (Opposite.op ((Opens.map jU.hom.base).obj A)))
              (PZ.map (H.map i).op))).trans
          (congrArg (fun z => jU.hom.c.app (Opposite.op A) ≫ z)
            (g.hom.c.naturality i.op).symm)).trans
        (Category.assoc (jU.hom.c.app (Opposite.op A)) (PX.map i.op)
          (g.hom.c.app (Opposite.op W))).symm).trans
      ((congrArg (fun z => z ≫ g.hom.c.app (Opposite.op W))
        (ofRestrict_c_app_comp_presheaf_map_unit U W)).trans (Category.id_comp _))
  have h0 : Z.presheaf.map (e.inv.app W).op =
      Z.presheaf.map cV.op ≫ Z.presheaf.map (hV.functor.map k).op :=
    (presheaf_map_eq_of_le Z.presheaf (e.inv.app W).op (cV.op ≫ (hV.functor.map k).op)).trans
      (Functor.map_comp Z.presheaf cV.op (hV.functor.map k).op)
  have hL : f.hom.c.app (Opposite.op A) ≫ Z.presheaf.map (e.inv.app W).op =
      (jV ≫ f).hom.c.app (Opposite.op A) ≫ PZ.map k.op :=
    (congrArg (fun z => f.hom.c.app (Opposite.op A) ≫ z) h0).trans
      (Category.assoc (f.hom.c.app (Opposite.op A)) (Z.presheaf.map cV.op)
        (Z.presheaf.map (hV.functor.map k).op)).symm
  exact hL.trans (((congrArg (fun z => z ≫ PZ.map k.op)
      (SheafedSpace.congr_hom_app hfac (Opposite.op A))).trans
    (Category.assoc _ _ _)).trans
      ((congrArg (fun z => (g ≫ jU).hom.c.app (Opposite.op A) ≫ z)
        (Functor.map_comp PZ _ _).symm).trans (hstep _)))

section Restriction

variable {X Z : RingedSpace.{u, u}} (f : Z ⟶ X) (U : Opens (X : TopCat))

/-- Continuity of the functor on opens induced by the inclusion of an open subspace, in the
phrasing the restricted ringed space uses. -/
theorem isContinuous_opensFunctor :
    U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) :=
  U.isOpenEmbedding.functor_isContinuous

/-- **Pushforward commutes with restriction to an open subset of the target.** The pushforward
of a sheaf of modules along `f`, restricted to an open subset `U` of the target, is the
pushforward along the restricted morphism `f⁻¹ U ⟶ U` of its restriction to `f⁻¹ U`. -/
noncomputable def pushforwardRestrictionBaseChangeIso
    (g : Z.restrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding)
    (hfac : Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ≫ f =
      g ≫ X.ofRestrict U.isOpenEmbedding) :
    SheafOfModules.pushforward (structureSheafHom f) ⋙
      AlgebraicGeometry.SheafOfModules.siteRestrict X U ≅
      AlgebraicGeometry.SheafOfModules.siteRestrict Z ((Opens.map f.hom.base).obj U) ⋙
        modulePushforward g :=
  Stacks.SheafOfModules.pushforwardBaseChange
    (F := U.isOpenEmbedding.functor) (G := Opens.map f.hom.base)
    (H := Opens.map g.hom.base)
    (K := ((Opens.map f.hom.base).obj U).isOpenEmbedding.functor)
    (instF := isContinuous_opensFunctor U)
    (instG := instIsContinuousOpensCarrierMapGrothendieckTopology (f := f.hom.base))
    (instH := instIsContinuousOpensCarrierMapGrothendieckTopology (f := g.hom.base))
    (instK := isContinuous_opensFunctor ((Opens.map f.hom.base).obj U))
    (𝟙 _) (structureSheafHom f) (structureSheafHom g) (𝟙 _)
    (openPreimageOpensIso f U g hfac)
    (by
      ext W x
      exact congrArg (fun q => q.hom x)
        (restrict_structureMap_eq f U g hfac (openPreimageOpensIso f U g hfac) W.unop))

/-- **The structure-sheaf map of `f` restricted to an open subset `U` of the target is the
structure-sheaf map of the restricted morphism `f⁻¹ U ⟶ U`.** -/
theorem unit_map_siteRestrict_baseChange
    (g : Z.restrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding)
    (hfac : Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ≫ f =
      g ≫ X.ofRestrict U.isOpenEmbedding) :
    (AlgebraicGeometry.SheafOfModules.siteRestrict X U).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) ≫
      (pushforwardRestrictionBaseChangeIso f U g hfac).hom.app
        (SheafOfModules.unit (structureSheafRing Z)) =
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g) := by
  refine Stacks.SheafOfModules.hom_ext_of_apply_eq fun W x => ?_
  exact congrArg (fun q => q.hom x)
    (restrict_structureMap_eq f U g hfac (openPreimageOpensIso f U g hfac) W.unop)

/-- **The comparison square.** Restricting the structure-sheaf map of `f` to an open subset `U`
of the target, transported to the restricted ringed space, is the structure-sheaf map of the
restricted morphism `f⁻¹ U ⟶ U`. This is the single identity both halves of the locality
argument run on: surjectivity over `U`, and the identification of the kernel over `U` with the
kernel of the restricted map. -/
theorem overFunctorIso_comp_baseChange_comm
    (g : Z.restrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding)
    (hfac : Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ≫ f =
      g ≫ X.ofRestrict U.isOpenEmbedding) :
    (U.sheafOfModulesEquivOver (structureSheafRing X)).functor.map
        ((SheafOfModules.overFunctor (structureSheafRing X) U).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))) ≫
      ((AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U).app
          ((SheafOfModules.pushforward (structureSheafHom f)).obj
            (SheafOfModules.unit (structureSheafRing Z))) ≪≫
        (pushforwardRestrictionBaseChangeIso f U g hfac).app
          (SheafOfModules.unit (structureSheafRing Z))).hom =
    ((AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U).app
        (SheafOfModules.unit (structureSheafRing X))).hom ≫
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (pushforwardRestrictionBaseChangeIso f U g hfac).hom.app
            (SheafOfModules.unit (structureSheafRing Z)))
          ((AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U).hom.naturality
            (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)))).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z =>
            (AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U).hom.app
              (SheafOfModules.unit (structureSheafRing X)) ≫ z)
          (unit_map_siteRestrict_baseChange f U g hfac))))

/-- Surjectivity of the structure-sheaf map over an open subset `U` of the target follows from
surjectivity of the structure-sheaf map of the restricted morphism `f⁻¹ U ⟶ U`. -/
theorem epi_unit_map_over_open_of_epi_restriction
    (h : Epi (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom (Stacks.SheafOfModules.openPreimageFactorization f U).map))) :
    Epi ((SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)).over U) := by
  let RX := structureSheafRing X
  let g := (Stacks.SheafOfModules.openPreimageFactorization f U).map
  let E := U.sheafOfModulesEquivOver RX
  let θ := AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U
  let T := θ.app ((SheafOfModules.pushforward (structureSheafHom f)).obj
      (SheafOfModules.unit (structureSheafRing Z))) ≪≫
    (pushforwardRestrictionBaseChangeIso f U g
      (Stacks.SheafOfModules.openPreimageFactorization f U).fac).app
        (SheafOfModules.unit (structureSheafRing Z))
  have hcmp := overFunctorIso_comp_baseChange_comm f U g
    (Stacks.SheafOfModules.openPreimageFactorization f U).fac
  have hcomp : Epi (E.functor.map ((SheafOfModules.overFunctor RX U).map
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))) ≫ T.hom) := by
    rw [hcmp]
    have : IsIso (θ.hom.app (SheafOfModules.unit RX)) :=
      (θ.app (SheafOfModules.unit RX)).isIso_hom
    exact @epi_comp _ _ _ _ _ _ inferInstance _ h
  have : IsIso T.hom := T.isIso_hom
  exact E.functor.epi_of_epi_map ((epi_comp_iff_of_isIso _ T.hom).mp hcomp)

/-- **The pullback of the open immersion of an open subset of the target is the restriction of
the source to its preimage.** This is the comparison between the two ways of presenting the
inverse image of an open subset: the hypothesis of locality uses the pullback, while the sheaf
machinery computes with the restricted ringed space. -/
noncomputable def pullbackRestrictPreimageIso :
    pullback (X.ofRestrict U.isOpenEmbedding) f ≅
      Z.restrict ((Opens.map f.hom.base).obj U).isOpenEmbedding := by
  let jU := X.ofRestrict U.isOpenEmbedding
  let V := (Opens.map f.hom.base).obj U
  let jV := Z.ofRestrict V.isOpenEmbedding
  let P := pullback jU f
  let p := pullback.fst jU f
  let q := pullback.snd jU f
  let g := (Stacks.SheafOfModules.openPreimageFactorization f U).map
  have hfac : jV ≫ f = g ≫ jU := (Stacks.SheafOfModules.openPreimageFactorization f U).fac
  have hqV (x : P) : q.hom.base x ∈ V := by
    change f.hom.base (q.hom.base x) ∈ U
    have hpq' : jU.hom.base (p.hom.base x) = f.hom.base (q.hom.base x) := by
      simpa using congrArg (fun k : P ⟶ X => k.hom.base x) pullback.condition
    rw [← hpq']
    exact (p.hom.base x).property
  have hrange : Set.range q.hom.base ⊆ Set.range jV.hom.base := by
    have hrV : Set.range jV.hom.base = (V : Set Z) := Opens.set_range_inclusion' V
    rw [hrV, Set.range_subset_iff]
    exact hqV
  let F := SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)
  let glift := PresheafedSpace.IsOpenImmersion.lift (F.map jV) (F.map q) hrange
  let qbar : P ⟶ Z.restrict V.isOpenEmbedding := F.preimage glift
  have hqbar : qbar ≫ jV = q := by
    apply F.map_injective
    rw [F.map_comp, F.map_preimage]
    exact PresheafedSpace.IsOpenImmersion.lift_fac (F.map jV) (F.map q) hrange
  have hpg : p = qbar ≫ g := by
    apply (cancel_mono jU).mp
    calc
      p ≫ jU = q ≫ f := pullback.condition
      _ = (qbar ≫ jV) ≫ f := by rw [← hqbar]
      _ = (qbar ≫ g) ≫ jU := by simp only [Category.assoc, hfac]
  let eInv : Z.restrict V.isOpenEmbedding ⟶ P := pullback.lift g jV hfac.symm
  have heInvP : eInv ≫ p = g := pullback.lift_fst g jV hfac.symm
  have heInvQ : eInv ≫ q = jV := pullback.lift_snd g jV hfac.symm
  refine ⟨qbar, eInv, ?_, ?_⟩
  · apply pullback.hom_ext
    · calc
        qbar ≫ eInv ≫ p = qbar ≫ g := by rw [heInvP]
        _ = p := hpg.symm
    · calc
        qbar ≫ eInv ≫ q = qbar ≫ jV := by rw [heInvQ]
        _ = q := hqbar
  · apply (cancel_mono jV).mp
    calc
      eInv ≫ qbar ≫ jV = eInv ≫ q := by rw [hqbar]
      _ = jV := heInvQ

/-- The comparison of `pullbackRestrictPreimageIso` is compatible with the projection to the
source. -/
theorem pullbackRestrictPreimageIso_hom_snd :
    (pullbackRestrictPreimageIso f U).hom ≫
      Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding =
      pullback.snd (X.ofRestrict U.isOpenEmbedding) f := by
  apply (SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map_injective
  rw [Functor.map_comp]
  dsimp only [pullbackRestrictPreimageIso]
  rw [Functor.map_preimage]
  exact PresheafedSpace.IsOpenImmersion.lift_fac
    ((SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map
      (Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding))
    ((SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map
      (pullback.snd (X.ofRestrict U.isOpenEmbedding) f)) _

/-- The comparison of `pullbackRestrictPreimageIso` identifies the restricted morphism with the
projection of the pullback to the open subset of the target. -/
theorem pullbackRestrictPreimageIso_hom_comp :
    (pullbackRestrictPreimageIso f U).hom ≫
      (Stacks.SheafOfModules.openPreimageFactorization f U).map =
      pullback.fst (X.ofRestrict U.isOpenEmbedding) f := by
  apply (cancel_mono (X.ofRestrict U.isOpenEmbedding)).mp
  rw [Category.assoc, ← (Stacks.SheafOfModules.openPreimageFactorization f U).fac,
    ← Category.assoc, pullbackRestrictPreimageIso_hom_snd]
  exact pullback.condition.symm

/-- Local generation of the ideal sheaf over an open subset `U` of the target follows from local
generation of the ideal sheaf of the restricted morphism `f⁻¹ U ⟶ U`.

The datum is carried along the comparison square of
`overFunctorIso_comp_baseChange_comm`: it identifies the kernel of the structure-sheaf map of
the restricted morphism with the restriction of `idealSheaf f` to `U`, transported to the
restricted ringed space, and the slice site over `U` is then reached through the equivalence
`TopologicalSpace.Opens.sheafOfModulesEquivOver`. -/
theorem localGeneratorsData_over_open_of_restriction
    (hlocal : IsClosedImmersion (Stacks.SheafOfModules.openPreimageFactorization f U).map) :
    Nonempty (SheafOfModules.LocalGeneratorsData.{u} ((idealSheaf f).over U)) := by
  classical
  let αf := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)
  let gi := (Stacks.SheafOfModules.openPreimageFactorization f U).map
  have hgi : Z.ofRestrict ((Opens.map f.hom.base).obj U).isOpenEmbedding ≫ f =
      gi ≫ X.ofRestrict U.isOpenEmbedding :=
    (Stacks.SheafOfModules.openPreimageFactorization f U).fac
  let αg := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom gi)
  let E := U.sheafOfModulesEquivOver (structureSheafRing X)
  let D := Classical.choice ((isClosedImmersion_iff gi).mp hlocal).2.2
  let a := (SheafOfModules.overFunctor (structureSheafRing X) U).map αf
  let τX := (AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U).app
    (SheafOfModules.unit (structureSheafRing X))
  let T := (AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U).app
      ((SheafOfModules.pushforward (structureSheafHom f)).obj
        (SheafOfModules.unit (structureSheafRing Z))) ≪≫
    (pushforwardRestrictionBaseChangeIso f U gi hgi).app
      (SheafOfModules.unit (structureSheafRing Z))
  have hcmp : E.functor.map a ≫ T.hom = τX.hom ≫ αg :=
    overFunctorIso_comp_baseChange_comm f U gi hgi
  let eker : E.functor.obj (kernel a) ≅ kernel αg :=
    PreservesKernel.iso E.functor a ≪≫
      kernel.mapIso (f := E.functor.map a) αg τX T hcmp
  have hφ : IsIso ((U.sheafRestrictSheafEquivOver.app (structureSheafRing X)).inv) :=
    (U.sheafRestrictSheafEquivOver.app (structureSheafRing X)).isIso_inv
  have : (SheafOfModules.overFunctor (structureSheafRing X) U).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  have : PreservesLimit (parallelPair αf 0)
      (SheafOfModules.overFunctor (structureSheafRing X) U) := by
    change PreservesLimit _ (SheafOfModules.pushforward.{u} (𝟙 ((structureSheafRing X).over U)))
    infer_instance
  let D₀ := Stacks.AlgebraicGeometry.DerivedPushforward.localGeneratorsDataOfIso.{u, u, u} D
    eker.symm
  let D₁ := Stacks.SheafOfModules.localGeneratorsDataPushforwardOfIsIso
    (G := (Opens.overEquivalence U).functor) (instφ := hφ)
    ((U.sheafRestrictSheafEquivOver.app (structureSheafRing X)).inv)
    (U.sheafOfModulesEquivOverInverseUnit (structureSheafRing X)) D₀
  let D₂ := Stacks.AlgebraicGeometry.DerivedPushforward.localGeneratorsDataOfIso.{u, u, u} D₁
    (E.unitIso.app (kernel a)).symm
  exact ⟨Stacks.AlgebraicGeometry.DerivedPushforward.localGeneratorsDataOfIso.{u, u, u} D₂
    (PreservesKernel.iso (SheafOfModules.overFunctor (structureSheafRing X) U) αf).symm⟩

end Restriction

/-- **Being a closed immersion is invariant under an isomorphism of the source.** -/
theorem closedImmersion_of_precomp_iso
    {A B W : RingedSpace.{u, u}} (e : A ≅ B) (g : B ⟶ W)
    (h : IsClosedImmersion (e.hom ≫ g)) : IsClosedImmersion g := by
  obtain ⟨hclosed, hepi, ⟨D⟩⟩ := (isClosedImmersion_iff _).mp h
  let α {P Q : RingedSpace.{u, u}} (k : P ⟶ Q) :=
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom k)
  let β := (SheafOfModules.pushforward (structureSheafHom g)).map
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom e.hom))
  let δ := β ≫ (structureSheafPushforwardComp e.hom g).inv.app
    (SheafOfModules.unit (structureSheafRing A))
  have hψe : IsIso (structureSheafHom e.hom) := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
    dsimp [structureSheafHom]
    have : IsIso e.hom.hom.c := inferInstance
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    exact Functor.map_isIso (forget₂ CommRingCat RingCat) _
  have hαe : IsIso (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom e.hom)) :=
    Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit (structureSheafHom e.hom)
  have hδ : IsIso δ := by
    dsimp only [δ, β]
    infer_instance
  have hα : α (e.hom ≫ g) = α g ≫ δ := unitToPushforwardObjUnit_compose e.hom g
  have hclosed' : Topology.IsClosedEmbedding g.hom.base := by
    have he : Topology.IsClosedEmbedding e.inv.hom.base :=
      (TopCat.homeoOfIso (asIso e.inv.hom.base)).isClosedEmbedding
    have heq : (e.hom ≫ g).hom.base ∘ e.inv.hom.base = g.hom.base := by
      ext x
      have hx : e.hom.hom.base (e.inv.hom.base x) = x :=
        congrArg (fun k : B ⟶ B => k.hom.base x) e.inv_hom_id
      change g.hom.base (e.hom.hom.base (e.inv.hom.base x)) = g.hom.base x
      rw [hx]
    rw [← heq]
    exact hclosed.comp he
  have hepi' : Epi (α g) := by
    rw [← epi_comp_iff_of_isIso (α g) δ, ← hα]
    exact hepi
  let EK : kernel (α g) ≅ kernel (α (e.hom ≫ g)) :=
    kernel.mapIso (f := α g) (α (e.hom ≫ g)) (Iso.refl _) (asIso δ) hα.symm
  exact (isClosedImmersion_iff g).mpr ⟨hclosed', hepi',
    ⟨Stacks.AlgebraicGeometry.DerivedPushforward.localGeneratorsDataOfIso.{u, u, u} D EK.symm⟩⟩

/-- **Stacks Project, Tag 01HL.** A morphism of ringed spaces whose restrictions over the
members of an open covering of the target are closed immersions is itself a closed immersion.

This is the Stacks statement with locally ringed spaces relaxed to ringed spaces; see
`Stacks.ClosedImmersion.isClosedImmersion_toShHom_of_iSup_eq_top` for the source's own
formulation. -/
@[stacks 01HL "stated for ringed spaces; the source states it for locally ringed spaces"]
theorem isClosedImmersion_of_iSup_eq_top
    {X Z : RingedSpace.{u, u}} (f : Z ⟶ X) {ι : Type v} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤)
    (hf : ∀ i, IsClosedImmersion (pullback.fst (X.ofRestrict (U i).isOpenEmbedding) f)) :
    IsClosedImmersion f := by
  -- The site of opens lives in the universe of the space, so reindex the covering by the range
  -- of its members before building any sheaf datum.
  let κ : Type u := Set.range U
  let W : κ → Opens X := fun j => j.1
  have hW : ⨆ j, W j = ⊤ := by
    rw [eq_top_iff, ← hU]
    exact iSup_le fun i => le_iSup_of_le ⟨U i, ⟨i, rfl⟩⟩ le_rfl
  have hfW (j : κ) :
      IsClosedImmersion (pullback.fst (X.ofRestrict (W j).isOpenEmbedding) f) := by
    obtain ⟨_, i, rfl⟩ := j
    exact hf i
  let α {A B : RingedSpace.{u, u}} (k : A ⟶ B) :=
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom k)
  let g (i : κ) := (Stacks.SheafOfModules.openPreimageFactorization f (W i)).map
  let e (i : κ) := pullbackRestrictPreimageIso f (W i)
  have hUsite : (Opens.grothendieckTopology (X : TopCat)).CoversTop W := by
    rw [Opens.coversTop_iff]
    exact TopologicalSpace.IsOpenCover.mk hW
  have hlocal (i : κ) : IsClosedImmersion (g i) := by
    refine closedImmersion_of_precomp_iso (e i) (g i) ?_
    rw [show (e i).hom ≫ g i = _ from pullbackRestrictPreimageIso_hom_comp f (W i)]
    exact hfW i
  have hclosed : Topology.IsClosedEmbedding f.hom.base := by
    refine ((TopologicalSpace.IsOpenCover.mk hW).isClosedEmbedding_iff_restrictPreimage
      f.hom.base.hom.continuous).mpr ?_
    intro i
    have hmap : (W i).carrier.restrictPreimage f.hom.base = (g i).hom.base := by
      funext x
      exact Subtype.ext <| congrArg (fun q => q.hom.base x)
        (Stacks.SheafOfModules.openPreimageFactorization f (W i)).fac
    rw [hmap]
    exact ((isClosedImmersion_iff (g i)).mp (hlocal i)).1
  have hepi : Epi (α f) :=
    Stacks.SheafOfModules.epi_of_epi_over_coversTop (α f) W hUsite fun i =>
      epi_unit_map_over_open_of_epi_restriction f (W i)
        ((isClosedImmersion_iff (g i)).mp (hlocal i)).2.1
  classical
  exact (isClosedImmersion_iff f).mpr ⟨hclosed, hepi,
    ⟨Stacks.SheafOfModules.bindLocalGeneratorsData (kernel (α f)) W hUsite fun i =>
      Classical.choice (localGeneratorsData_over_open_of_restriction f (W i) (hlocal i))⟩⟩

/-- **Stacks Project, Tag 01HL.** Let `f : Z ⟶ X` be a morphism of locally ringed spaces. For
`f` to be a closed immersion it suffices that there is an open covering `X = ⋃ Uᵢ` such that
each `f : f⁻¹ Uᵢ ⟶ Uᵢ` is a closed immersion.

This is the source's formulation. It is the ringed-space statement
`Stacks.ClosedImmersion.isClosedImmersion_of_iSup_eq_top` applied to the underlying morphism of
ringed spaces, since being a closed immersion of locally ringed spaces is by definition the
corresponding condition on that morphism. -/
@[stacks 01HL]
theorem isClosedImmersion_toShHom_of_iSup_eq_top
    {X Z : LocallyRingedSpace.{u}} (f : Z ⟶ X) {ι : Type v} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤)
    (hf : ∀ i, IsClosedImmersion
      (pullback.fst (X.toRingedSpace.ofRestrict (U i).isOpenEmbedding) f.toShHom)) :
    IsClosedImmersion f.toShHom :=
  isClosedImmersion_of_iSup_eq_top f.toShHom U hU hf

end Stacks.ClosedImmersion

end

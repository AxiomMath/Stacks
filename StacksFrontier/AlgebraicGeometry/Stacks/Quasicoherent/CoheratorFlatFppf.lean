module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LowerShriekQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticPullbackVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriekForget
public import StacksFrontier.CategoryTheory.Adjunction.CoreflectorThroughChart
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectCartesian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# The coherator of an algebraic stack, seen on the flat-fppf site

Let `𝒳` be an algebraic stack, `i : QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` the inclusion and `Q` a right adjoint
of `i` (the coherator of **Stacks 0778**; everything here is stated for an arbitrary adjunction
`i ⊣ Q`). Let `g : (Sh(𝒳_{flat,fppf}), 𝒪) → (Sh(𝒳_fppf), 𝒪_𝒳)` be the flat-fppf morphism of
ringed topoi of **Stacks 0788**, with `g_! ⊣ g^{-1}` on modules (**Stacks 0789** (2)). This file
proves **Stacks 0779** for the modules `𝓕` whose restriction `g^{-1}𝓕` is quasi-coherent, and in
particular for the modules cartesian along flat arrows between affine objects, which is what the
objects of `LQCoh^fbc(𝒪_𝒳)` are.

## The argument

This is the proof of the source, through **Stacks 07B1**.

* For quasi-coherent `𝓖`, the counit `g_! g^{-1} 𝓖 → 𝓖` is an isomorphism: both sides are
  quasi-coherent (**Stacks 07B0** (2)), it becomes an isomorphism under `g^{-1}`, by the triangle
  identity and `g^{-1} g_! = id`, and the flat objects detect isomorphisms of quasi-coherent
  modules. So `i ⋙ g^{-1}` is fully faithful
  (`AlgebraicGeometry.Stack.fullyFaithfulQuasicoherentInclusionCompModulePullback`).
* If `g^{-1}𝓕` is quasi-coherent, `g_! g^{-1} 𝓕` is quasi-coherent, and `g^{-1}` inverts the
  counit `Q(𝓕) → 𝓕`, by `CategoryTheory.Adjunction.isIso_map_counit_app_of_leftAdjoint`
  (`AlgebraicGeometry.Stack.isIso_modulePullback_map_counit_app_of_isQuasicoherentOnSite`).
* A module is parasitic exactly when `g^{-1}` kills it (**Stacks 07AR** (2)), and `g^{-1}` is
  exact. Hence `Q(𝓕) = 0` exactly when `𝓕` is parasitic, the kernel and cokernel of
  `Q(𝓕) → 𝓕` are parasitic, and `Q` preserves the colimits of such modules that `Mod(𝒪_𝒳)`
  computes.

A module cartesian along flat arrows between affine objects has quasi-coherent restriction to the
flat-fppf site: its restriction is cartesian along every arrow there between affine objects
(`AlgebraicGeometry.Stack.FlatFppf.isIso_restrictionBaseChange_modulePullback`), and that criterion
detects quasi-coherence
(`AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine`).

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against the modules of an algebraic stack, whose
abelian structure is the one found through the sheafification instances below. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FlatFppf.isContinuous_inclusion' FlatFppf.isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

namespace FlatFppf

/-- `g^* = g^{-1}`: the pullback of sheaves of modules to the flat-fppf site is restriction along
the inclusion of the flat objects. -/
abbrev modulePullbackRestrictionIso :=
  subsiteModulePullbackRestrictionIso B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
    le_rfl (objectProperty B S hS 𝒳)

/-- **Stacks 07AR** (2), for the pullback `g^*` that `g_!` is the left adjoint of: a sheaf of
`𝒪_𝒳`-modules is parasitic exactly when its pullback to the flat-fppf site vanishes. -/
theorem isParasitic_iff_isZero_modulePullback (F : fppfModules B S hS 𝒳) :
    IsParasitic B S hS 𝒳 .fppf F.val ↔ IsZero ((modulePullback B S hS 𝒳).obj F) := by
  rw [((modulePullbackRestrictionIso B S hS 𝒳).app F).isZero_iff,
    isZero_sheafOfModules_iff_forall_subsingleton]
  exact ⟨fun h ⟨⟨x, hx⟩⟩ => h x hx, fun h x hx => h (op ⟨x, hx⟩)⟩

/-- A map of `𝒪_𝒳`-modules whose pullback to the flat-fppf site is an isomorphism is bijective on
sections over every flat object. -/
theorem bijective_app_of_isIso_modulePullback_map {F G : fppfModules B S hS 𝒳} (φ : F ⟶ G)
    (h : IsIso ((modulePullback B S hS 𝒳).map φ)) (x : 𝒳.val.val.obj)
    (hx : flatObject B S hS 𝒳.val x) : Function.Bijective (φ.val.app (op x)) := by
  have h' : IsIso ((SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)))).map φ) :=
    (NatIso.isIso_map_iff (modulePullbackRestrictionIso B S hS 𝒳) φ).1 h
  exact (ConcreteCategory.isIso_iff_bijective _).1
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _
      (op (⟨x, hx⟩ : (objectProperty B S hS 𝒳).FullSubcategory))).map_isIso
        ((SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)))).map φ))

/-- The pullback of a quasi-coherent `𝒪_𝒳`-module to the flat-fppf site is quasi-coherent: it is
cartesian along the arrows between flat objects over affine schemes, being the restriction of a
module cartesian along all arrows between objects over affine schemes. -/
theorem isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite (G : fppfModules B S hS 𝒳)
    (hG : G.IsQuasicoherentOnSite) :
    ((modulePullback B S hS 𝒳).obj G).IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine B S hS 𝒳 _ ?_
  intro y y' f hy hy'
  have h0 : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
        le_rfl (objectProperty B S hS 𝒳)).obj)
      ((SheafOfModules.forget _).obj
        ((SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)))).obj G))
      f.op) :=
    FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite G hG f.hom hy hy'
  exact @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _ _ _ _
    ((SheafOfModules.forget _).mapIso ((modulePullbackRestrictionIso B S hS 𝒳).app G).symm) _ _
    f.op h0

end FlatFppf

/-! ### The coherator seen on the flat-fppf site -/

section Coherator

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- **`g_! g^{-1}` is the identity on quasi-coherent modules**: for a quasi-coherent
`𝒪_𝒳`-module `𝓖` the counit `g_! g^{-1} 𝓖 ⟶ 𝓖` is an isomorphism. Both sides are quasi-coherent
(**Stacks 07B0** (2)), and the counit is bijective over every flat object, since `g^{-1}` of it is
inverse to the unit, which is invertible (**Stacks 0789** (2)); the flat objects detect
isomorphisms of quasi-coherent modules. -/
theorem isIso_moduleLowerShriekAdjunction_counit_app_of_isQuasicoherentOnSite
    (G : fppfModules B S hS 𝒳) (hG : G.IsQuasicoherentOnSite) :
    IsIso ((FlatFppf.moduleLowerShriekAdjunction B S hS 𝒳).counit.app G) := by
  have := FlatFppf.isIso_moduleLowerShriekAdjunction_unit B S hS 𝒳
  let adjL := FlatFppf.moduleLowerShriekAdjunction B S hS 𝒳
  have hrκ : IsIso ((FlatFppf.modulePullback B S hS 𝒳).map (adjL.counit.app G)) := by
    have : IsIso (adjL.unit.app ((FlatFppf.modulePullback B S hS 𝒳).obj G) ≫
        (FlatFppf.modulePullback B S hS 𝒳).map (adjL.counit.app G)) := by
      rw [adjL.right_triangle_components G]
      infer_instance
    exact IsIso.of_isIso_comp_left (adjL.unit.app _) _
  exact isIso_of_flatObject
    (FlatFppf.isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite B S hS 𝒳 _
      (FlatFppf.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS 𝒳 G hG)) hG _
    (FlatFppf.bijective_app_of_isIso_modulePullback_map B S hS 𝒳 _ hrκ)

/-- `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_{𝒳_{flat,fppf}})` is fully faithful: the restriction to the flat-fppf
site of quasi-coherent modules has the fully faithful left adjoint `g_!`, whose counit is
invertible on them. -/
def fullyFaithfulQuasicoherentInclusionCompModulePullback :
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι ⋙ FlatFppf.modulePullback B S hS 𝒳).FullyFaithful :=
  haveI := FlatFppf.isIso_moduleLowerShriekAdjunction_unit B S hS 𝒳
  Adjunction.fullyFaithfulCompOfLeftAdjoint
    (i := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι) (FlatFppf.modulePullback B S hS 𝒳)
    (FlatFppf.moduleLowerShriekAdjunction B S hS 𝒳)
    fun G => isIso_moduleLowerShriekAdjunction_counit_app_of_isQuasicoherentOnSite B S hS 𝒳
      G.obj G.property

/-- The restriction `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_{𝒳_{flat,fppf}})` to the flat-fppf site is full. -/
instance full_quasicoherentInclusion_comp_modulePullback :
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι ⋙ FlatFppf.modulePullback B S hS 𝒳).Full :=
  (fullyFaithfulQuasicoherentInclusionCompModulePullback B S hS 𝒳).full

/-- The restriction `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_{𝒳_{flat,fppf}})` to the flat-fppf site is faithful. -/
instance faithful_quasicoherentInclusion_comp_modulePullback :
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι ⋙ FlatFppf.modulePullback B S hS 𝒳).Faithful :=
  (fullyFaithfulQuasicoherentInclusionCompModulePullback B S hS 𝒳).faithful

variable {Q : fppfModules B S hS 𝒳 ⥤ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).FullSubcategory}
  (adj : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).ι ⊣ Q)

/-- **Stacks 07B1**: the restriction to the flat-fppf site inverts the counit `Q(𝓕) ⟶ 𝓕` of any
coherator, at every `𝒪_𝒳`-module `𝓕` whose restriction to the flat-fppf site is quasi-coherent.
The restriction `ℋ` is then `g^{-1}` of the quasi-coherent module `g_! ℋ` (**Stacks 07B0** (2)),
and `g_! g^{-1} 𝓕 ⟶ 𝓕` is the coherator of `𝓕` after restriction. -/
theorem isIso_modulePullback_map_counit_app_of_isQuasicoherentOnSite (F : fppfModules B S hS 𝒳)
    (hF : ((FlatFppf.modulePullback B S hS 𝒳).obj F).IsQuasicoherentOnSite) :
    IsIso ((FlatFppf.modulePullback B S hS 𝒳).map (adj.counit.app F)) :=
  have := FlatFppf.isIso_moduleLowerShriekAdjunction_unit B S hS 𝒳
  adj.isIso_map_counit_app_of_leftAdjoint (FlatFppf.modulePullback B S hS 𝒳)
    (FlatFppf.moduleLowerShriekAdjunction B S hS 𝒳)
    (fun G => isIso_moduleLowerShriekAdjunction_counit_app_of_isQuasicoherentOnSite B S hS 𝒳
      G.obj G.property) F
    ⟨⟨_, FlatFppf.isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite B S hS 𝒳 _ hF⟩,
      ⟨Iso.refl _⟩⟩

/-- **A map of `𝒪_𝒳`-modules bijective on sections over every flat object becomes an isomorphism
on the flat-fppf site.** -/
theorem FlatFppf.isIso_modulePullback_map_of_bijective {F G : fppfModules B S hS 𝒳} (φ : F ⟶ G)
    (h : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x → Function.Bijective (φ.val.app (op x))) :
    IsIso ((FlatFppf.modulePullback B S hS 𝒳).map φ) := by
  let P := SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl (FlatFppf.objectProperty B S hS 𝒳)))
  have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (P.map φ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨⟨x, hx⟩⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    exact h x hx
  exact (NatIso.isIso_map_iff (FlatFppf.modulePullbackRestrictionIso B S hS 𝒳) φ).2
    (isIso_of_reflects_iso (P.map φ) (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _))

include adj in
/-- **A coherator inverts every map which becomes an isomorphism on the flat-fppf site, between
modules with quasi-coherent restriction to it.** The adjunction maps of source and target become
isomorphisms there (**Stacks 07B1**), so by naturality so does `i (Q k)`; and
`QCoh(𝒪_𝒳) → Mod(𝒪_{𝒳_{flat,fppf}})` is fully faithful. -/
theorem isIso_map_of_isIso_modulePullback_map {A A' : fppfModules B S hS 𝒳} (k : A ⟶ A')
    (hA : ((FlatFppf.modulePullback B S hS 𝒳).obj A).IsQuasicoherentOnSite)
    (hA' : ((FlatFppf.modulePullback B S hS 𝒳).obj A').IsQuasicoherentOnSite)
    (hk : IsIso ((FlatFppf.modulePullback B S hS 𝒳).map k)) : IsIso (Q.map k) := by
  let r := FlatFppf.modulePullback B S hS 𝒳
  have := isIso_modulePullback_map_counit_app_of_isQuasicoherentOnSite B S hS 𝒳 adj A hA
  have := isIso_modulePullback_map_counit_app_of_isQuasicoherentOnSite B S hS 𝒳 adj A' hA'
  have hn := adj.counit.naturality k
  have hr : r.map ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι.map (Q.map k)) ≫ r.map (adj.counit.app A') =
      r.map (adj.counit.app A) ≫ r.map k := by
    have h1 := congrArg r.map hn
    simp only [Functor.comp_map, Functor.id_map] at h1
    exact (r.map_comp _ _).symm.trans (h1.trans (r.map_comp _ _))
  have : IsIso (r.map ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι.map (Q.map k)) ≫ r.map (adj.counit.app A')) := by
    rw [hr]
    infer_instance
  have : IsIso (r.map ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι.map (Q.map k))) :=
    IsIso.of_isIso_comp_right _ (r.map (adj.counit.app A'))
  exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
    (fullyFaithfulQuasicoherentInclusionCompModulePullback B S hS 𝒳) _ _ (Q.map k) this

end Coherator

/-! ### Modules cartesian along flat arrows between affine objects -/

/-- A sheaf of `𝒪_𝒳`-modules on `𝒳_fppf` is *cartesian along flat arrows between affine
objects* when its base-change map along every arrow between objects over affine schemes which
lies over a flat morphism of schemes is an isomorphism. Every object of `LQCoh^fbc(𝒪_𝒳)` is such
a module (**Stacks 0779**, the step R2 of its proof). -/
def IsCartesianAlongFlatAffine (M : fppfModules B S hS 𝒳) : Prop :=
  ∀ ⦃z x : 𝒳.val.val.obj⦄ (φ : z ⟶ x),
    Flat (B.inclusion.map (𝒳.val.val.p.map φ).left) →
    IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z) →
    IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x) →
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj) M.val φ.op)

/-- The pullback to the flat-fppf site of a module cartesian along flat arrows between affine
objects is quasi-coherent (the step GT of the proof of **Stacks 0779**, with the criterion of
quasi-coherence on the flat-fppf site by cartesian-ness between affine objects). -/
theorem FlatFppf.isQuasicoherentOnSite_modulePullback_of_isCartesianAlongFlatAffine
    (M : fppfModules B S hS 𝒳) (hM : IsCartesianAlongFlatAffine B S hS 𝒳 M) :
    ((FlatFppf.modulePullback B S hS 𝒳).obj M).IsQuasicoherentOnSite :=
  FlatFppf.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine B S hS 𝒳 _
    fun _ _ f hy hy' => FlatFppf.isIso_restrictionBaseChange_modulePullback B S hS M hM f hy hy'

/-- The pullback of sheaves of modules to the flat-fppf site preserves colimits. -/
instance FlatFppf.preservesColimitsOfSize_modulePullback :
    PreservesColimitsOfSize.{u, u} (FlatFppf.modulePullback B S hS 𝒳) :=
  (RingedToposHom.pullbackAdjPushforwardModules (subsiteRingedToposHom B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl
      (FlatFppf.objectProperty B S hS 𝒳))).leftAdjoint_preservesColimits

/-- The pullback of sheaves of modules to the flat-fppf site preserves limits. -/
instance FlatFppf.preservesLimitsOfSize_modulePullback :
    PreservesLimitsOfSize.{u, u} (FlatFppf.modulePullback B S hS 𝒳) :=
  (FlatFppf.moduleLowerShriekAdjunction B S hS 𝒳).rightAdjoint_preservesLimits

/-- The pullback of sheaves of modules to the flat-fppf site is additive. -/
instance FlatFppf.additive_modulePullback : (FlatFppf.modulePullback B S hS 𝒳).Additive :=
  RingedToposHom.pullbackModules_additive (subsiteRingedToposHom B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl (FlatFppf.objectProperty B S hS 𝒳))

/-! ### Stacks 0779 for modules cartesian along flat arrows between affine objects -/

section Cartesian

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable {Q : fppfModules B S hS 𝒳 ⥤ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).FullSubcategory}
  (adj : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).ι ⊣ Q)

/-- The restriction to the flat-fppf site inverts the counit of a coherator at every module
cartesian along flat arrows between affine objects. -/
theorem isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine
    (F : fppfModules B S hS 𝒳) (hF : IsCartesianAlongFlatAffine B S hS 𝒳 F) :
    IsIso ((FlatFppf.modulePullback B S hS 𝒳).map (adj.counit.app F)) :=
  isIso_modulePullback_map_counit_app_of_isQuasicoherentOnSite B S hS 𝒳 adj F
    (FlatFppf.isQuasicoherentOnSite_modulePullback_of_isCartesianAlongFlatAffine B S hS 𝒳 F hF)

/-- The pullback of sheaves of modules to the flat-fppf site is a left adjoint, of the
pushforward (**Stacks 03D7**). -/
instance FlatFppf.isLeftAdjoint_modulePullback :
    (FlatFppf.modulePullback B S hS 𝒳).IsLeftAdjoint :=
  (RingedToposHom.pullbackAdjPushforwardModules (subsiteRingedToposHom B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl (FlatFppf.objectProperty B S hS 𝒳))).isLeftAdjoint

include adj in
/-- **Stacks 0779** (1), for a module cartesian along flat arrows between affine objects: the
coherator kills it exactly when it is parasitic. -/
theorem isZero_obj_iff_isParasitic_of_isCartesianAlongFlatAffine (F : fppfModules B S hS 𝒳)
    (hF : IsCartesianAlongFlatAffine B S hS 𝒳 F) :
    IsZero (Q.obj F) ↔ IsParasitic B S hS 𝒳 .fppf F.val :=
  (Adjunction.isZero_obj_iff_isZero_map_obj_of_isIso adj (FlatFppf.modulePullback B S hS 𝒳) F
    (isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine B S hS 𝒳 adj F hF)).trans
    (FlatFppf.isParasitic_iff_isZero_modulePullback B S hS 𝒳 F).symm

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0779** (2), the kernel, for a module cartesian along flat arrows between affine
objects: the kernel of the counit `Q(𝓕) ⟶ 𝓕` is parasitic. -/
theorem isParasitic_kernel_counit_of_isCartesianAlongFlatAffine (F : fppfModules B S hS 𝒳)
    (hF : IsCartesianAlongFlatAffine B S hS 𝒳 F) :
    IsParasitic B S hS 𝒳 .fppf (kernel (adj.counit.app F)).val :=
  have := isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine B S hS 𝒳 adj F hF
  (FlatFppf.isParasitic_iff_isZero_modulePullback B S hS 𝒳 _).2
    ((isZero_kernel_of_mono _).of_iso
      (PreservesKernel.iso (FlatFppf.modulePullback B S hS 𝒳) (adj.counit.app F)))

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0779** (2), the cokernel, for a module cartesian along flat arrows between affine
objects: the cokernel of the counit `Q(𝓕) ⟶ 𝓕` is parasitic. -/
theorem isParasitic_cokernel_counit_of_isCartesianAlongFlatAffine (F : fppfModules B S hS 𝒳)
    (hF : IsCartesianAlongFlatAffine B S hS 𝒳 F) :
    IsParasitic B S hS 𝒳 .fppf (cokernel (adj.counit.app F)).val :=
  have := isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine B S hS 𝒳 adj F hF
  (FlatFppf.isParasitic_iff_isZero_modulePullback B S hS 𝒳 _).2
    ((isZero_cokernel_of_epi _).of_iso
      (PreservesCokernel.iso (FlatFppf.modulePullback B S hS 𝒳) (adj.counit.app F)))

include adj in
/-- **Stacks 0779** (3), colimits, for a full subcategory of modules cartesian along flat arrows
between affine objects whose colimits are computed in `Mod(𝒪_𝒳)`: the coherator restricted to it
preserves them. -/
theorem preservesColimitsOfShape_ι_comp_of_isCartesianAlongFlatAffine
    (P : ObjectProperty (fppfModules B S hS 𝒳))
    (hP : ∀ F, P F → IsCartesianAlongFlatAffine B S hS 𝒳 F) (J : Type u) [Category.{u} J]
    [PreservesColimitsOfShape J P.ι] : PreservesColimitsOfShape J (P.ι ⋙ Q) :=
  have : PreservesColimitsOfShape J
      (show fppfModules B S hS 𝒳 ⥤ _ from FlatFppf.modulePullback B S hS 𝒳) :=
    (FlatFppf.preservesColimitsOfSize_modulePullback B S hS 𝒳).preservesColimitsOfShape
  Adjunction.preservesColimitsOfShape_ι_comp_of_isIso adj (FlatFppf.modulePullback B S hS 𝒳) P
    (fun F hF => isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine B S hS 𝒳 adj F
      (hP F hF)) J

end Cartesian

/-! ### `LQCoh^fbc(𝒪_𝒳)` -/

section LQCoh

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  {Q : fppfModules B S hS 𝒳 ⥤ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).FullSubcategory}
  (adj : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).ι ⊣ Q)

/-- The inclusion of `LQCoh^fbc(𝒪_𝒳)` into `Mod(𝒪_𝒳)` preserves colimits of `u`-small shapes,
`LQCoh^fbc(𝒪_𝒳)` being closed under them (**Stacks 0771** (5)). -/
instance preservesColimitsOfShape_lqcohSheafFbcFppfModules_ι (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι :=
  inferInstance

/-- The inclusion of `LQCoh^fbc(𝒪_𝒳)` into `Mod(𝒪_𝒳)` is right exact. -/
instance preservesFiniteColimits_lqcohSheafFbcFppfModules_ι :
    PreservesFiniteColimits (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι :=
  preservesFiniteColimits_of_preservesFiniteColimitsOfSize.{u} _ fun _ _ _ => inferInstance

end LQCoh

end AlgebraicGeometry.Stack

end

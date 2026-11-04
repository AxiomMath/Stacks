module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModules
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Stackification
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModulesExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationExtensions
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceExtensions

/-!
# Modules on a stackification at general universes

For a 1-morphism `f : 𝒳 ⥤ 𝒴` of categories fibred in groupoids that induces an equivalence of
stackifications, the inverse image `f^*` is an equivalence on sheaves of modules and on
quasi-coherent modules, with the fibred categories in arbitrary universes.

These declarations extend `StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModules`
and are kept in their own module so that the base file is unchanged.

## Main definitions

* `quasicoherentPullback_univ`: The inverse image of quasi-coherent modules along a 1-morphism
  of categories fibred in groupoids.

## Main results

* `isEquivalence_modulePullback_of_isStackificationEquivalence'`: `f^*` is an equivalence of
  categories of sheaves of modules.
* `isEquivalence_quasicoherentPullback_of_isStackificationEquivalence'`: `f^*` is an
  equivalence of categories of quasi-coherent modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

/-! ### Stacks 06WR at the universes of Stacks 06WH

The primed declarations below are the statements of the unprimed section after them with the two
fibred categories having their objects in `Type v` and their morphisms in `Type w`, both
independent of the universe `u` of the rings of the big fppf site, and with the module universe
`max u v w m`; the unprimed statements are derived from them at `v = w = m = u`. Nothing ties the
morphisms of `𝒳` and `𝒴` to the morphisms of the base: the Comparison Lemma for sheaves of
modules is available with the universe of the coefficient rings independent of the module
universe, `Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction'`, and the morphism
presheaves of Stacks 02ZB that
`CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence'` speaks of tie together
only the hom universes of source and target. The module universe is `max u v w m` because the
abelian input `(f.sheafPushforwardContinuous AddCommGrpCat.{max u v w m} _ _)` needs
`AddCommGrpCat.{max u v w m}` to have limits over the comma categories of `f.op`, whose objects
lie in `Type (max v w)`; that is the same bound Stacks 06WH carries. -/

universe v w m u₁ v₁ u₂ v₂

section DenseSubsiteOfUniv

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Restriction of sheaves of modules along a dense subsite inclusion `v` is an equivalence
when the coefficient sheaf of rings downstairs is, as a presheaf, the restriction along `v` of
the one upstairs.

This is the Comparison Lemma for sheaves of modules,
`Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction'`, with the coefficient
identification carried by a `CategoryTheory.eqToHom` instead of by an identity: the two sheaves
of rings are equal, by `CategoryTheory.ObjectProperty.FullSubcategory.ext`, so the structure
map is the identity after that substitution. -/
theorem isEquivalence_pushforward_eqToHom' (G : C ⥤ D) [G.IsDenseSubsite J K]
    [(G.sheafPushforwardContinuous AddCommGrpCat.{m} J K).IsEquivalence]
    (T : Sheaf J RingCat.{u}) (R : Sheaf K RingCat.{u}) (h : T.obj = G.op ⋙ R.obj) :
    (SheafOfModules.pushforward.{m}
      (⟨eqToHom h⟩ : T ⟶
        (G.sheafPushforwardContinuous RingCat.{u} J K).obj R)).IsEquivalence := by
  obtain rfl : T = (G.sheafPushforwardContinuous RingCat.{u} J K).obj R :=
    ObjectProperty.FullSubcategory.ext h
  exact Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction'
    (J := J) (K := K) (v := G) (R := R)

end DenseSubsiteOfUniv

/-- A 1-morphism inducing an equivalence of stackifications is a dense subsite inclusion for the
associated topologies. -/
private theorem isDenseSubsite_associatedTopology_of_isStackificationEquivalence'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    f.IsDenseSubsite (associatedTopology B S hS p B.topology)
      (associatedTopology B S hS q B.topology) :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  hF.isDenseSubsite_of_isStackificationEquivalence' (BigFppfOver.topology B S hS) hp hq heq

/-- **Stacks 06WR, the `Mod` clause.** Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`. If `f` induces an equivalence of stackifications,
then the inverse image of sheaves of modules of Stacks 06WE is an equivalence
`Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)`.

Equivalence of stackifications makes `f` a dense subsite inclusion for the associated fppf
topologies, by the engine of Stacks 06WQ; the structure sheaf of `𝒳` is the restriction along
`f` of that of `𝒴`, so the inverse image *is* restriction of sections, and the Comparison
Lemma for sheaves of modules applies. -/
theorem isEquivalence_modulePullback_of_isStackificationEquivalence'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    (modulePullback.{u, v, w, max u v w m, v, w} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).IsEquivalence := by
  have := isDenseSubsite_associatedTopology_of_isStackificationEquivalence' B S hS p q hp hq f hF
    heq
  exact isEquivalence_pushforward_eqToHom'.{u, max u v w m, v, w, v, w} f _ _
    (ringStructureSheafCore_obj_eq B S hS p q hp hq f hF.comp_eq B.topology le_rfl)

section QuasicoherentOfUniv

/-- **Quasi-coherence is reflected by `f^*`**, for a 1-morphism whose source structure functor
is literally the composite `f ⋙ q`.

Every object of `𝒴` is covered by images of objects of `𝒳`, because `f` is cover dense, so by
Stacks 03DN at clause (6) it suffices that `𝓖|_{𝒴/f x}` be quasi-coherent for each `x`. The
localization of `f` at `x` is an equivalence of sites `𝒳/x ≌ 𝒴/f x` — Stacks 06W0 gives the
equivalence of categories, and the correspondence of coverings is that both topologies are
inherited from the base — it matches the structure sheaves, and it carries `𝓖|_{𝒴/f x}` to
`(f^*𝓖)|_{𝒳/x}`; quasi-coherence is intrinsic to a ringed site up to such an equivalence,
which is Stacks 03DM at clause (6).

Writing the source structure functor as `f ⋙ q` is what makes the last identification an
equality of terms rather than a transport: the structure sheaf of `𝒳` is then the restriction
along `f` of that of `𝒴` by `CategoryTheory.Functor.op_comp`, so the scalar comparison in the
inverse image is an `CategoryTheory.eqToHom` on a reflexive equation.
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_modulePullback_univ` removes the restriction. -/
private theorem isQuasicoherentOnSite_of_modulePullback_comp'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
    (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hF : (f ⋙ q).IsFibredOneMorphism q f)
    (heq : letI : (f ⋙ q).IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS))
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    (hM : ((modulePullback.{u, v, w, m, v, w} B S hS (f ⋙ q) q hp hq f hF.comp_eq
      B.topology le_rfl).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  let J := associatedTopology B S hS (f ⋙ q) B.topology
  let K := associatedTopology B S hS q B.topology
  let : f.IsDenseSubsite J K :=
    isDenseSubsite_associatedTopology_of_isStackificationEquivalence' B S hS (f ⋙ q) q hp hq f hF
      heq
  let : f.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K f
  have hslice : ∀ U : 𝒳, (Over.post (X := U) f).IsEquivalence := by
    intro U
    let r := q ⋙ Over.forget (B.obj hS)
    have : (Over.post (X := f.obj U) r).IsEquivalence :=
      isEquivalence_overPost B S hS q hq (f.obj U)
    have : (Over.post (X := U) (f ⋙ r)).IsEquivalence :=
      isEquivalence_overPost B S hS (f ⋙ q) hp U
    have : (Over.post (X := U) f ⋙ Over.post r).IsEquivalence := by
      rw [← Over.post_comp]
      infer_instance
    exact Functor.isEquivalence_of_comp_right (Over.post f) (Over.post r)
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite']
  refine ⟨𝒳, fun x => f.obj x, ?_, fun x => ?_⟩
  · intro W
    refine K.superset_covering ?_ (Functor.is_cover_of_isCoverDense f K W)
    intro V g hg
    rw [Sieve.mem_ofObjects_iff]
    obtain ⟨⟨x, l, _, _⟩⟩ := hg
    exact ⟨x, ⟨l⟩⟩
  · let : (Over.post (X := x) f).IsEquivalence := hslice x
    let : (Over.post (X := x) f).IsDenseSubsite (J.over x) (K.over (f.obj x)) :=
      { functorPushforward_mem_iff := by
          intro Z T
          rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
            Sieve.overEquiv_functorPushforward_post]
          exact f.functorPushforward_mem_iff J K }
    let : ((Over.post (X := x) f).asEquivalence.symm).inverse.IsDenseSubsite
        (J.over x) (K.over (f.obj x)) :=
      inferInstanceAs ((Over.post (X := x) f).IsDenseSubsite _ _)
    let : ((Over.post (X := x) f).asEquivalence).inverse.IsDenseSubsite
        (K.over (f.obj x)) (J.over x) :=
      inferInstanceAs
        (((Over.post (X := x) f).asEquivalence.symm).functor.IsDenseSubsite _ _)
    exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex'
      (J' := J.over x) (Over.post (X := x) f).asEquivalence
      ((ringStructureSheafCore B S hS q hq B.topology le_rfl).over (f.obj x))
      (M.over (f.obj x))
      (Stacks.SheafOfModules.isQuasicoherent_over _ hM x)

/-- **Quasi-coherence is reflected by `f^*`** when `f` induces an equivalence of
stackifications. This is the content of Stacks 06WR beyond Stacks 06WH: the inverse image of a
quasi-coherent module is quasi-coherent by Stacks 06WH, and conversely a module whose inverse
image is quasi-coherent is itself quasi-coherent. -/
theorem isQuasicoherentOnSite_of_modulePullback_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS))
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    (hM : ((modulePullback.{u, v, w, m, v, w} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  obtain rfl := hF.comp_eq
  exact isQuasicoherentOnSite_of_modulePullback_comp' B S hS q hq f hp hF heq M hM

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)

/-- `QCoh(𝒪_𝒳)` of Stacks 06WG, with its coefficient sheaf of rings written in the spelling the
inverse image of Stacks 06WE uses. The fppf structure sheaf of a category fibred in groupoids
has the same presheaf however the fppf topology is selected, so the two full subcategories are
the same category, not merely equivalent ones. -/
theorem quasicoherentModules_eq' :
    FibredSite.quasicoherentModules.{u, v, w, max u v w m} B S hS p hp =
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS p hp B.topology le_rfl)).FullSubcategory := rfl

/-- The inverse image of quasi-coherent modules along a 1-morphism of categories fibred in
groupoids: the inverse image of sheaves of modules of Stacks 06WE, which preserves
quasi-coherence by Stacks 06WH, lifted to the full subcategories `QCoh` of Stacks 06WG. -/
noncomputable def quasicoherentPullback_univ :
    (SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS q hq B.topology le_rfl)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS p hp B.topology le_rfl)).FullSubcategory :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherentOnSite.{v, w, u, max u v w m}
        (ringStructureSheafCore B S hS q hq B.topology le_rfl)).ι ⋙
      modulePullback.{u, v, w, max u v w m, v, w} B S hS p q hp hq f hF.comp_eq B.topology le_rfl)
    fun M => isQuasicoherentOnSite_modulePullback.{u, v, w, m} B S hS p q hp hq f hF.comp_eq
      M.obj

/-- **Stacks 06WR, the `QCoh` clause.** If `f : 𝒳 ⥤ 𝒴` induces an equivalence of
stackifications, then the inverse image of quasi-coherent modules is an equivalence
`QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`.

Fullness and faithfulness come from the equivalence on all modules, since `QCoh` is a full
subcategory; essential surjectivity needs in addition that `f^*` reflects quasi-coherence,
which is `AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_modulePullback_univ`. -/
theorem isEquivalence_quasicoherentPullback_of_isStackificationEquivalence'
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    (quasicoherentPullback_univ.{u, v, w, m} B S hS p q hp hq f hF).IsEquivalence := by
  have hL := isEquivalence_modulePullback_of_isStackificationEquivalence'.{u, v, w, m}
    B S hS p q hp hq f hF heq
  have : (quasicoherentPullback_univ.{u, v, w, m} B S hS p q hp hq f hF).Faithful := by
    unfold quasicoherentPullback_univ
    infer_instance
  have : (quasicoherentPullback_univ.{u, v, w, m} B S hS p q hp hq f hF).Full := by
    unfold quasicoherentPullback_univ
    infer_instance
  have : (quasicoherentPullback_univ.{u, v, w, m} B S hS p q hp hq f hF).EssSurj := by
    refine ⟨fun N => ?_⟩
    have e := (modulePullback.{u, v, w, max u v w m, v, w} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).objObjPreimageIso N.obj
    exact ⟨⟨_, isQuasicoherentOnSite_of_modulePullback_univ B S hS p q hp hq f hF heq _
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm N.property)⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩
  exact Functor.IsEquivalence.mk

end QuasicoherentOfUniv

section DenseSubsite

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

end DenseSubsite

section Quasicoherent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u} [Category.{u} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)

end Quasicoherent

end AlgebraicGeometry.Stack

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Stackification
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Stackification and sheaves of modules (Stacks 06WR)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of a scheme `S`. If `f` induces an equivalence of stackifications, then the inverse image
`f^*` of Stacks 06WE is an equivalence `Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)`.

Inducing an equivalence of stackifications is
`CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence`, the two local
criteria of Stacks 02ZN, and what it gives is that `f` is a dense subsite inclusion for the
associated topologies of Stacks 06TP
(`CategoryTheory.Functor.IsFibredOneMorphism.isDenseSubsite_of_isStackificationEquivalence`,
the engine of Stacks 06WQ). The Comparison Lemma for sheaves of modules on a dense subsite,
`Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction`, then applies: restriction of
sections along `f` is an equivalence onto the sheaves of modules over the restricted sheaf of
rings, and the structure sheaf of `𝒳` *is* the restriction along `f` of the structure sheaf of
`𝒴` (`AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq`), so the restricted coefficient
ring needs no comparison map beyond a `CategoryTheory.eqToHom`.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_pushforward_eqToHom`: on a dense subsite whose
  Comparison Lemma for abelian sheaves holds, restriction of sheaves of modules along a
  tautological identification of the coefficient rings is an equivalence.
* `AlgebraicGeometry.Stack.isEquivalence_modulePullback_of_isStackificationEquivalence`:
  **Stacks 06WR for `Mod`.**

## Implementation notes

The source writes the two induced equivalences as `Mod(𝒪_𝒳) → Mod(𝒪_𝒴)` and
`QCoh(𝒪_𝒳) → QCoh(𝒪_𝒴)`, which is the opposite of the direction of `f^*`: the pullback
functor of Stacks 06WH, which is the one the lemma names, goes
`Mod(𝒪_𝒴) → Mod(𝒪_𝒳)`. The functor displayed here is that pullback,
`AlgebraicGeometry.Stack.modulePullback`; an equivalence in one direction is an equivalence in
the other, so no content is changed.

The hypothesis is kept at `CategoryTheory.Functor.IsFiberedInGroupoids`, as in the source, not
strengthened to an algebraic stack: the dense-subsite input and the Comparison Lemma both need
only fibredness in groupoids.

The two categories are taken in `Type u` with morphisms in `Type u`, the universe of the rings
of the big fppf site. This is what the Comparison Lemma for sheaves of modules needs: it is
stated for a module universe equal to the universe of the coefficient rings, and its abelian
input `(f.sheafPushforwardContinuous AddCommGrpCat.{u} _ _).IsEquivalence` needs
`AddCommGrpCat.{u}` to have limits over the comma categories of `f.op`, which bounds the
objects of `𝒳` by `u`. Every algebraic stack is essentially small in that universe
(`AlgebraicGeometry.essentiallySmall_obj_algebraicStack`), so this is the small-site form of
the statement rather than a restriction on which fibred categories it is about.

## References

* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
* [Stacks Project, Tag 06WQ](https://stacks.math.columbia.edu/tag/06WQ)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

section DenseSubsite

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Restriction of sheaves of modules along a dense subsite inclusion `v` is an equivalence
when the coefficient sheaf of rings downstairs is, as a presheaf, the restriction along `v` of
the one upstairs.

This is the Comparison Lemma for sheaves of modules,
`Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction`, with the coefficient
identification carried by a `CategoryTheory.eqToHom` instead of by an identity: the two sheaves
of rings are equal, by `CategoryTheory.ObjectProperty.FullSubcategory.ext`, so the structure
map is the identity after that substitution. -/
theorem isEquivalence_pushforward_eqToHom (v : C ⥤ D) [v.IsDenseSubsite J K]
    [(v.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsEquivalence]
    (T : Sheaf J RingCat.{u}) (R : Sheaf K RingCat.{u}) (h : T.obj = v.op ⋙ R.obj) :
    (SheafOfModules.pushforward.{u}
      (⟨eqToHom h⟩ : T ⟶
        (v.sheafPushforwardContinuous RingCat.{u} J K).obj R)).IsEquivalence := by
  obtain rfl : T = (v.sheafPushforwardContinuous RingCat.{u} J K).obj R :=
    ObjectProperty.FullSubcategory.ext h
  exact Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction
    (J := J) (K := K) (v := v) (R := R)

end DenseSubsite

/-- A 1-morphism inducing an equivalence of stackifications is a dense subsite inclusion for the
associated topologies. -/
private theorem isDenseSubsite_associatedTopology_of_isStackificationEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u} [Category.{u} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence (BigFppfOver.topology B S hS)) :
    f.IsDenseSubsite (associatedTopology B S hS p B.topology)
      (associatedTopology B S hS q B.topology) :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  hF.isDenseSubsite_of_isStackificationEquivalence (BigFppfOver.topology B S hS) hp hq heq

/-- **Stacks 06WR, the `Mod` clause.** Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`. If `f` induces an equivalence of stackifications,
then the inverse image of sheaves of modules of Stacks 06WE is an equivalence
`Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)`.

Equivalence of stackifications makes `f` a dense subsite inclusion for the associated fppf
topologies, by the engine of Stacks 06WQ; the structure sheaf of `𝒳` is the restriction along
`f` of that of `𝒴`, so the inverse image *is* restriction of sections, and the Comparison
Lemma for sheaves of modules applies. -/
@[stacks 06WR "modules"]
theorem isEquivalence_modulePullback_of_isStackificationEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u} [Category.{u} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence (BigFppfOver.topology B S hS)) :
    (modulePullback.{u, u, u, u, u, u} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).IsEquivalence := by
  have := isDenseSubsite_associatedTopology_of_isStackificationEquivalence B S hS p q hp hq f hF heq
  exact isEquivalence_pushforward_eqToHom f _ _
    (ringStructureSheafCore_obj_eq B S hS p q hp hq f hF.comp_eq B.topology le_rfl)

section Quasicoherent

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
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_modulePullback` removes the restriction. -/
private theorem isQuasicoherentOnSite_of_modulePullback_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u} [Category.{u} 𝒴]
    (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hF : (f ⋙ q).IsFibredOneMorphism q f)
    (heq : letI : (f ⋙ q).IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence (BigFppfOver.topology B S hS))
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    (hM : ((modulePullback.{u, u, u, u, u, u} B S hS (f ⋙ q) q hp hq f hF.comp_eq
      B.topology le_rfl).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  let J := associatedTopology B S hS (f ⋙ q) B.topology
  let K := associatedTopology B S hS q B.topology
  have : f.IsDenseSubsite J K :=
    isDenseSubsite_associatedTopology_of_isStackificationEquivalence B S hS (f ⋙ q) q hp hq f hF heq
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
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite]
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
    exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex
      (J' := J.over x) (Over.post (X := x) f).asEquivalence
      ((ringStructureSheafCore B S hS q hq B.topology le_rfl).over (f.obj x))
      (M.over (f.obj x))
      (Stacks.SheafOfModules.isQuasicoherent_over _ hM x)

/-- **Quasi-coherence is reflected by `f^*`** when `f` induces an equivalence of
stackifications. This is the content of Stacks 06WR beyond Stacks 06WH: the inverse image of a
quasi-coherent module is quasi-coherent by Stacks 06WH, and conversely a module whose inverse
image is quasi-coherent is itself quasi-coherent. -/
theorem isQuasicoherentOnSite_of_modulePullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u} [Category.{u} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence (BigFppfOver.topology B S hS))
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    (hM : ((modulePullback.{u, u, u, u, u, u} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  obtain rfl := hF.comp_eq
  exact isQuasicoherentOnSite_of_modulePullback_comp B S hS q hq f hp hF heq M hM

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u} [Category.{u} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)

/-- `QCoh(𝒪_𝒳)` of Stacks 06WG, with its coefficient sheaf of rings written in the spelling the
inverse image of Stacks 06WE uses. The fppf structure sheaf of a category fibred in groupoids
has the same presheaf however the fppf topology is selected, so the two full subcategories are
the same category, not merely equivalent ones. -/
theorem quasicoherentModules_eq :
    FibredSite.quasicoherentModules.{u, u, u, u} B S hS p hp =
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS p hp B.topology le_rfl)).FullSubcategory := rfl

/-- The inverse image of quasi-coherent modules along a 1-morphism of categories fibred in
groupoids: the inverse image of sheaves of modules of Stacks 06WE, which preserves
quasi-coherence by Stacks 06WH, lifted to the full subcategories `QCoh` of Stacks 06WG. -/
noncomputable def quasicoherentPullback :
    (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS q hq B.topology le_rfl)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS p hp B.topology le_rfl)).FullSubcategory :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS q hq B.topology le_rfl)).ι ⋙
      modulePullback.{u, u, u, u, u, u} B S hS p q hp hq f hF.comp_eq B.topology le_rfl)
    fun M => isQuasicoherentOnSite_modulePullback B S hS p q hp hq f hF.comp_eq M.obj

/-- **Stacks 06WR, the `QCoh` clause.** If `f : 𝒳 ⥤ 𝒴` induces an equivalence of
stackifications, then the inverse image of quasi-coherent modules is an equivalence
`QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`.

Fullness and faithfulness come from the equivalence on all modules, since `QCoh` is a full
subcategory; essential surjectivity needs in addition that `f^*` reflects quasi-coherence,
which is `AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_modulePullback`. -/
@[stacks 06WR "quasi-coherent modules"]
theorem isEquivalence_quasicoherentPullback_of_isStackificationEquivalence
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence (BigFppfOver.topology B S hS)) :
    (quasicoherentPullback B S hS p q hp hq f hF).IsEquivalence := by
  have hL := isEquivalence_modulePullback_of_isStackificationEquivalence B S hS p q hp hq f hF heq
  have := hL.faithful
  have := hL.full
  have := hL.essSurj
  have hfaithful : (quasicoherentPullback B S hS p q hp hq f hF).Faithful := by
    unfold quasicoherentPullback
    infer_instance
  have hfull : (quasicoherentPullback B S hS p q hp hq f hF).Full := by
    unfold quasicoherentPullback
    infer_instance
  have hess : (quasicoherentPullback B S hS p q hp hq f hF).EssSurj := by
    refine ⟨fun N => ?_⟩
    let e := (modulePullback.{u, u, u, u, u, u} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).objObjPreimageIso N.obj
    exact ⟨⟨_, isQuasicoherentOnSite_of_modulePullback B S hS p q hp hq f hF heq _
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm N.property)⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩
  exact Functor.IsEquivalence.mk

end Quasicoherent

end AlgebraicGeometry.Stack

end

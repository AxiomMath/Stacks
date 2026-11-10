module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitRelations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations
import StacksCore.Tactic.StacksAttribute

/-!
# `f^{-1} = (u_p -)^#`: the sheafification bridge for a morphism of sites

Let `u : D ⥤ C` be a continuous functor between sites `(D, K)` and `(C, J)`, representing a
morphism of sites `f : C → D`.  `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimit`
and its `...Adjunction` companion build the *presheaf*-level pullback `u_p` of Stacks 00VC
from the colimit formula `(u_p G)(U) = colim_{(V, φ) ∈ I^u_U} G(V)` and identify it with
Mathlib's abstract presheaf-level pullback.  The proof of Stacks 05VD, however, works with
`f^{-1}`, which is the *sheafification* of `u_p`, and with a structure map
`f^# : f^{-1} O_D ⟶ O_C` rather than with the Kan-extension unit.

This file crosses that gap.  The unit that `u_p` provides is a morphism of *presheaves*,
`O ⟶ u.op ⋙ u_p O`, whereas both `SheafOfModules.pullback` and the source's `f^*` are taken
along a morphism of *sheaves*.  So the object to build is the sheaf-level unit
`upSheafUnit : O ⟶ f_* ((u_p O)^#)`, and the fact to prove is that **every** structure map
`α : O ⟶ f_* R` factors through it — which is what identifies `(u_p O)^#` with `f^{-1} O` and
exhibits `f^#` as the second factor.

Everything up to and including that factorization is independent of the target category, so it
is stated for an arbitrary `A` and specialises to `RingCat` and to `CommRingCat` with no
further work.  The module-level statements that follow are at `RingCat`, where `u_p` on
presheaves of modules lives.

## Main definitions

* `Stacks.ModuleUp.upSheaf`: `(u_p O)^#`, the sheafification of the presheaf-level pullback.
* `Stacks.ModuleUp.upSheafify`: the sheafification unit `u_p O ⟶ (u_p O)^#`.
* `Stacks.ModuleUp.upSheafUnit`: the **sheaf**-level unit `O ⟶ f_* ((u_p O)^#)`, i.e. the
  morphism of sheaves that `SheafOfModules.pullback` takes as its argument.
* `Stacks.ModuleUp.structureDescent`: the descent `f^# : (u_p O)^# ⟶ R` of a structure map
  `α : O ⟶ f_* R`.
* `Stacks.ModuleUp.upSheafIso`: the identification `f^{-1} O ≅ (u_p O)^#` of Mathlib's
  abstract inverse image with the sheafified colimit formula.
* `Stacks.ModuleUp.upSheafifyRing`: the sheafification unit of the structure ring, written at
  the two spellings the module-level statements need.
* `Stacks.ModuleUp.upModulePullbackIso`, `Stacks.ModuleUp.upModuleSheafPullbackIso`:
  `f^{-1} F = (u_p F)^#` on presheaves and on sheaves of modules.
* `Stacks.ModuleUp.pullbackFactorization`: the factorization of the pullback of sheaves of
  modules as an inverse image followed by a change of rings.

## Main results

* `Stacks.ModuleUp.upSheafUnit_comp_structureDescent`: **the factorization**
  `α = upSheafUnit ≫ f_* (structureDescent α)`.  This is the statement that makes `(u_p O)^#`
  the inverse image: the sheaf-level unit is universal among structure maps.
* `Stacks.ModuleUp.upSheafify_comp_structureDescent`: the presheaf-level half of it, i.e. that
  `f^#` restricted along the sheafification unit is the Kan-extension descent.
* `Stacks.ModuleUp.hasLocalRelationFactorizations_of_sheaf`: the sheaf-level local equational
  criterion of Stacks 08FC part (2) read at the presheaf-level spelling of
  `SiteUpColimitRelations`, so that `Stacks.ModuleUp.hasLocalRelationFactorizations_up` can
  consume `Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat`.

## Implementation notes

**The universes are forced, not chosen.** `u_p` is built in `SiteUpColimit` for
`C D : Type w` with `[SmallCategory C] [SmallCategory D]`, and Mathlib's
`PresheafOfModules.pullbackObjIsDefined_eq_top` — the only unconditional source of
`(PresheafOfModules.pushforward φ).IsRightAdjoint` — is itself stated for small categories in
`Type u` with `RingCat.{u}`.  The module universe therefore equals the ring universe, which is
also what the statements of Tag 05VD use.

**`IsRightAdjoint` has to be supplied at the sheaf spelling.**
`((u.sheafPushforwardContinuous A K J).obj R).obj` is
`((whiskeringLeft _ _ _).obj u.op).obj R.obj`, which is definitionally but not syntactically
`u.op ⋙ R.obj`.  Mathlib's instance for `(PresheafOfModules.pushforward φ).IsRightAdjoint` is
keyed on the latter, so it does not fire for `η.hom`; `isRightAdjoint_presheafPushforward`
below restates it with the binder written at the sheaf spelling, after which the
`SheafOfModules` instance follows by search.  This is the "one spelling per statement"
discipline of `SiteUpColimitAdjunction`, applied to an instance rather than to a lemma.

**`Functor.lanAdjunction_unit` is not `rfl`.** `(L.lanAdjunction H).unit` and `L.lanUnit` are
proved equal in Mathlib by a `dsimp`/`simp` argument, so a bare `exact` across the two
spellings fails — with a message whose two sides differ only in that one says
`(u.op.lanAdjunction A).unit` and the other `u.op.lanUnit`.  The rewrite is explicit in the
proof of `upSheafUnit_comp_structureDescent`.

**`simpa` breaks the sheafification triangle, `exact` does not.** The proof of
`upSheafify_comp_structureDescent` is a bare composite of `Adjunction.homEquiv_unit` with
`Equiv.apply_symm_apply`.  Routing the same term through `simpa` fails with a type mismatch
whose two sides *print identically*: simp normalises `(sheafificationAdjunction J A).unit.app`
to `toSheafify` in the goal but not inside the supplied term's type.

**The identity-site spelling.** `PresheafOfModules.pullbackComp` composes a pullback along
`F : C ⥤ D` with one along `G : D ⥤ E`; the second step here is a change of rings on a fixed
site, so `G = 𝟭 C` and the hypothesis has to be read at the type
`u_p O ⟶ (𝟭 C).op ⋙ ((u_p O)^#).obj`.  `upSheafifyRing` is that reading, as a `def` with an
ascribed result type — a type *ascription* does not suffice, since `inferType` ignores it.  The
resulting `u ⋙ 𝟭 C` is `u` by `rfl`, so no `eqToHom` enters.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory Limits Functor

universe w

namespace Stacks.ModuleUp

section Generic

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C)
  {K : GrothendieckTopology D} (J : GrothendieckTopology C) [u.IsContinuous K J]
  {A : Type*} [Category.{w} A] [HasWeakSheafify J A]
  [∀ F : Dᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]

/-- `(u_p O)^#`, the sheafification of the presheaf-level pullback of Stacks 00VC. -/
noncomputable def upSheaf (O : Sheaf K A) : Sheaf J A :=
  (presheafToSheaf J A).obj (u.op.lan.obj O.obj)

/-- The sheafification unit `u_p O ⟶ (u_p O)^#`. -/
noncomputable def upSheafify (O : Sheaf K A) :
    u.op.lan.obj O.obj ⟶ (upSheaf u J O).obj :=
  (sheafificationAdjunction J A).unit.app (u.op.lan.obj O.obj)

/-- The underlying morphism of presheaves of the sheaf-level unit: the Kan-extension unit of
Stacks 00VC followed by the sheafification unit. -/
noncomputable def upSheafUnitHom (O : Sheaf K A) :
    O.obj ⟶ u.op ⋙ (upSheaf u J O).obj :=
  u.op.lanUnit.app O.obj ≫ whiskerLeft u.op (upSheafify u J O)

/-- **The sheaf-level unit `O ⟶ f_* ((u_p O)^#)`.**

This is the morphism of *sheaves* that `SheafOfModules.pullback` and the source's `f^*` are
taken along; the Kan-extension unit of `SiteUpColimit` is a morphism of presheaves and cannot
play that role. -/
noncomputable def upSheafUnit (O : Sheaf K A) :
    O ⟶ (u.sheafPushforwardContinuous A K J).obj (upSheaf u J O) :=
  ⟨upSheafUnitHom u J O⟩

/-- **`f^{-1} O = (u_p O)^#`.** Mathlib's abstract inverse image — the left adjoint of the
pushforward — is the sheafification of the colimit formula of Stacks 00VC. -/
noncomputable def upSheafIso (O : Sheaf K A) :
    (u.sheafPullback A K J).obj O ≅ upSheaf u J O :=
  (sheafPullbackConstruction.sheafPullbackIso u A K J).app O

/-- **The descent `f^#` of a structure map.** Given `α : O ⟶ f_* R`, this is the induced
morphism `(u_p O)^# ⟶ R`, obtained from the Kan-extension adjunction followed by the
sheafification adjunction. -/
noncomputable def structureDescent {O : Sheaf K A} {R : Sheaf J A}
    (α : O ⟶ (u.sheafPushforwardContinuous A K J).obj R) :
    upSheaf u J O ⟶ R :=
  ((sheafificationAdjunction J A).homEquiv _ R).symm
    (((u.op.lanAdjunction A).homEquiv O.obj R.obj).symm α.hom)

/-- The unit followed by `G` of the inverse of `homEquiv` recovers the morphism. -/
private theorem unit_comp_map_homEquiv_symm {E : Type*} {F' : Type*} [Category E] [Category F']
    {L : E ⥤ F'} {G : F' ⥤ E} (adj : L ⊣ G) {X : E} {Y : F'} (g : X ⟶ G.obj Y) :
    adj.unit.app X ≫ G.map ((adj.homEquiv X Y).symm g) = g :=
  (adj.homEquiv_unit X Y _).symm.trans ((adj.homEquiv X Y).apply_symm_apply g)

/-- The presheaf-level half of the factorization: `f^#` restricted along the sheafification
unit is the Kan-extension descent of the structure map. -/
lemma upSheafify_comp_structureDescent {O : Sheaf K A} {R : Sheaf J A}
    (α : O ⟶ (u.sheafPushforwardContinuous A K J).obj R) :
    upSheafify u J O ≫ (structureDescent u J α).hom
      = ((u.op.lanAdjunction A).homEquiv O.obj R.obj).symm α.hom :=
  unit_comp_map_homEquiv_symm (sheafificationAdjunction J A) _

/-- **The factorization of a structure map through the sheaf-level unit.**

`α = upSheafUnit ≫ f_* (f^#)`.  This is the statement that makes `(u_p O)^#` *be* the inverse
image `f^{-1} O`: the sheaf-level unit is universal among morphisms `O ⟶ f_* R`.  It is the
step the proof of Stacks 05VD needs in order to pass from its structure map to the colimit
formula of Stacks 00VC. -/
theorem upSheafUnit_comp_structureDescent {O : Sheaf K A} {R : Sheaf J A}
    (α : O ⟶ (u.sheafPushforwardContinuous A K J).obj R) :
    upSheafUnit u J O ≫ (u.sheafPushforwardContinuous A K J).map (structureDescent u J α)
      = α := by
  apply InducedCategory.Hom.ext
  change upSheafUnitHom u J O ≫ whiskerLeft u.op (structureDescent u J α).hom = α.hom
  rw [upSheafUnitHom, Category.assoc, ← whiskerLeft_comp, upSheafify_comp_structureDescent,
    ← Functor.lanAdjunction_unit u.op A]
  exact unit_comp_map_homEquiv_symm (u.op.lanAdjunction A) α.hom

end Generic

section Modules

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C)
  {K : GrothendieckTopology D} (J : GrothendieckTopology C) [u.IsContinuous K J]

/-- `(PresheafOfModules.pushforward η.hom).IsRightAdjoint` **at the sheaf spelling**.

Mathlib's instance is keyed on a morphism of presheaves of rings written `S ⟶ F.op ⋙ R`, while
`η.hom` for a morphism of *sheaves* `η` has target `((whiskeringLeft _ _ _).obj u.op).obj
R.obj`.  The two are definitionally equal and the discrimination tree does not see it, so the
instance is restated here with its binder at the sheaf spelling. -/
instance isRightAdjoint_presheafPushforward {O : Sheaf K RingCat.{w}} {R : Sheaf J RingCat.{w}}
    (η : O ⟶ (u.sheafPushforwardContinuous RingCat.{w} K J).obj R) :
    (PresheafOfModules.pushforward.{w} η.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top η.hom)

variable [RepresentablyFlat u]

/-- The sheafification unit of the structure ring, with its source written at the `upRing`
spelling of `SiteUpColimit` and its target at the identity-site spelling of
`PresheafOfModules.pullbackComp`.

Both crossings are definitional and neither is syntactic, which is why this is a `def` with an
ascribed result type: the statements below then mention one spelling only. -/
noncomputable def upSheafifyRing (O : Sheaf K RingCat.{w}) :
    upRing u O.obj ⟶ (𝟭 C).op ⋙ (upSheaf u J (A := RingCat.{w}) O).obj :=
  upSheafify u J O

/-- Pushforward of presheaves of modules along `upSheafifyRing u J O` is a right adjoint. -/
instance isRightAdjoint_pushforward_upSheafifyRing (O : Sheaf K RingCat.{w}) :
    (PresheafOfModules.pushforward.{w} (upSheafifyRing u J O)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (upSheafifyRing u J O))

/-- **`f^{-1} F = (u_p F)^#` at the presheaf level, with the ring change made explicit.**

Pullback of presheaves of modules along the sheaf-level unit is the colimit formula `u_p` of
Stacks 00VC followed by the change of rings along the sheafification unit of the structure
ring.  The first factor is `pullbackIsoUpModuleFunctorOfColimit`, i.e. the adjunction proved in
`SiteUpColimitAdjunction`; the second is a pullback along `𝟭 C`, so the site does not
change. -/
noncomputable def upModulePullbackIso (O : Sheaf K RingCat.{w}) :
    PresheafOfModules.pullback.{w} (upSheafUnitHom u J (A := RingCat.{w}) O) ≅
      upModuleFunctor u O.obj ⋙ PresheafOfModules.pullback.{w} (upSheafifyRing u J O) :=
  (PresheafOfModules.pullbackComp.{w} (ringUnit u O.obj) (upSheafifyRing u J O)).symm ≪≫
    isoWhiskerRight (pullbackIsoUpModuleFunctorOfColimit u O.obj) _

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **`f^{-1} F = (u_p F)^#` at the sheaf level.**

This is the identification the proof of Stacks 05VD turns on, in the form the source uses it:
the inverse image of a sheaf of `O`-modules is the sheafification of the colimit formula of
Stacks 00VC, with scalars changed along the sheafification unit of the structure ring. -/
noncomputable def upModuleSheafPullbackIso (O : Sheaf K RingCat.{w}) :
    SheafOfModules.pullback.{w} (upSheafUnit u J (A := RingCat.{w}) O) ≅
      SheafOfModules.forget O ⋙ upModuleFunctor u O.obj ⋙
        PresheafOfModules.pullback.{w} (upSheafifyRing u J O) ⋙
          PresheafOfModules.sheafification (R := upSheaf u J (A := RingCat.{w}) O)
            (𝟙 (upSheaf u J (A := RingCat.{w}) O).obj) :=
  SheafOfModules.pullbackIso.{w} (upSheafUnit u J (A := RingCat.{w}) O) ≪≫
    isoWhiskerLeft (SheafOfModules.forget O) (isoWhiskerRight (upModulePullbackIso u J O) _)

end Modules

section Factorization

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C)
  {K : GrothendieckTopology D} (J : GrothendieckTopology C) [u.IsContinuous K J]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- `(PresheafOfModules.pushforward ψ.hom).IsRightAdjoint` for a change of rings on a fixed
site, i.e. along `𝟭 C`, with the binder at the sheaf spelling. -/
instance isRightAdjoint_presheafPushforwardId {R R' : Sheaf J RingCat.{w}}
    (ψ : R ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J J).obj R') :
    (PresheafOfModules.pushforward.{w} ψ.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top ψ.hom)

/-- **`f^* = (change of rings along `f^#`) ∘ f^{-1}`.**

The two-step description of the pullback of sheaves of modules that Stacks 05VD reduces to:
`f^* F = O_C ⊗_{f^{-1} O_D} f^{-1} F` (Stacks 03D6).  The first factor changes the site and is
the inverse image proper; the second is a change of rings along `f^#` on the site `(C, J)`
alone.  Taken with `upSheafUnit_comp_structureDescent`, which says that `η ≫ f_* (f^#)` *is*
the structure map, this exhibits any `SheafOfModules.pullback` along a structure map as such a
composite. -/
noncomputable def pullbackFactorization {O : Sheaf K RingCat.{w}} {R R' : Sheaf J RingCat.{w}}
    (η : O ⟶ (u.sheafPushforwardContinuous RingCat.{w} K J).obj R)
    (ψ : R ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J J).obj R') :
    SheafOfModules.pullback.{w} η ⋙ SheafOfModules.pullback.{w} ψ ≅
      SheafOfModules.pullback.{w} (F := u ⋙ 𝟭 C)
        (η ≫ (u.sheafPushforwardContinuous RingCat.{w} K J).map ψ) :=
  SheafOfModules.pullbackComp.{w} η ψ

end Factorization

section RelationCriterion

variable {D : Type w} [SmallCategory D] {K : GrothendieckTopology D} {O : Sheaf K CommRingCat.{w}}
  [K.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The sheaf-level local equational criterion of Stacks 08FC part (2) gives the
presheaf-level one** of `SiteUpColimitRelations`.

The two statements are the same condition read at two spellings: the sheaf-level
`Stacks.SheafOfModules.LocallyFactorsRelations` is indexed by a number `m` of relations and is
taken at `m = 1`, and its restriction maps are written `(F.val.map f.op).hom` where
`Stacks.ModuleUp.sectionRestrict` is the pinned-result-type form of the same map.  So the
proof is a repackaging — but it is the repackaging that lets
`Stacks.ModuleUp.hasLocalRelationFactorizations_up` consume the output of
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat`, which is the first two
steps of the final paragraph of the proof of Stacks 05VD. -/
theorem hasLocalRelationFactorizations_of_sheaf
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))
    (hF : Stacks.SheafOfModules.HasLocalSingleRelationFactorizations O F) :
    HasLocalRelationFactorizations K (Stacks.commRingSheafToRingSheaf O).obj F.val := by
  intro V n a s hrel
  obtain ⟨S, hS, hfac⟩ := hF V n a s hrel
  refine ⟨S, hS, fun V' g hg ↦ ?_⟩
  obtain ⟨l, t, B, h1, h2⟩ := hfac g hg
  exact ⟨l, t, B, fun i ↦ h1 i, fun k ↦ h2 k 0⟩

end RelationCriterion

end Stacks.ModuleUp

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentPullbackUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalenceModules
import StacksCore.Tactic.StacksAttribute

/-!
# Intrinsic properties of modules

Section 03DG of the source defines when a property `P` of sheaves of modules on ringed topoi is
*intrinsic* — `P(F) ⇔ P(f^*F)` for every equivalence of ringed topoi `(f, f♯)` — and describes a
method for producing such properties out of a property `P(C, O, F)` of sheaves of modules on
ringed *sites*:

1. define `P(C, O, F)` for every site `C`, sheaf of rings `O` and `O`-module `F`;
2. show `P(C, O, F) ⇔ P(C', g_*O, g_*F)` for every special cocontinuous functor `u : C ⥤ C'`,
   `g : Sh(C) ⟶ Sh(C')` being the equivalence of topoi attached to `u`.

Lemma 03CR combined with (2) then makes `P` well defined on ringed topoi, that is, intrinsic; and
if moreover

3. `P(D, O_D, F) ⇒ P(C, O_C, f^*F)` for every morphism of ringed sites
   `(f, f♯) : (C, O_C) ⟶ (D, O_D)` given by a functor `u : D ⥤ C` satisfying the assumptions of
   Sites, Proposition 00X6,

then `P` is preserved under pullback along arbitrary morphisms of ringed topoi.  The section
illustrates the definition with the property of being free, and asserts that each of the global
properties of Definition 03DE is intrinsic.

This file states and proves all of that.

## Main definitions

* `AlgebraicGeometry.RingedTopos.ModuleProperty`: a property of sheaves of modules on ringed
  sites, step (1) of the method.
* `AlgebraicGeometry.RingedTopos.ModuleProperty.IsIntrinsic`: **the definition of an intrinsic
  property.**
* `AlgebraicGeometry.RingedTopos.ModuleProperty.SpecialCocontinuousInvariant`: condition (2).
* `AlgebraicGeometry.RingedTopos.ModuleProperty.SitePullbackStable`: condition (3).

## Main results

* `AlgebraicGeometry.RingedTopos.ModuleProperty.isIntrinsic_of_specialCocontinuousInvariant`:
  **a property satisfying (1) and (2) is intrinsic**, by Lemma 03CR.
* `AlgebraicGeometry.RingedTopos.ModuleProperty.pullbackModules_of_sitePullbackStable`: **a
  property satisfying (1), (2) and (3) is preserved under pullback along an arbitrary morphism
  of ringed topoi**, again by Lemma 03CR.
* `AlgebraicGeometry.RingedTopos.ModuleProperty.isIntrinsic_isFree` and its six companions:
  **each of the seven properties of Definition 03DE is intrinsic**, being free first among them.

## Implementation notes

**What "a property of `(C, O, F)`" carries.**  The source speaks of a property of the triple
`(C, O, F)`, and so tacitly of one that does not distinguish isomorphic triples; its uses of
Lemma 03CR depend on this, since 03CR identifies sheaves of modules and structure sheaves only up
to isomorphism.  The two halves of that tacit hypothesis are made explicit:
`ModuleProperty.IsIsoInvariant`, invariance under an isomorphism of sheaves of modules, and
`ModuleProperty.IsRingIsoInvariant`, invariance under replacing the structure sheaf by an
isomorphic one.  The latter is phrased through the pullback along
`AlgebraicGeometry.RingedToposHom.ofIdentityTopos`, the identity of the site together with an
isomorphism of structure sheaves, whose pullback of modules is restriction of scalars along that
isomorphism (`AlgebraicGeometry.RingedToposHom.pullbackModulesIsoRestrictionOfIdentityTopos`).
Only the conclusion "intrinsic" from (1) and (2) alone needs it; with (3) in hand it is not
used, the reverse implication being then supplied by the inverse equivalence.

**The two conditions, in the source's form.**  Condition (2) is stated with the structure sheaf
of the replacement site *equal* to `g_*O` and the module `g_*F`, exactly as in the source, for
every functor that is cocontinuous and exhibits a dense subsite — the definition
`Stacks.IsSpecialCocontinuous` of a special cocontinuous functor.  Condition (3) is stated for
every continuous functor `u : D ⥤ C` out of a site with finite limits that preserves finite
limits, which are the assumptions of Sites, Proposition 00X6, and for every morphism of ringed
topoi whose underlying morphism of topoi is the one `u` defines
(`Functor.isMorphismOfSites_of_preservesFiniteLimits`); that is a morphism of ringed sites given
by `u`.

**Universes.**  The ringed sites are `RingedTopos.{w, w, w}`, the universes of a Stacks site, the
generality at which Lemma 03CR is available.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DF](https://stacks.math.columbia.edu/tag/03DF)
* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedTopos

universe w

/-- **A property of sheaves of modules on ringed sites**, step (1) of the method of
Section 03DG: for every site `(C, J)` with a sheaf of commutative rings `O` and every sheaf of
`O`-modules `F`, a proposition `P(C, O, F)`. -/
abbrev ModuleProperty : Type (w + 1) :=
  ∀ X : RingedTopos.{w, w, w},
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) → Prop

namespace ModuleProperty

variable (P : ModuleProperty.{w})

/-- **An intrinsic property of sheaves of modules**, Section 03DG: `P(F) ⇔ P(f^*F)` whenever
`(f, f♯)` is an equivalence of ringed topoi, that is, its underlying morphism of topoi is an
equivalence and its structure map `f♯` is an isomorphism. -/
@[stacks 03DG "the definition of an intrinsic property of sheaves of modules"]
def IsIntrinsic : Prop :=
  ∀ {X Y : RingedTopos.{w, w, w}} (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
    P Y F ↔ P X (f.toModulesHom.pullbackModules.obj F)

/-- The property does not distinguish isomorphic sheaves of modules. -/
def IsIsoInvariant : Prop :=
  ∀ (X : RingedTopos.{w, w, w})
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}, (F ≅ G) →
    P X F → P X G

/-- The property does not distinguish isomorphic structure sheaves on the same site: it passes
along the pullback of modules attached to an isomorphism `φ : O ≅ O'`, the identity of the site
together with `φ` as structure map, which is restriction of scalars along `φ`
(`AlgebraicGeometry.RingedToposHom.pullbackModulesIsoRestrictionOfIdentityTopos`). -/
def IsRingIsoInvariant : Prop :=
  ∀ {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (O O' : Sheaf J CommRingCat.{w})
    (φ : O ⟶ (pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type w)))).obj O'),
    IsIso φ → ∀ G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O),
      P ⟨C, J, O⟩ G →
        P ⟨C, J, O'⟩ ((RingedToposHom.ofIdentityTopos φ).toModulesHom.pullbackModules.obj G)

/-- The ringed site `(C', g_*O)` attached to a dense subsite inclusion `v : C ⥤ C'` of a ringed
site `(C, O)`, `g : Sh(C) ⟶ Sh(C')` being the equivalence of topoi attached to `v`. -/
noncomputable abbrev denseSubsiteRingedTopos (X : RingedTopos.{w, w, w}) {C' : Type w}
    [SmallCategory C'] (J' : GrothendieckTopology C') (v : X.C ⥤ C') [v.IsDenseSubsite X.J J'] :
    RingedTopos.{w, w, w} where
  C := C'
  J := J'
  O := (Functor.IsDenseSubsite.morphismOfTopoi X.J J' v).pushforwardRing.obj X.O

/-- The equivalence of ringed topoi `(g, id) : (Sh(C), O) ⟶ (Sh(C'), g_*O)` attached to a dense
subsite inclusion `v : C ⥤ C'`. -/
noncomputable abbrev denseSubsiteHom (X : RingedTopos.{w, w, w}) {C' : Type w}
    [SmallCategory C'] (J' : GrothendieckTopology C') (v : X.C ⥤ C') [v.IsDenseSubsite X.J J'] :
    RingedToposHom X (denseSubsiteRingedTopos X J' v) where
  toToposHom := Functor.IsDenseSubsite.morphismOfTopoi X.J J' v
  fSharp := 𝟙 _

/-- **Condition (2) of the method of Section 03DG.**  For every special cocontinuous functor
`u : C ⥤ C'` — cocontinuous and exhibiting `(C, J)` as a dense subsite of `(C', J')` — every
sheaf of rings `O` on `C` and every `O`-module `F`, `P(C, O, F) ⇔ P(C', g_*O, g_*F)`, where
`g : Sh(C) ⟶ Sh(C')` is the equivalence of topoi attached to `u`. -/
def SpecialCocontinuousInvariant : Prop :=
  ∀ (X : RingedTopos.{w, w, w}) {C' : Type w} [SmallCategory C'] (J' : GrothendieckTopology C')
    (u : X.C ⥤ C') [u.IsCocontinuous X.J J'] [u.IsDenseSubsite X.J J']
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
    P X F ↔ P (denseSubsiteRingedTopos X J' u)
      ((RingedToposHom.pushforwardModules (denseSubsiteHom X J' u)).obj F)

/-- **Condition (3) of the method of Section 03DG.**  For every morphism of ringed sites
`(f, f♯) : (C, O_C) ⟶ (D, O_D)` given by a functor `u : D ⥤ C` satisfying the assumptions of
Sites, Proposition 00X6 — `u` is continuous, `D` has finite limits and `u` preserves them — and
every `O_D`-module `F`, `P(D, O_D, F) ⇒ P(C, O_C, f^*F)`.  The morphism of ringed sites is a
morphism of ringed topoi whose underlying morphism of topoi is the one Proposition 00X6
attaches to `u`. -/
def SitePullbackStable : Prop :=
  ∀ (X Y : RingedTopos.{w, w, w}) (u : Y.C ⥤ X.C) [u.IsContinuous Y.J X.J] [HasFiniteLimits Y.C]
    [PreservesFiniteLimits u] (f : RingedToposHom X Y),
    f.toToposHom = (Functor.isMorphismOfSites_of_preservesFiniteLimits u Y.J X.J).morphismOfTopoi →
    ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      P Y F → P X (f.toModulesHom.pullbackModules.obj F)

variable {P}

open RingedToposHom

/-- **Condition (2) read through the pullback.**  For a property invariant under isomorphism,
condition (2) says equivalently that `P(C', g_*O, G) ⇔ P(C, O, g^*G)` for every `g_*O`-module
`G`: the unit `G ⟶ g_*g^*G` of the adjunction of Stacks 03D7 is an isomorphism, `g^*` being an
equivalence. -/
theorem iff_pullbackModules_denseSubsiteHom (hiso : P.IsIsoInvariant)
    (h2 : P.SpecialCocontinuousInvariant) (X : RingedTopos.{w, w, w}) {C' : Type w}
    [SmallCategory C'] (J' : GrothendieckTopology C') (u : X.C ⥤ C') [u.IsDenseSubsite X.J J']
    (G : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseSubsiteRingedTopos X J' u).O)) :
    P (denseSubsiteRingedTopos X J' u) G ↔
      P X ((denseSubsiteHom X J' u).toModulesHom.pullbackModules.obj G) := by
  have : (denseSubsiteHom X J' u).toToposHom.pushforward.IsEquivalence :=
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence X.J J' u
  have : IsIso (denseSubsiteHom X J' u).fSharp := inferInstanceAs (IsIso (𝟙 _))
  have : (denseSubsiteHom X J' u).toModulesHom.pullbackModules.IsEquivalence :=
    isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules (X := X)
      (Y := denseSubsiteRingedTopos X J' u) (denseSubsiteHom X J' u)
  have := (pullbackAdjPushforwardModules (denseSubsiteHom X J' u)).unit_isIso_of_L_fully_faithful
  rw [h2 X J' u]
  exact ⟨hiso _ (asIso ((pullbackAdjPushforwardModules (denseSubsiteHom X J' u)).unit.app G)),
    hiso _ (asIso ((pullbackAdjPushforwardModules (denseSubsiteHom X J' u)).unit.app G)).symm⟩

/-- **A property passes around a square of the shape Lemma 03CR produces** once it passes along
the middle arrow.  The two vertical arrows are the equivalences `(g, id)` and `(e, id)` attached
to dense subsite inclusions, and the property crosses them by condition (2); the square is
consumed through its 2-isomorphism, and `e^*e_*F ≅ F` is the counit of Stacks 03D7. -/
theorem pullbackModules_of_square (hiso : P.IsIsoInvariant) (h2 : P.SpecialCocontinuousInvariant)
    {X Y : RingedTopos.{w, w, w}} (f : RingedToposHom X Y)
    {C' : Type w} [SmallCategory C'] {J' : GrothendieckTopology C'} {a : X.C ⥤ C'}
    [a.IsDenseSubsite X.J J'] {D' : Type w} [SmallCategory D'] {K' : GrothendieckTopology D'}
    {b : Y.C ⥤ D'} [b.IsDenseSubsite Y.J K']
    (h : RingedToposHom (denseSubsiteRingedTopos X J' a) (denseSubsiteRingedTopos Y K' b))
    (t : TwoIso (A := X) (B := denseSubsiteRingedTopos Y K' b)
      (RingedToposHom.comp (X := X) (Y := denseSubsiteRingedTopos X J' a)
        (Z := denseSubsiteRingedTopos Y K' b) h (denseSubsiteHom X J' a))
      (RingedToposHom.comp (X := X) (Y := Y) (Z := denseSubsiteRingedTopos Y K' b)
        (denseSubsiteHom Y K' b) f))
    (hh : ∀ G, P _ G → P _ (h.toModulesHom.pullbackModules.obj G))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (hF : P Y F) :
    P X (f.toModulesHom.pullbackModules.obj F) := by
  have : (denseSubsiteHom Y K' b).toToposHom.pushforward.IsEquivalence :=
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence Y.J K' b
  have : IsIso (denseSubsiteHom Y K' b).fSharp := inferInstanceAs (IsIso (𝟙 _))
  have : (pushforwardModules (denseSubsiteHom Y K' b)).IsEquivalence :=
    isEquivalence_pushforwardModules_of_isEquivalence_ringedToposEquivalenceModules (X := Y)
      (Y := denseSubsiteRingedTopos Y K' b) (denseSubsiteHom Y K' b)
  have := (pullbackAdjPushforwardModules (denseSubsiteHom Y K' b)).counit_isIso_of_R_fully_faithful
  refine hiso X ?_ ((iff_pullbackModules_denseSubsiteHom hiso h2 X J' a _).1
    (hh _ ((h2 Y K' b F).1 hF)))
  exact ((pullbackModulesCompIso (denseSubsiteHom X J' a) h).app _).symm ≪≫
    t.pullbackModulesIso.app _ ≪≫
    (pullbackModulesCompIso f (denseSubsiteHom Y K' b)).app _ ≪≫
    f.toModulesHom.pullbackModules.mapIso
      (asIso ((pullbackAdjPushforwardModules (denseSubsiteHom Y K' b)).counit.app F))

/-- **Section 03DG, conditions (1) and (2): the property is intrinsic.**  Let `P` be a property
of sheaves of modules on ringed sites (step (1), invariant under isomorphism of the data as
explained in the module documentation) satisfying condition (2).  Then `P(F) ⇔ P(f^*F)` for
every equivalence of ringed topoi `(f, f♯)`: the property is well defined on ringed topoi.

The addendum to Lemma 03CR,
`AlgebraicGeometry.RingedToposHom.exists_oneSided_isDenseSubsite_of_isEquivalence`, factors the
equivalence over a single replacement site through two equivalences attached to special
cocontinuous functors and a change of structure sheaf along an isomorphism; condition (2)
crosses the first two and the invariance under isomorphism the third.  The reverse implication
is the same argument for the inverse equivalence. -/
@[stacks 03DG "the method, steps (1) and (2): combined with Lemma 03CR they make the property
  well defined on ringed topoi, i.e. intrinsic"]
theorem isIntrinsic_of_specialCocontinuousInvariant (hiso : P.IsIsoInvariant)
    (hring : P.IsRingIsoInvariant) (h2 : P.SpecialCocontinuousInvariant) : P.IsIntrinsic := by
  have key : ∀ {X Y : RingedTopos.{w, w, w}} (f : RingedToposHom X Y)
      [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
      (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
      P Y F → P X (f.toModulesHom.pullbackModules.obj F) := by
    intro X Y f _ _ F hF
    obtain ⟨C', instC', J', v, u, instv, instu, -, -, -, -, -, -, h, hh, hfs, ⟨t⟩⟩ :=
      exists_oneSided_isDenseSubsite_of_isEquivalence X Y f
        (fun z : PEmpty.{w + 1} ↦ z.elim) (fun z : PEmpty.{w + 1} ↦ z.elim)
    obtain ⟨hTop, hSharp⟩ := h
    subst hh
    exact pullbackModules_of_square hiso h2 f _ t
      (fun G hG ↦ hring J' _ _ hSharp hfs G hG) F hF
  intro X Y f _ _ F
  have : (inverse (X := X) (Y := Y) f).toToposHom.pushforward.IsEquivalence :=
    inferInstanceAs f.toToposHom.inverseImage.IsEquivalence
  have : IsIso (inverse (X := X) (Y := Y) f).fSharp :=
    inferInstanceAs (IsIso (inv f.fSharpInverseImage))
  exact ⟨key f F, fun hP ↦ hiso Y (pullbackModulesInverseObjIso f F)
    (key (inverse (X := X) (Y := Y) f) _ hP)⟩

/-- **Section 03DG, conditions (1), (2) and (3): the property is preserved under pullback along
an arbitrary morphism of ringed topoi.**  Let `P` be a property of sheaves of modules on ringed
sites (step (1), invariant under isomorphism of sheaves of modules) satisfying conditions (2)
and (3).  Then for every morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and
every `O_D`-module `F`, `P(F) ⇒ P(f^*F)`.

Lemma 03CR,
`AlgebraicGeometry.RingedToposHom.exists_twoSided_isDenseSubsite_morphismOfSites`, factors the
morphism through two equivalences attached to special cocontinuous functors, which condition (2)
crosses, and a morphism of ringed sites given by a left exact continuous functor between sites
with finite limits, which condition (3) crosses. -/
@[stacks 03DG "the method, step (3): a property satisfying (1), (2) and (3) is preserved under
  pullback of modules along arbitrary morphisms of ringed topoi"]
theorem pullbackModules_of_sitePullbackStable (hiso : P.IsIsoInvariant)
    (h2 : P.SpecialCocontinuousInvariant) (h3 : P.SitePullbackStable)
    {X Y : RingedTopos.{w, w, w}} (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (hF : P Y F) :
    P X (f.toModulesHom.pullbackModules.obj F) := by
  obtain ⟨C', instC', J', D', instD', K', a, b, c, insta, instb, hflC, hflD, hsubJ, hsubK,
      hcont, hpfl, hflat, hc, -, -, -, -, h, hh, ⟨t⟩⟩ :=
    exists_twoSided_isDenseSubsite_morphismOfSites X Y f
      (fun z : PEmpty.{w + 1} ↦ z.elim) (fun z : PEmpty.{w + 1} ↦ z.elim)
  exact pullbackModules_of_square hiso h2 f h t (fun G hG ↦ h3 _ _ c h hh G hG) F hF

/-- **A property of sheaves of modules preserved under every pullback is intrinsic**, provided it
does not distinguish isomorphic modules: the reverse implication is the pullback along the
inverse equivalence, carried back by
`AlgebraicGeometry.RingedToposHom.pullbackModulesInverseObjIso`. -/
theorem isIntrinsic_of_forall_pullbackModules (hiso : P.IsIsoInvariant)
    (hpull : ∀ {X Y : RingedTopos.{w, w, w}} (f : RingedToposHom X Y)
      (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
      P Y F → P X (f.toModulesHom.pullbackModules.obj F)) : P.IsIntrinsic := by
  intro X Y f _ _ F
  have : (inverse (X := X) (Y := Y) f).toToposHom.pushforward.IsEquivalence :=
    inferInstanceAs f.toToposHom.inverseImage.IsEquivalence
  have : IsIso (inverse (X := X) (Y := Y) f).fSharp :=
    inferInstanceAs (IsIso (inv f.fSharpInverseImage))
  exact ⟨hpull f F, fun hP ↦ hiso Y (pullbackModulesInverseObjIso f F)
    (hpull (inverse (X := X) (Y := Y) f) _ hP)⟩

/-- A property satisfying conditions (1), (2) and (3) of Section 03DG is intrinsic; unlike
`AlgebraicGeometry.RingedTopos.ModuleProperty.isIntrinsic_of_specialCocontinuousInvariant`, this
needs no invariance under an isomorphism of structure sheaves. -/
theorem isIntrinsic_of_sitePullbackStable (hiso : P.IsIsoInvariant)
    (h2 : P.SpecialCocontinuousInvariant) (h3 : P.SitePullbackStable) : P.IsIntrinsic :=
  isIntrinsic_of_forall_pullbackModules hiso fun f F ↦
    pullbackModules_of_sitePullbackStable hiso h2 h3 f F

/-! ### The properties of Definition 03DE are intrinsic -/

/-- **Being free is intrinsic**, the example of Section 03DG.  The pullback of a free module is
free by Stacks 03DF, and freeness does not distinguish isomorphic modules. -/
@[stacks 03DG "the example: the property of being free is intrinsic"]
theorem isIntrinsic_isFree : ModuleProperty.IsIntrinsic.{w} fun _ F ↦ F.IsFree :=
  isIntrinsic_of_forall_pullbackModules.{w}
    (fun _ _ _ e h ↦ Stacks.SheafOfModules.Intrinsic.exists_isColimit_cofan_of_iso e h)
    fun f _ hF ↦ pullbackModules_isFree f hF

/-- **Being finite free is intrinsic**, Definition 03DE (2), as Section 03DG asserts. -/
@[stacks 03DG "each property of Definition 03DE is intrinsic: finite free"]
theorem isIntrinsic_isFiniteFree : ModuleProperty.IsIntrinsic.{w}
    fun X F ↦ SheafOfModules.IsFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F :=
  isIntrinsic_of_forall_pullbackModules.{w}
    (fun _ _ _ e h ↦ Stacks.SheafOfModules.Intrinsic.isFiniteFree_of_iso e h)
    fun f _ hF ↦ pullbackModules_isFiniteFree f hF

/-- **Being generated by global sections is intrinsic**, Definition 03DE (3), as Section 03DG
asserts. -/
@[stacks 03DG "each property of Definition 03DE is intrinsic: generated by global sections"]
theorem isIntrinsic_isGeneratedByGlobalSections :
    ModuleProperty.IsIntrinsic.{w} fun _ F ↦ F.IsGeneratedByGlobalSections :=
  isIntrinsic_of_forall_pullbackModules.{w}
    (fun _ _ _ e h ↦ ⟨_root_.SheafOfModules.GeneratingSections.equivOfIso e h.some⟩)
    fun f _ hF ↦ pullbackModules_isGeneratedByGlobalSections f hF

/-- **Being generated by `r` global sections is intrinsic**, Definition 03DE (4), as
Section 03DG asserts. -/
@[stacks 03DG "each property of Definition 03DE is intrinsic: generated by r global sections"]
theorem isIntrinsic_isGeneratedByGlobalSectionsOfCard (r : ℕ) :
    ModuleProperty.IsIntrinsic.{w} fun _ F ↦ F.IsGeneratedByGlobalSectionsOfCard r :=
  isIntrinsic_of_forall_pullbackModules.{w}
    (fun _ _ _ e h ↦
      Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSectionsOfCard_of_iso e r h)
    fun f _ hF ↦ pullbackModules_isGeneratedByGlobalSectionsOfCard f hF

/-- **Being generated by finitely many global sections is intrinsic**, Definition 03DE (5), as
Section 03DG asserts. -/
@[stacks 03DG "each property of Definition 03DE is intrinsic: generated by finitely many global
  sections"]
theorem isIntrinsic_exists_isGeneratedByGlobalSectionsOfCard :
    ModuleProperty.IsIntrinsic.{w} fun _ F ↦ ∃ r : ℕ, F.IsGeneratedByGlobalSectionsOfCard r :=
  isIntrinsic_of_forall_pullbackModules.{w}
    (fun _ _ _ e h ↦ ⟨h.choose,
      Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSectionsOfCard_of_iso e _
        h.choose_spec⟩)
    fun f _ hF ↦ pullbackModules_exists_isGeneratedByGlobalSectionsOfCard f hF

/-- **Having a global presentation is intrinsic**, Definition 03DE (6), as Section 03DG
asserts. -/
@[stacks 03DG "each property of Definition 03DE is intrinsic: global presentation"]
theorem isIntrinsic_isPresentedByGlobalSections :
    ModuleProperty.IsIntrinsic.{w} fun _ F ↦ F.IsPresentedByGlobalSections :=
  isIntrinsic_of_forall_pullbackModules.{w}
    (fun _ _ _ e h ↦ Stacks.SheafOfModules.Intrinsic.isPresentedByGlobalSections_of_iso e h)
    fun f _ hF ↦ pullbackModules_isPresentedByGlobalSections f hF

/-- **Having a finite global presentation is intrinsic**, Definition 03DE (7), as Section 03DG
asserts. -/
@[stacks 03DG "each property of Definition 03DE is intrinsic: finite global presentation"]
theorem isIntrinsic_isFinitelyPresentedByGlobalSections :
    ModuleProperty.IsIntrinsic.{w} fun _ F ↦ F.IsFinitelyPresentedByGlobalSections :=
  isIntrinsic_of_forall_pullbackModules.{w}
    (fun _ _ _ e h ↦
      Stacks.SheafOfModules.Intrinsic.isFinitelyPresentedByGlobalSections_of_iso e h)
    fun f _ hF ↦ pullbackModules_isFinitelyPresentedByGlobalSections f hF

end ModuleProperty

end AlgebraicGeometry.RingedTopos

end

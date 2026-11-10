module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalenceConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationCommRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
import StacksCore.Tactic.StacksAttribute

/-!
# `f^*` of a flat module is flat, for a morphism of sites given by a continuous flat functor

Let `u : D ⥤ C` be a continuous functor between sites `(D, K)` and `(C, J)` which is
`CategoryTheory.Functor.RepresentablyFlat` — equivalently, by Stacks 00X3, a functor commuting
with finite limits out of a site with finite limits — and let `(f, f^♯)` be the induced morphism
of ringed sites.  This file proves that `f^* F` is a flat `O_C`-module whenever `F` is a flat
`O_D`-module, which is Stacks 05VD for this class of morphisms.

That class is exactly the situation the source's proof reduces to: after invoking Stacks 03CR to
replace an arbitrary morphism of ringed topoi or ringed sites by an equivalent one, the proof
reads "we may assume that our sites `C` and `D` have all finite limits and that `f` is a
morphism of sites induced by a continuous functor `u : D → C` which commutes with finite
limits".  **The passage from an arbitrary morphism of ringed sites to that situation is Stacks
03CR, which is not formalized on this branch**; everything after it is here.

The proof is the one in the source, in three steps.

1. **`f^{-1}F` is flat over `f^{-1}O`.**  Flatness of `F` gives the local equational criterion
   of Stacks 08FC part (2)
   (`hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse`); the colimit
   formula `u_p` of Stacks 00VC transports it
   (`Stacks.ModuleUp.hasLocalRelationFactorizations_up`); sheafification preserves it
   (`Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify`); and `f^{-1}F` *is* that
   sheafification, which is `Stacks.ModuleUp.upModuleSheafPullbackIsoOfCommRing` below.  The
   other direction of Stacks 08FC then returns flatness.
2. **`f^* F = O_C ⊗_{f^{-1}O_D} f^{-1}F`** (Stacks 03D6), so Stacks 05V4
   (`Stacks.FlatChangeOfRings.isFlat_extendScalars`) finishes — once extension of scalars is
   identified with `SheafOfModules.pullback` along the identity functor, which is
   `Stacks.FlatChangeOfRings.extendScalarsIsoPullback` below.
3. The two steps are glued by `SheafOfModules.pullbackComp`, using that the structure map
   factors through the sheaf-level unit
   (`Stacks.ModuleUp.upSheafUnit_comp_structureDescent`).

## Main definitions

* `Stacks.ModuleUp.pullbackIdSheafificationIso`: **sheafifying over a sheaf of rings is
  pulling back the scalars and then sheafifying over the identity.**  Stated at Mathlib's own
  generality for a locally bijective `α : R₀ ⟶ R.obj`; both sides are left adjoint to
  `SheafOfModules.forget R ⋙ restrictScalars α`.
* `Stacks.ModuleUp.upSheafUnitRingOfCommRing`: the sheaf-level unit
  `O ⟶ f_* (f^{-1}O)` of `Stacks.ModuleUp.upSheafUnit`, read with `f^{-1}O` computed at
  `CommRingCat` and the whole morphism at `RingCat`.
* `Stacks.ModuleUp.upModulePullbackIsoOfCommRing`,
  `Stacks.ModuleUp.upModuleSheafPullbackIsoOfCommRing`: `f^{-1}F = (u_p F)^#` over that unit,
  on presheaves and on sheaves of modules.
* `Stacks.SheafOfModules.ChangeOfRings.structureMap` and `.overId`, reused from
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsAdjunction`, carry the
  identity-site retyping that `SheafOfModules.pullback` and `PresheafOfModules.pullback`
  require; no new retyping definition is introduced here.
* `Stacks.ModuleUp.ringSheafMapOfPushforward`: the underlying morphism of sheaves of rings of a
  structure map `O ⟶ f_* R` of sheaves of commutative rings.

## Main results

* `Stacks.ModuleUp.hasLocalRelationFactorizations_of_iso`: the local equational criterion is
  invariant under isomorphism of presheaves of modules.
* `Stacks.ModuleUp.isFlat_of_iso`: flatness is invariant under isomorphism.
* `Stacks.ModuleUp.sheafCompose_map_upSheafUnit`: **the bridge is compatible with the units.**
  Forgetting commutativity takes the `CommRingCat`-level sheaf unit to
  `upSheafUnitRingOfCommRing`.  This is what lets an arbitrary structure map of sheaves of
  *commutative* rings be factored through a unit whose module-level pullback is `u_p`.
* `Stacks.FlatChangeOfRings.isFlat_pullback_ringSheafMapId`: **Stacks 05V4 read for
  `SheafOfModules.pullback`.**
* `Stacks.ModuleUp.isFlat_pullback_upSheafUnitRingOfCommRing`: **step 1**, `f^{-1}` preserves
  flatness.
* `Stacks.ModuleUp.isFlat_pullback`: **Stacks 05VD** for a morphism of ringed sites whose
  underlying functor is continuous and representably flat, stated with the sheafification
  instances of the section carried as binders.
* `Stacks.ModuleUp.isFlat_pullback_of_representablyFlat`: the same, **with every one of those
  eleven instances derived instead of assumed**, so that `RepresentablyFlat u` and
  `u.IsContinuous K J` are the only hypotheses left.

## Implementation notes

**Why `pullbackIdSheafificationIso` is three lines.**  Three facts are `rfl` at this pin:
`PresheafOfModules.pushforward (F := 𝟭 C) α = PresheafOfModules.restrictScalars α`,
`PresheafOfModules.restrictScalars (𝟙 R.obj) = 𝟭 _`, and therefore
`(SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)) ⋙ pushforward α
= SheafOfModules.forget R ⋙ restrictScalars α`.  So the two left adjoints have literally the
same right adjoint and `CategoryTheory.Adjunction.leftAdjointUniq` applies with no comparison
isomorphism to supply.  The same three `rfl`s are what make
`Stacks.FlatChangeOfRings.extendScalarsIsoPullback` immediate from
`Stacks.FlatChangeOfRings.extendScalarsAdjunction`.

**The identity-site retyping has to be a `def`, and already exists.**
`SheafOfModules.pullback` and `PresheafOfModules.pullback` take a morphism whose target is
spelled `F.op ⋙ R` with `F = 𝟭 C`, while `Stacks.ModuleUp.upSheafifyRingOfCommRing` and
`Stacks.FlatChangeOfRings.ringSheafMap` have it spelled without the `(𝟭 C).op ⋙`.  The two are
definitionally equal and not syntactically so.  `Stacks.SheafOfModules.ChangeOfRings.overId`
and `.structureMap` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsAdjunction` are exactly that
retyping, and are reused here rather than redeclared; only the local bijectivity instances have
to be restated at the retyped spelling, since a `def` is opaque to instance search.

**`whiskerLeft_comp` cannot be used through `rw` here.**  It is `rfl`, and the `rw` fails to
find its own pattern in a goal that displays it, so the proof of
`Stacks.ModuleUp.upSheafUnitRingOfCommRing_hom_eq` is written with the whiskered composite
already split and crosses the remaining definitional gap with `congrArg`, which is
defeq-tolerant.  The same is true of
`Stacks.ModuleUp.upSheafify_comp_bridge` inside `whiskerLeft`.

**`PreservesSheafification` must be named.**  `infer_instance` for
`J.PreservesSheafification (forget₂ CommRingCat RingCat)` exhausts the `synthInstance`
heartbeat budget, as recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationCommRing`; the instance is
supplied by name in `Stacks.ModuleUp.upSheafify_comp_bridge`.  It is a `Prop` class, so the
instance baked into `Stacks.ModuleUp.sheafifyForgetToRingIso` and the one named here are
definitionally equal.

**Universes.**  Everything is at the single universe `w` of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimit`: the sites are small categories
in `Type w` and the structure sheaves and modules are at `w`.  This is forced rather than
chosen — `PresheafOfModules.pullbackObjIsDefined_eq_top`, the only unconditional source of
`(PresheafOfModules.pushforward φ).IsRightAdjoint`, is stated for small sites in `Type u` with
`RingCat.{u}`, and both directions of Stacks 08FC and Stacks 05V4 are at one universe on this
branch.  Lifting it therefore has to begin in Mathlib and not here.

**The sheafification hypotheses are all derivable, and are kept as binders only to pay for them
once.**  At a small site every typeclass of the `CommRing` section below — `HasWeakSheafify` for
`CommRingCat`, `RingCat` and `AddCommGrpCat`, `HasSheafCompose (forget₂ CommRingCat RingCat)`,
`WEqualsLocallyBijective` for `RingCat` and `AddCommGrpCat`, and the two `HasLeftKanExtension`
families — is an instance of the pinned Mathlib, because `max u v = w` there.  Removing the
binders is nevertheless not free: the definitions of that section then re-run the synthesis in
each statement, `Stacks.ModuleUp.upSheafUnitRingOfCommRing` stops elaborating, and
`Stacks.ModuleUp.upSheafify_comp_bridge` exhausts the `isDefEq` heartbeat budget on
`J.PreservesSheafification (forget₂ CommRingCat RingCat)` — the synthesis the note just above
records as already too expensive.  So the binders stay where the definitions are, and the
discharge happens once, in
`Stacks.ModuleUp.isFlat_pullback_of_representablyFlat`.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
* [SGA 4, Exposé V, Corollary 1.7.1](https://link.springer.com/book/10.1007/BFb0099239)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor Opposite
open Stacks.SheafOfModules.ChangeOfRings (structureMap overId)

universe w

namespace Stacks.ModuleUp

/-! ### Sheafifying over a sheaf of rings, versus pulling back the scalars first -/

section Comparison

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ (𝟭 C).op ⋙ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(PresheafOfModules.pushforward.{w} α).IsRightAdjoint]

/-- **Sheafifying over `R` is changing the scalars along `α` and then sheafifying over the
identity.**

Both functors are left adjoint to `SheafOfModules.forget R ⋙ restrictScalars α` — the right
adjoints are the *same* functor, not merely isomorphic ones — so this is uniqueness of left
adjoints.  It is the identification that lets Mathlib's description of
`SheafOfModules.pullback` as "pull back the presheaf of modules, then sheafify over the
identity" be read as a single sheafification over the pulled-back ring, which is the form in
which `Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify` states the criterion. -/
noncomputable def pullbackIdSheafificationIso :
    PresheafOfModules.pullback.{w} α ⋙ PresheafOfModules.sheafification.{w} (𝟙 R.obj) ≅
      PresheafOfModules.sheafification.{w} (R := R) α :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.pullbackPushforwardAdjunction.{w} α).comp
      (PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)))
    (PresheafOfModules.sheafificationAdjunction.{w} α)

end Comparison

/-! ### The local equational criterion is invariant under isomorphism -/

section Transport

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{w} R}

/-- Naturality of a morphism of presheaves of modules, read at the pinned result type of
`Stacks.ModuleUp.sectionRestrict`. -/
theorem app_sectionRestrict (f : M ⟶ N) {X Y : Cᵒᵖ} (g : X ⟶ Y) (m : M.obj X) :
    (f.app Y).hom (sectionRestrict R M g m) = sectionRestrict R N g ((f.app X).hom m) :=
  NatTrans.naturality_apply ((PresheafOfModules.toPresheaf R).map f) g m

/-- **The local equational criterion of Stacks 08FC part (2) is invariant under isomorphism**
of presheaves of modules: a relation among sections of `N` is carried to one among sections of
`M` by `e.inv`, and the factorisation produced there is carried back by `e.hom`. -/
theorem hasLocalRelationFactorizations_of_iso (e : M ≅ N)
    (h : HasLocalRelationFactorizations J R M) :
    HasLocalRelationFactorizations J R N := by
  intro V n a s hrel
  have hs : ∀ i, (e.hom.app (op V)).hom ((e.inv.app (op V)).hom (s i)) = s i := fun i => by
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, e.inv_hom_id]
    simp
  have hrel' : ∑ i : Fin n, a i • (e.inv.app (op V)).hom (s i) = 0 := by
    rw [← map_zero (e.inv.app (op V)).hom, ← hrel]
    simp
  obtain ⟨T, hT, hfac⟩ := h V n a (fun i => (e.inv.app (op V)).hom (s i)) hrel'
  refine ⟨T, hT, fun {V'} g hg => ?_⟩
  obtain ⟨l, t, B, h1, h2⟩ := hfac g hg
  refine ⟨l, fun k => (e.hom.app (op V')).hom (t k), B, fun i => ?_, h2⟩
  rw [← hs i, ← app_sectionRestrict e.hom g.op, h1 i]
  simp

end Transport

/-! ### Flatness is invariant under isomorphism -/

section FlatAnySite

/-! The site here is an arbitrary one, not a small one: nothing in the argument below sees the
objects or the morphisms of the site, only the endofunctor `- ⊗ F` of sheaves of modules, and
`Stacks.SheafOfModules.FlatColimits.tensorCoeffFunctor` is stated for an arbitrary site.  The
instantiation of Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3) at the small
Zariski comparison needs it here, that site having its objects one universe above its
sections. -/

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}

/-- **Flatness of a sheaf of modules is invariant under isomorphism, on an arbitrary site.**
This is `Stacks.ModuleUp.isFlat_of_iso` below with the site not required to be small.

Tensoring on the right is a functor of the tensoring sheaf itself (the flip of
`Stacks.SheafOfModules.Tensor.sheafTensor`), so an isomorphism of sheaves of modules induces an
isomorphism of the two tensor endofunctors, and exactness is a property closed under
isomorphism of functors.

This is the general-site form of `Stacks.SheafOfModules.isFlat_of_iso`
(`StacksDraft.Ch21.Sec17.ExistsKFlatResolution`), which states the same thing for the flatness
predicate of `StacksFrontier.CategoryTheory.Sites.Modules.Flat` and takes a bundled
`AlgebraicGeometry.RingedSite` rather than a site and a structure sheaf.  The two are not
interchangeable as they stand — the predicates and the spellings of the underlying sheaf of
rings differ — and unifying them is owed. -/
theorem isFlat_of_iso_anySite
    {F G : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)} (e : F ≅ G)
    (h : Stacks.SheafOfModules.IsFlat F) : Stacks.SheafOfModules.IsFlat G :=
  (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.mapIso e) h

end FlatAnySite

section Flat

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}

/-- **Flatness of a sheaf of modules is invariant under isomorphism.**

Tensoring on the right is a functor of the tensoring sheaf itself (the flip of
`Stacks.SheafOfModules.Tensor.sheafTensor`), so an isomorphism of sheaves of modules induces an
isomorphism of the two tensor endofunctors, and exactness is a property closed under
isomorphism of functors.

This is the general-site form of `Stacks.SheafOfModules.isFlat_of_iso`
(`StacksDraft.Ch21.Sec17.ExistsKFlatResolution`), which states the same thing for the flatness
predicate of `StacksFrontier.CategoryTheory.Sites.Modules.Flat` and takes a bundled
`AlgebraicGeometry.RingedSite` rather than a site and a structure sheaf.  The two are not
interchangeable as they stand — the predicates and the spellings of the underlying sheaf of
rings differ — and unifying them is owed. -/
theorem isFlat_of_iso {F G : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)}
    (e : F ≅ G) (h : Stacks.SheafOfModules.IsFlat F) : Stacks.SheafOfModules.IsFlat G :=
  isFlat_of_iso_anySite e h

end Flat

end Stacks.ModuleUp

/-! ### Stacks 05V4, read for `SheafOfModules.pullback` -/

namespace Stacks.FlatChangeOfRings

open Stacks

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (f : O₁ ⟶ O₂)

/-- **Extension of scalars is `SheafOfModules.pullback` along the identity functor.**

`Stacks.FlatChangeOfRings.extendScalarsAdjunction` makes extension of scalars a left adjoint of
`SheafOfModules.restrictScalars (ringSheafMap f)`, and `SheafOfModules.pushforward` along the
identity functor *is* that restriction of scalars, so the two left adjoints agree. -/
noncomputable def extendScalarsIsoPullback :
    SheafOfModules.pullback.{w} (structureMap (ringSheafMap f)) ≅ extendScalars f :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap (ringSheafMap f)))
    (extendScalarsAdjunction f)

/-- **Stacks 05V4 for `SheafOfModules.pullback`.**  Pullback along a change of rings on a fixed
site takes a flat sheaf of modules to a flat sheaf of modules. -/
@[stacks 05V4 "read for `SheafOfModules.pullback` along the identity functor of the site"]
theorem isFlat_pullback_ringSheafMapId
    (G : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (hG : SheafOfModules.IsFlat G) :
    SheafOfModules.IsFlat
      ((_root_.SheafOfModules.pullback.{w} (structureMap (ringSheafMap f))).obj G) :=
  Stacks.ModuleUp.isFlat_of_iso ((extendScalarsIsoPullback f).app G).symm
    (isFlat_extendScalars f G hG)

end Stacks.FlatChangeOfRings

namespace Stacks.ModuleUp

/-! ### The sheaf-level unit with `f^{-1}O` computed at `CommRingCat` -/

section CommRing

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C) [RepresentablyFlat u]
  {K : GrothendieckTopology D} (J : GrothendieckTopology C) [u.IsContinuous K J]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J RingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ F : Dᵒᵖ ⥤ CommRingCat.{w}, u.op.HasLeftKanExtension F]
  [∀ F : Dᵒᵖ ⥤ RingCat.{w}, u.op.HasLeftKanExtension F]

/-- **The sheaf-level unit `O ⟶ f_* (f^{-1}O)` at `RingCat`, with `f^{-1}O` computed at
`CommRingCat`.**

This is `Stacks.ModuleUp.upSheafUnit` composed with the bridge
`Stacks.ModuleUp.upSheafForgetToRingIso`, written out so that its underlying morphism of
presheaves of rings is the Kan-extension unit followed by
`Stacks.ModuleUp.upSheafifyRingOfCommRing`: that is the shape
`PresheafOfModules.pullbackComp` consumes, and it is what makes the module-level pullback along
this unit *be* the sheafified colimit formula `u_p`. -/
noncomputable def upSheafUnitRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    Stacks.commRingSheafToRingSheaf O ⟶
      (u.sheafPushforwardContinuous RingCat.{w} K J).obj
        (Stacks.commRingSheafToRingSheaf (upSheaf u J (A := CommRingCat.{w}) O)) :=
  ⟨ringUnit u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≫
    whiskerLeft u.op (upSheafifyRingOfCommRing u J O)⟩

omit [u.IsContinuous K J] in
/-- **The bridge is the sheafification unit of the underlying sheaf of rings.**

`Stacks.ModuleUp.upSheafForgetToRingIso` is a composite of
`CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves` and
`CategoryTheory.sheafComposeNatIso`, and both come with a compatibility with their units; this
assembles the two. -/
theorem upSheafify_comp_bridge (O : Sheaf K CommRingCat.{w}) :
    upSheafify u J (A := RingCat.{w}) (Stacks.commRingSheafToRingSheaf O) ≫
        (upSheafForgetToRingIso u J O).hom.hom
      = (lanForgetToRingIso u O.obj).inv ≫
          whiskerRight (upSheafify u J (A := CommRingCat.{w}) O)
            (forget₂ CommRingCat.{w} RingCat.{w}) := by
  let _ : J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w}) :=
    CategoryTheory.GrothendieckTopology.instPreservesSheafification J _
  change CategoryTheory.toSheafify J (u.op.lan.obj (O.obj ⋙ forget₂ _ _)) ≫
      ((presheafToSheaf J RingCat.{w}).map (lanForgetToRingIso u O.obj).inv).hom ≫
        (sheafifyForgetToRingIso J (u.op.lan.obj O.obj)).hom.hom = _
  rw [← Category.assoc, ← CategoryTheory.toSheafify_naturality, Category.assoc]
  congr 1
  exact CategoryTheory.sheafComposeIso_hom_fac J (forget₂ CommRingCat.{w} RingCat.{w})
    (u.op.lan.obj O.obj)

/-- The underlying morphism of presheaves of rings of
`Stacks.ModuleUp.upSheafUnitRingOfCommRing` is the `CommRingCat`-level sheaf unit with
commutativity forgotten. -/
theorem upSheafUnitRingOfCommRing_hom_eq (O : Sheaf K CommRingCat.{w}) :
    whiskerRight (upSheafUnitHom u J (A := CommRingCat.{w}) O)
        (forget₂ CommRingCat.{w} RingCat.{w})
      = (upSheafUnitRingOfCommRing u J O).hom := by
  have e1 : ringUnit u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≫
        whiskerLeft u.op (lanForgetToRingIso u O.obj).inv
      = whiskerRight (u.op.lanUnit.app O.obj) (forget₂ CommRingCat.{w} RingCat.{w}) ≫
        (Functor.associator u.op (u.op.lan.obj O.obj)
          (forget₂ CommRingCat.{w} RingCat.{w})).hom :=
    Functor.leftKanExtensionCompIsoOfPreserves_inv_fac _ _ _
  have e2 : (Functor.associator u.op (u.op.lan.obj O.obj)
        (forget₂ CommRingCat.{w} RingCat.{w})).hom ≫
        whiskerLeft u.op (whiskerRight (upSheafify u J (A := CommRingCat.{w}) O)
          (forget₂ CommRingCat.{w} RingCat.{w}))
      = whiskerRight (whiskerLeft u.op (upSheafify u J (A := CommRingCat.{w}) O))
          (forget₂ CommRingCat.{w} RingCat.{w}) := by
    ext X
    simp
  have main : (ringUnit u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≫
        whiskerLeft u.op (lanForgetToRingIso u O.obj).inv) ≫
        whiskerLeft u.op (whiskerRight (upSheafify u J (A := CommRingCat.{w}) O)
          (forget₂ CommRingCat.{w} RingCat.{w}))
      = whiskerRight (upSheafUnitHom u J (A := CommRingCat.{w}) O)
          (forget₂ CommRingCat.{w} RingCat.{w}) := by
    rw [e1, Category.assoc, e2, ← whiskerRight_comp]
    rfl
  refine main.symm.trans ?_
  rw [Category.assoc]
  exact congrArg
    (fun t => ringUnit u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≫ t)
    (congrArg (whiskerLeft u.op) (upSheafify_comp_bridge u J O)).symm

/-- **Forgetting commutativity takes the `CommRingCat`-level sheaf unit to
`Stacks.ModuleUp.upSheafUnitRingOfCommRing`.**

This is what makes the factorization `Stacks.ModuleUp.upSheafUnit_comp_structureDescent` of a
structure map of sheaves of *commutative* rings usable at `RingCat`, where sheaves of modules
live. -/
theorem sheafCompose_map_upSheafUnit (O : Sheaf K CommRingCat.{w}) :
    (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map
        (upSheafUnit u J (A := CommRingCat.{w}) O)
      = upSheafUnitRingOfCommRing u J O :=
  InducedCategory.Hom.ext (upSheafUnitRingOfCommRing_hom_eq u J O)

/-- Pushforward of presheaves of modules along the sheafification unit of the structure ring
is a right adjoint. -/
instance isRightAdjoint_pushforward_overId_upSheafifyRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    (PresheafOfModules.pushforward.{w} (overId (upSheafifyRingOfCommRing u J O))).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (overId (upSheafifyRingOfCommRing u J O)))

/-- Pushforward of presheaves of modules along `Stacks.ModuleUp.upSheafUnitRingOfCommRing` is a
right adjoint. -/
instance isRightAdjoint_pushforward_upSheafUnitRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    (PresheafOfModules.pushforward.{w} (upSheafUnitRingOfCommRing u J O).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (upSheafUnitRingOfCommRing u J O).hom)

/-- **`f^{-1}F = (u_p F)^#` at the presheaf level**, for the unit of
`Stacks.ModuleUp.upSheafUnitRingOfCommRing`: pullback of presheaves of modules along it is the
colimit formula `u_p` of Stacks 00VC followed by the change of rings along the sheafification
unit of the structure ring. -/
noncomputable def upModulePullbackIsoOfCommRing (O : Sheaf K CommRingCat.{w}) :
    PresheafOfModules.pullback.{w} (upSheafUnitRingOfCommRing u J O).hom ≅
      upModuleFunctor u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⋙
        PresheafOfModules.pullback.{w} (overId (upSheafifyRingOfCommRing u J O)) :=
  (PresheafOfModules.pullbackComp.{w} (ringUnit u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
      (overId (upSheafifyRingOfCommRing u J O))).symm ≪≫
    isoWhiskerRight (pullbackIsoUpModuleFunctorOfColimit u
      (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) _

variable [J.WEqualsLocallyBijective RingCat.{w}]

/-- The sheafification unit of the structure ring is locally injective. -/
instance isLocallyInjective_overId_upSheafifyRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    Presheaf.IsLocallyInjective J (overId (upSheafifyRingOfCommRing u J O)) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (upSheafifyRingOfCommRing u J O))

/-- The sheafification unit of the structure ring is locally surjective. -/
instance isLocallySurjective_overId_upSheafifyRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    Presheaf.IsLocallySurjective J (overId (upSheafifyRingOfCommRing u J O)) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (upSheafifyRingOfCommRing u J O))

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **`f^{-1}F = (u_p F)^#` at the sheaf level, over `f^{-1}O` computed at `CommRingCat`.**

This is the identification the proof of Stacks 05VD turns on, in the form in which Stacks 08FC
can consume it: the inverse image of a sheaf of `O`-modules is the sheafification of the
colimit formula of Stacks 00VC over the sheafification of the structure ring.  Compared with
`Stacks.ModuleUp.upModuleSheafPullbackIso` the two change-of-rings steps of Mathlib's
`SheafOfModules.pullbackIso` have been fused into a single sheafification, by
`Stacks.ModuleUp.pullbackIdSheafificationIso`. -/
noncomputable def upModuleSheafPullbackIsoOfCommRing (O : Sheaf K CommRingCat.{w}) :
    SheafOfModules.pullback.{w} (upSheafUnitRingOfCommRing u J O) ≅
      SheafOfModules.forget (Stacks.commRingSheafToRingSheaf O) ⋙
        upModuleFunctor u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⋙
          PresheafOfModules.sheafification.{w}
            (R := Stacks.commRingSheafToRingSheaf (upSheaf u J (A := CommRingCat.{w}) O))
            (upSheafifyRingOfCommRing u J O) :=
  SheafOfModules.pullbackIso.{w} (upSheafUnitRingOfCommRing u J O) ≪≫
    isoWhiskerLeft _ (isoWhiskerRight (upModulePullbackIsoOfCommRing u J O) _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _ (pullbackIdSheafificationIso
      (overId (upSheafifyRingOfCommRing u J O))))

variable [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **`f^{-1}` preserves flatness.**  The first two paragraphs of the proof of Stacks 05VD:
flatness of `F` gives the local equational criterion of Stacks 08FC part (2), the colimit
formula `u_p` transports it, sheafification preserves it, and `f^{-1}F` is that
sheafification. -/
theorem isFlat_pullback_upSheafUnitRingOfCommRing (O : Sheaf K CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))
    (hF : Stacks.SheafOfModules.IsFlat F) :
    Stacks.SheafOfModules.IsFlat
      ((SheafOfModules.pullback.{w} (upSheafUnitRingOfCommRing u J O)).obj F) := by
  have h2 : HasLocalRelationFactorizations K (Stacks.commRingSheafToRingSheaf O).obj F.val :=
    hasLocalRelationFactorizations_of_sheaf F
      (Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse hF)
  have h3 := hasLocalRelationFactorizations_up u _ F.val
    (CoverPreserving.of_isContinuous u K J) h2
  have h4 := hasLocalRelationFactorizations_sheafify (upSheafifyRingOfCommRing u J O)
    (CategoryTheory.toSheafify J
      ((upModuleFunctor u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})).obj F.val).presheaf) h3
  have h5 := hasLocalRelationFactorizations_of_iso
    ((SheafOfModules.forget _).mapIso
      ((upModuleSheafPullbackIsoOfCommRing u J O).app F).symm) h4
  exact Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations_freeUniverse _ _
    (hasLocalSingleRelationFactorizations_of_presheaf _ h5)

/-! ### Stacks 05VD for a morphism of sites given by a continuous representably flat functor -/

variable {R : Sheaf J CommRingCat.{w}}

/-- The morphism of sheaves of rings underlying a structure map `O ⟶ f_* R` of sheaves of
commutative rings; this is the morphism `SheafOfModules.pullback` is taken along. -/
noncomputable def ringSheafMapOfPushforward {O : Sheaf K CommRingCat.{w}}
    (η : O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w} K J).obj R) :
    Stacks.commRingSheafToRingSheaf O ⟶
      (u.sheafPushforwardContinuous RingCat.{w} K J).obj
        (Stacks.commRingSheafToRingSheaf R) :=
  (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map η

/-- Pushforward of presheaves of modules along `Stacks.ModuleUp.ringSheafMapOfPushforward` is a
right adjoint. -/
instance isRightAdjoint_pushforward_ringSheafMapOfPushforward {O : Sheaf K CommRingCat.{w}}
    (η : O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w} K J).obj R) :
    (PresheafOfModules.pushforward.{w} (ringSheafMapOfPushforward u J η).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (ringSheafMapOfPushforward u J η).hom)

omit [J.WEqualsLocallyBijective RingCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The factorization of a structure map through the sheaf-level unit, at `RingCat`.

`Stacks.ModuleUp.upSheafUnit_comp_structureDescent` is the same statement for sheaves of
commutative rings; this reads it after forgetting commutativity, using
`Stacks.ModuleUp.sheafCompose_map_upSheafUnit` for the first factor. -/
theorem upSheafUnitRingOfCommRing_comp_descent {O : Sheaf K CommRingCat.{w}}
    (η : O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w} K J).obj R) :
    upSheafUnitRingOfCommRing u J O ≫ (u.sheafPushforwardContinuous RingCat.{w} K J).map
        (structureMap
      (Stacks.FlatChangeOfRings.ringSheafMap (structureDescent u J η)))
      = ringSheafMapOfPushforward u J η := by
  have h : (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map
      (upSheafUnit u J (A := CommRingCat.{w}) O ≫
        (u.sheafPushforwardContinuous CommRingCat.{w} K J).map (structureDescent u J η))
      = ringSheafMapOfPushforward u J η := by
    rw [upSheafUnit_comp_structureDescent]
    rfl
  rw [Functor.map_comp, sheafCompose_map_upSheafUnit] at h
  exact h

/-- `Stacks.ModuleUp.isFlat_pullback` with the structure map presented as a composite.  The
morphism is a bound variable so that the factorization can be substituted into it: a `rw` on the
structure map inside `SheafOfModules.pullback` has a motive that is not type correct, because
the functor carries an `IsRightAdjoint` instance depending on the morphism. -/
theorem isFlat_pullback_of_descent (O : Sheaf K CommRingCat.{w})
    (ψ : upSheaf u J (A := CommRingCat.{w}) O ⟶ R)
    (η₂ : Stacks.commRingSheafToRingSheaf O ⟶
      (u.sheafPushforwardContinuous RingCat.{w} K J).obj (Stacks.commRingSheafToRingSheaf R))
    (h : upSheafUnitRingOfCommRing u J O ≫ (u.sheafPushforwardContinuous RingCat.{w} K J).map
      (structureMap
      (Stacks.FlatChangeOfRings.ringSheafMap ψ)) = η₂)
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))
    (hF : Stacks.SheafOfModules.IsFlat F) :
    Stacks.SheafOfModules.IsFlat ((SheafOfModules.pullback.{w} η₂).obj F) := by
  subst h
  exact Stacks.ModuleUp.isFlat_of_iso
    ((SheafOfModules.pullbackComp.{w} (upSheafUnitRingOfCommRing u J O)
      (structureMap
      (Stacks.FlatChangeOfRings.ringSheafMap ψ))).app F)
    (Stacks.FlatChangeOfRings.isFlat_pullback_ringSheafMapId ψ _
      (isFlat_pullback_upSheafUnitRingOfCommRing u J O F hF))

/-- **Stacks 05VD, for a morphism of ringed sites whose underlying functor is continuous and
representably flat.**  The pullback of a flat sheaf of modules is flat.

The hypotheses are exactly the situation the source's proof reduces to: by Stacks 00X3 a
continuous functor `u` out of a site with finite limits which commutes with them is
representably flat, and by Stacks 00X6 it then defines a morphism of sites.  The reduction of an
*arbitrary* morphism of ringed topoi or ringed sites to this situation is Stacks 03CR and is not
available on this branch.

The proof splits the pullback as `f^*` = (extension of scalars along `f^♯`) ∘ `f^{-1}` using
`SheafOfModules.pullbackComp` and the factorization of the structure map through the sheaf-level
unit, applies `Stacks.ModuleUp.isFlat_pullback_upSheafUnitRingOfCommRing` to the first factor
and Stacks 05V4 to the second.

The eleven sheafification typeclasses of the `variable` block are carried here as binders; they
are all instances at a small site, and `Stacks.ModuleUp.isFlat_pullback_of_representablyFlat`
is this statement with every one of them discharged.

**This declaration carries no Stacks registration, deliberately.** It is the form with the
sheafification instances assumed, and a registration whose own note says an input is carried as a
hypothesis is a *conditional* registration: it claims the tag while deferring part of it. Tag 05VD
is registered instead on `Stacks.ModuleUp.isFlat_pullback_of_representablyFlat` below, which
proves the same conclusion with all eleven instances derived, so nothing about the tag is lost by
leaving this form untagged — it remains available to callers that hold the instances for other
reasons. -/
theorem isFlat_pullback {O : Sheaf K CommRingCat.{w}}
    (η : O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w} K J).obj R)
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))
    (hF : Stacks.SheafOfModules.IsFlat F) :
    Stacks.SheafOfModules.IsFlat
      ((SheafOfModules.pullback.{w} (ringSheafMapOfPushforward u J η)).obj F) :=
  isFlat_pullback_of_descent u J O (structureDescent u J η) _
    (upSheafUnitRingOfCommRing_comp_descent u J η) F hF

end CommRing

/-! ### Stacks 05VD for a morphism of ringed sites, with the sheafification hypotheses derived -/

section Derived

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C) [RepresentablyFlat u]
  {K : GrothendieckTopology D} (J : GrothendieckTopology C) [u.IsContinuous K J]

/-- **Stacks 05VD for a morphism of ringed sites, assuming nothing the source does not assume.**

This is `Stacks.ModuleUp.isFlat_pullback` with every sheafification hypothesis of the section
above discharged by instance search instead of assumed: `HasWeakSheafify` for `CommRingCat`,
`RingCat` and `AddCommGrpCat` on both sites, `HasSheafCompose` for
`forget₂ CommRingCat RingCat` on both sites, `WEqualsLocallyBijective` for `RingCat` and
`AddCommGrpCat` on both sites, and the two `HasLeftKanExtension` families.  All eleven are
instances of the pinned Mathlib for a small site, so what is left — `RepresentablyFlat u` and
`u.IsContinuous K J` — is exactly the situation the source's proof reduces to.

They are kept as binders in the section above because they are wanted at *elaboration* time by
the definitions there: with them removed, `Stacks.ModuleUp.upSheafUnitRingOfCommRing` no longer
elaborates and `Stacks.ModuleUp.upSheafify_comp_bridge` exhausts the `isDefEq` heartbeat budget
re-deriving `J.PreservesSheafification (forget₂ CommRingCat RingCat)`, the synthesis already
recorded as too expensive in the implementation notes.  Discharging them once, here, at the
statement of the theorem costs nothing.

**The single-universe restriction is not liftable on this branch.**  The sites are small
categories in `Type w` with the structure sheaves and modules also at `w`.  This is forced by
`PresheafOfModules.pullbackObjIsDefined_eq_top`, the only unconditional source of
`(PresheafOfModules.pushforward φ).IsRightAdjoint` and hence of `SheafOfModules.pullback`
itself, which Mathlib states for `{C D : Type u} [SmallCategory C] [SmallCategory D]` and
`RingCat.{u}`.  Nothing weaker is available, so the object, morphism and section universes
cannot be separated here without first generalizing that Mathlib declaration. -/
@[stacks 05VD "ringed sites, for a morphism of sites given by a continuous representably flat \
functor, with no sheafification hypothesis assumed: the HasWeakSheafify, HasSheafCompose, \
WEqualsLocallyBijective and HasLeftKanExtension instances are all derived. The reduction of an \
arbitrary morphism of ringed sites to this case is Stacks 03CR",
  sga "4 V 8.2.9" "representably flat u", sga "4 V 1.7.1" "representably flat u"]
theorem isFlat_pullback_of_representablyFlat {R : Sheaf J CommRingCat.{w}}
    {O : Sheaf K CommRingCat.{w}}
    (η : O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w} K J).obj R)
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf (J := K) O))
    (hF : Stacks.SheafOfModules.IsFlat (J := K) (O := O) F) :
    Stacks.SheafOfModules.IsFlat (J := J) (O := R)
      ((SheafOfModules.pullback.{w} (ringSheafMapOfPushforward u J η)).obj F) :=
  isFlat_pullback u J η F hF

end Derived

end Stacks.ModuleUp

end

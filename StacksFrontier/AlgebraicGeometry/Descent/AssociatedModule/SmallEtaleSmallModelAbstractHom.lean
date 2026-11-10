module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelModules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePullbackExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModelAbstractHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationPullback

/-!
# `ε` factored through the model, and Stacks 05VD at `ε` and on the model

`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom` presents `ε` on the `Type u` model as an
`AlgebraicGeometry.RingedToposSiteHom`, which is what the Stacks 06YY / 08H5 / 07A4 chain
consumes.  Stacks 05VD, on the other hand, is stated for the *abstract* morphism of ringed
topoi — `AlgebraicGeometry.RingedToposHom`, whose geometric datum is a morphism of the
underlying topoi — because that is the shape its proof needs.  This file records `ε` on the
model in that shape as well, as the composite of two abstract morphisms of ringed topoi:

`(model) ⟶ (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)`,

the first factor being the comparison of the small étale site with its small model and the
second the existing
`AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom`.  Stacks 03D8, the
pseudo-functoriality of the pullback of sheaves of modules, then splits the pullback along the
composite.

**Stacks 05VD applies to `ε` itself, and the factorization is not needed for it.**
`AlgebraicGeometry.SmallEtale.isFlat_pullbackModulesToZariskiAbstract` is 05VD at `ε`: the
pullback of a flat sheaf of `𝒪_S`-modules is a flat sheaf of `𝒪`-modules on the small étale
site.  05VD binds its two ringed topoi at six independent universes, so the small étale ringed
topos being a `RingedTopos.{u, u + 1, u}` — section universe strictly below object universe —
costs nothing.  In particular 05VD does not pin its source to
`RingedTopos.{v, max u v, max u v}`, and the factorization through the model serves only the
statements on the model that other files consume.

The second conclusion drawn is **the comparison-pullback of `ε^*G` is a flat sheaf of modules on
the model whenever `G` is a flat sheaf of `𝒪_S`-modules.**

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallModelToposMorphism`: the comparison of the model with the
  small étale ringed topos, as a morphism of topoi.  Its inverse image is restriction along the
  comparison of sites and its direct image is restriction back along it, the two being
  Mathlib's equivalence of sheaf categories `CategoryTheory.Equivalence.sheafCongr`.
* `AlgebraicGeometry.SmallEtale.toEtaleAbstractRingedToposHom`: the comparison as an
  `AlgebraicGeometry.RingedToposHom`, with an invertible structure map — so an equivalence of
  ringed topoi.
* `AlgebraicGeometry.SmallEtale.fromEtaleAbstractRingedToposHom`: its inverse.
* `AlgebraicGeometry.SmallEtale.toZariskiSmallModelAbstractHom`: **`ε` on the model as an
  abstract morphism of ringed topoi**, the composite of the two.
* `AlgebraicGeometry.SmallEtale.pullbackModulesToEtale`,
  `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiAbstract` and
  `AlgebraicGeometry.SmallEtale.pullbackModulesSmallModelAbstract`: the three pullbacks of
  sheaves of modules involved, named so that the universes of the two ringed topoi are solved
  for from the morphism rather than defaulted.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_toEtaleAbstractRingedToposHom_fSharp` and
  `AlgebraicGeometry.SmallEtale.isEquivalence_toEtaleAbstract_pushforward`: the comparison is an
  equivalence of ringed topoi — its direct image of sheaves of sets is an equivalence and its
  structure map is an isomorphism.  These are what make
  `AlgebraicGeometry.RingedToposHom.inverse` available.
* `AlgebraicGeometry.SmallEtale.pullbackModulesCompIsoSmallModel`: **Stacks 03D8** for the
  factorization, `ε_model^* ≅ ε^* ⋙ (comparison)^*`.
* `AlgebraicGeometry.SmallEtale.isFlat_pullbackModulesToZariskiAbstract`: **Stacks 05VD for `ε`
  itself**, on the small étale site.  The general Stacks 05VD applies verbatim, its two ringed
  topoi being bound at six independent universes.
* `AlgebraicGeometry.SmallEtale.isFlat_pullbackModulesSmallModelAbstract`: **Stacks 05VD for
  `ε` read on the model.**  The general Stacks 05VD applies verbatim, both ringed topoi being
  `RingedTopos.{u, u, u}`.
* `AlgebraicGeometry.SmallEtale.isFlat_pullbackModulesToEtale_obj`: the comparison-pullback of
  `ε^*G` is flat on the model, for `G` flat on the small Zariski site.

## Implementation notes

**A natural isomorphism this file does not build, and why 05VD does not need it.**  Stacks 05VD
for `ε` itself — that `ε^*G` is a flat sheaf of
`𝒪`-modules on the small étale site — could also be obtained from
`isFlat_pullbackModulesToEtale_obj` together with
`AlgebraicGeometry.SmallEtale.isFlat_iff_smallModelModuleRestriction`, provided the two
transports of a sheaf of modules from the small étale site to the model were identified:

`pullbackModulesToEtale B S hS ≅ smallModelModuleRestriction B S hS`.

That identification is not built here, and 05VD at `ε` does not need it: it is
`isFlat_pullbackModulesToZariskiAbstract` above, from the general 05VD at `ε` directly.  The
reduction is recorded all the same, because the isomorphism identifies two equivalences that
other statements on the model will want.  Both are equivalences — the left-hand side because the
comparison is an equivalence of ringed topoi, the right-hand side by the Comparison Lemma for
sheaves of modules — and both are left adjoints, so by uniqueness of left adjoints the
identification reduces to `smallModelModuleRestriction ⋙ pushforwardModules (comparison) ≅ 𝟭`.
On underlying sheaves of sets that composite is restriction along
`smallModelEquiv.functor ⋙ smallModelEquiv.inverse`, which the unit isomorphism of
`CategoryTheory.Equivalence.sheafCongr` identifies with the identity; upgrading that to sheaves
of modules is `Stacks.Sheaves.RingedToposModules.isoOfSheafIso` together with the two operation
checks of `Stacks.CategoryTheory.binaryOp_comp_hom_app`, exactly as
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposEquivalencePullback.lean` does it for a
self-morphism of a ringed topos.  That is not done here.

**Why that route does not go through in this shape.**  The
reduction above is correct in outline but `smallModelModuleRestriction ⋙ pushforwardModules` is
*not* of the form `pushforwardModules k` for a self-morphism `k`, so
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoId` does not apply to it.  What is
directly available is the round trip of the two *abstract* pushforwards,
`pushforwardModules (inverse f) ⋙ pushforwardModules f` for
`f = toEtaleAbstractRingedToposHom`, by `pushforwardModulesIsoId` for `f.comp (inverse f)`
followed by `pushforwardModulesCompIso`; both inputs, `inverseImageCompPushforwardIsoId f` and
`forgetRing_map_comp_inverse_fSharp f`, exist at these universes.  Reaching
`smallModelModuleRestriction` from it is the step that is missing, and it is not a step the
equivalence of topoi supplies: `pushforwardModules (inverse f)` restricts scalars along
`inv f.fSharpInverseImage`, whose source is the *inverse-image* sheaf of rings
`(inverseImageCommRingFunctor f.toToposHom).obj (ringedTopos B S hS).O`, whereas
`smallModelModuleRestriction` restricts along the identity of the *restricted* sheaf of rings
`smallModelStructureSheaf B S hS`.  Those are two different sheaves — the first a sheafified left
adjoint, the second a restriction — so the comparison is a change-of-rings equivalence along
`fSharpInverseImage` and not an identification; `(fromEtaleAbstractRingedToposHom B S hS).fSharp`
does not even have the type of an endomorphism, so no `rfl` or `eqToHom` route exists.
Independently, both assemblies of the round trip exceed the default heartbeat budget, at `whnf`
and at `isDefEq` respectively, and `attribute [local irreducible]` on
`smallModelToposMorphism`, `toEtaleAbstractRingedToposHom`, `toEtaleStructureIso`,
`pushCommRingIsoSmallModel`, `fromEtaleAbstractRingedToposHom`, `RingedToposHom.inverse`,
`MorphismOfTopoi.inverse` and `RingedToposHom.comp` moves the blowup without removing it; it
cannot be put on `ringedTopos` or `smallModelRingedTopos`, since the universes of
`Stacks.ringSheaf` are then no longer solved for from their projections.

**Flatness on the small étale site.**  Invariance of flatness under isomorphism of sheaves of
modules *on the small étale site* needs `Stacks.ModuleUp.isFlat_of_iso` at two universes, since
the small étale site has its objects in `Type (u + 1)` and its morphisms in `Type u`.  That lemma
is stated at `{C : Type u} [Category.{v} C]`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SiteUpSheafificationPullback.lean`), so it is
available on the small étale site as well as on the model.

**Why the pullbacks are named.**
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` and
`AlgebraicGeometry.RingedToposHom.comp` take their two ringed topoi as implicit arguments which
the elaborator solves *before* the morphism, so an application that leaves them out has its
universe parameters defaulted to `0` and then fails to unify with the morphism.  Each
application below passes `(X := …)`, `(Y := …)` and `(Z := …)` explicitly for that reason, and
the results are named so that downstream statements inherit the solved universes.  The same
holds for `Stacks.SheafOfModules.IsFlat`, whose site is implicit and sits *after* a
`GrothendieckTopology.HasSheafCompose` instance argument in its telescope: every occurrence
below passes `(J := …)` as well as `(O := …)`.

**The structure map of the comparison is a composite of two isomorphisms.**  The abstract direct
image of sheaves of commutative rings along the comparison is restriction along
`smallModelEquiv.functor`, by `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`; that is
`pushCommRingIsoSmallModel`.  Read through it, the structure map is
`AlgebraicGeometry.SmallEtale.toEtaleStructureIso`, which is the unit isomorphism of the
equivalence of sheaf categories.  So `fSharp` is invertible by construction and no separate
argument is needed.

**The comparison itself is not built here.**  `smallModelToposMorphism`,
`pushCommRingIsoSmallModel`, `toEtaleAbstractRingedToposHom` and
`fromEtaleAbstractRingedToposHom` are
`AlgebraicGeometry.RingedTopos.smallModelToposMorphism`,
`.pushforwardCommRingIsoSmallModel`, `.toSmallModelAbstractHom` and `.fromSmallModelAbstractHom`
of `StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModelAbstractHom`, instantiated at
the small étale ringed topos of `S`; nothing about them is special to that site.  Each
instantiation hands `AlgebraicGeometry.SmallEtale.essentiallySmall` over in a `letI`, because the
structure projection `(ringedTopos B S hS).C` does not reduce at instance transparency and the
instance is therefore not found at the generic spelling.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER), part (3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison as a morphism of topoi -/

/-- **The comparison of the `Type u` model with the small étale ringed topos, as a morphism of
topoi.**  Its inverse image is restriction of sheaves of sets along the comparison of sites and
its direct image is restriction back along it; the two are the functor and the inverse of
Mathlib's equivalence of sheaf categories `CategoryTheory.Equivalence.sheafCongr`, on the nose,
so the adjunction is that equivalence read as an adjunction and the left exactness of the
inverse image is unconditional.

This is `AlgebraicGeometry.RingedTopos.smallModelToposMorphism`, the generic comparison of a
ringed topos with its equi-universe model, at the small étale ringed topos of `S`; essential
smallness is handed over by `AlgebraicGeometry.SmallEtale.essentiallySmall`, since the structure
projection `(ringedTopos B S hS).C` does not reduce at instance transparency. -/
public noncomputable def smallModelToposMorphism :
    MorphismOfTopoi (smallModelRingedTopos B S hS).Topos (ringedTopos B S hS).Topos :=
  letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
  RingedTopos.smallModelToposMorphism (ringedTopos B S hS)

/-- The direct image of sheaves of sets along the comparison is an equivalence of topoi, being
the inverse of `CategoryTheory.Equivalence.sheafCongr`. -/
public instance isEquivalence_smallModelToposMorphism_pushforward :
    (smallModelToposMorphism B S hS).pushforward.IsEquivalence :=
  letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
  RingedTopos.isEquivalence_smallModelToposMorphism_pushforward (ringedTopos B S hS)

/-- **The abstract direct image of sheaves of commutative rings along the comparison is
restriction along the comparison of sites.**  The identification is the identity on sections. -/
public noncomputable def pushCommRingIsoSmallModel :
    pushforwardCommRingFunctor.{u, u, u, u, u, u + 1} (smallModelToposMorphism B S hS) ≅
      (smallModelEquiv B S hS).functor.sheafPushforwardContinuous CommRingCat.{u}
        (topology B S hS) (smallModelTopology B S hS) :=
  letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
  RingedTopos.pushforwardCommRingIsoSmallModel (ringedTopos B S hS)

/-- The identification of the abstract direct image of the structure sheaf of the model with its
restriction along the comparison of sites, which is the target of
`AlgebraicGeometry.SmallEtale.toEtaleStructureIso`. -/
public noncomputable abbrev pushforwardStructureIsoSmallModel :
    (pushforwardCommRingFunctor.{u, u, u, u, u, u + 1} (smallModelToposMorphism B S hS)).obj
        (smallModelRingedTopos B S hS).O ≅
      ((smallModelEquiv B S hS).functor.sheafPushforwardContinuous CommRingCat.{u}
        (topology B S hS) (smallModelTopology B S hS)).obj (smallModelRingedTopos B S hS).O :=
  (pushCommRingIsoSmallModel B S hS).app (smallModelRingedTopos B S hS).O

/-! ### The comparison as an abstract morphism of ringed topoi -/

/-- **The comparison of the model with the small étale ringed topos, as an abstract morphism of
ringed topoi** `(model) ⟶ (S_étale, 𝒪)`.  The geometric datum is
`AlgebraicGeometry.SmallEtale.smallModelToposMorphism` and the structure map is the unit
isomorphism `AlgebraicGeometry.SmallEtale.toEtaleStructureIso` read through
`pushforwardStructureIsoSmallModel`. -/
public noncomputable def toEtaleAbstractRingedToposHom :
    AlgebraicGeometry.RingedToposHom (smallModelRingedTopos B S hS) (ringedTopos B S hS) :=
  letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
  RingedTopos.toSmallModelAbstractHom (ringedTopos B S hS)

/-- The underlying morphism of topoi of `toEtaleAbstractRingedToposHom` is
`smallModelToposMorphism`. -/
@[simp]
public theorem toEtaleAbstractRingedToposHom_toToposHom :
    (toEtaleAbstractRingedToposHom B S hS).toToposHom = smallModelToposMorphism B S hS := rfl

/-- The structure map of `toEtaleAbstractRingedToposHom` is the composite of `toEtaleStructureIso`
with the inverse of `pushforwardStructureIsoSmallModel`. -/
@[simp]
public theorem toEtaleAbstractRingedToposHom_fSharp :
    (toEtaleAbstractRingedToposHom B S hS).fSharp =
      (toEtaleStructureIso B S hS).hom ≫ (pushforwardStructureIsoSmallModel B S hS).inv := rfl

/-- **The structure map of the comparison is an isomorphism**, being a composite of two
isomorphisms.  With the direct image an equivalence of topoi, this says that the comparison is
an equivalence of ringed topoi. -/
public instance isIso_toEtaleAbstractRingedToposHom_fSharp :
    IsIso (toEtaleAbstractRingedToposHom B S hS).fSharp :=
  letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
  RingedTopos.isIso_toSmallModelAbstractHom_fSharp (ringedTopos B S hS)

/-- The direct image of the comparison, at the spelling in which
`AlgebraicGeometry.RingedToposHom.inverse` demands it.  A structure projection does not unfold
at instance transparency, so the instance has to be restated here. -/
public instance isEquivalence_toEtaleAbstract_pushforward :
    (toEtaleAbstractRingedToposHom B S hS).toToposHom.pushforward.IsEquivalence :=
  isEquivalence_smallModelToposMorphism_pushforward B S hS

/-- **The inverse of the comparison**, an abstract morphism of ringed topoi
`(S_étale, 𝒪) ⟶ (model)`.  Its geometric datum is the comparison's read backwards and its
structure map is the inverse of the inverse-image form of the comparison's. -/
public noncomputable def fromEtaleAbstractRingedToposHom :
    AlgebraicGeometry.RingedToposHom (ringedTopos B S hS) (smallModelRingedTopos B S hS) :=
  letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
  RingedTopos.fromSmallModelAbstractHom (ringedTopos B S hS)

/-- **`ε` on the model as an abstract morphism of ringed topoi**, the composite of the
comparison with the abstract form `AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom`
of `ε`.  Both of its ringed topoi are `AlgebraicGeometry.RingedTopos.{u, u, u}`, which is the
universe shape Stacks 05VD is available at. -/
public noncomputable abbrev toZariskiSmallModelAbstractHom :=
  AlgebraicGeometry.RingedToposHom.comp (X := smallModelRingedTopos B S hS)
    (Y := ringedTopos B S hS) (Z := S.zariskiRingedTopos)
    (toZariskiAbstractRingedToposHom B S hS) (toEtaleAbstractRingedToposHom B S hS)

/-! ### The three pullbacks of sheaves of modules -/

/-- The pullback of sheaves of modules along the comparison, `Mod(𝒪) ⥤ Mod(𝒪_model)`.  This is
the transport which `isFlat_pullbackModulesToEtale_obj` below computes flatness through. -/
public noncomputable abbrev pullbackModulesToEtale :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallModelRingedTopos B S hS)
    (Y := ringedTopos B S hS) (toEtaleAbstractRingedToposHom B S hS).toModulesHom

/-- `ε^*` on sheaves of modules, for the abstract form of `ε`, `Mod(𝒪_S) ⥤ Mod(𝒪)`. -/
public noncomputable abbrev pullbackModulesToZariskiAbstract :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := ringedTopos B S hS)
    (Y := S.zariskiRingedTopos) (toZariskiAbstractRingedToposHom B S hS).toModulesHom

/-- `ε_model^*` on sheaves of modules, `Mod(𝒪_S) ⥤ Mod(𝒪_model)`.  The result type is ascribed
with the underlying sheaves of rings written as
`Stacks.commRingSheafToRingSheaf`, the spelling `Stacks.SheafOfModules.IsFlat` is stated at, so
that the flatness statements below elaborate without further universe annotations. -/
public noncomputable abbrev pullbackModulesSmallModelAbstract :
    _root_.SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf
        (J := Opens.grothendieckTopology ↥S) S.zariskiCommRingSheaf) ⥤
      _root_.SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf
        (J := smallModelTopology B S hS) (smallModelStructureSheaf B S hS)) :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallModelRingedTopos B S hS)
    (Y := S.zariskiRingedTopos) (toZariskiSmallModelAbstractHom B S hS).toModulesHom

/-- **Stacks 03D8 for the factorization of `ε` through the model.**  The pullback of sheaves of
modules along `ε_model` is `ε^*` followed by the pullback along the comparison. -/
public noncomputable def pullbackModulesCompIsoSmallModel :
    pullbackModulesSmallModelAbstract B S hS ≅
      pullbackModulesToZariskiAbstract B S hS ⋙ pullbackModulesToEtale B S hS :=
  AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
    (toEtaleAbstractRingedToposHom B S hS) (toZariskiAbstractRingedToposHom B S hS)

/-! ### Stacks 05VD at `ε`, and on the model -/

/-- **Stacks 05VD for `ε` itself**: the pullback along `ε` of a flat sheaf of `𝒪_S`-modules is a
flat sheaf of `𝒪`-modules **on the small étale site**.

This is the general Stacks 05VD,
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`, applied verbatim at `ε`.  It is
available because that theorem binds its two ringed topoi at six independent universes; the
small étale ringed topos is a `RingedTopos.{u, u + 1, u}`, whose section universe lies strictly
below its object universe, and nothing about it has to be adjusted.  The typeclass hypotheses
05VD asks of the source are the small étale site's own — a sheafification of type-valued
presheaves, one of abelian presheaves, and the locally-bijective description of the weak
equivalences — all of which it has by being essentially small in the universe of its sections.

The sheafification instance is restated at the projection `(ringedTopos B S hS).J` rather than
synthesized, for the reason `AlgebraicGeometry.SmallEtale.hasWeakSheafify_ringedTopos_J` records
of the abelian one: `AlgebraicGeometry.SmallEtale.ringedTopos` is a `def` whose field does not
unfold at instance transparency.  It is introduced with `have`, so no new global instance is
registered. -/
public theorem isFlat_pullbackModulesToZariskiAbstract
    (G : _root_.SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf
      (J := Opens.grothendieckTopology ↥S) S.zariskiCommRingSheaf))
    (hG : Stacks.SheafOfModules.IsFlat (J := Opens.grothendieckTopology ↥S)
      (O := S.zariskiCommRingSheaf) G) :
    Stacks.SheafOfModules.IsFlat (J := topology B S hS)
      (O := commRingStructureSheaf B S hS)
      ((pullbackModulesToZariskiAbstract B S hS).obj G) := by
  have : HasSheafify (ringedTopos B S hS).J (Type u) :=
    inferInstanceAs (HasSheafify (topology B S hS) (Type u))
  exact Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules
    (toZariskiAbstractRingedToposHom B S hS).toModulesHom G hG

/-- **Stacks 05VD for `ε` read on the model.**  The pullback along `ε_model` of a flat sheaf of
`𝒪_S`-modules is a flat sheaf of modules on the model.

This is the general Stacks 05VD,
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`, applied verbatim at `ε_model`, the
model and the small Zariski ringed topos of `S` both being `RingedTopos.{u, u, u}`. -/
public theorem isFlat_pullbackModulesSmallModelAbstract
    (G : _root_.SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf
      (J := Opens.grothendieckTopology ↥S) S.zariskiCommRingSheaf))
    (hG : Stacks.SheafOfModules.IsFlat (J := Opens.grothendieckTopology ↥S)
      (O := S.zariskiCommRingSheaf) G) :
    Stacks.SheafOfModules.IsFlat (J := smallModelTopology B S hS)
      (O := smallModelStructureSheaf B S hS)
      ((pullbackModulesSmallModelAbstract B S hS).obj G) :=
  Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules
    (toZariskiSmallModelAbstractHom B S hS).toModulesHom G hG

/-- **The comparison-pullback of `ε^*G` is flat on the model**, for `G` a flat sheaf of
`𝒪_S`-modules on the small Zariski site of `S`.

This is `isFlat_pullbackModulesSmallModelAbstract` transported along Stacks 03D8 for the
factorization, flatness being invariant under isomorphism of sheaves of modules
(`Stacks.ModuleUp.isFlat_of_iso`).

It is Stacks 05VD for `ε` up to one identification: with
`pullbackModulesToEtale B S hS ≅ smallModelModuleRestriction B S hS` in hand,
`AlgebraicGeometry.SmallEtale.isFlat_iff_smallModelModuleRestriction` turns this into the
flatness of `ε^*G` as a sheaf of `𝒪`-modules on the small étale site itself. -/
public theorem isFlat_pullbackModulesToEtale_obj
    (G : _root_.SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf
      (J := Opens.grothendieckTopology ↥S) S.zariskiCommRingSheaf))
    (hG : Stacks.SheafOfModules.IsFlat (J := Opens.grothendieckTopology ↥S)
      (O := S.zariskiCommRingSheaf) G) :
    Stacks.SheafOfModules.IsFlat (J := smallModelTopology B S hS)
      (O := smallModelStructureSheaf B S hS)
      ((pullbackModulesToEtale B S hS).obj
        ((pullbackModulesToZariskiAbstract B S hS).obj G)) :=
  Stacks.ModuleUp.isFlat_of_iso (J := smallModelTopology B S hS)
    (O := smallModelStructureSheaf B S hS)
    ((pullbackModulesCompIsoSmallModel B S hS).app G)
    (isFlat_pullbackModulesSmallModelAbstract B S hS G hG)

end AlgebraicGeometry.SmallEtale

end

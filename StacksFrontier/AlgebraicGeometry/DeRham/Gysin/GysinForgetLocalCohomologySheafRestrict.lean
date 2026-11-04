module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinAbelianExcisionBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinSupportCohomologyOnEndoIso

/-!
# Forgetting the module structure commutes with excision, in every degree

Let `Y` be a scheme, `T ⊆ Y` a closed subset, `W ⊆ Y` an open subscheme and `n` a degree.  Local
cohomology with supports in `T` is local on `Y` in two parallel senses:

* for `𝒪_Y`-modules, as `Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`;
* for sheaves of abelian groups, in the spelling of the Gysin target of [Stacks, Tag 0G87], as
  `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso`.

This file proves that the two agree across [Stacks, Tag 0G74] part (2):
`forget_localCohomologySheafRestrict_comm`.  It is the **degree-`n` analogue of
`Stacks.Cohomology.SupportedComplexes.forget_supportedSectionsRestrict_comm`**, whose module
docstring records the degree-zero case and names the general degree as what the square of
[Stacks, Tag 0G87] needs.

## Main results

* `Stacks.Gysin.localCohomologyForgetLeg_eq`: **[Stacks, Tag 0G74] part (2) in degree `n`, at the
  spelling of `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn`** — the comparison
  `ℋ ⁿ_T(ℱ)_ab ⟶ i_*ℋ ⁿ_T(ℱ_ab)` obtained from the Gysin-spelling comparison
  `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso` by the bridge
  `Stacks.Gysin.supportCohomologyOnIso` — is the degree-`n` endofunctor comparison
  `Stacks.Cohomology.DegreewiseExcisionSquare.localCohomologyEndoForgetComparison` followed by
  `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso` inverted.
* `Stacks.Gysin.abelianLocalCohomologySheafRestrict_hom_app`: the abelian excision with the direct
  image from the closed subset folded in, written out as the endofunctor excision conjugated by
  `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso`.  True by
  definition.
* `Stacks.Gysin.restrictAbelian_map_localCohomologyForgetLeg`: that leg, restricted to the chart
  and split into its two factors.
* `Stacks.Gysin.forget_localCohomologySheafRestrict_comm`: **the degree-`n` square.**

## Implementation notes

**All the mathematics is in two inputs from the library.**  The square at the supported-sections
*endofunctor* spelling is
`Stacks.Cohomology.DegreewiseExcisionSquare.forget_localCohomologyRestrict_comm`, and the
identification of the two spellings of [Stacks, Tag 0G74] part (2) is
`supportCohomologySheafForgetIso_eq_localCohomologyEndoForget` of
`Stacks.Perfect.SupportedEndoForgetEndofunctor`.
What this file adds is the passage between the two spellings of each functor in sight, and the
cancellation of the bridge `Stacks.Gysin.supportCohomologyOnIso` against itself.

**Where the two readings meet, and what that costs.**  The degreewise square is stated at
`Stacks.Cohomology.RestrictForgetComparison.restrictModules`, `..restrictAbelian`,
`CategoryTheory.SheafOfModules.toSheaf` and
`Stacks.Cohomology.DegreewiseExcisionSquare.moduleExcisionEndo`; the Gysin side is stated at
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, `Stacks.Gysin.abelianRestrict`,
`Stacks.Perfect.AbelianFraction.abelianSheaf` and
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`.  Each pair is
*definitionally* equal, and each pair can be crossed by a `rfl` in a declaration of its own; what
cannot be done is to cross a pair inside a **composite** more than once per declaration.  The
measurements, all made with `drake` against the standard 200,000-heartbeat budget:

* `(abelianSheaf W).map φ = toSheaf_W.map φ'` with `φ` the module excision in either reading:
  about 15,000 heartbeats.  `(restrictAbelian W).map ψ = (abelianRestrict W).map ψ`: about 1,500.
  An equality of two *objects* across the pair, however deep: under the budget.
* the same two readings of one **two-factor composite**, as an `Eq`: about 190,000 — under the
  budget, but only just, and `attribute [local implicit_reducible]` on the five definitions below
  is what brings it there.
* an `Eq` **between two equations** in the two readings — which is what `exact`ing a lemma stated
  in one reading at a goal stated in the other amounts to — is two of those and does not fit.

So the chase is carried out entirely inside the reading of
`Stacks.Cohomology.DegreewiseExcisionSquare`: `localCohomologyForgetLeg_eq` and
`abelianLocalCohomologySheafRestrict_hom_app` are stated with the degreewise side first, the
functor the two halves are applied at is `restrictAbelian` and not `abelianRestrict`, and
`square_general` leaves every object the two readings disagree about a *variable*, so that
instantiating it crosses objects and never composites.  The leg on `Y` is for the same reason
left in the endofunctor-plus-bridge form in `forget_localCohomologySheafRestrict_comm`;
`restrictAbelian_map_localCohomologyForgetLeg` is the conversion to the Gysin-leg form, and
composing the two in one declaration is exactly the equation-against-equation check that does not
fit.  This is the concrete form of the obstacle recorded in
`Stacks.Cohomology.SupportedComplexes.LocalCohomologyExcisionPullbackDerived`.

**Every chase is a helper at a variable category, applied with `exact`.**  `rw` on a factor of
one of these composites fails: `kabstract` does not find a pattern that is printed verbatim in the
goal, the occurrence carrying the other reading's instances.  `rewrite_head`, `cancel_leg`,
`leg_half` and `leg_rest` are the four formal identities, each stated at arbitrary categories with
the objects implicit and the morphisms explicit.

**No `@[stacks ...]` attribute is attached to any declaration here.**  Every statement is a
compatibility between results that carry their own tags; the square of [Stacks, Tag 0G87] is what
this is an input to, and it is registered on
`Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`.  The degree-`n` square
below is what `Stacks.Gysin.excisionAbComparison_eq_abelianExcision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean` consumes, and the
obstacle recorded above — that composing it with `localCohomologyForgetLeg_eq` into the
all-Gysin-leg form does not fit the heartbeat budget — is not on that path: there the two readings
meet once, in a declaration whose two sides differ in one factor each.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit (derivedAbelianSupportedPushforward
  derivedAbelianSupportedPushforwardUnit)
open Stacks.Cohomology.DegreewiseExcisionSquare (abelianExcisionEndo moduleExcisionEndo
  localCohomologyEndoForgetComparison localCohomologyEndoForgetComparisonOpen)
open Stacks.Cohomology.RestrictForgetComparison (restrictAbelian restrictModules)
open Stacks.Cohomology.SupportedComplexes (abelianLocalCohomologyRestrictNatIso
  abelianLocalCohomologySheafPushforwardIso abelianLocalCohomologySheafRestrictNatIso
  abelianSupportedSections)
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.GysinAbelianSquare (abelianLocalCohomologyPushforward
  supportCohomologySheafForgetIso)
open Stacks.Perfect.LocalCohomologyExcision (localCohomologyRestrictNatIso)
open Stacks.Perfect.SupportedEndoForgetEndofunctor
  (supportCohomologySheafForgetIso_eq_localCohomologyEndoForget)
open Stacks.Perfect.SupportedFraction (supportPush)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforwardUnit)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  Stacks.Perfect.AbelianFraction.abelianSheaf Stacks.Gysin.abelianRestrict
  Stacks.Cohomology.DegreewiseExcisionSquare.moduleExcisionEndo
  Stacks.Cohomology.DegreewiseExcisionSquare.abelianExcisionEndo
  Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn
  Stacks.Perfect.LocalCohomologyExcision.supportedSectionsOn
  Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso
  Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso

/-! ### Formal identities, each at arbitrary categories -/

/-- **The head of a functor image re-spelled.**  Given `s = Fn.map f ≫ r` and `f = f'`, also
`s = Fn.map f' ≫ r`.

Stated at arbitrary categories, every object implicit and every morphism explicit: `f` and `f'`
are then read off the given equation instead of being solved for, and the crossing of two
definitionally equal spellings of one category is met by a single definitional check. -/
private theorem rewrite_head {D E : Type*} [Category* D] [Category* E] (Q : D ⥤ E)
    {a b : D} {z : E} (f f' : a ⟶ b) (r : Q.obj b ⟶ z) (s : Q.obj a ⟶ z)
    (hs : s = Q.map f ≫ r) (h : f = f') : s = Q.map f' ≫ r := by
  rw [hs, h]

/-- **A functor image cancelled against a comparison it is inverse to.**  Given `i ≫ j = 𝟙` and
`s = Q.map j ≫ r₁ ≫ r₂`, the composite `Q.map i ≫ s` is `r₁ ≫ r₂`.

Stated at arbitrary categories, every object implicit and every morphism explicit. -/
private theorem cancel_leg {D E : Type*} [Category* D] [Category* E] (Q : D ⥤ E)
    {a b : D} {c d : E} (i : a ⟶ b) (j : b ⟶ a) (s : Q.obj b ⟶ d) (r₁ : Q.obj a ⟶ c)
    (r₂ : c ⟶ d) (hs : s = Q.map j ≫ r₁ ≫ r₂) (hij : i ≫ j = CategoryStruct.id a) :
    Q.map i ≫ s = r₁ ≫ r₂ := by
  rw [hs, ← Category.assoc, ← Q.map_comp, hij, Q.map_id, Category.id_comp]

/-- **Half of a square conjugated by a pair of mutually inverse comparisons**: the factorisation
`ps = g ≫ z` of the leg turns the square `mex ≫ g = rr` into `mex ≫ ps = rr ≫ z`.

Stated at an arbitrary category with the objects implicit and the morphisms explicit. -/
private theorem leg_half {D : Type*} [Category* D] {a b m t : D}
    (mex : a ⟶ b) (ps : b ⟶ t) (g : b ⟶ m) (z : m ⟶ t) (rr : a ⟶ m)
    (hps : ps = g ≫ z) (hsq : mex ≫ g = rr) : mex ≫ ps = rr ≫ z := by
  rw [hps, ← Category.assoc, hsq]

/-- **The other half**: the pair `zz ≫ uu = 𝟙` and the reading `ee = Fn.map uu ≫ e ≫ z` of the
target comparison turn `(rgg ≫ e) ≫ z` into `rleg ≫ ee`, given the factorisation
`rleg = rgg ≫ Fn.map zz`.

Stated at arbitrary categories with the objects implicit and the morphisms explicit; the source of
`rgg` is a free object rather than `Fn.obj` of one, so that applying it never asks the elaborator
to invert `Fn` on an object. -/
private theorem leg_rest {D E : Type*} [Category* D] [Category* E] (Fn : D ⥤ E)
    {a m t : E} {y c : D}
    (z : m ⟶ t) (rleg : a ⟶ Fn.obj c) (rgg : a ⟶ Fn.obj y) (zz : y ⟶ c)
    (uu : c ⟶ y) (e : Fn.obj y ⟶ m) (ee : Fn.obj c ⟶ t)
    (hleg : rleg = rgg ≫ Fn.map zz)
    (hzu : zz ≫ uu = CategoryStruct.id y) (hee : ee = Fn.map uu ≫ e ≫ z) :
    (rgg ≫ e) ≫ z = rleg ≫ ee := by
  rw [hleg, Category.assoc, Category.assoc, cancel_leg Fn zz uu ee e z hee hzu]

/-! ### Stacks 0G74 part (2) in degree `n`, at the `localCohomologyOn` spelling -/

section Leg

variable {X : Scheme.{u}} {T : Set X} (hT : IsClosed T) (n : ℕ) (F : X.Modules)

/-- **[Stacks, Tag 0G74] part (2) in degree `n`, read from the endofunctor spelling onto
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn`.**

For a scheme `X`, a closed subset `T ⊆ X`, a degree `n` and an `𝒪_X`-module `ℱ`, the degree-`n`
endofunctor comparison
`Stacks.Cohomology.DegreewiseExcisionSquare.localCohomologyEndoForgetComparison`, followed by
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso` inverted — the
identification of the right derived functors of the abelian supported sections with the abelian
local cohomology sheaves pushed forward from `T` — is the Gysin-spelling comparison
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso` preceded by the bridge
`Stacks.Gysin.supportCohomologyOnIso` inverted:

`ℋ ⁿ_T(ℱ)_ab ⟶ i_*ℋ ⁿ_T(ℱ_ab)`.

This is
`supportCohomologySheafForgetIso_eq_localCohomologyEndoForget` of
`Stacks.Perfect.SupportedEndoForgetEndofunctor` with the module-side bridge cancelled, the
cancellation being legitimate because that bridge *is* `Stacks.Gysin.supportCohomologyOnIso`, by
`Stacks.Gysin.supportCohomologyOnIso_eq_endoIso`.

The equation is stated with the endofunctor side first on purpose: its two sides are composites in
two definitionally equal readings of the category of abelian sheaves on `X`, and writing the
endofunctor side first fixes the reading to the one the degree-`n` square of
[Stacks, Tag 0G87] speaks, so that the reading of the Gysin target is met exactly once, at the end
of `forget_localCohomologySheafRestrict_comm`. -/
theorem localCohomologyForgetLeg_eq :
    (localCohomologyEndoForgetComparison T (supportPush hT)
          (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
          (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
          (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT) n).app F ≫
        (abelianLocalCohomologySheafPushforwardIso T hT n).inv.app ((abelianSheaf X).obj F) =
      (abelianSheaf X).map ((supportCohomologyOnIso X T hT n).inv.app F) ≫
        (supportCohomologySheafForgetIso hT n).hom.app F :=
  (cancel_leg (abelianSheaf X) _ _ _ _ _
    (rewrite_head (abelianSheaf X) _ _ _ _
      (supportCohomologySheafForgetIso_eq_localCohomologyEndoForget hT n F)
      (supportCohomologyOnIso_hom_app_eq_endoIso X T hT n F).symm)
    (Iso.inv_hom_id_app (supportCohomologyOnIso X T hT n) F)).symm

end Leg

/-! ### The degree-`n` square -/

variable {Y : Scheme.{u}} (W : Y.Opens) {T : Set Y} (hT : IsClosed T)
  (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℕ) (F : Y.Modules)

/-- **The abelian excision with the direct image from the closed subset folded in, written
out.**  `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso` is by
definition the endofunctor excision
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` — here in the ascribed
spelling `Stacks.Cohomology.DegreewiseExcisionSquare.abelianExcisionEndo`, which is it — conjugated
by `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso` on `Y` and on
the chart.  This records that reading at the underlying abelian sheaf of a module. -/
theorem abelianLocalCohomologySheafRestrict_hom_app :
    (restrictAbelian W).map
          ((abelianLocalCohomologySheafPushforwardIso T hT n).hom.app
            ((abelianSheaf Y).obj F)) ≫
        (abelianExcisionEndo T W n).hom.app
            ((_root_.SheafOfModules.toSheaf (structureSheafRing Y.toRingedSpace)).obj F) ≫
          (abelianLocalCohomologySheafPushforwardIso (W.ι ⁻¹' T) hTW n).inv.app
            ((abelianSheaf W.toScheme).obj ((Scheme.Modules.restrictFunctor W.ι).obj F)) =
      (abelianLocalCohomologySheafRestrictNatIso (X := Y.carrier) T W hT hTW n).hom.app
        ((abelianSheaf Y).obj F) := rfl

/-- The degree-`n` comparison of [Stacks, Tag 0G74] part (2) on `Y`, restricted to the chart and
split into its two factors.  This is `localCohomologyForgetLeg_eq` carried through
`Stacks.Cohomology.RestrictForgetComparison.restrictAbelian`. -/
theorem restrictAbelian_map_localCohomologyForgetLeg :
    (restrictAbelian W).map
        ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).inv.app F) ≫
          (supportCohomologySheafForgetIso hT n).hom.app F) =
      (restrictAbelian W).map
          ((localCohomologyEndoForgetComparison T (supportPush hT)
            (derivedSupportedPushforwardUnit Y.toRingedSpace T hT)
            (derivedAbelianSupportedPushforward Y.toRingedSpace T hT)
            (derivedAbelianSupportedPushforwardUnit Y.toRingedSpace T hT) n).app F) ≫
        (restrictAbelian W).map
          ((abelianLocalCohomologySheafPushforwardIso T hT n).inv.app
            ((abelianSheaf Y).obj F)) :=
  (congrArg (restrictAbelian W).map (localCohomologyForgetLeg_eq hT n F)).symm.trans
    ((restrictAbelian W).map_comp _ _)

/-- **The tail of the chase**: the bridge
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso` on `Y` cancelled
against its inverse, and the endofunctor excision read back as
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso`.

The source `A` of the two restricted legs is left a variable: the one place the two readings of
the category of abelian sheaves on the chart have to meet is then a comparison of *objects*, made
once when this is applied, instead of a comparison of composites. -/
private theorem square_tail
    {A : Sheaf (Opens.grothendieckTopology W.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u}}
    (rgg : A ⟶ (restrictAbelian W).obj
        ((_root_.SheafOfModules.toSheaf (structureSheafRing Y.toRingedSpace) ⋙
          (abelianSupportedSections T).rightDerived n).obj F))
    :
    (rgg ≫ (abelianExcisionEndo T W n).hom.app
            ((_root_.SheafOfModules.toSheaf (structureSheafRing Y.toRingedSpace)).obj F)) ≫
        (abelianLocalCohomologySheafPushforwardIso (W.ι ⁻¹' T) hTW n).inv.app
          ((abelianSheaf W.toScheme).obj ((Scheme.Modules.restrictFunctor W.ι).obj F)) =
      (rgg ≫ (restrictAbelian W).map
            ((abelianLocalCohomologySheafPushforwardIso T hT n).inv.app
              ((abelianSheaf Y).obj F))) ≫
        (abelianLocalCohomologySheafRestrictNatIso (X := Y.carrier) T W hT hTW n).hom.app
          ((abelianSheaf Y).obj F) :=
  leg_rest (restrictAbelian W) _ _ _ _ _ _ _ rfl
    (Iso.inv_hom_id_app (abelianLocalCohomologySheafPushforwardIso T hT n)
      ((abelianSheaf Y).obj F))
    (abelianLocalCohomologySheafRestrict_hom_app W hT hTW n F).symm

/-- **The whole chase, with every object that the two readings of the category of abelian sheaves
disagree about left a variable.**  Given a morphism `mex` into the source of the chart's leg, the
degreewise square `hsq` and the factorisation `hleg` of the restricted ambient leg, the square
holds.  `leg_half` folds the chart's copy of [Stacks, Tag 0G74] part (2) into the leg and
`square_tail` the ambient one.

Nothing here crosses the two readings: `A`, `rgg` and `rleg` are variables, so the crossing is met
once, when this is applied in `forget_localCohomologySheafRestrict_comm`, and there it is a
comparison of objects and not of composites. -/
private theorem square_general
    {A : Sheaf (Opens.grothendieckTopology W.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u}}
    (mex : A ⟶ ((Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor
          W.toScheme.toRingedSpace (W.ι ⁻¹' T)).rightDerived n ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing W.toScheme.toRingedSpace)).obj
      ((Scheme.Modules.restrictFunctor W.ι).obj F))
    (rgg : A ⟶ (restrictAbelian W).obj
        ((_root_.SheafOfModules.toSheaf (structureSheafRing Y.toRingedSpace) ⋙
          (abelianSupportedSections T).rightDerived n).obj F))
    (hsq : mex ≫ (localCohomologyEndoForgetComparisonOpen T W (supportPush hTW)
            (derivedSupportedPushforwardUnit W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW)
            (derivedAbelianSupportedPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW)
            (derivedAbelianSupportedPushforwardUnit W.toScheme.toRingedSpace
              (W.ι ⁻¹' T) hTW) n).app
          ((Scheme.Modules.restrictFunctor W.ι).obj F) =
      rgg ≫ (abelianExcisionEndo T W n).hom.app
        ((_root_.SheafOfModules.toSheaf (structureSheafRing Y.toRingedSpace)).obj F)) :
    mex ≫ ((abelianSheaf W.toScheme).map
            ((supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.app
              ((Scheme.Modules.restrictFunctor W.ι).obj F)) ≫
          (supportCohomologySheafForgetIso hTW n).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj F)) =
      (rgg ≫ (restrictAbelian W).map
            ((abelianLocalCohomologySheafPushforwardIso T hT n).inv.app
              ((abelianSheaf Y).obj F))) ≫
        (abelianLocalCohomologySheafRestrictNatIso (X := Y.carrier) T W hT hTW n).hom.app
          ((abelianSheaf Y).obj F) :=
  (leg_half mex _ _ ((abelianLocalCohomologySheafPushforwardIso (W.ι ⁻¹' T) hTW n).inv.app
          ((abelianSheaf W.toScheme).obj ((Scheme.Modules.restrictFunctor W.ι).obj F))) _
    (localCohomologyForgetLeg_eq hTW n ((Scheme.Modules.restrictFunctor W.ι).obj F)).symm
    hsq).trans (square_tail W hT hTW n F rgg)

/-- **Forgetting the module structure commutes with excision, in every degree.**

For a scheme `Y`, a closed subset `T ⊆ Y`, an open subscheme `W ⊆ Y`, a degree `n` and an
`𝒪_Y`-module `ℱ`, the square

`ℋ ⁿ_T(ℱ)|_W ⟶ ℋ ⁿ_{W ∩ T}(ℱ|_W)` read on abelian sheaves, versus
`(i_*ℋ ⁿ_T(ℱ_ab))|_W ⟶ i'_*ℋ ⁿ_{W ∩ T}(ℱ_ab|_W)`,

commutes: the module excision
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` — here at the ascribed
spelling `Stacks.Cohomology.DegreewiseExcisionSquare.moduleExcisionEndo`, which is it — carried
along the forgetful functor and then through [Stacks, Tag 0G74] part (2) on the chart, is
[Stacks, Tag 0G74] part (2) on `Y` restricted to the chart, followed by the abelian excision
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso`.

The leg on the chart is the one of `localCohomologyForgetLeg_eq`: the Gysin-spelling comparison
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso` read at
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn` through the bridge
`Stacks.Gysin.supportCohomologyOnIso`.  The leg on `Y` is the same comparison, written in the
endofunctor form `localCohomologyForgetLeg_eq` identifies it with — the degree-`n` endofunctor
comparison followed by the pushforward bridge inverted — and
`restrictAbelian_map_localCohomologyForgetLeg` converts between the two forms; that it is written
in this form here and not the other is forced by the heartbeat budget, see the implementation
notes.

That the equation is well-typed is the underived identity
`Stacks.Gysin.restrictFunctorCompAbelianSheafIso`: restricting a module to `W` and forgetting
*is* forgetting and restricting the abelian sheaf.

This is the **degree-`n` analogue of
`Stacks.Cohomology.SupportedComplexes.forget_supportedSectionsRestrict_comm`**, which is the
degree-zero case at the degree-zero functors, and it is stated in the same two readings that one
is: the chart's forgetful functor as `CategoryTheory.SheafOfModules.toSheaf` at the structure
sheaf of the underlying ringed space, and the restriction of abelian sheaves as
`Stacks.Cohomology.SupportedComplexes.abelianRestrictOpen` at the carrier.  No hypothesis beyond
the closedness of `T` and of `W ∩ T` is needed — and those only because the local cohomology
sheaves on a closed subset and their direct images have to exist — and there is no restriction on
`n`. -/
theorem forget_localCohomologySheafRestrict_comm :
    (_root_.SheafOfModules.toSheaf (structureSheafRing W.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T W n).hom.app F) ≫
        ((abelianSheaf W.toScheme).map
            ((supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.app
              ((Scheme.Modules.restrictFunctor W.ι).obj F)) ≫
          (supportCohomologySheafForgetIso hTW n).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj F)) =
      ((restrictAbelian W).map
            ((localCohomologyEndoForgetComparison T (supportPush hT)
              (derivedSupportedPushforwardUnit Y.toRingedSpace T hT)
              (derivedAbelianSupportedPushforward Y.toRingedSpace T hT)
              (derivedAbelianSupportedPushforwardUnit Y.toRingedSpace T hT) n).app F) ≫
          (restrictAbelian W).map
            ((abelianLocalCohomologySheafPushforwardIso T hT n).inv.app
              ((abelianSheaf Y).obj F))) ≫
        (abelianLocalCohomologySheafRestrictNatIso (X := Y.carrier) T W hT hTW n).hom.app
          ((abelianSheaf Y).obj F) :=
  square_general W hT hTW n F
    ((_root_.SheafOfModules.toSheaf (structureSheafRing W.toScheme.toRingedSpace)).map
      ((moduleExcisionEndo T W n).hom.app F)) _
    (Stacks.Cohomology.DegreewiseExcisionSquare.forget_localCohomologyRestrict_comm
      T W (supportPush hT) (derivedSupportedPushforwardUnit Y.toRingedSpace T hT)
      (derivedAbelianSupportedPushforward Y.toRingedSpace T hT)
      (derivedAbelianSupportedPushforwardUnit Y.toRingedSpace T hT)
      (supportPush hTW)
      (derivedSupportedPushforwardUnit W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW)
      (derivedAbelianSupportedPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW)
      (derivedAbelianSupportedPushforwardUnit W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW) n F)

end Stacks.Gysin

end

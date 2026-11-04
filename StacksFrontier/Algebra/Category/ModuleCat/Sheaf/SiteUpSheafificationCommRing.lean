module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifyRelationCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# `f^{-1}` of a sheaf of commutative rings, read at `RingCat`

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafification` builds
`Stacks.ModuleUp.upSheaf u J O = (u_p O)^#` for a sheaf `O` with values in **any** category
admitting sheafification, in particular at `CommRingCat` and at `RingCat`.  The statements of
Stacks 08FC in this development are taken over `Sheaf J CommRingCat`
(`Stacks.SheafOfModules.HasLocalSingleRelationFactorizations`), while the module-level colimit
formula `u_p` of Stacks 00VC and the criterion of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitRelations` live at `RingCat`,
where `PresheafOfModules` is defined.

This file crosses that boundary: it identifies the underlying sheaf of rings of `(u_p O)^#` with
`(u_p (O ⋙ forget₂))^#`, and exhibits the resulting map from `u_p (O ⋙ forget₂)` as locally
bijective, which is the hypothesis shape of
`Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify`.

The identification is a composite of two Mathlib facts, neither of which needs new mathematics:

* `forget₂ CommRingCat RingCat` **preserves the left Kan extension along `u.op`**, because the
  index categories `I^u_U = CostructuredArrow u.op U` are filtered when `u` is
  `CategoryTheory.Functor.RepresentablyFlat` (Stacks 00X3), and `forget₂ CommRingCat RingCat`
  preserves filtered colimits.  Mathlib turns that into
  `CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves`.
* `forget₂ CommRingCat RingCat` **preserves sheafification**, so
  `CategoryTheory.sheafComposeNatIso` identifies "sheafify then forget" with "forget then
  sheafify".

## Main definitions

* `Stacks.ModuleUp.lanForgetToRingIso`: `u_p O ⋙ forget₂ ≅ u_p (O ⋙ forget₂)` on presheaves.
* `Stacks.ModuleUp.sheafifyForgetToRingIso`: `(P ⋙ forget₂)^# ≅ (P^#) ⋙ forget₂` on sheaves.
* `Stacks.ModuleUp.upSheafForgetToRingIso`: **the bridge**
  `(u_p (O ⋙ forget₂))^# ≅ commRingSheafToRingSheaf ((u_p O)^#)`.
* `Stacks.ModuleUp.upSheafifyRingOfCommRing`: the unit
  `u_p (O ⋙ forget₂) ⟶ commRingSheafToRingSheaf ((u_p O)^#)` obtained from it.

## Main results

* `Stacks.ModuleUp.isLocallySurjective_upSheafifyRingOfCommRing` and
  `Stacks.ModuleUp.isLocallyInjective_upSheafifyRingOfCommRing`: that unit is locally bijective,
  which is what `Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify` takes as its `α`.
* `Stacks.ModuleUp.hasLocalSingleRelationFactorizations_upSheafify`: **the whole sheafification
  step of Stacks 05VD**, i.e. the presheaf-level criterion for `u_p F` read as part (2) of
  Stacks 08FC for the sheafification over `f^{-1} O`.

## Implementation notes

**`PreservesSheafification` has to be supplied by name.** Mathlib's instance for a functor
between concrete categories carries a long list of side conditions, and `infer_instance` for
`J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})` exhausts the 20000-heartbeat
`synthInstance` budget.  Naming the instance
(`CategoryTheory.GrothendieckTopology.instPreservesSheafification`) discharges it immediately;
this is the "failed to synthesize / exhausted heartbeats ⇒ apply the instance by name" case, as
opposed to a universe-defaulting failure, which by-name application does not fix.

**`RepresentablyFlat u` is used only through filteredness of `I^u_U`.** It is what makes
`PreservesColimitsOfShape (CostructuredArrow u.op X) (forget₂ CommRingCat RingCat)` available
from Mathlib's filtered-colimit instance for `forget₂`; no continuity of `u` is needed for this
file.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor

universe w

namespace Stacks.ModuleUp

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C) [RepresentablyFlat u]
  {K : GrothendieckTopology D} (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J RingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ F : Dᵒᵖ ⥤ CommRingCat.{w}, u.op.HasLeftKanExtension F]
  [∀ F : Dᵒᵖ ⥤ RingCat.{w}, u.op.HasLeftKanExtension F]

/-- **`u_p` commutes with forgetting commutativity.**

The colimit formula of Stacks 00VC is a filtered colimit when `u` is representably flat, and
`forget₂ CommRingCat RingCat` preserves filtered colimits. -/
noncomputable def lanForgetToRingIso (O : Dᵒᵖ ⥤ CommRingCat.{w}) :
    u.op.lan.obj O ⋙ forget₂ CommRingCat.{w} RingCat.{w}
      ≅ u.op.lan.obj (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  Functor.leftKanExtensionCompIsoOfPreserves _ _ _

/-- **Sheafification commutes with forgetting commutativity.** -/
noncomputable def sheafifyForgetToRingIso (P : Cᵒᵖ ⥤ CommRingCat.{w}) :
    (presheafToSheaf J RingCat.{w}).obj (P ⋙ forget₂ CommRingCat.{w} RingCat.{w})
      ≅ (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((presheafToSheaf J CommRingCat.{w}).obj P) :=
  letI : J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w}) :=
    CategoryTheory.GrothendieckTopology.instPreservesSheafification J _
  (CategoryTheory.sheafComposeNatIso J (forget₂ CommRingCat.{w} RingCat.{w})
    (sheafificationAdjunction J CommRingCat.{w}) (sheafificationAdjunction J RingCat.{w})).app P

/-- **The bridge.** The sheaf of rings `f^{-1} O` computed at `RingCat` from the underlying sheaf
of rings of `O` is the underlying sheaf of rings of `f^{-1} O` computed at `CommRingCat`.

This is what lets the `RingCat`-valued criterion of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitRelations` be read as part (2) of
Stacks 08FC, which this development states over `Sheaf J CommRingCat`. -/
noncomputable def upSheafForgetToRingIso (O : Sheaf K CommRingCat.{w}) :
    upSheaf u J (A := RingCat.{w}) (Stacks.commRingSheafToRingSheaf O)
      ≅ Stacks.commRingSheafToRingSheaf (upSheaf u J (A := CommRingCat.{w}) O) :=
  (presheafToSheaf J RingCat.{w}).mapIso (lanForgetToRingIso u O.obj).symm ≪≫
    sheafifyForgetToRingIso J (u.op.lan.obj O.obj)

/-- The sheafification unit of `u_p (O ⋙ forget₂)`, with its target written at the underlying
sheaf of rings of `(u_p O)^#`.

This is the morphism `α` that `Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify` takes;
`Stacks.ModuleUp.isLocallySurjective_upSheafifyRingOfCommRing` and its injective companion
supply its hypotheses. -/
noncomputable def upSheafifyRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    upRing u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})
      ⟶ (Stacks.commRingSheafToRingSheaf (upSheaf u J (A := CommRingCat.{w}) O)).obj :=
  upSheafify u J (A := RingCat.{w}) (Stacks.commRingSheafToRingSheaf O) ≫
    (upSheafForgetToRingIso u J O).hom.hom

variable [J.WEqualsLocallyBijective RingCat.{w}]

omit [J.WEqualsLocallyBijective RingCat.{w}] in
/-- The presheaf component of the bridge is an isomorphism.

Recorded separately because `Iso.hom.hom` for a sheaf iso is not the spelling
`(sheafToPresheaf J RingCat).mapIso _ |>.hom` at which instance search finds it. -/
theorem isIso_upSheafForgetToRingIso_hom_hom (O : Sheaf K CommRingCat.{w}) :
    IsIso (upSheafForgetToRingIso u J O).hom.hom :=
  inferInstanceAs
    (IsIso ((sheafToPresheaf J RingCat.{w}).mapIso (upSheafForgetToRingIso u J O)).hom)

/-- The sheafification unit `u_p O' ⟶ (u_p O')^#` is locally surjective, **at the `upSheaf`
spelling**.

Mathlib's instance is keyed on `CategoryTheory.toSheafify`, whose target is spelled
`sheafify J _`; `Stacks.ModuleUp.upSheafify` is a `def` whose target is `(upSheaf u J O).obj`.
The two are definitionally equal, and instance search does not unfold a `def`, so a composite
built from `upSheafify` finds nothing unless the instance is restated here. -/
instance isLocallySurjective_upSheafify (O : Sheaf K RingCat.{w}) :
    Presheaf.IsLocallySurjective J (upSheafify u J (A := RingCat.{w}) O) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (toSheafify J (u.op.lan.obj O.obj)))

/-- The injective half of `Stacks.ModuleUp.isLocallySurjective_upSheafify`. -/
instance isLocallyInjective_upSheafify (O : Sheaf K RingCat.{w}) :
    Presheaf.IsLocallyInjective J (upSheafify u J (A := RingCat.{w}) O) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (u.op.lan.obj O.obj)))

/-- The map `Stacks.ModuleUp.upSheafifyRingOfCommRing` is locally surjective. -/
instance isLocallySurjective_upSheafifyRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    Presheaf.IsLocallySurjective J (upSheafifyRingOfCommRing u J O) := by
  have := isIso_upSheafForgetToRingIso_hom_hom u J O
  exact Presheaf.isLocallySurjective_comp J
    (upSheafify u J (A := RingCat.{w}) (Stacks.commRingSheafToRingSheaf O))
    (upSheafForgetToRingIso u J O).hom.hom

/-- The map `Stacks.ModuleUp.upSheafifyRingOfCommRing` is locally injective. -/
instance isLocallyInjective_upSheafifyRingOfCommRing (O : Sheaf K CommRingCat.{w}) :
    Presheaf.IsLocallyInjective J (upSheafifyRingOfCommRing u J O) := by
  have := isIso_upSheafForgetToRingIso_hom_hom u J O
  exact Presheaf.isLocallyInjective_comp J
    (upSheafify u J (A := RingCat.{w}) (Stacks.commRingSheafToRingSheaf O))
    (upSheafForgetToRingIso u J O).hom.hom

/-- **The presheaf-level criterion for `u_p F` gives part (2) of Stacks 08FC for its
sheafification over `f^{-1} O`.**

This composes the three pieces of the sheafification step of Stacks 05VD:
`Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify` passes the criterion of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitRelations` to the sheafification;
`Stacks.ModuleUp.upSheafifyRingOfCommRing` is the locally bijective map of presheaves of rings
that step needs, obtained from the bridge `Stacks.ModuleUp.upSheafForgetToRingIso`; and
`Stacks.ModuleUp.hasLocalSingleRelationFactorizations_of_presheaf` reads the result at the
`Sheaf J CommRingCat` spelling in which this development states Stacks 08FC.

The input is exactly what `Stacks.ModuleUp.hasLocalRelationFactorizations_up` produces from a
flat `F` over `O`, so this is the paragraph of the source running from "Since `f^{-1}F`, resp.
`f^{-1}O` is the sheafification of `u_p F`" to the application of the other direction of
Lemma 08FC. -/
theorem hasLocalSingleRelationFactorizations_upSheafify (O : Sheaf K CommRingCat.{w})
    {M₀ : PresheafOfModules.{w} (upRing u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))}
    {A : Sheaf J AddCommGrpCat.{w}} (φ : M₀.presheaf ⟶ A.obj)
    [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]
    (h : HasLocalRelationFactorizations J
      (upRing u (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) M₀) :
    Stacks.SheafOfModules.HasLocalSingleRelationFactorizations
      (upSheaf u J (A := CommRingCat.{w}) O)
      (PresheafOfModules.sheafify (upSheafifyRingOfCommRing u J O) φ) :=
  hasLocalSingleRelationFactorizations_of_presheaf _
    (hasLocalRelationFactorizations_sheafify (upSheafifyRingOfCommRing u J O) φ h)

end Stacks.ModuleUp

end

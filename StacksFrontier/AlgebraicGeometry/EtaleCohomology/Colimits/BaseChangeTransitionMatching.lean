module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelEtaleSquareEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyMapIsTheEdgeMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtComparisonVersusEdge
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedSectionsVersusSiteCohomology
import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomologySupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomologySupplement

/-!
# The transition maps of the cohomology diagram of Stacks 03Q6, in the étale-cohomology spelling

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelEtaleSquareEtaleCohomology.lean`
proves the index-naturality of the comparison between the derived sections of a level of Stacks
0EYL and the étale cohomology of its stage
(`Stacks.EtaleCohomology.TransitionBaseChange.levelEtaleCohomologyIso_naturality`), as an equation
between composites of Leray edge morphisms. The transition maps of the cohomology diagram of
Stacks 09YP are *not* presented as edge morphisms in the colimit statement: they are pinned by the
predicate `Stacks.WeakSites.ColimitSiteCohomology.IsCohomologyMap`, which is the field `map_eq` of
`Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone`.

This file joins the two, so that the naturality is stated about the diagram's own maps.

## Main results

* `Stacks.EtaleCohomology.TransitionBaseChange.isCohomologyMap_comp_levelEtaleCohomologyIso` —
  **the transition map of the cohomology diagram is the transition map of
  `Stacks.EtaleCohomology.etaleCohomologyFunctor`.** Any map pinned by `IsCohomologyMap` for the
  transition functor of the system and the transition map of a system of *restrictions* of abelian
  sheaves on the small étale sites of the stages becomes, across the comparison
  `levelEtaleCohomologyIso` at both ends, the map `stageEtaleCohomologyMap`.
* `Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH_hom_comp_extBridge` — **the
  comparison of derived global sections with the cohomology of the site, followed by the
  `Ext`-to-derived-`Hom` bridge, is `NatTrans.rightDerived` of the corepresentation of global
  sections by the constant sheaf.** This is the compatibility every `Ext`-side comparison of this
  library must be read through to meet the Leray edge morphism. Two things make it possible: the cast of
  `Stacks.Cohomology.GlobalSections.functorH_eq_extFunctorObj`, and
  `Stacks.Cohomology.GlobalSections.rightDerivedΓIsoExtFunctorObj`, the body of
  `rightDerivedΓIsoFunctorH` named at the `Abelian.extFunctorObj` spelling of its target.
* `Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH_comp_extFunctorObjIsoComp_inv_app`
  — **the `Ext`-side cohomology comparison is the Leray edge morphism of global sections.** Read
  through `rightDerivedΓIsoFunctorH`, the inverse of
  `Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp` is the edge morphism of the pair
  `(g⁻¹, Γ(C, -))`. This is the first consumer outside its own file of
  `Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app`, which states the
  identification at `(g⁻¹, Hom(ℤ_C, -))` — a shape nothing in this library holds.
* `Stacks.Cohomology.GlobalSections.extFunctorObjIsoRightDerivedCoyoneda_inv_eq` and
  `Stacks.Cohomology.GlobalSections.functorHIsoRightDerivedCoyoneda_inv` — **the right-hand-end
  conversion**, the mirror of the left-hand one: the *inverse* of the `Ext`-to-derived-`Hom`
  bridge is the inverse derived corepresentation of global sections followed by
  `rightDerivedΓIsoFunctorH`. That is the direction an `Ext`-versus-edge identification needs,
  since there the bridge appears inverted and applied to the coefficient object of the bigger
  site. The second form absorbs the cast into `functorHIsoRightDerivedCoyoneda` so that neither
  side of the equation meets it, and is the form to use.
* `Stacks.Cohomology.GlobalSections.functorHIsoRightDerivedCoyoneda` — the bridge read on
  `CategoryTheory.Sheaf.functorH`, which is the spelling consumers hold and which cannot be
  written as a bare composition at all.
* `ModuleSheafCohomology.extFunctorObjIsoRightDerived_inv_comp_hom` — the two comparisons of `Ext`
  out of `X` with the right derived functors of two functors corepresented by `X` differ by
  `NatTrans.rightDerived` of the comparison of the two functors. This is
  `ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality` at the identity, solved for the
  shape its consumers need; see its docstring, which corrects an earlier claim of this file that
  the statement was unproved in the library.

## What is and is not proved

The comparison whose index-naturality is transported here is the Leray edge comparison
`levelEtaleCohomologyIso`. The object-by-object identification used by the registered Stacks 03Q6
colimit statements —
`Stacks.EtaleCohomology.QcqsBaseChange.qcqsDiagramObjIsoEtaleCohomology` and its primed form — is
built instead from `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` (resp.
`sheafCohomologyIsoOfIsEquivalence'`), and **the two comparisons are still not identified with one
another**. What that identification needs is four things, and this
file settles the first and refutes the third:

1. a cast at the `Sheaf.functorH`-versus-`extFunctorObj` crossing, and a form of
   `rightDerivedΓIsoFunctorH` whose body can be computed with. **Both supplied**, at the
   definition site: `Stacks.Cohomology.GlobalSections.functorH_eq_extFunctorObj`,
   `rightDerivedΓIsoExtFunctorObj` and `rightDerivedΓIsoFunctorH_hom_comp_eqToHom` in
   `StacksFrontier/CategoryTheory/Sites/GlobalSections/DerivedGlobalSectionsCohomology.lean`, with
   `rightDerivedΓIsoFunctorH` now defined as the second composed with the first and its statement
   unchanged; and `rightDerivedΓIsoFunctorH_hom_comp_extBridge` here is the compatibility they
   unblock;
2. the identification of `Stacks.Cohomology.DenseSubsiteGlobal.pullbackConstantSheafIso` with the
   comparison of sections it is the adjoint transpose of — that is,
   `pullbackConstantSheafIso J K G AddCommGrpCat M` equals
   `(Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso J K G heC heD hu).app M`, the
   two routes to `g_! ℤ_C ≅ ℤ_D` agreeing. **Proved here**, unconditionally and in general — not
   only where the subsite is dense — by
   `pullbackConstantSheafIso_eq_lowerShriekConstantSheafIso`, whose content beyond the structural
   steps is `constantSheafΓAdj_unit_comp_constantSheafRestrictionIso`;
3. the naturality of `ModuleSheafCohomology.extFunctorObjIsoRightDerived` in its corepresenting
   object. **This is not missing**: it is
   `ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality`, proved in both degree halves
   and already consumed inside its own file;
4. the composition of the two restrictions
   (`Stacks.EtaleCohomology.AffineLimitCohomology.restrictToLevel` and
   `Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale`) through
   `Stacks.Cohomology.RightDerivedEdge.edge_app_comp`. Not done, and routine.

With (1), (2) and (3) in hand the **general** statement is proved here:
`rightDerivedΓIsoFunctorH_comp_extFunctorObjIsoComp_inv_app` says the `Ext`-side comparison is
the Leray edge morphism of `(g⁻¹, Γ(C, -))`, with its left-hand end in the shape consumers hold.
The **right-hand-end conversion is proved too**, as
`extFunctorObjIsoRightDerivedCoyoneda_inv_eq` and `functorHIsoRightDerivedCoyoneda_inv`, so a
consumer can rewrite that end as well.

What is **not** here is the two conversions assembled into one equation about
`extFunctorObjIsoComp` with both ends renamed, for the following reason.
Such an equation has to land in `CategoryTheory.Sheaf.functorH K p` on one side and in
`Abelian.extFunctorObj ℤ_K p` on the other, so it needs the cast of `functorH_eq_extFunctorObj`
at `K` applied to an object — and `(eqToHom (functorH_eq_extFunctorObj K p)).app N` exhausts the
heartbeat budget, in either placement, where the same thing at `J` inside
`rightDerivedΓIsoFunctorH_comp_extFunctorObjIsoComp_inv_app` costs nothing. The way through is
not a new input: state the assembled equation about
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence'` or
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIso`, whose *type* already
lands in `Sheaf.functorH K p` with no cast visible, so the crossing stays inside a definition that
has already elaborated. Doing that brings in the remaining factor of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`, namely
`ModuleSheafCohomology.extPrecomp` of the comparison of coefficient objects, which moves across
`ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality`; that is where
`pullbackConstantSheafIso_eq_lowerShriekConstantSheafIso` is consumed. Together with (4) those are
what the étale assembly waits on.

The terminality hypotheses are not removable. `(levelEtale E i).obj V` is an object of the *affine*
étale site of the stage, and it is terminal in the small étale site only when the stage is affine;
`Stacks.EtaleCohomology.TransitionBaseChange.isTerminal_levelEtale_obj` discharges them in that
case and they are false otherwise.

The system of abelian sheaves is required to be a system of *restrictions* of sheaves on the small
étale sites of the stages, with its transition map coming from a `ψ` in the direct-image direction.
That is the hypothesis the Stacks 03Q6 strings already record as not covered: `F` there is an
arbitrary system of abelian sheaves on the levels.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Cohomology.RightDerivedEdge

/-! ### The two degree-split comparisons of `Ext` with right derived functors -/

namespace ModuleSheafCohomology

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]

/-- **The two comparisons of `Ext` out of `X` with the right derived functors of two functors
corepresented by `X` differ by `NatTrans.rightDerived` of the comparison of the two functors.**

This is `ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality` at `x = 𝟙 X`, solved for
the shape a consumer holding one comparison and wanting the other needs: that lemma produces
`extPrecomp x n ≫ … = … ≫ NatTrans.rightDerived ρ n`, and at the identity `extPrecomp` is the
identity. The proof below is the direct degree split rather than that specialisation, but the
content is the same and no new homological algebra enters: in positive degree the two
`ModuleSheafCohomology.rightDerivedCoyonedaSuccIso` factors are inverse to one another, and in
degree zero the two `ModuleSheafCohomology.extZeroIsoCoyoneda` factors are, after which what
remains is `ModuleSheafCohomology.toRightDerivedZero_naturality_functor`.

The statement is not the compatibility that three module docs in this library record as
unproved, as `extFunctorObjIsoRightDerived_naturality` itself shows: the naturality of the comparison in its
corepresenting object is *already proved*, with both degree halves, and it is consumed by
`ModuleSheafCohomology.selfDerivedDeltaFunctorRestriction` and
`ModuleSheafCohomology.derivedDeltaFunctorRestriction`. What those module docs disclaim is
narrower — a compatibility between the degree-zero and positive-degree *branches* of
`extFunctorObjIsoRightDerived` and of
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH` — and the composite here needs none,
because each branch cancels against its own counterpart. -/
theorem extFunctorObjIsoRightDerived_inv_comp_hom (X : A) (G G' : A ⥤ Ab.{v}) [G.Additive]
    [PreservesFiniteLimits G] [G'.Additive] [PreservesFiniteLimits G']
    (α : G ≅ preadditiveCoyoneda.obj (op X)) (α' : G' ≅ preadditiveCoyoneda.obj (op X)) (n : ℕ) :
    (extFunctorObjIsoRightDerived G X α n).inv ≫
        (extFunctorObjIsoRightDerived G' X α' n).hom =
      NatTrans.rightDerived (α.hom ≫ α'.inv) n := by
  cases n with
  | zero =>
    have h : G.rightDerivedZeroIsoSelf.hom ≫ (α.hom ≫ α'.inv) ≫ G'.toRightDerivedZero =
        NatTrans.rightDerived (α.hom ≫ α'.inv) 0 := by
      rw [toRightDerivedZero_naturality_functor (α.hom ≫ α'.inv)]
      simp
    rw [extFunctorObjIsoRightDerived_zero, extFunctorObjIsoRightDerived_zero]
    simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      Functor.rightDerivedZeroIsoSelf_inv, Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using h
  | succ m =>
    have hinv : (rightDerivedIso α.symm (m + 1)).inv =
        NatTrans.rightDerived α.hom (m + 1) := rfl
    have hhom : (rightDerivedIso α'.symm (m + 1)).hom =
        NatTrans.rightDerived α'.inv (m + 1) := rfl
    rw [extFunctorObjIsoRightDerived_succ, extFunctorObjIsoRightDerived_succ]
    simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [hinv, hhom, ← NatTrans.rightDerived_comp]

end ModuleSheafCohomology

/-! ### The cohomology of a site as `Ext` out of the constant sheaf, as a named identification -/

namespace Stacks.Cohomology.GlobalSections

open Stacks.Cohomology.ExtComparison

universe w v v' u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u w}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})]
  [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]

attribute [local instance] additive_Γ

/-- **The cohomology of a site, as the right derived functors of `Hom` out of the constant sheaf
on `ℤ`.** This is the `Ext`-to-derived-`Hom` bridge
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda` read on
`CategoryTheory.Sheaf.functorH`, which is the spelling every consumer of this library's `Ext`-side
cohomology comparisons holds. It cannot be written as a bare composition — see
`functorH_eq_extFunctorObj` for the crossing that defeats the unifier — so the identification is
inserted explicitly. -/
def functorHIsoRightDerivedCoyoneda (p : ℕ) :
    Sheaf.functorH J p ≅
      (preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{max u w}).obj
        (AddCommGrpCat.of (ULift.{max u w} ℤ))))).rightDerived p :=
  eqToIso (functorH_eq_extFunctorObj J p) ≪≫
    extFunctorObjIsoRightDerivedCoyoneda ((constantSheaf J AddCommGrpCat.{max u w}).obj
      (AddCommGrpCat.of (ULift.{max u w} ℤ))) p

/-- `rightDerivedΓIsoExtFunctorObj` is the comparison of `Ext` out of the constant sheaf with the
right derived functors of global sections, which is what corepresentation by that sheaf makes it.
Both sides target `Abelian.extFunctorObj`, so nothing has to cross between the two spellings of
the cohomology of the site; that is exactly what
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoExtFunctorObj` exists for. -/
theorem rightDerivedΓIsoExtFunctorObj_hom (p : ℕ) :
    (rightDerivedΓIsoExtFunctorObj J p).hom =
      (ModuleSheafCohomology.extFunctorObjIsoRightDerived (Sheaf.Γ J AddCommGrpCat.{max u w})
        ((constantSheaf J AddCommGrpCat.{max u w}).obj
          (AddCommGrpCat.of (ULift.{max u w} ℤ))) (globalSectionsCorepresentation J) p).inv := by
  cases p with
  | zero =>
    rw [rightDerivedΓIsoExtFunctorObj_zero,
      ModuleSheafCohomology.extFunctorObjIsoRightDerived_zero]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  | succ m =>
    rw [rightDerivedΓIsoExtFunctorObj_succ,
      ModuleSheafCohomology.extFunctorObjIsoRightDerived_succ]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv]
    rfl

/-- **The comparison of derived global sections with the cohomology of the site, followed by the
`Ext`-to-derived-`Hom` bridge, is `NatTrans.rightDerived` of the corepresentation of global
sections by the constant sheaf.**

This is the compatibility that every `Ext`-side cohomology comparison of this library has to be
read through in order to meet the Leray edge morphism:
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app` is stated with
`extFunctorObjIsoRightDerivedCoyoneda` as its conjugator, while the consumers hold
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`, and this identifies the composite of
the two.

Both comparisons are defined by splitting on the degree and this library claims no compatibility
between the branches of either. None is needed: the two splittings cancel, which is
`ModuleSheafCohomology.extFunctorObjIsoRightDerived_inv_comp_hom`. Two things make the statement
writable and the proof possible: the cast
`eqToHom (functorH_eq_extFunctorObj J p)`, without which the composite cannot even be elaborated,
and `rightDerivedΓIsoExtFunctorObj`, the body of `rightDerivedΓIsoFunctorH` named at the
`Abelian.extFunctorObj` spelling of its target, without which a proof that computes with that
body has to cross the two spellings in a morphism type and exceeds the heartbeat budget.

The form over a terminal object follows by composing with
`NatTrans.rightDerived (CategoryTheory.Sheaf.ΓNatIsoSheafSections J _ hW).inv p`, since
`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH` is that followed by this
comparison. It is not stated here: doing so needs `HasTerminal C` in the statement, and then the
ambient instance and the `IsTerminal.hasTerminal` one used inside
`rightDerivedSectionsIsoFunctorH` reach `Sheaf.Γ` by different routes, whose reconciliation is a
`rfl` that exceeds the budget. A consumer that already has a terminal object in scope has the
instances agree and does not meet that. -/
theorem rightDerivedΓIsoFunctorH_hom_comp_extBridge (p : ℕ) :
    (rightDerivedΓIsoFunctorH J p).hom ≫ eqToHom (functorH_eq_extFunctorObj J p) ≫
        (extFunctorObjIsoRightDerivedCoyoneda ((constantSheaf J AddCommGrpCat.{max u w}).obj
          (AddCommGrpCat.of (ULift.{max u w} ℤ))) p).hom =
      NatTrans.rightDerived (globalSectionsCorepresentation J).hom p := by
  have hm := ModuleSheafCohomology.extFunctorObjIsoRightDerived_inv_comp_hom
    ((constantSheaf J AddCommGrpCat.{max u w}).obj (AddCommGrpCat.of (ULift.{max u w} ℤ)))
    (Sheaf.Γ J AddCommGrpCat.{max u w})
    (preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{max u w}).obj
      (AddCommGrpCat.of (ULift.{max u w} ℤ))))) (globalSectionsCorepresentation J) (Iso.refl _) p
  rw [← Category.assoc, rightDerivedΓIsoFunctorH_hom_comp_eqToHom,
    rightDerivedΓIsoExtFunctorObj_hom,
    show (extFunctorObjIsoRightDerivedCoyoneda ((constantSheaf J AddCommGrpCat.{max u w}).obj
        (AddCommGrpCat.of (ULift.{max u w} ℤ))) p).hom =
      (ModuleSheafCohomology.extFunctorObjIsoRightDerived _
        ((constantSheaf J AddCommGrpCat.{max u w}).obj
          (AddCommGrpCat.of (ULift.{max u w} ℤ))) (Iso.refl _) p).hom from rfl, hm]
  simp


/-- **The inverse of the `Ext`-to-derived-`Hom` bridge, in the shape consumers hold.** The
inverse of `extFunctorObjIsoRightDerivedCoyoneda` at the constant sheaf on `ℤ` is the inverse
derived corepresentation of global sections followed by `rightDerivedΓIsoFunctorH` and the cast.

This is `rightDerivedΓIsoFunctorH_hom_comp_extBridge` solved for the bridge, which is the
direction needed to rewrite the *right-hand* end of an `Ext`-versus-edge identification: there the
bridge appears inverted, applied to the coefficient object of the bigger site, and what a consumer
wants in its place is the cohomology of that site. -/
theorem extFunctorObjIsoRightDerivedCoyoneda_inv_eq (p : ℕ) :
    (extFunctorObjIsoRightDerivedCoyoneda ((constantSheaf J AddCommGrpCat.{max u w}).obj
        (AddCommGrpCat.of (ULift.{max u w} ℤ))) p).inv =
      NatTrans.rightDerived (globalSectionsCorepresentation J).inv p ≫
        (rightDerivedΓIsoFunctorH J p).hom ≫ eqToHom (functorH_eq_extFunctorObj J p) := by
  have h := rightDerivedΓIsoFunctorH_hom_comp_extBridge J p
  have h2 : (rightDerivedΓIsoFunctorH J p).hom ≫ eqToHom (functorH_eq_extFunctorObj J p) =
      NatTrans.rightDerived (globalSectionsCorepresentation J).hom p ≫
        (extFunctorObjIsoRightDerivedCoyoneda ((constantSheaf J AddCommGrpCat.{max u w}).obj
          (AddCommGrpCat.of (ULift.{max u w} ℤ))) p).inv := by
    rw [← h, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h2, ← Category.assoc, ← NatTrans.rightDerived_comp, Iso.inv_hom_id,
    NatTrans.rightDerived_id, Category.id_comp]

/-- **The right-hand-end conversion, cast-free.** The inverse of
`functorHIsoRightDerivedCoyoneda` — the `Ext`-to-derived-`Hom` bridge read on
`CategoryTheory.Sheaf.functorH` — is the inverse derived corepresentation of global sections
followed by `rightDerivedΓIsoFunctorH`.

This is the form a consumer uses. `extFunctorObjIsoRightDerivedCoyoneda_inv_eq` says the same
thing with the cast of `functorH_eq_extFunctorObj` written out, and both are needed: the
`Ext`-versus-edge identifications produce the bridge in the `Abelian.extFunctorObj` spelling, so
the cast has to appear somewhere, and here it is absorbed into
`functorHIsoRightDerivedCoyoneda` so that neither side of this equation meets it. That matters
because the crossing is not free in every position — see the module documentation. -/
theorem functorHIsoRightDerivedCoyoneda_inv (p : ℕ) :
    (functorHIsoRightDerivedCoyoneda J p).inv =
      NatTrans.rightDerived (globalSectionsCorepresentation J).inv p ≫
        (rightDerivedΓIsoFunctorH J p).hom := by
  show (eqToIso (functorH_eq_extFunctorObj J p) ≪≫
    extFunctorObjIsoRightDerivedCoyoneda ((constantSheaf J AddCommGrpCat.{max u w}).obj
      (AddCommGrpCat.of (ULift.{max u w} ℤ))) p).inv = _
  rw [Iso.trans_inv, extFunctorObjIsoRightDerivedCoyoneda_inv_eq, eqToIso.inv]
  simp

/-! ### The `Ext`-side comparison is the Leray edge morphism of global sections -/

section Edge

open Stacks.Cohomology.RightDerivedEdge

variable {D : Type u} [Category.{v'} D] (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsContinuous J K]
  [HasSheafify K AddCommGrpCat.{max u w}]
  [HasExt.{max u w} (Sheaf K AddCommGrpCat.{max u w})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u w})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{max u w})]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).Additive]
  [PreservesFiniteLimits (G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K)]
  [PreservesFiniteColimits (G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K)]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).PreservesInjectiveObjects]

/-- **The `Ext`-side cohomology comparison is the Leray edge morphism of global sections.** For
restriction `g⁻¹` along a continuous functor of sites, exact and preserving injective objects, and
for any identification `α` of `Hom(ℤ_C, g⁻¹ -)` with `Hom(X, -)`, the component of the inverse of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp` is — read through the comparison
`rightDerivedΓIsoFunctorH` of derived global sections with the cohomology of the site — the edge
morphism of the pair `(g⁻¹, Γ(C, -))`.

This is what every `Ext`-side comparison in this library had to be read through in order to meet a
resolution-level construction, and it is the first consumer of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app`: that lemma states the
identification with the edge morphism of `(g⁻¹, Hom(ℤ_C, -))`, which is not the shape anything
holds, and the passage to `Γ(C, -)` is
`Stacks.Cohomology.RightDerivedEdge.edge_app_comp_rightDerived_whiskerLeft` at the
corepresentation `globalSectionsCorepresentation` together with
`rightDerivedΓIsoFunctorH_hom_comp_extBridge`.

The coefficient object `X` and the identification `α` are arbitrary: nothing here needs them to
come from an adjunction, so this applies to
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIso` and to
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence'` alike. What is *not*
done is renaming the right-hand end: `extFunctorObjIsoRightDerivedCoyoneda X p` is left as the
bridge produces it, and turning it into `rightDerivedΓIsoFunctorH K p` needs `X` to be the
constant sheaf of `(D, K)` — which is `pullbackConstantSheafIso_eq_lowerShriekConstantSheafIso`
together with this file's compatibility at `K` — and is the step the étale assembly still
waits on. -/
theorem rightDerivedΓIsoFunctorH_comp_extFunctorObjIsoComp_inv_app
    {X : Sheaf K AddCommGrpCat.{max u w}}
    (α : G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K ⋙
        preadditiveCoyoneda.obj (op ((constantSheaf J AddCommGrpCat.{max u w}).obj
          (AddCommGrpCat.of (ULift.{max u w} ℤ)))) ≅
      preadditiveCoyoneda.obj (op X))
    (p : ℕ) (N : Sheaf K AddCommGrpCat.{max u w}) :
    (rightDerivedΓIsoFunctorH J p).hom.app
          ((G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).obj N) ≫
        (eqToHom (functorH_eq_extFunctorObj J p)).app
          ((G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).obj N) ≫
        (extFunctorObjIsoComp
          (G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K) α p).inv.app N =
      (edge (G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K)
            (Sheaf.Γ J AddCommGrpCat.{max u w}) p).app N ≫
        (NatTrans.rightDerived (Functor.whiskerLeft
            (G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K)
            (globalSectionsCorepresentation J).hom) p).app N ≫
          (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso α.symm p).inv.app N ≫
            (extFunctorObjIsoRightDerivedCoyoneda X p).inv.app N := by
  have hcomp := NatTrans.congr_app (rightDerivedΓIsoFunctorH_hom_comp_extBridge J p)
    ((G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).obj N)
  have hshape := edge_app_comp_rightDerived_whiskerLeft
    (G.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K)
    (globalSectionsCorepresentation J).hom p N
  rw [extFunctorObjIsoComp_inv_app_eq_edge_app]
  simp only [NatTrans.comp_app] at hcomp
  simp only [← Category.assoc] at hcomp ⊢
  rw [hcomp, ← hshape]

end Edge

end Stacks.Cohomology.GlobalSections

/-! ### The comparisons of global sections and of constant sheaves at independent morphism
universes -/

namespace Stacks.Cohomology.BiggerSiteGlobal

universe w v v' u

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)

section Sections

variable (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [u.IsContinuous J K] [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]

/-- **Restriction along a continuous functor does not change global sections**, for sites whose
morphisms live in independent universes. For terminal objects `e_C` of `C` and `e_D` of `D` with
`u(e_C) = e_D`, we have `Γ(C, g⁻¹ F) ≅ Γ(D, F)`, naturally in `F`. This generalizes
`Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso`, which asks the two sites to have
their morphisms in the same universe; the construction is the same. -/
def gammaCompRestrictionIso' {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD) :
    u.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A ≅ Sheaf.Γ K A :=
  have : HasTerminal C := heC.hasTerminal
  have : HasTerminal D := heD.hasTerminal
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections J A heC) ≪≫
    eqToIso ((show u.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op eC) =
        (sheafSections K A).obj (op (u.obj eC)) from rfl).trans (by rw [hu])) ≪≫
    (Sheaf.ΓNatIsoSheafSections K A heD).symm

end Sections

section Constant

variable [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- **Lower shriek takes the constant sheaf to the constant sheaf**, for sites whose morphisms
live in independent universes. For terminal objects `e_C`, `e_D` with `u(e_C) = e_D` and any
coefficient group `M`, `g_! M_C ≅ M_D`. This generalizes
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso`, which asks the two sites to have
their morphisms in the same universe; the construction, by uniqueness of left adjoints, is the
same. -/
def lowerShriekConstantSheafIso' {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD) :
    constantSheaf J AddCommGrpCat.{w} ⋙ lowerShriekAbelian J K u ≅
      constantSheaf K AddCommGrpCat.{w} :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((constantSheafΓAdj J AddCommGrpCat.{w}).comp (lowerShriekAdjunction' J K u))
      (gammaCompRestrictionIso' J K u AddCommGrpCat.{w} heC heD hu))
    (constantSheafΓAdj K AddCommGrpCat.{w})

end Constant

end Stacks.Cohomology.BiggerSiteGlobal

/-! ### The two routes to `g_! ℤ_C ≅ ℤ_D` -/

namespace Stacks.Cohomology.DenseSubsiteGlobal

open Stacks.Cohomology.BiggerSiteGlobal

universe w v v' u

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{w}] [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]

/-- At a terminal object, the unit of the constant-sheaf adjunction followed by the comparison of
global sections is the unit of `constantSheafAdj`, which is the sheafification map of the constant
presheaf. -/
private theorem constantSheafΓAdj_unit_comp_ΓNatIsoSheafSections [HasTerminal C] {e : C}
    (he : IsTerminal e) (M : AddCommGrpCat.{w}) :
    (constantSheafΓAdj J AddCommGrpCat.{w}).unit.app M ≫
        (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{w} he).hom.app
          ((constantSheaf J AddCommGrpCat.{w}).obj M) =
      (constantSheafAdj J AddCommGrpCat.{w} he).unit.app M ∧
    (constantSheafAdj J AddCommGrpCat.{w} he).unit.app M =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op e) := by
  refine ⟨Adjunction.unit_rightAdjointUniq_hom_app (constantSheafΓAdj J AddCommGrpCat.{w})
    (constantSheafAdj J AddCommGrpCat.{w} he) M, ?_⟩
  change ((constantPresheafAdj AddCommGrpCat.{w} he).comp
    (sheafificationAdjunction J AddCommGrpCat.{w})).unit.app M = _
  simp [Adjunction.comp_unit_app]

omit [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] in
/-- **The comparison of constant sheaves along a continuous and cocontinuous functor is the
adjoint transpose of the comparison of global sections.** The unit of the constant-sheaf
adjunction on `(C, J)`, followed by `constantSheafRestrictionIso` and by
`Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso'`, is the unit on `(D, K)`.

This is the hypothesis `hunit` of `pullbackConstantSheafIso_eq_lowerShriekConstantSheafIso`, so
with it that statement becomes unconditional.

Both units are read on the terminal objects, where the constant-sheaf adjunction is
`CategoryTheory.constantSheafAdj` and its unit is the sheafification map of the constant presheaf
(`CategoryTheory.constantPresheafAdj_unit_app` being the identity), and the comparison of global
sections is the uniqueness-of-right-adjoints isomorphism
`CategoryTheory.Sheaf.ΓNatIsoSheafSections`, so both normalisations are
`CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`. What remains after that is exactly
`CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility`, the compatibility of
sheafification with restriction read on the constant presheaf, which is the one fact
`constantSheafRestrictionIso` is built from.

## Implementation note

`constantSheafRestrictionIso` and `CategoryTheory.constantSheafAdj` have to be exposed by `change`
rather than by `simp only`, `unfold` or `rw` with their own names: on this definition none of
those three makes any progress at all, so the four-fold `CategoryTheory.Iso.trans` whose three
identity factors have to cancel never reaches `simp`. Writing the body out and letting `change`
match it up to definitional equality is what makes the cancellation happen. -/
theorem constantSheafΓAdj_unit_comp_constantSheafRestrictionIso
    {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD) (hu : G.obj eC = eD)
    (M : AddCommGrpCat.{w}) :
    (constantSheafΓAdj J AddCommGrpCat.{w}).unit.app M ≫
        (Sheaf.Γ J AddCommGrpCat.{w}).map
            ((constantSheafRestrictionIso J K G AddCommGrpCat.{w}).inv.app M) ≫
          (gammaCompRestrictionIso' J K G AddCommGrpCat.{w} heC heD hu).hom.app
            ((constantSheaf K AddCommGrpCat.{w}).obj M) =
      (constantSheafΓAdj K AddCommGrpCat.{w}).unit.app M := by
  subst hu
  have : HasTerminal C := heC.hasTerminal
  have : HasTerminal D := heD.hasTerminal
  obtain ⟨hJ, hJ'⟩ := constantSheafΓAdj_unit_comp_ΓNatIsoSheafSections J heC M
  obtain ⟨hK, hK'⟩ := constantSheafΓAdj_unit_comp_ΓNatIsoSheafSections K heD M
  have hkey := NatTrans.congr_app
    (G.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{w} J K
      ((Functor.const Dᵒᵖ).obj M)) (op eC)
  have hcsri : (constantSheafRestrictionIso J K G AddCommGrpCat.{w}).inv.app M =
      (G.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{w} J K).hom.app
        ((Functor.const Dᵒᵖ).obj M) := by
    show ((Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (Functor.const Dᵒᵖ)
          (G.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{w} J K).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Iso.refl _) (presheafToSheaf J AddCommGrpCat.{w})).inv.app M) = _
    simp
  have hfinal : (constantSheafAdj J AddCommGrpCat.{w} heC).unit.app M ≫
      ((sheafSections J AddCommGrpCat.{w}).obj (op eC)).map
        ((constantSheafRestrictionIso J K G AddCommGrpCat.{w}).inv.app M) =
      (constantSheafAdj K AddCommGrpCat.{w} heD).unit.app M := by
    rw [NatTrans.comp_app] at hkey
    rw [hcsri, hJ', hK']
    exact hkey
  have h2 : (gammaCompRestrictionIso' J K G AddCommGrpCat.{w} heC heD rfl).hom.app
        ((constantSheaf K AddCommGrpCat.{w}).obj M) ≫
      (Sheaf.ΓNatIsoSheafSections K AddCommGrpCat.{w} heD).hom.app
        ((constantSheaf K AddCommGrpCat.{w}).obj M) =
      (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{w} heC).hom.app
        ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
          ((constantSheaf K AddCommGrpCat.{w}).obj M)) := by
    simp only [Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj,
      gammaCompRestrictionIso', Iso.trans_hom, Functor.isoWhiskerLeft_hom, eqToIso.hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    exact Category.comp_id _
  refine (cancel_mono ((Sheaf.ΓNatIsoSheafSections K AddCommGrpCat.{w} heD).hom.app
    ((constantSheaf K AddCommGrpCat.{w}).obj M))).mp ?_
  rw [hK, ← hfinal, ← hJ]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{w} heC).hom.naturality]
  exact congrArg (fun z => (constantSheafΓAdj J AddCommGrpCat.{w}).unit.app M ≫
    (Sheaf.Γ J AddCommGrpCat.{w}).map
      ((constantSheafRestrictionIso J K G AddCommGrpCat.{w}).inv.app M) ≫ z) h2

/-- **The two routes to `g_! ℤ_C ≅ ℤ_D` agree, given that the comparison of constant sheaves is
the adjoint transpose of the comparison of global sections.**

`Stacks.Cohomology.DenseSubsiteGlobal.pullbackConstantSheafIso'` is built from
`constantSheafRestrictionIso` — hence from
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility` — and the counit of
`g_! ⊣ g⁻¹`; it needs no terminal object.
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso'` is built by uniqueness of left
adjoints from `Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso'`, which *is* the
comparison of global sections, and needs terminal objects on both sites. This identifies them.

`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence'` — and so the
`Ext`-side object-by-object identification registered for Stacks 03Q6 — uses the first; every
`Ext`-versus-resolution bridge in this library is stated for the second, because
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIso` is. So this equality is the degree-zero
content of matching the two Stacks 03Q6 comparisons, and it is the only missing input to that
matching that is not either supplied or routine.

**This is unconditional.** The content beyond the structural steps is
`constantSheafΓAdj_unit_comp_constantSheafRestrictionIso` above: the unit of the constant-sheaf
adjunction on `(C, J)`, followed by `constantSheafRestrictionIso` and the comparison of global
sections, is the unit on `(D, K)`. Everything else the equality needs is discharged here — the
counit triangle for `g_! ⊣ g⁻¹`, `CategoryTheory.Adjunction.comp`,
`CategoryTheory.Adjunction.ofNatIsoRight` and the uniqueness of left adjoints. -/
theorem pullbackConstantSheafIso_eq_lowerShriekConstantSheafIso
    {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD) (hu : G.obj eC = eD)
    (M : AddCommGrpCat.{w}) :
    pullbackConstantSheafIso' J K G AddCommGrpCat.{w} M =
      (lowerShriekConstantSheafIso'.{w, v, v', u} J K G heC heD hu).app M := by
  have hunit := constantSheafΓAdj_unit_comp_constantSheafRestrictionIso J K G heC heD hu M
  have htranspose : (G.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
        ((constantSheaf J AddCommGrpCat.{w}).obj M)
        ((constantSheaf K AddCommGrpCat.{w}).obj M)
        (pullbackConstantSheafIso' J K G AddCommGrpCat.{w} M).hom =
      (constantSheafRestrictionIso J K G AddCommGrpCat.{w}).inv.app M := by
    rw [show (pullbackConstantSheafIso' J K G AddCommGrpCat.{w} M).hom =
        ((G.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
          ((constantSheaf J AddCommGrpCat.{w}).obj M)
          ((constantSheaf K AddCommGrpCat.{w}).obj M)).symm
          ((constantSheafRestrictionIso J K G AddCommGrpCat.{w}).inv.app M) from by
      rw [Adjunction.homEquiv_counit]; rfl]
    exact Equiv.apply_symm_apply _ _
  refine Iso.ext ((Adjunction.homEquiv
    (Adjunction.ofNatIsoRight
      ((constantSheafΓAdj J AddCommGrpCat.{w}).comp
        (lowerShriekAdjunction'.{w, v, v', u} J K G))
      (gammaCompRestrictionIso' J K G AddCommGrpCat.{w} heC heD hu)) M
    ((constantSheaf K AddCommGrpCat.{w}).obj M)).injective ?_)
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (Adjunction.ofNatIsoRight
      ((constantSheafΓAdj J AddCommGrpCat.{w}).comp
        (lowerShriekAdjunction'.{w, v, v', u} J K G))
      (gammaCompRestrictionIso' J K G AddCommGrpCat.{w} heC heD hu))
    (constantSheafΓAdj K AddCommGrpCat.{w}) M).symm
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv, Equiv.trans_apply,
    htranspose, Adjunction.homEquiv_unit, Category.assoc]
  exact hunit

end Stacks.Cohomology.DenseSubsiteGlobal

/-! ### The transition maps of the diagram, in the étale-cohomology spelling -/

namespace Stacks.EtaleCohomology.TransitionBaseChange

open AlgebraicGeometry
open Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open Stacks.WeakSites.ColimitSiteCohomology

attribute [local instance] hasSheafify_smallEtale enoughInjectives_smallEtale hasExt_smallEtale

universe v u

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX)
  [hcont : ∀ i : E.system.I,
    (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]

attribute [local instance] isContinuous_transition isContinuous_stageBaseChange
  isContinuous_transition_comp_levelEtale isContinuous_levelEtale_comp_stageBaseChange
  isContinuous_transition_comp isContinuous_stageBaseChange_comp

variable {i j : E.system.I} (a : i ⟶ j)
  [HasSheafify (E.system.J i) Ab.{max u v + 1}] [HasSheafify (E.system.J j) Ab.{max u v + 1}]
  [HasInjectiveResolutions (Sheaf (E.system.J i) Ab.{max u v + 1})]
  [HasInjectiveResolutions (Sheaf (E.system.J j) Ab.{max u v + 1})]
  [(levelPush E Ab.{max u v + 1} a).PreservesInjectiveObjects]
  [(levelEtaleRestrict E Ab.{max u v + 1} i).PreservesInjectiveObjects]
  [(levelEtaleRestrict E Ab.{max u v + 1} j).PreservesInjectiveObjects]
  [(levelEtaleRestrict E Ab.{max u v + 1} i).IsEquivalence]
  [(levelEtaleRestrict E Ab.{max u v + 1} j).IsEquivalence]

attribute [local instance] preservesInjectiveObjects_stagePush

/-- **The transition maps of the cohomology diagram of Stacks 03Q6 are the transition maps of
`Stacks.EtaleCohomology.etaleCohomologyFunctor`.**

Let `a : i ⟶ j` be an arrow of the index category of the system of Stacks 0EYL, let `𝒢ᵢ` and `𝒢ⱼ`
be abelian sheaves on the small étale sites of the two stages, let `ψ : 𝒢ⱼ ⟶ (Xᵢ ⟶ Xⱼ)_* 𝒢ᵢ` be a
transition map between them, and let `m` be *any* map on the derived sections of the levels pinned
by `Stacks.WeakSites.ColimitSiteCohomology.IsCohomologyMap` for the transition functor of the
system and the induced transition map of the restricted sheaves. Then, across the comparison
`levelEtaleCohomologyIso` at both ends, `m` is `stageEtaleCohomologyMap`:

`m` is the transition map of the cohomology diagram of Stacks 09YP — that is exactly what the
field `map_eq` of `Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone` asserts of the
diagram's maps — so this is the index-naturality clause of Stacks 03Q6 stated about the diagram's
own maps rather than about edge morphisms.

The proof is `Stacks.WeakSites.ColimitSiteCohomology.IsCohomologyMap.eq_map_comp_edge_app`, which
rewrites `m` as a Leray edge morphism, followed by `levelEtaleCohomologyIso_naturality`.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
theorem isCohomologyMap_comp_levelEtaleCohomologyIso
    (𝒢i : Sheaf (stageTopology E i) Ab.{max u v + 1})
    (𝒢j : Sheaf (stageTopology E j) Ab.{max u v + 1})
    (ψ : 𝒢j ⟶ (stagePush E Ab.{max u v + 1} a).obj 𝒢i)
    (V : E.system.C j) (hV : IsTerminal ((levelEtale E j).obj V))
    (hV' : IsTerminal ((levelEtale E i).obj ((E.system.u a).obj V))) (p : ℕ)
    {m : ((((sheafSections (E.system.J j) Ab.{max u v + 1}).obj (op V)).rightDerived p).obj
        ((levelEtaleRestrict E Ab.{max u v + 1} j).obj 𝒢j)) ⟶
      ((((sheafSections (E.system.J i) Ab.{max u v + 1}).obj
          (op ((E.system.u a).obj V))).rightDerived p).obj
        ((levelEtaleRestrict E Ab.{max u v + 1} i).obj 𝒢i))}
    (hm : IsCohomologyMap (E.system.J j) (E.system.J i) (E.system.u a)
      ((levelEtaleRestrict E Ab.{max u v + 1} j).map ψ ≫
        (levelEtaleSquare E Ab.{max u v + 1} a).inv.app 𝒢i).hom V p m) :
    m ≫ (levelEtaleCohomologyIso E i ((E.system.u a).obj V) hV' p 𝒢i).hom =
      (levelEtaleCohomologyIso E j V hV p 𝒢j).hom ≫
        stageEtaleCohomologyMap E a 𝒢i 𝒢j ψ V hV hV' p := by
  have h := levelEtaleCohomologyIso_naturality E a 𝒢i 𝒢j ψ V hV hV' p
  rw [IsCohomologyMap.eq_map_comp_edge_app (E.system.u a)
    ((levelEtaleRestrict E Ab.{max u v + 1} j).map ψ ≫
      (levelEtaleSquare E Ab.{max u v + 1} a).inv.app 𝒢i) V p hm,
    levelEtaleCohomologyIso_hom, levelEtaleCohomologyIso_hom]
  simp only [Category.assoc] at h ⊢
  exact h

end Stacks.EtaleCohomology.TransitionBaseChange

end

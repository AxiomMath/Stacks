module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.CocycleFormula

/-!
# Stacks 01F1 part (1), canonical comparison: degree zero, and the 03FD resolution formula

`Stacks.Cohomology.ModulePushforwardComparison.rightDerived_forget_iso_cocycles_of_hom_app_eq`
proves the *canonical comparison in every degree* clause of Stacks 01F1 abstractly: for an exact
`G`, an isomorphism `e : E ⋙ G ≅ T ⋙ Av` and a comparison
`Φ : E.rightDerived n ⋙ G ≅ T ⋙ Av.rightDerived n` whose component at `M` is computed on a pair
of injective resolutions `(I, J)` by a comparison `φ` of resolutions, `Φ` carries a cocycle to
the same cocycle.  It was written for part (2) and nothing in it is specific to pushforwards.

and its degree-zero companion
`Stacks.Cohomology.ModulePushforwardComparison.rightDerivedZeroCompForgetIso_cocycles` are both
abstract in the four functors involved; they were written for part (2) and nothing in either is
specific to pushforwards.

This file instantiates both at part (1) — module-valued sections over an open subset `U`, the
forgetful functor, and abelian-group-valued sections over `U` — which brings part (1) to the same
position as part (2): the clause is **proved in degree zero**, and in every degree it is reduced
to one statement about the second factor of the comparison alone.  For part (1) that second
factor is `ModuleSheafCohomology.sectionsComparisonIso`, the constructive form of Stacks 03FD;
the hypothesis `hΞ` below is the one thing still missing, and the last section of this docstring
says what proving it needs.

The degree-`n` theorem is therefore **not** tagged: a clause tag must not sit on a statement
carrying the clause's own content as a hypothesis, and the degree-zero theorem is not the clause
either, which asks for every degree.  Apart from `hΞ`, and the renaming of the clause's unused
`hφ` to `_hφ`, the degree-`n` statement is the clause verbatim, so discharging `hΞ` turns it into
the clause with that hypothesis deleted and nothing else changed.

## Main results

* `sectionsForgetIso_eq_trans`: `Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso`
  is `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` followed by
  `ModuleSheafCohomology.sectionsComparisonIso` — the two-factor shape the abstract reduction
  consumes.
* `sectionsForgetIso_zero_eq`: in degree zero the comparison of part (1) *is* the canonical
  isomorphism of left exact functors with their zeroth right derived functors.  Unlike part (2)
  this does not hold by construction — part (1)'s comparison is one formula in every degree, with
  no case split on the degree — but it follows from the degree-zero normalization
  `Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso_zero`, because the
  transformation that normalization composes with is an isomorphism.
* `rightDerivedSectionsForgetIso_cocycles_zero`: **Stacks 01F1 part (1), canonical comparison, in
  degree zero**, unconditionally.  The companion of, in the namespace
  `Stacks.Cohomology.ModulePushforwardComparison`,
  `rightDerived_modulePushforward_forget_iso_cocycles_zero`.
* `rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq`: **Stacks 01F1 part (1), canonical
  comparison in every degree, from the resolution-level formula for Stacks 03FD.**

## Implementation notes

The only work beyond the two instantiations is the hypothesis on cycles.  The abstract statements
carry `e.hom.app (I.cocomplex.X n)` in them, because in general the two functors `E ⋙ G` and
`T ⋙ Av` are merely isomorphic; here `e` is
`Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso`, which is `Iso.refl` because
module-valued sections followed by forgetting *is* forgetting the coefficient sheaf followed by
sections, so the clause's hypothesis — which has no such factor — is the abstract one with an
identity inserted.  This is the same adjustment part (2) makes, for the same reason.

## What `hΞ` needs

**RESOLVED.** The clause is closed unconditionally as
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso_cocycles`, carrying
`@[stacks 01F1 "part (1), canonical comparison in every degree"]`; Tag 01F1 is at 11 of 11
clause tags.  `hXi` is discharged for *every* pair of resolutions by
`Stacks.Cohomology.ModuleComparison.sectionsComparisonIso_hom_app_succ_eq`, so no iso
equality was needed; the equality is nevertheless available as
`Stacks.Cohomology.ModuleComparison.sectionsComparisonIso_eq_two_step_succ`.
The statements below therefore remain
correctly untagged -- the unconditional form is a separate declaration -- and the analysis
that follows is kept only as a record of how the obligation was reduced.

`ModuleSheafCohomology.sectionsComparisonIso` is `ModuleSheafCohomology.comparisonIso`, which in
positive degree is `DeltaFunctor.IsUniversal.isoOfIso` — effacement induction, with no formula.
`Stacks.Cohomology.ModuleComparison.comparisonIso_hom_eq_extMapComp` supplies one: the comparison
is the `Ext`-level map `e ↦ Ext.mk₀ b ∘ F(e)`, conjugated by the two identifications of `Ext`
with right-derived functors, and those identifications are read on a resolution by
`ModuleSheafCohomology.rightDerivedCoyonedaSuccIso_app` together with
`ModuleSheafCohomology.extCyclesMap_apply`, under which the class of a cocycle `t` is
`CategoryTheory.InjectiveResolution.extMk t`.  Both are stated for the *chosen* resolution and
transport to an arbitrary one along
`Stacks.Cohomology.DerivedCompTransport.isoRightDerivedObj_hom_eq`.

What is then missing is the effect of `Abelian.Ext.mapExactFunctor` on a class presented by a
cocycle:

`(I.extMk t m hm ht).mapExactFunctor F = J.extMk (F.map t ≫ φ.f n) m hm _`

for `F` exact, `I` an injective resolution of `Z`, `J` an injective resolution of `F.obj Z` and
`φ` a comparison of the image of `I` with `J` extending the identity.  Mathlib has
`CategoryTheory.InjectiveResolution.extMk_comp_mk₀`, which is a comparison of resolutions in the
*same* category, and `Abelian.Ext.mapExactFunctor_mk₀`, `_comp` and `_extClass`, but nothing
applying `Ext.mapExactFunctor` to `extMk`.  The obstruction is that the image of an injective
resolution under `SheafOfModules.toSheaf` is a resolution by `Ext`-acyclic objects and not by
injectives, so `CategoryTheory.InjectiveResolution.extEquivCohomologyClass` — which needs
`IsKInjective` — does not apply to it, and the proof has to go through the quasi-isomorphism
`F.map I.ι'` in the derived category instead, in the style of the proof of `extMk_comp_mk₀`.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparison

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- The comparison of Stacks 01F1 part (1) as a composite of its two factors: the canonical
identification of the module-valued side with the derived composite, which is
`rightDerivedCompIso` for `evaluationCompForgetIso`, followed by the constructive form of
Stacks 03FD.  This is the shape that
`Stacks.Cohomology.ModulePushforwardComparison.rightDerivedCompIso_trans_hom_app_eq` consumes. -/
theorem sectionsForgetIso_eq_trans (n : ℕ) :
    rightDerivedSectionsForgetIso R U n =
      rightDerivedCompIso (SheafOfModules.evaluation R (op U))
          (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u})
          (SheafOfModules.toSheaf R ⋙
            (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U))
          (evaluationCompForgetIso R U) n ≪≫
        ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X) R U n :=
  rfl

/-- **In degree zero the comparison of Stacks 01F1 part (1) is the canonical one**: the two
canonical isomorphisms of the left exact functors with their zeroth right derived functors, read
through `evaluationCompForgetIso`.

This is not true by construction, as it is for part (2): `rightDerivedSectionsForgetIso` is one
formula in every degree and makes no case split on the degree.  It follows from the degree-zero
normalization `rightDerivedSectionsForgetIso_zero` by cancelling
`Functor.whiskerRight (SheafOfModules.evaluation R (op U)).toRightDerivedZero`, which is an
isomorphism because `CategoryTheory.Functor.toRightDerivedZero` is the inverse of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` for a left exact functor. -/
theorem sectionsForgetIso_zero_eq :
    rightDerivedSectionsForgetIso R U 0 =
      Functor.isoWhiskerRight (SheafOfModules.evaluation R (op U)).rightDerivedZeroIsoSelf
          (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) ≪≫
        evaluationCompForgetIso R U ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (op U)).rightDerivedZeroIsoSelf.symm := by
  have hiso : IsIso (Functor.whiskerRight
      (SheafOfModules.evaluation R (op U)).toRightDerivedZero
      (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u})) := by
    rw [← Functor.rightDerivedZeroIsoSelf_inv]
    exact inferInstanceAs (IsIso (Functor.isoWhiskerRight
      (SheafOfModules.evaluation R (op U)).rightDerivedZeroIsoSelf.symm
      (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u})).hom)
  have hZ : Functor.whiskerRight (SheafOfModules.evaluation R (op U)).toRightDerivedZero
        (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) ≫
      (Functor.isoWhiskerRight (SheafOfModules.evaluation R (op U)).rightDerivedZeroIsoSelf
          (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) ≪≫
        evaluationCompForgetIso R U ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (op U)).rightDerivedZeroIsoSelf.symm).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf R)
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).toRightDerivedZero := by
    rw [Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Iso.symm_hom, Functor.rightDerivedZeroIsoSelf_inv, ← Category.assoc,
      ← Functor.whiskerRight_comp, Functor.rightDerivedZeroIsoSelf_inv_hom_id,
      Functor.whiskerRight_id', Category.id_comp]
    exact Category.id_comp _
  exact Iso.ext ((cancel_epi (Functor.whiskerRight
    (SheafOfModules.evaluation R (op U)).toRightDerivedZero
    (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}))).1
      ((rightDerivedSectionsForgetIso_zero R U).trans hZ.symm))

/-- **Stacks 01F1, part (1), canonical comparison, in degree zero.**  In degree zero the
comparison sends a cocycle to the same cocycle in an abelian injective resolution, for any
comparison `φ` of resolutions extending the identity and any induced map `c` on cocycles.

This is unconditional.  By `sectionsForgetIso_zero_eq` the comparison in degree zero is the
canonical isomorphism of left exact functors with their zeroth right derived functors, and the
clause for that isomorphism is
`Stacks.Cohomology.ModulePushforwardComparison.rightDerivedZeroCompForgetIso_cocycles`, whose
content is `CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles` on both sides
together with the naturality of `evaluationCompForgetIso` at the augmentation `I.ι.f 0`. -/
theorem rightDerivedSectionsForgetIso_cocycles_zero (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    let E := SheafOfModules.evaluation R (op U)
    let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
    let A := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles 0) ⟶ L.cycles 0)
      (_ : c ≫ L.iCycles 0 = G.map (K.iCycles 0) ≫ A.map (φ.f 0)),
      G.map (K.homologyπ 0 ≫ (I.isoRightDerivedObj E 0).inv) ≫
          (rightDerivedSectionsForgetIso R U 0).hom.app M ≫
          (J.isoRightDerivedObj A 0).hom =
        c ≫ L.homologyπ 0 := by
  intro E G A K _ c hc
  rw [sectionsForgetIso_zero_eq R U]
  exact ModulePushforwardComparison.rightDerivedZeroCompForgetIso_cocycles
    E G (SheafOfModules.toSheaf R) A
    (evaluationCompForgetIso R U) I J φ hφ c
    (hc.trans (congrArg (G.map (K.iCycles 0) ≫ ·) (Category.id_comp _).symm))

/-- **Stacks 01F1, part (1), canonical comparison in every degree, from the resolution-level
formula for Stacks 03FD.**  In every degree the comparison sends a cocycle to the same cocycle in
an abelian injective resolution.  Here `φ` is any comparison of resolutions extending the
identity, and `c` is its induced map on cocycles; `c` is determined by its hypothesis, because
the inclusion of the cocycles is a monomorphism.

The hypothesis `hΞ` says that the second factor of the comparison — the constructive Stacks 03FD
isomorphism `ModuleSheafCohomology.sectionsComparisonIso` — is computed at `M` on the pair
`(I, J)` by `φ`.  Everything else is
`Stacks.Cohomology.ModulePushforwardComparison.rightDerived_forget_iso_cocycles_of_hom_app_eq`,
whose statement is abstract in the four functors involved, together with
`Stacks.Cohomology.ModulePushforwardComparison.rightDerivedCompIso_trans_hom_app_eq` for the
first factor.  The companion for part (2) is, in the same namespace,
`rightDerived_modulePushforward_forget_iso_cocycles_succ`. -/
theorem rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq (n : ℕ) (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (_hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    (hΞ : (ModuleSheafCohomology.sectionsComparisonIso
          (Opens.grothendieckTopology X) R U n).hom.app M =
      (I.isoRightDerivedObj (SheafOfModules.toSheaf R ⋙
          (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) n).hom ≫
        (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (op U)).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
            (ComplexShape.up ℕ) n).map φ ≫
        (J.isoRightDerivedObj
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) n).inv) :
    let E := SheafOfModules.evaluation R (op U)
    let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
    let A := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles n) ⟶ L.cycles n)
      (_ : c ≫ L.iCycles n = G.map (K.iCycles n) ≫ A.map (φ.f n)),
      G.map (K.homologyπ n ≫ (I.isoRightDerivedObj E n).inv) ≫
          (rightDerivedSectionsForgetIso R U n).hom.app M ≫
          (J.isoRightDerivedObj A n).hom =
        c ≫ L.homologyπ n := by
  intro E G A K _ c hc
  rw [sectionsForgetIso_eq_trans R U n]
  exact ModulePushforwardComparison.rightDerived_forget_iso_cocycles_of_hom_app_eq
    E G (SheafOfModules.toSheaf R) A
    (evaluationCompForgetIso R U) n I J φ _
    (ModulePushforwardComparison.rightDerivedCompIso_trans_hom_app_eq
      E G (SheafOfModules.toSheaf R) A
      (evaluationCompForgetIso R U) n I J φ _ hΞ)
    c (hc.trans (congrArg (G.map (K.iCycles n) ≫ ·) (Category.id_comp _).symm))

end Stacks.Cohomology.ModuleComparison

end

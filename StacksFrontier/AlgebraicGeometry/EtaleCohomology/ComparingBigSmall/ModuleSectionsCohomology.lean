module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedModulePullback
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructureUnivLE

/-!
# Stacks 0DDH, parts (2), (4) and (6), with cohomology computed in `D(𝒪)`

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of `B`. For a complex `K` of
sheaves of `𝒪`-modules the source writes `H^n_étale(T, K)` for `H^n(RΓ(T, K))`, where
`RΓ(T, -)` is the right derived functor of sections *on the derived category of modules*
(Cohomology on Sites, Section 21.20). This file states the module clauses of Stacks 0DDH with
exactly that derived functor:

* **part (6)**: `H^n_étale(T, M) = H^n(T_étale, i_f^*M)` for `M` in `D((Sch/S)_étale, 𝒪)`;
* **part (2)**: `H^n_étale(S, Lπ_S^*K) = H^n(S_étale, K)` for `K` in `D(S_étale, 𝒪_S)`;
* **part (4)**: `H^n_étale(T, Lπ_S^*K) = H^n(T_étale, Lf_small^*K)` for `K` in `D(S_étale, 𝒪_S)`,

each as an isomorphism of functors to `D(Ab)`, natural in the coefficient object.

## The two inputs

* The same clauses computed on the underlying complexes of abelian sheaves, which are
  `AlgebraicGeometry.bigSmallEtaleModuleCohomologyIso`,
  `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIsoSelf` and
  `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIso`.
* **Stacks 0D6J** on the two sites: the derived functor of sections computed in `D(𝒪)` is the
  derived functor of sections of abelian sheaves applied to the underlying abelian complex. This
  is `Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso`, applied to sections over the
  object `T ⟶ S` of the big étale site, which are corepresented by the free abelian sheaf on that
  object, and to global sections of the small étale site of `T`, which are sections over its
  final object.

## Main definitions

* `AlgebraicGeometry.bigEtaleModuleSections` — sections over `T ⟶ S` of a sheaf of `𝒪`-modules on
  the big étale site of `S`, as an abelian group.
* `AlgebraicGeometry.smallEtaleModuleGlobalSections` — global sections of a sheaf of
  `𝒪`-modules on the small étale site of `T`, as an abelian group.

## Main results

* `AlgebraicGeometry.derivedBigEtaleModuleSectionsIso` and
  `AlgebraicGeometry.derivedSmallEtaleModuleGlobalSectionsIso` — Stacks 0D6J on the two sites.
* `AlgebraicGeometry.bigSmallEtaleModuleSectionsCohomologyIso` — **Stacks 0DDH, part (6)**.
* `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIsoSelf` —
  **Stacks 0DDH, part (2)**.
* `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIso` —
  **Stacks 0DDH, part (4)**.

## References

* [Stacks Project, Tag 0DDH](https://stacks.math.columbia.edu/tag/0DDH)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

attribute [local instance] HasDerivedCategory.standard

/-- Sections over the object `T ⟶ S` of the big étale site of `S` of a sheaf of `𝒪`-modules, as
an abelian group. -/
public abbrev bigEtaleModuleSections :
    SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) ⥤ Ab.{u + 1} :=
  SheafOfModules.toSheaf.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) ⋙
    bigEtaleSections B T S f

/-- Global sections of a sheaf of `𝒪`-modules on the small étale site of `T`, as an abelian
group. -/
public abbrev smallEtaleModuleGlobalSections :
    SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property) ⥤ Ab.{u + 1} :=
  SheafOfModules.toSheaf.{u + 1} (SmallEtale.structureSheaf B T.obj T.property) ⋙
    Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}

/-- `RΓ(T, -)` on `D((Sch/S)_étale, 𝒪)` exists: sheaves of `𝒪`-modules form a Grothendieck abelian
category, so every complex has a K-injective resolution. -/
public instance hasRightDerivedFunctor_bigEtaleModuleSections :
    ((bigEtaleModuleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property))
          (ComplexShape.up ℤ)) :=
  letI := Stacks.SheafOfModules.sheafModulesGrothendieck.{u + 1, u, u, 0}
    (BigEtaleOver.topology B S.obj S.property) (BigEtaleOver.structureSheaf B S.obj S.property)
  Stacks.Cohomology.DerivedLowerShriek.alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    _

/-- `RΓ(T_étale, -)` on `D(T_étale, 𝒪_T)` exists: sheaves of `𝒪_T`-modules form a Grothendieck
abelian category, so every complex has a K-injective resolution. -/
public instance hasRightDerivedFunctor_smallEtaleModuleGlobalSections :
    ((smallEtaleModuleGlobalSections B T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property))
          (ComplexShape.up ℤ)) :=
  letI := Stacks.SheafOfModules.sheafModulesGrothendieck.{u + 1, u, u, 0}
    (SmallEtale.topology B T.obj T.property) (SmallEtale.structureSheaf B T.obj T.property)
  Stacks.Cohomology.DerivedLowerShriek.alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    _

/-- `RΓ(T, -)` on `D((Sch/S)_étale, 𝒪)`, the right derived functor of sections over `T ⟶ S`
computed on complexes of `𝒪`-modules. -/
public abbrev derivedBigEtaleModuleSections :
    DerivedCategory (SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property)) ⥤
      DerivedCategory Ab.{u + 1} :=
  ((bigEtaleModuleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property))
        (ComplexShape.up ℤ))

/-- `RΓ(T_étale, -)` on `D(T_étale, 𝒪_T)`, the right derived functor of global sections computed
on complexes of `𝒪_T`-modules. -/
public abbrev derivedSmallEtaleModuleGlobalSections :
    DerivedCategory (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property)) ⥤
      DerivedCategory Ab.{u + 1} :=
  ((smallEtaleModuleGlobalSections B T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property))
        (ComplexShape.up ℤ))

/-- The free abelian sheaf on an object of a site is sectionwise torsion free: it is the
sheafification of a sectionwise free abelian presheaf. -/
lemma freeYoneda_isTorsionFree {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] (U : C) (V : Cᵒᵖ) :
    Module.IsTorsionFree ℤ
      (((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{u + 1} J).obj U).obj.obj V) :=
  ModuleSheafCohomology.isTorsionFree_sheafify J
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free) (fun W => by
      show Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{u + 1} (W.unop ⟶ U)))
      exact Module.Flat.isTorsionFree) V

/-- **Stacks 0D6J on the big étale site of `S`, at the object `T ⟶ S`.** `RΓ(T, -)` computed on
complexes of `𝒪`-modules is `RΓ(T, -)` of the underlying complex of abelian sheaves. Sections
over `T ⟶ S` are corepresented by the free abelian sheaf on that object, which is sectionwise
torsion free, so `Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso` applies. -/
public def derivedBigEtaleModuleSectionsIso :
    derivedBigEtaleModuleSections B T S f ≅
      (SheafOfModules.toSheaf.{u + 1}
          (BigEtaleOver.structureSheaf B S.obj S.property)).mapDerivedCategory ⋙
        (((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
              (ComplexShape.up ℤ))) :=
  letI := bigEtaleSheaf_isGrothendieckAbelian B S
  Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso.{0, u, u, u + 1}
    (BigEtaleOver.topology B S.obj S.property) (BigEtaleOver.structureSheaf B S.obj S.property)
    (bigEtaleSections B T S f) _
    (((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) (ComplexShape.up ℤ)))
    ((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)).obj (Over.mk f))
    (Stacks.Cohomology.FreeYonedaUnivLE.evaluationRepresentation.{0}
      (BigEtaleOver.topology B S.obj S.property) (Over.mk f)).symm
    (freeYoneda_isTorsionFree (BigEtaleOver.topology B S.obj S.property) (Over.mk f))

/-- **Stacks 0D6J on the small étale site of `T`, for global sections.** `RΓ(T_étale, -)` computed
on complexes of `𝒪_T`-modules is `RΓ(T_étale, -)` of the underlying complex of abelian sheaves.
Global sections are sections over the final object of the small étale site, which are
corepresented by the free abelian sheaf on it. -/
public def derivedSmallEtaleModuleGlobalSectionsIso :
    derivedSmallEtaleModuleGlobalSections B T ≅
      (SheafOfModules.toSheaf.{u + 1}
          (SmallEtale.structureSheaf B T.obj T.property)).mapDerivedCategory ⋙
        (((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
              (ComplexShape.up ℤ))) :=
  letI := smallEtaleSheaf_isGrothendieckAbelian B T
  Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso.{0, u, u, u + 1}
    (SmallEtale.topology B T.obj T.property) (SmallEtale.structureSheaf B T.obj T.property)
    (Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) _
    (((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) (ComplexShape.up ℤ)))
    ((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{u + 1}
      (SmallEtale.topology B T.obj T.property)).obj (SmallEtale.final B T.obj T.property))
    ((Stacks.Cohomology.FreeYonedaUnivLE.evaluationRepresentation.{0}
      (SmallEtale.topology B T.obj T.property) (SmallEtale.final B T.obj T.property)).symm ≪≫
      (Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B T.obj T.property) Ab.{u + 1}
        (SmallEtale.finalIsTerminal B T.obj T.property)).symm)
    (freeYoneda_isTorsionFree (SmallEtale.topology B T.obj T.property)
      (SmallEtale.final B T.obj T.property))

/-- **Stacks 0DDH, part (6).** Let `f : T ⟶ S` be a morphism of a big étale site and let `M` be
an unbounded complex of sheaves of `𝒪`-modules on the big étale site over `S`. Cohomology over
the object `T ⟶ S` agrees with cohomology on the small étale site of `T` of `i_f^*M`, naturally
in `M`:
`H^n_étale(T, M) = H^n(T_étale, i_f^*M)`.

Both sides are computed, as in the source, by the right derived functors of sections on the
derived categories of modules. The proof is the comparison on underlying abelian complexes,
`AlgebraicGeometry.bigSmallEtaleModuleCohomologyIso`, transported by Stacks 0D6J on both sites
(`AlgebraicGeometry.derivedBigEtaleModuleSectionsIso` and
`AlgebraicGeometry.derivedSmallEtaleModuleGlobalSectionsIso`). -/
@[stacks 0DDH "part (6)"]
public def bigSmallEtaleModuleSectionsCohomologyIso :
    derivedBigEtaleModuleSections B T S f ≅
      (smallEtaleModuleRestriction B T S f).mapDerivedCategory ⋙
        derivedSmallEtaleModuleGlobalSections B T :=
  derivedBigEtaleModuleSectionsIso B T S f ≪≫ bigSmallEtaleModuleCohomologyIso B T S f ≪≫
    Functor.isoWhiskerLeft _ (derivedSmallEtaleModuleGlobalSectionsIso B T).symm

/-- **Stacks 0DDH, part (2).** Let `S` be an object of a big étale site and let `K` be an
unbounded complex of sheaves of `𝒪_{S_étale}`-modules. Cohomology on the big étale site of `S`
of the derived pullback `Lπ_S^*K` agrees with cohomology of `K` on the small étale site of `S`,
naturally in `K`:
`H^n_étale(S, Lπ_S^*K) = H^n(S_étale, K)`.

Both sides are computed, as in the source, by the right derived functors of sections on the
derived categories of modules. The proof is the comparison on underlying abelian complexes,
`AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIsoSelf`, transported by
Stacks 0D6J on both sites. -/
@[stacks 0DDH "part (2)"]
public def bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIsoSelf :
    derivedSmallEtaleModuleProjectionPullback B S ⋙ derivedBigEtaleModuleSections B S S (𝟙 S) ≅
      derivedSmallEtaleModuleGlobalSections B S :=
  Functor.isoWhiskerLeft _ (derivedBigEtaleModuleSectionsIso B S S (𝟙 S)) ≪≫
    bigSmallEtaleModuleProjectionPullbackCohomologyIsoSelf B S ≪≫
    (derivedSmallEtaleModuleGlobalSectionsIso B S).symm

/-- **Stacks 0DDH, part (4).** Let `f : T ⟶ S` be a morphism of a big étale site and let `K` be
an unbounded complex of sheaves of `𝒪_{S_étale}`-modules. Cohomology over the object `T ⟶ S` of
the big étale site of `S` of the derived pullback `Lπ_S^*K` agrees with cohomology on the small
étale site of `T` of the derived small étale pullback `Lf_small^*K`, naturally in `K`:
`H^n_étale(T, Lπ_S^*K) = H^n(T_étale, Lf_small^*K)`.

Both sides are computed, as in the source, by the right derived functors of sections on the
derived categories of modules. The proof is the comparison on underlying abelian complexes,
`AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIso`, transported by
Stacks 0D6J on both sites. -/
@[stacks 0DDH "part (4)"]
public def bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIso :
    derivedSmallEtaleModuleProjectionPullback B S ⋙ derivedBigEtaleModuleSections B T S f ≅
      derivedSmallEtaleModulePullback B T S f ⋙ derivedSmallEtaleModuleGlobalSections B T :=
  Functor.isoWhiskerLeft _ (derivedBigEtaleModuleSectionsIso B T S f) ≪≫
    bigSmallEtaleModuleProjectionPullbackCohomologyIso B T S f ≪≫
    Functor.isoWhiskerLeft _ (derivedSmallEtaleModuleGlobalSectionsIso B T).symm

end AlgebraicGeometry

end

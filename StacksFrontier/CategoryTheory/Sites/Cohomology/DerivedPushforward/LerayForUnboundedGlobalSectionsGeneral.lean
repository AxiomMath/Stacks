module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSectionsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatUnit
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0D6H on global sections, for an arbitrary morphism of ringed sites

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites, given by the continuous functor
`u : D ⥤ C`. This file discharges
`Stacks.Cohomology.LerayUnbounded.ComputesSecond f_* (Γ(D, -))` with no flatness hypothesis, so
that `derivedGlobalSectionsPushforwardIso` gives

`RΓ(D, -) ∘ Rf_* ≅ RΓ(C, -)`

as functors `D(O_C) ⟶ D(Γ(O_D))`, the right hand side being derived global sections on `C` with
scalars restricted along the ring map `Γ(O_D) ⟶ Γ(O_C)`. That is the global-sections clause of
Stacks 0D6H at the source's generality.

## How

The route is the one that closed the clause on sections over an object in
`LerayForUnboundedSectionsGeneral.lean`, and the only thing it needs is a corepresenting object
for the target functor. **Global sections are corepresented by the structure sheaf itself**, not
by an extension by zero: `CategoryTheory.SheafOfModules.unitHomEquiv` reads `Hom(O_D, M)` as
`M.sections`, the limit over the whole site, and the packaged comparison is
`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`. So no final object and no punctual
presentation of `Γ(D, -)` is involved; what the source's own proof needs — the third morphism of
the chain `(C, O_C) → (D, O_D) → (pt, O_pt)` — is not what the clause needs.

Given that, for a K-injective `I` and a K-injective resolution `s : f_* I ⟶ J`:

* `CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex` identifies the complex of
  global sections with the Hom complex out of `(O_D)[0]`, naturally in the complex;
* `Stacks.Injectives.isIso_homologyMap_homComplexPostcomp` turns invertibility of the induced
  map on degree-`n` cohomology into bijectivity of postcomposition with `s⟦n⟧` on morphisms out
  of `(O_D)[0]` in `K(O_D)`;
* `bijective_postcomp_quotient_shift_of_isKInjective` is that bijectivity, and it rests on
  `bijective_qh_map_pushforward_of_isKInjective`, i.e. on Stacks 0FPI and the 07A6 derived
  adjunction.

The one geometric input is that the comparison `Lf^* ⟶ f^*` of Stacks 06YY is invertible at
`(O_D)[0]`, which holds because that complex is bounded above with flat terms: the structure
sheaf is flat by `Stacks.SheafOfModules.isFlat_unit` — the analogue here of Stacks 03EV's
flatness of `j_{V!} O_V` there — and the other terms are zero.

## Main results

All in the namespace `Stacks.Cohomology.LerayUnbounded`.

* `computesSecond_pushforwardTopos_globalSections`: the hypothesis, discharged.
* `derivedGlobalSectionsPushforwardIsoGeneral`: **Stacks 0D6H**, the global-sections clause, for
  an arbitrary morphism of ringed sites.

## Implementation notes

**The two sides are modules over different rings, and the corepresentability is of an
abelian-group-valued functor.** `Γ(D, -)` here lands in `ModuleCat (Γ(O_D))`, while
`CategoryTheory.preadditiveCoyoneda` lands in `AddCommGrpCat`. The passage between the two is
free: `HomologicalComplex.quasiIso_map_iff_of_preservesHomology` along
`forget₂ (ModuleCat (Γ(O_D))) AddCommGrpCat`, whose `Functor.PreservesHomology` and
`CategoryTheory.Functor.ReflectsIsomorphisms` instances are both found by instance search. So
the degree-`n` statement is proved for the composite with `forget₂`, where the corepresenting
object lives, and the quasi-isomorphism is read back in `ModuleCat (Γ(O_D))`.

**No `HasLeftDerivedFunctor` in the binders.** Unlike
`derivedSectionsOverObjectPushforwardIsoGeneral`, whose statement carries that `Prop` class as
an instance argument, the two results above do not: the conclusion mentions only `Rf_*` and
derived global sections, and the class — needed in the proof, where `Lf^*` appears — is
discharged inside from
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`.
It is only the intermediate lemmas, which name `derivedPullbackComparison`, that carry it.

**The assembly is split.** Written as a single declaration it exceeds the default heartbeat
budget in `whnf`; split across `isIso_homologyMap_globalSections_forget_map`,
`quasiIso_globalSections_map` and `computesSecond_pushforwardTopos_globalSections` it compiles
in seconds. `Stacks.Cohomology.LerayUnbounded.isIso_of_comp_sq` is reused from the sibling
module rather than restated.

What remains in the binders is `HasSheafify` and `WEqualsLocallyBijective` on both sites, which
is what makes `f^*` — and hence the comparison of Stacks 06YY — exist at all.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 05NI](https://stacks.math.columbia.edu/tag/05NI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.Localization
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.SiteModules
open CochainComplex.HomComplex

namespace Stacks.Cohomology.LerayUnbounded

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Every term of the complex `(O_D)[0]` is flat: the one in degree zero is the structure sheaf
read as a module over itself, flat by `Stacks.SheafOfModules.isFlat_unit`, and the others are
zero. -/
theorem isFlat_single_unit_X (i : ℤ) :
    SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (((CochainComplex.singleFunctor (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).X i) := by
  by_cases h : i = 0
  · subst h
    exact SheafOfModules.IsFlat.of_iso Y.O
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
      (Stacks.SheafOfModules.isFlat_unit Y.O)
  · exact SheafOfModules.IsFlat.of_isZero Y.O
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h)

section Comparison

variable [(pullbackOnHomotopy f.toRingedToposSiteHom).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- **The comparison `Lf^* ⟶ f^*` is invertible at `(O_D)[0]`**, that complex being bounded above
with flat terms (Stacks 06YY, with the flatness of the structure sheaf from
`Stacks.SheafOfModules.isFlat_unit`). -/
theorem isIso_derivedPullbackComparison_app_single_unit :
    IsIso ((derivedPullbackComparison f.toRingedToposSiteHom).app
      ((HomotopyCategory.quotient (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))) :=
  isIso_derivedPullbackComparison_app_boundedAbove f.toRingedToposSiteHom
    f.isMorphismOfSites_toRingedToposSiteHom _ ⟨0, inferInstance⟩ isFlat_single_unit_X

/-- **The degree-`n` piece, in abelian groups.** The map that a K-injective resolution `s` of
`f_* I` induces on the degree-`n` cohomology of the complexes of global sections, read in abelian
groups, is invertible: global sections are corepresented by the structure sheaf
(`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`), so the induced map is the one on
the cohomology of a Hom complex, and `Stacks.Injectives.isIso_homologyMap_homComplexPostcomp`
reduces its invertibility to the bijectivity of postcomposition with `s⟦n⟧` in the homotopy
category. -/
theorem isIso_homologyMap_globalSections_forget_map
    (I : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (hI : I.IsKInjective)
    {J : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : (f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) (n : ℤ)
    [IsIso ((derivedPullbackComparison f.toRingedToposSiteHom).app
      ((HomotopyCategory.quotient (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))))] :
    IsIso (HomologicalComplex.homologyMap
      (((globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        forget₂ (ModuleCat.{u} (RingCat.sectionsSubring
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
          AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map s) n) := by
  have : IsIso (HomologicalComplex.homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) s) n) :=
    Stacks.Injectives.isIso_homologyMap_homComplexPostcomp _ s n
      (bijective_postcomp_quotient_shift_of_isKInjective f.toRingedToposSiteHom
        f.isMorphismOfSites_toRingedToposSiteHom _ I hI s hJ hs n)
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (coyonedaUnitGlobalSectionsIso (J := Y.J) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n)) s).1 ?_
  exact isIso_homologyMap_coyonedaComplexMap _ s n

/-- **Global sections carry a K-injective resolution of `f_* I` to a quasi-isomorphism** of
complexes of `Γ(O_D)`-modules. The degreewise statement is
`isIso_homologyMap_globalSections_forget_map`, in abelian groups; `forget₂` preserves and
reflects homology, so it is equivalent to the statement in `ModuleCat (Γ(O_D))`. -/
theorem quasiIso_globalSections_map
    (I : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (hI : I.IsKInjective)
    {J : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : (f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s)
    [IsIso ((derivedPullbackComparison f.toRingedToposSiteHom).app
      ((HomotopyCategory.quotient (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))))] :
    QuasiIso (((globalSectionsFunctor.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u} (RingCat.sectionsSubring
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)) AddCommGrpCat.{u}),
    quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_globalSections_forget_map f I hI s hJ hs n

end Comparison

/-- A quasi-isomorphism becomes invertible under `Qh` after passing to the homotopy category. -/
private theorem isIso_Qh_map_quotient_map {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {K L : CochainComplex A ℤ} {s : K ⟶ L} (hs : QuasiIso s) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) := by
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff]
  exact hs

/-- **The hypothesis of Stacks 0D6H's global-sections clause, discharged.** For every morphism of
ringed sites, `f_* I` computes `RΓ(D, -)` for every K-injective complex `I` of `O_C`-modules.

Testing on a K-injective resolution `s : f_* I ⟶ J` reduces this to `Γ(D, s)` being a
quasi-isomorphism, which is `quasiIso_globalSections_map`; the comparison of `RΓ(D, -)` is
invertible at `J` because `J` is K-injective, and `s` becomes invertible in the derived category,
so the naturality square at `s` gives the conclusion. -/
theorem computesSecond_pushforwardTopos_globalSections :
    ComputesSecond f.toRingedToposSiteHom.pushforwardTopos
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) := by
  intro I hI
  let := hasLeftDerivedFunctor_pullbackOnHomotopy f.toRingedToposSiteHom
    f.isMorphismOfSites_toRingedToposSiteHom
  obtain ⟨J, s, hJ, hs⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have := isIso_derivedPullbackComparison_app_single_unit f
  have hq : QuasiIso (((globalSectionsFunctor.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map s) := quasiIso_globalSections_map f I hI s hJ hs
  refine isIso_of_comp_sq ((totalDerivedUnit
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).naturality
      ((HomotopyCategory.quotient (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)).map s)) ?_ ?_ ?_
  · exact isIso_Qh_map_quotient_map hq
  · have := hJ
    exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ J
  · have := isIso_Qh_map_quotient_map hs
    exact ((Stacks.DerivedFunctor.totalRightDerived
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).mapIso
      (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (ComplexShape.up ℤ)).map s)))).isIso_hom

/-- **Stacks 0D6H, the global-sections clause, for an arbitrary morphism of ringed sites.** Let
`f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the continuous functor
`u : D ⥤ C`. Then `RΓ(D, -) ∘ Rf_* = RΓ(C, -)` as functors `D(O_C) ⟶ D(Γ(O_D))`, the right hand
side being the derived global sections on `C` with scalars restricted along the induced ring map
`Γ(O_D) ⟶ Γ(O_C)`.

No flatness: this is `derivedGlobalSectionsPushforwardIso` with its hypothesis discharged by
`computesSecond_pushforwardTopos_globalSections`. The source's other clause, the one on sections
over an object of `D`, is
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral`. -/
@[stacks 0D6H "the clause on global sections, as functors into the derived category of modules
over the global sections of the structure sheaf of the target, for an arbitrary morphism of
ringed sites; the clause on sections over an object of the target site is
derivedSectionsOverObjectPushforwardIsoGeneral"]
noncomputable def derivedGlobalSectionsPushforwardIsoGeneral :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedGlobalSections Y ≅
      derivedGlobalSectionsRestricted f :=
  derivedGlobalSectionsPushforwardIso f (computesSecond_pushforwardTopos_globalSections f)

end Stacks.Cohomology.LerayUnbounded

end

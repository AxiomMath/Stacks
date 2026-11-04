module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PostcompIntoPushforwardOfKInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Modules.SectionsOverObjectCorepresentable
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexFromSinglePostcomp
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatSliceExtension
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0D6H on sections over an object, for an arbitrary morphism of ringed sites

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. This file discharges
`Stacks.Cohomology.LerayUnbounded.ComputesSecond f_* (Γ(V, -))` with no flatness hypothesis, so
that `derivedSectionsOverObjectPushforwardIso` gives

`RΓ(V, -) ∘ Rf_* ≅ RΓ(U, -)`

for every morphism of ringed sites, which is the clause of Stacks 0D6H on sections over an
object at the source's generality.

## How

`Γ(V, -)` is corepresented by `j_{V!} O_V` (Stacks 0G1V,
`Stacks.Sites.ExtensionByZero.coyonedaExtensionByZeroUnitIso`), so the complex of sections over
`V` of a complex is the Hom complex out of `(j_{V!} O_V)[0]`
(`CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex`, natural in the complex by
`homComplexSingleIsoCoyonedaComplex_naturality`). For a K-injective `I` and a K-injective
resolution `s : f_* I ⟶ J`:

* `Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff` turns the invertibility
  of the comparison `Γ(V, f_* I) ⟶ RΓ(V, f_* I)` into `Γ(V, s)` being a quasi-isomorphism;
* `isIso_homologyMap_homComplexPostcomp` turns that, degree by degree, into bijectivity of
  postcomposition with `s⟦n⟧` on morphisms out of `(j_{V!} O_V)[0]` in `K(O_D)`;
* `bijective_postcomp_quotient_shift_of_isKInjective` is that bijectivity, and it rests on
  `bijective_qh_map_pushforward_of_isKInjective`, i.e. on Stacks 0FPI and the 07A6 derived
  adjunction.

The one geometric input is that the comparison `Lf^* ⟶ f^*` of Stacks 06YY is invertible at
`(j_{V!} O_V)[0]`, which holds because that complex is bounded above with flat terms: `j_{V!} O_V`
is flat by Stacks 03EV and the other terms are zero.

## Main results

* `Stacks.Cohomology.LerayUnbounded.computesSecond_pushforwardTopos_sectionsOverObject`:
  the hypothesis, discharged.
* `Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral`:
  **Stacks 0D6H**, the clause on sections over an object, for an arbitrary morphism of ringed
  sites.

## Implementation notes

No `hmos` is carried: `AlgebraicGeometry.RingedSite.Hom` *stores* `isMorphismOfSites`, so a
morphism of ringed sites is already what the 07A6/0FPI chain asks of a morphism of ringed topoi,
and `AlgebraicGeometry.RingedSite.Hom.isMorphismOfSites_toRingedToposSiteHom` supplies it in the
spelling that chain uses. What remains in the binders is `HasSheafify` and
`WEqualsLocallyBijective` on both sites, which is what makes `f^*` exist at all, and the
`HasLeftDerivedFunctor` `Prop` class, discharged inside by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`.

The global-sections clause of Stacks 0D6H is not covered here. It is
`derivedGlobalSectionsPushforwardIsoGeneral` of `LerayForUnboundedGlobalSectionsGeneral`, which
runs this same route with `Γ(D, -)` corepresented by the structure sheaf itself.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.Localization
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open CochainComplex.HomComplex

namespace Stacks.Cohomology.LerayUnbounded

universe u v w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Every term of the complex `(j_{V!} O_V)[0]` is flat: the one in degree zero is
`j_{V!} O_V`, flat by Stacks 03EV, and the others are zero. -/
theorem isFlat_single_extensionByZeroUnit_X (i : ℤ) :
    SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (Stacks.Sites.ExtensionByZero.extensionByZeroUnitObj Y.J
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)).X i) := by
  by_cases h : i = 0
  · subst h
    exact SheafOfModules.IsFlat.of_iso Y.O
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
      (Stacks.Sites.OverModules.sheafExtensionUnit_isFlat Y.J Y.O V)
  · exact SheafOfModules.IsFlat.of_isZero Y.O
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h)

variable [(pullbackOnHomotopy f.toRingedToposSiteHom).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))]

/-- **The comparison `Lf^* ⟶ f^*` is invertible at `(j_{V!} O_V)[0]`**, that complex being
bounded above with flat terms (Stacks 06YY, with the flatness of `j_{V!} O_V` from Stacks
03EV). -/
theorem isIso_derivedPullbackComparison_app_single_extensionByZeroUnit :
    IsIso ((derivedPullbackComparison f.toRingedToposSiteHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (Stacks.Sites.ExtensionByZero.extensionByZeroUnitObj Y.J
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)))) :=
  isIso_derivedPullbackComparison_app_boundedAbove f.toRingedToposSiteHom
    f.isMorphismOfSites_toRingedToposSiteHom _ ⟨0, inferInstance⟩
    (isFlat_single_extensionByZeroUnit_X V)

/-- If `a ≫ b = c ≫ d` with `a`, `b` and `d` invertible, so is `c`. Used to read off the
invertibility of a comparison from the naturality square at a resolution. -/
theorem isIso_of_comp_sq {C : Type*} [Category C] {W Z₁ Z₂ Z₃ : C} {a : W ⟶ Z₁} {b : Z₁ ⟶ Z₃}
    {c : W ⟶ Z₂} {d : Z₂ ⟶ Z₃} (h : a ≫ b = c ≫ d) (ha : IsIso a) (hb : IsIso b)
    (hd : IsIso d) : IsIso c := by
  have := ha
  have := hb
  have := hd
  have hc : c = (a ≫ b) ≫ inv d := (IsIso.eq_comp_inv d).2 h.symm
  rw [hc]
  infer_instance

/-- **The degree-`n` piece.** The map that a K-injective resolution `s` of `f_* I` induces on the
degree-`n` cohomology of the complexes of sections over `V` is invertible: sections over `V` are
corepresented by `j_{V!} O_V`, so the induced map is the one on the cohomology of a Hom complex,
and `Stacks.Injectives.isIso_homologyMap_homComplexPostcomp` reduces its invertibility to the
bijectivity of postcomposition with `s⟦n⟧` in the homotopy category. -/
theorem isIso_homologyMap_sectionsOverObject_map
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : (f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) (n : ℤ)
    [IsIso ((derivedPullbackComparison f.toRingedToposSiteHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (Stacks.Sites.ExtensionByZero.extensionByZeroUnitObj Y.J
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V))))] :
    IsIso (HomologicalComplex.homologyMap
      (((sectionsOverObject Y V).mapHomologicalComplex (ComplexShape.up ℤ)).map s) n) := by
  have : IsIso (HomologicalComplex.homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (Stacks.Sites.ExtensionByZero.extensionByZeroUnitObj Y.J
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)) s) n) :=
    Stacks.Injectives.isIso_homologyMap_homComplexPostcomp _ s n
      (bijective_postcomp_quotient_shift_of_isKInjective f.toRingedToposSiteHom
        f.isMorphismOfSites_toRingedToposSiteHom _ I hI s hJ hs n)
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (Stacks.Sites.ExtensionByZero.coyonedaExtensionByZeroUnitIso Y.J
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)
      (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n)) s).1 ?_
  exact isIso_homologyMap_coyonedaComplexMap _ s n

/-- **Sections over `V` carry a K-injective resolution of `f_* I` to a quasi-isomorphism.** -/
theorem quasiIso_sectionsOverObject_map
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : (f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s)
    [IsIso ((derivedPullbackComparison f.toRingedToposSiteHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (Stacks.Sites.ExtensionByZero.extensionByZeroUnitObj Y.J
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V))))] :
    QuasiIso (((sectionsOverObject Y V).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_sectionsOverObject_map f V I hI s hJ hs n

/-- A quasi-isomorphism of complexes becomes invertible under `Qh ∘ quotient`. -/
private theorem isIso_Qh_map_quotient_map_of_quasiIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] {K L : CochainComplex C ℤ} (g : K ⟶ L) (hg : QuasiIso g) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g)) := by
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff]
  exact hg

/-- **The hypothesis of Stacks 0D6H's clause on sections over an object, discharged.** For every
morphism of ringed sites and every object `V` of the target, `f_* I` computes `RΓ(V, -)` for every
K-injective complex `I` of `O_C`-modules.

Testing on a K-injective resolution `s : f_* I ⟶ J` reduces this to `Γ(V, s)` being a
quasi-isomorphism, which is `quasiIso_sectionsOverObject_map`; the comparison of `RΓ(V, -)` is
invertible at `J` because `J` is K-injective, and `s` becomes invertible in the derived category,
so the naturality square at `s` gives the conclusion. -/
theorem computesSecond_pushforwardTopos_sectionsOverObject :
    ComputesSecond f.toRingedToposSiteHom.pushforwardTopos (sectionsOverObject Y V) := by
  intro I hI
  obtain ⟨J, s, hJ, hs⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)
  have := isIso_derivedPullbackComparison_app_single_extensionByZeroUnit f V
  have hq : QuasiIso (((sectionsOverObject Y V).mapHomologicalComplex
    (ComplexShape.up ℤ)).map s) := quasiIso_sectionsOverObject_map f V I hI s hJ hs
  refine isIso_of_comp_sq ((totalDerivedUnit (sectionsOverObject Y V)).naturality
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)).map s))
    ?_ ?_ ?_
  · exact isIso_Qh_map_quotient_map_of_quasiIso _ hq
  · have := hJ
    exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ J
  · have := isIso_Qh_map_quotient_map_of_quasiIso s hs
    exact ((Stacks.DerivedFunctor.totalRightDerived (sectionsOverObject Y V)).mapIso
      (asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).map s)))).isIso_hom

/-- **Stacks 0D6H, the clause on sections over an object, for an arbitrary morphism of ringed
sites.** Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the continuous
functor `u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. Then
`RΓ(V, -) ∘ Rf_* = RΓ(U, -)` as functors `D(O_C) ⟶ D(Ab)`.

No flatness: this is `derivedSectionsOverObjectPushforwardIso` with its hypothesis discharged by
`computesSecond_pushforwardTopos_sectionsOverObject`. The source's other clause, the one about
global sections into `D(Γ(O_D))`, is
`Stacks.Cohomology.LerayUnbounded.derivedGlobalSectionsPushforwardIsoGeneral`. -/
@[stacks 0D6H "the clause on sections over an object of the target site, for an arbitrary
morphism of ringed sites; the clause on global sections into the derived category of modules
over the global sections of the structure sheaf of the target is
derivedGlobalSectionsPushforwardIsoGeneral"]
noncomputable def derivedSectionsOverObjectPushforwardIsoGeneral :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ≅
      derivedSectionsOverObject X (f.u.obj V) :=
  derivedSectionsOverObjectPushforwardIso f V
    (computesSecond_pushforwardTopos_sectionsOverObject f V)

end Stacks.Cohomology.LerayUnbounded

end

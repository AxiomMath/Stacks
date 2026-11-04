module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkSourceComparison
public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations

/-!
# The open equality of the stalk diagram, below `DerivedCategory.Q`

Let `i' : Z' ⟶ X'`, `g : Z' ⟶ Z`, `f : X' ⟶ X`, `i : Z ⟶ X` be a pullback square of schemes with
`i` a closed immersion. Composing both sides of the equality
`Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEq` with the comparison tail of
Stacks 0661 gives an equality `DerivedStalkBaseChangeEqQ` in which no isomorphism of functors
occurs: on the left the derived stalk of the derived base change map of Stacks 08HY, the
canonical map from the derived pullback along `g` to the degreewise pullback, the derived stalk of
`Ri'_*` on the image, and `DerivedCategory.Q` of maps of complexes; on the right the same
ingredients for `i` and `f` followed by `DerivedCategory.Q` of the *underived* comparison of
Stacks 065Z. This file shows that the two equalities are equivalent, and that the equality below
`DerivedCategory.Q` at the K-flat complexes already implies both, hence Stacks 0E23.

## Main definitions

* `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQAt`: the open equality
  below `DerivedCategory.Q`, at one point and one complex.
* `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQ`: the open equality
  below `DerivedCategory.Q`, at every point and every complex.
* `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQKFlat`: the open equality
  below `DerivedCategory.Q`, at every point and every K-flat complex.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.stalkComparison_app_Q_comp_counit`: the comparison
  of Stacks 0661 at the four local rings, against its counit equation.
* `Stacks.Cohomology.ClosedImmersionBaseChange.stalkComparison_app_derivedStalk_comp_counit`: the
  same at the derived stalk of a complex.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEq_app_Q`: the open equality
  at `DerivedCategory.Q.obj P` for a K-flat `P`, assuming `DerivedStalkBaseChangeEqQ`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChange_lhs_naturality`: the
  left-hand side of the open equality is natural in the complex.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEq_of_Q`:
  `DerivedStalkBaseChangeEqQ` implies `DerivedStalkBaseChangeEq`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEqQ_of_eq`:
  `DerivedStalkBaseChangeEq` implies `DerivedStalkBaseChangeEqQ`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEqQ_of_kFlat`:
  `DerivedStalkBaseChangeEqQKFlat` implies `DerivedStalkBaseChangeEqQ`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_Q` and
  `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_Q_kFlat`: Stacks
  0E23 at the level of functors, assuming `DerivedStalkBaseChangeEqQ`, respectively
  `DerivedStalkBaseChangeEqQKFlat`.

## Implementation notes

The concrete equations mix `AlgebraicGeometry.Scheme.Modules` with
`CategoryTheory.SheafOfModules (structureSheafRing _)`, which are definitionally but not reducibly
equal, so `rw` and `simp` cannot check their motives. `tailEqChase`, `comparisonTailChase`,
`naturalityChase` and `transferEq` state the cancellations for free objects and morphisms and are
applied by `exact`.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

universe u

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isLeftDerived_alphaG isLeftDerived_alphaH

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- The comparison of Stacks 0661 at the four local rings, against its counit equation. -/
theorem stalkComparison_app_Q_comp_counit (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (hpt : i (g w) = f (i' w))
    (K' : CochainComplex (ModuleCat.{u} (ToType (Z.presheaf.stalk (g w)))) ℤ) :
    (stalkComparison sq w hpt).app (DerivedCategory.Q.obj K') ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategory.map ((alphaH (g := g) w).app K') ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} (g.stalkMap w).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K') =
      (Lg w hpt).map
          ((ModuleCat.restrictScalars.{u, u, u}
            (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app K') ≫
        (alphaG w hpt).app
            (((ModuleCat.restrictScalars.{u, u, u}
              (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K') ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (derivedBaseChangeComparison.{u, u, u, u, u} (i.stalkMap (g w)).hom
              (ringRR' w hpt) (g.stalkMap w).hom (i'.stalkMap w).hom
              (stalkMap_ringHom_square sq w hpt)
              (Lg w hpt) (Lh w) (alphaG w hpt) (alphaH w)).1 (ComplexShape.up ℤ)).app K') :=
  derivedBaseChangeComparison_snd_app_comp_counit.{u, u, u, u, u} _ _ _ _
    (stalkMap_ringHom_square sq w hpt) (Lg w hpt) (Lh w) (alphaG w hpt) (alphaH w) K'

/-- A naturality step followed by a counit equation, at free objects of an arbitrary category. -/
theorem comparisonTailChase {A : Type*} [Category A] {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : A}
    (sc₁ : a₀ ⟶ a₁) (t₁ : a₁ ⟶ a₂) (t₂ : a₂ ⟶ a₃) (t₃ : a₃ ⟶ a₄)
    (u : a₀ ⟶ a₅) (sc₂ : a₅ ⟶ a₂) (v : a₅ ⟶ a₆) (al : a₆ ⟶ a₇) (q : a₇ ⟶ a₄) (lr : a₀ ⟶ a₆)
    (hnat : sc₁ ≫ t₁ = u ≫ sc₂)
    (hstep : sc₂ ≫ t₂ ≫ t₃ = v ≫ al ≫ q)
    (hu : u ≫ v = lr) :
    sc₁ ≫ t₁ ≫ t₂ ≫ t₃ = lr ≫ al ≫ q := by
  rw [← Category.assoc, hnat, Category.assoc, hstep, ← Category.assoc, hu]

/-- A commuting square carried by a functor, at free objects of arbitrary categories. -/
theorem mapNaturality {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z t : C} (p : x ⟶ y) (q : y ⟶ t) (p' : x ⟶ z) (q' : z ⟶ t)
    (hpq : p ≫ q = p' ≫ q') : F.map p ≫ F.map q = F.map p' ≫ F.map q' := by
  rw [← F.map_comp, ← F.map_comp, hpq]

/-- Transport of an equation of morphisms along an isomorphism on each side. -/
theorem transferEq {A : Type*} [Category A] {x₁ x₂ y₁ y₂ : A}
    (L₁ R₁ : x₁ ⟶ y₁) (L₂ R₂ : x₂ ⟶ y₂) (a : x₁ ⟶ x₂) (b : y₁ ⟶ y₂) (ha : IsIso a)
    (hL : a ≫ L₂ = L₁ ≫ b) (hR : a ≫ R₂ = R₁ ≫ b) (h : L₁ = R₁) : L₂ = R₂ := by
  have := ha
  rw [← cancel_epi a, hL, hR, h]

/-- Three naturality squares composed, at free objects of an arbitrary category. -/
theorem naturalityChase {A : Type*} [Category A] {x₁ y₁ z₁ t₁ x₂ y₂ z₂ t₂ : A}
    (s₁ : x₁ ⟶ y₁) (m₁ : y₁ ⟶ z₁) (e₁ : z₁ ⟶ t₁)
    (s₂ : x₂ ⟶ y₂) (m₂ : y₂ ⟶ z₂) (e₂ : z₂ ⟶ t₂)
    (a : x₁ ⟶ x₂) (b : y₁ ⟶ y₂) (c : z₁ ⟶ z₂) (d : t₁ ⟶ t₂)
    (hs : a ≫ s₂ = s₁ ≫ b) (hm : b ≫ m₂ = m₁ ≫ c) (he : c ≫ e₂ = e₁ ≫ d) :
    a ≫ s₂ ≫ m₂ ≫ e₂ = (s₁ ≫ m₁ ≫ e₁) ≫ d := by
  rw [← Category.assoc, hs, Category.assoc, ← Category.assoc b m₂ e₂, hm, Category.assoc, he]
  simp

/-- The comparison of Stacks 0661 at the derived stalk of a complex `P`, composed with the
comparison tail, equals the composite of the derived extension of scalars of the stalk
factorizations, the comparison `alphaG`, and `DerivedCategory.Q` of the underived comparison of
Stacks 065Z at the stalk complex of `P`. -/
theorem stalkComparison_app_derivedStalk_comp_counit (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (hpt : i (g w) = f (i' w))
    (P : CochainComplex Z.Modules ℤ) :
    (stalkComparison sq w hpt).app
          ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj (DerivedCategory.Q.obj P)) ≫
        ((Lh (g := g) w ⋙ (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategory).map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
            (g w)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategory.map
          ((alphaH (g := g) w).app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} (g.stalkMap w).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) =
      (Lg w hpt).map
          ((ModuleCat.restrictScalars.{u, u, u}
                (i.stalkMap (g w)).hom).mapDerivedCategory.map
              ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                (g w)).mapDerivedCategoryFactors.hom.app P) ≫
            (ModuleCat.restrictScalars.{u, u, u}
                (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
        (alphaG w hpt).app
            (((ModuleCat.restrictScalars.{u, u, u}
                (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (derivedBaseChangeComparison.{u, u, u, u, u} (i.stalkMap (g w)).hom
              (ringRR' w hpt) (g.stalkMap w).hom (i'.stalkMap w).hom
              (stalkMap_ringHom_square sq w hpt)
              (Lg w hpt) (Lh w) (alphaG w hpt) (alphaH w)).1 (ComplexShape.up ℤ)).app
                (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) :=
  comparisonTailChase _ _ _ _ _ _ _ _ _ _
    (((stalkComparison sq w hpt).naturality
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
        (g w)).mapDerivedCategoryFactors.hom.app P)).symm)
    (stalkComparison_app_Q_comp_counit sq w hpt
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))
    (((Lg w hpt).map_comp _ _).symm)

/-- In a category, if `si ≫ sh = 𝟙`, `th ≫ t₁ ≫ t₂ = tr`, `bc ≫ tr ≫ t₃ = sr ≫ qc`,
`sh ≫ lr₁ ≫ lr₂ = sr` and `rc ≫ t₁ ≫ t₂ ≫ t₃ = lr₁ ≫ lr₂ ≫ qc` with `t₁ ≫ t₂ ≫ t₃` an isomorphism,
then `si ≫ bc ≫ th = rc`. -/
theorem tailEqChase {A : Type*} [Category A] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : A}
    (si : o₀ ⟶ o₁) (sh : o₁ ⟶ o₀) (bc : o₁ ⟶ o₂) (th : o₂ ⟶ o₃)
    (t₁ : o₃ ⟶ o₄) (t₂ : o₄ ⟶ o₅) (t₃ : o₅ ⟶ o₆)
    (tr : o₂ ⟶ o₅) (sr : o₁ ⟶ o₇) (qc : o₇ ⟶ o₆) {o₈ : A} (lr₁ : o₀ ⟶ o₈) (lr₂ : o₈ ⟶ o₇)
    (rc : o₀ ⟶ o₃)
    (htarget : th ≫ t₁ ≫ t₂ = tr)
    (hQ : bc ≫ tr ≫ t₃ = sr ≫ qc)
    (hsource : sh ≫ lr₁ ≫ lr₂ = sr)
    (hinv : si ≫ sh = CategoryStruct.id o₀)
    (hright : rc ≫ t₁ ≫ t₂ ≫ t₃ = lr₁ ≫ lr₂ ≫ qc)
    (hiso : IsIso (t₁ ≫ t₂ ≫ t₃)) :
    si ≫ bc ≫ th = rc := by
  have := hiso
  rw [← cancel_mono (t₁ ≫ t₂ ≫ t₃)]
  simp [reassoc_of% htarget, hQ, ← hsource, reassoc_of% hinv, hright]

/-- In a category, if `sh ≫ si = 𝟙`, `th ≫ t₁ ≫ t₂ = tr`, `sh ≫ lr₁ ≫ lr₂ = sr`,
`rc ≫ t₁ ≫ t₂ ≫ t₃ = lr₁ ≫ lr₂ ≫ qc` and `si ≫ bc ≫ th = rc`, then
`bc ≫ tr ≫ t₃ = sr ≫ qc`. -/
theorem qEqChase {A : Type*} [Category A] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : A}
    (si : o₀ ⟶ o₁) (sh : o₁ ⟶ o₀) (bc : o₁ ⟶ o₂) (th : o₂ ⟶ o₃)
    (t₁ : o₃ ⟶ o₄) (t₂ : o₄ ⟶ o₅) (t₃ : o₅ ⟶ o₆)
    (tr : o₂ ⟶ o₅) (sr : o₁ ⟶ o₇) (qc : o₇ ⟶ o₆) {o₈ : A} (lr₁ : o₀ ⟶ o₈) (lr₂ : o₈ ⟶ o₇)
    (rc : o₀ ⟶ o₃)
    (htarget : th ≫ t₁ ≫ t₂ = tr)
    (hsource : sh ≫ lr₁ ≫ lr₂ = sr)
    (hinv : sh ≫ si = CategoryStruct.id o₁)
    (hright : rc ≫ t₁ ≫ t₂ ≫ t₃ = lr₁ ≫ lr₂ ≫ qc)
    (heq : si ≫ bc ≫ th = rc) :
    bc ≫ tr ≫ t₃ = sr ≫ qc := by
  calc bc ≫ tr ≫ t₃
      = (sh ≫ si) ≫ bc ≫ (th ≫ t₁ ≫ t₂) ≫ t₃ := by rw [hinv, htarget]; simp
    _ = sh ≫ (si ≫ bc ≫ th) ≫ t₁ ≫ t₂ ≫ t₃ := by simp
    _ = sh ≫ lr₁ ≫ lr₂ ≫ qc := by rw [heq, hright]
    _ = sr ≫ qc := by rw [← hsource]; simp

open Stacks.Cohomology.DerivedBaseChange in
/-- The open equality below `DerivedCategory.Q` at one point and one complex: for a point `w` of
`Z'` and a cochain complex `P` of `𝒪_Z`-modules, the derived stalk at `i' w` of the derived base
change map of Stacks 08HY at `DerivedCategory.Q.obj P`, followed by the target chain computed
against the comparison tail of Stacks 0661, is the source chain computed against that comparison,
followed by `DerivedCategory.Q` of the underived comparison of Stacks 065Z at the stalk complex of
`P`. -/
abbrev DerivedStalkBaseChangeEqQAt (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) : Prop :=
  letI := isClosedImmersion_of_isPullback sq
  (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
        (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
          f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) (DerivedCategory.Q.obj P)) ≫
      ((derivedPushforward i'.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          (AlgebraicGeometry.pullbackComparisonOnComplex g P) ≫
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i' w).hom.app
          (DerivedCategory.Q.obj (((Scheme.Modules.pullback g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z'
                w).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback g).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso g w).symm
              (ComplexShape.up ℤ)).hom.app P))) ≫
      (ModuleCat.restrictScalars.{u, u, u}
          (i'.stalkMap w).hom).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars.{u, u, u} (g.stalkMap w).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
    ((derivedPullback f.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
                i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
            (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P) ≫
        (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
            (AlgebraicGeometry.pullbackComparisonOnComplex f
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X'
                (i' w)).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                  (Stacks.ModuleSkyscraper.pullbackStalkIso f (i' w)).symm
                  (ComplexShape.up ℤ)).hom.app
                (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) ≫
          DerivedCategory.Q.map
              (((ModuleCat.extendScalars.{u, u, u}
                  (f.stalkMap (i' w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).map
                ((NatIso.mapHomologicalComplex
                      (modulesStalkFunctorCongr (ptEq sq w).symm)
                      (ComplexShape.up ℤ)).inv.app
                    (((Scheme.Modules.pushforward i).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj P) ≫
                  ((ModuleCat.restrictScalars.{u, u, u}
                    (X.presheaf.stalkCongr
                      (Inseparable.of_eq (ptEq sq w).symm)).hom.hom).mapHomologicalComplex
                        (ComplexShape.up ℤ)).map
                    ((NatTrans.mapHomologicalComplex
                      (Stacks.ModuleSkyscraper.pushStalkMap i (g w))
                        (ComplexShape.up ℤ)).app P))) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (StacksDraft.DerivedRingIso.extendScalarsRestrictIso
                  (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w))).hom.hom
                  (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w).symm)).hom.hom
                  (stalkCongr_symm_hom_hom_apply (ptEq sq w))
                  (stalkCongr_hom_symm_hom_apply (ptEq sq w))
                  (f.stalkMap (i' w)).hom).hom (ComplexShape.up ℤ)).app
                (((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (derivedBaseChangeComparison.{u, u, u, u, u} (i.stalkMap (g w)).hom
          (ringRR' w (ptEq sq w)) (g.stalkMap w).hom (i'.stalkMap w).hom
          (stalkMap_ringHom_square sq w (ptEq sq w))
          (Lg w (ptEq sq w)) (Lh w) (alphaG w (ptEq sq w)) (alphaH w)).1
            (ComplexShape.up ℤ)).app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))

/-- The open equality below `DerivedCategory.Q`: `DerivedStalkBaseChangeEqQAt` at every point of
`Z'` and at every cochain complex of `𝒪_Z`-modules. -/
abbrev DerivedStalkBaseChangeEqQ (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] : Prop :=
  ∀ (w : Z') (P : CochainComplex Z.Modules ℤ), DerivedStalkBaseChangeEqQAt sq w P

/-- The open equality below `DerivedCategory.Q` at the K-flat complexes:
`DerivedStalkBaseChangeEqQAt` at every point of `Z'` and at every K-flat cochain complex of
`𝒪_Z`-modules. -/
abbrev DerivedStalkBaseChangeEqQKFlat (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] : Prop :=
  ∀ (w : Z') (P : CochainComplex Z.Modules ℤ),
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P →
      DerivedStalkBaseChangeEqQAt sq w P

open Stacks.Cohomology.DerivedBaseChange in
/-- The open equality of the stalk diagram at `DerivedCategory.Q.obj P` for a K-flat complex `P`,
assuming `DerivedStalkBaseChangeEqQAt` at `w` and `P`. -/
theorem derivedStalkBaseChangeEq_app_Q_of_at (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion i']
    (w : Z') (P : CochainComplex Z.Modules ℤ) (hQ : DerivedStalkBaseChangeEqQAt sq w P)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P) :
    (derivedStalkSourceIso w (ptEq sq w)).inv.app (DerivedCategory.Q.obj P) ≫
        (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
            f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) (DerivedCategory.Q.obj P)) ≫
        (derivedStalkTargetIso w).hom.app (DerivedCategory.Q.obj P) =
      (stalkComparison sq w (ptEq sq w)).app
        ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj (DerivedCategory.Q.obj P)) := by
  have : IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
      (g w)).mapDerivedCategoryFactors.hom.app P) :=
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
      (g w)).mapDerivedCategoryFactors.app P).isIso_hom
  have : IsIso ((ModuleCat.restrictScalars.{u, u, u}
      (i'.stalkMap w).hom).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars.{u, u, u} (g.stalkMap w).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))) :=
    ((ModuleCat.restrictScalars.{u, u, u}
      (i'.stalkMap w).hom).mapDerivedCategoryFactors.app _).isIso_hom
  have : IsIso ((alphaH (g := g) w).app
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) :=
    (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).comparison_isIso_of_kFlat _
      (AlgebraicGeometry.kFlat_modulesStalkFunctor (g w) P hP)
  refine tailEqChase _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedStalkTargetIso_hom_app_Q_comp_comparison (i' := i') (g := g) w P) hQ
    (derivedStalkSourceIso_hom_app_Q_comp_alphaG w (ptEq sq w) P)
    ((derivedStalkSourceIso w (ptEq sq w)).inv_hom_id_app (DerivedCategory.Q.obj P))
    (stalkComparison_app_derivedStalk_comp_counit sq w (ptEq sq w) P)
    (by
      refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_)
      · exact ((Lh (g := g) w ⋙ (ModuleCat.restrictScalars.{u, u, u}
          (i'.stalkMap w).hom).mapDerivedCategory).mapIso
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              (g w)).mapDerivedCategoryFactors.app P)).isIso_hom
      · infer_instance
      · infer_instance)

open Stacks.Cohomology.DerivedBaseChange in
/-- The open equality of the stalk diagram at `DerivedCategory.Q.obj P` for a K-flat complex `P`,
assuming `DerivedStalkBaseChangeEqQ`. -/
theorem derivedStalkBaseChangeEq_app_Q (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion i']
    (h : DerivedStalkBaseChangeEqQ sq) (w : Z') (P : CochainComplex Z.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P) :
    (derivedStalkSourceIso w (ptEq sq w)).inv.app (DerivedCategory.Q.obj P) ≫
        (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
            f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) (DerivedCategory.Q.obj P)) ≫
        (derivedStalkTargetIso w).hom.app (DerivedCategory.Q.obj P) =
      (stalkComparison sq w (ptEq sq w)).app
        ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj (DerivedCategory.Q.obj P)) :=
  derivedStalkBaseChangeEq_app_Q_of_at sq w P (h w P) hP

open Stacks.Cohomology.DerivedBaseChange in
/-- The left-hand side of the open equality, the composite of the inverse of the source chain,
the derived stalk of the derived base change map and the target chain, is natural in the object
of the derived category. -/
theorem derivedStalkBaseChange_lhs_naturality (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion i'] (w : Z')
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))}
    (u : K₁ ⟶ K₂) :
    (AlgebraicGeometry.derivedStalkFunctor (g w) ⋙
          (ModuleCat.restrictScalars.{u, u, u}
            (i.stalkMap (g w)).hom).mapDerivedCategory ⋙ Lg w (ptEq sq w)).map u ≫
        ((derivedStalkSourceIso w (ptEq sq w)).inv.app K₂ ≫
          (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
            (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
              f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) K₂) ≫
          (derivedStalkTargetIso w).hom.app K₂) =
      ((derivedStalkSourceIso w (ptEq sq w)).inv.app K₁ ≫
          (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
            (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
              f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) K₁) ≫
          (derivedStalkTargetIso w).hom.app K₁) ≫
        (AlgebraicGeometry.derivedStalkFunctor (g w) ⋙ Lh w ⋙
          (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategory).map u :=
  naturalityChase _ _ _ _ _ _ _ _ _ _
    ((derivedStalkSourceIso w (ptEq sq w)).inv.naturality u)
    (mapNaturality (AlgebraicGeometry.derivedStalkFunctor (i' w)) _ _ _ _
      ((derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
        f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)).naturality u))
    ((derivedStalkTargetIso w).hom.naturality u)

/-- `DerivedStalkBaseChangeEqQKFlat` implies the open equality `DerivedStalkBaseChangeEq`. -/
private theorem derivedStalkBaseChangeEq_of_Q_kFlat_aux (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (h : DerivedStalkBaseChangeEqQKFlat sq) :
    DerivedStalkBaseChangeEq sq := by
  have := isClosedImmersion_of_isPullback sq
  intro w K
  obtain ⟨P, s, hP, -, hs, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Z.toSheafedSpace
      (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map s) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hs
  have uIso : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  exact transferEq _ _ _ _ _ _
    ((Functor.mapIso (AlgebraicGeometry.derivedStalkFunctor (g w) ⋙
      (ModuleCat.restrictScalars.{u, u, u}
        (i.stalkMap (g w)).hom).mapDerivedCategory ⋙ Lg w (ptEq sq w)) uIso).isIso_hom)
    (derivedStalkBaseChange_lhs_naturality sq w uIso.hom)
    ((stalkComparison sq w (ptEq sq w)).naturality
      ((AlgebraicGeometry.derivedStalkFunctor (g w)).map uIso.hom))
    (derivedStalkBaseChangeEq_app_Q_of_at sq w P (h w P hP) hP)

open Stacks.Cohomology.DerivedBaseChange in
/-- `DerivedStalkBaseChangeEqQ` implies the open equality `DerivedStalkBaseChangeEq` of the stalk
diagram. -/
theorem derivedStalkBaseChangeEq_of_Q (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (h : DerivedStalkBaseChangeEqQ sq) :
    DerivedStalkBaseChangeEq sq :=
  derivedStalkBaseChangeEq_of_Q_kFlat_aux sq fun w P _ => h w P

open Stacks.Cohomology.DerivedBaseChange in
/-- Stacks 0E23 at the level of functors, assuming `DerivedStalkBaseChangeEqQ`: if `i` and
`f` are Tor-independent, the derived base change square is an isomorphism. -/
theorem isIso_derivedBaseChangeSquare_of_Q (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (h : DerivedStalkBaseChangeEqQ sq) :
    IsIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)) :=
  isIso_derivedBaseChangeSquare_of_eq sq htor (derivedStalkBaseChangeEq_of_Q sq h)

open Stacks.Cohomology.DerivedBaseChange in
/-- `DerivedStalkBaseChangeEqQKFlat` implies the open equality `DerivedStalkBaseChangeEq` of the
stalk diagram. -/
theorem derivedStalkBaseChangeEq_of_Q_kFlat (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (h : DerivedStalkBaseChangeEqQKFlat sq) :
    DerivedStalkBaseChangeEq sq :=
  derivedStalkBaseChangeEq_of_Q_kFlat_aux sq h

open Stacks.Cohomology.DerivedBaseChange in
/-- The open equality `DerivedStalkBaseChangeEq` of the stalk diagram implies
`DerivedStalkBaseChangeEqQ`. -/
theorem derivedStalkBaseChangeEqQ_of_eq (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (heq : DerivedStalkBaseChangeEq sq) :
    DerivedStalkBaseChangeEqQ sq := by
  have := isClosedImmersion_of_isPullback sq
  intro w P
  exact qEqChase _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedStalkTargetIso_hom_app_Q_comp_comparison (i' := i') (g := g) w P)
    (derivedStalkSourceIso_hom_app_Q_comp_alphaG w (ptEq sq w) P)
    ((derivedStalkSourceIso w (ptEq sq w)).hom_inv_id_app (DerivedCategory.Q.obj P))
    (stalkComparison_app_derivedStalk_comp_counit sq w (ptEq sq w) P)
    (heq w (DerivedCategory.Q.obj P))

open Stacks.Cohomology.DerivedBaseChange in
/-- `DerivedStalkBaseChangeEqQKFlat` implies `DerivedStalkBaseChangeEqQ`. -/
theorem derivedStalkBaseChangeEqQ_of_kFlat (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (h : DerivedStalkBaseChangeEqQKFlat sq) :
    DerivedStalkBaseChangeEqQ sq :=
  derivedStalkBaseChangeEqQ_of_eq sq (derivedStalkBaseChangeEq_of_Q_kFlat sq h)

open Stacks.Cohomology.DerivedBaseChange in
/-- Stacks 0E23 at the level of functors, assuming `DerivedStalkBaseChangeEqQKFlat`: if `i`
and `f` are Tor-independent, the derived base change square is an isomorphism. -/
theorem isIso_derivedBaseChangeSquare_of_Q_kFlat (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (h : DerivedStalkBaseChangeEqQKFlat sq) :
    IsIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)) :=
  isIso_derivedBaseChangeSquare_of_eq sq htor (derivedStalkBaseChangeEq_of_Q_kFlat sq h)

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end

module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk

/-!
# Computing the derived stalk comparison at a complex that is not K-flat

Let `f : X ⟶ Y` be a morphism of schemes and `x : X`.
`AlgebraicGeometry.derivedPullbackStalkIso` is an isomorphism of functors on the whole unbounded
derived category of `𝒪_Y`-modules, so it is invertible at every object; what is hard is to say
*what* it is at a given object.  Its characterizing equation
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` holds at every cochain complex `P`,
but it determines the isomorphism only when the comparison it is composed with is a
monomorphism, and that comparison — derived extension of scalars against termwise extension of
scalars, at the stalk complex of `P` — is known to be invertible only for a K-flat `P`.  A
pushforward `i_* C` along a closed immersion is never K-flat, so the equation alone does not
compute the isomorphism there.

This file turns the equation into a determination statement and then transports it off the
K-flat class.  A complex `P` which is not K-flat receives a quasi-isomorphism `s : W ⟶ P` from a
K-flat `W` (Stacks 06YS, `Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution`);
`DerivedCategory.Q` inverts `s`, and the isomorphism is natural, so the determination at `W`
transports along `s` to a determination at `P` with no hypothesis on `P` at all.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isIso_derivedStalkExtensionComparison`: the comparison that
  `derivedPullbackStalkIso_comp_comparison` composes with is invertible as soon as the *stalk*
  complex of `P` at `f x` is K-flat.
* `AlgebraicGeometry.isIso_derivedStalkExtensionComparison_of_kFlat`: the same under K-flatness
  of `P` itself, which is the hypothesis a resolution supplies.
* `AlgebraicGeometry.derivedPullbackStalkIso_hom_app_eq_of_mono`: **the characterization at one
  complex.**  A morphism satisfying the equation of
  `derivedPullbackStalkIso_comp_comparison` at `P` *is* `derivedPullbackStalkIso` at `P`, as soon
  as the comparison is a monomorphism.
* `AlgebraicGeometry.derivedPullbackStalkIso_hom_app_eq_of_kFlatResolution`: **the
  characterization at an arbitrary complex.**  For *any* `P`, a morphism at `P` is
  `derivedPullbackStalkIso` at `P` as soon as it is carried by a quasi-isomorphism `W ⟶ P` from a
  morphism satisfying the equation at a K-flat `W`.  There is no hypothesis on `P`.

## Implementation notes

*Why a monomorphism and not an isomorphism.*  Determination needs only right cancellation, so
`derivedPullbackStalkIso_hom_app_eq_of_mono` takes `Mono`; the two invertibility lemmas above
are the suppliers of that hypothesis, and are stated separately because the sharp one asks for
K-flatness of the stalk complex only.  That is strictly weaker than K-flatness of `P`: off the
image of a closed immersion `i` the stalk of `i_* C` vanishes, and a zero complex is K-flat.

*Why the transported statement quantifies over a morphism at `W` rather than inverting.*  The
transport of the characterization along a resolution `s : W ⟶ P` is, as a formula,
`inv (F.map (Q.map s)) ≫ (α.app W ≫ inv (β.app W)) ≫ G.map (Q.map s)`, and writing that down
needs the invertibility of the comparison at `W` to be available when the *statement* is
elaborated.  Taking the two morphisms and the two equations as hypotheses says the same thing
with no inverse in sight, and is the form a consumer who computes a candidate for the
isomorphism can actually apply.

*The derived-category instance.*  `AlgebraicGeometry.hasDerivedCategory_ringedSpaceModules` of
`DerivedStalk.lean` is re-attached here with `attribute [local instance]`: the declaration is
public, only its instance attribute is `local`, so each file that wants it says so.  It is
wanted because `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is stated
for the ringed-space spelling of the category of modules.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u w

namespace AlgebraicGeometry

attribute [local instance] hasDerivedCategory_ringedSpaceModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
  [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]

/-! ### Invertibility of the two comparisons -/

omit [HasDerivedCategory.{w} X.Modules] in
/-- **The comparison of `derivedPullbackStalkIso_comp_comparison` is invertible on a K-flat
stalk complex.**  The composite of derived extension of scalars applied to the factorization of
the derived stalk functor with the comparison of derived against termwise extension of scalars
is invertible as soon as the complex of stalks of `P` at `f x` is K-flat over `𝒪_{Y, f x}`.

The first factor is a component of an isomorphism of functors, and the second is invertible on a
K-flat complex by `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`'s field
`comparison_isIso_of_kFlat`.  K-flatness of the stalk complex is strictly weaker than K-flatness
of `P`: a zero stalk complex is K-flat. -/
theorem isIso_derivedStalkExtensionComparison (P : CochainComplex Y.Modules ℤ)
    (hP : CochainComplex.KFlat
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f x)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) :
    IsIso
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).comparison.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have h := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (f.stalkMap x).hom).comparison_isIso_of_kFlat _ hP
  infer_instance

omit [HasDerivedCategory.{w} X.Modules] in
/-- `isIso_derivedStalkExtensionComparison` under K-flatness of `P` itself, which is what a
K-flat resolution of Stacks 06YS supplies.  The stalk of a K-flat complex is K-flat by
`AlgebraicGeometry.kFlat_modulesStalkFunctor`, the stalk criterion of Stacks 06YB. -/
theorem isIso_derivedStalkExtensionComparison_of_kFlat (P : CochainComplex Y.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P) :
    IsIso
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).comparison.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  isIso_derivedStalkExtensionComparison f x P (kFlat_modulesStalkFunctor (f x) P hP)

/-! ### The characterization -/

/-- **The derived stalk comparison is determined at a complex where its comparison is monic.**
A morphism `φ` from the derived stalk of the derived pullback of `P` to derived extension of
scalars of the derived stalk of `P` which satisfies the equation of
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` *is* the component of
`AlgebraicGeometry.derivedPullbackStalkIso` at `P`.

The hypothesis is right cancellation for the comparison, supplied by
`isIso_derivedStalkExtensionComparison`; the content is the equation itself, which holds at
every `P`. -/
theorem derivedPullbackStalkIso_hom_app_eq_of_mono (P : CochainComplex Y.Modules ℤ)
    (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom ⋙ derivedStalkFunctor x).obj (DerivedCategory.Q.obj P) ⟶
        (derivedStalkFunctor (f x) ⋙
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor).obj (DerivedCategory.Q.obj P))
    (hmono : Mono
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).comparison.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (hφ : φ ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).comparison.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (derivedStalkFunctor x).map (pullbackComparisonOnComplex f P) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
            (ComplexShape.up ℤ)).hom.app P)) :
    φ = (derivedPullbackStalkIso f x).hom.app (DerivedCategory.Q.obj P) := by
  have hchar : (derivedPullbackStalkIso f x).hom.app (DerivedCategory.Q.obj P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).comparison.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (derivedStalkFunctor x).map (pullbackComparisonOnComplex f P) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
            (ComplexShape.up ℤ)).hom.app P) :=
    derivedPullbackStalkIso_comp_comparison f x P
  exact hmono.right_cancellation _ _ (hφ.trans hchar.symm)

/-- **The derived stalk comparison, characterized at an arbitrary complex.**  Let `P` be *any*
cochain complex of `𝒪_Y`-modules, `s : W ⟶ P` a quasi-isomorphism from a K-flat complex — one
exists by Stacks 06YS — and `ψ` a morphism at `W` satisfying the equation of
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison`.  Then a morphism `φ` at `P` which
`s` carries `ψ` to is the component of `AlgebraicGeometry.derivedPullbackStalkIso` at `P`.

There is no hypothesis on `P`.  This is what makes the derived stalk comparison computable at a
complex that is not K-flat — a pushforward along a closed immersion, say: `ψ` is pinned down at
`W` by `derivedPullbackStalkIso_hom_app_eq_of_mono`, whose monomorphism hypothesis
`isIso_derivedStalkExtensionComparison_of_kFlat` discharges from the K-flatness of `W`, and the
naturality of the comparison transports that along `s`, which `DerivedCategory.Q` inverts. -/
theorem derivedPullbackStalkIso_hom_app_eq_of_kFlatResolution
    (P W : CochainComplex Y.Modules ℤ) (s : W ⟶ P) [QuasiIso s]
    (hW : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace W)
    (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom ⋙ derivedStalkFunctor x).obj (DerivedCategory.Q.obj P) ⟶
        (derivedStalkFunctor (f x) ⋙
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor).obj (DerivedCategory.Q.obj P))
    (ψ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom ⋙ derivedStalkFunctor x).obj (DerivedCategory.Q.obj W) ⟶
        (derivedStalkFunctor (f x) ⋙
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor).obj (DerivedCategory.Q.obj W))
    (hψ : ψ ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).functor.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapDerivedCategoryFactors.hom.app W) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (f.stalkMap x).hom).comparison.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
            (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) =
      (derivedStalkFunctor x).map (pullbackComparisonOnComplex f W) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
            (ComplexShape.up ℤ)).hom.app W))
    (hφ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom ⋙ derivedStalkFunctor x).map (DerivedCategory.Q.map s) ≫ φ =
      ψ ≫ (derivedStalkFunctor (f x) ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (f.stalkMap x).hom).functor).map (DerivedCategory.Q.map s)) :
    φ = (derivedPullbackStalkIso f x).hom.app (DerivedCategory.Q.obj P) := by
  have hψe : ψ = (derivedPullbackStalkIso f x).hom.app (DerivedCategory.Q.obj W) :=
    derivedPullbackStalkIso_hom_app_eq_of_mono f x W ψ
      (have := isIso_derivedStalkExtensionComparison_of_kFlat f x W hW; inferInstance) hψ
  have hnat := (derivedPullbackStalkIso f x).hom.naturality (DerivedCategory.Q.map s)
  have htrans : ψ ≫ (derivedStalkFunctor (f x) ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (f.stalkMap x).hom).functor).map (DerivedCategory.Q.map s) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom ⋙ derivedStalkFunctor x).map (DerivedCategory.Q.map s) ≫
        (derivedPullbackStalkIso f x).hom.app (DerivedCategory.Q.obj P) := by
    rw [hψe]
    exact hnat.symm
  have hiso : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom ⋙ derivedStalkFunctor x).map (DerivedCategory.Q.map s)) := by
    have hs : IsIso (DerivedCategory.Q.map s) := inferInstance
    exact ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom ⋙ derivedStalkFunctor x).mapIso
        (@asIso _ _ _ _ _ hs)).isIso_hom
  exact (cancel_epi _).1 (hφ.trans htrans)

end AlgebraicGeometry

end

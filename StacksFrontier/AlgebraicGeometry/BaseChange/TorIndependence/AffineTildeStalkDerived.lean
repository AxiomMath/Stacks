module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineTildeStalkCompatibility
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkNatTrans
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompGeneral

/-!
# The affine case of the Tag 0098 / Tag 08DW stalk coherence: the two routes, and the reduction

Let `c : A ⟶ A'` be a homomorphism of commutative rings and `y` a point of `Spec A'` with image
`x` in `Spec A`. The derived stalk at `y` of the derived pullback along `Spec c` of a derived
sheafification can be computed in two ways, and this file names both as morphisms of functors on
`D(A)` and reduces their equality to one equation on the K-flat class.

* `AlgebraicGeometry.derivedAffineTildeStalkLeft` goes through `Spec A'`: the affine comparison
  square of Stacks 08DW part (2), then `AlgebraicGeometry.derivedTildeStalkIso` at `A'` read
  backwards, then the composition isomorphism for derived extension of scalars along `c` and the
  germ map of `A'`.
* `AlgebraicGeometry.derivedAffineTildeStalkRight` goes through `Spec A`: the derived stalk
  formula of Stacks 0098 for `Spec c`, then `derivedTildeStalkIso` at `A` read backwards, then
  the composition isomorphism along the germ map of `A` and the germ map of `Spec c` at `y`,
  transported along `AlgebraicGeometry.specGermRingHom_stalkMap`.

Both are morphisms `L~ ⋙ L(Spec c)^* ⋙ (−)_y ⟶ − ⊗ᴸ_A 𝒪_{Spec A',y}`.

## Main definitions

* `AlgebraicGeometry.derivedAffineTildeStalkLeft` and
  `AlgebraicGeometry.derivedAffineTildeStalkRight`: the two routes.

## Main results

* `AlgebraicGeometry.derivedAffineTildeStalk_eq_of_kFlat`: the two routes agree as soon as they
  agree on the image of every K-flat complex of `A`-modules.
* `AlgebraicGeometry.derivedAffineTildeStalk_eq_of_comparison`: the two routes agree as soon as
  their composites with the comparison of
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` along the composite germ
  map agree on every K-flat complex.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedExtensionScalarsComp

universe u

namespace AlgebraicGeometry

open Stacks.ModuleSkyscraper

variable {A A' : CommRingCat.{u}} (c : A ⟶ A') (y : (Spec A').carrier)

/-- **The first route: through `Spec A'`.** The derived stalk at `y` of `L(Spec c)^*(M̃^•)`,
computed by the affine comparison square of Stacks 08DW part (2) and then by the derived stalk
formula of Stacks 01HV at `A'`, as a morphism of functors on `D(A)` into derived extension of
scalars along `A ⟶ 𝒪_{Spec A',y}`. -/
public def derivedAffineTildeStalkLeft :
    (tilde.functor A).mapDerivedCategory ⋙
        (Stacks.Duality.derivedPullback (Spec.map c) ⋙ derivedStalkFunctor y) ⟶
      (totalDerivedExtensionScalars.{u, u, u} ((specGermRingHom A' y).comp c.hom)).functor :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (affinePullbackComparison A A' c).hom (derivedStalkFunctor y) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, u} c.hom).functor
      (derivedTildeStalkIso A' y).inv ≫
    (derivedExtensionScalarsCompIsoGeneral c.hom (specGermRingHom A' y)).hom

/-- **The second route: through `Spec A`.** The derived stalk at `y` of `L(Spec c)^*(M̃^•)`,
computed by the derived stalk formula of Stacks 0098 for `Spec c` and then by Stacks 01HV at `A`,
with the two extensions of scalars merged and transported along
`AlgebraicGeometry.specGermRingHom_stalkMap`. -/
public def derivedAffineTildeStalkRight :
    (tilde.functor A).mapDerivedCategory ⋙
        (Stacks.Duality.derivedPullback (Spec.map c) ⋙ derivedStalkFunctor y) ⟶
      (totalDerivedExtensionScalars.{u, u, u} ((specGermRingHom A' y).comp c.hom)).functor :=
  Functor.whiskerLeft (tilde.functor A).mapDerivedCategory
      (derivedPullbackStalkIso (Spec.map c) y).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedTildeStalkIso A ((Spec.map c).base y)).inv
      (totalDerivedExtensionScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).functor ≫
    (derivedExtensionScalarsCompIsoGeneral (specGermRingHom A ((Spec.map c).base y))
      ((Spec.map c).stalkMap y).hom).hom ≫
    eqToHom (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
      (specGermRingHom_stalkMap c y))

/-- **The two routes agree as soon as they agree on the K-flat complexes.** -/
public theorem derivedAffineTildeStalk_eq_of_kFlat
    (h : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ, CochainComplex.KFlat.{u, u} P →
      (derivedAffineTildeStalkLeft c y).app (DerivedCategory.Q.obj P) =
        (derivedAffineTildeStalkRight c y).app (DerivedCategory.Q.obj P)) :
    derivedAffineTildeStalkLeft c y = derivedAffineTildeStalkRight c y := by
  refine StacksDraft.LeftResolutions.natTrans_eq_of_left_resolutions DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (fun P => CochainComplex.KFlat.{u, u} P) ?_ _ _ h
  intro K
  obtain ⟨P, p, hP, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} K
  exact ⟨P, hP, p, hp⟩

/-- **The two routes agree as soon as their composites with the derived-functor comparison
agree** on every K-flat complex: the comparison of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` along the composite germ map
`A ⟶ 𝒪_{Spec A',y}` with degreewise extension of scalars. -/
public theorem derivedAffineTildeStalk_eq_of_comparison
    (h : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ, CochainComplex.KFlat.{u, u} P →
      (derivedAffineTildeStalkLeft c y).app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u}
            ((specGermRingHom A' y).comp c.hom)).comparison.app P =
        (derivedAffineTildeStalkRight c y).app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u}
            ((specGermRingHom A' y).comp c.hom)).comparison.app P) :
    derivedAffineTildeStalkLeft c y = derivedAffineTildeStalkRight c y := by
  refine derivedAffineTildeStalk_eq_of_kFlat c y fun P hP => ?_
  have := (totalDerivedExtensionScalars.{u, u, u}
    ((specGermRingHom A' y).comp c.hom)).comparison_isIso_of_kFlat P hP
  exact (cancel_mono ((totalDerivedExtensionScalars.{u, u, u}
    ((specGermRingHom A' y).comp c.hom)).comparison.app P)).mp (h P hP)

end AlgebraicGeometry

end

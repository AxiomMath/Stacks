module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkNatTrans
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional

/-!
# The derived stalk of an iterated derived pullback

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and `x` a point of `X`.  Stacks 0098 in
its derived form, `AlgebraicGeometry.derivedPullbackStalkIso`, computes the derived stalk of a
derived pullback:

`(Lf^* K)_x  ≅  𝒪_{X,x} ⊗ᴸ_{𝒪_{Y,f x}} K_{f x}`.

Iterating it along `g` and then `f` computes the derived stalk at `x` of `Lg^* ⋙ Lf^*`.  Applying
it once to `L(f ≫ g)^*` computes the derived stalk of the single derived pullback along the
composite.  The composition formula of Tag 0D5S,
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, identifies the two derived
pullbacks; the *coherence* that the two stalk computations agree through that identification is
what this file is about.

That coherence is what a consumer of the derived base change map of Stacks 08HY needs.
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint` describes that map as the
transpose of a composite of two Tag 0D5S composition isomorphisms with the derived pullback of a
counit; so computing its derived stalk requires knowing how the derived stalk formula interacts
with a Tag 0D5S composition isomorphism, and nothing in the development said.

## Main definitions

* `AlgebraicGeometry.derivedStalkExtensionCompIso`: derived extension of scalars along the germ
  map of `g` at `f x`, then along the germ map of `f` at `x`, is derived extension of scalars
  along the germ map of `f ≫ g` at `x`.  This is
  `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso` at the germ maps,
  transported along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`.
* `AlgebraicGeometry.derivedPullbackStalkCompIso`: **the two-step derived stalk computation** of
  an iterated derived pullback, `Lg^* ⋙ Lf^* ⋙ (−)_x ≅ (−)_{g (f x)} ⋙ (𝒪_{X,x} ⊗ᴸ −)`.

## Main results

* `AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat`: **the coherence, reduced to one
  equation at K-flat complexes.**  The two stalk computations agree — as isomorphisms of functors
  on the whole unbounded derived category — as soon as a single equation between the two
  comparisons holds at the K-flat complexes.
* `AlgebraicGeometry.derivedPullbackStalkCompIso_hom_eq_of_kFlat` and
  `AlgebraicGeometry.derivedPullbackStalkCompIso_eq_of_kFlat`: the same conclusion as an equation
  of morphisms of functors and as an equality of isomorphisms, which is the form a consumer of
  Stacks 08HY applies.

## Implementation notes

*What the reduction leaves.*  The hypothesis of
`derivedPullbackStalkIso_comp_of_kFlat` is an equation at a K-flat complex `P` between
morphisms built from `AlgebraicGeometry.pullbackComparisonOnComplex`, the comparison of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` and the *underived* stalk
formula `Stacks.ModuleSkyscraper.pullbackStalkIso`.  At a K-flat complex every comparison in
sight is invertible, so that equation is a statement about degreewise data: it is the
compatibility of the underived stalk formula of Stacks 0098 with composition, together with the
compatibility of `derivedPullbackCompIsoCanonical` with
`AlgebraicGeometry.pullbackComparisonOnComplex`.  Both are statements about explicit module maps
rather than about derived functors; that is the point of the reduction.  Both are available now —
`Stacks.ModuleSkyscraper.pullbackStalkIso_comp_app` and
`AlgebraicGeometry.pullbackComparisonOnComplex_comp` — and
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/DerivedStalkCompositionAssembly.lean`
assembles them into the hypothesis, so the three conclusions below also hold unconditionally:
see `AlgebraicGeometry.derivedPullbackStalkIso_comp`,
`AlgebraicGeometry.derivedPullbackStalkCompIso_hom_eq` and
`AlgebraicGeometry.derivedPullbackStalkCompIso_eq`.

*Why the hypothesis carries the inverse of the whiskered composition isomorphism, rather than its
`hom` on the other side of the equation.*  The two are equivalent, by cancelling an isomorphism;
but cancelling it means rewriting with `CategoryTheory.Functor.map_comp` inside a component of a
composite of morphisms of functors, and that rewrite does not fire here.  The two spellings of
the category of modules on a scheme carry two `Category` instances which are definitionally but
not *reducibly* equal, and `rw` matches at reducible transparency; forcing it
through `slice_lhs` instead exhausts the heartbeat budget in `isDefEq`.  With the inverse on the
hypothesis the reduction is a single application of
`AlgebraicGeometry.derivedPullbackStalkIso_hom_eq_of_kFlat_of_iso` and nothing has to be
rewritten.  The conclusion is then moved across by `CategoryTheory.Iso.inv_comp_eq` and
`CategoryTheory.Iso.ext`, which touch no components.

*Why the hypothesis is at K-flat complexes and not at all complexes.*  K-flatness is what a
resolution of Stacks 06YS supplies, and the invertibility of the extension-of-scalars comparison
which the cancellation needs follows from it; asking for the equation everywhere would be a
strictly stronger hypothesis for the same conclusion.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open StacksDraft.DerivedExtensionScalarsComp

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)

/-- **Derived extension of scalars along the germ maps composes.**  Extending scalars along the
germ map of `g` at `f x` and then along the germ map of `f` at `x` is extending scalars along the
germ map of `f ≫ g` at `x`.

This is `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso` at the two germ
maps, transported along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`. -/
def derivedStalkExtensionCompIso :
    (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap (f x)).hom).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor :=
  derivedExtensionScalarsCompIso (g.stalkMap (f x)).hom (f.stalkMap x).hom ≪≫
    eqToIso (congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor)
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x).symm)

/-- **The two-step derived stalk computation of an iterated derived pullback.**  The derived stalk
at `x` of `Lg^*` followed by `Lf^*` is the derived stalk at `g (f x)`, extended along the germ map
of `f ≫ g` at `x`.

The three steps are `AlgebraicGeometry.derivedPullbackStalkIso` for `f` at `x`, the same for `g`
at `f x`, and `derivedStalkExtensionCompIso` to merge the two extensions of scalars. -/
def derivedPullbackStalkCompIso :
    derivedPullback g.toLRSHom.toShHom ⋙ derivedPullback f.toLRSHom.toShHom ⋙
        derivedStalkFunctor x ≅
      derivedStalkFunctor (g (f x)) ⋙
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor :=
  Functor.isoWhiskerLeft _ (derivedPullbackStalkIso f x) ≪≫
    Functor.isoWhiskerRight (derivedPullbackStalkIso g (f x))
      (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor ≪≫
    Functor.isoWhiskerLeft _ (derivedStalkExtensionCompIso f g x)

/-- **The coherence of the derived stalk formula with the composition formula of Tag 0D5S,
reduced to one equation on the K-flat class.**

Suppose that at every K-flat complex `P` of `𝒪_Z`-modules the two-step stalk computation
`derivedPullbackStalkCompIso`, read backwards along the Tag 0D5S composition isomorphism and
composed with the comparison of derived against degreewise extension of scalars along the germ
map of `f ≫ g`, is the comparison of the derived pullback along `f ≫ g` followed by the underived
stalk formula of Stacks 0098 — that is, that it satisfies the equation which characterizes
`AlgebraicGeometry.derivedPullbackStalkIso` for `f ≫ g`.  Then the two stalk computations agree
as isomorphisms of functors on the whole unbounded derived category.

The hypothesis is a statement about degreewise data; see the implementation notes. -/
theorem derivedPullbackStalkIso_comp_of_kFlat
    (hcomp : ∀ P : CochainComplex Z.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P →
      (derivedStalkFunctor x).map
            ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
              g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
          (derivedPullbackStalkCompIso f g x).hom.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso (f ≫ g) x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    (Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x)).inv ≫ (derivedPullbackStalkCompIso f g x).hom =
      (derivedPullbackStalkIso (f ≫ g) x).hom :=
  derivedPullbackStalkIso_hom_eq_of_kFlat_of_iso (f ≫ g) x _ _ hcomp

/-- **The coherence, as an equality of isomorphisms.**  Under the hypothesis of
`derivedPullbackStalkIso_comp_of_kFlat`, the two-step derived stalk computation of an iterated
derived pullback is the Tag 0D5S composition isomorphism followed by the one-step computation.

This is the form a consumer reasoning about the derived base change map of Stacks 08HY applies:
the composition isomorphism appears there in the adjoint description of the map, and this says
what the derived stalk does to it. -/
theorem derivedPullbackStalkCompIso_hom_eq_of_kFlat
    (hcomp : ∀ P : CochainComplex Z.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P →
      (derivedStalkFunctor x).map
            ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
              g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
          (derivedPullbackStalkCompIso f g x).hom.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso (f ≫ g) x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    (derivedPullbackStalkCompIso f g x).hom =
      (Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x)).hom ≫ (derivedPullbackStalkIso (f ≫ g) x).hom :=
  (Iso.inv_comp_eq _).1 (derivedPullbackStalkIso_comp_of_kFlat f g x hcomp)

/-- **The coherence, as an isomorphism of isomorphisms.**  Under the same hypothesis the two-step
derived stalk computation *is* the Tag 0D5S composition isomorphism composed with the one-step
computation, as isomorphisms of functors. -/
theorem derivedPullbackStalkCompIso_eq_of_kFlat
    (hcomp : ∀ P : CochainComplex Z.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P →
      (derivedStalkFunctor x).map
            ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
              g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
          (derivedPullbackStalkCompIso f g x).hom.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso (f ≫ g) x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    derivedPullbackStalkCompIso f g x =
      Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x) ≪≫ derivedPullbackStalkIso (f ≫ g) x :=
  Iso.ext (derivedPullbackStalkCompIso_hom_eq_of_kFlat f g x hcomp)

end AlgebraicGeometry

end

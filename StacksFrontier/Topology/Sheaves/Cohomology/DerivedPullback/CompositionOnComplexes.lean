module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# The composition formula of Tag 0D5S, read on a single complex

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`Stacks.DerivedPullback.Composition.derivedPullbackCompComparisonCanonical` is the comparison
`Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*` of Tag 0D5S, and
`derivedPullbackCompIsoCanonical_hom_app_comp_comparison` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/CompositionUnconditional.lean`
already says how it interacts with the comparisons `Lf^* ⟶ K(f^*)` of Tag 06YJ — but on the
*homotopy* category, against the comparison at an object of `K(𝒪_Z)`.

A consumer of the derived stalk formula meets those comparisons in a different spelling.
`AlgebraicGeometry.pullbackComparisonOnComplex` is the comparison evaluated at a *cochain
complex*, through the identification `DerivedCategory.quotientCompQhIso` of the homotopy-category
quotient with `DerivedCategory.Q`, and it is that map which characterizes
`AlgebraicGeometry.derivedPullbackStalkIso`.  Nothing related the composition formula to it, so
the derived stalk of an iterated derived pullback could not be computed; the compatibility is one
half of the hypothesis `hcomp` of
`AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat`, the other half being the composition
compatibility of the underived stalk formula of Tag 0098.

This file supplies the missing compatibility.  It is proved in two steps.  The first is an
identity on homotopy categories relating `CategoryTheory.Functor.mapHomotopyCategoryCompIso` to
the three `CategoryTheory.Functor.mapHomotopyCategoryFactors` that surround it; the second
transports the homotopy-category statement onto complexes, which is a chain of naturality squares
and one cancellation.

## Main definitions

* `Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex`: the comparison
  `Lf^* (Q P) ⟶ Q (f^* P)` at a cochain complex, for a morphism of ringed spaces.  This is
  `AlgebraicGeometry.pullbackComparisonOnComplex` with the scheme hypothesis dropped; the two
  agree by `AlgebraicGeometry.pullbackComparisonOnComplex_eq`.

## Main results

* `StacksDraft.MapHomotopyCategory.mapHomotopyCategoryCompIso_hom_app_comp_factors`: for additive
  functors related by `e : F ⋙ G ≅ H`, the composition isomorphism on homotopy categories,
  followed by the factorization for `H`, is the two factorizations for `F` and `G` followed by the
  quotient of the composition isomorphism on complexes.
* `Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_comp`: **the
  compatibility.**  The comparison of Tag 0D5S, followed by the comparison on complexes for
  `f ≫ g`, is the comparison on complexes for `g`, then for `f`, then the degreewise
  pullback-composition isomorphism.
* `AlgebraicGeometry.pullbackComparisonOnComplex_comp`: the same for morphisms of schemes, which
  is the form the derived stalk formula consumes.

## Implementation notes

*Why the homotopy-category identity is proved by `change`.*  All three components of
`mapHomotopyCategoryFactors` are identity morphisms, because `mapHomotopyCategoryFactors` is
`CategoryTheory.Quotient.lift.isLift`, whose components are `Iso.refl`.  Rewriting with that fact
is what fails: the source and target of such a component are
`(HomotopyCategory.quotient _ c ⋙ F.mapHomotopyCategory c).obj K` and
`(F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient _ c).obj K`, which are equal only after
unfolding `CategoryTheory.Quotient.lift`, so substituting an identity morphism for the component
produces a term that is not type-correct at the implicit transparency at which `rw` and `simp`
check their results, and the rewrite is rejected.  Changing the *statement* instead avoids the
problem: each component, and the component of the composition isomorphism, is definitionally the
quotient functor applied to an explicit morphism of complexes, and `change` checks that at default
transparency.  After it the goal is an identity between images under one functor and `simp`
closes it.

*Why the comparison on complexes is restated for ringed spaces.*
`AlgebraicGeometry.pullbackComparisonOnComplex` is stated for a morphism of schemes, while Tag
0D5S and every map in its proof live on ringed spaces.  Proving the compatibility for schemes
directly would mean rewriting across the two spellings of the category of modules on a scheme,
which carry two `Category` instances that are definitionally but not reducibly equal, so `rw`
does not fire.  Proved on ringed spaces the statement is about one instance throughout, and the
scheme-level corollary is obtained in term mode, where the conversion check runs at default
transparency.

*Why the proof is cut into pieces and the rewrites are made inside `conv`.*  The goal is a
composite of eight morphisms between objects of a derived category, and every `rw` on it pays for
one traversal; the whole compatibility in a single declaration with one `rw` chain costs about
twice the default heartbeat budget.  Restricting each rewrite to the side it acts on, and moving
the two steps that are themselves rewriting — the cancellation of `quotientCompQhIso` against its
inverse, and the image under `DerivedCategory.Qh` of the homotopy-category identity — into their
own declarations brings it to about seventy per cent of the budget.  The cancellation is phrased
with `CategoryTheory.Iso.hom_inv_id_assoc` rather than by rewriting with
`CategoryTheory.Functor.map_id`, because a goal of this size costs more than the whole budget in
`CategoryTheory.Category.id_comp` alone.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace StacksDraft.MapHomotopyCategory

variable {ι : Type*} {V W W' : Type*} [Category* V] [Category* W] [Category* W']
  [Preadditive V] [Preadditive W] [Preadditive W']

/-- **The composition isomorphism on homotopy categories, against the three factorizations.**
Let `e : F ⋙ G ≅ H` be an isomorphism of additive functors.  On the image of a complex `K` under
the homotopy-category quotient, the composition isomorphism
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` followed by the factorization of
`H.mapHomotopyCategory` agrees with `G.mapHomotopyCategory` of the factorization for `F`, then the
factorization for `G`, then the quotient of the composition isomorphism on complexes.

Every morphism named here except the last is an identity; see the implementation notes for why the
statement is nonetheless not closed by `rfl`. -/
theorem mapHomotopyCategoryCompIso_hom_app_comp_factors {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι)
    (K : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c).hom.app ((HomotopyCategory.quotient V c).obj K) ≫
        (H.mapHomotopyCategoryFactors c).hom.app K =
      (G.mapHomotopyCategory c).map ((F.mapHomotopyCategoryFactors c).hom.app K) ≫
        (G.mapHomotopyCategoryFactors c).hom.app ((F.mapHomologicalComplex c).obj K) ≫
        (HomotopyCategory.quotient W' c).map
          ((Functor.mapHomologicalComplexCompIso e c).hom.app K) := by
  change (HomotopyCategory.quotient W' c).map
        ((Functor.mapHomologicalComplexCompIso e c).hom.app K) ≫
      (HomotopyCategory.quotient W' c).map (𝟙 ((H.mapHomologicalComplex c).obj K)) =
    (HomotopyCategory.quotient W' c).map
        ((G.mapHomologicalComplex c).map (𝟙 ((F.mapHomologicalComplex c).obj K))) ≫
      (HomotopyCategory.quotient W' c).map
        (𝟙 ((G.mapHomologicalComplex c).obj ((F.mapHomologicalComplex c).obj K))) ≫
      (HomotopyCategory.quotient W' c).map
        ((Functor.mapHomologicalComplexCompIso e c).hom.app K)
  simp

end StacksDraft.MapHomotopyCategory

namespace Stacks.DerivedPullback.Composition

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The comparison of Tag 06YJ at a cochain complex**, for a morphism of ringed spaces: the
derived pullback of `Q P` maps to `Q` of the degreewise pullback of `P`.

The comparison itself lives on the homotopy category, so the map is the derived pullback of the
identification `DerivedCategory.quotientCompQhIso`, then the comparison at the quotient of `P`,
then the factorization of degreewise pullback through the quotient, then that identification
again.  For a morphism of schemes this is `AlgebraicGeometry.pullbackComparisonOnComplex`, by
`AlgebraicGeometry.pullbackComparisonOnComplex_eq`. -/
def derivedPullbackComparisonOnComplex {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (P : CochainComplex (ModuleSheaves Y) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (derivedPullback f).map ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).inv.app P) ≫
    (derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.app
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The pullback-composition isomorphism on homotopy categories, against the factorizations of
degreewise pullback.**  This is
`StacksDraft.MapHomotopyCategory.mapHomotopyCategoryCompIso_hom_app_comp_factors` at
`Stacks.DerivedPullback.Composition.modulePullbackComp`, whose isomorphism on homotopy categories
is `Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso`. -/
theorem pullbackOnHomotopyCompIso_hom_app_comp_factors
    (P : CochainComplex (ModuleSheaves Z) ℤ) :
    (pullbackOnHomotopyCompIso f g).hom.app
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P) ≫
        ((modulePullback (f ≫ g)).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P =
      ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
        ((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
              (ComplexShape.up ℤ)).hom.app P) :=
  StacksDraft.MapHomotopyCategory.mapHomotopyCategoryCompIso_hom_app_comp_factors
    (modulePullbackComp f g) (ComplexShape.up ℤ) P

/-- `pullbackOnHomotopyCompIso_hom_app_comp_factors` in the derived category, with each factor
localized separately.  It is recorded on its own because deriving it inside the proof of
`derivedPullbackComparisonOnComplex_comp` costs more heartbeats than that proof has left. -/
theorem Qh_map_pullbackOnHomotopyCompIso_hom_app_comp_factors
    (P : CochainComplex (ModuleSheaves Z) ℤ) :
    DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (((modulePullback (f ≫ g)).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) =
      DerivedCategory.Qh.map
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
            (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P)) ≫
        DerivedCategory.Qh.map
            (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
              (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
                (ComplexShape.up ℤ)).hom.app P)) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Qh.map
    (pullbackOnHomotopyCompIso_hom_app_comp_factors f g P)

/-- The derived pullback along `f` of `DerivedCategory.quotientCompQhIso` cancels the derived
pullback of its inverse.  Phrased with a trailing morphism, so that using it is one rewrite and
no identity morphism is ever substituted into the goal; see the implementation notes. -/
theorem derivedPullback_map_quotientCompQhIso_hom_inv_assoc
    (P : CochainComplex (ModuleSheaves Z) ℤ) {T : DerivedCategory (ModuleSheaves X)}
    (h : (derivedPullback f).obj
      ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).obj
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶ T) :
    (derivedPullback f).map ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).hom.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).inv.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫ h = h :=
  Iso.hom_inv_id_assoc ((derivedPullback f).mapIso
    ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).app
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) h

open Stacks.Cohomology.DerivedPushforwardComposition in
/-- **The composition formula of Tag 0D5S, on a complex.**  The comparison
`Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*`, followed by the comparison on complexes for `f ≫ g`, is the derived
pullback along `f` of the comparison on complexes for `g`, then the comparison on complexes for
`f`, then the degreewise pullback-composition isomorphism of
`Stacks.DerivedPullback.Composition.modulePullbackComp`.

This is the compatibility of the composition formula with
`AlgebraicGeometry.pullbackComparisonOnComplex` that the derived stalk of an iterated derived
pullback needs.  The proof is `derivedPullbackCompIsoCanonical_hom_app_comp_comparison` carried
from the homotopy category onto complexes: one naturality square for the comparison of Tag 0D5S,
one for the comparison of Tag 06YJ along `f`, one for `DerivedCategory.quotientCompQhIso`, the
cancellation `derivedPullback_map_quotientCompQhIso_hom_inv_assoc`, and
`Qh_map_pullbackOnHomotopyCompIso_hom_app_comp_factors`. -/
theorem derivedPullbackComparisonOnComplex_comp (P : CochainComplex (ModuleSheaves Z) ℤ) :
    (derivedPullbackCompComparisonCanonical f g).app (DerivedCategory.Q.obj P) ≫
        derivedPullbackComparisonOnComplex (f ≫ g) P =
      (derivedPullback f).map (derivedPullbackComparisonOnComplex g P) ≫
        derivedPullbackComparisonOnComplex f
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
            (ComplexShape.up ℤ)).hom.app P) := by
  have hfac : (derivedPullbackCompComparisonCanonical f g).app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackComparison (f ≫ g)).app
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P) =
      (derivedPullback f).map ((derivedPullbackComparison g).app
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackComparison f).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app
            ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) :=
    derivedPullbackCompIsoCanonical_hom_app_comp_comparison f g _
  have hnatf : (derivedPullback f).map (DerivedCategory.Qh.map
          (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ)).obj
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      (derivedPullbackComparison f).app
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
            (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P)) :=
    (derivedPullbackComparison f).naturality _
  have hnatA : (derivedPullback f).map ((derivedPullback g).map
          ((DerivedCategory.quotientCompQhIso (ModuleSheaves Z)).inv.app P)) ≫
        (derivedPullbackCompComparisonCanonical f g).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) =
      (derivedPullbackCompComparisonCanonical f g).app (DerivedCategory.Q.obj P) ≫
        (derivedPullback (f ≫ g)).map
          ((DerivedCategory.quotientCompQhIso (ModuleSheaves Z)).inv.app P) :=
    (derivedPullbackCompComparisonCanonical f g).naturality _
  have hnatQ : DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
              (ComplexShape.up ℤ)).hom.app P)) ≫
        (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.app
          (((modulePullback (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.app
          (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
          (ComplexShape.up ℤ)).hom.app P) :=
    (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.naturality _
  unfold derivedPullbackComparisonOnComplex
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  conv_rhs => rw [derivedPullback_map_quotientCompQhIso_hom_inv_assoc f g P,
    reassoc_of% hnatf, ← hnatQ]
  conv_lhs => rw [← reassoc_of% hnatA, reassoc_of% hfac,
    reassoc_of% (Qh_map_pullbackOnHomotopyCompIso_hom_app_comp_factors f g P)]

end Stacks.DerivedPullback.Composition

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The scheme-level comparison on a complex is the ringed-space one.**  Both sides are the same
composite: the scheme spelling of the category of modules and the ringed-space spelling are
definitionally equal, and `AlgebraicGeometry.Scheme.Modules.pullback` is degreewise pullback along
the underlying morphism of ringed spaces. -/
theorem pullbackComparisonOnComplex_eq (P : CochainComplex Y.Modules ℤ) :
    pullbackComparisonOnComplex f P =
      Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex
        f.toLRSHom.toShHom P :=
  rfl

/-- **The composition formula of Tag 0D5S against the comparison on complexes, for schemes.**
This is `Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_comp` at the
underlying morphisms of ringed spaces, which is the shape
`AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat` asks for: it rewrites the comparison on
complexes for `f ≫ g` in terms of the two factors. -/
theorem pullbackComparisonOnComplex_comp (P : CochainComplex Z.Modules ℤ) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompComparisonCanonical
          f.toLRSHom.toShHom g.toLRSHom.toShHom).app (DerivedCategory.Q.obj P) ≫
        pullbackComparisonOnComplex (f ≫ g) P =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).map (pullbackComparisonOnComplex g P) ≫
        pullbackComparisonOnComplex f
            (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (Stacks.DerivedPullback.Composition.modulePullbackComp f.toLRSHom.toShHom
                g.toLRSHom.toShHom) (ComplexShape.up ℤ)).hom.app P) :=
  Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_comp
    f.toLRSHom.toShHom g.toLRSHom.toShHom P

end AlgebraicGeometry

end

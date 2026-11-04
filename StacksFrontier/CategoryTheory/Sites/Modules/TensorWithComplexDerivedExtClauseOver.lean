module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClause
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Stacks 0CS6 on cohomology, over the source's base ring

Let `(C, O)` be a ringed site, let `R` be the source's base ring, let `K` be a complex of
`O`-modules and let `(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded
`R`-algebra. The canonical map of Stacks 0CS6 in the source's `D(R)`,

`RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)`,

is `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver`. This file
identifies the two cohomology modules it compares with the `Ext`-groups
`Ext^n_{D(E, d)}(M, N)` and `Ext^n_{D(O)}(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)` and proves the source's second
assertion for it: **that the degree-`n` cohomology of the canonical map in `D(R)` is the map on
`Ext` induced by `- ⊗_E^𝐋 K`**, for every `M`, `N` in `D(E, d)` and every `n`, with no further
hypothesis.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIsoOver`: an exact functor commutes
  with the homology functors of the derived categories.
* `AlgebraicGeometry.RingedSite.homologyForgetEquiv`: the degree-`n` cohomology of an object of
  `D(R)` and of its underlying object of `D(ℤ)` are the same abelian group.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquivOver` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomTargetExtEquivOver`: the source and
  the target of the canonical map in `D(R)`, read on cohomology.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_homology`:
  **the central clause of Stacks 0CS6, in the source's `D(R)`.**

## Implementation notes

*Why this is bookkeeping and not a second proof of the clause.* The forgetful functor of
`R`-modules is exact and faithful, and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_forget` says that
forgetting the `R`-action of the canonical map in `D(R)` returns the `D(ℤ)`-valued
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived`. So the two readings of the
degree-`n` cohomology are one abelian group — that is
`AlgebraicGeometry.RingedSite.homologyForgetEquiv`, the comparison of the homology functors with
an exact functor — and the clause over `R` follows from
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived_homology` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClause` by moving that
comparison across the map, which is its naturality.

*What the two `Ext` readings assert.* They are isomorphisms of abelian groups out of the
degree-`n` cohomology of the `D(R)`-valued source and target. That is what the source asserts on
cohomology: it identifies the two cohomology modules of its map with the `Ext`-groups it
compares, and the content of the clause is which map between them the canonical map induces. No
`R`-linearity of the two identifications is claimed, and none is used.

*The source of the canonical map is the source's own reduced left-hand side, not `RHom(M, N)`.*
Stacks 0CS6 writes its map as `RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)`. The map built here
starts instead at `Q(Hom^•(P_M, P_N))` with `P_M = DifferentialGradedModule.propertyPModel E M`
and `P_N` likewise, which is the left-hand side *after* the substitution the source's own proof
makes: "we may assume `M` and `N` are differential graded `E`-modules with property (P); this does
not change the left hand side of the arrow by Lemma 22.31.3". What is proved here about that
object is exactly the property the source attributes to `RHom(M, N)` — that its degree-`n`
cohomology is `Ext^n_{D(E, d)}(M, N)` — and that is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquivOver` below. So the clause
the tag asserts, the one about cohomology modules, is proved; what is *not* asserted anywhere is
the identification of the two objects **in `D(R)`**, an isomorphism
`RHom(M, N) ≅ Q(Hom^•(P_M, P_N))`.

That identification is [Stacks, Tag 0BYV] followed by [Stacks, Tag 0BYW], and both are in the
library: `DifferentialGraded.Bimodule.derivedPrecomp_isIso`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomPrecompositionIso.lean:134`) replaces the
first argument by a quasi-isomorphic bimodule, and
`DifferentialGradedModule.DerivedHomData.comparisonNatIso`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLeftOrthogonal.lean:258`) identifies
derived Hom out of a property-(P) module with ordinary differential graded Hom. Neither applies
here, because the library's derived Hom is valued in the derived category of a *differential
graded* algebra: `DifferentialGradedModule.DerivedHomData`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHom.lean:101`) carries
`functor : D(B, d) ⥤ D(A, d)` for differential graded `R`-algebras `A`, `B` and an
`(A, B)`-bimodule, whereas the object above lives in Mathlib's `DerivedCategory (ModuleCat R)`.
Three things are missing, and the first makes the statement unformable rather than merely unproved:

* a `BimoduleStructure (DifferentialGradedAlgebra.degreeZero R R) E P_M`, exhibiting `P_M` as an
  `(R, E)`-bimodule in the sense the derived Hom needs. The library's only constructors of a
  `BimoduleStructure` are `DifferentialGradedModule.endomorphismBimoduleStructure`
  (`StacksFrontier/Algebra/DifferentialGraded/Module/EndomorphismBimodule.lean:222`),
  `DifferentialGradedModule.restrictScalarsBimoduleStructure`
  (`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorAlgebraComparison.lean:156`) and
  `DifferentialGradedModule.oppBimoduleStructure`
  (`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleFlip.lean:405`). None of the three puts
  an algebra concentrated in degree zero on the *left*: the last one does use
  `DifferentialGradedAlgebra.degreeZero R R`, but as the right-hand algebra, so it gives derived
  Hom *out of* a `D(R)`-module and not derived Hom *valued in* `D(R)`. So
  `DifferentialGradedModule.derivedHomData (DifferentialGradedAlgebra.degreeZero R R) E P_M`
  cannot be applied, and the goal `RHom(M, N) ≅ Q(Hom^•(P_M, P_N))` has no well-typed statement;
* a transport of the resulting isomorphism along
  `DifferentialGradedModule.degreeZeroDerivedEquivalence`
  (`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroAlgebra.lean:908`), which identifies
  `derivedCategory' (DifferentialGradedAlgebra.degreeZero R R)` with
  `DerivedCategory (ModuleCat R)`;
* a comparison in `CochainComplex (ModuleCat R) ℤ` between the degree-zero component of the
  differential graded internal Hom and `DGCategory.homComplexModules P_M P_N`, the Hom complex the
  source object above is `DerivedCategory.Q` of.

Until those exist, the identification of this file's source object with the chapter's `RHom(M, N)`
is available only degreewise on cohomology, which is what
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquivOver` states.

*Why the two modules cannot be imported together without a rename.*
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_eq` was declared twice, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomLocalization` and in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleForget`, at two
different statements about the same map. This file is the first to read both the module-level
forget chain and the degree-`n` chain, and the clash made that impossible; the second is now
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_eq_objIso`.

*The universe parameters* are the diagonal ones of the site, with the base ring's universe `o`
independent of them.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

/-- **An exact additive functor commutes with the homology functors of complexes.** In each
degree the homology of the image of a complex is the image of its homology, because the functor
preserves the short complex that computes it. -/
def mapHomologicalComplexCompHomologyFunctorIsoOver
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (n : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun Z => (Z.sc n).mapHomologyIso F) (fun ψ =>
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map ψ) F)

/-- **An exact additive functor commutes with the homology functors of the derived
categories.** The comparison on complexes, carried through the two identifications of the
homology functor of the derived category with the one of complexes by the universal property of
the localization. -/
def mapDerivedCategoryCompHomologyFunctorIsoOver
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors
        (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      mapHomologicalComplexCompHomologyFunctorIsoOver F n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSite

universe u o

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, o} X R]
  (K : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- **The degree-`n` cohomology of an object of `D(R)` and of its underlying object of `D(ℤ)`
are the same abelian group.** The forgetful functor of `R`-modules is exact, so it commutes with
the homology functors; forgetting the scalars of an `R`-module does not change its underlying
group, so the comparison is an isomorphism of abelian groups out of the cohomology over `R`
itself. -/
def homologyForgetEquiv (A : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj A) ≃+
      ↥((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((forgetBaseRing R).mapDerivedCategory.obj A)) :=
  ((CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIsoOver (forgetBaseRing R) n).app
    A).symm.addCommGroupIsoToAddEquiv

/-- **That comparison is natural.** Moving it across the degree-`n` cohomology of a morphism of
`D(R)` gives the degree-`n` cohomology of the morphism with its `R`-action forgotten. -/
theorem homologyForgetEquiv_naturality {A B : DerivedCategory (ModuleCat.{u} R)} (f : A ⟶ B)
    (n : ℤ) (x : ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj A)) :
    homologyForgetEquiv R B n
        (ModuleCat.Hom.hom ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map f) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        ((forgetBaseRing R).mapDerivedCategory.map f) (homologyForgetEquiv R A n x) :=
  congrArg (fun z => AddCommGrpCat.Hom.hom z x)
    ((CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIsoOver
      (forgetBaseRing R) n).inv.naturality f)

/-- **Stacks 0CS6, the source of the canonical map in `D(R)`**, read on cohomology and *for
every* `M`, `N` *in* `D(E, d)`. The degree-`n` cohomology of the source of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver` is the
`Ext`-group

`Ext^n_{D(E, d)}(M, N) = Hom_{D(E, d)}(M, N[n])`,

so that source really is `RHom(M, N)` read on cohomology. It is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv` read through
`AlgebraicGeometry.RingedSite.homologyForgetEquiv` and
`AlgebraicGeometry.RingedSite.dgHomComplexModulesDerivedForgetIso`, which say that forgetting the
`R`-action changes neither the cohomology group nor the complex it is taken of. There is no
hypothesis on `M` or `N`. -/
@[stacks 0CS6 "the source of the canonical map in D(R) is RHom(M, N), read on cohomology, for \
every M, N in D(E, d)"]
def tensorWithComplexDerivedHomSourceExtEquivOver
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra)
    (n : ℤ) :
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        (DerivedCategory.Q.obj ((DifferentialGradedModule.dgCategory.{_, _, u}
            (Rep.{u, u, u, u, u, o} X R K).algebra).homComplexModules
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N)))) ≃+ (M ⟶ N⟦n⟧) :=
  (homologyForgetEquiv R _ n).trans
    ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
        (dgHomComplexModulesDerivedForgetIso X R K _ _)).addCommGroupIsoToAddEquiv).trans
      (tensorWithComplexDerivedHomSourceExtEquiv.{u, o} X R K M N n))

/-- **Stacks 0CS6, the target of the canonical map in `D(R)`**, read on cohomology and *for
every* `M`, `N` *in* `D(E, d)`. The degree-`n` cohomology of the target of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver` is the
`Ext`-group

`Ext^n_{D(O)}(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•) = Hom_{D(O)}(M ⊗_E^𝐋 K^•, (N ⊗_E^𝐋 K^•)[n])`.

It is `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomTargetExtEquiv` read through
`AlgebraicGeometry.RingedSite.homologyForgetEquiv` and
`AlgebraicGeometry.RingedSite.globalDerivedHomForgetAppOver`. Together with
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquivOver` it exhibits both
cohomology modules of the clause as the `Ext`-groups the clause compares; that the *map* between
them is the one induced by `- ⊗_E^𝐋 K^•` is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_homology`.

There is no hypothesis on `M` or `N`, and none on the site. -/
@[stacks 0CS6 "the target of the canonical map in D(R) read on cohomology: its degree-n \
cohomology is Ext^n_{D(O)}(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K), for every M, N in D(E, d)"]
def tensorWithComplexDerivedHomTargetExtEquivOver
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra)
    (n : ℤ) :
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        ((scalarRestriction X R).mapDerivedCategory.obj
          (((globalDerivedHomModules X).obj
              (op ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M))).obj
            ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N)))) ≃+
      ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M ⟶
        ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N)⟦n⟧) :=
  (homologyForgetEquiv R _ n).trans
    ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
        (globalDerivedHomForgetAppOver X R _ _)).addCommGroupIsoToAddEquiv).trans
      (tensorWithComplexDerivedHomTargetExtEquiv.{u, o} X R K M N n))

/-- **Stacks 0CS6, the central clause, in the source's `D(R)`.** The degree-`n` cohomology of
the canonical map

`RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)`

of `D(R)` is the map on `Ext` induced by the derived tensor product with `K`, for every `M`, `N`
in `D(E, d)` and every `n`, with both sides read as the `Ext`-groups they are by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquivOver` and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomTargetExtEquivOver`.

There is no hypothesis on `M` or `N`: the statement is quantified over every object of
`D(E, d)`, as the source's is, and the property-(P) reduction of the source's proof is performed
by the choice of representative `DifferentialGradedModule.propertyPModel`. Nor is anything
assumed about the site.

This is `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived_homology` read over
the source's base ring: the canonical map in `D(R)` forgets to the `D(ℤ)`-valued one by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_forget`, and
forgetting the scalars changes neither the cohomology groups nor the map between them. -/
@[stacks 0CS6 "H^n of the canonical map is the Ext map induced by - ⊗_E^𝐋 K, for every M, N in \
D(E, d) and every n, in the source's D(R)"]
theorem tensorWithComplexDerivedHomMapDerivedModulesOver_homology
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra)
    (n : ℤ)
    (η : ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      (DerivedCategory.Q.obj ((DifferentialGradedModule.dgCategory.{_, _, u}
          (Rep.{u, u, u, u, u, o} X R K).algebra).homComplexModules
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N))))) :
    tensorWithComplexDerivedHomTargetExtEquivOver X R K M N n
        (ModuleCat.Hom.hom ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (tensorWithComplexDerivedHomMapDerivedModulesOver X R K M N)) η) =
      tensorWithComplexDerivedExtMap.{u, u, u, u, u, o} X R K n
        (tensorWithComplexDerivedHomSourceExtEquivOver X R K M N n η) := by
  rw [tensorWithComplexDerivedHomTargetExtEquivOver, tensorWithComplexDerivedHomSourceExtEquivOver]
  simp only [AddEquiv.trans_apply]
  rw [homologyForgetEquiv_naturality]
  have key2 : (forgetBaseRing R).mapDerivedCategory.map
          (tensorWithComplexDerivedHomMapDerivedModulesOver X R K M N) ≫
        (globalDerivedHomForgetAppOver X R
          ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M)
          ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N)).hom =
      (dgHomComplexModulesDerivedForgetIso X R K _ _).hom ≫
        tensorWithComplexDerivedHomMapDerived.{u, o} X R K M N :=
    (Iso.inv_comp_eq _).mp (tensorWithComplexDerivedHomMapDerivedModulesOver_forget X R K M N)
  have hmap := congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map key2
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hmap
  refine Eq.trans ?_ (tensorWithComplexDerivedHomMapDerived_homology.{u, o} X R K M N n _)
  refine congrArg (tensorWithComplexDerivedHomTargetExtEquiv.{u, o} X R K M N n) ?_
  simp only [Iso.addCommGroupIsoToAddEquiv_apply, CategoryTheory.Functor.mapIso_hom]
  exact congrArg (fun z => AddCommGrpCat.Hom.hom z (homologyForgetEquiv R _ n η)) hmap

end AlgebraicGeometry.RingedSite

end

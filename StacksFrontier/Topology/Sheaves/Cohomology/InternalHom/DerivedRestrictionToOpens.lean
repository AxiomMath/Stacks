module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategoryHoms
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom on a ringed space commutes with restriction to an open

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of `D(O_X)`. **Stacks 08DL** says
that the derived internal Hom commutes with restriction to an open `U ⊆ X`:

```
RSheafHom(K|_U, L|_U) = RSheafHom(K, L)|_U.
```

The reason is that the construction of `RSheafHom(K, L)` is local: it is computed from the
internal Hom complex `SheafHom^•(A, B)` of representatives whose target is K-injective, the
sections of that complex over an open `V` are the Hom complex of the restrictions to `V`, and
the restriction of a K-injective complex stays K-injective (Stacks 08BS). So both sides are the
class of one and the same complex of `O_U`-modules, and the comparison between them is induced
degreewise by the canonical restriction isomorphism of internal Homs of modules.

## Main definitions

* `Stacks.SheafOfModules.derivedRestrict`: restriction of `O_X`-modules to the opens contained
  in `U`, on derived categories.
* `Stacks.SheafOfModules.derivedSheafHomRestrictionIso`: the comparison isomorphism
  `RSheafHom(K, L)|_U ≅ RSheafHom(K|_U, L|_U)` of Stacks 08DL.
* `Stacks.SheafOfModules.sheafHomRestrictionComplexMap`: the chain-level restriction map of
  internal Hom complexes underlying it.
* `Stacks.SheafOfModules.sliceToSubspaceFunctor`: the equivalence between the slice-site model
  of `O_U`-modules and the open-subspace model.
* `Stacks.SheafOfModules.derivedRestrictToSubspaceIso`: the identification of the two models of
  derived restriction to `U`, the slice-site one above and the derived restriction to the open
  subspace `U`.

## Main results

* `Stacks.SheafOfModules.hasRightDerivedFunctor_homotopyRestriction`: restriction to the opens
  contained in `U` has a right derived functor, which is the instance hypothesis
  `derivedRestrictToSubspaceIso` takes and is no longer owed by its consumers.

* `Stacks.SheafOfModules.derivedSheafHomRestrictionIso_natural_left` and
  `Stacks.SheafOfModules.derivedSheafHomRestrictionIso_natural_right`: the comparison is natural
  in each of the two variables.
* `Stacks.SheafOfModules.sheafHomRestrictionComplexMap_isRestriction`: on every local
  homogeneous cochain the chain-level map is the canonical restriction of internal Hom.
* `Stacks.SheafOfModules.derivedSheafHomRestrictionIso_model`: on representatives with
  K-injective target the comparison is the class of that chain-level map.

## Implementation notes

A topological space together with a sheaf of commutative rings on it is a ringed site, namely the
site of its opens with the open-cover topology, and under that reading the derived internal Hom
of the space is the derived internal Hom of the site. So every statement below is the ringed-site
statement of Stacks 08JB, read off along `Stacks.SheafOfModules.ringedSite` exactly as the
K-injectivity statement of `Stacks.SheafOfModules.isKInjective_sheafHomComplex_of_isKFlat` is.

Restriction to `U` is restriction to the *slice site* `Opens X / U`, that is, to the site whose
objects are the opens contained in `U`; its category of modules is
`SheafOfModules ((structureSheaf Rc).over U)`. This is the model the section data of an internal
Hom complex uses — the sections of `SheafHom^•(A, B)` over `V ⊆ U` are indexed by the objects of
`Opens X / V` — and it is the model in which the chain-level comparison and its local formula are
stated. It is equivalent to, but not the same as, the open-subspace model `O_U`-modules used in
`Stacks.SheafOfModules.restrictComplexToSubspace`.

Sheaves of modules on the slice site are indexed by `Tensor.ringSheaf ((ringedSite Rc).over U).O`
in the derived internal Hom of the slice site and by `(structureSheaf Rc).over U` in the
restriction functor; these are the same sheaf of rings, but only after the forgetting of
commutativity is commuted past the pushforward along `Over.forget U`, which is invisible at the
transparency elaboration uses by default. The functors involved are therefore made
`implicit_reducible` locally, as they are in the site-level file.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]

/-- Restriction of `O_X`-modules to the opens contained in `U`, on derived categories. It is the
functor induced by the degreewise restriction of complexes, which is exact, so it takes the class
of a complex to the class of its restriction. -/
abbrev derivedRestrict :
    DerivedCategory (StructureSheafModules Rc) ⥤
      DerivedCategory (SheafOfModules.{u} ((structureSheaf Rc).over U)) :=
  (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory

/-- **Stacks 08DL.** For objects `K`, `L` of `D(O_X)` the derived internal Hom commutes with
restriction to an open `U`: restricting `RSheafHom(K, L)` to the opens contained in `U` gives the
derived internal Hom `RSheafHom(K|_U, L|_U)` of the restrictions. -/
@[stacks 08DL]
def derivedSheafHomRestrictionIso (K L : DerivedCategory (StructureSheafModules Rc)) :
    (derivedRestrict Rc U).obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj L) ≅
      ((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over U)).obj
          (op ((derivedRestrict Rc U).obj K))).obj ((derivedRestrict Rc U).obj L) := by
  letI : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  letI : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  exact (RingedSite.derivedHomRestriction (ringedSite Rc) U).iso K L

/-- The restriction functor along the ringed-site structure sheaf preserves finite limits; the two
structure sheaves agree up to commutativity forgetting. -/
private instance preservesFiniteLimits_overFunctor_ringSheaf :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
  ‹PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›

/-- The restriction functor along the ringed-site structure sheaf preserves finite colimits. -/
private instance preservesFiniteColimits_overFunctor_ringSheaf :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
  ‹PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›

/-- The comparison of Stacks 08DL is natural in the contravariant variable: restricting the map
`RSheafHom(K, L) ⟶ RSheafHom(K', L)` induced by `f : K' ⟶ K` gives the map induced by `f|_U`. -/
@[stacks 08DL "functoriality in the first variable"]
theorem derivedSheafHomRestrictionIso_natural_left
    {K K' L : DerivedCategory (StructureSheafModules Rc)} (f : K' ⟶ K) :
    (derivedRestrict Rc U).map
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).map f.op).app L) ≫
        (derivedSheafHomRestrictionIso Rc U K' L).hom =
      (derivedSheafHomRestrictionIso Rc U K L).hom ≫
        ((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over U)).map
          ((derivedRestrict Rc U).map f).op).app ((derivedRestrict Rc U).obj L) := by
  exact (RingedSite.derivedHomRestriction (ringedSite Rc) U).natural_left f

/-- The comparison of Stacks 08DL is natural in the covariant variable: restricting the map
`RSheafHom(K, L) ⟶ RSheafHom(K, L')` induced by `g : L ⟶ L'` gives the map induced by `g|_U`. -/
@[stacks 08DL "functoriality in the second variable"]
theorem derivedSheafHomRestrictionIso_natural_right
    {K L L' : DerivedCategory (StructureSheafModules Rc)} (g : L ⟶ L') :
    (derivedRestrict Rc U).map
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).map g) ≫
        (derivedSheafHomRestrictionIso Rc U K L').hom =
      (derivedSheafHomRestrictionIso Rc U K L).hom ≫
        ((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over U)).obj
          (op ((derivedRestrict Rc U).obj K))).map ((derivedRestrict Rc U).map g) := by
  exact (RingedSite.derivedHomRestriction (ringedSite Rc) U).natural_right g

/-- The chain-level comparison underlying Stacks 08DL: the map of complexes of `O_U`-modules
from the restriction of the internal Hom complex `SheafHom^•(A, B)` to the internal Hom complex
`SheafHom^•(A|_U, B|_U)` of the restrictions. -/
def sheafHomRestrictionComplexMap (A B : CochainComplex (StructureSheafModules Rc) ℤ) :
    restrictComplex Rc (sheafHomComplex Rc A B).obj U ⟶
      (RingedSite.sheafHomComplex ((ringedSite Rc).over U)
        (restrictComplex Rc A U) (restrictComplex Rc B U)).obj := by
  letI : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  letI : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
    ‹PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
  exact (RingedSite.derivedHomRestriction (ringedSite Rc) U).complexMap A B

omit [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}] in
/-- On every local homogeneous cochain, the chain-level comparison of Stacks 08DL is the
canonical restriction isomorphism of internal Homs of modules. This is what pins the comparison
down: a cochain over `V ⊆ U` is sent to the cochain it already is, read along the identification
of `Opens X / V` with the opens contained in `V` inside `Opens X / U`. -/
@[stacks 08DL "restriction of internal-Hom complexes"]
theorem sheafHomRestrictionComplexMap_isRestriction
    (A B : CochainComplex (StructureSheafModules Rc) ℤ) :
    RingedSite.IsInternalHomRestrictionMap (ringedSite Rc) U A B
      (sheafHomRestrictionComplexMap Rc U A B) := by
  exact RingedSite.derivedHomRestriction_complexMap_isRestriction (ringedSite Rc) U A B

/-- On the classes of complexes `A` and `B` with `B` K-injective, both sides of Stacks 08DL are
the class of an internal Hom complex, and the comparison is the class of the chain-level
restriction map. Together with naturality this determines the comparison. -/
@[stacks 08DL "canonical model characterization"]
theorem derivedSheafHomRestrictionIso_model
    (A B : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf (ringedSite Rc).O)) ℤ)
    [B.IsKInjective] :
    letI : PreservesFiniteLimits
        (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
      ‹PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
    letI : PreservesFiniteColimits
        (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf (ringedSite Rc).O) U) :=
      ‹PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)›
    (derivedSheafHomRestrictionIso Rc U
          (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
        (RingedSite.restrictionTargetComparison (ringedSite Rc) U A B).hom =
      (RingedSite.restrictionSourceComparison (ringedSite Rc) U A B).hom ≫
        DerivedCategory.Q.map (sheafHomRestrictionComplexMap Rc U A B) := by
  exact RingedSite.derivedHomRestriction_model (ringedSite Rc) U A B

section OpenSubspace

open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

/-- Mathlib's equivalence between the slice-site model of `O_U`-modules, modules over the
structure sheaf of the site of opens contained in `U`, and the open-subspace model, modules over
the restriction of the structure sheaf to the topological space `U`. This is the functor of that
equivalence, with its target named in the open-subspace model. -/
def sliceToSubspaceFunctor :
    SheafOfModules.{u} ((structureSheaf Rc).over U) ⥤
      SheafOfModules.{u} (resRing U (structureSheaf Rc)) :=
  (U.sheafOfModulesEquivOver (structureSheaf Rc)).functor

/-- Passing between the two models of `O_U`-modules is additive: it is the identity on the
underlying maps of sheaves. -/
instance sliceToSubspaceFunctor_additive : (sliceToSubspaceFunctor Rc U).Additive :=
  inferInstanceAs (U.sheafOfModulesEquivOver (structureSheaf Rc)).functor.Additive

/-- Passing between the two models of `O_U`-modules preserves finite limits, being one half of
an equivalence of categories. -/
instance sliceToSubspaceFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (sliceToSubspaceFunctor Rc U) :=
  inferInstanceAs
    (PreservesFiniteLimits (U.sheafOfModulesEquivOver (structureSheaf Rc)).functor)

/-- Passing between the two models of `O_U`-modules preserves finite colimits, being one half of
an equivalence of categories. -/
instance sliceToSubspaceFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (sliceToSubspaceFunctor Rc U) :=
  inferInstanceAs
    (PreservesFiniteColimits (U.sheafOfModulesEquivOver (structureSheaf Rc)).functor)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)] in
/-- Restriction of `O_X`-modules to the opens contained in `U`, followed by the equivalence
between the slice-site and the open-subspace model of `O_U`-modules, is restriction to the open
subspace `U`. Both functors send a module to its sections over the opens contained in `U`, with
the sections of `O_X` over those opens acting, so the equality holds on the nose. -/
theorem overFunctor_comp_sliceToSubspaceFunctor :
    SheafOfModules.overFunctor.{u} (structureSheaf Rc) U ⋙ sliceToSubspaceFunctor Rc U =
      jStar U (structureSheaf Rc) :=
  rfl

/-- Restriction to the opens contained in `U` on derived categories, read through the
equivalence between the slice-site and the open-subspace model of `O_U`-modules, is induced by
restriction to the open subspace `U` on homotopy categories. This is the factorization that
exhibits it as a right derived functor of that homotopy-category functor. -/
def derivedRestrictToSubspaceFactorsh :
    DerivedCategory.Qh ⋙ derivedRestrict Rc U ⋙
        (sliceToSubspaceFunctor Rc U).mapDerivedCategory ≅
      homotopyRestriction (structureSheaf Rc) U :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategoryFactorsh
      (sliceToSubspaceFunctor Rc U).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sliceToSubspaceFunctor Rc U).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (eqToIso (overFunctor_comp_sliceToSubspaceFunctor Rc U)) (ComplexShape.up ℤ))
      DerivedCategory.Qh

/-- **Restriction to the opens contained in `U` has a right derived functor.** Restriction is
exact, so `Stacks.SheafOfModules.derivedRestrictToSubspaceFactorsh` exhibits the functor it
induces on derived categories as a right derived functor of it, and having one is having one.

This discharges the instance hypothesis of
`Stacks.SheafOfModules.derivedRestrictToSubspaceIso`. -/
instance hasRightDerivedFunctor_homotopyRestriction :
    (homotopyRestriction (structureSheaf Rc) U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Rc))
        (ComplexShape.up ℤ)) :=
  letI := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Rc)) (ComplexShape.up ℤ))
    (derivedRestrict Rc U ⋙ (sliceToSubspaceFunctor Rc U).mapDerivedCategory)
    (derivedRestrictToSubspaceFactorsh Rc U)
  Functor.HasRightDerivedFunctor.mk'
    (L := DerivedCategory.Qh)
    (RF := derivedRestrict Rc U ⋙ (sliceToSubspaceFunctor Rc U).mapDerivedCategory)
    (α := (derivedRestrictToSubspaceFactorsh Rc U).inv)

/-- **The two models of derived restriction to an open agree.** Restriction of `O_X`-modules to
the opens contained in `U`, induced on derived categories and read through the equivalence
between the slice-site and the open-subspace model of `O_U`-modules, is the unbounded derived
restriction to the open subspace `U`.

Restriction is exact, so the functor it induces on derived categories already inverts the
quasi-isomorphisms and is therefore a right derived functor of restriction on homotopy
categories; the comparison is the uniqueness of a right derived functor. -/
def derivedRestrictToSubspaceIso
    [(homotopyRestriction (structureSheaf Rc) U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Rc))
        (ComplexShape.up ℤ))] :
    derivedRestrict Rc U ⋙ (sliceToSubspaceFunctor Rc U).mapDerivedCategory ≅
      derivedRestriction (structureSheaf Rc) U :=
  letI := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Rc)) (ComplexShape.up ℤ))
    (derivedRestrict Rc U ⋙ (sliceToSubspaceFunctor Rc U).mapDerivedCategory)
    (derivedRestrictToSubspaceFactorsh Rc U)
  Functor.rightDerivedNatIso
    (derivedRestrict Rc U ⋙ (sliceToSubspaceFunctor Rc U).mapDerivedCategory)
    (derivedRestriction (structureSheaf Rc) U)
    (derivedRestrictToSubspaceFactorsh Rc U).inv
    ((homotopyRestriction (structureSheaf Rc) U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Rc)) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Rc)) (ComplexShape.up ℤ))
    (Iso.refl _)

end OpenSubspace

end Stacks.SheafOfModules

end

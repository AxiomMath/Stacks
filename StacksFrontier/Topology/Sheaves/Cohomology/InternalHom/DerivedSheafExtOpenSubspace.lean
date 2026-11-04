module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.RingedSpace.RestrictTransitive
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafExtRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexAlgebraOpenSubspace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceNatural

/-!
# Ext sheaves commute with restriction to an open subspace

Let `(Y, O_Y)` be a ringed space and `U ⊆ Y` an open, read as the ringed space
`Stacks.SheafOfModules.openSubspace U`, which is `Y.restrict U.isOpenEmbedding`. Restriction of
`O_Y`-modules to `U` is exact, so it descends to derived categories, `K ↦ K|_U`. For objects
`K`, `L` of `D(O_Y)` and every integer `n` there is an isomorphism of `O_U`-modules

```
SheafExt^n_{O_Y}(K, L)|_U ≅ SheafExt^n_{O_U}(K|_U, L|_U),
```

natural in both variables, and an isomorphism `RSheafHom_{O_Y}(K, L)|_U ≅ RSheafHom_{O_U}(K|_U,
L|_U)` in `D(O_U)` of which the first is the degree-`n` cohomology sheaf. This is [Stacks, Tag
08DL] and its consequence for the Ext sheaves of [Stacks, Tag 0BQP], read on the open subspace
rather than on the slice site `Opens Y / U` of the opens contained in `U`.

Restriction to `U` factors as restriction to the slice site followed by the equivalence between
modules on the slice site and modules on the open subspace. The comparison is the composite of
the slice-site form of 08DL, `Stacks.SheafOfModules.derivedSheafHomRestrictionIso`, and of the
invariance of the derived internal Hom under an equivalence of ringed sites,
`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomNatIsoOfIso`, at the equivalence
`TopologicalSpace.Opens.overEquivalence U` between the opens of `U` and the slice over `U`; the
derived functor of the composite is compared with the composite of the derived functors by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, and an exact functor commutes with
the cohomology sheaves by `Stacks.Homology.derivedHomologyIso`.

## Main definitions

* `Stacks.SheafOfModules.openSubspaceRestrictFunctor`: restriction of `O_Y`-modules to the open
  subspace `U`, which is `ExtensionByZeroModules.jStar` by definition.
* `Stacks.SheafOfModules.derivedSheafHomOpenSubspaceIso`: `RSheafHom(K, L)|_U ≅
  RSheafHom(K|_U, L|_U)` in `D(O_U)`.
* `Stacks.SheafOfModules.derivedSheafExtOpenSubspaceIso`: `SheafExt^n(K, L)|_U ≅
  SheafExt^n(K|_U, L|_U)`.

## Main results

* `Stacks.SheafOfModules.openSubspaceRestrictFunctor_eq_comp` and
  `Stacks.SheafOfModules.openSubspaceRestrictFunctor_eq_jStar`: the two descriptions of the
  restriction functor, both by definition.
* `Stacks.SheafOfModules.derivedSheafExtOpenSubspaceIso_natural_left` and
  `Stacks.SheafOfModules.derivedSheafExtOpenSubspaceIso_natural_right`: the comparison of Ext
  sheaves is natural in each variable; likewise
  `Stacks.SheafOfModules.derivedSheafHomOpenSubspaceIso_natural_left` and
  `Stacks.SheafOfModules.derivedSheafHomOpenSubspaceIso_natural_right` for the derived internal
  Hom.

## Implementation notes

The restriction functor is defined as the composite of
`SheafOfModules.overFunctor` with `Stacks.SheafOfModules.sliceToSubspaceFunctor`, the form in
which the comparison is built, and it is `ExtensionByZeroModules.jStar` by `rfl`
(`Stacks.SheafOfModules.overFunctor_comp_sliceToSubspaceFunctor`). Its exactness is inherited
from the two factors.

The second factor is the pushforward along the structure map
`Stacks.SheafOfModules.openSubspacePhi` of the equivalence of ringed sites, by definition, so the
site-equivalence statements apply to it with their exactness hypotheses supplied by
`inferInstanceAs`, following `Stacks.SheafOfModules.derivedSheafHomSchemeOpenIso`.

That restriction commutes with placing a module in one degree,
`(K|_U)` of `F[0]` being `(F|_U)[0]`, naturally in `F`, is Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` at
`Stacks.SheafOfModules.openSubspaceRestrictFunctor`, the object `DerivedCategory.Q.obj
((HomologicalComplex.single _ _ n).obj F)` being `(DerivedCategory.singleFunctor _ n).obj F` by
definition.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {Y : RingedSpace.{u, u}} (U : Opens Y.carrier)

/-! ### Restriction to the open subspace -/

/-- **Restriction of `O_Y`-modules to the open subspace `U`**: restriction to the slice site of
the opens contained in `U`, read on the ringed space `Stacks.SheafOfModules.openSubspace U`. On
sections it is `M ↦ (W ↦ M(W))` for the opens `W ⊆ U`. -/
def openSubspaceRestrictFunctor :
    StructureSheafModules Y.sheaf ⥤ StructureSheafModules (openSubspace U).sheaf :=
  _root_.SheafOfModules.overFunctor.{u} (structureSheaf Y.sheaf) U ⋙
    sliceToSubspaceFunctor Y.sheaf U

/-- Restriction to the open subspace is restriction to the slice site followed by the passage
from the slice-site to the open-subspace model of `O_U`-modules. -/
theorem openSubspaceRestrictFunctor_eq_comp :
    openSubspaceRestrictFunctor U =
      _root_.SheafOfModules.overFunctor.{u} (structureSheaf Y.sheaf) U ⋙
        sliceToSubspaceFunctor Y.sheaf U :=
  rfl

/-- Restriction to the open subspace is the restriction functor `j^*` of extension by zero. -/
theorem openSubspaceRestrictFunctor_eq_jStar :
    openSubspaceRestrictFunctor U = ExtensionByZeroModules.jStar U (structureSheaf Y.sheaf) :=
  rfl

/-- Restriction to the open subspace is additive. -/
instance openSubspaceRestrictFunctor_additive : (openSubspaceRestrictFunctor U).Additive :=
  inferInstanceAs (_root_.SheafOfModules.overFunctor.{u} (structureSheaf Y.sheaf) U ⋙
    sliceToSubspaceFunctor Y.sheaf U).Additive

/-- Restriction to the open subspace is left exact. -/
instance openSubspaceRestrictFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (openSubspaceRestrictFunctor U) :=
  inferInstanceAs (PreservesFiniteLimits
    (_root_.SheafOfModules.overFunctor.{u} (structureSheaf Y.sheaf) U ⋙
      sliceToSubspaceFunctor Y.sheaf U))

/-- Restriction to the open subspace is right exact. -/
instance openSubspaceRestrictFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (openSubspaceRestrictFunctor U) :=
  inferInstanceAs (PreservesFiniteColimits
    (_root_.SheafOfModules.overFunctor.{u} (structureSheaf Y.sheaf) U ⋙
      sliceToSubspaceFunctor Y.sheaf U))

/-- The derived functor of restriction to the open subspace is the composite of the derived
functors of its two factors. -/
abbrev openSubspaceRestrictCompIso :
    (openSubspaceRestrictFunctor U).mapDerivedCategory ≅
      (_root_.SheafOfModules.overFunctor.{u} (structureSheaf Y.sheaf) U).mapDerivedCategory ⋙
        (sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (_root_.SheafOfModules.overFunctor.{u} (structureSheaf Y.sheaf) U)
    (sliceToSubspaceFunctor Y.sheaf U)

/-! ### The derived internal Hom -/

/-- **The derived internal Hom of the slice site, read on the open subspace.** The transport to
`Stacks.SheafOfModules.openSubspace U` of `RSheafHom(K, L)` computed on the slice site of the
opens contained in `U` is the derived internal Hom on the open subspace of the transports. -/
def derivedSheafHomSliceToSubspaceIso
    (K L : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite Y.sheaf).over U).O))) :
    (sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor ((ringedSite Y.sheaf).over U)).obj (op K)).obj L) ≅
      ((RingedSite.derivedSheafHomBifunctor (ringedSite (openSubspace U).sheaf)).obj
        (op ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.obj K))).obj
          ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.obj L) :=
  letI := openSubspaceEquivalenceFunctorIsContinuous U
  letI := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.siteEquivDerivedSheafHomNatIsoOfIso
    (X := (ringedSite Y.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
    U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U)
    (hlim := inferInstanceAs (PreservesFiniteLimits (sliceToSubspaceFunctor Y.sheaf U)))
    (hcolim := inferInstanceAs (PreservesFiniteColimits (sliceToSubspaceFunctor Y.sheaf U)))
    K L

/-- The transport of the derived internal Hom off the slice site is natural in the second,
covariant variable. -/
theorem derivedSheafHomSliceToSubspaceIso_natural_right
    (K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite Y.sheaf).over U).O)))
    {L L' : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite Y.sheaf).over U).O))}
    (g : L ⟶ L') :
    (sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor ((ringedSite Y.sheaf).over U)).obj (op K)).map g) ≫
        (derivedSheafHomSliceToSubspaceIso U K L').hom =
      (derivedSheafHomSliceToSubspaceIso U K L).hom ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite (openSubspace U).sheaf)).obj
          (op ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.obj K))).map
            ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.map g) :=
  let := openSubspaceEquivalenceFunctorIsContinuous U
  let := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.siteEquivDerivedSheafHomNatIsoOfIso_natural_right
    (X := (ringedSite Y.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
    U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U)
    (hlim := inferInstanceAs (PreservesFiniteLimits (sliceToSubspaceFunctor Y.sheaf U)))
    (hcolim := inferInstanceAs (PreservesFiniteColimits (sliceToSubspaceFunctor Y.sheaf U)))
    g

/-- The transport of the derived internal Hom off the slice site is natural in the first,
contravariant variable. -/
theorem derivedSheafHomSliceToSubspaceIso_natural_left
    {K K' L : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite Y.sheaf).over U).O))}
    (f : K' ⟶ K) :
    (sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor ((ringedSite Y.sheaf).over U)).map f.op).app L) ≫
        (derivedSheafHomSliceToSubspaceIso U K' L).hom =
      (derivedSheafHomSliceToSubspaceIso U K L).hom ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite (openSubspace U).sheaf)).map
          ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.map f).op).app
            ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.obj L) :=
  let := openSubspaceEquivalenceFunctorIsContinuous U
  let := openSubspaceEquivalenceInverseIsContinuous U
  RingedSite.siteEquivDerivedSheafHomNatIsoOfIso_natural_left
    (X := (ringedSite Y.sheaf).over U) (Y := ringedSite (openSubspace U).sheaf)
    U.overEquivalence.symm (openSubspacePhi U) (hφ := isIso_openSubspacePhi U)
    (hlim := inferInstanceAs (PreservesFiniteLimits (sliceToSubspaceFunctor Y.sheaf U)))
    (hcolim := inferInstanceAs (PreservesFiniteColimits (sliceToSubspaceFunctor Y.sheaf U)))
    f

/-- **Derived internal Hom commutes with restriction to an open subspace.** For objects `K`, `L`
of `D(O_Y)`, `RSheafHom_{O_Y}(K, L)|_U ≅ RSheafHom_{O_U}(K|_U, L|_U)` in `D(O_U)`: the
restriction to the slice site of [Stacks, Tag 08DL], transported to the open subspace, with
the derived functor of the composite compared to the composite of the derived functors. -/
def derivedSheafHomOpenSubspaceIso (K L : DerivedCategory (StructureSheafModules Y.sheaf)) :
    (openSubspaceRestrictFunctor U).mapDerivedCategory.obj
        (((derivedSheafHom Y.sheaf).obj (op K)).obj L) ≅
      ((derivedSheafHom (openSubspace U).sheaf).obj
        (op ((openSubspaceRestrictFunctor U).mapDerivedCategory.obj K))).obj
          ((openSubspaceRestrictFunctor U).mapDerivedCategory.obj L) :=
  (openSubspaceRestrictCompIso U).app _ ≪≫
    (sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.mapIso
      (derivedSheafHomRestrictionIso Y.sheaf U K L) ≪≫
    derivedSheafHomSliceToSubspaceIso U _ _ ≪≫
    ((derivedSheafHom (openSubspace U).sheaf).mapIso
      ((openSubspaceRestrictCompIso U).app K).op).app _ ≪≫
    ((derivedSheafHom (openSubspace U).sheaf).obj _).mapIso
      ((openSubspaceRestrictCompIso U).app L).symm

/-- The comparison of derived internal Homs is natural in the second, covariant variable. -/
theorem derivedSheafHomOpenSubspaceIso_natural_right
    (K : DerivedCategory (StructureSheafModules Y.sheaf))
    {L L' : DerivedCategory (StructureSheafModules Y.sheaf)} (g : L ⟶ L') :
    (openSubspaceRestrictFunctor U).mapDerivedCategory.map
        (((derivedSheafHom Y.sheaf).obj (op K)).map g) ≫
        (derivedSheafHomOpenSubspaceIso U K L').hom =
      (derivedSheafHomOpenSubspaceIso U K L).hom ≫
        ((derivedSheafHom (openSubspace U).sheaf).obj
          (op ((openSubspaceRestrictFunctor U).mapDerivedCategory.obj K))).map
            ((openSubspaceRestrictFunctor U).mapDerivedCategory.map g) := by
  have h1 := (openSubspaceRestrictCompIso U).hom.naturality
    (((derivedSheafHom Y.sheaf).obj (op K)).map g)
  have h2 := (CommSq.mk (derivedSheafHomRestrictionIso_natural_right Y.sheaf U g (K := K))).map
    (sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory
  have h3 := derivedSheafHomSliceToSubspaceIso_natural_right U
    ((derivedRestrict Y.sheaf U).obj K) ((derivedRestrict Y.sheaf U).map g)
  have h4 := ((derivedSheafHom (openSubspace U).sheaf).map
    ((openSubspaceRestrictCompIso U).app K).op.hom).naturality
      ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.map
        ((derivedRestrict Y.sheaf U).map g))
  have h5 := (openSubspaceRestrictCompIso U).inv.naturality g
  have h5' := (CommSq.mk h5).map ((derivedSheafHom (openSubspace U).sheaf).obj
    (op ((openSubspaceRestrictFunctor U).mapDerivedCategory.obj K)))
  exact ((CommSq.mk h1).vert_comp
    (h2.vert_comp ((CommSq.mk h3).vert_comp ((CommSq.mk h4).vert_comp h5')))).w

/-- The comparison of derived internal Homs is natural in the first, contravariant variable. -/
theorem derivedSheafHomOpenSubspaceIso_natural_left
    {K K' L : DerivedCategory (StructureSheafModules Y.sheaf)} (f : K' ⟶ K) :
    (openSubspaceRestrictFunctor U).mapDerivedCategory.map
        (((derivedSheafHom Y.sheaf).map f.op).app L) ≫
        (derivedSheafHomOpenSubspaceIso U K' L).hom =
      (derivedSheafHomOpenSubspaceIso U K L).hom ≫
        ((derivedSheafHom (openSubspace U).sheaf).map
          ((openSubspaceRestrictFunctor U).mapDerivedCategory.map f).op).app
            ((openSubspaceRestrictFunctor U).mapDerivedCategory.obj L) := by
  have h1 := (openSubspaceRestrictCompIso U).hom.naturality
    (((derivedSheafHom Y.sheaf).map f.op).app L)
  have h2 := (CommSq.mk (derivedSheafHomRestrictionIso_natural_left Y.sheaf U f (L := L))).map
    (sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory
  have h3 := derivedSheafHomSliceToSubspaceIso_natural_left U ((derivedRestrict Y.sheaf U).map f)
    (L := (derivedRestrict Y.sheaf U).obj L)
  have h4 := congrArg (fun φ => ((derivedSheafHom (openSubspace U).sheaf).map φ.op).app
      ((sliceToSubspaceFunctor Y.sheaf U).mapDerivedCategory.obj
        ((derivedRestrict Y.sheaf U).obj L)))
    ((openSubspaceRestrictCompIso U).hom.naturality f)
  simp only [op_comp, Functor.map_comp] at h4
  have h5 := ((derivedSheafHom (openSubspace U).sheaf).map
    ((openSubspaceRestrictFunctor U).mapDerivedCategory.map f).op).naturality
      ((openSubspaceRestrictCompIso U).app L).inv
  exact ((CommSq.mk h1).vert_comp
    (h2.vert_comp ((CommSq.mk h3).vert_comp ((CommSq.mk h4.symm).vert_comp (CommSq.mk h5.symm))))).w

/-! ### The Ext sheaves -/

/-- **Ext sheaves commute with restriction to an open subspace.** For objects `K`, `L` of
`D(O_Y)` and an integer `n`, `SheafExt^n_{O_Y}(K, L)|_U ≅ SheafExt^n_{O_U}(K|_U, L|_U)`: the
restriction of a cohomology sheaf is the cohomology sheaf of the restriction, restriction being
exact, followed by the degree-`n` cohomology of
`Stacks.SheafOfModules.derivedSheafHomOpenSubspaceIso`. -/
def derivedSheafExtOpenSubspaceIso (K L : DerivedCategory (StructureSheafModules Y.sheaf))
    (n : ℤ) :
    (openSubspaceRestrictFunctor U).obj (derivedSheafExt Y.sheaf K L n) ≅
      derivedSheafExt (openSubspace U).sheaf
        ((openSubspaceRestrictFunctor U).mapDerivedCategory.obj K)
        ((openSubspaceRestrictFunctor U).mapDerivedCategory.obj L) n :=
  ((Stacks.Homology.derivedHomologyIso (openSubspaceRestrictFunctor U) n).app
      (((derivedSheafHom Y.sheaf).obj (op K)).obj L)).symm ≪≫
    (DerivedCategory.homologyFunctor (StructureSheafModules (openSubspace U).sheaf) n).mapIso
      (derivedSheafHomOpenSubspaceIso U K L)

/-- **The comparison of Ext sheaves is natural in the second variable**: restricting the map of
Ext sheaves that `g : L ⟶ L'` induces gives the map induced by `g|_U`. -/
theorem derivedSheafExtOpenSubspaceIso_natural_right
    (K : DerivedCategory (StructureSheafModules Y.sheaf))
    {L L' : DerivedCategory (StructureSheafModules Y.sheaf)} (g : L ⟶ L') (n : ℤ) :
    (openSubspaceRestrictFunctor U).map (derivedSheafExtMap Y.sheaf n (𝟙 K) g) ≫
        (derivedSheafExtOpenSubspaceIso U K L' n).hom =
      (derivedSheafExtOpenSubspaceIso U K L n).hom ≫
        derivedSheafExtMap (openSubspace U).sheaf n (𝟙 _)
          ((openSubspaceRestrictFunctor U).mapDerivedCategory.map g) := by
  have hid : ∀ {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
      (A : DerivedCategory (StructureSheafModules Rc))
      {B B' : DerivedCategory (StructureSheafModules Rc)} (b : B ⟶ B'),
      derivedSheafExtMap Rc n (𝟙 A) b =
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (((derivedSheafHom Rc).obj (op A)).map b) := fun Rc A _ _ b =>
    congrArg (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
      (RingedSite.derivedSheafHomMap_id_left (ringedSite Rc) (derivedInternalHom Rc) A b)
  have h1 := (Stacks.Homology.derivedHomologyIso (openSubspaceRestrictFunctor U) n).inv.naturality
    (((derivedSheafHom Y.sheaf).obj (op K)).map g)
  have h2 := (CommSq.mk (derivedSheafHomOpenSubspaceIso_natural_right U K g)).map
    (DerivedCategory.homologyFunctor (StructureSheafModules (openSubspace U).sheaf) n)
  rw [hid, hid]
  exact ((CommSq.mk h1).vert_comp h2).w

/-- The comparison of Ext sheaves is natural in the first variable: restricting the map of Ext
sheaves that `f : K' ⟶ K` induces gives the map induced by `f|_U`. -/
theorem derivedSheafExtOpenSubspaceIso_natural_left
    {K K' : DerivedCategory (StructureSheafModules Y.sheaf)}
    (L : DerivedCategory (StructureSheafModules Y.sheaf))
    (f : K' ⟶ K) (n : ℤ) :
    (openSubspaceRestrictFunctor U).map (derivedSheafExtMap Y.sheaf n f (𝟙 L)) ≫
        (derivedSheafExtOpenSubspaceIso U K' L n).hom =
      (derivedSheafExtOpenSubspaceIso U K L n).hom ≫
        derivedSheafExtMap (openSubspace U).sheaf n
          ((openSubspaceRestrictFunctor U).mapDerivedCategory.map f) (𝟙 _) := by
  have hid : ∀ {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
      {A A' : DerivedCategory (StructureSheafModules Rc)} (a : A' ⟶ A)
      (B : DerivedCategory (StructureSheafModules Rc)),
      derivedSheafExtMap Rc n a (𝟙 B) =
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (((derivedSheafHom Rc).map a.op).app B) := fun Rc _ _ a B =>
    congrArg (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
      (RingedSite.derivedSheafHomMap_id_right (ringedSite Rc) (derivedInternalHom Rc) a B)
  have h1 := (Stacks.Homology.derivedHomologyIso (openSubspaceRestrictFunctor U) n).inv.naturality
    (((derivedSheafHom Y.sheaf).map f.op).app L)
  have h2 := (CommSq.mk (derivedSheafHomOpenSubspaceIso_natural_left U f (L := L))).map
    (DerivedCategory.homologyFunctor (StructureSheafModules (openSubspace U).sheaf) n)
  rw [hid, hid]
  exact ((CommSq.mk h1).vert_comp h2).w

end Stacks.SheafOfModules

end

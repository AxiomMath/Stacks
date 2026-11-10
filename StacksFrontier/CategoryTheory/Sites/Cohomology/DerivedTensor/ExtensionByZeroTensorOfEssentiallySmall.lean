module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.Algebra.Homology.MapTotalComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and the total tensor complex over a site with large objects

Let `(C, O)` be a ringed site whose objects form a type in an arbitrary universe `c` while its
morphisms, the sections of `O` and the sections of its modules all lie in one universe `u`, let
`C` be essentially `u`-small, and let `U` be an object of `C`.  This file carries the two
complex-level consequences of Stacks 0E8I to that configuration:

`Tot(j_{U!}P ⊗_O Q) ≅ j_{U!}(Tot(P ⊗_{O|_U} Q|_U))`,

and, read off it, Stacks 0E8K: the restriction `Q|_U` of a K-flat complex `Q` of `O`-modules is
a K-flat complex of `O|_U`-modules.

## Main definitions

* `Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.extension` and `restriction`:
  extension by zero and restriction, with source and target spelled as the module categories of
  the ringed site and of its localization.
* `Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.extensionTensorIso`: Stacks 0E8I,
  `j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`, in the spelling of the tensor bifunctor.
* `Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.extensionTensorBicomplexIso`: the
  bidegreewise comparison of the two bicomplexes, assembled from the two naturalities of Stacks
  0E8I.
* `Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.tensorComplexExtensionIso`: the
  comparison of the two total complexes.

## Main results

* `Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.kFlat_restrictionComplex`: **Stacks
  0E8K** at this universe shape.

## Implementation notes

The comparison of the bicomplexes is assembled from the two naturalities of Stacks 0E8I with
`HomologicalComplex.Hom.isoOfComponents`, and not from an isomorphism of *bifunctors* through
`HomologicalComplex.mapBifunctorNatIso` as the single-universe
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ExtensionByZeroTensor.lean` does.
At this universe shape Stacks 0E8I is available as a family of isomorphisms of functors in the
module on the slice,
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso`, one for each module on
the big site, together with its naturality in that module,
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionSheafTensor_naturality_right`;
packaging the pair into an isomorphism of bifunctors is work the bicomplex does not need, since
one differential of the bicomplex is covered by each of the two naturalities directly.

`restrictionTensorIso` is stated through tensoring on the right with a fixed module, while the
bicomplexes are built from `Stacks.SheafOfModules.Tensor.sheafTensor`; the two objectwise
tensor products agree only after unfolding both to their restriction maps, which is costly to
check.  So its components are first restated, for arbitrary modules, as
`Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.extensionTensorIso` in the spelling of
the bifunctor, with its two naturalities; every statement about the bicomplexes then refers to
that spelling only, and the identification is checked once.

Passing from the bicomplexes to the total complexes is
`HomologicalComplex₂.TotalMap.totalIso`, whose hypothesis is that extension by zero preserves
the coproducts indexed by the bidegrees of a fixed total degree.  Those are coproducts of
shapes in `Type 0`, and extension by zero is a left adjoint, so it preserves colimits of every
size; no finiteness hypothesis on either complex is needed.

*The spelling of the sheaf of rings on the slice, and why it has to be pinned.*  Two spellings
occur in the inputs: `(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U`,
in which extension by zero and `restrictionTensorIso` are stated, and
`Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)`, in which the tensor bifunctor and the
total tensor complex are, and which is the spelling of
`AlgebraicGeometry.RingedSite.Modules (X.over U)`.  They are definitionally equal — restricting
to the slice and forgetting commutativity commute on the nose — but *not reducibly* so: one is
`Sheaf.over` applied to a `sheafCompose`, the other a `sheafCompose` applied to `Sheaf.over`,
and identifying them unfolds both.  Term-level elaboration pays that once and is unaffected;
instance synthesis, which runs at reducible transparency, is not: with extension by zero left
in its own spelling, the `Additive` instance needed to form
`HomologicalComplex₂.TotalMap.mapBicomplex` is not found, because the `Preadditive` arguments of
the goal are those of the other spelling.  So `extension` and `restriction` restate the two
functors at the `RingedSite.Modules` spelling once and for all, and the instances the
construction needs are established at those restatements.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall

universe u c

open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Sites.ExtensionByZero.OfEssentiallySmall

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C] (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]

/-! ### The slice hypotheses at the spelling of the localized ringed site -/

/-- Sheafification on the slice, at the spelling `(X.over U).J` of the localized ringed site.

`AlgebraicGeometry.RingedSite.over` is `@[implicit_reducible]`, so `(X.over U).J` does not
reduce to `X.J.over U` at the transparency instance synthesis runs at: the hypothesis above is
not found for the localized spelling, and with it the module category of the localized ringed
site is not even known to be abelian.  Restating it here, as
`AlgebraicGeometry.RingedSite.sliceHasSheafify` does for a family of slices, is what makes
`AlgebraicGeometry.RingedSite.Modules (X.over U)` usable. -/
local instance sliceHasSheafify : HasSheafify (X.over U).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (X.J.over U) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences on the slice, at the localized spelling, for the
reason recorded at `sliceHasSheafify`. -/
local instance sliceWEqualsLocallyBijective :
    (X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})

/-! ### Extension by zero and restriction, at the spelling the tensor product uses -/

/-- Extension by zero `j_{U!}` from the localized site, with source and target spelled as the
module categories of `X.over U` and of `X`. -/
abbrev extension :
    RingedSite.Modules.{max c u, u, u} (X.over U) ⥤ RingedSite.Modules.{c, u, u} X :=
  extendByZero X U

/-- Restriction `F ↦ F|_U` of sheaves of modules to the localized site, with source and target
spelled as the module categories of `X` and of `X.over U`. -/
abbrev restriction :
    RingedSite.Modules.{c, u, u} X ⥤ RingedSite.Modules.{max c u, u, u} (X.over U) :=
  SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U

/-- **Extension by zero is additive**, being a left adjoint of the additive restriction. -/
instance additive_extension : (extension X U).Additive :=
  have := sheafRestrictionIsRightAdjoint X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  (SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).left_adjoint_additive

/-- **Restriction to the localized site is additive**, being computed on sections. -/
instance additive_restriction : (restriction X U).Additive :=
  inferInstanceAs
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive

/-- **Extension by zero preserves the coproducts a total complex is assembled from.** It is a
left adjoint, so it preserves colimits of every size; the shapes a total complex needs are the
bidegrees of a fixed total degree, which lie in `Type 0`. -/
instance preservesColimits_extension : PreservesColimitsOfSize.{0, 0} (extension X U) :=
  have := sheafRestrictionIsRightAdjoint X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  (SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).leftAdjoint_preservesColimits

/-- **Extension by zero is exact**, Stacks 03DJ: the left-exact half. -/
instance preservesFiniteLimits_extension : PreservesFiniteLimits (extension X U) :=
  ((exactFunctor_iff _).mp
    (extensionByZero_exact X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)).1

/-- **Extension by zero is exact**, Stacks 03DJ: the right-exact half, which is formal since it
is a left adjoint. -/
instance preservesFiniteColimits_extension : PreservesFiniteColimits (extension X U) :=
  ((exactFunctor_iff _).mp
    (extensionByZero_exact X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)).2

/-- `j_{U!}` on cochain complexes of modules on the localized site. -/
abbrev extensionComplex :
    CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ ⥤
      CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ :=
  (extension X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction to the localized site on cochain complexes of `O`-modules. -/
abbrev restrictionComplex :
    CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ ⥤
      CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ :=
  (restriction X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-! ### The two bicomplexes -/

variable
  [(sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{max c u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{max c u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  [HasBinaryBiproducts (RingedSite.Modules.{c, u, u} X)]
  [HasBinaryBiproducts (RingedSite.Modules.{max c u, u, u} (X.over U))]

variable (P : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ)
  (Q : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)

/-- The bicomplex `(p, q) ↦ j_{U!}P^p ⊗_O Q^q` of modules on `C`, whose total complex is
`Tot(j_{U!}P ⊗_O Q)`. -/
abbrev extensionTensorBicomplex :
    HomologicalComplex₂ (RingedSite.Modules.{c, u, u} X)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((sheafTensor.{c, u, u, u, u} X.O).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj ((extensionComplex X U).obj P)).obj Q

/-- The bicomplex `(p, q) ↦ P^p ⊗_{O|_U} (Q^q)|_U` of modules on `C/U`, whose total complex is
`Tot(P ⊗_{O|_U} Q|_U)`. -/
abbrev sliceTensorBicomplex :
    HomologicalComplex₂ (RingedSite.Modules.{max c u, u, u} (X.over U))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj ((restrictionComplex X U).obj Q)

/- `restrictionTensorIso` and the `FormulaExtension.extensionFunctor` it is built from are made
opaque for the remainder of the file.

Every statement below compares two whole objects or two whole morphisms of sheaves of modules,
and uses `restrictionTensorIso` only through its components and its naturality, never through
its construction.  That construction goes by `presheafExtendByZeroIsoExtension`, which
identifies Mathlib's presheaf-level extension by zero with the concrete direct sum of the
extension formula; left transparent, `extensionFunctor` unfolds to that direct sum and the
unifier descends into it rather than comparing the two arguments it is applied to, and the
checks below then do not fit in the elaboration budget.  With both opaque the comparisons are
first-order.  Nothing here projects a section out of an extension, which is the one thing the
attribute would block. -/
attribute [local irreducible] Stacks.Sites.OverModules.FormulaExtension.extensionFunctor
  Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso

/-! ### Stacks 0E8I in the spelling of the tensor bifunctor -/

/-- **Stacks 0E8I, read through the tensor bifunctor:** for a module `G` on the slice and a
module `F` on `C`, `j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`.

This is the component of `restrictionTensorIso` at `G`, with source and target spelled through
`Stacks.SheafOfModules.Tensor.sheafTensor`, in which the two bicomplexes are.  Tensoring on the
right with `F`, in which `restrictionTensorIso` is stated, sheafifies an objectwise tensor
product that is the canonical one only after unfolding both down to their restriction maps.
Stating the identification here, once and for arbitrary `G` and `F`, keeps it out of every
statement below, each of which mentions these isomorphisms at several bidegrees. -/
@[sga "4 IV 12.11" "b), special case", sga "4 XVII 5.2.1" "partial"]
def extensionTensorIso (G : RingedSite.Modules.{max c u, u, u} (X.over U))
    (F : RingedSite.Modules.{c, u, u} X) :
    ((sheafTensor.{c, u, u, u, u} X.O).obj ((extension X U).obj G)).obj F ≅
      (extension X U).obj
        (((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj G).obj ((restriction X U).obj F)) :=
  (restrictionTensorIso X U F).app G

omit [EssentiallySmall.{u} X.C]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify X.J AddCommGrpCat.{u}]
    [(sheafTensor.{c, u, u, u, u} X.O).Additive]
    [∀ M, ((sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
    [(sheafTensor.{max c u, u, u, u, u} (X.O.over U)).Additive]
    [∀ M, ((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj M).Additive]
    [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{max c u, u, u, u, u} (X.O.over U))
        (ComplexShape.up ℤ)]
    [HasBinaryBiproducts (RingedSite.Modules.{c, u, u} X)]
    [HasBinaryBiproducts (RingedSite.Modules.{max c u, u, u} (X.over U))] in
/-- **The tensor bifunctor on the slice acts on a restricted morphism as
`sliceTensorRightMap`**: tensoring `G` with the restriction of `α : F ⟶ F'` is the
sheafification of the objectwise morphism `G ⊗ F|_U ⟶ G ⊗ F'|_U`, by definition.

Stated on its own so that the identification of the two spellings of the sheaf of rings on the
slice, and of the two objectwise tensor products, is paid in a declaration of its own. -/
lemma sheafTensor_obj_map_restriction {F F' : RingedSite.Modules.{c, u, u} X} (α : F ⟶ F')
    (G : RingedSite.Modules.{max c u, u, u} (X.over U)) :
    ((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj G).map ((restriction X U).map α) =
      sliceTensorRightMap X U α G :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(sheafTensor.{c, u, u, u, u} X.O).Additive]
    [∀ M, ((sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
    [(sheafTensor.{max c u, u, u, u, u} (X.O.over U)).Additive]
    [∀ M, ((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj M).Additive]
    [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{max c u, u, u, u, u} (X.O.over U))
        (ComplexShape.up ℤ)]
    [HasBinaryBiproducts (RingedSite.Modules.{c, u, u} X)]
    [HasBinaryBiproducts (RingedSite.Modules.{max c u, u, u} (X.over U))] in
/-- **`extensionTensorIso` is natural in the module on `C`**: this is
`restrictionSheafTensor_naturality_right`, with the morphism on the slice read as the action of
the tensor bifunctor on the restriction of `α`. -/
lemma extensionTensorIso_naturality_right (G : RingedSite.Modules.{max c u, u, u} (X.over U))
    {F F' : RingedSite.Modules.{c, u, u} X} (α : F ⟶ F') :
    ((sheafTensor.{c, u, u, u, u} X.O).obj ((extension X U).obj G)).map α ≫
        (extensionTensorIso X U G F').hom =
      (extensionTensorIso X U G F).hom ≫
        (extension X U).map
          (((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj G).map
            ((restriction X U).map α)) := by
  rw [sheafTensor_obj_map_restriction]
  exact restrictionSheafTensor_naturality_right X U α G

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(sheafTensor.{c, u, u, u, u} X.O).Additive]
    [∀ M, ((sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
    [(sheafTensor.{max c u, u, u, u, u} (X.O.over U)).Additive]
    [∀ M, ((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj M).Additive]
    [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{max c u, u, u, u, u} (X.O.over U))
        (ComplexShape.up ℤ)]
    [HasBinaryBiproducts (RingedSite.Modules.{c, u, u} X)]
    [HasBinaryBiproducts (RingedSite.Modules.{max c u, u, u} (X.over U))] in
/-- **`extensionTensorIso` is natural in the module on the slice**: this is the naturality of
`restrictionTensorIso` as an isomorphism of functors, read through the tensor bifunctor. -/
lemma extensionTensorIso_naturality_left {G G' : RingedSite.Modules.{max c u, u, u} (X.over U)}
    (β : G ⟶ G') (F : RingedSite.Modules.{c, u, u} X) :
    ((sheafTensor.{c, u, u, u, u} X.O).map ((extension X U).map β)).app F ≫
        (extensionTensorIso X U G' F).hom =
      (extensionTensorIso X U G F).hom ≫
        (extension X U).map
          (((sheafTensor.{max c u, u, u, u, u} (X.O.over U)).map β).app
            ((restriction X U).obj F)) :=
  (restrictionTensorIso X U F).hom.naturality β

/-! ### The comparison of the two bicomplexes -/

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{max c u, u, u, u, u} (X.O.over U))
        (ComplexShape.up ℤ)]
    [HasBinaryBiproducts (RingedSite.Modules.{c, u, u} X)]
    [HasBinaryBiproducts (RingedSite.Modules.{max c u, u, u} (X.over U))] in
/-- **The square of `extensionTensorIso` along the differential of `Q`**, stated at the
bidegrees of the two bicomplexes it is to be pasted into: this is the differential of
`extensionTensorBicomplex` in the second index, and it is covered by the naturality of Stacks
0E8I in the module on the big site. -/
lemma extensionTensorBicomplex_comm_right (p i j : ℤ) :
    (extensionTensorIso X U (P.X p) (Q.X i)).hom ≫
        ((HomologicalComplex₂.TotalMap.mapBicomplex (extension X U)
          (sliceTensorBicomplex X U P Q)).X p).d i j =
      ((extensionTensorBicomplex X U P Q).X p).d i j ≫
        (extensionTensorIso X U (P.X p) (Q.X j)).hom :=
  (extensionTensorIso_naturality_right X U (P.X p) (Q.d i j)).symm

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{max c u, u, u, u, u} (X.O.over U))
        (ComplexShape.up ℤ)]
    [HasBinaryBiproducts (RingedSite.Modules.{c, u, u} X)]
    [HasBinaryBiproducts (RingedSite.Modules.{max c u, u, u} (X.over U))] in
/-- **The square of `extensionTensorIso` along the differential of `P`**, stated in the one
bidegree `q` of the differential of `extensionTensorBicomplex` in the first index: it is
covered by the naturality of Stacks 0E8I in the module on the slice. -/
lemma extensionTensorBicomplex_comm_left (q i j : ℤ) :
    (extensionTensorIso X U (P.X i) (Q.X q)).hom ≫
        ((HomologicalComplex₂.TotalMap.mapBicomplex (extension X U)
          (sliceTensorBicomplex X U P Q)).d i j).f q =
      ((extensionTensorBicomplex X U P Q).d i j).f q ≫
        (extensionTensorIso X U (P.X j) (Q.X q)).hom :=
  (extensionTensorIso_naturality_left X U (P.d i j) (Q.X q)).symm

/-- **Stacks 0E8I bidegreewise**: the bicomplex `(p, q) ↦ j_{U!}P^p ⊗_O Q^q` is the termwise
extension by zero of the bicomplex `(p, q) ↦ P^p ⊗_{O|_U} (Q^q)|_U`.

In bidegree `(p, q)` this is `extensionTensorIso`; the differential in `p` is covered by
`extensionTensorBicomplex_comm_left` and the differential in `q` by
`extensionTensorBicomplex_comm_right`. -/
def extensionTensorBicomplexIso :
    extensionTensorBicomplex X U P Q ≅
      HomologicalComplex₂.TotalMap.mapBicomplex (extension X U)
        (sliceTensorBicomplex X U P Q) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => extensionTensorIso X U (P.X p) (Q.X q))
      (fun i j _ => extensionTensorBicomplex_comm_right X U P Q p i j))
    (fun i j _ => by
      ext q : 1
      exact extensionTensorBicomplex_comm_left X U P Q q i j)

/-! ### The comparison of the two total complexes -/

/-- **Stacks 0E8I for total tensor complexes over a site with large objects:**
`Tot(j_{U!}P ⊗_O Q) ≅ j_{U!}(Tot(P ⊗_{O|_U} Q|_U))`.

The two bicomplexes are identified bidegreewise by `extensionTensorBicomplexIso`, and
extension by zero commutes with the coproducts forming the total complex because it is a left
adjoint. -/
def tensorComplexExtensionIso :
    ((tensorComplex.{c, u, u} X.O).obj ((extensionComplex X U).obj P)).obj Q ≅
      (extensionComplex X U).obj
        (((tensorComplex.{max c u, u, u} (X.O.over U)).obj P).obj
          ((restrictionComplex X U).obj Q)) :=
  have : HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.TotalMap.mapBicomplex (extension X U)
        (sliceTensorBicomplex X U P Q)) (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (extensionTensorBicomplexIso X U P Q) _
  HomologicalComplex₂.total.mapIso (extensionTensorBicomplexIso X U P Q) (ComplexShape.up ℤ) ≪≫
    HomologicalComplex₂.TotalMap.totalIso (extension X U) (sliceTensorBicomplex X U P Q)

/-! ### K-flatness of the restriction -/

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasBinaryBiproducts (RingedSite.Modules.{c, u, u} X)]
    [HasBinaryBiproducts (RingedSite.Modules.{max c u, u, u} (X.over U))] in
/-- **Stacks Project, Tag 0E8K over a site with large objects.** Let `(C, O)` be a ringed site
whose objects form a type in an arbitrary universe `c` while its morphisms, the sections of `O`
and the sections of its modules lie in one universe `u`, let `C` be essentially `u`-small, and
let `U` be an object of `C`.  If `Q` is a K-flat complex of `O`-modules, then `Q|_U` is a
K-flat complex of `O|_U`-modules.

The proof is the source's.  Let `P` be an acyclic complex of `O|_U`-modules.  Extension by
zero is exact (Stacks 03DJ), so `j_{U!}P` is acyclic, and the K-flatness of `Q` then makes
`Tot(j_{U!}P ⊗_O Q)` acyclic.  That complex is `j_{U!}(Tot(P ⊗_{O|_U} Q|_U))` by
`tensorComplexExtensionIso`, and extension by zero reflects exactness (Stacks 0E8G), so
`Tot(P ⊗_{O|_U} Q|_U)` is acyclic as well.

The attribute records the universe shape.  The tag is carried in full by
`Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex`, where the objects, the
morphisms and the sections lie in a single universe — the faithful reading of the tag's ringed
site, which this statement specializes to at `c := u`; that registration stands and this one
does not replace it. -/
@[stacks 0E8K "for a site essentially u-small, objects in Type c, morphisms and modules in u"]
theorem kFlat_restrictionComplex (hQ : Stacks.SheafOfModules.IsKFlat X.O Q) :
    Stacks.SheafOfModules.IsKFlat (X.O.over U) ((restrictionComplex X U).obj Q) := by
  intro G hG
  have hext : ((extensionComplex X U).obj
      (((tensorComplex.{max c u, u, u} (X.O.over U)).obj G).obj
        ((restrictionComplex X U).obj Q))).Acyclic := fun n =>
    (hQ ((extensionComplex X U).obj G)
      (HomologicalComplex.Acyclic.map (extension X U) hG) n).of_iso
      (tensorComplexExtensionIso X U G Q)
  intro n
  rw [HomologicalComplex.exactAt_iff]
  refine (extensionByZero_exact_iff X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U _).mp ?_
  exact (HomologicalComplex.exactAt_iff _ n).mp (hext n)

end Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall

end

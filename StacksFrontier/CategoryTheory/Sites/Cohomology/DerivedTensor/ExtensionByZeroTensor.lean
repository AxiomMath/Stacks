module

public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Extension by zero and the derived tensor product

Let `(C, O)` be a ringed site, `U` an object of `C` and `j_! : Mod(O_U) ⥤ Mod(O)` extension by
zero from the localized site `C/U`, the left adjoint of restriction. For `L` in `D(O_U)` and `K`
in `D(O)`,

`j_!L ⊗^L_O K = j_!(L ⊗^L_{O_U} K|_U)`.

This is Stacks 0GL1. The proof is the one of the source: represent `L` by a complex of
`O_U`-modules and `K` by a K-flat complex of `O`-modules, and apply Stacks 0E8I termwise.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.kFlatModel` is a K-flat complex representing a given object
  of `D(O)`, with `kFlatModelIso` the isomorphism and `kFlatModel_kFlat` its K-flatness.
* `Stacks.DerivedTensor.ExtensionByZero.tensorOfExtension` and `extensionOfTensor` are the two
  bifunctors `Mod(O_U) ⥤ Mod(O) ⥤ Mod(O)` sending `(G, F)` to `j_!G ⊗_O F` and to
  `j_!(G ⊗_{O_U} F|_U)`.

## Main results

* `Stacks.DerivedTensor.ExtensionByZero.tensorOfExtensionIso` is **Stacks 0E8I** with the
  extension by zero in the *left* tensor slot, which is the slot Stacks 0GL1 puts it in.
* `Stacks.DerivedTensor.ExtensionByZero.tensorComplexExtensionIso` is the same identification
  for total tensor complexes, `Tot(j_!P ⊗_O Q) ≅ j_!(Tot(P ⊗_{O_U} Q|_U))`.
* `Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex` is **Stacks 0E8K**: the
  restriction `K|_U` of a K-flat complex `K` of `O`-modules is a K-flat complex of
  `O_U`-modules.
* `Stacks.DerivedTensor.ExtensionByZero.derivedTensorOfKFlatModels` is Stacks 0GL1 for objects
  of the derived categories presented by a K-flat complex on each side.
* `Stacks.DerivedTensor.ExtensionByZero.derivedTensorExtensionIso` is **Stacks 0GL1**.

## Implementation notes

The library's bifunctorial form of Stacks 0E8I identifies `F ⊗_O j_!G` with `j_!(F|_U ⊗_{O_U} G)`,
with the module on the big site in the left tensor slot, while Stacks 0GL1 tensors `j_!L` on the
left. The two are exchanged by the symmetry of the tensor product of sheaves of modules
(`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`) on each of the two sites, and the exchange
is made here at the level of *sheaves*, before any total complex is formed, so that no Koszul
sign ever has to be tracked: `tensorOfExtensionIso` is the braiding on `C`, the flip of that
isomorphism, and the braiding on `C/U`.

The whole construction is a chain of isomorphisms, so no commuting square has to be proved. Its
two substantial steps are the passage from sheaves to total complexes, which is
`HomologicalComplex.mapBifunctorNatIso` followed by
`HomologicalComplex₂.TotalMap.totalIso` — extension by zero is a left adjoint, so it preserves
the coproducts the total complex is built from, with no finiteness hypothesis on the
complexes — and the passage from complexes to the derived categories, which is the right-hand
K-flat comparison of the derived tensor product on `C` together with the left-hand one on `C/U`.

Stacks 0E8K is the underived statement that `tensorComplexExtensionIso` yields at once, so it is
proved here rather than alongside the other transport results for restriction. K-flatness of
`K|_U` quantifies over the acyclic complexes `G` of `O_U`-modules, and extension by zero turns
each such `G` into an acyclic complex of `O`-modules at which the K-flatness of `K` may be
used; `tensorComplexExtensionIso` identifies the resulting total complex with `j_!` of the one
whose acyclicity is wanted, and `j_!` reflects exactness. So no presentation of `K` is needed:
unlike the colimit presentation used for restriction of K-flat *resolutions*, the argument is
the source's, and it applies to every K-flat complex.

Three spellings of the sheaf of rings of the localized site occur in the inputs:
`X.ringSheaf.over U` (extension by zero), `(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U`
(restriction) and
`Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)` (the tensor product and the derived tensor
product). They are definitionally equal, but the last is not reducibly equal to the first two,
so an instance proved for one spelling is not found for another. Everything here is therefore
written at the last spelling, the one the derived tensor product uses, and `extension` and
`restriction` restate the two functors there once and for all; the instances the construction
needs are then established at those restatements, each in its own declaration.

## References

* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K), K-flatness of the
  restriction.
* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I), extension by zero and
  the underived tensor product.
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ), exactness of extension
  by zero.
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G), extension by zero
  reflects exactness.
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS), existence of K-flat
  resolutions.
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU), the derived tensor
  product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.ExtensionByZero
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex sheafTensorBraiding)
open Stacks.DerivedTensor.RingedSite (Modules)

universe d u

namespace Stacks.DerivedTensor.RingedSite

/-! ### K-flat representatives of objects of the derived category -/

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{_, _, _, u, u} R).Additive] [∀ M, ((sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor R) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules R)]

/-- A K-flat complex of `O`-modules representing a given object of `D(O)`: a K-flat resolution
(Stacks 06YS) of any complex representing it. -/
def kFlatModel (M : DerivedCategory (Modules R)) : CochainComplex (Modules R) ℤ :=
  (exists_kFlat_quasiIso R (DerivedCategory.Q.objPreimage M)).choose

/-- The quasi-isomorphism from `kFlatModel R M` to the chosen representative of `M`. -/
def kFlatModelHom (M : DerivedCategory (Modules R)) :
    kFlatModel R M ⟶ DerivedCategory.Q.objPreimage M :=
  (exists_kFlat_quasiIso R (DerivedCategory.Q.objPreimage M)).choose_spec.choose

/-- `kFlatModel R M` is K-flat. -/
theorem kFlatModel_kFlat (M : DerivedCategory (Modules R)) :
    Stacks.SheafOfModules.KFlat R (kFlatModel R M) :=
  (exists_kFlat_quasiIso R (DerivedCategory.Q.objPreimage M)).choose_spec.choose_spec.1

/-- `kFlatModelHom R M` is a quasi-isomorphism. -/
instance quasiIso_kFlatModelHom (M : DerivedCategory (Modules R)) :
    QuasiIso (kFlatModelHom R M) :=
  (exists_kFlat_quasiIso R (DerivedCategory.Q.objPreimage M)).choose_spec.choose_spec.2

/-- `kFlatModel R M` represents `M`: a K-flat resolution is a quasi-isomorphism, hence an
isomorphism in `D(O)`. -/
def kFlatModelIso (M : DerivedCategory (Modules R)) :
    DerivedCategory.Q.obj (kFlatModel R M) ≅ M :=
  asIso (DerivedCategory.Q.map (kFlatModelHom R M)) ≪≫ DerivedCategory.Q.objObjPreimageIso M

end Stacks.DerivedTensor.RingedSite

namespace Stacks.DerivedTensor.ExtensionByZero

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Extension by zero and restriction, at the spelling the derived tensor product uses -/

/-- Restriction `F ↦ F|_U` of sheaves of modules to the localized site `C/U`. -/
abbrev restriction : Modules X.O ⥤ Modules (X.O.over U) :=
  SheafOfModules.overFunctor (SheafOfModules.Tensor.ringSheaf X.O) U

/-- Restriction to `C/U` is additive. -/
instance additive_restriction : (restriction X U).Additive where map_add := rfl

/-- Extension by zero `j_!` from the localized site `C/U`, the left adjoint of restriction. -/
abbrev extension : Modules (X.O.over U) ⥤ Modules X.O := extensionByZeroFunctor X U

/-- Extension by zero from `C/U` is additive. -/
instance additive_extension : (extension X U).Additive :=
  letI : (SheafOfModules.overFunctor (SheafOfModules.Tensor.ringSheaf X.O) U).Additive := ⟨rfl⟩
  (extensionByZeroAdjunction X U).left_adjoint_additive

/-- Extension by zero preserves all colimits, being a left adjoint. This is what makes it
commute with the coproducts a total complex is assembled from. -/
instance preservesColimits_extension : PreservesColimitsOfSize.{0, 0} (extension X U) :=
  (extensionByZeroAdjunction X U).leftAdjoint_preservesColimits

/-- Restriction to `C/U` preserves finite limits. -/
instance preservesFiniteLimits_restriction : PreservesFiniteLimits (restriction X U) :=
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))

/-- Restriction to `C/U` preserves finite colimits. -/
instance preservesFiniteColimits_restriction : PreservesFiniteColimits (restriction X U) :=
  inferInstanceAs (PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))

/-- Extension by zero is left exact: it is the left-exact half of the exactness of extension
by zero, Stacks 03DJ. -/
instance preservesFiniteLimits_extension : PreservesFiniteLimits (extension X U) :=
  letI := Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))))

/-! ### Stacks 0E8I with the extension by zero in the left tensor slot -/

/-- `G ↦ (F ↦ j_!G ⊗_O F)`: extension by zero from `C/U`, followed by tensoring on the left
with it. -/
abbrev tensorOfExtension : Modules (X.O.over U) ⥤ Modules X.O ⥤ Modules X.O :=
  extension X U ⋙ sheafTensor X.O

/-- `G ↦ (F ↦ j_!(G ⊗_{O_U} F|_U))`: tensoring on the left with `G` over the localized site,
applied to the restriction of the second variable, followed by extension by zero. -/
abbrev extensionOfTensor : Modules (X.O.over U) ⥤ Modules X.O ⥤ Modules X.O :=
  sheafTensor (X.O.over U) ⋙
    (Functor.whiskeringLeft _ _ _).obj (restriction X U) ⋙
      (Functor.whiskeringRight _ _ _).obj (extension X U)

/-- **Stacks 0E8I** with the extension by zero in the left tensor slot:
`j_!G ⊗_O F ≅ j_!(G ⊗_{O_U} F|_U)`, naturally in `G` and in `F`. It is the symmetry of `⊗_O`,
the bifunctorial form of Stacks 0E8I read in the other variable order, and the symmetry of
`⊗_{O_U}`. -/
def tensorOfExtensionIso : tensorOfExtension X U ≅ extensionOfTensor X U :=
  Functor.isoWhiskerLeft (extensionByZeroFunctor X U) (sheafTensorBraiding X.O) ≪≫
    (flipFunctor _ _ _).mapIso (extensionTensorBifunctorIso X U) ≪≫
    (flipFunctor _ _ _).mapIso (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (restriction X U) (sheafTensorBraiding (X.O.over U)))
      ((Functor.whiskeringRight _ _ _).obj (extensionByZeroFunctor X U)))

/-! ### The identification of total tensor complexes -/

variable
  [(sheafTensor X.O).Additive]
  [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive]
  [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]

/-- For each `G`, the functor `F ↦ j_!G ⊗_O F` is additive. -/
instance additive_tensorOfExtension_obj (M : Modules (X.O.over U)) :
    ((tensorOfExtension X U).obj M).Additive :=
  inferInstanceAs ((sheafTensor X.O).obj ((extension X U).obj M)).Additive

/-- For each `G`, the functor `F ↦ j_!(G ⊗_{O_U} F|_U)` is additive. -/
instance additive_extensionOfTensor_obj (M : Modules (X.O.over U)) :
    ((extensionOfTensor X U).obj M).Additive :=
  inferInstanceAs
    (restriction X U ⋙ (sheafTensor (X.O.over U)).obj M ⋙ extension X U).Additive

/-- `j_!` on cochain complexes of `O_U`-modules. -/
abbrev extensionComplex := (extension X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction to `C/U` on cochain complexes of `O`-modules. -/
abbrev restrictionComplex := (restriction X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **Stacks 0E8I for total tensor complexes:** `Tot(j_!P ⊗_O Q) ≅ j_!(Tot(P ⊗_{O_U} Q|_U))`.
The two bicomplexes are identified termwise by Stacks 0E8I, and extension by zero commutes with
the coproducts forming the total complex because it is a left adjoint. -/
def tensorComplexExtensionIso (P : CochainComplex (Modules (X.O.over U)) ℤ)
    (Q : CochainComplex (Modules X.O) ℤ) :
    ((tensorComplex X.O).obj ((extensionComplex X U).obj P)).obj Q ≅
      (extensionComplex X U).obj
        (((tensorComplex (X.O.over U)).obj P).obj ((restrictionComplex X U).obj Q)) :=
  HomologicalComplex.mapBifunctorNatIso P Q (ComplexShape.up ℤ) (tensorOfExtensionIso X U) ≪≫
    HomologicalComplex₂.TotalMap.totalIso (c₁₂ := ComplexShape.up ℤ) (extension X U)
      ((((sheafTensor (X.O.over U)).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj ((restrictionComplex X U).obj Q))

/-! ### K-flatness of the restriction -/

/-- **Stacks Project, Tag 0E8K.** Let `(C, O)` be a ringed site and let `U` be an object of
`C`. If `K` is a K-flat complex of `O`-modules, then `K|_U` is a K-flat complex of
`O_U`-modules.

Let `G` be an acyclic complex of `O_U`-modules. Extension by zero is exact (Stacks 03DJ), so
`j_!G` is acyclic, and the K-flatness of `K` then makes `Tot(j_!G ⊗_O K)` acyclic. That
complex is `j_!(Tot(G ⊗_{O_U} K|_U))` by `tensorComplexExtensionIso`, and extension by zero
reflects exactness (Stacks 0E8G), so `Tot(G ⊗_{O_U} K|_U)` is acyclic as well. -/
@[stacks 0E8K]
theorem kFlat_restrictionComplex (Q : CochainComplex (Modules X.O) ℤ)
    (hQ : Stacks.SheafOfModules.KFlat X.O Q) :
    Stacks.SheafOfModules.KFlat (X.O.over U) ((restrictionComplex X U).obj Q) := by
  intro P hP
  have hext : ((extensionComplex X U).obj
      (((tensorComplex (X.O.over U)).obj P).obj ((restrictionComplex X U).obj Q))).Acyclic :=
    fun n => (hQ _ (HomologicalComplex.Acyclic.map (extension X U) hP) n).of_iso
      (tensorComplexExtensionIso X U P Q)
  intro n
  rw [HomologicalComplex.exactAt_iff]
  refine (Stacks.Sites.ExtensionByZero.extensionByZero_exact_iff X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U _).mp ?_
  exact (HomologicalComplex.exactAt_iff _ n).mp (hext n)

/-! ### The derived statement -/

variable [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]

/-- The canonical derived tensor product of `O`-modules (Stacks 06YU). -/
abbrev baseDerivedTensor := RingedSite.canonicalDerivedTensorProduct X.O

/-- The canonical derived tensor product of `O_U`-modules (Stacks 06YU). -/
abbrev sliceDerivedTensor := RingedSite.canonicalDerivedTensorProduct (X.O.over U)

/-- **Stacks 0GL1 on K-flat complexes:** for `P` a K-flat complex of `O_U`-modules and `Q` a
K-flat complex of `O`-modules, `j_!P ⊗^L_O Q = j_!(P ⊗^L_{O_U} Q|_U)`. A K-flat right factor
computes the derived tensor product on `C`, a K-flat left factor computes it on `C/U`, and the
two ordinary total complexes are identified by `tensorComplexExtensionIso`. -/
def derivedTensorOfKFlat (P : CochainComplex (Modules (X.O.over U)) ℤ)
    (Q : CochainComplex (Modules X.O) ℤ)
    (hP : Stacks.SheafOfModules.KFlat (X.O.over U) P)
    (hQ : Stacks.SheafOfModules.KFlat X.O Q) :
    ((baseDerivedTensor X).tensor.obj
          (DerivedCategory.Q.obj ((extensionComplex X U).obj P))).obj
        (DerivedCategory.Q.obj Q) ≅
      (extension X U).mapDerivedCategory.obj
        (((sliceDerivedTensor X U).tensor.obj (DerivedCategory.Q.obj P)).obj
          (DerivedCategory.Q.obj ((restrictionComplex X U).obj Q))) :=
  (baseDerivedTensor X).comparisonRight ((extensionComplex X U).obj P) Q hQ ≪≫
    DerivedCategory.Q.mapIso (tensorComplexExtensionIso X U P Q) ≪≫
    ((extension X U).mapDerivedCategoryFactors.app
      (((tensorComplex (X.O.over U)).obj P).obj ((restrictionComplex X U).obj Q))).symm ≪≫
    (extension X U).mapDerivedCategory.mapIso
      ((sliceDerivedTensor X U).comparisonLeft P ((restrictionComplex X U).obj Q) hP).symm

/-- **Stacks 0GL1** for objects of the two derived categories presented by a K-flat complex on
each side: `derivedTensorOfKFlat` transported along the two presenting isomorphisms. -/
def derivedTensorOfKFlatModels
    (P : CochainComplex (Modules (X.O.over U)) ℤ) (Q : CochainComplex (Modules X.O) ℤ)
    (hP : Stacks.SheafOfModules.KFlat (X.O.over U) P)
    (hQ : Stacks.SheafOfModules.KFlat X.O Q)
    {L : DerivedCategory (Modules (X.O.over U))} (eL : DerivedCategory.Q.obj P ≅ L)
    {K : DerivedCategory (Modules X.O)} (eK : DerivedCategory.Q.obj Q ≅ K) :
    ((baseDerivedTensor X).tensor.obj ((extension X U).mapDerivedCategory.obj L)).obj K ≅
      (extension X U).mapDerivedCategory.obj
        (((sliceDerivedTensor X U).tensor.obj L).obj
          ((restriction X U).mapDerivedCategory.obj K)) :=
  ((baseDerivedTensor X).tensor.obj
      ((extension X U).mapDerivedCategory.obj L)).mapIso eK.symm ≪≫
    ((baseDerivedTensor X).tensor.mapIso
      ((extension X U).mapDerivedCategory.mapIso eL.symm ≪≫
        (extension X U).mapDerivedCategoryFactors.app P)).app (DerivedCategory.Q.obj Q) ≪≫
    derivedTensorOfKFlat X U P Q hP hQ ≪≫
    (extension X U).mapDerivedCategory.mapIso
      (((sliceDerivedTensor X U).tensor.obj (DerivedCategory.Q.obj P)).mapIso
          (((restriction X U).mapDerivedCategoryFactors.app Q).symm ≪≫
            (restriction X U).mapDerivedCategory.mapIso eK) ≪≫
        ((sliceDerivedTensor X U).tensor.mapIso eL).app
          ((restriction X U).mapDerivedCategory.obj K))

/-- **Stacks 0GL1.** Let `(C, O)` be a ringed site, `U` an object of `C` and `j_!` extension by
zero from the localized site `C/U`. For `L` in `D(O_U)` and `K` in `D(O)`,

`j_!L ⊗^L_O K = j_!(L ⊗^L_{O_U} K|_U)`. -/
@[stacks 0GL1]
def derivedTensorExtensionIso (L : DerivedCategory (Modules (X.O.over U)))
    (K : DerivedCategory (Modules X.O)) :
    ((baseDerivedTensor X).tensor.obj ((extension X U).mapDerivedCategory.obj L)).obj K ≅
      (extension X U).mapDerivedCategory.obj
        (((sliceDerivedTensor X U).tensor.obj L).obj
          ((restriction X U).mapDerivedCategory.obj K)) :=
  derivedTensorOfKFlatModels X U
    (RingedSite.kFlatModel (X.O.over U) L) (RingedSite.kFlatModel X.O K)
    (RingedSite.kFlatModel_kFlat (X.O.over U) L) (RingedSite.kFlatModel_kFlat X.O K)
    (RingedSite.kFlatModelIso (X.O.over U) L) (RingedSite.kFlatModelIso X.O K)

end Stacks.DerivedTensor.ExtensionByZero

end

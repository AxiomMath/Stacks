module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
import StacksCore.Tactic.StacksAttribute

/-! # Derived internal Hom out of a derived tensor product

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. **Stacks 08J9**
asserts a canonical isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_O L, M)`

in `D(O)`, functorial in `K`, `L` and `M`, which recovers the tensor–internal-Hom adjunction
of Stacks 08J8 on taking degree-zero global hypercohomology. This file constructs the
isomorphism, derives the adjunction isomorphism of morphism groups from it, and records that
the second is obtained from the first exactly as the source says — by applying Stacks 08JA to
both sides.

The construction follows the source. Choose a K-flat complex `B` representing `L`, a
K-injective complex `I` representing `M` and any complex `A` representing `K`. Then
`SheafHom(B, I)` is K-injective by Stacks 0A96, so it represents `RSheafHom(L, M)` and, being
K-injective, computes `RSheafHom(K, RSheafHom(L, M))` as the class of
`SheafHom(A, SheafHom(B, I))`. The currying isomorphism of Stacks 0A90 identifies that complex
with `SheafHom(Tot(A ⊗_O B), I)`, whose class is `RSheafHom(K ⊗^L_O L, M)` because
`Tot(A ⊗_O B)` computes the derived tensor product for a K-flat right factor (Stacks 06YU) and
`I` is K-injective.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedCurryIso`: the canonical isomorphism.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`: the induced isomorphism of morphism
  groups `(K ⟶ RSheafHom(L, M)) ≃+ (K ⊗^L_O L ⟶ M)`.
* `AlgebraicGeometry.RingedSite.derivedCurryGlobalEquiv`: the canonical isomorphism read on
  degree-zero global hypercohomology.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections` and
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections_homologyMap`: the
  isomorphism of morphism groups is the one induced by `derivedCurryIso` on degree-zero global
  hypercohomology, read through Stacks 08JA.
* `AlgebraicGeometry.RingedSite.derivedCurryGlobalEquiv_apply`: that equivalence is the map
  induced by `derivedCurryIso`.

## What this file does not contain

Stacks 08J9 asserts the isomorphism *functorially* in the three objects, and splits into five
clauses: the isomorphism, its naturality in all three variables, its comparison with the
complex-level currying isomorphism of Stacks 0A90 at a K-flat middle and K-injective target,
the isomorphism of morphism groups, and the compatibility of the two through Stacks 08JA.
Three of those five are here — the isomorphism is `derivedCurryIso`, the isomorphism of
morphism groups is `derivedCurryHomEquiv`, and the compatibility is
`derivedCurryHomEquiv_globalSections`.

**The only clause of 08J9 that this file carries the tag for is the last one**, the source's
closing assertion that the isomorphism recovers the tensor–internal-Hom bijection (21.35.0.1)
of Stacks 08J8 on taking `H⁰(C, -)`: that is `derivedCurryHomEquiv_globalSections` and its
`_homologyMap` form. The bijection of morphism groups carries the tag of Stacks 08J8, and the
isomorphism carries 08J9 in its functorial form. The other two clauses are **not** in this
file:

* **naturality** in `K`, `L` and `M` for arbitrary morphisms of `D(O)`;
* the **comparison** with Stacks 0A90 on the class of a given triple of complexes, rather than
  on the chosen representatives of their classes.

Both are proved, and carry the tag, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality`: the
three-variable naturality square for arbitrary morphisms of `D(O)` is
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural`, its trifunctor form is
`AlgebraicGeometry.RingedSite.derivedCurryNatIso`, and the comparison on a given triple with
K-flat middle and K-injective target is
`AlgebraicGeometry.RingedSite.derivedCurryIso_comparison`.

The naturality of `derivedCurryHomEquiv` in its three objects is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingHomEquivNaturality`.

## Implementation notes

The representative of `K` is `AlgebraicGeometry.RingedSite.kInjectiveModel`, used here only as
*some* complex representing the object: the construction places no condition on `A`, since the
derived internal Hom out of an arbitrary source is computed by a K-injective target (Stacks
0A97) and the derived tensor product is computed by a K-flat *right* factor (Stacks 06YU,
`Stacks.SheafOfModules.DerivedTensorProduct.comparisonRight`). Only `B` must be K-flat and
only `I` must be K-injective.

The total tensor complex is `Stacks.SheafOfModules.Tensor.tensorComplex`, the spelling in which
both the K-flat comparison of Stacks 06YU and the currying isomorphism
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso` of Stacks 0A90 are stated.

The universes are the diagonal `RingedSite.{u, u, u}`: the functorial K-injective resolution
behind the derived internal Hom needs sheaves of `O`-modules to be Grothendieck abelian in the
module universe, and the iterated internal Hom of this statement raises that universe. See the
implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom`.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The derived internal Hom `RSheafHom(L, M)` is the class of the internal Hom complex of the
chosen K-flat representative of `L` into the chosen K-injective representative of `M`. -/
def derivedSheafHomObjectsKFlatModelIso :
    ((derivedSheafHomBifunctor X).obj (op L)).obj M ≅
      DerivedCategory.Q.obj (sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj :=
  derivedSheafHomObjectsModelIso X (kFlatModelIso X L) (kInjectiveModelIso X M) ≪≫
    derivedSheafHomComparison X (kFlatModel X L) (kInjectiveModel X M)

/-- The derived tensor product `K ⊗^L_O L` is the class of the total tensor complex of the
chosen representative of `K` with the chosen K-flat representative of `L`, by the one-sided
K-flat comparison of Stacks 06YU. -/
def derivedTensorObjectsKFlatModelIso :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj (kInjectiveModel X K)).obj
          (kFlatModel X L)) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).mapIso
      (kInjectiveModelIso X K).symm).app L ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (DerivedCategory.Q.obj (kInjectiveModel X K))).mapIso (kFlatModelIso X L).symm ≪≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
        (kInjectiveModel X K) (kFlatModel X L) (isKFlat_kFlatModel X L)

/-- **The derived currying isomorphism of Stacks 08J9.** For objects `K`, `L`, `M` of `D(O)`,
the canonical isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_O L, M)`

in `D(O)`.

It is the complex-level currying isomorphism of Stacks 0A90 between the chosen
representatives, conjugated by the four comparisons that identify the two derived objects with
classes of complexes: the K-injective model of the derived internal Hom (Stacks 0A97) applied
twice, the K-injectivity of `SheafHom(B, I)` for a K-flat `B` and a K-injective `I`
(Stacks 0A96), and the one-sided K-flat comparison of the derived tensor product
(Stacks 06YU). -/
def derivedCurryIso :
    ((derivedSheafHomBifunctor X).obj (op K)).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M) ≅
      ((derivedSheafHomBifunctor X).obj
        (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L))).obj M :=
  haveI : (sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj.IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X (kFlatModel X L) (kInjectiveModel X M)
      (isKFlat_kFlatModel X L)
  derivedSheafHomObjectsModelIso X (kInjectiveModelIso X K)
      (derivedSheafHomObjectsKFlatModelIso X L M).symm ≪≫
    derivedSheafHomComparison X (kInjectiveModel X K)
        (sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj ≪≫
      DerivedCategory.Q.mapIso (sheafHomTensorCurryIso X (kInjectiveModel X K)
          (kFlatModel X L) (kInjectiveModel X M)) ≪≫
        (derivedSheafHomComparison X
            (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj (kInjectiveModel X K)).obj
              (kFlatModel X L)) (kInjectiveModel X M)).symm ≪≫
          (derivedSheafHomObjectsModelIso X
            (derivedTensorObjectsKFlatModelIso X K L).symm (kInjectiveModelIso X M)).symm

/-- The derived currying isomorphism on degree-zero global hypercohomology, as an additive
equivalence. -/
def derivedCurryGlobalEquiv :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op K)).obj
            (((derivedSheafHomBifunctor X).obj (op L)).obj M))) : Type u) ≃+
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj
            (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L))).obj
              M)) : Type u) :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((derivedModuleGlobalSections X).mapIso
        (derivedCurryIso X K L M))).addCommGroupIsoToAddEquiv

/-- `derivedCurryGlobalEquiv` is the map induced by the derived currying isomorphism on
degree-zero global hypercohomology. -/
theorem derivedCurryGlobalEquiv_apply
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M))) : Type u)) :
    derivedCurryGlobalEquiv X K L M z =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (derivedCurryIso X K L M).hom) z :=
  rfl

/-- **The tensor–internal-Hom isomorphism of morphism groups**, Stacks 08J8 as 08J9 gives it:
morphisms `K ⟶ RSheafHom(L, M)` in `D(O)` are morphisms `K ⊗^L_O L ⟶ M`.

It is the derived currying isomorphism read on degree-zero global hypercohomology, with both
sides identified with groups of morphisms by Stacks 08JA. -/
@[stacks 08J8 "the tensor-internal-Hom bijection of morphism groups"]
def derivedCurryHomEquiv :
    (K ⟶ ((derivedSheafHomBifunctor X).obj (op L)).obj M) ≃+
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L ⟶ M) :=
  (derivedSheafHomGlobalSectionsEquiv X K
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)).symm.trans
    ((derivedCurryGlobalEquiv X K L M).trans
      (derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) M))

/-- **The isomorphism of morphism groups is the derived currying isomorphism on global
hypercohomology.** This is the last assertion of Stacks 08J9: taking degree-zero global
hypercohomology of `derivedCurryIso` and identifying both sides with morphism groups by
Stacks 08JA gives `derivedCurryHomEquiv`, the bijection (21.35.0.1) of Stacks 08J8. -/
@[stacks 08J9 "recovers the morphism-group bijection on H^0"]
theorem derivedCurryHomEquiv_globalSections
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M))) : Type u)) :
    derivedCurryHomEquiv X K L M
        (derivedSheafHomGlobalSectionsEquiv X K
          (((derivedSheafHomBifunctor X).obj (op L)).obj M) x) =
      derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) M
        (derivedCurryGlobalEquiv X K L M x) := by
  unfold derivedCurryHomEquiv
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]

/-- `derivedCurryHomEquiv_globalSections` with the additive equivalence
`derivedCurryGlobalEquiv` spelled out as the map induced by `derivedCurryIso`. -/
@[stacks 08J9 "recovers the morphism-group bijection on H^0"]
theorem derivedCurryHomEquiv_globalSections_homologyMap
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M))) : Type u)) :
    derivedCurryHomEquiv X K L M
        (derivedSheafHomGlobalSectionsEquiv X K
          (((derivedSheafHomBifunctor X).obj (op L)).obj M) x) =
      derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedCurryIso X K L M).hom) x) := by
  rw [derivedCurryHomEquiv_globalSections, derivedCurryGlobalEquiv_apply]

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexShift
import StacksCore.Tactic.StacksAttribute

/-!
# The global derived hom in every degree

Let `(C, O)` be a ringed site and let `K`, `L` be objects of `D(O)`. The degree-zero cohomology
of the global derived hom `RHom_O(K, L) = RΓ(C, RSheafHom(K, L))` of Tag 0B6E is the group of
morphisms `K ⟶ L` of `D(O)`, which is
`AlgebraicGeometry.RingedSite.globalDerivedHomModulesDegreeZeroEquiv`. This file computes the
cohomology in *every* degree,

`H^n(RHom_O(K, L)) = Hom_{D(O)}(K, L[n]) = Ext^n_{D(O)}(K, L)`,

by moving the degree into the covariant variable.

What that move needs is the commutation of the derived internal Hom with the translation in its
covariant variable,

`RSheafHom(K, L[n]) ≅ RSheafHom(K, L)[n]`,

which is built here as well and is of independent interest.

It is constructed here as an isomorphism *at each pair of objects*, and nothing below claims
naturality in either variable; in particular it is not assembled into a
`CategoryTheory.Functor.CommShift` for
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, whose absence is what the files
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Exactness` record. It *is* natural in
both variables for arbitrary morphisms of `D(O)`, which is
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_hom_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftNaturality`: the
two-variable localization argument that the section "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects`
describes as missing is not needed for it, because the model used in both variables here is the
K-injective one.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective`: the commutation with
  the translation at a K-injective representative of the covariant variable.
* `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso`: the commutation with the
  translation `RSheafHom(K, L[n]) ≅ RSheafHom(K, L)[n]` for arbitrary objects of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` and
  `AlgebraicGeometry.RingedSite.globalDerivedHomModulesDegreeEquiv`: the degree-`n` cohomology
  of `RHom_O(K, L)` is `Hom_{D(O)}(K, L[n])`, in the abelian-group-valued and in the
  `D(Γ(C, O))`-valued reading of the global derived hom.

## Implementation notes

The commutation with the translation is proved at representatives and transported, as every
statement about `RSheafHom` at arbitrary objects of `D(O)` in this cluster is. At a K-injective
target the derived internal Hom is the ordinary internal Hom complex
(`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, Tag 0A97), a shift of a K-injective
complex is K-injective, and the ordinary internal Hom complex commutes with the translation in
its target by `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso`; the localization functor
commutes with the translation by construction. So the identification is a composite of four
isomorphisms, none of which has to be computed.

The transport to arbitrary objects uses the chosen K-injective representatives
`AlgebraicGeometry.RingedSite.kInjectiveModel` of the derived composition of Tag 0A98, as
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` does, and
`AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso` for the transport itself; the
shifted representative of `L[n]` is the shift of the representative of `L`, which is why the
commutation of the localization functor with the translation appears twice.

The degree-`n` cohomology is then read as the degree-zero cohomology of the `n`-fold shift: the
homology functors of the derived category form a shift sequence (Mathlib's
`CategoryTheory.Functor.ShiftSequence` instance on `DerivedCategory.homologyFunctor _ 0`,
with `DerivedCategory.shift_homologyFunctor` identifying its members with the homology functors
in the other degrees), derived global sections commute with the translation because the
quasi-isomorphisms are stable under it (Mathlib's
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift`), and the shift is then moved into the
covariant variable of `RSheafHom` by the identification above, where Tag 08JA applies in degree
zero.

Nothing is proved natural *here*: what this file provides is the identification of the two
morphism groups in each degree, which is what a consumer computing `Ext` out of the global
derived hom needs. The naturality of both the commutation with the translation and the degree-`n`
identification, in both variables and for arbitrary morphisms of `D(O)`, is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftNaturality` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeNaturality`,
whose degree-zero input is the model-independence of Tag 08JA in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence`.

## References

* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The derived internal Hom commutes with the translation in its covariant variable -/

/-- **The derived internal Hom commutes with the translation in its covariant variable, at a
K-injective representative.** For an arbitrary complex `A` and a K-injective complex `I` of
`O`-modules,

`RSheafHom(A, I[n]) ≅ RSheafHom(A, I)[n]`.

Both sides are computed by the ordinary internal Hom complex, because `I[n]` is K-injective
along with `I`, and the ordinary internal Hom complex commutes with the translation in its
target by `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso`. -/
def derivedSheafHomTargetShiftIsoOfKInjective
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (n : ℤ) :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
        (DerivedCategory.Q.obj (I⟦n⟧)) ≅
      (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
        (DerivedCategory.Q.obj I))⟦n⟧ :=
  derivedSheafHomComparison X A (I⟦n⟧) ≪≫
    DerivedCategory.Q.mapIso (sheafHomTargetShiftIso X (K := A) (M := I) n).symm ≪≫
      (DerivedCategory.Q.commShiftIso n).app (sheafHomComplex X A I).obj ≪≫
        (CategoryTheory.shiftFunctor (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
          (derivedSheafHomComparison X A I).symm

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The derived internal Hom commutes with the translation in its covariant variable.** For
arbitrary objects `K`, `L` of `D(O)` and every integer `n`,

`RSheafHom(K, L[n]) ≅ RSheafHom(K, L)[n]`.

The chosen K-injective representative `I` of `L` has `I[n]` as a K-injective representative of
`L[n]`, and at those representatives the identification is
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective`. -/
def derivedSheafHomTargetShiftIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    ((derivedSheafHomBifunctor X).obj (op K)).obj (L⟦n⟧) ≅
      (((derivedSheafHomBifunctor X).obj (op K)).obj L)⟦n⟧ :=
  derivedSheafHomObjectsModelIso X (kInjectiveModelIso X K)
      ((DerivedCategory.Q.commShiftIso n).app (kInjectiveModel X L) ≪≫
        (CategoryTheory.shiftFunctor (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
          (kInjectiveModelIso X L)) ≪≫
    derivedSheafHomTargetShiftIsoOfKInjective X (kInjectiveModel X K) (kInjectiveModel X L) n ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
        (derivedSheafHomObjectsModelIso X (kInjectiveModelIso X K) (kInjectiveModelIso X L)).symm

/-! ### The cohomology of the global derived hom in every degree -/

/-- **Stacks 0B6E, the cohomology of the global derived hom in every degree.** The degree-`n`
cohomology of `RHom_O(K, L)` is the group of morphisms `K ⟶ L[n]` in `D(O)`, that is the
`Ext`-group `Ext^n_{D(O)}(K, L)`. This is the abelian-group-valued reading
`AlgebraicGeometry.RingedSite.globalDerivedHom` of the global derived hom.

The degree is moved into the covariant variable: the homology functors of the derived category
form a shift sequence, derived global sections commute with the translation, and the derived
internal Hom commutes with the translation in its covariant variable by
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso`; in degree zero the cohomology is
the morphism group by Stacks 08JA, which is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`. -/
@[stacks 0B6E "the degree-n cohomology of RHom_O(K, L) is Hom_{D(O)}(K, L[n])",
  stacks 08JA "global sections in every degree, via the translation in the covariant variable"]
def globalDerivedHomDegreeEquiv
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        (((globalDerivedHom X).obj (op K)).obj L) : Type u) ≃+ (K ⟶ L⟦n⟧) :=
  ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).app
          ((derivedModuleGlobalSections X).obj
            (((derivedSheafHomBifunctor X).obj (op K)).obj
              L))).symm.addCommGroupIsoToAddEquiv).trans
    ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
          ((((derivedModuleGlobalSections X).commShiftIso n).app
                (((derivedSheafHomBifunctor X).obj (op K)).obj L)).symm ≪≫
            (derivedModuleGlobalSections X).mapIso
              (derivedSheafHomTargetShiftIso X K L n).symm)).addCommGroupIsoToAddEquiv).trans
      (derivedSheafHomGlobalSectionsEquiv X K (L⟦n⟧)))

/-- **Stacks 0B6E, the cohomology of the global derived hom in every degree**, for the
`D(Γ(C, O))`-valued global derived hom `AlgebraicGeometry.RingedSite.globalDerivedHomModules`:
the degree-`n` cohomology of `RHom_O(K, L)`, read on the underlying complex of abelian groups as
Stacks 08JA states it, is the group of morphisms `K ⟶ L[n]` of `D(O)`.

This is `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` transported along
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget`, and it is the degree-`n` form
of `AlgebraicGeometry.RingedSite.globalDerivedHomModulesDegreeZeroEquiv`. -/
@[stacks 0B6E "the degree-n cohomology of RHom_O(K, L) in D(Γ(C, O)) is Hom_{D(O)}(K, L[n])"]
def globalDerivedHomModulesDegreeEquiv
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((underlyingDerivedGroup X).obj
          (((globalDerivedHomModules X).obj (op K)).obj L)) : Type u) ≃+ (K ⟶ L⟦n⟧) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      (globalDerivedHomForgetApp X K L)).addCommGroupIsoToAddEquiv).trans
    (globalDerivedHomDegreeEquiv X K L n)

end AlgebraicGeometry.RingedSite

end

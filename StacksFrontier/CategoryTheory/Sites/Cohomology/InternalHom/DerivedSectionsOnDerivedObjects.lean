module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsFromAKFlatSource
import StacksCore.Tactic.StacksAttribute

/-! # Sections of the derived internal Hom, for arbitrary objects of the derived category

Let `(C, O)` be a ringed site and let `L`, `M` be objects of `D(O)`. **Stacks 08JA** asserts

`H⁰(U, RSheafHom(L, M)) = Hom_{D(O|_U)}(L|_U, M|_U)` and
`H⁰(C, RSheafHom(L, M)) = Hom_{D(O)}(L, M)`.

This file proves both. Following the source, the two identifications are obtained from the
corresponding statements at a chosen pair of representatives — a K-flat complex `A`
representing `L` and a K-injective complex `I` representing `M`, for which the internal Hom
complex `SheafHom(A, I)` is K-injective by Stacks 0A96 — by transporting along the
isomorphisms `Q A ≅ L` and `Q I ≅ M`.

## Main definitions

* `AlgebraicGeometry.RingedSite.kFlatModel`: the chosen K-flat complex representing an object
  of `D(O)`, with `AlgebraicGeometry.RingedSite.kFlatModelIso` the isomorphism identifying its
  class with that object.
* `AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso`: the derived internal Hom of
  two objects of `D(O)`, compared with the derived internal Hom of chosen representatives.
* `AlgebraicGeometry.RingedSite.restrictModelIso`: the restriction of an object of `D(O)` to a
  slice of the site, compared with the degreewise restriction of a representing complex.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv`: Stacks 08JA over an object of
  the site.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`: Stacks 08JA globally.

## What this file does not contain

The two declarations above are the two assertions of Stacks 08JA and carry its tag, each
qualified by the clause it states. Two further claims, which the Stacks text does not make
but which a consumer of this tag may expect, are **absent**:

* that the **sections** identification is natural in `L`, or in `M`, for arbitrary morphisms of
  `D(O)`;
* the comparison of either identification with the unit of the derived sections functor.

The agreement of the **global** identification, on the class of a K-flat complex and the class
of a K-injective complex, with the identification
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat` built directly from
those complexes is no longer among them, and never was a definitional unfolding — the chosen
models here are different complexes. It is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply_of_isKFlat`, in
`…InternalHom.DerivedSectionsAgreement`, which proves it for an **arbitrary** such pair of
representatives from the two naturalities of the K-flat form. The **sections** agreement is
still absent.

Naturality of the **global** identification is likewise no longer among them, in either
variable and for arbitrary objects and an arbitrary morphism of `D(O)`: in `L` it is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source`, in
`…InternalHom.DerivedSectionsSourceNaturality`, and in `M` it is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`, in
`…InternalHom.DerivedSectionsTargetNaturality`. The latter file also derives the consequence the
development asks of it, that morphisms out of the structure sheaf are global hypercohomology
classes naturally in the object
(`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality`). The two
variables together are
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`, in
`…InternalHom.GlobalDerivedHomModelIndependence`.

Neither is the input this file used to reduce them all to, the naturality of Stacks 0A94 in both
variables with respect to `AlgebraicGeometry.RingedSite.homMap`. In the global case the
conjugation identity is `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap` — the
compatibility of `AlgebraicGeometry.RingedSite.SheafHomComplex.globalSectionsIso` with `homMap`,
obtained from `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, which computes the
global description of the internal Hom complex on the cochain determined by a global section
without the structure having to record it — and the resulting both-variable naturality is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`. Both
are in `…InternalHom.GlobalHomNaturality`. The local companion is
`AlgebraicGeometry.RingedSite.sectionsIso_homMap_v`, the compatibility that Stacks 0A95 is proved
from.

What the remaining claims cost is therefore not that input but the passage from complexes to
arbitrary morphisms of `D(O)`, and that cost is asymmetric. In the **contravariant** variable a
morphism `Q A' ⟶ Q A` between classes of complexes that are not K-injective is not the class of
a morphism of complexes, so `derivedSheafHomComparison_naturality` does not apply to it directly
and a localization argument is needed; that is what
`derivedSheafHomGlobalSectionsEquiv_naturality_source` carries out. In the **covariant**
variable no such argument is needed, the representative of the target being K-injective: a
morphism between the classes of two K-injective models is the class of a morphism of complexes,
by `AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`; that is why
`derivedSheafHomGlobalSectionsEquiv_naturality_target` needs no closure properties of its clause
and no calculus of fractions.

## Implementation notes

The representative of the target is the K-injective model
`AlgebraicGeometry.RingedSite.kInjectiveModel` already used for the derived composition of
Stacks 0A98, and the representative of the source is a chosen K-flat resolution of *that*
complex rather than of a separate preimage under the localization functor. This is only an
economy: it reuses `kInjectiveModelIso` instead of introducing a second essential-surjectivity
witness for `DerivedCategory.Q`, and the composite `Q (kFlatModel L) ≅ Q (kInjectiveModel L)
≅ L` is the required isomorphism either way.

`kFlatModel` is `Classical.choose` of the **proved**
`Stacks.SheafOfModules.exists_kFlat_quasiIso` (Stacks 06YS), which is the permitted shape, and
is the same pattern as `AlgebraicGeometry.RingedSite.kFlatHomResolution`.

The restriction `L|_U` of an object of `D(O)` is the functor induced on derived categories by
restriction of sheaves of modules to the slice site,
`CategoryTheory.Functor.mapDerivedCategory` of `SheafOfModules.overFunctor`; its exactness is
taken as a hypothesis rather than deduced from
the sheafification hypotheses on every slice. On the class of a complex that functor is the
degreewise restriction `AlgebraicGeometry.RingedSite.restrictComplex`, which is what
`CategoryTheory.Functor.mapDerivedCategoryFactors` records and what lets the statement at
representatives of Stacks 0A94 be transported here.

The universes are the diagonal `RingedSite.{u, u, u}`, inherited from the whole Section 34
cluster: the functorial K-injective resolution needs sheaves of `O`-modules to be Grothendieck
abelian in the module universe and the internal Hom complex raises that universe, so an
iterated internal Hom forces the site and module universes together. See the implementation
notes of `StacksDraft.Ch21.Sec34.DerivedInternalHomOnASite`.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
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

/-- A chosen K-flat complex quasi-isomorphic to the chosen K-injective representative of an
object of `D(O)`, from the existence of K-flat resolutions (Stacks 06YS). -/
def kFlatModel
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X (kInjectiveModel X L)).choose

/-- The augmentation of the chosen K-flat representative into the chosen K-injective one. -/
def kFlatModelMap
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    kFlatModel X L ⟶ kInjectiveModel X L :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X (kInjectiveModel X L)).choose_spec.choose

/-- The chosen K-flat representative is K-flat. -/
theorem isKFlat_kFlatModel
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Stacks.SheafOfModules.IsKFlat X.O (kFlatModel X L) :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (kInjectiveModel X L)).choose_spec.choose_spec.1

/-- The augmentation of the chosen K-flat representative is a quasi-isomorphism. -/
instance quasiIso_kFlatModelMap
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    QuasiIso (kFlatModelMap X L) :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (kInjectiveModel X L)).choose_spec.choose_spec.2

/-- The augmentation of the chosen K-flat representative becomes invertible in `D(O)`. -/
instance isIso_Q_map_kFlatModelMap
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (DerivedCategory.Q.map (kFlatModelMap X L)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-- The chosen K-flat complex does represent the given object of `D(O)`. -/
def kFlatModelIso
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DerivedCategory.Q.obj (kFlatModel X L) ≅ L :=
  asIso (DerivedCategory.Q.map (kFlatModelMap X L)) ≪≫ kInjectiveModelIso X L

/-- The derived internal Hom of two objects of `D(O)`, compared with the derived internal Hom
of complexes representing them. -/
def derivedSheafHomObjectsModelIso
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M) :
    ((derivedSheafHomBifunctor X).obj (op L)).obj M ≅
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
        (DerivedCategory.Q.obj I) :=
  ((derivedSheafHomBifunctor X).mapIso eA.op).app M ≪≫
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).mapIso eI.symm

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- At the identity identifications the comparison of derived internal Homs is the identity. -/
theorem derivedSheafHomObjectsModelIso_refl
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedSheafHomObjectsModelIso X (Iso.refl (DerivedCategory.Q.obj A))
      (Iso.refl (DerivedCategory.Q.obj I))).hom = 𝟙 _ := by
  simp [derivedSheafHomObjectsModelIso]

/-- **Stacks 08JA globally.** For arbitrary objects `L`, `M` of `D(O)` the degree-zero global
hypercohomology of the derived internal Hom `RSheafHom(L, M)` is the group of morphisms
`L ⟶ M` in the derived category of `O`-modules.

A K-injective complex representing `M` and a K-flat complex representing `L` are chosen; the
internal Hom complex between them is K-injective by Stacks 0A96, so global sections compute
derived global sections and the degree-zero cohomology is the group of derived-category
morphisms, by Stacks 0A94. -/
@[stacks 08JA "global sections", sga "6 I 8.1" "partial"]
def derivedSheafHomGlobalSectionsEquiv
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u) ≃+ (L ⟶ M) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        ((derivedModuleGlobalSections X).mapIso
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)))).addCommGroupIsoToAddEquiv).trans
    ((derivedSheafHomGlobalSectionsEquivOfKFlat X (kFlatModel X L) (kInjectiveModel X M)
        (isKFlat_kFlatModel X L)).trans
      (Linear.homCongr ℤ (kFlatModelIso X L) (kInjectiveModelIso X M)).toAddEquiv)

variable (U : X.C)
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- The restriction to the slice over `U` of an object of `D(O)`, compared with the class of
the degreewise restriction of a complex representing it. -/
def restrictModelIso
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) :
    DerivedCategory.Q.obj (restrictComplex X A U) ≅
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj L :=
  ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.app A).symm ≪≫
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.mapIso eA

/-- **Stacks 08JA over an object of the site.** For arbitrary objects `L`, `M` of `D(O)` the
degree-zero hypercohomology over `U` of the derived internal Hom `RSheafHom(L, M)` is the
group of morphisms `L|_U ⟶ M|_U` in the derived category of `O|_U`-modules.

A K-injective complex representing `M` and a K-flat complex representing `L` are chosen; the
internal Hom complex between them is K-injective by Stacks 0A96, so sections compute derived
sections and the degree-zero cohomology is the group of derived-category morphisms between
the restrictions, by Stacks 0A94. -/
@[stacks 08JA "sections over an object"]
def derivedSheafHomSectionsEquiv
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u) ≃+
      ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj L ⟶
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj M) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).mapIso
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)))).addCommGroupIsoToAddEquiv).trans
    ((derivedSheafHomSectionsEquivOfKFlat X U (kFlatModel X L) (kInjectiveModel X M)
        (isKFlat_kFlatModel X L)).trans
      (Linear.homCongr ℤ (restrictModelIso X U (kFlatModelIso X L))
        (restrictModelIso X U (kInjectiveModelIso X M))).toAddEquiv)

end AlgebraicGeometry.RingedSite

end

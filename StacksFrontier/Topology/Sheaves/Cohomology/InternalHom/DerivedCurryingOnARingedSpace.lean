module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.KFlatIntoKInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a derived tensor product, on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of `D(O_X)`. **Stacks 08DJ**
asserts a canonical isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_{O_X} L, M)`

in `D(O_X)`, functorial in `K`, `L` and `M`, which recovers the tensor--internal-Hom bijection
of Stacks 08DI on taking `H⁰(X, -)`.

Functoriality is expressed as an isomorphism of trifunctors on
`D(O_X)ᵒᵖ × D(O_X)ᵒᵖ × D(O_X)`, between `(K, L, M) ↦ RSheafHom(K, RSheafHom(L, M))` and
`(K, L, M) ↦ RSheafHom(K ⊗^L_{O_X} L, M)`, not as a bare isomorphism at fixed objects; and the
recovery of Stacks 08DI is stated and proved, not asserted in a comment.

## Main definitions

* `Stacks.SheafOfModules.iteratedDerivedSheafHomFunctor` and
  `Stacks.SheafOfModules.derivedTensorSheafHomFunctor`: the two sides of the isomorphism as
  trifunctors on triples of objects of `D(O_X)`, contravariant in the first two slots.
* `Stacks.SheafOfModules.derivedCurryIso`: the canonical isomorphism at a triple of objects.
* `Stacks.SheafOfModules.derivedCurryNatIso`: the isomorphism of trifunctors.
* `Stacks.SheafOfModules.DerivedCurryingData`: the content of Stacks 08DJ as a single datum —
  the isomorphism of trifunctors, the identification of its components with
  `derivedCurryIso`, and the recovery of Stacks 08DI on degree-zero global hypercohomology.

## Main results

* `Stacks.SheafOfModules.derivedCurryingData` (Stacks 08DJ): the canonical isomorphism,
  functorial in all three objects, recovering Stacks 08DI on `H⁰(X, -)`.
* `Stacks.SheafOfModules.derivedCurryIso_natural`: the naturality square of `derivedCurryIso`
  for arbitrary morphisms of `D(O_X)` in all three variables, written with the induced maps
  `derivedSheafHomMap` and `derivedTensorMap` of Stacks 08DI.
* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_eq_globalSectionsCurry` and
  `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_globalSections`: the bijection of
  Stacks 08DI is `derivedCurryIso` read on degree-zero global hypercohomology, both sides
  being identified with morphism groups by Stacks 08DK; as an identity of additive
  equivalences and in its elementwise form.
* `Stacks.SheafOfModules.derivedCurryIso_comparison`: on a triple of complexes with K-flat
  middle and K-injective target, `derivedCurryIso` is the currying isomorphism of complexes,
  conjugated by the identifications of the two derived objects with classes of internal Hom
  complexes. This is the construction described above Stacks 08DJ in the source.

## Implementation notes

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of
its opens with the open-cover topology, so the ringed-site statement of Stacks 08J9 applies
verbatim: nothing is reproved here. Each declaration below is the site-level term, type-checked
against the space-level statement, read off along `Stacks.SheafOfModules.ringedSite` exactly as
Stacks 08DI, 08DK and 0A8T are in the neighbouring files; there is no comparison layer between
the two settings.

The derived internal Hom and the derived tensor product used here are
`Stacks.SheafOfModules.derivedSheafHom` and `Stacks.SheafOfModules.derivedTensor`, the ones
Stacks 08DI and 08DK are stated for, so the three tags of this section speak about one and the
same pair of functors and the recovery statement is an identity between the declarations that
carry those tags rather than between two parallel constructions.

**Where the site spelling is written out.** `derivedSheafHom` and `derivedTensor` are
abbreviations for `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor (ringedSite Rc)` and
`derivedTensorProductFunctor (ringedSite Rc)`, so the two spellings denote the same functor.
They are not interchangeable for unification in *argument* position, however: a statement
written with the space spelling and proved by the site-level term makes the elaborator unfold
the ringed-site structure underneath an `AddEquiv` coercion, which exhausts the recursion
budget. So in the statements about degree-zero global hypercohomology the site spelling is
written out, and the two identifications of Stacks 08DI and 08DK — which are genuine
definitions, not abbreviations — are bridged by the `rfl` lemmas
`derivedSheafHomTensorEquiv_eq` and `derivedSheafHomGlobalSectionsEquiv_eq` and applied by
rewriting rather than by unification.

**The two spellings of the currying isomorphism of complexes.** The complex-level isomorphism
of Stacks 0A8M has two independent realizations in this development: the one built from the
monoidal closed structure on complexes of `O_X`-modules,
`Stacks.Cohomology.SheafHomComplexCurrying.sheafHomTensorIsoConstruction`, and the one built
from the explicit curry and uncurry cochain formulas on the internal Hom complex of
Stacks 0A8Z, `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso` (tagged 0A90, the
ringed-site form of 0A8M). The two are isomorphisms between complexes that are themselves only
*isomorphic*, not equal — `MonoidalClosed.ihom` is a sheafification while the internal Hom
sheaf of Stacks 03EM is already a sheaf — and the identification of the two internal Homs,
`AlgebraicGeometry.RingedSite.ihomIsoInternalHomSheaf`, exists at the level of single sheaves
of modules only. No comparison of the two currying isomorphisms of *complexes* exists, so
`derivedCurryIso_comparison` below is stated for the second spelling, which is the one the
derived construction is built from; it is deliberately not stated for the first.

## References

* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A8M](https://stacks.math.columbia.edu/tag/0A8M)
* [Stacks Project, Tag 0A8T](https://stacks.math.columbia.edu/tag/0A8T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- Triples of objects of `D(O_X)`, contravariant in the first two slots and covariant in the
third: the common source of the two sides of Stacks 08DJ. -/
abbrev derivedTriples :=
  (DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc)))ᵒᵖ ×
    (DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))

/-- The left-hand side of Stacks 08DJ as a trifunctor: the iterated derived internal Hom
`(K, L, M) ↦ RSheafHom(K, RSheafHom(L, M))`. -/
abbrev iteratedDerivedSheafHomFunctor :
    derivedTriples Rc ⥤ DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc)) :=
  RingedSite.iteratedHomFunctor (ringedSite Rc)

/-- The right-hand side of Stacks 08DJ as a trifunctor: the derived internal Hom out of the
derived tensor product, `(K, L, M) ↦ RSheafHom(K ⊗^L_{O_X} L, M)`. -/
abbrev derivedTensorSheafHomFunctor :
    derivedTriples Rc ⥤ DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc)) :=
  RingedSite.tensorHomFunctor (ringedSite Rc)

/-- **The derived currying isomorphism of Stacks 08DJ at a triple of objects.** For objects
`K`, `L`, `M` of `D(O_X)` on a ringed space, the canonical isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_{O_X} L, M)`

in `D(O_X)`. It is the currying isomorphism of internal Hom complexes, conjugated by the
comparisons identifying each side with the class of a complex: the derived internal Hom into a
K-injective target is the class of the internal Hom complex, the internal Hom complex out of a
K-flat complex into a K-injective one is again K-injective (Stacks 0A8T), and the derived
tensor product with a K-flat right factor is the total tensor complex. -/
abbrev derivedCurryIso (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    ((derivedSheafHom Rc).obj (op K)).obj (((derivedSheafHom Rc).obj (op L)).obj M) ≅
      ((derivedSheafHom Rc).obj (op (((derivedTensor Rc).obj K).obj L))).obj M :=
  RingedSite.derivedCurryIso (ringedSite Rc) K L M

/-- **Stacks 08DJ: the derived currying isomorphism is an isomorphism of trifunctors.** The
canonical isomorphism of `Stacks.SheafOfModules.derivedCurryIso`, bundled as an isomorphism
between the trifunctor `(K, L, M) ↦ RSheafHom(K, RSheafHom(L, M))` and the trifunctor
`(K, L, M) ↦ RSheafHom(K ⊗^L_{O_X} L, M)` on `D(O_X)ᵒᵖ × D(O_X)ᵒᵖ × D(O_X)`. -/
abbrev derivedCurryNatIso :
    iteratedDerivedSheafHomFunctor Rc ≅ derivedTensorSheafHomFunctor Rc :=
  RingedSite.derivedCurryNatIso (ringedSite Rc)

/-- The components of the isomorphism of trifunctors are the canonical isomorphisms. -/
theorem derivedCurryNatIso_hom_app
    (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    (derivedCurryNatIso Rc).hom.app (op K, op L, M) = (derivedCurryIso Rc K L M).hom :=
  RingedSite.derivedCurryNatIso_hom_app (ringedSite Rc) K L M

/-- **Functoriality of the derived currying isomorphism in all three objects.** For morphisms
`k : K' ⟶ K`, `l : L' ⟶ L` and `m : M ⟶ M'` of `D(O_X)` the square formed by `derivedCurryIso`
at `(K, L, M)` and at `(K', L', M')` commutes: the isomorphism is natural contravariantly in
the source and in the middle object and covariantly in the target. -/
theorem derivedCurryIso_natural
    {K K' L L' M M' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))}
    (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M') :
    derivedSheafHomMap Rc k (derivedSheafHomMap Rc l m) ≫ (derivedCurryIso Rc K' L' M').hom =
      (derivedCurryIso Rc K L M).hom ≫
        derivedSheafHomMap Rc (derivedTensorMap Rc k l) m := by
  have h := (derivedCurryNatIso Rc).hom.naturality
    (show ((op K, op L, M) : derivedTriples Rc) ⟶ (op K', op L', M') from (k.op, l.op, m))
  rw [derivedCurryNatIso_hom_app, derivedCurryNatIso_hom_app] at h
  exact h

section GlobalSections

/-- The tensor--internal-Hom bijection of Stacks 08DI on a ringed space is the ringed-site one,
by definition. -/
theorem derivedSheafHomTensorEquiv_eq
    (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    derivedSheafHomTensorEquiv Rc K L M =
      RingedSite.derivedCurryHomEquiv (ringedSite Rc) K L M :=
  rfl

/-- The identification of Stacks 08DK on a ringed space is the ringed-site one, by
definition. -/
theorem derivedSheafHomGlobalSectionsEquiv_eq
    (L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    derivedSheafHomGlobalSectionsEquiv Rc L M =
      RingedSite.derivedSheafHomGlobalSectionsEquiv (ringedSite Rc) L M :=
  rfl

/-- **Stacks 08DJ recovers Stacks 08DI on `H⁰(X, -)`.** The tensor--internal-Hom bijection

`Hom_{D(O_X)}(K, RSheafHom(L, M)) = Hom_{D(O_X)}(K ⊗^L_{O_X} L, M)`

of Stacks 08DI is the derived currying isomorphism read on degree-zero global
hypercohomology: it is the composite of the identification of Stacks 08DK for
`RSheafHom(K, RSheafHom(L, M))`, run backwards, with the map induced by
`derivedCurryIso` on `H⁰(X, -)`, and then with the identification of Stacks 08DK for
`RSheafHom(K ⊗^L_{O_X} L, M)`. -/
theorem derivedSheafHomTensorEquiv_eq_globalSectionsCurry
    (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    derivedSheafHomTensorEquiv Rc K L M =
      @AddEquiv.trans _ _ _
        (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc)) K
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)).toAdd _
        (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc))
          (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M).toAdd
        (@AddEquiv.symm _ _ _
          (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc)) K
            (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)).toAdd
          (derivedSheafHomGlobalSectionsEquiv Rc K
            (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
              (op L)).obj M)))
        (@AddEquiv.trans _ _ _ _ _
          (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc))
            (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M).toAdd
          (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
              ((derivedModuleGlobalSections (ringedSite Rc)).mapIso
                (RingedSite.derivedCurryIso (ringedSite Rc) K L
                  M))).addCommGroupIsoToAddEquiv)
          (derivedSheafHomGlobalSectionsEquiv Rc
            (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M)) :=
  rfl

/-- `derivedSheafHomTensorEquiv_eq_globalSectionsCurry` elementwise: the bijection of
Stacks 08DI sends the class of a degree-zero global hypercohomology class of
`RSheafHom(K, RSheafHom(L, M))` to the class of its image under `H⁰(X, -)` of the derived
currying isomorphism. -/
theorem derivedSheafHomTensorEquiv_globalSections
    (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M))) :
        Type u)) :
    derivedSheafHomTensorEquiv Rc K L M
        (derivedSheafHomGlobalSectionsEquiv Rc K
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M) x) =
      derivedSheafHomGlobalSectionsEquiv Rc
          (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (RingedSite.derivedCurryIso (ringedSite Rc) K L M).hom) x) := by
  refine (congrArg (fun equivalence => equivalence
    (derivedSheafHomGlobalSectionsEquiv Rc K
      (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M) x))
    (derivedSheafHomTensorEquiv_eq_globalSectionsCurry Rc K L M)).trans ?_
  exact congrArg (fun sectionValue => derivedSheafHomGlobalSectionsEquiv Rc
      (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (RingedSite.derivedCurryIso (ringedSite Rc) K L M).hom) sectionValue))
    (@AddEquiv.symm_apply_apply _ _ _
      (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc)) K
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)).toAdd
      (derivedSheafHomGlobalSectionsEquiv Rc K
        (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)) x)

end GlobalSections

/-- **The construction described above Stacks 08DJ.** For complexes `A`, `B`, `I` of
`O_X`-modules with `B` K-flat and `I` K-injective, the derived currying isomorphism at the
classes of `A`, `B`, `I` is the currying isomorphism of internal Hom complexes

`SheafHom^•(A, SheafHom^•(B, I)) ≅ SheafHom^•(Tot(A ⊗_{O_X} B), I)`,

read through the identifications of both derived objects with classes of complexes. The
left-hand identification uses that `SheafHom^•(B, I)` is K-injective (Stacks 0A8T); the
right-hand one uses that `Tot(A ⊗_{O_X} B)` computes the derived tensor product because `B` is
K-flat. -/
theorem derivedCurryIso_comparison
    (A B I : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ)
    (hB : IsKFlat Rc B) [I.IsKInjective] :
    (derivedCurryIso Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
            (DerivedCategory.Q.obj I)).hom ≫
        (RingedSite.tensorHomRepresentativeIso (ringedSite Rc) A B I hB).hom =
      (RingedSite.iteratedHomRepresentativeIso (ringedSite Rc) A B I hB).hom ≫
        DerivedCategory.Q.map
          (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B I).hom :=
  RingedSite.derivedCurryIso_comparison (ringedSite Rc) A B I hB

/-- The content of Stacks 08DJ for a ringed space `(X, O_X)`, as a single datum: the canonical
isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_{O_X} L, M)`,

its functoriality in `K`, `L` and `M`, and the fact that it recovers Stacks 08DI on taking
`H⁰(X, -)`.

Functoriality is the datum of an isomorphism of trifunctors together with the identification of
its components with `Stacks.SheafOfModules.derivedCurryIso`, so the three fields do speak about
one isomorphism and not about two unrelated ones. -/
structure DerivedCurryingData where
  /-- The isomorphism of trifunctors
  `(K, L, M) ↦ RSheafHom(K, RSheafHom(L, M))` ≅ `(K, L, M) ↦ RSheafHom(K ⊗^L_{O_X} L, M)`:
  the canonical isomorphism together with its functoriality in all three objects. -/
  natIso : iteratedDerivedSheafHomFunctor Rc ≅ derivedTensorSheafHomFunctor Rc
  /-- At a triple of objects the isomorphism of trifunctors is the canonical isomorphism
  `derivedCurryIso`. -/
  natIso_app (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    natIso.hom.app (op K, op L, M) = (derivedCurryIso Rc K L M).hom
  /-- Applying `H⁰(X, -)` to the canonical isomorphism and identifying both sides with groups
  of morphisms in `D(O_X)` by Stacks 08DK gives the tensor--internal-Hom bijection of
  Stacks 08DI. -/
  globalSections (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    derivedSheafHomTensorEquiv Rc K L M =
      @AddEquiv.trans _ _ _
        (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc)) K
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)).toAdd _
        (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc))
          (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M).toAdd
        (@AddEquiv.symm _ _ _
          (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc)) K
            (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj M)).toAdd
          (derivedSheafHomGlobalSectionsEquiv Rc K
            (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
              (op L)).obj M)))
        (@AddEquiv.trans _ _ _ _ _
          (Preadditive.homGroup (C := DerivedCategory (StructureSheafModules Rc))
            (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M).toAdd
          (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
              ((derivedModuleGlobalSections (ringedSite Rc)).mapIso
                (RingedSite.derivedCurryIso (ringedSite Rc) K L
                  M))).addCommGroupIsoToAddEquiv)
          (derivedSheafHomGlobalSectionsEquiv Rc
            (((derivedTensorProductFunctor (ringedSite Rc)).obj K).obj L) M))

/-- **Stacks 08DJ.** Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of
`D(O_X)`. There is a canonical isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_{O_X} L, M)`

in `D(O_X)`, functorial in `K`, `L` and `M`, which recovers the tensor--internal-Hom bijection
of Stacks 08DI on taking `H⁰(X, -)`. -/
@[stacks 08DJ, sga "6 I 7.4" "first isomorphism"]
def derivedCurryingData : DerivedCurryingData Rc where
  natIso := derivedCurryNatIso Rc
  natIso_app K L M := derivedCurryNatIso_hom_app Rc K L M
  globalSections K L M := derivedSheafHomTensorEquiv_eq_globalSectionsCurry Rc K L M

end Stacks.SheafOfModules

end

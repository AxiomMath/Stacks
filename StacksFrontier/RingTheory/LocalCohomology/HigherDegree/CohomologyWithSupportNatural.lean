module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import all StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence

/-!
# The local cohomology comparison isomorphisms, as isomorphisms of functors

Let `A` be a commutative ring and `T ⊆ Spec A` a subset. The two comparison isomorphisms of
`StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison` are stated
there object by object, at a fixed `A`-module `M`. Both are built from natural transformations,
and this file states them as natural isomorphisms of functors on `ModuleCat A`, each pinned to
the object-level version by an `_app` lemma:

* local cohomology with support in `T` of a module placed in degree zero is the classical
  `ℕ`-indexed right derived functor of `T`-supported sections, Mathlib's
  `CategoryTheory.Functor.rightDerived`;
* over a Noetherian ring the supported-sections model and the coreflection model of Stacks 0A6Q
  agree, which is Stacks 0955.

Composing the two gives the form the degreewise comparison of Stacks 0A6T must take for a tower
`n ↦ M/IⁿM` to be transported along it: the `n`-th right derived functor of `V(I)`-supported
sections is the `n`-th local cohomology functor of the coreflection model, naturally in the
module.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyWithSupportInRightDerivedNatIso` — local cohomology with
  support in `T` of a module placed in degree zero, as a functor of the module, is the classical
  `n`-th right derived functor of `T`-supported sections.
* `Stacks.LocalCohomology.localCohomologyModelsNatIso` — over a Noetherian ring the two models of
  local cohomology agree as functors of the module.
* `Stacks.LocalCohomology.sectionsWithSupportRightDerivedIsoLocalCohomologyNatIso` — the composite
  of the two: `N ↦ Rⁿ Γ_{V(I)}(N)` is `N ↦ H ⁿ_I(N)`, naturally in `N`.

## Main results

* `Stacks.LocalCohomology.localCohomologyWithSupportInRightDerivedNatIso_app`,
  `Stacks.LocalCohomology.localCohomologyModelsNatIso_app` and
  `Stacks.LocalCohomology.sectionsWithSupportRightDerivedIsoLocalCohomologyNatIso_app` — the
  components of the three natural isomorphisms, each pinned to the object-level comparison of
  `CohomologyWithSupportComparison`.

## Implementation notes

The functors are written out as honest composites. `localCohomologyWithSupportIn A T K i` is by
definition `(DerivedCategory.homologyFunctor _ i).obj ((derivedSectionsWithSupportIn A T).obj K)`
and `localCohomologyModule A I hI M i` is the same with `derivedSectionsWithSupportIn A (V(I))`
replaced by `localCohomologyDerived A I hI`, so the two sides of each isomorphism below are
`DerivedCategory.singleFunctor _ 0 ⋙ R ⋙ DerivedCategory.homologyFunctor _ i` for the two
derived functors `R`, and their values at a module are literally the modules compared in
`CohomologyWithSupportComparison`.

The naturality of the second comparison is immediate:
`Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology` is a natural transformation
and `Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology` says it is a natural
isomorphism over a Noetherian ring, so whiskering it on both sides is all that is needed.

The first comparison needs an argument. The object-level isomorphism
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoRightDerived` is built by
`Stacks.Cohomology.rightDerivedSingleIso`, a private declaration of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence` reached by
`import all`, which fixes the chosen injective resolution of the single module `M` and carries no
naturality of its own; the natural isomorphism is the separate construction
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, which runs the same
argument through the functor `Stacks.DerivedIndexing.resH` of extended chosen injective
resolutions. The two were not known to agree. The private section below proves that they do —
`Stacks.LocalCohomology.SingleCompare.natIso_app_eq`, for any right derived functor of any
additive functor between abelian categories — so the natural isomorphism here is pinned to the
object-level one on the nose. Both sides are read off the same chosen injective resolution: the
comparison is a chain of five identifications, of the single functor with the extended chosen
resolution, of the unit of the derived functor there, of the two factorizations of the cohomology
functor through the homotopy category, of the two directions of the comparison of `F(K.extend e)`
with `(F K).extend e`, and of the chosen resolution with itself in the homotopy category.

Several intermediate statements are spelled out with the complex written as
`(injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat` rather than as
`(injectiveResolution M).cochainComplex`, and with `ComplexShape.embeddingUpNat.f n = n` supplied
by `ComplexShape.embeddingUpNat_f` rather than by `rfl`. The two
spellings are definitionally equal, but only at default transparency: a term that mixes them is
not type-correct at the transparency `rw` and `simp` use to match, and every rewrite in the
neighbourhood then fails with "did not find an occurrence" even though the pattern is visibly
present. Normalising the spellings is what makes the chain of rewrites go through.

`HasDerivedCategory.standard` is pinned as a local instance, as in every file of this
development; it is already baked into the types of the local cohomology objects. The module
universe equals the ring universe, as in `CohomologyWithSupportComparison`.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe vA uA vB uB u

namespace Stacks.LocalCohomology.SingleCompare

section Pieces

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B] (F : A ⥤ B) [F.Additive]

/-- In a single degree, the two comparisons between applying an additive functor degreewise and
extending a complex by zero are inverse to each other. -/
private theorem mapExtendXIso_inv {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex A c) (o : Option ι) :
    (Stacks.DerivedIndexing.mapExtendXIso F K o).inv =
      (Stacks.DerivedIndexing.mapExtendXIsoSymm F K o).hom := by
  cases o with
  | some a => rfl
  | none => exact (F.map_isZero (HomologicalComplex.extend.isZero_X K rfl)).eq_of_src _ _

/-- The two comparisons between applying an additive functor degreewise and extending a complex
by zero along an embedding of complex shapes are inverse to each other. -/
private theorem mapExtendIso_inv {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex A c) :
    (Stacks.DerivedIndexing.mapExtendIso F e K).inv =
      (Stacks.DerivedIndexing.mapExtendIsoSymm F e K).hom := by
  ext i'
  exact mapExtendXIso_inv F K (e.r i')

/-- The functor induced on homotopy categories by an additive functor is the lift of the functor
on complexes on the nose: the comparison is the identity at every complex. -/
private theorem mapHomotopyCategoryFactors_hom_app {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex A c) :
    (F.mapHomotopyCategoryFactors c).hom.app K = 𝟙 _ := rfl

/-- Extension by zero on homotopy categories is the lift of extension by zero on complexes on the
nose: the comparison is the identity at every complex. -/
private theorem extendHomotopyFunctorFactors_hom_app {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (e : c.Embedding c') [e.IsRelIff]
    (K : HomologicalComplex A c) :
    (e.extendHomotopyFunctorFactors A).hom.app K = 𝟙 _ := rfl

/-- The components of the homotopy-category comparison of extension by zero with homology: at the
class of a complex it is the chain of the two factorizations through the quotient and the
homology isomorphism of the extension. -/
private theorem extendHomotopyHomologyNatIso_hom_app {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (e : c.Embedding c') [e.IsRelIff] {j : ι} {j' : ι'}
    (hj : e.f j = j') (K : HomologicalComplex A c) :
    (Stacks.DerivedIndexing.extendHomotopyHomologyNatIso (A := A) e hj).hom.app
        ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.homologyFunctor A c' j').map
          ((e.extendHomotopyFunctorFactors A).hom.app K) ≫
        (HomotopyCategory.homologyFunctorFactors A c' j').hom.app (K.extend e) ≫
        (K.extendHomologyIso e hj).hom ≫
        (HomotopyCategory.homologyFunctorFactors A c j).inv.app K := rfl

end Pieces

section Derived

/-- A functor sends a morphism equal to an identity to an identity. -/
private theorem map_eq_id_of_eq_id {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {X : C}
    {f : X ⟶ X} (h : f = 𝟙 X) : G.map f = 𝟙 _ :=
  h ▸ G.map_id X

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The chosen injective resolution of an object is isomorphic to itself by the identity in the
homotopy category: the comparison is the descent of the identity, hence homotopic to it. -/
private theorem injectiveResolution_iso_hom (M : A) :
    (injectiveResolution M).iso.hom = 𝟙 _ :=
  HomotopyCategory.eq_of_homotopy _ _ (InjectiveResolution.descIdHomotopy _ _)

/-- At the chosen injective resolution, the identification of `F.rightDerivedToHomotopyCategory`
with `F` applied to the resolution is the identity. -/
private theorem isoRightDerivedToHomotopyCategoryObj_hom (F : A ⥤ B) [F.Additive] (M : A) :
    ((injectiveResolution M).isoRightDerivedToHomotopyCategoryObj F).hom = 𝟙 _ := by
  have h1 : (F.mapHomotopyCategory (ComplexShape.up ℕ)).map (injectiveResolution M).iso.hom =
      𝟙 _ :=
    map_eq_id_of_eq_id _ (injectiveResolution_iso_hom M)
  show (F.mapHomotopyCategory (ComplexShape.up ℕ)).map (injectiveResolution M).iso.hom ≫
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).app
        (injectiveResolution M).cocomplex).hom = 𝟙 _
  rw [h1]
  exact Category.comp_id _

/-- **At the chosen injective resolution, `Rⁿ F` is the degree-`n` homology of `F` applied to the
resolution, through the factorization of homology over the homotopy category.** -/
private theorem isoRightDerivedObj_hom (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    ((injectiveResolution M).isoRightDerivedObj F n).hom =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex) := by
  have h2 : (HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) n).map
      ((injectiveResolution M).isoRightDerivedToHomotopyCategoryObj F).hom = 𝟙 _ :=
    map_eq_id_of_eq_id _ (isoRightDerivedToHomotopyCategoryObj_hom F M)
  show (HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) n).map
      ((injectiveResolution M).isoRightDerivedToHomotopyCategoryObj F).hom ≫
      ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex)).hom = _
  rw [h2]
  exact Category.id_comp _

/-- `isoRightDerivedObj_hom`, for the inverse. -/
private theorem isoRightDerivedObj_inv (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    ((injectiveResolution M).isoRightDerivedObj F n).inv =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex) := by
  have h : (injectiveResolution M).isoRightDerivedObj F n =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex) :=
    Iso.ext (isoRightDerivedObj_hom F M n)
  rw [h, Iso.app_inv]

/-- The components of the identification of an object placed in degree zero with its extended
chosen injective resolution: the comparison of the two single functors, followed by the
augmentation. -/
private theorem singleIsoResCompQh_hom_app (M : A) :
    (Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app M =
      (DerivedCategory.quotientCompQhIso A).inv.app
          ((CochainComplex.singleFunctor A 0).obj M) ≫
        DerivedCategory.Qh.map (Stacks.DerivedIndexing.resUnit.app M) := by
  rw [Stacks.DerivedFunctor.singleIsoResCompQh]
  simp only [Iso.trans_hom, NatTrans.comp_app, asIso_hom, Functor.whiskerRight_app,
    Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
  rfl

/-- **The two identifications of an object placed in degree zero with its chosen injective
resolution agree**: the one built in `Stacks.Cohomology.rightDerivedSingleIso` from the image
under `Q` of the augmentation is the component of
`Stacks.DerivedFunctor.singleIsoResCompQh`. -/
private theorem single_iso_eq (M : A) :
    (DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M ≫
        DerivedCategory.Q.map (injectiveResolution M).ι' ≫
          ((DerivedCategory.quotientCompQhIso A).app
            (injectiveResolution M).cochainComplex).inv =
      (Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app M := by
  rw [singleIsoResCompQh_hom_app, Stacks.DerivedIndexing.resUnit_app,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.app_inv, DerivedCategory.quotientCompQhIso_inv_naturality]
  rfl

/-- The components of the inverse of `Stacks.DerivedFunctor.resCompUnitIso` are the inverses of
the components of the unit of the derived functor at the extended chosen resolutions. -/
private theorem resCompUnitIso_inv_app (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (M : A) :
    (Stacks.DerivedFunctor.resCompUnitIso F RF α hres).inv.app M =
      @CategoryTheory.inv _ _ _ _ (α.app (Stacks.DerivedIndexing.resH.obj M))
        (Stacks.DerivedFunctor.isIso_unit_app_resH_obj F RF α hres M) := by
  have h : ∀ X, IsIso ((Functor.whiskerLeft
      (Stacks.DerivedIndexing.resH (C := A)) α).app X) := fun X ↦
    Stacks.DerivedFunctor.isIso_unit_app_resH_obj F RF α hres X
  have : IsIso (Functor.whiskerLeft (Stacks.DerivedIndexing.resH (C := A)) α) :=
    NatIso.isIso_of_isIso_app _
  rw [Stacks.DerivedFunctor.resCompUnitIso, asIso_inv, NatIso.isIso_inv_app]
  rfl

/-- The components of the first step of `Stacks.DerivedIndexing.rightDerivedIsoRes`, with the
identity comparison of extension by zero on homotopy categories removed. -/
private theorem nStep₁_inv_app (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (Stacks.DerivedIndexing.nStep₁ F n).inv.app M =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).hom.app
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).extend ComplexShape.embeddingUpNat) ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex) := by
  have h3 : (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
      ((ComplexShape.embeddingUpNat.extendHomotopyFunctorFactors B).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex)) = 𝟙 _ :=
    map_eq_id_of_eq_id _ (extendHomotopyFunctorFactors_hom_app ComplexShape.embeddingUpNat _)
  have key := extendHomotopyHomologyNatIso_hom_app (A := B)
    ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution M).cocomplex)
  rw [h3] at key
  exact key.trans (Category.id_comp _)

/-- **A closed form for the inverse components of
`Stacks.DerivedIndexing.rightDerivedIsoRes`**: the comparison of `F` applied to the extended
chosen resolution with the extension of `F` applied to it, followed by the homology isomorphism
of the extension, read through the factorizations of homology over the homotopy category. -/
private theorem rightDerivedIsoRes_inv_app (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app M =
      (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
            (Stacks.DerivedIndexing.mapExtendIso F ComplexShape.embeddingUpNat
              (injectiveResolution M).cocomplex).inv) ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).hom.app
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).extend ComplexShape.embeddingUpNat) ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex) := by
  show (Stacks.DerivedIndexing.nStep₂ F n).inv.app M ≫
      (Stacks.DerivedIndexing.nStep₁ F n).inv.app M = _
  rw [nStep₁_inv_app]
  rfl

/-- **The tails of the two comparisons agree, after the factorization of homology over the
homotopy category has been stripped off.** This is the naturality of that factorization, applied
to the comparison of `F` applied to the extended chosen resolution with the extension of `F`
applied to it. -/
private theorem tail_core (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat)) ≫
      (Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app M =
    (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
        (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat
          (injectiveResolution M).cocomplex).hom ≫
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
      ((injectiveResolution M).isoRightDerivedObj F n).inv := by
  rw [rightDerivedIsoRes_inv_app, isoRightDerivedObj_inv, ← mapExtendIso_inv]
  exact NatIso.naturality_1_assoc _ _ _

/-- **The tails of the two comparisons agree.** The degree-`n` cohomology of `F` applied to the
extended chosen resolution, read in the derived category, is `Rⁿ F` of the object, computed the
same way by either route. -/
private theorem tail_eq (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))) ≫
      (Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app M =
    (DerivedCategory.homologyFunctor B (n : ℤ)).map
        ((DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))) ≫
      (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat)) ≫
      (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
        (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat
          (injectiveResolution M).cocomplex).hom ≫
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
      ((injectiveResolution M).isoRightDerivedObj F n).inv :=
  (DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj_assoc B
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))
      (n : ℤ) ((Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app M)).trans
    (congrArg (fun t ↦ (DerivedCategory.homologyFunctor B (n : ℤ)).map
          ((DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))) ≫
        (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat)) ≫ t)
      (tail_core F M n))

/-- **The object-level and the natural comparison of `Hⁿ(RF(M[0]))` with `Rⁿ F (M)` agree.**
`Stacks.Cohomology.rightDerivedSingleIso`, built at a single object from the chosen injective
resolution, is the component at that object of
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`. The object-level
isomorphism is therefore natural in the object, which its construction does not show. -/
private theorem natIso_app_eq (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (M : A) (n : ℕ) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF α hres n).app M =
      Stacks.Cohomology.rightDerivedSingleIso F RF α hres M n := by
  refine Iso.ext ?_
  have hL : ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        F RF α hres n).app M).hom =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (RF.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app M)) ≫
        (DerivedCategory.homologyFunctor B (n : ℤ)).map
          ((Stacks.DerivedFunctor.resCompUnitIso F RF α hres).inv.app M) ≫
        ((DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))) ≫
          (Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app M) := by
    show (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (RF.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app M)) ≫
        𝟙 _ ≫
        (DerivedCategory.homologyFunctor B (n : ℤ)).map
          ((Stacks.DerivedFunctor.resCompUnitIso F RF α hres).inv.app M) ≫
        𝟙 _ ≫
        (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))) ≫
        (Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app M = _
    rw [Category.id_comp, Category.id_comp]
  have hR : (Stacks.Cohomology.rightDerivedSingleIso F RF α hres M n).hom =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (RF.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M ≫
              DerivedCategory.Q.map (injectiveResolution M).ι' ≫
              ((DerivedCategory.quotientCompQhIso A).app
                (injectiveResolution M).cochainComplex).inv) ≫
            (@CategoryTheory.inv _ _ _ _
              (α.app (Stacks.DerivedIndexing.resH.obj M))
              (Stacks.DerivedFunctor.isIso_unit_app_resH_obj F RF α hres M)) ≫
            DerivedCategory.Qh.map
              (𝟙 ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  ((injectiveResolution M).cocomplex.extend
                    ComplexShape.embeddingUpNat)))) ≫
            (DerivedCategory.quotientCompQhIso B).hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat))) ≫
        (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat)) ≫
        (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
          (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat
            (injectiveResolution M).cocomplex).hom ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
        ((injectiveResolution M).isoRightDerivedObj F n).inv := rfl
  have hW : (DerivedCategory.homologyFunctor B (n : ℤ)).map
      (DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((injectiveResolution M).cocomplex.extend
            ComplexShape.embeddingUpNat))))) = 𝟙 _ := by
    simp only [CategoryTheory.Functor.map_id]
  rw [hL.trans (congrArg (fun t ↦ (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (RF.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app M)) ≫
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        ((Stacks.DerivedFunctor.resCompUnitIso F RF α hres).inv.app M) ≫ t)
    (tail_eq F M n)), hR, single_iso_eq, resCompUnitIso_inv_app]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  refine congrArg (fun t ↦ _ ≫ _ ≫ t) ?_
  refine Eq.trans (Category.id_comp _).symm ?_
  exact congrArg (fun t ↦ t ≫ _) hW.symm

end Derived

end Stacks.LocalCohomology.SingleCompare

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A]

/-- **Local cohomology with support in `T` is the classical right derived functor of supported
sections, naturally in the module.** The degree-`n` local cohomology with support in `T` of a
module placed in degree zero, as a functor of that module, is Mathlib's `n`-th right derived
functor of `T`-supported sections.

The left-hand side is written as the composite of the degree-zero single functor, the total right
derived functor of supported sections and the degree-`n` cohomology functor, whose value at `M`
is `localCohomologyWithSupportIn A T (M[0]) n` by definition. Its component at a module is the
object-level comparison `localCohomologyWithSupportInIsoRightDerived`, which is
`localCohomologyWithSupportInRightDerivedNatIso_app`. -/
def localCohomologyWithSupportInRightDerivedNatIso (T : Set (PrimeSpectrum A)) (n : ℕ) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        derivedSectionsWithSupportIn.{u, u} A T ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) ≅
      (sectionsWithSupportInFunctor.{u, u} A T).rightDerived n :=
  letI : EnoughInjectives (ModuleCat.{u} A) := ModuleCat.enoughInjectives A
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (sectionsWithSupportInFunctor.{u, u} A T)
    (derivedSectionsWithSupportIn.{u, u} A T)
    (derivedSectionsWithSupportInUnit.{u, u} A T)
    (fun K ↦ by
      obtain ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨J, q, hJ, hq⟩)
    n

/-- The component of `Stacks.LocalCohomology.localCohomologyWithSupportInRightDerivedNatIso` at a
module is the object-level comparison
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoRightDerived`. -/
theorem localCohomologyWithSupportInRightDerivedNatIso_app (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (n : ℕ) :
    (localCohomologyWithSupportInRightDerivedNatIso A T n).app M =
      localCohomologyWithSupportInIsoRightDerived A T M n :=
  let : EnoughInjectives (ModuleCat.{u} A) := ModuleCat.enoughInjectives A
  Stacks.LocalCohomology.SingleCompare.natIso_app_eq
    (sectionsWithSupportInFunctor.{u, u} A T)
    (derivedSectionsWithSupportIn.{u, u} A T)
    (derivedSectionsWithSupportInUnit.{u, u} A T)
    (fun K ↦ by
      obtain ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨J, q, hJ, hq⟩)
    M n

variable [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)

/-- **The two models of local cohomology agree over a Noetherian ring, naturally in the
module.** The degree-`i` local cohomology with support in the closed set `V(I)`, computed as the
total right derived functor of `V(I)`-supported sections, is the degree-`i` local cohomology in
the coreflection model of Stacks 0A6Q, as isomorphic functors of the module.

The comparison is the canonical map of Stacks 0A6U, a natural transformation of endofunctors of
`D(A)`, which is a natural isomorphism over a Noetherian ring by Stacks 0955; the isomorphism
below is that natural isomorphism whiskered with the degree-zero single functor and the degree-`i`
cohomology functor. -/
def localCohomologyModelsNatIso (i : ℤ) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        derivedSectionsWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A)) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ≅
      DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        localCohomologyDerived.{u, u} A I hI ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i :=
  have : IsIso (compareSectionsWithSupportLocalCohomology.{u, u} A I hI) :=
    isIso_compareSectionsWithSupportLocalCohomology.{u, u} A I hI
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
    (Functor.isoWhiskerRight (asIso (compareSectionsWithSupportLocalCohomology.{u, u} A I hI))
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i))

/-- The component of `Stacks.LocalCohomology.localCohomologyModelsNatIso` at a module is the
object-level comparison
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`. -/
theorem localCohomologyModelsNatIso_app (M : ModuleCat.{u} A) (i : ℤ) :
    (localCohomologyModelsNatIso A I hI i).app M =
      localCohomologyWithSupportInIsoLocalCohomologyModule A I hI M i :=
  Iso.ext rfl

/-- **The right derived functors of supported sections are the local cohomology functors.** Over
a Noetherian ring, with `I` a finitely generated ideal, Mathlib's `n`-th right derived functor of
`V(I)`-supported sections is the `n`-th local cohomology functor of the coreflection model of
Stacks 0A6Q, as isomorphic functors on `ModuleCat A`.

This is the composite of the two comparisons above, and it is the form in which the right-hand
side of the degreewise comparison of Stacks 0A6T and Stacks 0DWR is functorial in the module: an
inverse limit over a tower `n ↦ M/IⁿM` of modules can be transported along it. -/
def sectionsWithSupportRightDerivedIsoLocalCohomologyNatIso (n : ℕ) :
    (sectionsWithSupportInFunctor.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))).rightDerived
        n ≅
      DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        localCohomologyDerived.{u, u} A I hI ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) :=
  (localCohomologyWithSupportInRightDerivedNatIso A
      (PrimeSpectrum.zeroLocus (I : Set A)) n).symm ≪≫
    localCohomologyModelsNatIso A I hI (n : ℤ)

/-- The component of
`Stacks.LocalCohomology.sectionsWithSupportRightDerivedIsoLocalCohomologyNatIso` at a module is
the composite of the two object-level comparisons of
`StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison`. -/
theorem sectionsWithSupportRightDerivedIsoLocalCohomologyNatIso_app
    (M : ModuleCat.{u} A) (n : ℕ) :
    (sectionsWithSupportRightDerivedIsoLocalCohomologyNatIso A I hI n).app M =
      (localCohomologyWithSupportInIsoRightDerived A
          (PrimeSpectrum.zeroLocus (I : Set A)) M n).symm ≪≫
        localCohomologyWithSupportInIsoLocalCohomologyModule A I hI M (n : ℤ) := by
  show ((localCohomologyWithSupportInRightDerivedNatIso A
        (PrimeSpectrum.zeroLocus (I : Set A)) n).app M).symm ≪≫
      (localCohomologyModelsNatIso A I hI (n : ℤ)).app M = _
  rw [localCohomologyWithSupportInRightDerivedNatIso_app, localCohomologyModelsNatIso_app]

end Stacks.LocalCohomology

end

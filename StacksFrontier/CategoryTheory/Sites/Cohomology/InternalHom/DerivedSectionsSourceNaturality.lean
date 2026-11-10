module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsFromAKFlatSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality
public import StacksFrontier.CategoryTheory.CommutingSquares
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.CommutingSquares

/-! # Naturality of Stacks 08JA in its contravariant variable

Let `(C, O)` be a ringed site. Stacks 08JA identifies the degree-zero global hypercohomology of
the derived internal Hom `RSheafHom(L, M)` with the group of morphisms `L ⟶ M` of `D(O)`,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`. This file proves that
identification natural in `L`, for an **arbitrary** morphism of `D(O)`: a morphism `u : L' ⟶ L`
acts on the left-hand side through the contravariant functoriality of the derived internal Hom
and on the right-hand side by precomposition.

## Main results

* `Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso_naturality_complexMap`:
  the comparison of Stacks 07A5 identifying the global sections of a K-injective complex with its
  derived global sections is natural for morphisms of complexes.
* `RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_source`:
  the naturality at the classes of complexes, for the class of a morphism of complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_source`:
  the naturality at the classes of a K-flat source and a K-injective target, for an arbitrary
  morphism of `D(O)` between the classes of the two K-flat complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap`:
  **Stacks 08JA, naturality in the source variable**, for arbitrary objects and an arbitrary
  morphism of `D(O)`.

## Implementation notes

Two of the unfoldings below also exist on the main line, under the names this file's carry
without a suffix:
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply` of
`…InternalHom.GlobalDerivedHomLocalization` and
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply` of
`…InternalHom.GlobalDerivedHomTransport`. The copies here are suffixed rather than retired in
favour of those: importing either module here adds 49 modules of instances, which measurably
turns five green modules of this cluster red with heartbeat timeouts in proofs that are not
edited. The second of the two also differs — the main-line statement brackets its conjugation to
the left, as `Linear.homCongr` produces it — which is what the `_assoc` suffix records.

The identification of Stacks 08JA is the composite of four comparisons: the choice of a K-flat
representative of the source and of a K-injective representative of the target, the K-injective
target computing the derived internal Hom (Stacks 0A97), global sections computing derived
global sections on the K-injective complex `SheafHom(A, I)` (Stacks 07A5), and Stacks 0A94. Each
of the last three is natural for morphisms of *complexes* — the third because
`globalSectionsKInjectiveIso` is a composite of the unit of a derived functor with canonical
identifications, and the fourth by
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`.

Extending that to an arbitrary morphism of `D(O)` is done in two steps, and neither needs a
naturality of the choice of representatives.

*Between classes of K-flat complexes*, the clause is closed under composition and under taking
the inverse of an invertible morphism, so by the calculus of fractions
(`DerivedCategory.right_fac`) it is enough to know it for the class of a morphism of complexes:
the given morphism is a right fraction whose apex is replaced by a K-flat resolution of it
(Stacks 06YS), which is the argument of
`AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal_natural_left` for Stacks 0A99.

*For arbitrary objects*, the comparison `derivedSheafHomObjectsModelIso` with the chosen
representatives is itself dinatural — `derivedSheafHomObjectsModelIso_natural_source` — carrying
a morphism `u : L' ⟶ L` to the morphism of the classes of the chosen K-flat representatives that
`u` conjugates to. So the general clause follows from the K-flat one at that conjugate, with no
clause for the comparison isomorphisms themselves.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.Cohomology.ModuleSections

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Global sections computing derived global sections on a K-injective complex is natural.**
The comparison `globalSectionsKInjectiveIso` of Stacks 07A5 is the unit of the derived functor
read through canonical identifications, and each of those four pieces is natural, so the
comparison is natural for morphisms of complexes. -/
lemma globalSectionsKInjectiveIso_naturality_complexMap
    {J J' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective] [J'.IsKInjective] (ψ : J ⟶ J') :
    DerivedCategory.Q.map (RingedSite.globalSectionsComplexMap X ψ) ≫
        (globalSectionsKInjectiveIso X J').hom =
      (globalSectionsKInjectiveIso X J).hom ≫
        (derivedModuleGlobalSections X).map (DerivedCategory.Q.map ψ) := by
  exact CategoryTheory.square_comp
    ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.naturality _)
    (CategoryTheory.square_comp
      (DerivedCategory.Qh.map_commSq
        ⟨((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.naturality
          ψ⟩).w
      (CategoryTheory.square_comp ((derivedModuleGlobalSectionsUnit X).naturality
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ψ))
        ((derivedModuleGlobalSections X).map_commSq
          ⟨(DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.naturality
              ψ⟩).w))

end Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Naturality at the classes of complexes -/

/-- Stacks 08JA on a K-injective internal Hom complex is the three comparisons it is built
from.

`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomLocalization` is the
same statement with the same `rfl` proof. This copy is kept, under a name of its own, because
importing that module here adds 49 further modules of instances and that measurably turns five
green modules of this cluster red with heartbeat timeouts in proofs it does not touch. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply_comparisons
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I x =
      sheafHomGlobalHomologyEquivDerivedCategoryHom X A I
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
            (globalSectionsComplex X (sheafHomComplex X A I).obj)).hom
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
              (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) x)) := rfl

/-- **Stacks 08JA on a K-injective internal Hom complex is natural in the source**, for the
class of a morphism of complexes. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_source
    {A A' I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I).obj).IsKInjective] (c : A' ⟶ A)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A' I
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map c).op).app
              (DerivedCategory.Q.obj I))) x) =
      DerivedCategory.Q.map c ≫
        derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I x := by
  have hcomp : ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map c).op).app
        (DerivedCategory.Q.obj I) ≫ (derivedSheafHomComparison X A' I).hom =
      (derivedSheafHomComparison X A I).hom ≫
        DerivedCategory.Q.map (homMap X c (𝟙 I)) := by
    simpa using derivedSheafHomComparison_naturality X c (𝟙 I)
  have s1 := ((derivedModuleGlobalSections X).map_commSq ⟨hcomp⟩).w
  have s2 : (derivedModuleGlobalSections X).map
          (DerivedCategory.Q.map (homMap X c (𝟙 I))) ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I).obj)).inv =
      (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv ≫
        DerivedCategory.Q.map
          (globalSectionsComplexMap X (homMap X c (𝟙 I))) := by
    rw [Iso.comp_inv_eq, Category.assoc, globalSectionsKInjectiveIso_naturality_complexMap,
      Iso.inv_hom_id_assoc]
  have hfac := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
    (globalSectionsComplexMap X (homMap X c (𝟙 I)))
  have s3 := ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map_commSq
    ⟨CategoryTheory.square_comp s1 s2⟩).w
  -- `key` is not stated by hand: the two glued squares read on `x` already are the equation
  -- wanted, and its instance arguments are the ones instance search picks there, which a
  -- hand-written copy does not reproduce.  The two normalizations do not commute either —
  -- rewriting the homology functor to `homologyMap` first respells the object the composite
  -- passes through, and `ConcreteCategory.comp_apply` then no longer fires on it.
  have key := ConcreteCategory.congr_hom (CategoryTheory.square_comp s3 hfac) x
  simp only [Category.assoc, ConcreteCategory.comp_apply] at key
  simp only [HomologicalComplex.homologyFunctor_map] at key
  have h94 := sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality X c (𝟙 I)
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
        (globalSectionsComplex X (sheafHomComplex X A I).obj)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) x))
  rw [derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply_comparisons,
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply_comparisons]
  simp only [Iso.app_hom]
  rw [key]
  -- `rw [h94]` cannot be used: the class `0A94` is stated for an element of `C.homology 0` and
  -- the element here is typed at `(homologyFunctor _ _ 0).obj C`, so the two sides agree only
  -- up to unfolding, which `rw`'s syntactic matching does not do.
  refine h94.trans ?_
  simp

/-! ### Extension to an arbitrary morphism between classes of K-flat complexes -/

/-- The source-naturality clause of Stacks 08JA at the classes of two K-flat complexes, for a
given morphism of `D(O)` between them. -/
private def SourceNatural
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    (ρ : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A) : Prop :=
  ∀ x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u),
    derivedSheafHomGlobalSectionsEquivOfKFlat X A' I hA'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map ρ.op).app (DerivedCategory.Q.obj I))) x) =
      ρ ≫ derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x

/-- The clause holds for the class of a morphism of complexes. -/
private lemma sourceNatural_Q_map
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    (c : A' ⟶ A) : SourceNatural X I hA hA' (DerivedCategory.Q.map c) := by
  have : ((sheafHomComplex X A I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X A I hA
  have : ((sheafHomComplex X A' I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X A' I hA'
  intro x
  exact derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_source X c x

/-- The clause is closed under composition. -/
private lemma sourceNatural_comp
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    {A A' A'' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    (hA'' : Stacks.SheafOfModules.IsKFlat X.O A'')
    {ρ₁ : DerivedCategory.Q.obj A'' ⟶ DerivedCategory.Q.obj A'}
    {ρ₂ : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A}
    (h₁ : SourceNatural X I hA' hA'' ρ₁) (h₂ : SourceNatural X I hA hA' ρ₂) :
    SourceNatural X I hA hA'' (ρ₁ ≫ ρ₂) := by
  intro x
  have hsplit : ((derivedSheafHomBifunctor X).map (ρ₁ ≫ ρ₂).op).app
        (DerivedCategory.Q.obj I) =
      ((derivedSheafHomBifunctor X).map ρ₂.op).app (DerivedCategory.Q.obj I) ≫
        ((derivedSheafHomBifunctor X).map ρ₁.op).app (DerivedCategory.Q.obj I) := by
    rw [op_comp, Functor.map_comp, NatTrans.comp_app]
  rw [hsplit, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply, h₁, h₂,
    Category.assoc]

/-- The clause is closed under inverting an invertible morphism. -/
private lemma sourceNatural_inv
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    {ρ : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A} [IsIso ρ]
    (h : SourceNatural X I hA hA' ρ) : SourceNatural X I hA' hA (inv ρ) := by
  intro y
  have hid : ((derivedSheafHomBifunctor X).map (inv ρ).op).app (DerivedCategory.Q.obj I) ≫
      ((derivedSheafHomBifunctor X).map ρ.op).app (DerivedCategory.Q.obj I) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, IsIso.hom_inv_id, op_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app]
  have hround : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map ρ.op).app (DerivedCategory.Q.obj I)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map (inv ρ).op).app
              (DerivedCategory.Q.obj I))) y) = y := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp, hid,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hx := h ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((derivedModuleGlobalSections X).map
      (((derivedSheafHomBifunctor X).map (inv ρ).op).app (DerivedCategory.Q.obj I))) y)
  rw [hround] at hx
  rw [hx, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- **The clause holds for an arbitrary morphism of `D(O)` between the classes of two K-flat
complexes.** The morphism is written as a right fraction whose apex is replaced by a K-flat
resolution of it, and the clause is closed under composition and under inverses of
isomorphisms. -/
private lemma sourceNatural_of_kFlat
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    (ρ : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A) :
    SourceNatural X I hA hA' ρ := by
  obtain ⟨P₀, s₀, hs₀, g₀, hfac₀⟩ := DerivedCategory.right_fac ρ
  obtain ⟨P, p, hP, hp⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X P₀
  have := hs₀
  have : QuasiIso p := hp
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  have hsr : IsIso (DerivedCategory.Q.map (p ≫ s₀)) := by
    rw [Functor.map_comp]; infer_instance
  have hρ : inv (DerivedCategory.Q.map (p ≫ s₀)) ≫
      DerivedCategory.Q.map (p ≫ g₀) = ρ := by
    -- Transposed first: `Functor.map_comp` under an `inv` would leave its `IsIso` argument
    -- behind, and `rw` refuses the resulting motive.
    rw [IsIso.inv_comp_eq, hfac₀, Functor.map_comp, Functor.map_comp, Category.assoc,
      IsIso.hom_inv_id_assoc]
  rw [← hρ]
  exact sourceNatural_comp X I hA hP hA'
    (sourceNatural_inv X I hA' hP (sourceNatural_Q_map X I hA' hP (p ≫ s₀)))
    (sourceNatural_Q_map X I hA hP (p ≫ g₀))

/-- **Stacks 08JA at a K-flat source and a K-injective target is natural in the source**, for an
arbitrary morphism of `D(O)` between the classes of two K-flat complexes. This is the clause
`SourceNatural` written out; it is the companion of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_target` and,
unlike the model-based
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap`,
it is stated at the given complexes, which is what a consumer comparing the two forms of
Stacks 08JA needs.

Unlike the target clause this one needs the calculus of fractions: a morphism between the classes
of two complexes that are not K-injective is not the class of a morphism of complexes. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_source
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    (ρ : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A' I hA'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map ρ.op).app (DerivedCategory.Q.obj I))) x) =
      ρ ≫ derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x :=
  sourceNatural_of_kFlat X I hA hA' ρ x

/-! ### Naturality for arbitrary objects -/

/-- Stacks 08JA is the comparison with the chosen representatives followed by Stacks 08JA at
those representatives.

This is `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomTransport` with the
conjugation bracketed to the right: that one states it as `Linear.homCongr` produces it,
`(e.inv ≫ f) ≫ e'.hom`, and the consumers in this cluster want `e.inv ≫ f ≫ e'.hom`. -/
theorem derivedSheafHomGlobalSectionsEquiv_apply_assoc
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L M x =
      (kFlatModelIso X L).inv ≫
        derivedSheafHomGlobalSectionsEquivOfKFlat X (kFlatModel X L) (kInjectiveModel X M)
            (isKFlat_kFlatModel X L)
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              ((derivedModuleGlobalSections X).map
                (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
                  (kInjectiveModelIso X M)).hom) x) ≫
          (kInjectiveModelIso X M).hom := by
  rw [← Category.assoc]
  rfl

/-- **The comparison of the derived internal Hom with the chosen representatives is dinatural in
the source.** A morphism `u : L' ⟶ L` of `D(O)` is carried to the morphism of the classes of the
chosen K-flat representatives that `u` conjugates to. -/
private lemma derivedSheafHomObjectsModelIso_natural_source
    {L L' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : L' ⟶ L) :
    ((derivedSheafHomBifunctor X).map u.op).app M ≫
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
          (kInjectiveModelIso X M)).hom =
      (derivedSheafHomObjectsModelIso X (kFlatModelIso X L) (kInjectiveModelIso X M)).hom ≫
        ((derivedSheafHomBifunctor X).map
          ((kFlatModelIso X L').hom ≫ u ≫ (kFlatModelIso X L).inv).op).app
            (DerivedCategory.Q.obj (kInjectiveModel X M)) := by
  have hcomp : ((kFlatModelIso X L').hom ≫ u ≫ (kFlatModelIso X L).inv) ≫
      (kFlatModelIso X L).hom = (kFlatModelIso X L').hom ≫ u := by
    simp
  have s1 : ((derivedSheafHomBifunctor X).map u.op).app M ≫
        ((derivedSheafHomBifunctor X).map (kFlatModelIso X L').hom.op).app M =
      ((derivedSheafHomBifunctor X).map (kFlatModelIso X L).hom.op).app M ≫
        ((derivedSheafHomBifunctor X).map
          ((kFlatModelIso X L').hom ≫ u ≫ (kFlatModelIso X L).inv).op).app M := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, hcomp]
  have s2 := (((derivedSheafHomBifunctor X).map
    ((kFlatModelIso X L').hom ≫ u ≫ (kFlatModelIso X L).inv).op).naturality
      (kInjectiveModelIso X M).inv).symm
  exact CategoryTheory.square_comp s1 s2

/-- **Stacks 08JA, naturality in the source variable.** For objects `L'`, `L`, `M` of `D(O)` and
an arbitrary morphism `u : L' ⟶ L`, the identification of the degree-zero global
hypercohomology of `RSheafHom(L, M)` with `Hom_{D(O)}(L, M)` carries the contravariant
functoriality of the derived internal Hom to precomposition with `u`. -/
@[stacks 08JA "global sections, naturality in the source"]
theorem derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (u : L' ⟶ L)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L' M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map u.op).app M)) x) =
      u ≫ derivedSheafHomGlobalSectionsEquiv X L M x := by
  have hx : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
            (kInjectiveModelIso X M)).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map u.op).app M)) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map
            ((kFlatModelIso X L').hom ≫ u ≫ (kFlatModelIso X L).inv).op).app
              (DerivedCategory.Q.obj (kInjectiveModel X M))))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
              (kInjectiveModelIso X M)).hom) x) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      derivedSheafHomObjectsModelIso_natural_source, Functor.map_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]
  have hnat := sourceNatural_of_kFlat X (kInjectiveModel X M) (isKFlat_kFlatModel X L)
    (isKFlat_kFlatModel X L') ((kFlatModelIso X L').hom ≫ u ≫ (kFlatModelIso X L).inv)
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
          (kInjectiveModelIso X M)).hom) x)
  -- The two instances of `derivedSheafHomGlobalSectionsEquiv_apply_assoc` are supplied with their
  -- arguments: left to `rw` to find, unifying its pattern against terms of this size exhausts
  -- the elaborator's budget.
  have e' := derivedSheafHomGlobalSectionsEquiv_apply_assoc X L' M
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (((derivedSheafHomBifunctor X).map u.op).app M)) x)
  have e := derivedSheafHomGlobalSectionsEquiv_apply_assoc X L M x
  -- `hx` is carried into the K-flat clause by `congrArg` rather than by `rw`: every rewrite
  -- whose pattern is one of these hypercohomology classes exhausts the elaborator's budget,
  -- while congruence and transitivity cost nothing.
  have step := (congrArg (fun z => derivedSheafHomGlobalSectionsEquivOfKFlat X (kFlatModel X L')
    (kInjectiveModel X M) (isKFlat_kFlatModel X L') z) hx).trans hnat
  have h1 := congrArg
    (fun g => (kFlatModelIso X L').inv ≫ g ≫ (kInjectiveModelIso X M).hom) step
  have h2 := congrArg (fun g => u ≫ g) e
  refine e'.trans (h1.trans (Eq.trans ?_ h2.symm))
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.RingedSite

end

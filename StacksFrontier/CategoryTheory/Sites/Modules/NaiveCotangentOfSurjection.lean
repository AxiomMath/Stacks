module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquareHomotopy
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPresentationComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquareIdentity
public import StacksFrontier.CategoryTheory.Sites.Modules.CorepresentingConormalSequence
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The naive cotangent complex of a surjection of sheaves of rings

Let `a : A ⟶ B` be a locally surjective morphism of sheaves of commutative rings on a site, with
kernel `I`. The constants `A ⟶ A[B]` of the canonical polynomial presentation carry `I` into
the kernel of `A[B] ⟶ B`, so they induce a map of conormal sheaves `I/I² ⟶ I'/(I')²`; placed
in degree `-1` this is a chain map

`η : (I/I²)[1] ⟶ NL_{B/A}`.

It is a quasi-isomorphism: `NL_{B/A}` of a surjection is `I/I²` placed in degree `-1`
(Stacks 00S4 for sheaves). This file constructs `η` and proves that it becomes an isomorphism
in the derived category.

The argument does not compute cohomology sheaves. It compares `NL_{B/A}` with the naive
cotangent complex `NL(α)` of the presentation of `B` over `A` whose generators are the local
sections of `A` themselves, `A[A] ⟶ A ⟶ B`: by **Stacks 08TY** the comparison
`NL(α) ⟶ NL_{B/A}` is a quasi-isomorphism, and the constants `A ⟶ A[A]` and the evaluation
`A[A] ⟶ A` give chain maps `(I/I²)[1] ⟶ NL(α) ⟶ (I/I²)[1]` composing to the identity one way
and, by the homotopy of **Stacks 00S1 (2)** between the two maps of presentations `𝟙` and
`A[A] ⟶ A ⟶ A[A]`, homotopic to the identity the other way.

## Main definitions

* `Stacks.SheafOfModules.conormalToNaiveCotangentComplex`: the chain map `η`.

## Main results

* `Stacks.SheafOfModules.isIso_Q_map_conormalToNaiveCotangentComplex`: `η` is an isomorphism in
  the derived category.

## References

* [Stacks Project, Tag 00S4](https://stacks.math.columbia.edu/tag/00S4)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)
open Stacks.Sites.Conormal (conormalSheaf conormalSequence conormalSheafMapOfSquare
  tensorSheafMapOfSquare conormalClass tensorDifferential kernelIdeal toAssociatedModule)
open Stacks.Sites.FreeAlgebra (freeAlgebraSheaf freeAlgebraSheafCoefficientMap
  underlyingPresheaf canonicalPresentation)

universe t u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [HasWeakSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The sheafification unit sends `0` to `0`. -/
theorem toAssociatedModule_zero (A B : Sheaf J CommRingCat.{u}) (φ : A ⟶ B)
    [Presheaf.IsLocallySurjective J φ.hom]
    (M : PresheafOfModules.{u} (Stacks.Sites.Conormal.quotientPresheaf φ.hom ⋙
      forget₂ CommRingCat RingCat)) (X : Cᵒᵖ) :
    toAssociatedModule.{u, u, u, u} J A B φ M X 0 = 0 := by
  have h := Stacks.Sites.Conormal.toAssociatedModule_add.{u, u, u, u} J A B φ M X 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

section Eta

variable (A B : Sheaf J CommRingCat.{u}) (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J a.hom] in
/-- The constants `A ⟶ A[B]` lie over `B`: followed by the canonical presentation they are
`a`. -/
theorem coefficientMap_comp_canonicalPresentation :
    freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B) ≫
        canonicalPresentation J A B a = a ≫ 𝟙 B :=
  (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap J A B a).trans
    (Category.comp_id a).symm

/-- The map of conormal sheaves `I/I² ⟶ I'/(I')²` induced by the constants `A ⟶ A[B]`, from
the conormal sheaf of `a` to the degree `-1` term of `NL_{B/A}`. -/
noncomputable def conormalToNaiveCotangentConormal :
    conormalSheaf.{u, u, u, u} J A B a ⟶
      (canonicalConormalSequence.{u, u, u, u} J A B a).X₁ :=
  conormalSheafMapOfSquare.{u, u, u, u} J A _ B B a (canonicalPresentation J A B a)
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) (𝟙 B)
    (coefficientMap_comp_canonicalPresentation J A B a)

/-- On the class of a local section `x` of `I`, the map is the class of the constant `x`. -/
theorem conormalToNaiveCotangentConormal_conormalClass {R : Sheaf J CommRingCat.{u}}
    (r : R ⟶ A) (X : Cᵒᵖ) (x : kernelIdeal a.hom X) :
    (conormalToNaiveCotangentConormal J A B a).val.app X
        (conormalClass.{u, u, u, u} J R A B r a X x) =
      conormalClass.{u, u, u, u} J A _ B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a) X
        ⟨(freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom.app X x,
          Stacks.Sites.Conormal.kernelIdeal_le_comap_square a.hom
            (canonicalPresentation J A B a).hom
            (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom
            (𝟙 B : B ⟶ B).hom
            (Stacks.Sites.Conormal.hom_of_square
              (coefficientMap_comp_canonicalPresentation J A B a)) X x.2⟩ :=
  Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J R A A _ B B r
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) a
    (canonicalPresentation J A B a)
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) (𝟙 B)
    (coefficientMap_comp_canonicalPresentation J A B a) X x

omit [HasWeakSheafify J CommRingCat.{u}] in
  /-- The constants have no differential, for any presentation `P ⟶ B` over `A`. -/
  private theorem conormalSheafMapOfSquare_comp_conormalSequence_f {P : Sheaf J CommRingCat.{u}}
    (c : A ⟶ P) (φ : P ⟶ B) [Presheaf.IsLocallySurjective J φ.hom] (h : c ≫ φ = a ≫ 𝟙 B) :
    conormalSheafMapOfSquare.{u, u, u, u} J A P B B a φ c (𝟙 B) h ≫
      (conormalSequence.{u, u, u, u} J A P B c φ).f = 0 := by
  apply Stacks.Sites.Conormal.sheafify_hom_ext.{u, u, u, u} J A B a
    (Stacks.Sites.Conormal.conormalPresheaf a.hom)
  intro X cl
  obtain ⟨x, rfl⟩ := (kernelIdeal a.hom X).toCotangent_surjective cl
  show (conormalSequence.{u, u, u, u} J A P B c φ).f.val.app X
      ((conormalSheafMapOfSquare.{u, u, u, u} J A P B B a φ c (𝟙 B) h).val.app X
        (conormalClass.{u, u, u, u} J A A B (𝟙 A) a X x)) =
    (0 : conormalSheaf.{u, u, u, u} J A B a ⟶ _).val.app X
      (conormalClass.{u, u, u, u} J A A B (𝟙 A) a X x)
  rw [Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A A A P B B
    (𝟙 A) c a φ c (𝟙 B) h X x]
  refine (Stacks.Sites.Conormal.conormalSequence_f_class.{u, u, u, u} J A P B c φ X _).trans ?_
  refine Eq.trans ?_ (rfl : (0 : (conormalSequence.{u, u, u, u} J A P B c φ).X₂.val.obj X) =
    (0 : conormalSheaf.{u, u, u, u} J A B a ⟶ _).val.app X _)
  show toAssociatedModule.{u, u, u, u} J P B φ
      (Stacks.Sites.Conormal.tensorPresheaf φ.hom c.hom) X
      ((1 : _ ⧸ kernelIdeal φ.hom X) ⊗ₜ[_]
        CommRingCat.KaehlerDifferential.d (f := c.hom.app X) (c.hom.app X x)) = 0
  have hd : CommRingCat.KaehlerDifferential.d (f := c.hom.app X) (c.hom.app X x) = 0 :=
    ModuleCat.Derivation.d_map (CommRingCat.KaehlerDifferential.D (c.hom.app X)) _
  simp only [hd]
  exact (congrArg _ (TensorProduct.tmul_zero _ _)).trans
    (toAssociatedModule_zero J P B φ _ X)

/-- The constants have no differential: the map of conormal sheaves induced by the constants,
followed by the conormal map of the canonical presentation, vanishes. -/
theorem conormalToNaiveCotangentConormal_comp_f :
    conormalToNaiveCotangentConormal J A B a ≫
      (canonicalConormalSequence.{u, u, u, u} J A B a).f = 0 :=
  conormalSheafMapOfSquare_comp_conormalSequence_f J A B a _ _
    (coefficientMap_comp_canonicalPresentation J A B a)

/-- **The canonical chain map `η : (I/I²)[1] ⟶ NL_{B/A}`** of a locally surjective `a`, with
`I = Ker a`: in degree `-1` it is the map of conormal sheaves induced by the constants
`A ⟶ A[B]`. -/
noncomputable def conormalToNaiveCotangentComplex :
    (CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).obj
        (conormalSheaf.{u, u, u, u} J A B a) ⟶
      naiveCotangentComplex.{u, u, u, u} J A B a :=
  letI : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  HomologicalComplex.mkHomFromSingle
    (conormalToNaiveCotangentConormal J A B a ≫
      eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u} J A B a).symm)
    (by
      rintro k hk
      obtain rfl : k = 0 := by simpa using hk.symm
      rw [naiveCotangentComplex_d_negOne_zero, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, ← Category.assoc,
        conormalToNaiveCotangentConormal_comp_f, zero_comp])

/-- In degree `-1`, `η` is the map of conormal sheaves induced by the constants. -/
theorem conormalToNaiveCotangentComplex_f_negOne :
    (conormalToNaiveCotangentComplex J A B a).f (-1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (conormalSheaf.{u, u, u, u} J A B a)).hom ≫
        conormalToNaiveCotangentConormal J A B a ≫
        eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u} J A B a).symm := by
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromSingle_f _ _

end Eta

section EtaNaturality

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable (A B : Sheaf J CommRingCat.{u}) (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom]
  (A' B' : Sheaf J CommRingCat.{u}) (a' : A' ⟶ B') [Presheaf.IsLocallySurjective J a'.hom]
  (f : A ⟶ A') (β : B ⟶ B') (hsq : a ≫ β = f ≫ a')

/-- The constants `A ⟶ A[B]` are compatible with a square: the class of `x` in `I/I²` goes to the
same class of `A'[B']`-conormal sheaf whether one first applies the constants or the square. -/
private theorem conormalToNaiveCotangentConormal_class_comp (X : Cᵒᵖ) (x : kernelIdeal a.hom X) :
    (naiveCotangentConormalMapOfSquare.{u, u, u, u} J A B a A' B' a' f β hsq).val.app X
        ((conormalToNaiveCotangentConormal J A B a).val.app X
          (conormalClass.{u, u, u, u} J A A B (𝟙 A) a X x)) =
      (conormalToNaiveCotangentConormal J A' B' a').val.app X
        ((conormalSheafMapOfSquare.{u, u, u, u} J A A' B B' a a' f β hsq.symm).val.app X
          (conormalClass.{u, u, u, u} J A A B (𝟙 A) a X x)) := by
  have e₁ := conormalToNaiveCotangentConormal_conormalClass J A B a (𝟙 A) X x
  have e₂ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A A'
    _ _ B B' (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap J A' _)
    (canonicalPresentation J A B a) (canonicalPresentation J A' B' a')
    (canonicalFreeAlgebraMapOfSquare J A A' B B' f β) β
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A' B B' a a' f β hsq) X
    ⟨(freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom.app X x,
      Stacks.Sites.Conormal.kernelIdeal_le_comap_square a.hom
        (canonicalPresentation J A B a).hom
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom
        (𝟙 B : B ⟶ B).hom
        (Stacks.Sites.Conormal.hom_of_square
          (coefficientMap_comp_canonicalPresentation J A B a)) X x.2⟩
  have e₃ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A A'
    A A' B B' (𝟙 A) (𝟙 A') a a' f β hsq.symm X x
  have e₄ := conormalToNaiveCotangentConormal_conormalClass J A' B' a' (𝟙 A') X
    ⟨f.hom.app X x, Stacks.Sites.Conormal.kernelIdeal_le_comap_square a.hom a'.hom f.hom β.hom
      (Stacks.Sites.Conormal.hom_of_square hsq.symm) X x.2⟩
  have h : (canonicalFreeAlgebraMapOfSquare J A A' B B' f β).hom.app X
      ((freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom.app X x) =
      (freeAlgebraSheafCoefficientMap J A' (underlyingPresheaf J B')).hom.app X (f.hom.app X x) :=
    congrArg (fun t : A ⟶ _ ↦ t.hom.app X x.1)
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A A' _ _ f
        (underlyingPresheafMap J B B' β))
  refine ((congrArg _ e₁).trans e₂).trans (Eq.trans ?_ ((congrArg (fun t ↦
    (conormalToNaiveCotangentConormal J A' B' a').val.app X t) e₃).trans e₄).symm)
  exact congrArg (conormalClass.{u, u, u, u} J A' _ B' (freeAlgebraSheafCoefficientMap J A' _)
    (canonicalPresentation J A' B' a') X) (Subtype.ext h)


include hsq in
/-- **`η` is natural in commutative squares of surjections**, on conormal sheaves: the constants
`A ⟶ A[B]` followed by the map `A[B] ⟶ A'[B']` of a square are `f` followed by the constants
`A' ⟶ A'[B']`. -/
theorem conormalToNaiveCotangentConormal_comp_mapOfSquare :
    conormalToNaiveCotangentConormal J A B a ≫
        naiveCotangentConormalMapOfSquare.{u, u, u, u} J A B a A' B' a' f β hsq =
      conormalSheafMapOfSquare.{u, u, u, u} J A A' B B' a a' f β hsq.symm ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (conormalToNaiveCotangentConormal J A' B' a') := by
  exact Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun X x ↦
    conormalToNaiveCotangentConormal_class_comp J A B a A' B' a' f β hsq X x)

variable {B A'} in
/-- The map of conormal sheaves `Ker a/Ker a² ⟶ Ker a'/Ker a'²` induced by a factorisation
`a = f ≫ a'` of locally surjective morphisms. -/
noncomputable def conormalMapOfFac (a' : A' ⟶ B) [Presheaf.IsLocallySurjective J a'.hom]
    (hf : a = f ≫ a') :
    conormalSheaf.{u, u, u, u} J A B a ⟶ conormalSheaf.{u, u, u, u} J A' B a' :=
  conormalSheafMapOfSquare.{u, u, u, u} J A A' B B a a' f (𝟙 B)
    (comp_id_eq_comp_of_fac J A B a A' a' f hf).symm

variable {B A'} in
/-- `η` on conormal sheaves is natural in factorisations `a = f ≫ a'`. -/
theorem conormalToNaiveCotangentConormal_comp_mapOfBase (a' : A' ⟶ B)
    [Presheaf.IsLocallySurjective J a'.hom] (hf : a = f ≫ a') :
    conormalToNaiveCotangentConormal J A B a ≫
        naiveCotangentConormalMapOfBase.{u, u, u, u} J A B a A' a' f hf =
      conormalMapOfFac J A a f a' hf ≫ conormalToNaiveCotangentConormal J A' B a' := by
  exact Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun X x ↦
    conormalToNaiveCotangentConormal_class_comp J A B a A' B a' f (𝟙 B)
      (comp_id_eq_comp_of_fac J A B a A' a' f hf) X x)

variable {B A'} in
/-- **`η` is natural in factorisations through a second surjection**: for `a = f ≫ a'` with
`a'` locally surjective, `η_a` followed by the base change `NL_{B/A} ⟶ NL_{B/A'}` of
**Stacks 08TX** is the map of conormal sheaves induced by `f`, followed by `η_{a'}`. -/
theorem conormalToNaiveCotangentComplex_comp_mapOfBase (a' : A' ⟶ B)
    [Presheaf.IsLocallySurjective J a'.hom] (hf : a = f ≫ a') :
    conormalToNaiveCotangentComplex J A B a ≫
        naiveCotangentComplexMapOfBase.{u, u, u, u} J A B a A' a' f hf =
      (CochainComplex.singleFunctor
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).map
          (conormalMapOfFac J A a f a' hf) ≫
        conormalToNaiveCotangentComplex J A' B a' := by
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    conormalToNaiveCotangentComplex_f_negOne, naiveCotangentComplexMapOfBase_f_negOne,
    conormalToNaiveCotangentComplex_f_negOne]
  show _ = ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).map _).f (-1) ≫ _
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc (conormalToNaiveCotangentConormal J A B a),
    conormalToNaiveCotangentConormal_comp_mapOfBase J A a f a' hf, Category.assoc]

include hsq in
/-- **`η` is natural in commutative squares of surjections**: `η_a` followed by the map
`NL_{B/A} ⟶ NL_{B'/A'}` of **Stacks 08TX** attached to the square is the map of conormal
sheaves of the square followed by `η_{a'}`, read through restriction of scalars along `β`. -/
theorem conormalToNaiveCotangentComplex_comp_mapOfSquare :
    conormalToNaiveCotangentComplex J A B a ≫
        naiveCotangentComplexMapOfSquare.{u, u, u, u} J A B a A' B' a' f β hsq =
      (CochainComplex.singleFunctor
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).map
          (conormalSheafMapOfSquare.{u, u, u, u} J A A' B B' a a' f β hsq.symm) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)) (ComplexShape.up ℤ)
          (-1)).inv.app (conormalSheaf.{u, u, u, u} J A' B' a') ≫
        ((_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (conormalToNaiveCotangentComplex J A' B' a') := by
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B')) :=
    hasZeroObject_of_hasTerminal_object
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    conormalToNaiveCotangentComplex_f_negOne, naiveCotangentComplexMapOfSquare_f_negOne,
    Functor.mapHomologicalComplex_map_f, conormalToNaiveCotangentComplex_f_negOne,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  show _ = ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).map _).f (-1) ≫ _
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Functor.map_comp_assoc (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)),
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Category.assoc (conormalToNaiveCotangentConormal J A B a),
    conormalToNaiveCotangentConormal_comp_mapOfSquare J A B a A' B' a' f β hsq, Category.assoc,
    Iso.inv_hom_id_assoc]

end EtaNaturality


end Stacks.SheafOfModules

namespace Stacks.Sites.Conormal

open TensorProduct

section FactorThroughBase

variable {C : Type u} [Category.{u} C]
variable {A₁ A₂ B₁ B₂ R₁ R₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂)
  (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (δ : A₁ ⟶ R₂) (β : B₁ ⟶ B₂) (ρ : R₁ ⟶ R₂)
  (hsq : (δ ≫ a₂) ≫ φ₂ = φ₁ ≫ β) (ha : ρ ≫ a₂ = a₁ ≫ (δ ≫ a₂))

include ha in
/-- A morphism of presentations factoring through the base ring of the second presentation
induces zero on relative differentials, since `d (a₂ r) = 0`. -/
theorem differentialsMapOfSquare_eq_zero_of_factor (X : Cᵒᵖ)
    (ω : (differentialsPresheaf a₁).obj X) :
    differentialsMapOfSquare (δ ≫ a₂) a₁ a₂ ρ ha X ω = 0 := by
  let := (a₁.app X).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj X)
      (Set.range (KaehlerDifferential.D (R₁.obj X) (A₁.obj X))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      show differentialsMapOfSquare (δ ≫ a₂) a₁ a₂ ρ ha X
        (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x) = 0
      rw [differentialsMapOfSquare_d]
      exact ModuleCat.Derivation.d_map (CommRingCat.KaehlerDifferential.D (a₂.app X))
        (δ.app X x)
  | zero => rw [map_zero]
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul r ω hω ih => rw [map_smulₛₗ, ih, smul_zero]

include hsq ha in
/-- The same on the scalar extensions of the differentials. -/
theorem tensorMapOfSquareₛₗ_eq_zero_of_factor (X : Cᵒᵖ)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfSquareₛₗ φ₁ φ₂ (δ ≫ a₂) β hsq a₁ a₂ ρ ha X t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul b ω =>
      refine (TensorProduct.map_tmul _ _ b ω).trans ?_
      rw [differentialsMapOfSquare_eq_zero_of_factor a₁ a₂ δ ρ ha X ω]
      exact TensorProduct.tmul_zero _ _
  | add t t' ht ht' => rw [map_add, ht, ht', add_zero]

end FactorThroughBase

section FactorThroughBaseSheaves

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R₁ R₂ A₁ A₂ B₁ B₂ : Sheaf J CommRingCat.{u}) (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂)
  (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) (δ : A₁ ⟶ R₂) (β : B₁ ⟶ B₂) (ρ : R₁ ⟶ R₂)
  (hsq : (δ ≫ a₂) ≫ φ₂ = φ₁ ≫ β) (ha : ρ ≫ a₂ = a₁ ≫ (δ ≫ a₂))
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

include hsq ha in
/-- A morphism of presentations factoring through the base ring of the second presentation
induces the zero map on the scalar extensions of the differentials. -/
theorem tensorSheafMapOfSquare_eq_zero_of_factor :
    tensorSheafMapOfSquare.{u, u, u, u} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ (δ ≫ a₂) β ρ hsq ha =
      0 := by
  apply sheafify_hom_ext.{u, u, u, u} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom)
  intro X t
  refine (tensorSheafMapOfSquare_toAssociatedModule.{u, u, u, u}
    J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ (δ ≫ a₂) β ρ hsq ha X t).trans ?_
  rw [show tensorMapOfSquareₛₗ φ₁.hom φ₂.hom (δ ≫ a₂).hom β.hom (hom_of_square hsq)
      a₁.hom a₂.hom ρ.hom (hom_of_square ha) X t = 0 from
    tensorMapOfSquareₛₗ_eq_zero_of_factor φ₁.hom φ₂.hom a₁.hom a₂.hom δ.hom β.hom ρ.hom
      (hom_of_square hsq) (hom_of_square ha) X t]
  exact Stacks.SheafOfModules.toAssociatedModule_zero J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X

end FactorThroughBaseSheaves

section Composites

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable {R₁ R₂ A₁ A₂ A₃ B B₃ : Sheaf J CommRingCat.{u}} (a₁ : R₁ ⟶ A₁) (a₂ : R₁ ⟶ A₂)
  (a₃ : R₂ ⟶ A₃) (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (φ₃ : A₃ ⟶ B₃) (ψ : A₁ ⟶ A₂) (ψ' : A₂ ⟶ A₃)
  (β : B ⟶ B₃) (ρ : R₁ ⟶ R₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
  [Presheaf.IsLocallySurjective J φ₃.hom]

/-- A map of conormal sheaves along a change of presentation followed by one along a square is
the map along the composite square. -/
theorem conormalSheafMapOfFac_comp_ofSquare (hψ : ψ ≫ φ₂ = φ₁) (h' : ψ' ≫ φ₃ = φ₂ ≫ β)
    (h'' : (ψ ≫ ψ') ≫ φ₃ = φ₁ ≫ β) :
    conormalSheafMapOfFac.{u, u, u, u} J B A₁ A₂ φ₁ φ₂ ψ hψ ≫
        conormalSheafMapOfSquare.{u, u, u, u} J A₂ A₃ B B₃ φ₂ φ₃ ψ' β h' =
      conormalSheafMapOfSquare.{u, u, u, u} J A₁ A₃ B B₃ φ₁ φ₃ (ψ ≫ ψ') β h'' := by
  refine conormal_hom_ext _ _ (fun X x ↦ ?_)
  refine (congrArg (fun t ↦ (conormalSheafMapOfSquare.{u, u, u, u} J A₂ A₃ B B₃ φ₂ φ₃ ψ' β
    h').val.app X t) (conormalSheafMapOfFac_conormalClass.{u, u, u, u} J A₁ B A₁ A₂ (𝟙 A₁) ψ
      φ₁ φ₂ ψ hψ X x)).trans ?_
  refine (conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A₁ A₁ A₂ A₃ B B₃ ψ (ψ ≫ ψ') φ₂ φ₃
    ψ' β h' X _).trans ?_
  exact (conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A₁ A₁ A₁ A₃ B B₃ (𝟙 A₁)
    (ψ ≫ ψ') φ₁ φ₃ (ψ ≫ ψ') β h'' X x).symm

/-- The same for the maps of the scalar extensions of the differentials. -/
theorem tensorSheafMapOfFac_comp_ofSquare (hψ : ψ ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂)
    (h' : ψ' ≫ φ₃ = φ₂ ≫ β) (ha' : ρ ≫ a₃ = a₂ ≫ ψ') (h'' : (ψ ≫ ψ') ≫ φ₃ = φ₁ ≫ β)
    (ha'' : ρ ≫ a₃ = a₁ ≫ (ψ ≫ ψ')) :
    tensorSheafMapOfFac.{u, u, u, u} J R₁ B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        tensorSheafMapOfSquare.{u, u, u, u} J R₁ R₂ A₂ A₃ B B₃ a₂ a₃ φ₂ φ₃ ψ' β ρ h' ha' =
      tensorSheafMapOfSquare.{u, u, u, u} J R₁ R₂ A₁ A₃ B B₃ a₁ a₃ φ₁ φ₃ (ψ ≫ ψ') β ρ h''
        ha'' := by
  refine tensorSheaf_hom_ext.{u, u, u, u} J R₁ A₁ B a₁ φ₁ _ (fun X x ↦ ?_)
  refine (congrArg (fun t ↦ (tensorSheafMapOfSquare.{u, u, u, u} J R₁ R₂ A₂ A₃ B B₃ a₂ a₃ φ₂ φ₃
    ψ' β ρ h' ha').val.app X t) (tensorSheafMapOfFac_tensorDifferential.{u, u, u, u} J R₁ B A₁
      A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha X x)).trans ?_
  refine (tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J R₁ R₂ A₂ A₃ B B₃ a₂ a₃ φ₂ φ₃
    ψ' β ρ h' ha' X _).trans ?_
  exact (tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J R₁ R₂ A₁ A₃ B B₃ a₁ a₃ φ₁ φ₃
    (ψ ≫ ψ') β ρ h'' ha'' X x).symm

end Composites

section Composites₂

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable {R₁ R₂ A₁ A₂ A₃ B B₁ : Sheaf J CommRingCat.{u}} (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂)
  (a₃ : R₂ ⟶ A₃) (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B) (φ₃ : A₃ ⟶ B) (ψ : A₁ ⟶ A₂) (ψ' : A₂ ⟶ A₃)
  (β : B₁ ⟶ B) (ρ : R₁ ⟶ R₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
  [Presheaf.IsLocallySurjective J φ₃.hom]

/-- A map of conormal sheaves along a square followed by one along a change of presentation is
the map along the composite square. -/
theorem conormalSheafMapOfSquare_comp_ofFac (h : ψ ≫ φ₂ = φ₁ ≫ β) (hψ' : ψ' ≫ φ₃ = φ₂)
    (h'' : (ψ ≫ ψ') ≫ φ₃ = φ₁ ≫ β) :
    conormalSheafMapOfSquare.{u, u, u, u} J A₁ A₂ B₁ B φ₁ φ₂ ψ β h ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (conormalSheafMapOfFac.{u, u, u, u} J B A₂ A₃ φ₂ φ₃ ψ' hψ') =
      conormalSheafMapOfSquare.{u, u, u, u} J A₁ A₃ B₁ B φ₁ φ₃ (ψ ≫ ψ') β h'' := by
  refine conormal_hom_ext _ _ (fun X x ↦ ?_)
  refine (congrArg (fun t ↦ (conormalSheafMapOfFac.{u, u, u, u} J B A₂ A₃ φ₂ φ₃ ψ' hψ').val.app
    X t) (conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A₁ A₁ A₁ A₂ B₁ B (𝟙 A₁) ψ
      φ₁ φ₂ ψ β h X x)).trans ?_
  refine (conormalSheafMapOfFac_conormalClass.{u, u, u, u} J A₁ B A₂ A₃ ψ (ψ ≫ ψ') φ₂ φ₃
    ψ' hψ' X _).trans ?_
  exact (conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A₁ A₁ A₁ A₃ B₁ B (𝟙 A₁)
    (ψ ≫ ψ') φ₁ φ₃ (ψ ≫ ψ') β h'' X x).symm

/-- The same for the maps of the scalar extensions of the differentials. -/
theorem tensorSheafMapOfSquare_comp_ofFac (h : ψ ≫ φ₂ = φ₁ ≫ β) (ha : ρ ≫ a₂ = a₁ ≫ ψ)
    (hψ' : ψ' ≫ φ₃ = φ₂) (ha' : a₂ ≫ ψ' = a₃) (h'' : (ψ ≫ ψ') ≫ φ₃ = φ₁ ≫ β)
    (ha'' : ρ ≫ a₃ = a₁ ≫ (ψ ≫ ψ')) :
    tensorSheafMapOfSquare.{u, u, u, u} J R₁ R₂ A₁ A₂ B₁ B a₁ a₂ φ₁ φ₂ ψ β ρ h ha ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (tensorSheafMapOfFac.{u, u, u, u} J R₂ B A₂ A₃ a₂ a₃ φ₂ φ₃ ψ' hψ' ha') =
      tensorSheafMapOfSquare.{u, u, u, u} J R₁ R₂ A₁ A₃ B₁ B a₁ a₃ φ₁ φ₃ (ψ ≫ ψ') β ρ h''
        ha'' := by
  refine tensorSheaf_hom_ext.{u, u, u, u} J R₁ A₁ B₁ a₁ φ₁ _ (fun X x ↦ ?_)
  refine (congrArg (fun t ↦ (tensorSheafMapOfFac.{u, u, u, u} J R₂ B A₂ A₃ a₂ a₃ φ₂ φ₃ ψ' hψ'
    ha').val.app X t) (tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J R₁ R₂ A₁ A₂ B₁ B
      a₁ a₂ φ₁ φ₂ ψ β ρ h ha X x)).trans ?_
  refine (tensorSheafMapOfFac_tensorDifferential.{u, u, u, u} J R₂ B A₂ A₃ a₂ a₃ φ₂ φ₃
    ψ' hψ' ha' X _).trans ?_
  exact (tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J R₁ R₂ A₁ A₃ B₁ B a₁ a₃ φ₁ φ₃
    (ψ ≫ ψ') β ρ h'' ha'' X x).symm

end Composites₂

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

section Quasi

variable (A B : Sheaf J CommRingCat.{u}) (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom]

/-- The generators `ℰ = A` (the local sections of `A`) of the auxiliary presentation. -/
abbrev surjectionGenerators : Functor Cᵒᵖ (Type u) := underlyingPresheaf J A

/-- `α : A ⟶ B` on underlying sets. -/
abbrev surjectionGeneratorsMap : surjectionGenerators J A ⟶ underlyingPresheaf J B :=
  Functor.whiskerRight a.hom (forget CommRingCat.{u})

/-- The evaluation `A[A] ⟶ A`, `[x] ↦ x`. -/
noncomputable abbrev surjectionEvaluation :
    freeAlgebraSheaf J A (surjectionGenerators J A) ⟶ A :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc J A A (surjectionGenerators J A) (𝟙 A) (𝟙 _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The constants `A ⟶ A[A]` followed by the evaluation `A[A] ⟶ A` are the identity of `A`. -/
theorem coefficientMap_comp_surjectionEvaluation :
    freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A) ≫
      surjectionEvaluation J A = 𝟙 A :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc J A A _ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J a.hom] in
/-- The evaluation `A[A] ⟶ A` followed by `α : A ⟶ B` is the presentation `A[A] ⟶ B`. -/
theorem surjectionEvaluation_comp :
    surjectionEvaluation J A ≫ a =
      presentation J A B a (surjectionGenerators J A) (surjectionGeneratorsMap J A B a) := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A B _ ?_ ?_
  · rw [← Category.assoc, coefficientMap_comp_surjectionEvaluation, Category.id_comp,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc]
    rfl

/-- The presentation `A[A] ⟶ B` is locally surjective. -/
instance surjectionPresentation_isLocallySurjective :
    Presheaf.IsLocallySurjective J
      (presentation J A B a (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)).hom := by
  rw [← surjectionEvaluation_comp]
  have : Presheaf.IsLocallySurjective J (surjectionEvaluation J A).hom := by
    have h : (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)).hom ≫
        (surjectionEvaluation J A).hom = 𝟙 _ :=
      Stacks.Sites.Conormal.hom_of_comp_eq (coefficientMap_comp_surjectionEvaluation J A)
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J h
  exact Presheaf.isLocallySurjective_comp J _ _

/-- The auxiliary presentation `A[A] ⟶ A ⟶ B`. -/
noncomputable abbrev surjectionPresentation :
    freeAlgebraSheaf J A (surjectionGenerators J A) ⟶ B :=
  presentation J A B a (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J a.hom] in
/-- The constants `A ⟶ A[A]` followed by `A[A] ⟶ B` are `α`. -/
theorem coefficientMap_comp_surjectionPresentation :
    freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A) ≫
      surjectionPresentation J A B a = a ≫ 𝟙 B :=
  (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc J A B _ _ _).trans
    (Category.comp_id a).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J a.hom] in
/-- The evaluation `A[A] ⟶ A` followed by `α` is the presentation `A[A] ⟶ B`, as a square over
`𝟙 B`. -/
theorem surjectionEvaluation_comp' :
    surjectionEvaluation J A ≫ a = surjectionPresentation J A B a ≫ 𝟙 B :=
  (surjectionEvaluation_comp J A B a).trans (Category.comp_id _).symm

/-- `NL(α)` for the auxiliary presentation. -/
noncomputable abbrev surjectionNL :
    CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ :=
  presentationNaiveCotangentComplex.{u, u, u, u} J A B a (surjectionGenerators J A)
    (surjectionGeneratorsMap J A B a)

/-- The constants `A ⟶ A[A]` on conormal sheaves. -/
noncomputable abbrev surjectionConstants :
    conormalSheaf.{u, u, u, u} J A B a ⟶
      (presentationConormalSequence.{u, u, u, u} J A B a (surjectionGenerators J A)
        (surjectionGeneratorsMap J A B a)).X₁ :=
  conormalSheafMapOfSquare.{u, u, u, u} J A _ B B a (surjectionPresentation J A B a)
    (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) (𝟙 B)
    (coefficientMap_comp_surjectionPresentation J A B a)

/-- The evaluation `A[A] ⟶ A` on conormal sheaves. -/
noncomputable abbrev surjectionEvaluationConormal :
    (presentationConormalSequence.{u, u, u, u} J A B a (surjectionGenerators J A)
        (surjectionGeneratorsMap J A B a)).X₁ ⟶
      conormalSheaf.{u, u, u, u} J A B a :=
  conormalSheafMapOfSquare.{u, u, u, u} J _ A B B (surjectionPresentation J A B a) a
    (surjectionEvaluation J A) (𝟙 B) (surjectionEvaluation_comp' J A B a)

/-- On conormal sheaves, the constants followed by the evaluation are the identity. -/
theorem surjectionConstants_comp_evaluation :
    surjectionConstants J A B a ≫ surjectionEvaluationConormal J A B a = 𝟙 _ := by
  refine (Stacks.Sites.Conormal.conormalSheafMapOfSquare_comp.{u, u, u, u} J A _ A B B B a
    (surjectionPresentation J A B a) a _ (surjectionEvaluation J A) (𝟙 B) (𝟙 B)
    (coefficientMap_comp_surjectionPresentation J A B a)
    (surjectionEvaluation_comp' J A B a)).trans ?_
  exact Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_id.{u, u, u, u} J A B a _
    (coefficientMap_comp_surjectionEvaluation J A) _

omit [HasWeakSheafify J CommRingCat.{u}] in
/-- The constants have no differential, for any presentation `P ⟶ B` whose base ring is `A`. -/
theorem constants_comp_conormalSequence_f {P : Sheaf J CommRingCat.{u}} (c : A ⟶ P) (φ : P ⟶ B)
    [Presheaf.IsLocallySurjective J φ.hom] (h : c ≫ φ = a ≫ 𝟙 B) :
    conormalSheafMapOfSquare.{u, u, u, u} J A P B B a φ c (𝟙 B) h ≫
      (conormalSequence.{u, u, u, u} J A P B c φ).f = 0 :=
  conormalSheafMapOfSquare_comp_conormalSequence_f J A B a c φ h

/-- The constants followed by the evaluation, on conormal sheaves: the map of the morphism of
presentations `A[A] ⟶ A ⟶ A[A]`. -/
theorem surjectionEvaluationConormal_comp_constants
    (h : (surjectionEvaluation J A ≫
      freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) ≫
        surjectionPresentation J A B a = surjectionPresentation J A B a ≫ 𝟙 B) :
    conormalSheafMapOfSquare.{u, u, u, u} J _ _ B B (surjectionPresentation J A B a)
        (surjectionPresentation J A B a)
        (surjectionEvaluation J A ≫ freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
        (𝟙 B) h =
      surjectionEvaluationConormal J A B a ≫ surjectionConstants J A B a := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun X x ↦ ?_)
  refine (Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A A _ _ B B
    (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
    (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
    (surjectionPresentation J A B a) (surjectionPresentation J A B a) _ (𝟙 B) h X x).trans ?_
  refine Eq.trans ?_ (congrArg (fun t ↦ (surjectionConstants J A B a).val.app X t)
    (Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A A _ A B B
      (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) (𝟙 A)
      (surjectionPresentation J A B a) a (surjectionEvaluation J A) (𝟙 B)
      (surjectionEvaluation_comp' J A B a) X x)).symm
  refine Eq.trans ?_ (Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u}
    J A A A _ B B (𝟙 A) (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) a
    (surjectionPresentation J A B a)
    (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) (𝟙 B)
    (coefficientMap_comp_surjectionPresentation J A B a) X _).symm
  rfl

/-- The constants `A ⟶ A[A]`, placed in degree `-1`: the chain map `(I/I²)[1] ⟶ NL(α)`. -/
noncomputable def surjectionEta :
    (CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).obj
        (conormalSheaf.{u, u, u, u} J A B a) ⟶ surjectionNL J A B a := by
  letI : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  refine HomologicalComplex.mkHomFromSingle
    (surjectionConstants J A B a ≫
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a _ _).symm) ?_
  rintro k hk
  obtain rfl : k = 0 := by simpa using hk.symm
  have h0 : surjectionConstants J A B a ≫
      (presentationConormalSequence.{u, u, u, u} J A B a (surjectionGenerators J A)
        (surjectionGeneratorsMap J A B a)).f = 0 :=
    constants_comp_conormalSequence_f J A B a _ _
      (coefficientMap_comp_surjectionPresentation J A B a)
  rw [presentationNaiveCotangentComplex_d_negOne_zero, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, ← Category.assoc, h0, zero_comp]

/-- In degree `-1`, `surjectionEta` is `surjectionConstants`. -/
theorem surjectionEta_f_negOne :
    (surjectionEta J A B a).f (-1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (conormalSheaf.{u, u, u, u} J A B a)).hom ≫ surjectionConstants J A B a ≫
        eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a _ _).symm := by
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromSingle_f _ _

/-- The evaluation `A[A] ⟶ A`, read in degree `-1`: the chain map `NL(α) ⟶ (I/I²)[1]`. -/
noncomputable def surjectionEv :
    surjectionNL J A B a ⟶
      (CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).obj
        (conormalSheaf.{u, u, u, u} J A B a) := by
  letI : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  refine HomologicalComplex.mkHomToSingle
    (eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a _ _) ≫
      surjectionEvaluationConormal J A B a) ?_
  intro i hi
  exact (presentationNaiveCotangentComplex_isZero_X J A B a _ _ i
    (by rintro rfl; simp at hi) (by rintro rfl; simp at hi)).eq_of_src _ _

/-- In degree `-1`, `surjectionEv` is `surjectionEvaluationConormal`. -/
theorem surjectionEv_f_negOne :
    (surjectionEv J A B a).f (-1) =
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a _ _) ≫
        surjectionEvaluationConormal J A B a ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (conormalSheaf.{u, u, u, u} J A B a)).inv := by
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  rw [surjectionEv, HomologicalComplex.mkHomToSingle_f, Category.assoc]

/-- `surjectionEta` followed by `surjectionEv` is the identity of `(I/I²)[1]`. -/
theorem surjectionEta_comp_ev :
    surjectionEta J A B a ≫ surjectionEv J A B a = 𝟙 _ := by
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, surjectionEta_f_negOne, surjectionEv_f_negOne,
    HomologicalComplex.id_f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (surjectionConstants J A B a), surjectionConstants_comp_evaluation,
    Category.id_comp, Iso.hom_inv_id]

/-- **The two maps of presentations `𝟙` and `A[A] ⟶ A ⟶ A[A]` are homotopic**, which makes
`surjectionEv ≫ surjectionEta` homotopic to the identity of `NL(α)`. -/
noncomputable def surjectionEvEtaHomotopy :
    Homotopy (𝟙 (surjectionNL J A B a)) (surjectionEv J A B a ≫ surjectionEta J A B a) := by
  letI : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  have hsq : 𝟙 _ ≫ surjectionPresentation J A B a = surjectionPresentation J A B a ≫ 𝟙 B := by
    rw [Category.id_comp, Category.comp_id]
  have hsq' : (surjectionEvaluation J A ≫
      freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) ≫
        surjectionPresentation J A B a = surjectionPresentation J A B a ≫ 𝟙 B := by
    rw [Category.assoc, coefficientMap_comp_surjectionPresentation, ← Category.assoc,
      surjectionEvaluation_comp']
    simp
  have ha : 𝟙 A ≫ freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A) =
      freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A) ≫ 𝟙 _ := by simp
  have ha' : 𝟙 A ≫ freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A) =
      freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A) ≫
        (surjectionEvaluation J A ≫
          freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) := by
    rw [← Category.assoc, coefficientMap_comp_surjectionEvaluation]
  let H : (presentationConormalSequence.{u, u, u, u} J A B a (surjectionGenerators J A)
      (surjectionGeneratorsMap J A B a)).X₂ ⟶
      (presentationConormalSequence.{u, u, u, u} J A B a (surjectionGenerators J A)
        (surjectionGeneratorsMap J A B a)).X₁ :=
    Stacks.Sites.Conormal.conormalHomotopyOfSquare.{u, u, u, u} J A A _ _ B B
      (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
      (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
      (surjectionPresentation J A B a) (surjectionPresentation J A B a) (𝟙 _)
      (surjectionEvaluation J A ≫ freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
      (𝟙 B) (𝟙 A) hsq hsq' ha ha'
  have key₁ : (𝟙 _ : (presentationConormalSequence.{u, u, u, u} J A B a
        (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)).X₁ ⟶ _) =
      ((presentationConormalSequence.{u, u, u, u} J A B a (surjectionGenerators J A)
        (surjectionGeneratorsMap J A B a)).f ≫ H :
          (presentationConormalSequence.{u, u, u, u} J A B a
            (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)).X₁ ⟶
          (presentationConormalSequence.{u, u, u, u} J A B a
            (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)).X₁) +
        surjectionEvaluationConormal J A B a ≫ surjectionConstants J A B a :=
    (Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_id.{u, u, u, u} J _ B _ _ rfl hsq).symm.trans
      ((Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_add.{u, u, u, u} J A A _ _ B B
        (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
        (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
        (surjectionPresentation J A B a) (surjectionPresentation J A B a) (𝟙 _)
        (surjectionEvaluation J A ≫ freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
        (𝟙 B) (𝟙 A) hsq hsq' ha ha').trans
        (congrArg (_ + ·) (surjectionEvaluationConormal_comp_constants J A B a hsq')))
  have key₀ : (𝟙 _ : (presentationConormalSequence.{u, u, u, u} J A B a
        (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)).X₂ ⟶ _) =
      H ≫ (presentationConormalSequence.{u, u, u, u} J A B a (surjectionGenerators J A)
        (surjectionGeneratorsMap J A B a)).f :=
    (Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_id.{u, u, u, u} J A _ B
      (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
      (surjectionPresentation J A B a) _ rfl _ rfl hsq ha).symm.trans
      ((Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_add.{u, u, u, u} J A A _ _ B B
        (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
        (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
        (surjectionPresentation J A B a) (surjectionPresentation J A B a) (𝟙 _)
        (surjectionEvaluation J A ≫ freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
        (𝟙 B) (𝟙 A) hsq hsq' ha ha').trans
        ((congrArg (_ + ·)
          (Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_zero_of_factor J A A _ _ B B
            (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
            (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
            (surjectionPresentation J A B a) (surjectionPresentation J A B a)
            (surjectionEvaluation J A) (𝟙 B) (𝟙 A) hsq' ha')).trans (add_zero _)))
  refine Stacks.NaiveCotangentFinitePresentation.homotopyOfIsZeroX
    (fun i h1 h2 ↦ presentationNaiveCotangentComplex_isZero_X J A B a _ _ i h1 h2)
    (eqToHom (presentationNaiveCotangentComplex_X_zero J A B a _ _) ≫ H ≫
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a _ _).symm) ?_ ?_
  · rw [HomologicalComplex.id_f, HomologicalComplex.comp_f, surjectionEta_f_negOne,
      surjectionEv_f_negOne, presentationNaiveCotangentComplex_d_negOne_zero]
    have := congrArg (fun t ↦ eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a
        (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)) ≫ t ≫
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a _ _).symm) key₁
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl, Preadditive.add_comp,
      Preadditive.comp_add, Category.assoc] at this
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.inv_hom_id_assoc]
    exact this
  · have hz : (surjectionEv J A B a ≫ surjectionEta J A B a).f 0 = 0 := by
      rw [HomologicalComplex.comp_f,
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
          (conormalSheaf.{u, u, u, u} J A B a) 0 (by decide)).eq_of_tgt
          ((surjectionEv J A B a).f 0) 0, zero_comp]
    rw [hz, add_zero, HomologicalComplex.id_f, presentationNaiveCotangentComplex_d_negOne_zero]
    have := congrArg (fun t ↦ eqToHom (presentationNaiveCotangentComplex_X_zero J A B a
        (surjectionGenerators J A) (surjectionGeneratorsMap J A B a)) ≫ t ≫
      eqToHom (presentationNaiveCotangentComplex_X_zero J A B a _ _).symm) key₀
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl, Category.assoc] at this
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact this

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B))]

/-- `surjectionEta` is an isomorphism in the derived category. -/
theorem isIso_Q_map_surjectionEta : IsIso (DerivedCategory.Q.map (surjectionEta J A B a)) :=
  ⟨⟨DerivedCategory.Q.map (surjectionEv J A B a),
    by rw [← CategoryTheory.Functor.map_comp, surjectionEta_comp_ev,
      CategoryTheory.Functor.map_id],
    by rw [← CategoryTheory.Functor.map_comp, ← DerivedCategory.Q_map_eq_of_homotopy
      (h := surjectionEvEtaHomotopy J A B a), CategoryTheory.Functor.map_id]⟩⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B))] in
/-- `η` factors through the auxiliary presentation: it is `surjectionEta` followed by the
comparison `NL(α) ⟶ NL_{B/A}`. -/
theorem surjectionEta_comp_comparison :
    surjectionEta J A B a ≫
        naiveCotangentComplexComparison.{u, u, u, u} J A B a (surjectionGenerators J A)
          (surjectionGeneratorsMap J A B a) =
      conormalToNaiveCotangentComplex J A B a := by
  let : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  have hmain : (surjectionConstants J A B a ≫
      presentationConormalMap.{u, u, u, u} J A (surjectionGenerators J A) (underlyingPresheaf J B)
        (surjectionGeneratorsMap J A B a) B a (surjectionGeneratorsMap J A B a) (𝟙 _)
        (Category.comp_id _) : conormalSheaf.{u, u, u, u} J A B a ⟶
          (canonicalConormalSequence.{u, u, u, u} J A B a).X₁) =
      conormalToNaiveCotangentConormal J A B a := by
    refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun X x ↦ ?_)
    have e1 := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A A A _
      B B (𝟙 A) (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) a
      (surjectionPresentation J A B a)
      (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)) (𝟙 B)
      (coefficientMap_comp_surjectionPresentation J A B a) X x
    have e2 := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{u, u, u, u} J A B _ _
      (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A))
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (surjectionPresentation J A B a) (canonicalPresentation J A B a)
      (freeAlgebraMap J A (surjectionGenerators J A) (underlyingPresheaf J B)
        (surjectionGeneratorsMap J A B a))
      (freeAlgebraMap_comp_presentation J A _ _ (surjectionGeneratorsMap J A B a) B a _ (𝟙 _)
        (Category.comp_id _)) X
      ⟨(freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)).hom.app X x,
        Stacks.Sites.Conormal.kernelIdeal_le_comap_square a.hom
          (surjectionPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)).hom
          (𝟙 B : B ⟶ B).hom
          (Stacks.Sites.Conormal.hom_of_square
            (coefficientMap_comp_surjectionPresentation J A B a)) X x.2⟩
    have e3 := conormalToNaiveCotangentConormal_conormalClass J A B a (𝟙 A) X x
    have e4 : (freeAlgebraMap J A (surjectionGenerators J A) (underlyingPresheaf J B)
        (surjectionGeneratorsMap J A B a)).hom.app X
          ((freeAlgebraSheafCoefficientMap J A (surjectionGenerators J A)).hom.app X x) =
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom.app X x :=
      congrArg (fun t ↦ (ConcreteCategory.hom (t.hom.app X)) (x : A.obj.obj X))
        (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A (surjectionGenerators J A)
          (underlyingPresheaf J B) (surjectionGeneratorsMap J A B a))
    refine (congrArg _ e1).trans (e2.trans (Eq.trans ?_ e3.symm))
    exact congrArg _ (Subtype.ext e4)
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, surjectionEta_f_negOne, conormalToNaiveCotangentComplex_f_negOne]
  have hc := presentationNaiveCotangentComplexMap_f_negOne.{u, u, u, u} J A
    (surjectionGenerators J A) (underlyingPresheaf J B) (surjectionGeneratorsMap J A B a) B a
    (surjectionGeneratorsMap J A B a) (𝟙 _) (Category.comp_id _)
  show _ ≫ (presentationNaiveCotangentComplexMap.{u, u, u, u} J A
    (surjectionGenerators J A) (underlyingPresheaf J B) (surjectionGeneratorsMap J A B a) B a
    (surjectionGeneratorsMap J A B a) (𝟙 _) (Category.comp_id _)).f (-1) = _
  rw [hc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (surjectionConstants J A B a)]
  exact congrArg (fun t ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
    (conormalSheaf.{u, u, u, u} J A B a)).hom ≫ t ≫
      eqToHom (presentationNaiveCotangentComplex_X_negOne.{u, u, u, u} J A B a
        (underlyingPresheaf J B) (𝟙 _)).symm) hmain

/-- **`η : (I/I²)[1] ⟶ NL_{B/A}` is an isomorphism in the derived category**: the naive
cotangent complex of a surjection is its conormal sheaf placed in degree `-1`. -/
@[sga "6 0 4.3" "partial"]
instance isIso_Q_map_conormalToNaiveCotangentComplex :
    IsIso (DerivedCategory.Q.map (conormalToNaiveCotangentComplex J A B a)) := by
  have := isIso_Q_map_surjectionEta J A B a
  have : IsIso (DerivedCategory.Q.map (naiveCotangentComplexComparison.{u, u, u, u} J A B a
      (surjectionGenerators J A) (surjectionGeneratorsMap J A B a))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := _) _).2
      (quasiIso_naiveCotangentComplexComparison_site.{u, u, u, u} J A B a _ _)
  rw [← surjectionEta_comp_comparison, Functor.map_comp]
  infer_instance

end Quasi

end Stacks.SheafOfModules

end

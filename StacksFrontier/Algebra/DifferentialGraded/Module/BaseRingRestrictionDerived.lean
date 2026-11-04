module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Equivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseRingRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedForgetful
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction

/-!
# The derived category of a differential graded algebra does not see the base ring

Let `S → R` be a homomorphism of commutative rings and `(A, d)` a differential graded algebra over
`R`, regarded over `S` as `DifferentialGradedAlgebra.restrictBase`. Regarding a differential
graded `A`-module over `S` does not change its underlying complex of abelian groups, so it
preserves quasi-isomorphisms, and so does its inverse. The equivalence of homotopy categories
`DifferentialGradedModule.restrictBaseHomotopyEquiv` therefore descends to an equivalence of
derived categories `D(A, d) ≌ D(A_S, d)`. It commutes with restriction of scalars along a
homomorphism of differential graded algebras, and with the forgetful functors to the derived
categories of modules over the two base rings.

## Main definitions

* `DifferentialGradedModule.forgetRestrictBaseIso`: the underlying complex of a module regarded
  over `S` is the underlying complex of `R`-modules, with scalars restricted to `S`.
* `DifferentialGradedModule.derivedRestrictBase` and
  `DifferentialGradedModule.derivedExtendBase`: the induced functors between derived categories.
* `DifferentialGradedModule.derivedRestrictBaseEquiv`: the equivalence `D(A, d) ≌ D(A_S, d)`.
* `DifferentialGradedModule.derivedRestrictionRestrictBaseIso`: its compatibility with derived
  restriction of scalars along a homomorphism of differential graded algebras.
* `DifferentialGradedModule.derivedForgetRestrictBaseIso`: its compatibility with the forgetful
  functors `D(A, d) ⥤ D(R)` and `D(A_S, d) ⥤ D(S)`.

## Main results

* `DifferentialGradedModule.quasiIso_restrictBase_map_iff` and
  `DifferentialGradedModule.quasiIso_extendBase_map_iff`: both functors preserve and reflect
  quasi-isomorphisms.
* `DifferentialGradedModule.isZero_derivedRestrictBase_obj_iff` and
  `DifferentialGradedModule.isIso_derivedRestrictBase_map_iff`: zero objects and isomorphisms
  of `D(A, d)` can be detected after regarding over `S`.

## Implementation notes

The derived equivalence is `CategoryTheory.Localization.equivalence`, applied to the two functors
of homotopy categories followed by the localizations; its functor is by construction the descent
`DifferentialGradedModule.derivedRestrictBase`. All compatibilities on derived categories are
obtained by `CategoryTheory.Localization.liftNatIso` from the corresponding ones on homotopy
categories, which come from the module level, where every functor involved keeps the underlying
type, grading and differential.

## References

* [Stacks Project, Tag 09KV](https://stacks.math.columbia.edu/tag/09KV)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u u' v w w'

namespace DifferentialGradedModule

section complexes

variable {R : Type u} [CommRing R] (S : Type u') [CommRing S] [Algebra S R]
  {A : DifferentialGradedAlgebra.{u, v} R}

variable (A) in
/-- The underlying complex of a differential graded `A`-module regarded over `S` is its
underlying complex of `R`-modules with scalars restricted to `S`. -/
def forgetRestrictBaseIso :
    restrictBase S A ⋙ forgetToCochainComplex.{u', v, w} (A.restrictBase S) ≅
      forgetToCochainComplex.{u, v, w} A ⋙
        (ModuleCat.restrictScalars.{w} (algebraMap S R)).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  NatIso.ofComponents
    (fun M => HomologicalComplex.Hom.isoOfComponents
      (fun _ => Iso.refl _)
      (by
        rintro i j (rfl : i + 1 = j)
        simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_d, forgetToCochainComplex,
          toCochainComplex_d]
        ext x
        rfl))
    (by intros; ext n x; rfl)

/-- A homomorphism of differential graded `A`-modules is a quasi-isomorphism exactly when it is
one after regarding it over `S`. -/
theorem quasiIso_restrictBase_map_iff {M N : DifferentialGradedModule.{u, v, w} A} (g : M ⟶ N) :
    QuasiIso ((forgetToCochainComplex (A.restrictBase S)).map ((restrictBase S A).map g)) ↔
      QuasiIso ((forgetToCochainComplex A).map g) := by
  refine (quasiIso_iff_of_arrow_mk_iso
    ((forgetToCochainComplex (A.restrictBase S)).map ((restrictBase S A).map g))
    (((ModuleCat.restrictScalars.{w} (algebraMap S R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((forgetToCochainComplex A).map g))
    (Arrow.isoOfNatIso (forgetRestrictBaseIso S A) (Arrow.mk g))).trans ?_
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ _

/-- A homomorphism of differential graded modules over `A` regarded over `S` is a
quasi-isomorphism exactly when it is one after letting `R` act through `A`. -/
theorem quasiIso_extendBase_map_iff {N N' : DifferentialGradedModule.{u', v, w} (A.restrictBase S)}
    (g : N ⟶ N') :
    QuasiIso ((forgetToCochainComplex A).map ((extendBase S A).map g)) ↔
      QuasiIso ((forgetToCochainComplex (A.restrictBase S)).map g) := by
  rw [← quasiIso_restrictBase_map_iff S ((extendBase S A).map g)]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    ((forgetToCochainComplex (A.restrictBase S)).mapArrow.mapIso
      (Arrow.isoOfNatIso (restrictBaseEquiv S A).counitIso (Arrow.mk g)))

end complexes

section derived

/-- A natural isomorphism between two functors out of a localized category, obtained from one
between their composites with the localization functor. -/
def baseRingLiftNatIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {F G : D ⥤ E}
    (e : L ⋙ F ≅ L ⋙ G) : F ≅ G :=
  letI : Localization.Lifting L W (L ⋙ F) F := ⟨Iso.refl _⟩
  letI : Localization.Lifting L W (L ⋙ G) G := ⟨Iso.refl _⟩
  Localization.liftNatIso L W (L ⋙ F) (L ⋙ G) F G e

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra S R]
  (A : DifferentialGradedAlgebra.{u, u} R)

/-- A morphism of the homotopy category of `A` is a quasi-isomorphism exactly when it is one after
regarding it over `S`. -/
theorem quasiIsomorphisms_restrictBaseHomotopyFunctor_map_iff
    {X Y : HomotopyCategory.{u, u, u} A} (f : X ⟶ Y) :
    quasiIsomorphisms' (A.restrictBase S) ((restrictBaseHomotopyFunctor S A).map f) ↔
      quasiIsomorphisms' A f := by
  obtain ⟨M⟩ := X
  obtain ⟨N⟩ := Y
  induction f using Quot.inductionOn with
  | h g =>
    exact (quasiIsomorphisms_map_iff' (A.restrictBase S) ((restrictBase S A).map g)).trans
      ((quasiIso_restrictBase_map_iff S g).trans (quasiIsomorphisms_map_iff' A g).symm)

/-- A morphism of the homotopy category of `A` regarded over `S` is a quasi-isomorphism exactly
when it is one after letting `R` act through `A`. -/
theorem quasiIsomorphisms_extendBaseHomotopyFunctor_map_iff
    {X Y : HomotopyCategory.{u, u, u} (A.restrictBase S)} (f : X ⟶ Y) :
    quasiIsomorphisms' A ((extendBaseHomotopyFunctor S A).map f) ↔
      quasiIsomorphisms' (A.restrictBase S) f := by
  obtain ⟨M⟩ := X
  obtain ⟨N⟩ := Y
  induction f using Quot.inductionOn with
  | h g =>
    exact (quasiIsomorphisms_map_iff' A ((extendBase S A).map g)).trans
      ((quasiIso_extendBase_map_iff S g).trans
        (quasiIsomorphisms_map_iff' (A.restrictBase S) g).symm)

/-- Regarding over `S` inverts the quasi-isomorphisms, once followed by the localization. -/
theorem quasiIsomorphisms_isInvertedBy_restrictBase :
    (quasiIsomorphisms' A).IsInvertedBy
      (restrictBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' (A.restrictBase S)).Q) :=
  fun _ _ f hf => Localization.inverts (quasiIsomorphisms' (A.restrictBase S)).Q
    (quasiIsomorphisms' (A.restrictBase S)) _
    ((quasiIsomorphisms_restrictBaseHomotopyFunctor_map_iff S A f).mpr hf)

/-- Letting `R` act through `A` inverts the quasi-isomorphisms, once followed by the
localization. -/
theorem quasiIsomorphisms_isInvertedBy_extendBase :
    (quasiIsomorphisms' (A.restrictBase S)).IsInvertedBy
      (extendBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' A).Q) :=
  fun _ _ f hf => Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _
    ((quasiIsomorphisms_extendBaseHomotopyFunctor_map_iff S A f).mpr hf)

/-- Regarding differential graded `A`-modules over `S`, on derived categories:
`D(A, d) ⥤ D(A_S, d)`. -/
def derivedRestrictBase : derivedCategory' A ⥤ derivedCategory' (A.restrictBase S) :=
  Localization.lift (restrictBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' (A.restrictBase S)).Q)
    (quasiIsomorphisms_isInvertedBy_restrictBase S A) (quasiIsomorphisms' A).Q

/-- Regarding over `S` on derived categories is induced by the same on homotopy categories. -/
def derivedRestrictBaseFactorization :
    (quasiIsomorphisms' A).Q ⋙ derivedRestrictBase S A ≅
      restrictBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' (A.restrictBase S)).Q :=
  Localization.fac _ _ _

/-- `DifferentialGradedModule.derivedRestrictBase` lifts regarding over `S` on homotopy
categories. -/
instance : Localization.Lifting (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
    (restrictBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' (A.restrictBase S)).Q)
    (derivedRestrictBase S A) :=
  ⟨derivedRestrictBaseFactorization S A⟩

/-- Letting `R` act through `A`, on derived categories: `D(A_S, d) ⥤ D(A, d)`. -/
def derivedExtendBase : derivedCategory' (A.restrictBase S) ⥤ derivedCategory' A :=
  Localization.lift (extendBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' A).Q)
    (quasiIsomorphisms_isInvertedBy_extendBase S A) (quasiIsomorphisms' (A.restrictBase S)).Q

/-- Letting `R` act through `A` on derived categories is induced by the same on homotopy
categories. -/
def derivedExtendBaseFactorization :
    (quasiIsomorphisms' (A.restrictBase S)).Q ⋙ derivedExtendBase S A ≅
      extendBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' A).Q :=
  Localization.fac _ _ _

/-- `DifferentialGradedModule.derivedExtendBase` lifts letting `R` act through `A` on homotopy
categories. -/
instance : Localization.Lifting (quasiIsomorphisms' (A.restrictBase S)).Q
    (quasiIsomorphisms' (A.restrictBase S))
    (extendBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' A).Q) (derivedExtendBase S A) :=
  ⟨derivedExtendBaseFactorization S A⟩

/-- **The derived category does not see the base ring.** Regarding differential graded
`A`-modules over `S` is an equivalence of derived categories `D(A, d) ≌ D(A_S, d)`. -/
def derivedRestrictBaseEquiv : derivedCategory' A ≌ derivedCategory' (A.restrictBase S) :=
  Localization.equivalence (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
    (quasiIsomorphisms' (A.restrictBase S)).Q (quasiIsomorphisms' (A.restrictBase S))
    (restrictBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' (A.restrictBase S)).Q)
    (derivedRestrictBase S A)
    (extendBaseHomotopyFunctor S A ⋙ (quasiIsomorphisms' A).Q)
    (derivedExtendBase S A)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedExtendBaseFactorization S A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictBaseHomotopyEquiv S A).unitIso.symm _ ≪≫
      Functor.leftUnitor _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedRestrictBaseFactorization S A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictBaseHomotopyEquiv S A).counitIso _ ≪≫
      Functor.leftUnitor _)

/-- The functor of `derivedRestrictBaseEquiv` is `derivedRestrictBase`. -/
@[simp]
theorem derivedRestrictBaseEquiv_functor :
    (derivedRestrictBaseEquiv S A).functor = derivedRestrictBase S A := rfl

/-- The inverse of `derivedRestrictBaseEquiv` is `derivedExtendBase`. -/
@[simp]
theorem derivedRestrictBaseEquiv_inverse :
    (derivedRestrictBaseEquiv S A).inverse = derivedExtendBase S A := rfl

/-- An object is zero exactly when its image under an equivalence of categories is zero. -/
private theorem isZero_functor_obj_iff {C D : Type*} [Category* C] [Category* D] (e : C ≌ D)
    (X : C) : IsZero (e.functor.obj X) ↔ IsZero X :=
  ⟨IsZero.of_full_of_faithful_of_isZero _ X, fun h =>
    IsZero.of_full_of_faithful_of_isZero e.inverse _ (h.of_iso (e.unitIso.app X).symm)⟩

/-- An object of `D(A, d)` is zero exactly when it is zero after regarding it over `S`. -/
theorem isZero_derivedRestrictBase_obj_iff (X : derivedCategory' A) :
    IsZero ((derivedRestrictBaseEquiv S A).functor.obj X) ↔ IsZero X :=
  isZero_functor_obj_iff (derivedRestrictBaseEquiv S A) X

/-- A morphism of `D(A, d)` is an isomorphism exactly when it is one after regarding it over
`S`. -/
theorem isIso_derivedRestrictBase_map_iff {X Y : derivedCategory' A} (f : X ⟶ Y) :
    IsIso ((derivedRestrictBaseEquiv S A).functor.map f) ↔ IsIso f :=
  isIso_iff_of_reflects_iso f (derivedRestrictBaseEquiv S A).functor

/-- An object of `D(A_S, d)` is zero exactly when it is zero after letting `R` act through
`A`. -/
theorem isZero_derivedExtendBase_obj_iff (X : derivedCategory' (A.restrictBase S)) :
    IsZero ((derivedRestrictBaseEquiv S A).inverse.obj X) ↔ IsZero X :=
  isZero_functor_obj_iff (derivedRestrictBaseEquiv S A).symm X

/-- A morphism of `D(A_S, d)` is an isomorphism exactly when it is one after letting `R` act
through `A`. -/
theorem isIso_derivedExtendBase_map_iff {X Y : derivedCategory' (A.restrictBase S)} (f : X ⟶ Y) :
    IsIso ((derivedRestrictBaseEquiv S A).inverse.map f) ↔ IsIso f :=
  isIso_iff_of_reflects_iso f (derivedRestrictBaseEquiv S A).inverse

end derived

section restriction

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra S R]
  {A B : DifferentialGradedAlgebra.{u, u} R}

/-- Regarding over `S` commutes with restriction of scalars along a homomorphism of differential
graded algebras, on differential graded modules: the two composites agree on the nose, so the
isomorphism is the identity. -/
def restrictScalarsRestrictBaseIso (φ : A.Hom B) :
    restrictScalarsFunctor φ ⋙ restrictBase S A ≅
      restrictBase S B ⋙ restrictScalarsFunctor (φ.restrictBase S) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Regarding over `S` commutes with restriction of scalars along a homomorphism of differential
graded algebras, on homotopy categories. -/
def restrictScalarsHomotopyRestrictBaseIso (φ : A.Hom B) :
    restrictScalarsHomotopyFunctor φ ⋙ restrictBaseHomotopyFunctor S A ≅
      restrictBaseHomotopyFunctor S B ⋙ restrictScalarsHomotopyFunctor (φ.restrictBase S) :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictScalarsHomotopyFunctorIso φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (restrictBaseHomotopyFunctorIso S A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictScalarsRestrictBaseIso S φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (restrictScalarsHomotopyFunctorIso (φ.restrictBase S)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictBaseHomotopyFunctorIso S B).symm _ ≪≫
      Functor.associator _ _ _)

/-- **Changing the base ring commutes with derived restriction of scalars.** For a homomorphism
`φ : A → B` of differential graded algebras over `R`, derived restriction of scalars along `φ`
followed by regarding over `S` is derived restriction of scalars along `φ` regarded over `S`,
preceded by regarding over `S`. -/
def derivedRestrictionRestrictBaseIso (φ : A.Hom B) :
    derivedRestriction φ ⋙ (derivedRestrictBaseEquiv S A).functor ≅
      (derivedRestrictBaseEquiv S B).functor ⋙ derivedRestriction (φ.restrictBase S) :=
  baseRingLiftNatIso (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedRestrictionFactorization φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedRestrictBaseFactorization S A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictScalarsHomotopyRestrictBaseIso S φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedRestrictionFactorization (φ.restrictBase S)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedRestrictBaseFactorization S B).symm _ ≪≫
      Functor.associator _ _ _)

end restriction

section forget

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra S R]
  (A : DifferentialGradedAlgebra.{u, u} R)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

/-- On homotopy categories, the underlying complex of a module regarded over `S`, read in the
derived category of `S`-modules, is its underlying complex of `R`-modules read in the derived
category of `R`-modules, followed by restriction of scalars. -/
def forgetHomotopyRestrictBaseIso :
    restrictBaseHomotopyFunctor S A ⋙ forgetHomotopyToDerivedCategory (A.restrictBase S) ≅
      forgetHomotopyToDerivedCategory A ⋙
        (ModuleCat.restrictScalars.{u} (algebraMap S R)).mapDerivedCategory :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictBaseHomotopyFunctorIso S A) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (forgetHomotopyToDerivedCategoryIso (A.restrictBase S)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (forgetRestrictBaseIso S A) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (ModuleCat.restrictScalars.{u} (algebraMap S R)).mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (forgetHomotopyToDerivedCategoryIso A).symm _ ≪≫
      Functor.associator _ _ _)

/-- **The forgetful functors to complexes agree.** Regarding over `S` and then forgetting to
`D(S)` is forgetting to `D(R)` and then restricting scalars to `S`. -/
def derivedForgetRestrictBaseIso :
    (derivedRestrictBaseEquiv S A).functor ⋙ derivedForget (A.restrictBase S) ≅
      derivedForget A ⋙ (ModuleCat.restrictScalars.{u} (algebraMap S R)).mapDerivedCategory :=
  baseRingLiftNatIso (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedRestrictBaseFactorization S A) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedForgetFactorization (A.restrictBase S)) ≪≫
      forgetHomotopyRestrictBaseIso S A ≪≫
      Functor.isoWhiskerRight (derivedForgetFactorization A).symm _ ≪≫
      Functor.associator _ _ _)

end forget

end DifferentialGradedModule

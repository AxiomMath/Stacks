module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# A complex with zero differentials is the direct sum of its terms

A family of objects `F : ℤ → A` in an additive category assembles into the cochain complex
carrying `F n` in degree `n` with all differentials zero. That complex is the coproduct, in
`CochainComplex A ℤ`, of the single complexes `(singleFunctor A n).obj (F n)`: a chain map out
of a complex with zero differentials is precisely a family of maps `F m ⟶ K.X m` each killed by
`K.d m (m + 1)`, and that is precisely a family of chain maps out of the singles, because a
chain map out of `(singleFunctor A n).obj (F n)` is a single such map in degree `n`. The two
sides therefore have the same universal property, and the comparison is an isomorphism with no
hypothesis on the existence of coproducts.

Since the localization functor `DerivedCategory.Q` is defined on the nose by composing with the
single functors, the same decomposition holds in the derived category whenever `Q` preserves
`ℤ`-indexed coproducts: an object of `D(A)` represented by a complex with zero differentials is
the direct sum of the shifted single objects `(DerivedCategory.singleFunctor A n).obj (F n)`.

## Main results

* `CochainComplex.zeroDifferentialComplex` — the complex with `X n = F n` and zero differentials.
* `CochainComplex.singleInj` — the canonical chain map from the single complex in degree `n`.
* `CochainComplex.isColimitCofan` — the cofan of the `singleInj` is a colimit; this is the
  universal property and needs no coproduct hypothesis.
* `CochainComplex.coproductIso` — the resulting isomorphism
  `∐ (fun n => (singleFunctor A n).obj (F n)) ≅ zeroDifferentialComplex F`.
* `CochainComplex.derivedIsColimitCofan` and `CochainComplex.derivedCoproductIso` — the same
  statements in the derived category, for a localization functor preserving `ℤ`-indexed
  coproducts.

## Implementation notes

`derivedIsColimitCofan` and `derivedCoproductIso` take
`PreservesColimitsOfShape (Discrete ℤ) DerivedCategory.Q` and the existence of the coproduct as
hypotheses rather than deducing them from Grothendieck's axioms, because `ℤ` lives in `Type 0`
while a Grothendieck abelian category is usually only locally small in a larger universe `w`.
`CategoryTheory.Limits.preservesColimitsOfShape_discrete_shrink` here and
`CategoryTheory.Limits.hasCoproducts_shrink` in Mathlib bridge the gap: `w`-indexed coproducts
give `ℤ`-indexed ones through the equivalence `Discrete (ULift.{w} ℤ) ≌ Discrete ℤ`.

## References

* `Mathlib/Algebra/Homology/Single.lean` — the single complexes and the description of chain
  maps into and out of them.
* `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean` — the localization functor
  `DerivedCategory.Q` and `DerivedCategory.singleFunctor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w v' v u' u

namespace CategoryTheory.Limits

/-- Shrinking the universe of the index type of preserved coproducts: a functor which preserves
coproducts indexed by `ULift.{w'} J` preserves coproducts indexed by `J`, since the two index
categories are equivalent. -/
public lemma preservesColimitsOfShape_discrete_shrink {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (J : Type w)
    [PreservesColimitsOfShape (Discrete (ULift.{w'} J)) G] :
    PreservesColimitsOfShape (Discrete J) G :=
  preservesColimitsOfShape_of_equiv
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _) G

end CategoryTheory.Limits

namespace CochainComplex

section ZeroDifferential

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The cochain complex attached to a family of objects `F : ℤ → A` by placing `F n` in degree
`n` and taking every differential to be zero. -/
public def zeroDifferentialComplex (F : ℤ → A) : CochainComplex A ℤ where
  X := F
  d _ _ := 0

/-- The degree `n` term of the zero-differential complex of `F` is `F n`. -/
public lemma zeroDifferentialComplex_X (F : ℤ → A) (n : ℤ) :
    (zeroDifferentialComplex F).X n = F n := rfl

/-- Every differential of the zero-differential complex of `F` vanishes. -/
@[simp] public lemma zeroDifferentialComplex_d (F : ℤ → A) (n m : ℤ) :
    (zeroDifferentialComplex F).d n m = 0 := rfl

/-- The zero-differential complex of `F` is zero in degree `n` as soon as `F n` is. -/
public theorem isZero_zeroDifferentialComplex_X (F : ℤ → A) (n : ℤ) (h : IsZero (F n)) :
    IsZero ((zeroDifferentialComplex F).X n) := h

end ZeroDifferential

section Coproduct

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]

/-- The canonical chain map from the single complex carrying `F n` in degree `n` into the
zero-differential complex of `F`: it is the identity of `F n` in degree `n` and zero elsewhere.
No condition is needed for this to be a chain map, the target having zero differentials. -/
public def singleInj (F : ℤ → A) (n : ℤ) :
    (CochainComplex.singleFunctor A n).obj (F n) ⟶ zeroDifferentialComplex F :=
  HomologicalComplex.mkHomFromSingle
    (eqToHom (zeroDifferentialComplex_X F n).symm) (fun _ _ => by simp)

/-- In degree `n`, `CochainComplex.singleInj F n` is the identification of the degree `n` term
of the single complex with `F n`. -/
@[simp] public lemma singleInj_f_self (F : ℤ → A) (n : ℤ) :
    (singleInj F n).f n = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (F n)).hom ≫
      eqToHom (zeroDifferentialComplex_X F n).symm := by
  rw [singleInj, HomologicalComplex.mkHomFromSingle_f]

/-- **A complex with zero differentials is the direct sum of its terms.** The cofan of the
canonical maps `CochainComplex.singleInj F n` exhibits the zero-differential complex of
`F : ℤ → A` as the coproduct of the single complexes `(singleFunctor A n).obj (F n)` in
`CochainComplex A ℤ`.

Both sides have the same universal property: a chain map into a complex `K` out of either one is
a family of morphisms `F m ⟶ K.X m` killed by the differentials of `K`. -/
public def isColimitCofan (F : ℤ → A) :
    IsColimit (Cofan.mk (zeroDifferentialComplex F) (singleInj F) :
      Cofan fun n : ℤ => (CochainComplex.singleFunctor A n).obj (F n)) :=
  Cofan.IsColimit.mk _
    (fun t =>
      { f := fun m => eqToHom (zeroDifferentialComplex_X F m) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m (F m)).inv ≫ (t.inj m).f m
        comm' := fun i j _ => by simp })
    (fun t j => HomologicalComplex.from_single_hom_ext (by simp))
    (fun t m hm => by
      ext k
      have h := HomologicalComplex.congr_hom (hm k) k
      simp only [cofan_mk_inj, HomologicalComplex.comp_f, singleInj_f_self] at h
      dsimp only
      rw [← h]
      simp)

/-- The direct sum of the single complexes `(singleFunctor A n).obj (F n)`, when it exists, is
the zero-differential complex of `F`. -/
public def coproductIso (F : ℤ → A)
    [HasCoproduct fun n : ℤ => (CochainComplex.singleFunctor A n).obj (F n)] :
    (∐ fun n : ℤ => (CochainComplex.singleFunctor A n).obj (F n)) ≅ zeroDifferentialComplex F :=
  colimit.isoColimitCocone ⟨_, isColimitCofan F⟩

end Coproduct

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **A complex with zero differentials is the direct sum of its terms in the derived
category.** If the localization functor `DerivedCategory.Q` preserves `ℤ`-indexed coproducts
then the images of the canonical maps `CochainComplex.singleInj F n` exhibit the object
represented by the zero-differential complex of `F` as the direct sum of the objects
`(DerivedCategory.singleFunctor A n).obj (F n)`. -/
public def derivedIsColimitCofan (F : ℤ → A)
    [PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := A))] :
    IsColimit (Cofan.mk (DerivedCategory.Q.obj (zeroDifferentialComplex F))
        (fun n => DerivedCategory.Q.map (singleInj F n)) :
      Cofan fun n : ℤ => (DerivedCategory.singleFunctor A n).obj (F n)) :=
  isColimitCofanMkObjOfIsColimit DerivedCategory.Q _ _ (isColimitCofan F)

/-- The direct sum in `D(A)` of the single objects `(DerivedCategory.singleFunctor A n).obj
(F n)` is the object represented by the complex with `F n` in degree `n` and zero
differentials. -/
public def derivedCoproductIso (F : ℤ → A)
    [PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := A))]
    [HasCoproduct fun n : ℤ => (DerivedCategory.singleFunctor A n).obj (F n)] :
    (∐ fun n : ℤ => (DerivedCategory.singleFunctor A n).obj (F n)) ≅
      DerivedCategory.Q.obj (zeroDifferentialComplex F) :=
  colimit.isoColimitCocone ⟨_, derivedIsColimitCofan F⟩

end Derived

end CochainComplex

end

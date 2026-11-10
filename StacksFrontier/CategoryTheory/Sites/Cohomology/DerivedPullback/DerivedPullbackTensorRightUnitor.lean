module

public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.RightUnitorCoherenceInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedUnitorCoherenceUnitPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposRightUnitorCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality

/-! # The right-unitor coherence of the comparison of total tensor complexes

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of
the underlying sites which is a morphism of sites. **Stacks 07A4** is proved by comparing total
tensor complexes of K-flat representatives, and the comparison
`f^*Tot(K ⊗_{𝒪_D} L) ≅ Tot(f^*K ⊗_{𝒪_C} f^*L)` of
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` is what carries it. This file proves
the **right-unitor coherence of that comparison**: at `L = 𝒪_D[0]`, the comparison followed by
the unit comparison `f^*𝒪_D ⟶ 𝒪_C` in the second tensor factor and by the unit law
`Tot(f^*K ⊗ 𝒪_C[0]) ≅ f^*K` is the degreewise pullback of the unit law
`Tot(K ⊗ 𝒪_D[0]) ≅ K`.

This is the complex-level form of the right-unitor coherence of Stacks 07A4.  Its derived form,
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_rightUnitor`, and the base case
`K = 𝒪_D[0]` of **Stacks 0944** that it feeds are proved from it in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ProjectionFormulaUnitObject.lean`.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_rightUnitor`: **the right-unitor
  coherence of the comparison of total tensor complexes.**
* `Stacks.Sheaves.DerivedPullback.ι_totalSingleIso_hom` and
  `Stacks.Sheaves.DerivedPullback.totalSingleIso_inv_f`: the single-row identification
  `Tot(F(K, M[0])) ≅ (p ↦ F(K^p, M))` of an arbitrary additive bifunctor, read on the one
  summand of total degree `n` that does not vanish.
* `Stacks.Sheaves.DerivedPullback.mapBifunctorUnitIso`: the unit law `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` of
  Tag 06YM, restated with its source spelled as `HomologicalComplex.mapBifunctor`, with its
  value and the value of its inverse on that summand.
* `Stacks.Sheaves.DerivedPullback.pullbackUnitComplexMap`: the unit comparison
  `f^*(𝒪_D[0]) ⟶ 𝒪_C[0]` on complexes, the morphism underlying
  `Stacks.Sheaves.DerivedPullback.derivedPullbackUnitMap`.

## Implementation notes

**Where the content sits.** All of the mathematics is already available one level down: the
module-level right-unitor coherence
`Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` of Stacks 03EL for the
site-presented pullback. What this file does is transport it to complexes, across the
summandwise formula `ι_pullbackToposTensorTotalIso_hom` for the comparison of total tensor
complexes.

**The passage needs the unit law on a summand.** The unit law
`Stacks.SheafOfModules.tensorComplexUnitIso` is
`CochainComplex.KFlatBifunctor.totalSingleIso` followed by the termwise unit law, and
`totalSingleIso` comes with no formula on a summand of the total complex. `ι_totalSingleIso_hom`
supplies one: on the summand of bidegree `(n, 0)` the identification is the identification of
the degree-zero term of `M[0]` with `M`, and `singleObjXSelf_zero_hom` records that in the degree
`0` that identification is the identity, since the term is `if (0 : ℤ) = 0 then M else 0`.

**Seams, and the two devices used against them.** Four pairs of spellings meet here, each a
definitional equality that `rw` and `simp` do not see because it unfolds a semireducible
definition: the degree-`n` term of a degreewise pullback against the pullback of a term, the
degree-zero term of `M[0]` against `M`, the total tensor complex spelled with
`Stacks.SheafOfModules.Tensor.tensorComplex` against `HomologicalComplex.mapBifunctor`, and the
unit law of the tensor product read through `CategoryTheory.Functor.flip`. A composite whose seam
carries two such spellings is a term that is not type-correct at the transparency a rewrite
checks at, so `rw` reports that it cannot find its pattern.

The two cures are the ones this directory prescribes. *Declare the crossing once, in a type*:
`mapBifunctorUnitIso`, `tensorUnitRight`, `ιUnitSummand`, `ιPullSummand` and
`pullbackUnitComparison` are the five aliases that let every statement below be written in one
spelling. *Supply the reassociations in term position*: the proofs are chains of `Eq.trans` and
`congrArg` rather than `rw`, so that each step is checked at default transparency, where the
seams are invisible.

**No inverse of the comparison of Stacks 03EL is used.** The coherence is stated with the
comparison of total tensor complexes as `hom`, and proved by cancelling the unit law of the
target rather than by inverting the degreewise comparison, for which no `IsIso` instance is
available at either spelling.

**No left unitor and no associator.** Only the right unitor is treated, as in the module-level
file; nothing here registers a monoidal structure on `f^*`.

**Only the degree zero of the unit complex.** The structure sheaf is placed in degree zero
throughout, which is the degree in which it is the unit of the total tensor complex. The
dévissage of Stacks 0944 also needs `𝒪_D[i]` for `i ≠ 0`, where the identification to prove is
`Tot(K ⊗ 𝒪_D[i]) ≅ K⟦-i⟧` rather than `Tot(K ⊗ 𝒪_D[0]) ≅ K`; that is
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_singleUnitor`, not this file.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

/-! ## A complex concentrated in degree zero, in the degree zero -/

section Bookkeeping

variable {V W : Type*} [Category V] [Category W] [HasZeroMorphisms V] [HasZeroObject V]

/-- **The degree-zero term of a complex concentrated in degree zero is the object itself, on the
nose.** The term is `if (0 : ℤ) = 0 then M else 0`, which reduces to `M`, so the identification
`HomologicalComplex.singleObjXSelf` is the identity there. The identity is written at the source
of that identification, which is the spelling a further functor application consumes. -/
private lemma singleObjXSelf_zero_hom (M : V) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom =
      𝟙 (((HomologicalComplex.single V (ComplexShape.up ℤ) 0).obj M).X 0) := rfl

/-- The inverse of `HomologicalComplex.singleObjXSelf` in degree zero is likewise the
identity. -/
private lemma singleObjXSelf_zero_inv (M : V) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).inv = 𝟙 M := rfl

/-- The image of that identification under a functor is an identity. The identity is written at
the degree-zero term of `M[0]`, which is the spelling the functor application forces. -/
private lemma map_singleObjXSelf_zero_hom [HasZeroMorphisms W] (G : V ⥤ W) (M : V) :
    G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom =
      𝟙 (G.obj (((HomologicalComplex.single V (ComplexShape.up ℤ) 0).obj M).X 0)) :=
  (eqToHom_map G (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (0 : ℤ) M)).trans
    (eqToHom_refl _ _)

end Bookkeeping

/-! ## The identification of a shift by zero, and of a total complex with one row -/

section SingleRow

variable {A : Type*} [Category A] [Preadditive A]

/-- **The identification of a shift by `a = 0` with the identity, in a single degree.** Both it
and the identification of the degree-`n` term of `K⟦a⟧` with that of `K` are transports along an
equality of indices, so they agree. -/
private lemma shiftFunctorZero'_inv_app_f (W : CochainComplex A ℤ) (a : ℤ) (ha : a = 0)
    (n : ℤ) :
    ((CategoryTheory.shiftFunctorZero' (CochainComplex A ℤ) a ha).inv.app W).f n =
      (W.XIsoOfEq (show n + a = n by rw [ha, add_zero])).inv := by
  subst ha
  simp [CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f,
    HomologicalComplex.XIsoOfEq]

variable [HasZeroObject A]

open StacksDraft.TotalSingleRow in
/-- **The comparison `W⟦-q⟧ ⟶ Tot(singleRow W q)` in a single degree**, with the index of the
one possibly nonzero summand supplied as a variable together with the equation it satisfies.
Writing it this way is what lets the comparison be used at `q = 0`, where the index of that
summand is `n + -0` and not `n`. -/
private lemma totalSingleRowUnit_f (W : CochainComplex A ℤ) (q n p : ℤ) (hp : n + -q = p)
    [(singleRow W q).HasTotal (ComplexShape.up ℤ)] :
    (totalSingleRowUnit W q).f n =
      (q * n).negOnePow • ((W.XIsoOfEq hp).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (W.X p)).inv ≫
          (singleRow W q).ιTotal (ComplexShape.up ℤ) p q n (by dsimp; omega)) := by
  subst hp
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  rfl

end SingleRow

/-! ## The single-row identification of a total complex, on a summand -/

section TotalSingle

open CochainComplex.KFlatBifunctor StacksDraft.TotalSingleRow

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **The inverse of the single-row identification `Tot(F(K, M[0])) ≅ (p ↦ F(K^p, M))`, in a
single degree**: it lands in the one summand of total degree `n` that does not vanish, namely
the one of bidegree `(n, 0)`. -/
lemma totalSingleIso_inv_f (K : CochainComplex A ℤ) (M : B) (n : ℤ) :
    (totalSingleIso F K M).inv.f n =
      (F.obj (K.X n)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).inv ≫
        HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          n 0 n (add_zero n) := by
  have hT : (singleRow (rowComplex F K M) 0).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M 0) _
  have hI : IsIso (totalSingleRowUnit (rowComplex F K M) 0) :=
    isIso_totalSingleRowUnit (rowComplex F K M) 0
  have h1 : (totalSingleIso F K M).inv.f n =
      ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).inv.app
            (rowComplex F K M) ≫ totalSingleRowUnit (rowComplex F K M) 0).f n ≫
        (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).inv
          (ComplexShape.up ℤ)).f n := rfl
  have h2 : ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).inv.app
        (rowComplex F K M) ≫ totalSingleRowUnit (rowComplex F K M) 0).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          ((rowComplex F K M).X n)).inv ≫
        (singleRow (rowComplex F K M) 0).ιTotal (ComplexShape.up ℤ) n 0 n (add_zero n) := by
    rw [HomologicalComplex.comp_f,
      shiftFunctorZero'_inv_app_f (rowComplex F K M) (-0 : ℤ) neg_zero n,
      totalSingleRowUnit_f (rowComplex F K M) 0 n n (by omega), zero_mul,
      Int.negOnePow_zero, one_smul, Iso.inv_hom_id_assoc]
  have h3 : (singleRow (rowComplex F K M) 0).ιTotal (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
        (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).inv
          (ComplexShape.up ℤ)).f n =
      ((mapBifunctorSingleIso F K M 0).inv.f n).f 0 ≫
        HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          n 0 n (add_zero n) := by
    rw [HomologicalComplex₂.ιTotal_map]
  have h4 : ((mapBifunctorSingleIso F K M 0).inv.f n).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          ((rowComplex F K M).X n)).hom ≫
        (F.obj (K.X n)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self (F.obj (K.X n))
      (ComplexShape.up ℤ) 0 M
  refine h1.trans ?_
  refine (congrArg (fun z => z ≫ (HomologicalComplex₂.total.map
    (mapBifunctorSingleIso F K M 0).inv (ComplexShape.up ℤ)).f n) h2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    ((rowComplex F K M).X n)).inv ≫ z) h3).trans ?_
  refine (congrArg (fun z => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
      ((rowComplex F K M).X n)).inv ≫ z ≫
    HomologicalComplex.ιMapBifunctor K
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
      n 0 n (add_zero n)) h4).trans ?_
  refine (congrArg (fun z => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    ((rowComplex F K M).X n)).inv ≫ z) (Category.assoc _ _ _)).trans ?_
  exact Iso.inv_hom_id_assoc _ _

/-- **The single-row identification `Tot(F(K, M[0])) ≅ (p ↦ F(K^p, M))` on the one summand of
total degree `n` that does not vanish**: on the summand of bidegree `(n, 0)` it is the
identification of the degree-zero term of `M[0]` with `M`. -/
lemma ι_totalSingleIso_hom (K : CochainComplex A ℤ) (M : B) (n : ℤ) :
    HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          n 0 n (add_zero n) ≫
        (totalSingleIso F K M).hom.f n =
      (F.obj (K.X n)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
  refine (cancel_epi ((F.obj (K.X n)).map
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).inv)).1 ?_
  have hih : (totalSingleIso F K M).inv.f n ≫ (totalSingleIso F K M).hom.f n =
      𝟙 ((rowComplex F K M).X n) := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (fun z => z ≫ (totalSingleIso F K M).hom.f n)
    (totalSingleIso_inv_f F K M n)).symm.trans (hih.trans (Iso.inv_hom_id_map _ _).symm)

end TotalSingle

/-! ## The unit law of the total tensor complex, on a summand -/

section TensorUnit

universe u

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **The unit law `A ⊗_𝒪 𝒪 ≅ A` of Tag 06YM at one sheaf of modules**, with its source spelled
as an application of the tensor bifunctor rather than through
`CategoryTheory.Functor.flip`. This is
`Stacks.SheafOfModules.sheafTensorUnitNatIso` at that sheaf, and the spelling is the only
difference; declaring it absorbs that definitional equality into a declared type. -/
def tensorUnitRight (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≅ A :=
  (Stacks.SheafOfModules.sheafTensorUnitNatIso R).app A

omit [∀ (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- The termwise unit law `(p ↦ K^p ⊗_𝒪 𝒪) ≅ K` in a single degree is the unit law of the tensor
product there. -/
private lemma rowComplexUnitIso_hom_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (n : ℤ) :
    (Stacks.SheafOfModules.rowComplexUnitIso R K).hom.f n = (tensorUnitRight R (K.X n)).hom :=
  Category.comp_id _

/-- **The inclusion of the summand of bidegree `(n, 0)` of `Tot(K ⊗_𝒪 𝒪[0])`**, with its source
spelled with the structure sheaf rather than with the degree-zero term of `𝒪[0]`. -/
def ιUnitSummand
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (K.X n)).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ⟶
      (HomologicalComplex.mapBifunctor K
        ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
            (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)).X n :=
  HomologicalComplex.ιMapBifunctor K
    ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
        (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
    (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) n 0 n (add_zero n)

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` of Tag 06YM, with its source spelled as a total
complex.** This is `Stacks.SheafOfModules.tensorComplexUnitIso` — see
`mapBifunctorUnitIso_hom_eq` — and the spelling of the source is the only difference. It is
forced rather than chosen: the comparison of total tensor complexes has
`HomologicalComplex.mapBifunctor` as its target, while the unit law is stated with
`Stacks.SheafOfModules.Tensor.tensorComplex`, and the two are definitionally equal only at
*default* transparency, so a composite carrying both is a term in which
`HomologicalComplex.comp_f` cannot find its pattern. -/
def mapBifunctorUnitIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    HomologicalComplex.mapBifunctor K
        ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
            (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≅ K :=
  CochainComplex.KFlatBifunctor.totalSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≪≫
    Stacks.SheafOfModules.rowComplexUnitIso R K

/-- The restated unit law is the unit law of Tag 06YM. -/
lemma mapBifunctorUnitIso_hom_eq
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    (mapBifunctorUnitIso R K).hom =
      (Stacks.SheafOfModules.tensorComplexUnitIso R K).hom := rfl

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` on the one summand of total degree `n` that does not
vanish**: on the summand of bidegree `(n, 0)` it is the unit law `K^n ⊗_𝒪 𝒪 ≅ K^n` of the tensor
product. -/
lemma ι_mapBifunctorUnitIso_hom
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (n : ℤ) :
    ιUnitSummand R K n ≫ (mapBifunctorUnitIso R K).hom.f n = (tensorUnitRight R (K.X n)).hom := by
  have hsplit : (mapBifunctorUnitIso R K).hom.f n =
      (CochainComplex.KFlatBifunctor.totalSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor R) K
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom.f n ≫
        (Stacks.SheafOfModules.rowComplexUnitIso R K).hom.f n := rfl
  refine (congrArg (fun z => ιUnitSummand R K n ≫ z) hsplit).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (Stacks.SheafOfModules.rowComplexUnitIso R K).hom.f n)
    (ι_totalSingleIso_hom (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) n)).trans ?_
  refine (congrArg (fun z => z ≫ (Stacks.SheafOfModules.rowComplexUnitIso R K).hom.f n)
    (map_singleObjXSelf_zero_hom _ _)).trans ?_
  exact (Category.id_comp _).trans (rowComplexUnitIso_hom_f R K n)

/-- **The inverse of the unit law, in a single degree**: it is the inverse unit law of the tensor
product followed by the inclusion of the summand of bidegree `(n, 0)`. -/
lemma mapBifunctorUnitIso_inv_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (n : ℤ) :
    (mapBifunctorUnitIso R K).inv.f n =
      (tensorUnitRight R (K.X n)).inv ≫ ιUnitSummand R K n := by
  exact ((Iso.inv_comp_eq _).2 ((Iso.eq_comp_inv
    ((HomologicalComplex.eval _ _ n).mapIso (mapBifunctorUnitIso R K))).2
      (ι_mapBifunctorUnitIso_hom R K n))).symm

end TensorUnit

/-! ## The right-unitor coherence at the level of complexes -/

section Complexes

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

/-- The structure sheaf of the target, placed in degree zero. -/
abbrev unitComplexTarget :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ :=
  (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)
      0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The structure sheaf of the source, placed in degree zero. -/
abbrev unitComplexSource :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
      0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The ordinary unit comparison `f^*𝒪_D ⟶ 𝒪_C`** of
`SheafOfModules.pullbackObjUnitToUnit`, with its source and target spelled through
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` and
`Stacks.SheafOfModules.Tensor.ringSheaf`, which is the spelling the module-level right-unitor
coherence is stated at. -/
def pullbackUnitComparison :
    f.pullbackTopos.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing

/-- **The unit comparison `f^*(𝒪_D[0]) ⟶ 𝒪_C[0]` on complexes**: the degreewise pullback of the
structure sheaf in degree zero is the pullback of the structure sheaf in degree zero, and that is
carried to the structure sheaf of the source by the ordinary comparison. This is the morphism of
complexes underlying `Stacks.Sheaves.DerivedPullback.derivedPullbackUnitMap`. -/
def pullbackUnitComplexMap :
    (pullbackComplex f).obj (unitComplexTarget (Y := Y)) ⟶ unitComplexSource (X := X) :=
  ((HomologicalComplex.singleMapHomologicalComplex f.pullbackTopos (ComplexShape.up ℤ) 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom ≫
    (HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).map (pullbackUnitComparison f)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- In degree zero the unit comparison on complexes is the ordinary comparison
`f^*𝒪_D ⟶ 𝒪_C`. -/
lemma pullbackUnitComplexMap_f_zero :
    (pullbackUnitComplexMap f).f 0 = pullbackUnitComparison f := by
  have h1 : (pullbackUnitComplexMap f).f 0 =
      ((HomologicalComplex.singleMapHomologicalComplex f.pullbackTopos
            (ComplexShape.up ℤ) 0).app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom.f 0 ≫
        ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map (pullbackUnitComparison f)).f 0 := rfl
  have h2 : ((HomologicalComplex.singleMapHomologicalComplex f.pullbackTopos
          (ComplexShape.up ℤ) 0).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom.f 0 =
      f.pullbackTopos.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (f.pullbackTopos.obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).inv :=
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self f.pullbackTopos
      (ComplexShape.up ℤ) 0 _
  have h3 : ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map (pullbackUnitComparison f)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (f.pullbackTopos.obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom ≫
        pullbackUnitComparison f ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv :=
    HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 (pullbackUnitComparison f)
  rw [h1, h2, h3, Category.assoc, Iso.inv_hom_id_assoc, map_singleObjXSelf_zero_hom]
  refine (Category.id_comp _).trans ?_
  refine (congrArg (fun z => pullbackUnitComparison f ≫ z) (singleObjXSelf_zero_inv
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).trans ?_
  exact Category.comp_id _

/-- **The inclusion of the summand of bidegree `(n, 0)` of `Tot(f^*K ⊗_{𝒪_C} f^*(𝒪_D[0]))`**,
with its source spelled with the pullback of the structure sheaf rather than with the degree-zero
term of the degreewise pullback of `𝒪_D[0]`. -/
def ιPullSummand
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (((pullbackComplex f).obj K).X n)).obj
        (f.pullbackTopos.obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
      (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K)
        ((pullbackComplex f).obj (unitComplexTarget (Y := Y)))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)).X n :=
  HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K)
    ((pullbackComplex f).obj (unitComplexTarget (Y := Y)))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) n 0 n (add_zero n)

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)

set_option maxHeartbeats 1000000 in
-- The kernel check of the `rw` below exceeds the default heartbeats under Lean v4.35.0.
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **The module-level right-unitor coherence, read at the module of degree `n` of a complex.**
This is `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` at `A = K^n`, with the
comparison of Stacks 03EL spelled at the degrees of the pullback complexes, as
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg` is. The seam between that spelling and
the pullbacks of the degrees is crossed by `pullbackToposTensorMapDeg_eq`, which is where it has
already been paid for. -/
lemma rightUnitorCoherence_deg
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) :
    pullbackToposTensorMapDeg f hmos K (unitComplexTarget (Y := Y)) n 0 ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (((pullbackComplex f).obj K).X n)).map (pullbackUnitComparison f) ≫
          (tensorUnitRight X.O (((pullbackComplex f).obj K).X n)).hom =
      f.pullbackTopos.map (tensorUnitRight Y.O (K.X n)).hom := by
  rw [pullbackToposTensorMapDeg_eq]
  exact pullbackToposRightUnitorCoherence f hmos (K.X n)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The second and third factors of the left-hand side of the right-unitor coherence on
complexes, on the summand of bidegree `(n, 0)`. -/
private lemma ι_rightUnitor_lhs
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) :
    ιPullSummand f K n ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
            (pullbackUnitComplexMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ)).f n ≫
          (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom.f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            (((pullbackComplex f).obj K).X n)).map (pullbackUnitComparison f) ≫
        (tensorUnitRight X.O (((pullbackComplex f).obj K).X n)).hom := by
  have h1 : ιPullSummand f K n ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackUnitComplexMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)).f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            (𝟙 (((pullbackComplex f).obj K).X n))).app
          (((pullbackComplex f).obj (unitComplexTarget (Y := Y))).X 0) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            (((pullbackComplex f).obj K).X n)).map ((pullbackUnitComplexMap f).f 0) ≫
          ιUnitSummand X.O ((pullbackComplex f).obj K) n :=
    HomologicalComplex.ι_mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
      (pullbackUnitComplexMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ) n 0 n (add_zero n)
  have h2 : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
          (𝟙 (((pullbackComplex f).obj K).X n))).app
        (((pullbackComplex f).obj (unitComplexTarget (Y := Y))).X 0) =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (((pullbackComplex f).obj K).X n)).obj
        (((pullbackComplex f).obj (unitComplexTarget (Y := Y))).X 0)) := by
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app]
  refine (congrArg (fun z => z ≫ (mapBifunctorUnitIso X.O
    ((pullbackComplex f).obj K)).hom.f n) h1).trans ?_
  refine (congrArg (fun z => (z ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (((pullbackComplex f).obj K).X n)).map ((pullbackUnitComplexMap f).f 0) ≫
        ιUnitSummand X.O ((pullbackComplex f).obj K) n) ≫
      (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom.f n) h2).trans ?_
  refine (congrArg (fun z => z ≫
    (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom.f n)
    (Category.id_comp _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
      (((pullbackComplex f).obj K).X n)).map ((pullbackUnitComplexMap f).f 0) ≫ z)
    (ι_mapBifunctorUnitIso_hom X.O ((pullbackComplex f).obj K) n)).trans ?_
  exact congrArg (fun z => ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
      (((pullbackComplex f).obj K).X n)).map z ≫
    (tensorUnitRight X.O (((pullbackComplex f).obj K).X n)).hom)
    (pullbackUnitComplexMap_f_zero f)

/-- The right-unitor coherence on complexes, in a single degree, after the unit law of the target
has been cancelled: the composite is the identity. -/
private lemma rightUnitor_degree
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) :
    f.pullbackTopos.map ((mapBifunctorUnitIso Y.O K).inv.f n) ≫
        (pullbackToposTensorTotalIso f hmos K (unitComplexTarget (Y := Y))).hom.f n ≫
          (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
              (pullbackUnitComplexMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
              (ComplexShape.up ℤ)).f n ≫
            (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom.f n =
      𝟙 (f.pullbackTopos.obj (K.X n)) := by
  have h1 : f.pullbackTopos.map ((mapBifunctorUnitIso Y.O K).inv.f n) =
      f.pullbackTopos.map (tensorUnitRight Y.O (K.X n)).inv ≫
        f.pullbackTopos.map (ιUnitSummand Y.O K n) := by
    rw [mapBifunctorUnitIso_inv_f]
    exact f.pullbackTopos.map_comp _ _
  have h2 : f.pullbackTopos.map (ιUnitSummand Y.O K n) ≫
        (pullbackToposTensorTotalIso f hmos K (unitComplexTarget (Y := Y))).hom.f n =
      pullbackToposTensorMapDeg f hmos K (unitComplexTarget (Y := Y)) n 0 ≫
        ιPullSummand f K n :=
    ι_pullbackToposTensorTotalIso_hom f hmos K (unitComplexTarget (Y := Y)) n 0 n (add_zero n)
  refine (congrArg (fun z => z ≫
      (pullbackToposTensorTotalIso f hmos K (unitComplexTarget (Y := Y))).hom.f n ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
            (pullbackUnitComplexMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ)).f n ≫
          (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom.f n) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => f.pullbackTopos.map (tensorUnitRight Y.O (K.X n)).inv ≫ z)
    (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun z => f.pullbackTopos.map (tensorUnitRight Y.O (K.X n)).inv ≫ z ≫
      ((HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackUnitComplexMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)).f n ≫
        (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom.f n)) h2).trans ?_
  refine (congrArg (fun z => f.pullbackTopos.map (tensorUnitRight Y.O (K.X n)).inv ≫ z)
    (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun z => f.pullbackTopos.map (tensorUnitRight Y.O (K.X n)).inv ≫
    pullbackToposTensorMapDeg f hmos K (unitComplexTarget (Y := Y)) n 0 ≫ z)
    (ι_rightUnitor_lhs f K n)).trans ?_
  refine (congrArg (fun z => f.pullbackTopos.map (tensorUnitRight Y.O (K.X n)).inv ≫ z)
    (rightUnitorCoherence_deg f hmos K n)).trans ?_
  exact Iso.inv_hom_id_map _ _

/-- **The right-unitor coherence of the comparison of total tensor complexes.** The comparison
`f^*Tot(K ⊗_{𝒪_D} 𝒪_D[0]) ≅ Tot(f^*K ⊗_{𝒪_C} f^*(𝒪_D[0]))`, followed by the unit comparison in
the second tensor factor and by the unit law of the total tensor complex of the source, is the
degreewise pullback of the unit law of the target.

The unit law of the target is an isomorphism, so it is enough to prove the identity after
precomposing with its inverse; that turns both sides into morphisms out of `f^*K`, where in each
degree the left-hand side begins with the degreewise pullback of the inclusion of the summand of
bidegree `(n, 0)`. The summandwise formula `ι_pullbackToposTensorTotalIso_hom` then produces the
degreewise comparison of Stacks 03EL, and `ι_rightUnitor_lhs` together with
`rightUnitorCoherence_deg` is the module-level right-unitor coherence at `K^n`. -/
theorem pullbackToposTensorTotalIso_rightUnitor
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackToposTensorTotalIso f hmos K (unitComplexTarget (Y := Y))).hom ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
            (pullbackUnitComplexMap f) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ) ≫
          (mapBifunctorUnitIso X.O ((pullbackComplex f).obj K)).hom =
      (pullbackComplex f).map (mapBifunctorUnitIso Y.O K).hom := by
  refine (cancel_epi ((pullbackComplex f).map (mapBifunctorUnitIso Y.O K).inv)).1 ?_
  rw [Iso.inv_hom_id_map]
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.id_f, CategoryTheory.Functor.mapHomologicalComplex_map_f]
  exact rightUnitor_degree f hmos K n

end Complexes

end Stacks.Sheaves.DerivedPullback

end

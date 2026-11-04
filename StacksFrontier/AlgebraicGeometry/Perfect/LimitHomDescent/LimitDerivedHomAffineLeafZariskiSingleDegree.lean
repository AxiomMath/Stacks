module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.LimitDerivedHomUnitColimRingSystemGlue

/-!
# Maps out of the structure sheaf in an arbitrary degree, along a directed system of rings

`Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq_source` and
`Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Q_map_ext_single_eq` are the two clauses of
the affine case of Stacks 09RE at the first argument `R[0]`: morphisms `A[0] ⟶ A ⊗_R C'` in
`D(A)` are the filtered colimit of the `A_j[0] ⟶ A_j ⊗_R C'`, for an arbitrary complex `C'` of
`R`-modules.  **This file states the same two clauses with `R[0]` replaced by `R[j]`, the
structure sheaf in an arbitrary degree `j`.**

The affine leaf of Stacks 09RI needs every degree, not only `0`: the hypothesis the dévissage
consumes is `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim` of
`StacksFrontier/CategoryTheory/PullbackData/LimitSystemColimShift.lean`, which quantifies the
colimit statement over *all* shifts `n` of its first argument, and the shift of the structure
sheaf by `n` is the structure sheaf in degree `-n` (the same reindexing that
`AlgebraicGeometry.Space.representedAffineUnitObjShiftIso` performs on the geometric side).  So
every statement that computes the leaf at the structure sheaf is needed at every degree, and the
existing ones are stated at `0` alone.

Nothing in the argument depends on the degree.  Each of the three facts that the degree-`0`
statements discharge at `0` holds at `j` for the same reason:

* `A ⊗_R R[j]` is strictly bounded above by `j` rather than by `0`, and its only possibly
  nonzero term is projective because extension of scalars is a left adjoint whose right adjoint
  preserves epimorphisms — so it is K-projective by
  `CochainComplex.isKProjective_of_projective` at the bound `j`;
* `R[j]` has finitely many nonzero terms and they are finitely presented;
* `A ⊗_R R[j] ≅ A[j]`, by the same two factors as
  `Stacks.LimitHomDescent.Affine.extSingleSelfIso`.

## Main definitions

* `Stacks.LimitHomDescent.Affine.extSingleDegreeSelfIso`: **`A ⊗_R R[j] ≅ A[j]`**, which at
  `j = 0` is `Stacks.LimitHomDescent.Affine.extSingleSelfIso` on the nose
  (`extSingleDegreeSelfIso_zero`).

## Main results

* `Stacks.LimitHomDescent.Affine.isKProjective_ext_singleDegree`: `A ⊗_R R[j]` is K-projective.
* `Stacks.LimitHomDescent.Affine.finitePresentation_singleDegree_X`: the terms of `R[j]` are
  finitely presented.
* `Stacks.LimitHomDescent.Affine.extSingleDegreeSelfIso_hom_comp` and
  `extSingleDegreeSelfIso_inv_comp_map`: the identification is compatible with the two-step
  comparison `Stacks.LimitHomDescent.Affine.extCompIsoOf`.
* `Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Q_map_ext_singleDegree_eq`: **eventual
  injectivity at the first argument `R[j]`.**
* `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_singleDegree_eq` and
  `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_singleDegree_eq_source`: **every
  map over the colimit comes from a stage, at the first argument `R[j]`** — the second with the
  source read as the structure sheaf `A_j[j]` rather than as `A_j ⊗_R R[j]`.

## References

* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace Stacks.LimitHomDescent.Affine

variable {R A A' : CommRingCat.{u}}

/-! ### K-projectivity and finite presentation in an arbitrary degree -/

/-- **`A ⊗_R R[j]` is K-projective**: it is strictly bounded above by `j` and its terms are
projective, the one in degree `j` because extension of scalars preserves projective objects and
the others because they vanish.

This is `Stacks.LimitHomDescent.Affine.isKProjective_ext_single` with the degree `0` replaced by
an arbitrary `j`; nothing in its argument used `j = 0` beyond the bound handed to
`CochainComplex.isKProjective_of_projective`. -/
theorem isKProjective_ext_singleDegree (f : R ⟶ A) (j : ℤ) :
    ((ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
      (ModuleCat.of R R))).IsKProjective := by
  have hz : ∀ n : ℤ, n ≠ j → IsZero (((ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R)
      (ComplexShape.up ℤ) j).obj (ModuleCat.of R R))).X n) := fun n hn =>
    (ModuleCat.extendScalars.{u, u, u} f.hom).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j (ModuleCat.of R R) n hn)
  have : CochainComplex.IsStrictlyLE ((ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R)
      (ComplexShape.up ℤ) j).obj (ModuleCat.of R R))) j := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => hz n (by omega)
  have : ∀ n : ℤ, Projective (((ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R)
      (ComplexShape.up ℤ) j).obj (ModuleCat.of R R))).X n) := by
    intro n
    by_cases hn : n = j
    · subst hn
      exact Projective.of_iso ((ModuleCat.extendScalars.{u, u, u} f.hom).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of R R))).symm
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).map_projective
          (ModuleCat.of R R) inferInstance)
    · exact (hz n hn).projective
  exact CochainComplex.isKProjective_of_projective _ j

/-- Every term of `R[j]` is a finitely presented `R`-module. -/
theorem finitePresentation_singleDegree_X (R : CommRingCat.{u}) (j n : ℤ) :
    Module.FinitePresentation R
      (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
        (ModuleCat.of R R)).X n) := by
  by_cases hn : n = j
  · subst hn
    have : Module.FinitePresentation R (ModuleCat.of R R) :=
      inferInstanceAs (Module.FinitePresentation R R)
    exact Module.FinitePresentation.of_equiv
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
        (ModuleCat.of R R)).symm.toLinearEquiv
  · have : Subsingleton (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
        (ModuleCat.of R R)).X n) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j (ModuleCat.of R R) n hn)
    infer_instance

/-! ### `A ⊗_R R[j] ≅ A[j]` -/

/-- **`A ⊗_R R[j] ≅ A[j]`**: extension of scalars carries the one-term complex `R` in degree `j`
to the one-term complex `A ⊗_R R` in degree `j`, and `A ⊗_R R ≅ A`.

`Stacks.LimitHomDescent.Affine.extSingleSelfIso` in an arbitrary degree. -/
def extSingleDegreeSelfIso (f : R ⟶ A) (j : ℤ) :
    (ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
        (ModuleCat.of R R)) ≅
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) j).obj
        (ModuleCat.of A A) :=
  (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} f.hom)
      (ComplexShape.up ℤ) j).app (ModuleCat.of R R) ≪≫
    (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) j).mapIso
      (ModuleCat.ExtendScalars.objSelfIso.{u} f.hom)

/-- **In degree `0` this is `Stacks.LimitHomDescent.Affine.extSingleSelfIso`**, on the nose: the
existing identification is the one above at `j = 0`, so nothing below is a second notion. -/
theorem extSingleDegreeSelfIso_zero (f : R ⟶ A) :
    extSingleDegreeSelfIso f 0 = extSingleSelfIso f := rfl

/-- **`extSingleDegreeSelfIso` is compatible with `extCompIsoOf`.**  For a factorisation
`f ≫ β = f'`, identifying `A ⊗_R R[j]` with `A[j]` and then `A' ⊗_A A[j]` with `A'[j]` is
identifying `A' ⊗_A (A ⊗_R R[j])` with `A' ⊗_R R[j]` and then with `A'[j]`.

`Stacks.LimitHomDescent.Affine.extSingleSelfIso_hom_comp` in an arbitrary degree: degreewise
away from `j` both sides land in a zero object, and in degree `j` the two
`HomologicalComplex.singleObjXSelf` identifications cancel and the naturality of
`ModuleCat.extendScalarsComp` reduces the claim to
`ModuleCat.ExtendScalars.objSelfIso_inv_comp_map_objSelfIso_inv`. -/
theorem extSingleDegreeSelfIso_hom_comp (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A') (h : f ≫ β = f')
    (j : ℤ) :
    (ext β).map (extSingleDegreeSelfIso f j).hom ≫ (extSingleDegreeSelfIso β j).hom =
      (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) j).obj (ModuleCat.of R R))).hom ≫
        (extSingleDegreeSelfIso f' j).hom := by
  subst h
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = j
  · subst hn
    simp only [HomologicalComplex.comp_f, extSingleDegreeSelfIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapHomologicalComplex_map_f, Functor.mapIso_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, extCompIsoOf, extComp,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      eqToIso_refl, Iso.refl_hom, Category.comp_id, CommRingCat.hom_comp,
      Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.symm_hom,
      Iso.map_inv_hom_id_assoc, NatTrans.mapHomologicalComplex]
    rw [ModuleCat.ExtendScalars.map_map_comp_objSelfIso_hom]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j
      (ModuleCat.of (A' : Type u) (A' : Type u)) n hn).eq_of_tgt _ _

/-- **The inverse form of `Stacks.LimitHomDescent.Affine.extSingleDegreeSelfIso_hom_comp`.** -/
theorem extSingleDegreeSelfIso_inv_comp (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A') (h : f ≫ β = f')
    (j : ℤ) :
    (extSingleDegreeSelfIso β j).inv ≫ (ext β).map (extSingleDegreeSelfIso f j).inv =
      (extSingleDegreeSelfIso f' j).inv ≫
        (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) j).obj (ModuleCat.of R R))).inv :=
  (Iso.inv_eq_inv ((ext β).mapIso (extSingleDegreeSelfIso f j) ≪≫ extSingleDegreeSelfIso β j)
      (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) j).obj (ModuleCat.of R R)) ≪≫
        extSingleDegreeSelfIso f' j)).mpr
    (extSingleDegreeSelfIso_hom_comp f β f' h j)

/-- **Conjugating a chain map out of `A ⊗_R R[j]` by `extSingleDegreeSelfIso` commutes with the
two-step comparison.**  `Stacks.LimitHomDescent.Affine.extSingleSelfIso_inv_comp_map` in an
arbitrary degree. -/
theorem extSingleDegreeSelfIso_inv_comp_map (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A')
    (h : f ≫ β = f') (j : ℤ) {C' : CochainComplex (ModuleCat.{u} R) ℤ}
    (t : (ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
      (ModuleCat.of R R)) ⟶ (ext f).obj C') :
    (extSingleDegreeSelfIso β j).inv ≫ (ext β).map ((extSingleDegreeSelfIso f j).inv ≫ t) ≫
        (extCompIsoOf f β f' h C').hom =
      (extSingleDegreeSelfIso f' j).inv ≫
        (extCompIsoOf f β f' h ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℤ) j).obj (ModuleCat.of R R))).inv ≫
          (ext β).map t ≫ (extCompIsoOf f β f' h C').hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (extSingleDegreeSelfIso_inv_comp f β f' h j)]

/-! ### The two clauses at the first argument `R[j]` -/

namespace RingSystem

variable {J : Type v} [Preorder J] (S : RingSystem.{v, u} R J) [IsDirected J (· ≤ ·)] [Nonempty J]
  (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
    (fun j (x : S.A j) => S.γ j x))
  {C' : CochainComplex (ModuleCat.{u} R) ℤ}

include hcol in
/-- **Eventual injectivity in the derived category at the first argument `R[j]`**: two chain maps
`R[j] ⟶ C'` whose extensions to the colimit `A` agree in `D(A)` already have extensions to some
stage `A_j` agreeing in `D(A_j)`.

`Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Q_map_ext_single_eq` in an arbitrary
degree. -/
theorem exists_le_Q_map_ext_singleDegree_eq (j : ℤ)
    (u w : (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
      (ModuleCat.of R R) ⟶ C')
    (h : DerivedCategory.Q.map ((ext S.φlim).map u) =
      DerivedCategory.Q.map ((ext S.φlim).map w)) :
    ∃ i : J, DerivedCategory.Q.map ((ext (S.φ i)).map u) =
      DerivedCategory.Q.map ((ext (S.φ i)).map w) :=
  have := isKProjective_ext_singleDegree S.φlim j
  S.exists_le_Q_map_ext_eq hcol (finite_support_single_obj j (ModuleCat.of R R))
    (finitePresentation_singleDegree_X R j) u w h

include hcol in
/-- **Every map over the colimit comes from a stage, in the derived category, at the first
argument `R[j]`**: a morphism `A ⊗_R R[j] ⟶ A ⊗_R C'` of `D(A)` is `A ⊗_{A_i} t` for a chain map
`t : A_i ⊗_R R[j] ⟶ A_i ⊗_R C'` at some stage `i`, for an arbitrary complex `C'`.

`Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq` in an arbitrary
degree. -/
theorem exists_Q_map_ext_singleDegree_eq (j : ℤ)
    (v : DerivedCategory.Q.obj ((ext S.φlim).obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
          (ModuleCat.of R R))) ⟶
      DerivedCategory.Q.obj ((ext S.φlim).obj C')) :
    ∃ (i : J) (t : (ext (S.φ i)).obj ((HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℤ) j).obj (ModuleCat.of R R)) ⟶ (ext (S.φ i)).obj C'),
      DerivedCategory.Q.map ((extCompIsoOf (S.φ i) (S.γ i) S.φlim (S.φ_γ i)
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
            (ModuleCat.of R R))).inv ≫
        (ext (S.γ i)).map t ≫
          (extCompIsoOf (S.φ i) (S.γ i) S.φlim (S.φ_γ i) C').hom) = v :=
  have := isKProjective_ext_singleDegree S.φlim j
  S.exists_Q_map_ext_eq hcol (finite_support_single_obj j (ModuleCat.of R R))
    (finitePresentation_singleDegree_X R j) v

include hcol in
/-- **Every map out of the structure sheaf in degree `j` over the colimit comes from a stage, in
the derived category.**  A morphism `A[j] ⟶ A ⊗_R C'` of `D(A)` is `A ⊗_{A_i} t` for a chain map
`t : A_i[j] ⟶ A_i ⊗_R C'` at some stage `i`, the source being read through
`Stacks.LimitHomDescent.Affine.extSingleDegreeSelfIso` at both ends.

`Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq_source` in an arbitrary
degree, conjugated by `extSingleDegreeSelfIso` exactly as that one is by `extSingleSelfIso`. -/
theorem exists_Q_map_ext_singleDegree_eq_source (j : ℤ)
    (v : DerivedCategory.Q.obj ((HomologicalComplex.single (ModuleCat.{u} S.lim)
        (ComplexShape.up ℤ) j).obj (ModuleCat.of S.lim S.lim)) ⟶
      DerivedCategory.Q.obj ((ext S.φlim).obj C')) :
    ∃ (i : J) (t : (HomologicalComplex.single (ModuleCat.{u} (S.A i)) (ComplexShape.up ℤ) j).obj
        (ModuleCat.of (S.A i) (S.A i)) ⟶ (ext (S.φ i)).obj C'),
      DerivedCategory.Q.map ((extSingleDegreeSelfIso (S.γ i) j).inv ≫ (ext (S.γ i)).map t ≫
        (extCompIsoOf (S.φ i) (S.γ i) S.φlim (S.φ_γ i) C').hom) = v := by
  obtain ⟨i, t, ht⟩ := S.exists_Q_map_ext_singleDegree_eq hcol j
    (DerivedCategory.Q.map (extSingleDegreeSelfIso S.φlim j).hom ≫ v)
  refine ⟨i, (extSingleDegreeSelfIso (S.φ i) j).inv ≫ t, ?_⟩
  rw [extSingleDegreeSelfIso_inv_comp_map (S.φ i) (S.γ i) S.φlim (S.φ_γ i) j t, Functor.map_comp,
    ht, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end RingSystem

end Stacks.LimitHomDescent.Affine

end

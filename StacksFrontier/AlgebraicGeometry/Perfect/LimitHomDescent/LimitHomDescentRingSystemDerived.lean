module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.RingSystemHomotopy
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing

/-!
# Maps of extended complexes along a directed system of rings, in the derived category

`Stacks.LimitHomDescent.Affine.RingSystem.exists_Qh_map_ext_eq` and
`Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Qh_map_ext_eq` say that, for a directed
system of `R`-algebras `R ⟶ A_j` with colimit `A` and complexes `C`, `C'` of `R`-modules with `C`
bounded and of finitely presented terms, the maps `A ⊗_R C ⟶ A ⊗_R C'` in the **homotopy**
category are the filtered colimit of the maps `A_j ⊗_R C ⟶ A_j ⊗_R C'`.  This file states the
same two clauses in the **derived** category.

The transfer is `CochainComplex.IsKProjective.Q_map_surjective` and
`CochainComplex.IsKProjective.nonempty_homotopy_of_Q_map_eq` (the two halves of
`CochainComplex.IsKProjective.Qh_map_bijective`, read on cochain complexes): when `A ⊗_R C` is
K-projective, maps out of it in `D(A)` are maps of complexes, and two maps of complexes agreeing
in `D(A)` are homotopic.  Only the complex at the **vertex** need be K-projective — the
stage-level conclusions are obtained by applying `DerivedCategory.Q` to a homotopy, which needs
nothing.  As in the homotopy-category statements, the second complex `C'` is arbitrary.

The case the affine leaf of Stacks 09RI uses is `C = R[0]`, where `A_j ⊗_R C` is the one-term
complex `A_j ⊗_R R` and the Hom-groups are `Hom_{D(A_j)}(A_j[0], A_j ⊗_R C')`: the rings `A_j`
vary with `j`, which is what a `Stacks.LimitHomDescent.Affine.RingSystem` describes and what
`Stacks.FilteredColimitHom.exists_descends_derived` — stated for a system of complexes over one
fixed ring — cannot.  That case is `exists_Q_map_ext_single_eq` and
`exists_le_Q_map_ext_single_eq` below, where boundedness, finite presentation and
K-projectivity are all discharged, so that only the colimit hypothesis on the rings remains.

## Main definitions

* `Stacks.LimitHomDescent.Affine.extSingleSelfIso`: the identification `A ⊗_R R[0] ≅ A[0]`,
  which is what reads the statements below as statements about morphisms out of `A_j[0]`.  Its
  compatibility with `Stacks.LimitHomDescent.Affine.extCompIsoOf` is **not** proved here.

## Main results

* `Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Q_map_ext_eq`: eventual injectivity in the
  derived category.
* `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_eq`: every map over the colimit
  comes from a stage, in the derived category.
* `Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Q_map_ext_single_eq` and
  `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq`: the two clauses at the
  first argument `R[0]`, with no hypothesis on the complexes at all.

## Implementation notes

`Stacks.Homology.isKProjective_single` is not applied directly: `(ext f).obj R[0]` is `A ⊗_R -`
applied degreewise to `R[0]`, which is isomorphic to but not a `HomologicalComplex.single`
(`extSingleSelfIso`), and no transfer of `CochainComplex.IsKProjective` along an isomorphism is
available in the tree.  `isKProjective_ext_single` therefore repeats that lemma's argument —
`CochainComplex.isKProjective_of_projective` at `0`, the degree-zero term being projective
because extension of scalars is a left adjoint whose right adjoint preserves epimorphisms
(`CategoryTheory.Adjunction.map_projective`).

## References

* [Stacks Project, Tag 064B](https://stacks.math.columbia.edu/tag/064B)
* [Stacks Project, Tag 09RE](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.FilteredColimitHom (Qh)

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace Stacks.LimitHomDescent.Affine

variable {R A : CommRingCat.{u}}

/-- **`A ⊗_R R[0]` is K-projective**: it is strictly bounded above by `0` and its terms are
projective, the degree-zero one because extension of scalars preserves projective objects and
the others because they vanish. -/
theorem isKProjective_ext_single (f : R ⟶ A) :
    ((ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R R))).IsKProjective := by
  set K := (ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of R R))
  have hz : ∀ n : ℤ, n ≠ 0 → IsZero (K.X n) := fun n hn =>
    (ModuleCat.extendScalars.{u, u, u} f.hom).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R R) n hn)
  have : CochainComplex.IsStrictlyLE K 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => hz n (by omega)
  have : ∀ n : ℤ, Projective (K.X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact Projective.of_iso ((ModuleCat.extendScalars.{u, u, u} f.hom).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R))).symm
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).map_projective
          (ModuleCat.of R R) inferInstance)
    · exact (hz n hn).projective
  exact CochainComplex.isKProjective_of_projective _ 0

/-- **A complex concentrated in one degree has only finitely many nonzero terms.** -/
theorem finite_support_single_obj {𝒜 : Type*} [Category* 𝒜] [HasZeroMorphisms 𝒜]
    [HasZeroObject 𝒜] (j : ℤ) (X : 𝒜) :
    {n : ℤ | ¬ IsZero (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).obj X).X n)}.Finite :=
  (Set.finite_singleton j).subset fun n hn => not_not.1 fun hne =>
    hn (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j X n hne)

/-- Every term of `R[0]` is a finitely presented `R`-module. -/
theorem finitePresentation_single_X (R : CommRingCat.{u}) (n : ℤ) :
    Module.FinitePresentation R
      (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R R)).X n) := by
  by_cases hn : n = 0
  · subst hn
    have : Module.FinitePresentation R (ModuleCat.of R R) :=
      inferInstanceAs (Module.FinitePresentation R R)
    exact Module.FinitePresentation.of_equiv
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).symm.toLinearEquiv
  · have : Subsingleton (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R R)).X n) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R R) n hn)
    infer_instance

/-- **`A ⊗_R R[0] ≅ A[0]`**: extension of scalars carries the one-term complex `R` in degree
zero to the one-term complex `A` in degree zero.

This is the identification a consumer needs in order to read the statements below as being
about morphisms out of the structure sheaf: it is the degreewise commutation of extension of
scalars with `HomologicalComplex.single`, followed by
`ModuleCat.ExtendScalars.objSelfIso` in degree zero. -/
def extSingleSelfIso (f : R ⟶ A) :
    (ext f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R R)) ≅
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A) :=
  (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} f.hom)
      (ComplexShape.up ℤ) 0).app (ModuleCat.of R R) ≪≫
    (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapIso
      (ModuleCat.ExtendScalars.objSelfIso.{u} f.hom)

namespace RingSystem

variable {J : Type v} [Preorder J] (S : RingSystem.{v, u} R J) [IsDirected J (· ≤ ·)] [Nonempty J]
  (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
    (fun j (x : S.A j) => S.γ j x))
  {C C' : CochainComplex (ModuleCat.{u} R) ℤ} (hC : {n : ℤ | ¬ IsZero (C.X n)}.Finite)
  (hfp : ∀ n : ℤ, Module.FinitePresentation R (C.X n))

include hcol hC hfp in
/-- **Eventual injectivity in the derived category**: two chain maps `u, w : C ⟶ C'` whose
extensions to the colimit `A` agree in `D(A)` already have extensions to some stage `A_j`
agreeing in `D(A_j)`.

Only `A ⊗_R C` is assumed K-projective; the conclusion at a stage is the image under
`DerivedCategory.Q` of a homotopy. -/
theorem exists_le_Q_map_ext_eq [((ext S.φlim).obj C).IsKProjective] (u w : C ⟶ C')
    (h : DerivedCategory.Q.map ((ext S.φlim).map u) =
      DerivedCategory.Q.map ((ext S.φlim).map w)) :
    ∃ j : J, DerivedCategory.Q.map ((ext (S.φ j)).map u) =
      DerivedCategory.Q.map ((ext (S.φ j)).map w) := by
  obtain ⟨j, hj⟩ := S.exists_le_Qh_map_ext_eq hcol hC hfp u w
    (HomotopyCategory.eq_of_homotopy _ _
      (CochainComplex.IsKProjective.nonempty_homotopy_of_Q_map_eq h).some)
  exact ⟨j, DerivedCategory.Q_map_eq_of_homotopy _ (HomotopyCategory.homotopyOfEq _ _ hj)⟩

include hcol hC hfp in
/-- **Every map over the colimit comes from a stage, in the derived category**: a morphism
`A ⊗_R C ⟶ A ⊗_R C'` of `D(A)` is `A ⊗_{A_j} t` for a chain map
`t : A_j ⊗_R C ⟶ A_j ⊗_R C'` at some stage `j`. -/
theorem exists_Q_map_ext_eq [((ext S.φlim).obj C).IsKProjective]
    (v : DerivedCategory.Q.obj ((ext S.φlim).obj C) ⟶
      DerivedCategory.Q.obj ((ext S.φlim).obj C')) :
    ∃ (j : J) (t : (ext (S.φ j)).obj C ⟶ (ext (S.φ j)).obj C'),
      DerivedCategory.Q.map ((extCompIsoOf (S.φ j) (S.γ j) S.φlim (S.φ_γ j) C).inv ≫
        (ext (S.γ j)).map t ≫
          (extCompIsoOf (S.φ j) (S.γ j) S.φlim (S.φ_γ j) C').hom) = v := by
  obtain ⟨v₀, rfl⟩ := CochainComplex.IsKProjective.Q_map_surjective
    ((ext S.φlim).obj C) ((ext S.φlim).obj C') v
  obtain ⟨j, t, hj⟩ := S.exists_Qh_map_ext_eq hcol hC hfp v₀
  exact ⟨j, t, DerivedCategory.Q_map_eq_of_homotopy _ (HomotopyCategory.homotopyOfEq _ _ hj)⟩

include hcol in
/-- **Eventual injectivity in the derived category at the first argument `R[0]`**: two chain maps
`R[0] ⟶ C'` whose extensions to the colimit `A` agree in `D(A)` already have extensions to some
stage `A_j` agreeing in `D(A_j)`.

This is the Hom-side input of the structure-sheaf leaf of Stacks 09RI clause (1): the source is
`A_j ⊗_R R[0]`, the one-term complex `A_j ⊗_R R`, and the target complex `C'` is arbitrary. -/
theorem exists_le_Q_map_ext_single_eq
    (u w : (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R R) ⟶ C')
    (h : DerivedCategory.Q.map ((ext S.φlim).map u) =
      DerivedCategory.Q.map ((ext S.φlim).map w)) :
    ∃ j : J, DerivedCategory.Q.map ((ext (S.φ j)).map u) =
      DerivedCategory.Q.map ((ext (S.φ j)).map w) :=
  have := isKProjective_ext_single S.φlim
  S.exists_le_Q_map_ext_eq hcol (finite_support_single_obj 0 (ModuleCat.of R R))
    (finitePresentation_single_X R) u w h

include hcol in
/-- **Every map over the colimit comes from a stage, in the derived category, at the first
argument `R[0]`**: a morphism `A ⊗_R R[0] ⟶ A ⊗_R C'` of `D(A)` is `A ⊗_{A_j} t` for a chain map
`t : A_j ⊗_R R[0] ⟶ A_j ⊗_R C'` at some stage `j`, for an arbitrary complex `C'`. -/
theorem exists_Q_map_ext_single_eq
    (v : DerivedCategory.Q.obj ((ext S.φlim).obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of R R))) ⟶
      DerivedCategory.Q.obj ((ext S.φlim).obj C')) :
    ∃ (j : J) (t : (ext (S.φ j)).obj ((HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R)) ⟶ (ext (S.φ j)).obj C'),
      DerivedCategory.Q.map ((extCompIsoOf (S.φ j) (S.γ j) S.φlim (S.φ_γ j)
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (ModuleCat.of R R))).inv ≫
        (ext (S.γ j)).map t ≫
          (extCompIsoOf (S.φ j) (S.γ j) S.φlim (S.φ_γ j) C').hom) = v :=
  have := isKProjective_ext_single S.φlim
  S.exists_Q_map_ext_eq hcol (finite_support_single_obj 0 (ModuleCat.of R R))
    (finitePresentation_single_X R) v

end RingSystem

end Stacks.LimitHomDescent.Affine

end

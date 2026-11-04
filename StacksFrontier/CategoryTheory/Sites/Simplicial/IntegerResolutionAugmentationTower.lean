module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorBarStructure

/-!
# The augmentation of the integral resolution against the bottom of its Postnikov tower

Let `S` be a simplicial-site situation (Stacks 09WE) and let
`L = (… → g_{1!}ℤ → g_{0!}ℤ)` be the integral resolution of Stacks 09WI, read as a cochain
complex supported in degrees `≤ 0`. Stacks 0D9I attaches to `L` the tower of its brutal
truncations, and reads `L` both as the derived colimit of that tower — with the inclusions
`σ^{≥-n}L ⟶ L` as coprojections — and through the Postnikov system whose bottom object `Y₀` is
the brutal truncation `σ^{≥0}L` shifted by zero, with projection
`StacksDraft.BrutalPostnikov.totProj` onto its bottom term `X₀ = g_{0!}ℤ`.

At the bottom of the tower those two readings of the structural map `X₀ ⟶ ℤ` have to be
identified, and that is what this file proves: the degree-zero coprojection followed by the
identification `L ≅ ℤ` of `integerResolutionDerivedIso` is the inverse of
`StacksDraft.BrutalPostnikov.totAtTowerIso`, followed by `totProj`, the identification of `X₀`
with `g_{0!}ℤ` and the augmentation `g_{0!}ℤ ⟶ ℤ`. This is the identity that Stacks 0D9K needs in
order to read its augmentation identity
(`CategoryTheory.SimplicialSiteSituation.integerProjection_comp_derivedTensorAugmentation`)
against the map the tower argument of
`StacksDraft.BrutalPostnikov.exists_hom_of_termDiff_comp_eq_zero` delivers its conclusion
against; tensoring the identity below with `K` turns one into the other.

Two things have to be crossed. First, both sides are images under the localization functor of
maps of complexes: the only non-localized factor is `totAtTowerIso`, and it is the image of the
identification `σ^{≥0}L⟦0⟧ ≅ σ^{≥0}L` of complexes precisely because the localization functor
commutes with the shift and its commutation isomorphism in degree zero is the one built from
`shiftFunctorZero'` on both sides. Second, the two sides reach the augmentation by different
routes: `CategoryTheory.SimplicialSiteSituation.integerAugmentation` through
`CategoryTheory.SimplicialSiteSituation.resolutionAugmentation'`, and
`CategoryTheory.SimplicialSiteSituation.integerResolutionAugmentation` through
`CategoryTheory.SimplicialSiteSituation.integerChainAugmentation` and
`HomologicalComplex.extendMap`; `integerResolutionAugmentation_f_zero` relates them, by
computing in degree zero the extension along `ComplexShape.embeddingUpIntLE 0` of a map of chain
complexes into a complex concentrated in degree zero.

## Main results

* `StacksDraft.BrutalPostnikov.totAtTowerIso_inv_eq`: at the bottom of the tower the
  identification `Y₀ ≅ σ^{≥0}L` is the image under the localization functor of the
  identification `σ^{≥0}L⟦0⟧ ≅ σ^{≥0}L` of complexes.
* `StacksDraft.BrutalPostnikov.ιStupidTrunc_comp_eq_totProjHom_comp`: a map of complexes out of
  `L` into a complex concentrated in degree zero, restricted along the inclusion `σ^{≥0}L ⟶ L`,
  is the projection of the truncation onto its bottom term followed by that map in degree zero.
* `ChainComplex.extendMap_toSingle₀Equiv_symm_f`: the extension along an embedding of complex
  shapes of a map into a complex concentrated in degree zero is, in the image of degree zero, the
  map it was built from.
* `CategoryTheory.SimplicialSiteSituation.integerResolutionAugmentation_f_zero`: in degree zero
  the augmentation of the integral resolution is the identification of the degree-zero term with
  `g_{0!}ℤ` followed by `integerAugmentation`.
* `CategoryTheory.SimplicialSiteSituation.ιStupidTrunc_comp_integerResolutionDerivedIso`:
  **the degree-zero coprojection of the derived colimit, followed by the identification of the
  integral resolution with `ℤ`, is the bottom of the Postnikov tower followed by the
  augmentation.**

## References

* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex
open StacksDraft.StupidTruncation
open scoped Simplicial

namespace StacksDraft.BrutalPostnikov

universe w v u

/-! ### The identification `Y₀ ≅ σ^{≥0}L` comes from the complexes -/

section Zero

/-- For a functor commuting with the shift, the commutation isomorphism in a degree that is
zero, followed by the identification of the shift by that degree with the identity, is the image
of that identification. This is the axiom `Functor.commShiftIso_zero` read at a degree that is
zero rather than at the literal `0`. -/
private theorem map_shiftFunctorZero'_hom {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] (a : ℤ) (ha : a = 0) (X : C) :
    (F.commShiftIso a).hom.app X ≫ (shiftFunctorZero' D a ha).hom.app (F.obj X) =
      F.map ((shiftFunctorZero' C a ha).hom.app X) := by
  rw [F.commShiftIso_zero' ℤ a ha]
  simp [CategoryTheory.Functor.CommShift.isoZero'_hom_app]

/-- The inverse form of `map_shiftFunctorZero'_hom`. -/
private theorem map_shiftFunctorZero'_inv {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] (a : ℤ) (ha : a = 0) (X : C) :
    (shiftFunctorZero' D a ha).inv.app (F.obj X) ≫ (F.commShiftIso a).inv.app X =
      F.map ((shiftFunctorZero' C a ha).inv.app X) := by
  rw [F.commShiftIso_zero' ℤ a ha]
  simp [CategoryTheory.Functor.CommShift.isoZero'_inv_app]

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (L : CochainComplex A ℤ)

/-- **At the bottom of the tower the identification `Y₀ ≅ σ^{≥0}L` is the image under the
localization functor of the identification `σ^{≥0}L⟦0⟧ ≅ σ^{≥0}L` of complexes.** Both are built
from the shift by `a + 1 = 0`; the comparison is the commutation of the localization functor with
that shift, which in degree zero is the identification of the shift with the identity on
complexes and on the derived category. -/
theorem totAtTowerIso_hom_eq (a : ℤ) (ha : a + 1 = 0) :
    (totAtTowerIso L a ha).hom =
      DerivedCategory.Q.map ((shiftFunctorZero' (CochainComplex A ℤ) (a + 1) ha).hom.app
        (L.stupidTrunc (embeddingUpIntGE (a + 1)))) :=
  map_shiftFunctorZero'_hom DerivedCategory.Q (a + 1) ha _

/-- `totAtTowerIso_hom_eq` for the inverse. -/
theorem totAtTowerIso_inv_eq (a : ℤ) (ha : a + 1 = 0) :
    (totAtTowerIso L a ha).inv =
      DerivedCategory.Q.map ((shiftFunctorZero' (CochainComplex A ℤ) (a + 1) ha).inv.app
        (L.stupidTrunc (embeddingUpIntGE (a + 1)))) :=
  map_shiftFunctorZero'_inv DerivedCategory.Q (a + 1) ha _

/-- `totAtTowerIso_inv_eq` with both the shift and the truncation spelled at the literal degree
zero, which is the spelling in which `totProj` names the projection of the bottom truncation. -/
private theorem totAtTowerIso_inv_eq_zero :
    (totAtTowerIso L (-1) (by ring)).inv =
      DerivedCategory.Q.map ((shiftFunctorZero' (CochainComplex A ℤ) (0 : ℤ) rfl).inv.app
        (L.stupidTrunc (embeddingUpIntGE (0 : ℤ)))) :=
  totAtTowerIso_inv_eq L (-1) (by ring)

/-! ### A map into a complex concentrated in degree zero, restricted to the bottom truncation -/

omit [HasDerivedCategory.{w} A] in
/-- **A map of complexes out of `L` into a complex concentrated in degree zero, restricted along
the inclusion `σ^{≥0}L ⟶ L`, is the projection of the truncation onto its bottom term followed by
the map in degree zero.** Both sides are maps into a complex concentrated in degree zero, so it
is enough to compare them there, and there the inclusion and the projection are both the
identification of the bottom term of the truncation with `L⁰`. -/
theorem ιStupidTrunc_comp_eq_totProjHom_comp (Z : A)
    (α : L ⟶ (CochainComplex.singleFunctor A 0).obj Z) :
    ιStupidTrunc L (embeddingUpIntGE (0 : ℤ)) ≫ α =
      (shiftFunctorZero' (CochainComplex A ℤ) (0 : ℤ) rfl).inv.app
          (L.stupidTrunc (embeddingUpIntGE (0 : ℤ))) ≫
        totProjHom L 0 ≫
          (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map
            (α.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom) := by
  apply to_single_hom_ext
  simp only [HomologicalComplex.comp_f, ιStupidTruncGE_f L 0 0 le_rfl, totProjHom,
    HomologicalComplex.single_map_f_self,
    CochainComplex.shiftFunctor_map_f', Category.assoc]
  simp [CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f,
    singleShiftIso, CochainComplex.singleFunctors, stupidTruncGEπ_f]

/-- **The inclusion of the bottom brutal truncation, followed by a map of the derived category
out of `L` that comes from a map of complexes into a complex concentrated in degree zero, is the
bottom of the Postnikov tower followed by that map in degree zero.** The three hypotheses name
the three pieces the consumer has: `γ` is the map of the derived category, `ε` the map of single
complexes it is read through in degree zero. -/
theorem Q_ιStupidTrunc_comp_eq (Z : A) (α : L ⟶ (CochainComplex.singleFunctor A 0).obj Z)
    (γ : DerivedCategory.Q.obj L ⟶ (DerivedCategory.singleFunctor A 0).obj Z)
    (hγ : γ = DerivedCategory.Q.map α)
    (ε : (DerivedCategory.singleFunctor A 0).obj (L.X 0) ⟶
      (DerivedCategory.singleFunctor A 0).obj Z)
    (hε : ε = (DerivedCategory.singleFunctor A 0).map
      (α.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom)) :
    DerivedCategory.Q.map (ιStupidTrunc L (embeddingUpIntGE (0 : ℤ))) ≫ γ =
      (totAtTowerIso L (-1) (by ring)).inv ≫ totProjAt L 0 ≫ ε := by
  subst hγ
  subst hε
  calc DerivedCategory.Q.map (ιStupidTrunc L (embeddingUpIntGE (0 : ℤ))) ≫
        DerivedCategory.Q.map α
      = DerivedCategory.Q.map (ιStupidTrunc L (embeddingUpIntGE (0 : ℤ)) ≫ α) :=
        (DerivedCategory.Q.map_comp _ _).symm
    _ = DerivedCategory.Q.map
          ((shiftFunctorZero' (CochainComplex A ℤ) (0 : ℤ) rfl).inv.app
              (L.stupidTrunc (embeddingUpIntGE (0 : ℤ))) ≫
            totProjHom L 0 ≫
              (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map
                (α.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom)) :=
        congrArg _ (ιStupidTrunc_comp_eq_totProjHom_comp L Z α)
    _ = (totAtTowerIso L (-1) (by ring)).inv ≫ totProjAt L 0 ≫
          (DerivedCategory.singleFunctor A 0).map
            (α.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom) := by
        rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp,
          totAtTowerIso_inv_eq_zero L]
        rfl

end Zero

end StacksDraft.BrutalPostnikov

namespace CategoryTheory.SimplicialSiteSituation

open StacksDraft.BrutalPostnikov

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The two routes to the augmentation of the integral resolution -/

/-- Two spellings of the hypothesis locating a degree in the image of an embedding of complex
shapes give the same identification of terms, and the identification cancels with its inverse.
Stated with two hypotheses, and in the associated form, so that it applies by rewriting where
the proof irrelevance that makes the two identifications equal is not available to the
matcher. -/
private theorem extendXIso_inv_comp_hom_assoc {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    [Limits.HasZeroObject C] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c) (e : c.Embedding c') {i : ι} {i' : ι'}
    (h₁ h₂ : e.f i = i') {W : C} (g : K.X i ⟶ W) :
    (K.extendXIso e h₁).inv ≫ (K.extendXIso e h₂).hom ≫ g = g :=
  Iso.inv_hom_id_assoc _ _

/-- The extension along an embedding of complex shapes of a map of chain complexes into a complex
concentrated in degree zero, read in the degree the embedding sends `0` to and through the
identification of the target with its value there, is the map it was built from. -/
theorem _root_.ChainComplex.extendMap_toSingle₀Equiv_symm_f {V : Type*} [Category* V]
    [Limits.HasZeroMorphisms V] [Limits.HasZeroObject V]
    {K : ChainComplex V ℕ} {Z : V} (β : K.X 0 ⟶ Z) (hβ : K.d 1 0 ≫ β = 0)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) {i' : ℤ} (h : e.f 0 = i') :
    (HomologicalComplex.extendMap ((ChainComplex.toSingle₀Equiv K Z).symm ⟨β, hβ⟩) e ≫
          (HomologicalComplex.extendSingleIso e Z 0 i' h).hom).f i' ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i' Z).hom =
      (K.extendXIso e h).hom ≫ β := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ e h,
    HomologicalComplex.extendSingleIso_hom_f]
  simp only [ChainComplex.single₀, Category.assoc]
  rw [extendXIso_inv_comp_hom_assoc]
  simp

/-- An isomorphism composed with a second one and then with the inverse of the second. -/
private theorem trans_hom_comp_inv_comp {C : Type*} [Category* C] {X Y W V : C}
    (a : X ≅ Y) (b : Y ≅ W) (g : Y ⟶ V) : (a ≪≫ b).hom ≫ b.inv ≫ g = a.hom ≫ g := by
  simp

variable (S : SimplicialSiteSituation.{u})

/-- **In degree zero the augmentation of the integral resolution of Stacks 09WI is the
identification of the degree-zero term of the resolution with `g_{0!}ℤ` followed by the
augmentation `g_{0!}ℤ ⟶ ℤ`.** The two sides reach that augmentation by different routes —
`integerAugmentation` through `resolutionAugmentation'`, and `integerResolutionAugmentation`
through `integerChainAugmentation` and `HomologicalComplex.extendMap` — and this is the
comparison of the two. -/
theorem integerResolutionAugmentation_f_zero :
    (integerResolutionAugmentation S).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (totalIntegerSheaf S)).hom =
      (integerResolutionComplexXIso S 0).hom ≫ integerAugmentation S :=
  (ChainComplex.extendMap_toSingle₀Equiv_symm_f (simplicialIntegerResolution S).augmentation
        (simplicialIntegerResolution S).augmentation_comp (ComplexShape.embeddingUpIntLE 0)
        (show (ComplexShape.embeddingUpIntLE 0).f 0 = (0 : ℤ) by simp)).trans
    (trans_hom_comp_inv_comp _ _ _).symm

/-! ### The augmentation identity at the bottom of the Postnikov tower -/

/-- **The degree-zero coprojection of the derived colimit of the brutal truncations of the
integral resolution, followed by the identification of that resolution with the constant sheaf
`ℤ`, is the bottom of the Postnikov system of Stacks 0D9I followed by the augmentation
`g_{0!}ℤ ⟶ ℤ`.** On the left is the inclusion `σ^{≥0}L ⟶ L` of the bottom brutal truncation,
which is the coprojection recorded by
`isHomotopyColimitWith_integerResolutionSystem`, followed by
`integerResolutionDerivedIso`; on the right is the identification of `Y₀` with that truncation,
the projection `Y₀ ⟶ X₀` of the Postnikov system, the identification of `X₀` with `g_{0!}ℤ`, and
the augmentation. Tensoring with an object `K` of the derived category of the total site turns
this into the identification, in the form Stacks 0D9K consumes it, of the structural map
`X₀ ⟶ K` of the Postnikov system with the derived tensor product of `K` with the augmentation. -/
theorem ιStupidTrunc_comp_integerResolutionDerivedIso :
    DerivedCategory.Q.map (ιStupidTrunc (integerResolutionComplex S)
          (embeddingUpIntGE (-((0 : ℕ) : ℤ)))) ≫ (integerResolutionDerivedIso S).hom =
      (totAtTowerIso (integerResolutionComplex S) (-((1 : ℕ) : ℤ)) (by simp)).inv ≫
        totProj (integerResolutionComplex S) 0 ≫
          (integerResolutionTermIso S 0).hom ≫
            (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerAugmentation S) :=
  Q_ιStupidTrunc_comp_eq (integerResolutionComplex S) (totalIntegerSheaf S)
    (integerResolutionAugmentation S) _ (Category.comp_id _) _
    (((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map_comp _ _).symm.trans
      (congrArg (fun f => (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map f)
        (integerResolutionAugmentation_f_zero S).symm))

end CategoryTheory.SimplicialSiteSituation

end

module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothetyEvaluation
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothety

/-!
# Invertibility over a slice through the evaluation morphism

For a ringed site `X` and an object `U`, we compare the restriction to `C/U` of the evaluation
morphism `R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` with the evaluation morphism formed over `C/U`, and deduce a
criterion for a morphism into `R𝓗om_O(K, K)` to restrict to an isomorphism over `U`.

## Main results

* `derivedSheafHomRestrictionDatum_eq_map_comp_counit`: the restricted evaluation morphism
  factors through the mate of the restriction comparison and the evaluation morphism over `C/U`.
* `isIso_restrictD_map_of_isIso_evaluation`: a morphism `a : E ⟶ R𝓗om_O(K, K)` with invertible
  evaluation restricts to an isomorphism over `U` when the derived endomorphisms of `K|_U` are
  isomorphic to an object with commuting endomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction extension)

universe u

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

section Slice

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.over U).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over U).O)
      (ComplexShape.up ℤ)]

/-- The slice tensor comparison followed by the restriction of the evaluation morphism
`R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` is the mate tensored with `L|_U` followed by the evaluation morphism
formed over `C/U`. -/
theorem derivedSheafHomRestrictionDatum_eq_map_comp_counit
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomRestrictionDatum X U L M =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map
          (derivedSheafHomRestrictionTranspose X U L M)).app ((restrictD X U).obj L) ≫
        RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L)
          ((restrictD X U).obj M) := by
  have ht := derivedSheafHomRestrictionDatum_eq_sliceCurryEquiv_transpose X U L M
  rwa [sliceCurryEquiv_eq, RingedSite.derivedCurryHomEquiv_apply] at ht

variable [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar U).unit]

/-- Let `a : E ⟶ R𝓗om_O(K, K)` be a morphism such that `a ⊗ K` followed by the evaluation morphism
is invertible, let `E'` be an object of `D(O|_U)` whose endomorphisms commute (for instance the
unit of a monoidal structure) with `E|_U ≅ E'`, and suppose `R𝓗om_{O|_U}(K|_U, K|_U) ≅ E'`. Then
`a|_U` is an isomorphism. -/
theorem isIso_restrictD_map_of_isIso_evaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : E ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op K)).obj K)
    (ha : IsIso (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app K ≫
      RingedSite.derivedSheafHomCounit X K K))
    {E' : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))}
    (hE' : ∀ f g : E' ⟶ E', f ≫ g = g ≫ f) (φ : (restrictD X U).obj E ≅ E')
    (ψ : ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
        (op ((restrictD X U).obj K))).obj ((restrictD X U).obj K) ≅ E') :
    IsIso ((restrictD X U).map a) := by
  have := isIso_derivedSheafHomRestrictionTranspose X U K K
  set r := restrictD X U
  set τ := derivedSheafHomRestrictionTranspose X U K K
  set T := (Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).flip.obj (r.obj K)
  set c := RingedSite.derivedSheafHomCounit (X.over U) (r.obj K) (r.obj K)
  have ht : T.map τ ≫ c = (sliceTensorRestrictionObjIso X U
      (((RingedSite.derivedSheafHomBifunctor X).obj (op K)).obj K) K).inv ≫
        r.map (RingedSite.derivedSheafHomCounit X K K) :=
    (derivedSheafHomRestrictionDatum_eq_map_comp_counit X U K K).symm
  have hT : T.map (r.map a) = (sliceTensorRestrictionObjIso X U E K).inv ≫
      r.map (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app K) ≫
        (sliceTensorRestrictionObjIso X U _ K).hom := by
    rw [Iso.eq_inv_comp]
    exact (sliceTensorRestrictionObjIso_naturality X U a K).symm
  have hiso : IsIso (T.map (φ.inv ≫ r.map a ≫ τ) ≫ c) := by
    have e : T.map (φ.inv ≫ r.map a ≫ τ) ≫ c = T.map φ.inv ≫
        (sliceTensorRestrictionObjIso X U E K).inv ≫
          r.map (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app K ≫
            RingedSite.derivedSheafHomCounit X K K) := by
      rw [T.map_comp, T.map_comp, Category.assoc, Category.assoc, ht, hT, r.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [e]
    infer_instance
  have key := CategoryTheory.isIso_of_isIso_map_comp_of_iso T hE' c
    (bijective_derivedSheafHomCounit (X.over U) E' _ _) ψ _ hiso
  have e₄ : r.map a = φ.hom ≫ (φ.inv ≫ r.map a ≫ τ) ≫ inv τ := by simp
  rw [e₄]
  infer_instance

end Slice

/-! ### Invertibility is local -/

section Glueing

variable (X : RingedSite.{u, u, u}) [HasBinaryProducts X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

end Glueing

end Stacks.Cohomology.SliceDerivedSheafHom

end

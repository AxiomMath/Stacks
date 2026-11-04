module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite

/-!
# Reconstructing the sheaf of meromorphic functions from its affine charts

A sheaf of `𝒪_X`-algebras on the small étale site of an algebraic space whose sections over
every affine étale chart `U` are a localization of `𝒪_X(U)` at its nonzerodivisors is
isomorphic, as an `𝒪_X`-algebra, to the sheaf of meromorphic functions `𝒦_X`.

## Main results

* `CategoryTheory.Under.localizationPresheafIso`: two algebras over one presheaf of rings which
  are objectwise localizations at the same submonoid are isomorphic as algebras.
* `CategoryTheory.Under.isoOfCoverDense`: an algebra comparison over a cover-dense subcategory
  extends, with its structural map, to the whole site.
* `AlgebraicGeometry.Space.iso_meromorphic_of_isLocalization_affineCharts`: the reconstruction.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u v w

namespace CategoryTheory.Under

/-- Two algebras over the same presheaf of rings which are objectwise localizations at the same
submonoid are isomorphic as algebras. -/
public noncomputable def localizationPresheafIso
    {C : Type v} [Category.{w} C] {R : C ⥤ CommRingCat.{u}}
    (A D : Under R) (M : ∀ U, Submonoid (R.obj U))
    (hA : ∀ U, letI := (A.hom.app U).hom.toAlgebra;
      IsLocalization (M U) (A.right.obj U))
    (hD : ∀ U, letI := (D.hom.app U).hom.toAlgebra;
      IsLocalization (M U) (D.right.obj U)) : A ≅ D := by
  letI (U : C) : Algebra (R.obj U) (A.right.obj U) := (A.hom.app U).hom.toAlgebra
  letI (U : C) : Algebra (R.obj U) (D.right.obj U) := (D.hom.app U).hom.toAlgebra
  letI (U : C) : IsLocalization (M U) (A.right.obj U) := hA U
  letI (U : C) : IsLocalization (M U) (D.right.obj U) := hD U
  let e (U : C) := IsLocalization.algEquiv (M U) (A.right.obj U) (D.right.obj U)
  let i : A.right ≅ D.right := NatIso.ofComponents
    (fun U => (e U).toRingEquiv.toCommRingCatIso) (by
      intro U V f
      apply CommRingCat.hom_ext
      apply IsLocalization.ringHom_ext (M U)
      ext r
      change e V (A.right.map f (A.hom.app U r)) =
        D.right.map f (e U (A.hom.app U r))
      rw [← CommRingCat.comp_apply, ← A.hom.naturality]
      change e V (algebraMap (R.obj V) (A.right.obj V) (R.map f r)) = _
      rw [(e V).commutes]
      change _ = D.right.map f (e U (algebraMap (R.obj U) (A.right.obj U) r))
      rw [(e U).commutes]
      exact ConcreteCategory.congr_hom (D.hom.naturality f) r)
  refine Under.isoMk i ?_
  ext U r
  exact (e U).commutes r

/-- An algebra comparison over a cover-dense subcategory extends, with its structural map, to an
algebra comparison over the whole site. -/
public noncomputable def isoOfCoverDense
    {C : Type v} [Category.{w} C] {D : Type*} [Category* D]
    {J : GrothendieckTopology D} (G : C ⥤ D)
    [G.IsCoverDense J] [G.IsLocallyFull J]
    {R : Dᵒᵖ ⥤ CommRingCat.{u}} (A E : Under R)
    (hA : Presheaf.IsSheaf J A.right) (hE : Presheaf.IsSheaf J E.right)
    (e : Under.mk (Functor.whiskerLeft G.op A.hom) ≅
      Under.mk (Functor.whiskerLeft G.op E.hom)) : A ≅ E := by
  let i : G.op ⋙ A.right ≅ G.op ⋙ E.right := (Under.forget _).mapIso e
  let j := Functor.IsCoverDense.presheafIso
    (ℱ := ⟨A.right, hA⟩) (ℱ' := ⟨E.right, hE⟩) i
  refine Under.isoMk j ?_
  apply (Functor.IsCoverDense.restrictHomEquivHom (G := G)
    (ℱ := R) (ℱ' := ⟨E.right, hE⟩)).symm.injective
  change Functor.whiskerLeft G.op (A.hom ≫ j.hom) = Functor.whiskerLeft G.op E.hom
  rw [Functor.whiskerLeft_comp]
  change Functor.whiskerLeft G.op A.hom ≫
      Functor.whiskerLeft G.op
        (Functor.IsCoverDense.sheafHom (G := G) (ℱ' := ⟨E.right, hE⟩) i.hom) = _
  rw [Functor.IsCoverDense.sheafHom_restrict_eq]
  exact Under.w e.hom

end CategoryTheory.Under

namespace AlgebraicGeometry.Space

open CategoryTheory.Under in
/-- **Reconstruction of `𝒦_X` from its affine-chart sections.**  Any sheaf of `𝒪_X`-algebras
whose sections over every affine étale chart `U` are a localization of `𝒪_X(U)` at the
nonzerodivisors is isomorphic, as an algebra over `𝒪_X`, to the sheaf of meromorphic
functions. -/
public theorem iso_meromorphic_of_isLocalization_affineCharts
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (D : Under (structurePresheaf B S hS X.1))
    (hDsheaf : Presheaf.IsSheaf (SmallEtale.topology B S hS X.1) D.right)
    (hDloc : ∀ (U : SmallEtale B S hS X.1), IsAffine (smallEtaleScheme B S hS X.1 U) →
      letI := (D.hom.app (op U)).hom.toAlgebra
      IsLocalization ((structurePresheaf B S hS X.1).obj (op U))⁰ (D.right.obj (op U))) :
    Nonempty (Under.mk (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom ≅ D) := by
  have : (AffineEtale.inclusion B S hS X.1).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  exact ⟨isoOfCoverDense (AffineEtale.inclusion B S hS X.1) _ _
    (meromorphicFunctionSheaf B S hS X.1 X.2).property hDsheaf
    (localizationPresheafIso _ _
      (fun U => ((structurePresheaf B S hS X.1).obj (op U.unop.obj))⁰)
      (fun U => isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin U.unop.obj
        U.unop.property)
      fun U => hDloc U.unop.obj U.unop.property)⟩

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# The base change comparison through injective resolutions of a sheaf

If cohomology commutes with base change for `f` at a coefficient universe `w`, a torsion abelian
sheaf `G` on `X_étale` has a bounded below injective resolution `G[0] ⟶ I` and `(g')⁻¹ I` one
`q : (g')⁻¹ I ⟶ L` such that the degreewise comparison `g⁻¹ f_* I ⟶ f'_* (g')⁻¹ I ⟶ f'_* L` is a
quasi-isomorphism (`Stacks.EtaleCohomology.isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso`).

## Implementation notes

The statement is universe polymorphic and the module has few imports: the kernel checks the
instantiation of `Stacks.EtaleCohomology.isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso`
within its budget only at a universe variable and in a context with few instances, and a consumer
instantiates this statement at a given universe rather than elaborating it there.

## Main results

* `Stacks.EtaleCohomology.exists_resolution_quasiIso_etaleAbelianBaseChange`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

/-- **The degreewise base change comparison through injective resolutions of a sheaf.** If
cohomology commutes with base change for `f` at the coefficient universe `w`, a torsion abelian
sheaf `G` on `X_étale` has a bounded below injective resolution `G[0] ⟶ I`, and `(g')⁻¹ I` one
`q : (g')⁻¹ I ⟶ L`, such that `g⁻¹ f_* I ⟶ f'_* (g')⁻¹ I ⟶ f'_* L` is a quasi-isomorphism. The
statement is universe polymorphic so that it is instantiated, not elaborated, at a given
universe. -/
theorem exists_resolution_quasiIso_etaleAbelianBaseChange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (hpbc : CohomologyCommutesWithBaseChange.{u, w} f)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) w})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) :
    ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}) ℤ)
      (i : (CochainComplex.singleFunctor _ 0).obj G ⟶ I) (_ : QuasiIso i)
      (_ : ∀ n, Injective (I.X n)) (_ : I.IsStrictlyGE 0)
      (L : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}) ℤ)
      (q : ((etaleAbelianInverseImage.{u, w} g').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I ⟶ L)
      (_ : QuasiIso q) (_ : ∀ n, Injective (L.X n)) (_ : L.IsStrictlyGE 0),
      QuasiIso ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, w} f g g' f' sq.w)
          (ComplexShape.up ℤ)).app I ≫
        ((etaleAbelianDirectImage.{u, w} f').mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
  obtain ⟨I, i, hi, hIinj, hI⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      ((CochainComplex.singleFunctor _ 0).obj G) 0
  have hgI : CochainComplex.IsStrictlyGE
      (((etaleAbelianInverseImage.{u, w} g').mapHomologicalComplex _).obj I) 0 :=
    (CochainComplex.isStrictlyGE_iff _ 0).2 fun m hm =>
      (etaleAbelianInverseImage.{u, w} g').map_isZero
        ((CochainComplex.isStrictlyGE_iff I 0).1 hI m hm)
  obtain ⟨L, q, hq, hLinj, hL⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (((etaleAbelianInverseImage.{u, w} g').mapHomologicalComplex _).obj I) 0
  have h₀ : IsIso ((etaleAbelianDerivedBaseChange.{u, w} f g g' f' sq.w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
    have hG₀ := hpbc g g' f' sq G hG
    have : IsIso (DerivedCategory.Q.map i) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ i).2 hi
    exact (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G ≪≫
      asIso (DerivedCategory.Q.map i) ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm)).1 hG₀
  have hφ := isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso.{u, w} f g g' f' sq.w I ⟨0, hI⟩
    (fun n => Functor.rightAcyclic_of_injective _ _) L ⟨0, hL⟩
    (fun n => Functor.rightAcyclic_of_injective _ _) q h₀
  exact ⟨I, i, hi, hIinj, hI, L, q, hq, hLinj, hL,
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hφ⟩


end Stacks.EtaleCohomology

end

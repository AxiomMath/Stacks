module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperPushforwardTwistTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper base change for sheaves of modules on resolutions

Let `f` be proper, `X' = Y' ×_Y X` with projections `f'` and `g'`, `Λ` a ring and `M` a bounded
below complex of injective sheaves of `Λ`-modules on `X_étale` with torsion cohomology sheaves.
For every quasi-isomorphism `ψ : (g')^{-1} M ⟶ T` onto a bounded below complex of injectives, the
morphism of complexes `g^{-1} f_* M ⟶ f'_* (g')^{-1} M ⟶ f'_* T` is a quasi-isomorphism: this is
the proper base change theorem [Stacks, Tag 0DDE] on resolutions, in the form
`CategoryTheory.Functor.BaseChangeQuasiIsoAt` consumed by the trace formula.

The proof is the one of `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper`:
forgetting the module structures carries the morphism to the abelian comparison followed by
`f'_*` of a quasi-isomorphism, which is a quasi-isomorphism by the abelian proper base change
theorem. The same precautions about spellings apply (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange`).

## Main results

* `Stacks.EtaleCohomology.quasiIso_etaleModuleBaseChange_comp_of_isProper`.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.SheafOfModules.coefficientSheafification
  Stacks.EtaleCohomology.etaleAbelianDirectImage_additive

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type w) [Ring Λ]

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- `Stacks.Cohomology.DerivedBaseChangeResolution.isIso_Q_map_natTrans_comp_of_forget` for the
étale functors, with the base change maps `αm, αa` and the comparisons `σ, τ, τ', σ'` of the
forgetful functors with direct and inverse image as variables: if the abelian comparison through
every resolution `ψ : (g')^{-1} I ⟶ T` is a quasi-isomorphism and the forgetful functors carry
`αm` to `αa` (`hP`), then `αm` is a quasi-isomorphism on resolutions at `I`. -/
theorem baseChangeQuasiIsoAt_etaleModuleBaseChange_of_forget
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (αm : etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleInverseImage.{u, w} Λ g ⟶
      etaleModuleInverseImage.{u, w} Λ g' ⋙ etaleModuleDirectImage.{u, w} Λ f')
    (αa : etaleAbelianDirectImage.{u, w} f ⋙ etaleAbelianInverseImage.{u, w} g ⟶
      etaleAbelianInverseImage.{u, w} g' ⋙ etaleAbelianDirectImage.{u, w} f')
    (σ : etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianDirectImage.{u, w} f ≅
      etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleForgetAb.{u, w} Λ Y)
    (τ : etaleModuleForgetAb.{u, w} Λ Y ⋙ etaleAbelianInverseImage.{u, w} g ≅
      etaleModuleInverseImage.{u, w} Λ g ⋙ etaleModuleForgetAb.{u, w} Λ Y')
    (τ' : etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianInverseImage.{u, w} g' ≅
      etaleModuleInverseImage.{u, w} Λ g' ⋙ etaleModuleForgetAb.{u, w} Λ X')
    (σ' : etaleModuleForgetAb.{u, w} Λ X' ⋙ etaleAbelianDirectImage.{u, w} f' ≅
      etaleModuleDirectImage.{u, w} Λ f' ⋙ etaleModuleForgetAb.{u, w} Λ Y')
    (hP : ∀ M : EtaleModules.{u, w} Λ X,
      (etaleAbelianInverseImage.{u, w} g).map (σ.hom.app M) ≫
          τ.hom.app ((etaleModuleDirectImage.{u, w} Λ f).obj M) ≫
            (etaleModuleForgetAb.{u, w} Λ Y').map (αm.app M) =
        αa.app ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
          (etaleAbelianDirectImage.{u, w} f').map (τ'.hom.app M) ≫
            σ'.hom.app ((etaleModuleInverseImage.{u, w} Λ g').obj M))
    (I : CochainComplex.Plus (EtaleModules.{u, w} Λ X))
    (hy : ∀ (L : CochainComplex.Plus (EtaleModules.{u, w} Λ X'))
      (i : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I ⟶ L), QuasiIso i.hom →
      (∀ n, Injective (L.obj.X n)) → QuasiIso
        ((NatTrans.mapHomologicalComplex αa (ComplexShape.up ℤ)).app
            (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              I.obj) ≫
          ((etaleAbelianDirectImage.{u, w} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatIso.mapHomologicalComplex τ' (ComplexShape.up ℤ)).hom.app I.obj ≫
              ((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map
                i.hom))) :
    Functor.BaseChangeQuasiIsoAt (etaleModuleDirectImage.{u, w} Λ f')
      (etaleModuleDirectImage.{u, w} Λ f) (etaleModuleInverseImage.{u, w} Λ g)
      (etaleModuleInverseImage.{u, w} Λ g') αm I :=
  fun T ψ hψ hT => (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    (Stacks.Cohomology.DerivedBaseChangeResolution.isIso_Q_map_natTrans_comp_of_forget
      αm αa σ τ τ' σ' hP I T ψ ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hy T ψ hψ hT)))

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- **Proper base change on resolutions, from the abelian one.** If the abelian base change map
is invertible at the underlying complex of abelian sheaves of a bounded below complex `M` of
injective sheaves of `Λ`-modules, then for every quasi-isomorphism `ψ : (g')^{-1} M ⟶ T` the
morphism `g^{-1} f_* M ⟶ f'_* (g')^{-1} M ⟶ f'_* T` is a quasi-isomorphism. -/
theorem quasiIso_etaleModuleBaseChange_comp_of_isIso_etaleAbelianDerivedBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (w : f' ≫ g = g' ≫ f)
    (M : CochainComplex.Plus (EtaleModules.{u, w} Λ X)) [∀ n, Injective (M.obj.X n)]
    (hbc : IsIso ((etaleAbelianDerivedBaseChange.{u, w} f g g' f' sq.w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M.obj))))) :
    Functor.BaseChangeQuasiIsoAt (etaleModuleDirectImage.{u, w} Λ f')
      (etaleModuleDirectImage.{u, w} Λ f) (etaleModuleInverseImage.{u, w} Λ g)
      (etaleModuleInverseImage.{u, w} Λ g') (etaleModuleBaseChange Λ f f' g g' w) M := by
  -- the square enters the cube identity as `sq.w.symm`; use the same proof term in the goal
  obtain rfl : w = sq.w.symm := rfl
  have hy := fun (T : CochainComplex.Plus (EtaleModules.{u, w} Λ X'))
      (ψ : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj M ⟶ T)
      (hψ : QuasiIso ψ.hom) (hT : ∀ n, Injective (T.obj.X n)) =>
    have := hT
    quasiIso_etaleAbelianBaseChange_comp_etaleModuleForget_of_isIso Λ f sq M T ψ hψ hbc
  have hP := etaleModuleForgetDirectImageIso_comp_map_etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w
  -- the base change maps and the comparisons enter `hy`, `hP` and the goal with differently
  -- spelled implicit arguments; as variables they are compared with themselves
  generalize etaleAbelianBaseChange.{u, w} f g g' f' sq.w = αa at hy hP
  generalize etaleModuleForgetInverseImageIso.{u, w} Λ g' = τ' at hy hP
  generalize etaleModuleForgetInverseImageIso.{u, w} Λ g = τ at hP
  generalize etaleModuleForgetDirectImageIso.{u, w} Λ f = σ at hP
  generalize etaleModuleForgetDirectImageIso.{u, w} Λ f' = σ' at hP
  generalize etaleModuleBaseChange Λ f f' g g' sq.w.symm = αm at hP ⊢
  exact baseChangeQuasiIsoAt_etaleModuleBaseChange_of_forget Λ f f' g g' αm αa σ τ τ' σ' hP M hy

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **Proper base change for sheaves of modules on resolutions** ([Stacks, Tag 0DDE], with
coefficients in a ring `Λ`). Let `f : X ⟶ Y` be proper, `X' = Y' ×_Y X` with projections `f'`
and `g'`, and `M` a bounded below complex of injective sheaves of `Λ`-modules on `X_étale` with
torsion cohomology sheaves. For every quasi-isomorphism `ψ : (g')^{-1} M ⟶ T` onto a bounded below
complex of injectives, `g^{-1} f_* M ⟶ f'_* (g')^{-1} M ⟶ f'_* T` is a quasi-isomorphism. -/
@[sga "4 XVII 4.3.2" "(ii)"]
theorem quasiIso_etaleModuleBaseChange_comp_of_isProper (Λ : Type) [Ring Λ]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (w : f' ≫ g = g' ≫ f)
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) [∀ n, Injective (M.obj.X n)]
    (hM : isTorsionPlus.{u, 0} Λ X
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj M))) :
    Functor.BaseChangeQuasiIsoAt (etaleModuleDirectImage.{u, 0} Λ f')
      (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleInverseImage.{u, 0} Λ g)
      (etaleModuleInverseImage.{u, 0} Λ g') (etaleModuleBaseChange Λ f f' g g' w) M := by
  obtain ⟨n₀, hn₀⟩ := M.property
  have hE : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        M.obj))).IsGE n₀ := by
    have : CochainComplex.IsStrictlyGE
        (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M.obj) n₀ :=
      (CochainComplex.isStrictlyGE_iff _ n₀).2 fun m hm =>
        (etaleModuleForgetAb.{u, 0} Λ X).map_isZero
          ((CochainComplex.isStrictlyGE_iff M.obj n₀).1 hn₀ m hm)
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso _).symm.app _) n₀
  have hT : ∀ m, IsTorsionEtaleModule Λ X (M.obj.homology m) := fun m =>
    IsTorsionEtaleModule.of_iso Λ X
      (show (DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ X) m).obj
          (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj M)) ≅ _ from
        (DerivedCategory.homologyFunctor _ m).mapIso
          ((DerivedCategory.quotientCompQhIso _).app M.obj) ≪≫
        (DerivedCategory.homologyFunctorFactors _ m).app M.obj) (hM m)
  have hT' : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M.obj))) := fun m =>
    Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
      (etaleModuleForgetHomologyIso.{u, 0} Λ M.obj m).symm (hT m)
  exact quasiIso_etaleModuleBaseChange_comp_of_isIso_etaleAbelianDerivedBaseChange.{u, 0} Λ f sq w
    M (isIso_etaleAbelianDerivedBaseChange_of_isProper f sq _ n₀ hE hT')

end Stacks.EtaleCohomology

end

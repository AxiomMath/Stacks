module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDerivedConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.ProjectionFormulaBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleTorsionBaseChange

/-!
# The projection formula for proper morphisms and a torsion coefficient ring: the reduction

Let `f : X ⟶ Y` be a proper morphism of schemes and `Λ` a torsion ring. [Stacks, Tag 0F0G] says
that the projection formula map `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` is an isomorphism for all
`E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`. Following the source, the map is checked after
pulling back to every geometric point `ȳ` of `Y`
(`isIso_iff_forall_isIso_etaleModuleDerivedInverseImage_map`); by the base change hexagon
(`isIso_map_etaleModuleProjectionFormulaMap_of_isIso`) and the base change theorem for unbounded
complexes ([Stacks, Tag 0F0C], for `Λ`-modules through `ℤ/nℤ`-modules,
`isIso_etaleAbelianDerivedBaseChange_forget_of_isProper`), it becomes the projection formula map
of the geometric fibre `X_ȳ ⟶ ȳ`, which is [Stacks, Tag 0F12] for `X_ȳ`, a quasi-compact and
quasi-separated scheme of finite cohomological dimension ([Stacks, Tag 095U]).

## Main results

* `Stacks.EtaleCohomology.isIso_iff_forall_isIso_etaleModuleDerivedInverseImage_map`: a morphism
  of `D(Y_étale, Λ)` is invertible as soon as its inverse image to every geometric point is.
* `Stacks.EtaleCohomology.exists_nat_cast_eq_zero_of_isTorsion`: a torsion ring is killed by some
  `n ≥ 1`.
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeMate_eq`: the mate base change map is the
  descended one.
* `Stacks.EtaleCohomology.isIso_etaleModuleProjectionFormulaMap_of_isProper`: the reduction,
  granted Tags 095T, 095U and 0F12.

## Implementation notes

The base change map of the hexagon is the mate `etaleModuleDerivedBaseChangeMate` of the two
derived adjunctions `f⁻¹ ⊣ Rf_*`. The base change theorem is known, through forgetting the
`Λ`-structure, for the map `etaleModuleDerivedBaseChangeGeneral` built by descent along the
derived-functor units (`isIso_etaleModuleDerivedBaseChange_app_of_isIso`). The two maps are equal
(`etaleModuleDerivedBaseChangeMate_eq`): the underived base change map is the mate of the
comparison of composite inverse images (`etaleModuleBaseChange_eq_mateEquiv`), the descent of a
mate along `Q` is the mate of the derived 2-square
(`Stacks.Homology.DerivedSquare.cochainDerivedSquare_mateEquiv`), and the derived 2-square of the
comparison of composite inverse images is the comparison of the composite derived inverse images
(`Stacks.Homology.DerivedSquare.derivedTwoSquare_eq_pullbackComparison`). Nothing in this file is
registered under Tag 0F0G: the reduction takes Tags 095T, 095U and 0F12 as hypotheses.

## References

* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **A torsion ring is killed by a positive integer**: the unit has finite additive order. -/
theorem exists_nat_cast_eq_zero_of_isTorsion {Λ : Type r} [Ring Λ] (hΛ : IsAddTorsion Λ) :
    ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0 := by
  have h1 : IsOfFinAddOrder (1 : Λ) := hΛ 1
  exact ⟨addOrderOf (1 : Λ), h1.addOrderOf_pos, by rw [← nsmul_one, addOrderOf_nsmul_eq_zero]⟩

variable (Λ : Type r) [CommRing Λ]

/-- **A morphism of `D(Y_étale, Λ)` is invertible as soon as its inverse image to every geometric
point of `Y` is**: forgetting the `Λ`-structure is conservative and commutes with inverse
images, and the geometric points detect isomorphisms of `D(Y_étale)`. -/
theorem isIso_iff_forall_isIso_etaleModuleDerivedInverseImage_map {Y : Scheme.{u}}
    {K L : DerivedCategory (EtaleModules.{u, r} Λ Y)} (φ : K ⟶ L) :
    IsIso φ ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      IsIso ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ y).map φ) := by
  refine ⟨fun _ _ _ _ _ ↦ inferInstance, fun h ↦ ?_⟩
  suffices IsIso ((etaleModuleForgetDerived.{u, r} Λ Y).map φ) from
    isIso_of_reflects_iso φ (etaleModuleForgetDerived.{u, r} Λ Y)
  rw [isIso_iff_forall_isIso_etaleAbelianDerivedInverseImage_map]
  intro Ω _ _ y
  have := h Ω y
  have e := (etaleModuleDerivedInverseImageForgetIso.{u, r} Λ y).hom.naturality φ
  have : IsIso ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ y ⋙
      etaleModuleForgetDerived.{u, r} Λ _).map φ) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have h' : (etaleModuleForgetDerived.{u, r} Λ Y ⋙ etaleAbelianDerivedInverseImage.{u, r} y).map φ =
      inv ((etaleModuleDerivedInverseImageForgetIso.{u, r} Λ y).hom.app K) ≫
        (etaleModuleDerivedInverseImageGeneral.{u, r} Λ y ⋙
          etaleModuleForgetDerived.{u, r} Λ _).map φ ≫
          (etaleModuleDerivedInverseImageForgetIso.{u, r} Λ y).hom.app L := by
    rw [e, IsIso.inv_hom_id_assoc]
  show IsIso ((etaleModuleForgetDerived.{u, r} Λ Y ⋙
    etaleAbelianDerivedInverseImage.{u, r} y).map φ)
  rw [h']
  infer_instance

section BaseChangeMate

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g)

/-- **The underived base change map of étale sheaves of `Λ`-modules is the mate, along the two
vertical adjunctions `f⁻¹ ⊣ f_*` and `f'⁻¹ ⊣ f'_*`, of the comparison
`g⁻¹ ⋙ f'⁻¹ ≅ P⁻¹ ≅ f⁻¹ ⋙ g'⁻¹` of the two composite inverse images.** It is built as the
inverse mate, along the horizontal adjunctions, of the comparison of the two composite direct
images, and the two agree by
`Stacks.CategoryTheory.mateEquiv_symm_comp_eq_mateEquiv_leftAdjointCompIso`. -/
theorem etaleModuleBaseChange_eq_mateEquiv :
    etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' (hP₁.symm.trans hP₂) =
      (mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ f) (etaleModuleInverseImageAdj.{u, r} Λ f')
        (TwoSquare.mk _ _ _ _ ((etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm.hom ≫
          (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm.inv))).natTrans := by
  subst hP₁
  exact congrArg TwoSquare.natTrans
    (Stacks.CategoryTheory.mateEquiv_symm_comp_eq_mateEquiv_leftAdjointCompIso
      (etaleModuleInverseImageAdj.{u, r} Λ f) (etaleModuleInverseImageAdj.{u, r} Λ f')
      (etaleModuleInverseImageAdj.{u, r} Λ g) (etaleModuleInverseImageAdj.{u, r} Λ g')
      (etaleModuleInverseImageAdj.{u, r} Λ (g' ≫ f))
      (smallEtalePushforwardComp' g' f (g' ≫ f) rfl (ModuleCat.{max (u + 1) r} Λ))
      (smallEtalePushforwardComp' f' g (g' ≫ f) hP₂ (ModuleCat.{max (u + 1) r} Λ)))

/-- **The mate base change map is the descended one**: the base change map
`etaleModuleDerivedBaseChangeMate`, the mate along the two derived adjunctions `f⁻¹ ⊣ Rf_*` of the
comparison of the two composite derived inverse images, is the base change map
`etaleModuleDerivedBaseChangeGeneral` obtained by descending the underived one along the
derived-functor unit of `Rf_*`. This is
`Stacks.Homology.DerivedSquare.cochainDerivedSquare_mateEquiv` for the
underived mate `etaleModuleBaseChange_eq_mateEquiv`, with the derived 2-square of the comparison
of composite inverse images read by
`Stacks.Homology.DerivedSquare.derivedTwoSquare_eq_pullbackComparison`. -/
theorem etaleModuleDerivedBaseChangeMate_eq (M : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    etaleModuleDerivedBaseChangeMate.{u, r} Λ f g g' f' P hP₁ hP₂ M =
      (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' (hP₁.symm.trans hP₂)).app M := by
  rw [etaleModuleDerivedBaseChangeGeneral,
    etaleModuleBaseChange_eq_mateEquiv.{u, r} Λ f g g' f' P hP₁ hP₂,
    Stacks.Homology.DerivedSquare.cochainDerivedSquare_mateEquiv _ _ _ _ _
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective,
    Stacks.Homology.DerivedSquare.derivedTwoSquare_eq_pullbackComparison]
  rfl

end BaseChangeMate

/-- **The reduction of [Stacks, Tag 0F0G] to its three inputs.** Let
`f : X ⟶ Y` be proper and `Λ` a torsion ring. Granted

* `h095T`: cohomology commutes with base change for `f` ([Stacks, Tag 095T]);
* `h095U`: for every proper `p : S ⟶ T` all of whose fibres have dimension at most `N`,
  `R^q p_* F = 0` for every torsion abelian sheaf `F` and `q > 2N` ([Stacks, Tag 095U]);
* `h0F12`: for every quasi-compact quasi-separated `p : Z ⟶ Spec Ω` over a separably closed field
  whose higher direct images vanish on torsion sheaves above some degree (that is,
  `cd(Z) < ∞`), the projection formula map of `p` is invertible at every pair `(E, K)`: this is
  [Stacks, Tag 0F12] for `Z`, read through `D((Spec Ω)_étale, Λ) ≃ D(Λ)` (global sections), under
  which `Rp_*` is `RΓ(Z, -)`, `p⁻¹K` is the constant complex `K̲` and the projection formula map
  is the map `RΓ(Z, E) ⊗^L_Λ K ⟶ RΓ(Z, E ⊗^L_Λ K̲)` of the source,

the projection formula map `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` is an isomorphism for all
`E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`.

The proof is the source's: the map is checked after pulling back to every geometric point `ȳ`;
there, by the base change hexagon, it is the projection formula map of `X_ȳ ⟶ ȳ` up to the base
change maps at `E` and at `E ⊗^L_Λ f⁻¹K`, which are invertible by [Stacks, Tag 0F0C] (from
`h095T` and `h095U`, through `etaleModuleDerivedBaseChangeMate_eq`), and the projection formula
map of `X_ȳ ⟶ ȳ` is invertible by `h0F12`, `X_ȳ` having bounded fibre dimension, hence finite
cohomological dimension by `h095U`. -/
theorem isIso_etaleModuleProjectionFormulaMap_of_isProper (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (h095T : CohomologyCommutesWithBaseChange.{u, r} f)
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    (h0F12 : ∀ ⦃Ω : Type u⦄ [Field Ω] [IsSepClosed Ω] ⦃Z : Scheme.{u}⦄
      (p : Z ⟶ Spec (.of Ω)) [QuasiCompact p] [QuasiSeparated p],
      (∃ d : ℕ, ∀ F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
        Stacks.Torsion.torsionSheafProperty Z.smallEtaleTopology F → ∀ q : ℕ, d < q →
          IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F)) →
      ∀ (E : DerivedCategory (EtaleModules.{u, r} Λ Z))
        (K : DerivedCategory (EtaleModules.{u, r} Λ (Spec (.of Ω)))),
        IsIso (etaleModuleProjectionFormulaMap.{u, r} Λ p E K))
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    IsIso (etaleModuleProjectionFormulaMap.{u, r} Λ f E K) := by
  obtain ⟨n, hn0, hn⟩ := exists_nat_cast_eq_zero_of_isTorsion hΛ
  rw [isIso_iff_forall_isIso_etaleModuleDerivedInverseImage_map]
  intro Ω _ _ y
  have sq : IsPullback (pullback.fst f y) (pullback.snd f y) f y := IsPullback.of_hasPullback f y
  have hbc (M : DerivedCategory (EtaleModules.{u, r} Λ X)) :
      IsIso (etaleModuleDerivedBaseChangeMate.{u, r} Λ f y (pullback.fst f y) (pullback.snd f y)
        (pullback.fst f y ≫ f) rfl pullback.condition M) := by
    rw [etaleModuleDerivedBaseChangeMate_eq]
    exact isIso_etaleModuleDerivedBaseChange_app_of_isIso.{u, r} Λ f y _ _ _ M
      (isIso_etaleAbelianDerivedBaseChange_forget_of_isProper.{u, r} Λ hn h095T h095U sq hn0 M)
  have : IsProper (pullback.snd f y) := inferInstance
  obtain ⟨N, hN⟩ := exists_topologicalKrullDim_fiber_le (pullback.snd f y)
  exact isIso_map_etaleModuleProjectionFormulaMap_of_isIso.{u, r} Λ f y (pullback.fst f y)
    (pullback.snd f y) _ rfl pullback.condition E K (hbc E) (hbc _)
    (h0F12 (pullback.snd f y) ⟨2 * N, fun F hF q hq ↦ h095U _ N hN F hF q hq⟩ _ _)

end Stacks.EtaleCohomology

end

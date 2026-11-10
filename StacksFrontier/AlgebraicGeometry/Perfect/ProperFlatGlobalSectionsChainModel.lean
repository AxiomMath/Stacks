module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.BaseChangeFlat

/-!
# The finite projective model as a chain map to the Čech model

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism and `F` a coherent `𝒪_X`-module
flat over `A`. [Stacks, Tag 07VK] (1) gives a bounded complex `M` of finite projective
`A`-modules with an isomorphism `RΓ(X, F) ≅ Q M` in `D(A)`. This file shows that `M` admits a
morphism of complexes `M ⟶ K`, into the `A`-linear alternating Čech model
`K = baseAlternatingCechComplex` of a finite affine cover, which is a quasi-isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_finiteProjectiveModel_quasiIso`:
  the model, with a chain map to the Čech model which is a quasi-isomorphism.
* `StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat`: termwise extension of
  scalars along any ring map carries a quasi-isomorphism of bounded above termwise flat
  complexes to a quasi-isomorphism.

## References

* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace StacksDraft.PseudoCoherence

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Termwise extension of scalars preserves quasi-isomorphisms of bounded above termwise flat
complexes.** If `u : M ⟶ K` is a quasi-isomorphism of bounded above complexes of flat
`A`-modules and `φ : A →+* A'` is a ring map, then applying `ModuleCat.extendScalars φ` termwise
to `u` gives a quasi-isomorphism. -/
theorem quasiIso_extendScalars_map_of_flat {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A') {M K : CochainComplex (ModuleCat.{u} A) ℤ} (b c : ℤ)
    [M.IsStrictlyLE b] [K.IsStrictlyLE c]
    [∀ n : ℤ, Module.Flat A (M.X n)] [∀ n : ℤ, Module.Flat A (K.X n)]
    (u : M ⟶ K) [QuasiIso u] :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) := by
  have hQu : IsIso (DerivedCategory.Q.map u) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hM : IsIso ((extendScalarsDerivedCounit φ).app M) :=
    isIso_extendScalarsDerivedCounit_app_of_flat φ M b
  have hK : IsIso ((extendScalarsDerivedCounit φ).app K) :=
    isIso_extendScalarsDerivedCounit_app_of_flat φ K c
  have hFu : IsIso ((DerivedCategory.Q ⋙ extendScalarsDerived φ).map u) := by
    change IsIso ((extendScalarsDerived φ).map (DerivedCategory.Q.map u))
    infer_instance
  have h : ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).map u =
      inv ((extendScalarsDerivedCounit φ).app M) ≫
        ((DerivedCategory.Q ⋙ extendScalarsDerived φ).map u ≫
          (extendScalarsDerivedCounit φ).app K) := by
    rw [IsIso.eq_inv_comp]
    exact ((extendScalarsDerivedCounit φ).naturality u).symm
  have hiso : IsIso (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map u) := by
    rw [h]
    infer_instance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hiso

end StacksDraft.PseudoCoherence

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **A bounded complex of finite projective `A`-modules with a quasi-isomorphism to the Čech
model.** For `A` Noetherian, `f` proper and `F` coherent and flat over `A`, and for a finite
affine open cover `U` of `X` whose finite intersections are affine, there is a bounded complex
`M` of finite projective `A`-modules and a **morphism of complexes** `M ⟶ K` to the `A`-linear
alternating Čech model `K` of `U` which is a quasi-isomorphism. -/
theorem exists_finiteProjectiveModel_quasiIso [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] [LinearOrder I]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite A (M.X i)) ∧ (∀ i : ℤ, Module.Projective A (M.X i)) ∧
        ∃ u : M ⟶ baseAlternatingCechComplex f U hU F, QuasiIso u := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := isPerfect_derivedGlobalSections f F hflat
  refine ⟨M, a, b, hGE, hLE, hfin, hproj, ?_⟩
  have hprojX : ∀ n : ℤ, CategoryTheory.Projective (M.X n) := fun n =>
    have := hproj n
    inferInstance
  have hKP : M.IsKProjective := CochainComplex.isKProjective_of_projective M b
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective M
    (baseAlternatingCechComplex f U hU F)
    (e.inv ≫ (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU F haff).inv)
  refine ⟨u, (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 ?_⟩
  rw [hu]
  infer_instance

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end

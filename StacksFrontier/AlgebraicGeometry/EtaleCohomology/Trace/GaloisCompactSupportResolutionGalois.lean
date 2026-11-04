module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionCoeffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpPairing
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Algebra.Homology.HorseshoePrescribed

/-!
# The chain model `Γ^Gal(I)` of `RΓ^Gal_c(X_k̄, ℱ_M)`: vanishing and coeffacements

For an injective resolution `I` of `j_! F` on the compactification `X̄`, `Γ^Gal(I)` is a complex of
discrete Galois modules whose underlying complex is `Γ(X̄_k̄, I|_{X̄_k̄})`
(`Stacks.EtaleCohomology.galoisGlobalSections_comp_underlying`). Forgetting the action is exact and
faithful, so the vanishing of `H^m_c` above degree `2` and the vanishing of `H_c^{2-i}(π)` for a
coeffacement `π` of the left derived functors `Tᵢ` of Tag 03VM, proved on the underlying complexes
(`Stacks.EtaleCohomology.isZero_homology_compactSupportResolution_of_two_lt`,
`AlgebraicGeometry.homologyMap_compactSupportResolution_eq_zero`), hold for `Γ^Gal(I)`
(`AlgebraicGeometry.isZero_homology_galoisHomOpA_of_two_lt`,
`AlgebraicGeometry.homologyMap_galoisHomOpA_eq_zero`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius
open Stacks.GroupCohomology Stacks.EtaleCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

section Forget

variable {Λ : Type} [Ring Λ] {k : Type u} [Field k] {kbar : Type u} [Field kbar] [Algebra k kbar]

/-- Forgetting the Galois action of discrete Galois modules is faithful. -/
instance faithful_continuousModuleUnderlying_galois :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)).Faithful :=
  inferInstanceAs (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _).Faithful

/-- The cohomology of a complex of discrete Galois modules vanishes when that of its underlying
complex of modules does. -/
lemma isZero_homology_of_isZero_underlying (X : CochainComplex (GaloisModules Λ k kbar) ℤ) (m : ℤ)
    (h : IsZero ((((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
      (kbar ≃ₐ[k] kbar)).mapHomologicalComplex _).obj X).homology m)) :
    IsZero (X.homology m) := by
  have e := (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
    (kbar ≃ₐ[k] kbar)).mapHomologicalComplexHomologyFunctorIso m
  rw [IsZero.iff_id_eq_zero, ← Functor.map_eq_zero_iff
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)),
    CategoryTheory.Functor.map_id]
  exact (IsZero.of_iso h (e.app X).symm).eq_of_src _ _

/-- A morphism of complexes of discrete Galois modules is zero on cohomology when its underlying
morphism of complexes of modules is. -/
lemma homologyMap_eq_zero_of_underlying {X X' : CochainComplex (GaloisModules Λ k kbar) ℤ}
    (f : X ⟶ X') (m : ℤ)
    (h : HomologicalComplex.homologyMap
      (((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1}
        Λ (kbar ≃ₐ[k] kbar)).mapHomologicalComplex _).map f) m = 0) :
    HomologicalComplex.homologyMap f m = 0 := by
  have e := (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
    (kbar ≃ₐ[k] kbar)).mapHomologicalComplexHomologyFunctorIso m
  have hn := e.hom.naturality f
  change HomologicalComplex.homologyMap _ m ≫ _ = _ ≫
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)).map
      (HomologicalComplex.homologyMap f m) at hn
  rw [← Functor.map_eq_zero_iff
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar))]
  rw [h] at hn
  exact ((e.app X).cancel_iso_hom_left _ _).1 (hn.symm.trans (zero_comp.trans comp_zero.symm))

end Forget

section ChainModel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsSeparable k kbar] (Λ : Type) [Ring Λ] [Finite Λ]

/-- **The Galois chain model `Γ^Gal(I)` of `RΓ^Gal_c(X_k̄, F)` has no cohomology above degree
`2`.** -/
theorem isZero_homology_galoisHomOpA_of_two_lt (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (m : ℤ) (hm : 2 < m) :
    IsZero ((galoisHomOpA (Over.mk j.toBase) kbar I.cocomplex).homology m) :=
  isZero_homology_of_isZero_underlying _ m
    (isZero_homology_compactSupportResolution_of_two_lt f j kbar Λ F I m hm)

end ChainModel

section ShortExact

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [Algebra.IsSeparable k kbar] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
  {Λ : Type} [Ring Λ] (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Y.left) ℤ)

/-- **A degreewise split short exact sequence `L₁ → L₂ → L₃` of complexes gives short exact
sequences `Γ^Gal(L₁) → Γ^Gal(L₂) → Γ^Gal(L₃)` and
`Γ^Gal(ℋom^•(L₃, K)) → Γ^Gal(ℋom^•(L₂, K)) → Γ^Gal(ℋom^•(L₁, K))`.** -/
theorem shortExact_galoisHomOp_of_splitting
    (S : ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ))
    (h : ∀ p, Nonempty ((S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) p)).Splitting)) :
    (S.map ((galoisGlobalSections Λ Y kbar).mapHomologicalComplex _)).ShortExact ∧
      ((Stacks.AbelianInternalHom.homOpComplexPrecompShortComplex
          (M := etaleHomOpTarget Y Kc) S).map
        ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex _)).ShortExact :=
  ⟨HomologicalComplex.shortExact_map_mapHomologicalComplex_of_splitting S h _,
    HomologicalComplex.shortExact_map_mapHomologicalComplex_of_splitting _
      (Stacks.AbelianInternalHom.homOpComplexPrecompShortComplex_splitting S h) _⟩

end ShortExact

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsSeparable k kbar]

/-- **A coeffacement for `Tᵢ` is zero on the Galois chain models** `Γ^Gal(I)` in degree `2 - i`. -/
theorem homologyMap_galoisHomOpA_eq_zero (i : ℕ) (hi : i ≤ 2)
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (π : M ⟶ N)
    (h : ((compactSupportRepresentationHomology B X x Λ f j kbar).functor i).map π = 0)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
        ((representationSheaf B X x Λ).obj M))))
    (I' : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
        ((representationSheaf B X x Λ).obj N))))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
        ((representationSheaf B X x Λ).map π)) ≫ I'.ι) :
    HomologicalComplex.homologyMap
      (((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map φ)
      ((2 - i : ℕ) : ℤ) = 0 :=
  homologyMap_eq_zero_of_underlying _ _
    (homologyMap_compactSupportResolution_eq_zero B X x Λ f j kbar i hi π h I I' φ hφ)

end AlgebraicGeometry

end

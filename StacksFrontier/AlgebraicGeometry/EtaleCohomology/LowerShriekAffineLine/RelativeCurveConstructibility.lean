module
public import StacksCore.Algebra.Homology.TotalComplexHomotopy
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.RingTheory.AdicCompletion.AnalyticallyUnramified
public import StacksFrontier.RingTheory.NoetherNormalization.Basic
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.CurveConstructibility
public import StacksFrontier.CategoryTheory.Abelian.ExtKillingByMonomorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImageUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ConstructiblePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.Annihilator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CohomologicalBound

/-!
# Compactly supported cohomology of a smooth family of curves with constructible coefficients

Let `f : X ⟶ Y` be separated, quasi-compact and smooth of relative dimension one over a Noetherian
scheme. This file proves that `Rf_!` carries a constructible torsion sheaf of `Λ`-modules placed in
degree zero to an object with constructible cohomology sheaves. This is the common form of
Tags 0GKY and 0GKZ over a Noetherian base, and it is proved by a route different from the
source's (whose proof of Tag 0GKY has a gap, see that tag's docstring): descending induction on
the cohomological degree, starting from the vanishing of `R^q f_!` in high degrees (Tag 0G2A,
from Tag 095U), over all constructible sheaves killed by a fixed integer `n`. Each such sheaf is a
quotient of a finite sum of sheaves `e_! (Λ/nΛ)̲` with `e` étale from an affine scheme
(Tag 095N), whose `Rf_!` is `R(e ≫ f)_! (Λ/nΛ)̲`, constructible by Tag 0GKX.

## Main results

* `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_extensionByZero_constantSheaf`:
  `Rf_!(e_! M̲)` is constructible.
* `exists_epi_sigma_etaleModuleExtensionByZero_quotientNSMul`: the presentation of a constructible
  sheaf killed by `n`.
* `isConstructibleEtaleModule_homology_obj₃_of_distinguished`: the step of the induction.
* `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_smoothOfRelativeDimension_one`:
  `Rf_!(ℱ[0])` has constructible cohomology sheaves for a constructible torsion sheaf `ℱ`.

## Implementation notes

The comparison `(ι ≫ π)_! ≅ π_* ∘ ι_!` for an open immersion `ι` followed by a finite `π` whose
composite is étale is `Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIsoDirectImage`, and
Tag 095N in the model `EtaleModules` is
`Stacks.EtaleCohomology.exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule`.
The named arguments are `h095T` (Tag 095T), `h0GKV` (Tag 0GKV, from which Tag 0GKW is proved) and
`h095U` (Tag 095U).

## References

* [Stacks Project, Tag 0GKY](https://stacks.math.columbia.edu/tag/0GKY)
* [Stacks Project, Tag 0GKZ](https://stacks.math.columbia.edu/tag/0GKZ)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Abelian.hasFiniteBiproducts

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- Extension by zero along two equal étale morphisms. -/
theorem etaleModuleExtensionByZero_congr {U X : Scheme.{u}} {a b : U ⟶ X} [Etale a] [Etale b]
    (h : a = b) : etaleModuleExtensionByZero.{u, u + 1} Λ a = etaleModuleExtensionByZero Λ b := by
  subst h
  rfl

/-- **`Rf_!` of an étale extension by zero of `M̲`**, granted Tags 095T and 0GKV and the comparison
`e_! = π_* ∘ ι_!` for an étale `e = ι ≫ π` with `ι` an open immersion and `π` finite
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIsoDirectImage`). Let `f : X ⟶ Y` be
separated, quasi-compact and smooth of relative dimension one over a Noetherian scheme, `J` a
compactification of `f`, `e : W ⟶ X` étale with `W` affine, and `M` a finite `Λ`-module killed by
`n > 0`. Then `Rf_!(e_! M̲)` has constructible cohomology sheaves.

Zariski's main theorem factors the étale `W ⟶ X̄` as an open immersion `ι : W ⟶ T` followed by a
finite `π : T ⟶ X̄`; then `Rf_!(e_! M̲) = Rf̄_* π_* ι_! M̲ = R(e ≫ f)_! M̲`, computed through the
compactification `T` of `W` over `Y`, and `e ≫ f` is separated, quasi-compact and smooth of
relative dimension one, so Tag 0GKX applies.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_extensionByZero_constantSheaf
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] {n : ℕ} (hn0 : 0 < n)
    (hM : ∀ m : M, n • m = 0) {X Y W : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [SmoothOfRelativeDimension 1 f] (J : CompactificationOf (Over.mk f))
    (e : W ⟶ X) [Etale e] [IsAffine W] :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((etaleModuleExtensionByZero.{u, u + 1} Λ e).obj
          ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  classical
  let G := (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have : IsNoetherian J.space := isNoetherian_of_locallyOfFiniteType J.toBase
  let ε := e ≫ J.immersion
  have : LocallyOfFinitePresentation ε :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  obtain ⟨T, ι, π, hι, hιqc, hπ, hπfp, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization ε
  have := hι
  have := hπ
  have : Etale (ι ≫ π) := hfac ▸ (inferInstance : Etale ε)
  have hg : ι ≫ π ≫ J.toBase = e ≫ f := by
    rw [← Category.assoc, ← hfac]
    simp [ε]
  let J' := CompactificationOf.ofFactorizationGeneral (e ≫ f) ι (π ≫ J.toBase) hg
  have : SmoothOfRelativeDimension 0 e :=
    (Etale.iff_smoothOfRelativeDimension_zero e).1 inferInstance
  have : SmoothOfRelativeDimension 1 (e ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have h0GKX := isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf_of_nsmul Λ M
    h095T h0GKV hn0 hM (e ≫ f) J'
  -- `R(e ≫ f)_! M̲ = R(π ≫ f̄)_* ι_! M̲ = Rf̄_* π_* ι_! M̲ = Rf̄_* ε_! M̲ = Rf_! e_! M̲`
  let S := DerivedCategory.singleFunctor
  let e₁ : (derivedLowerShriekUnbounded.{u, u + 1} (e ≫ f) J' Λ).obj ((S _ 0).obj G) ≅
      (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).obj
        ((S _ 0).obj ((etaleModuleDirectImage.{u, u + 1} Λ π).obj
          ((etaleModuleExtensionByZero.{u, u + 1} Λ ι).obj G))) :=
    (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ (π ≫ J.toBase)).mapIso
        ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u + 1} Λ ι).app _ ≪≫
          ((etaleModuleExtensionByZero.{u, u + 1} Λ ι).mapDerivedCategorySingleFunctor 0).app G) ≪≫
      (etaleModuleDerivedDirectImageUnboundedCompIso.{u, u + 1} Λ π J.toBase).app _ ≪≫
      (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).mapIso
        (((etaleModuleDirectImage.{u, u + 1} Λ π).mapDerivedCategorySingleFunctor 0).app _)
  let e₂ : (derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
      ((S _ 0).obj ((etaleModuleExtensionByZero.{u, u + 1} Λ e).obj G)) ≅
      (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).obj
        ((S _ 0).obj ((etaleModuleDirectImage.{u, u + 1} Λ π).obj
          ((etaleModuleExtensionByZero.{u, u + 1} Λ ι).obj G))) :=
    (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).mapIso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u + 1} Λ J.immersion).app _ ≪≫
        ((etaleModuleExtensionByZero.{u, u + 1} Λ J.immersion).mapDerivedCategorySingleFunctor
          0).app _ ≪≫
        (S _ 0).mapIso
          ((etaleModuleExtensionByZeroCompIso.{u, u + 1} Λ e J.immersion).app G).symm ≪≫
        (S _ 0).mapIso (eqToIso (congrArg (fun F ↦ F.obj G)
          (etaleModuleExtensionByZero_congr Λ hfac))) ≪≫
        (S _ 0).mapIso ((etaleModuleExtensionByZeroCompIsoDirectImage Λ ι π).app G))
  exact isConstructibleEtaleComplex_of_iso Λ (e₁ ≪≫ e₂.symm) h0GKX

/-! ### Presentations by extensions by zero of a constant sheaf killed by `n` -/

/-- The quotient `Λ/nΛ`, as a `Λ`-module: the cokernel of multiplication by `n`. -/
abbrev quotientNSMul (n : ℕ) : ModuleCat.{u + 1} Λ := cokernel (n • 𝟙 (ModuleCat.of Λ Λ))

omit [IsNoetherianRing Λ] in
/-- The quotient `Λ/nΛ` is a finite `Λ`-module. -/
instance (n : ℕ) : Module.Finite Λ (quotientNSMul Λ n) :=
  Module.Finite.of_surjective (cokernel.π (n • 𝟙 (ModuleCat.of Λ Λ))).hom
    ((ModuleCat.epi_iff_surjective (cokernel.π (n • 𝟙 (ModuleCat.of Λ Λ)))).1 inferInstance)

omit [IsNoetherianRing Λ] in
/-- Every element of `Λ/nΛ` is killed by `n`. -/
theorem nsmul_quotientNSMul (n : ℕ) (m : quotientNSMul Λ n) : n • m = 0 := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (cokernel.π (n • 𝟙 (ModuleCat.of Λ Λ)))).1
    inferInstance m
  rw [← map_nsmul, show (n • y : Λ) = (n • 𝟙 (ModuleCat.of Λ Λ)).hom y by simp,
    ← ConcreteCategory.comp_apply, cokernel.condition]
  rfl

/-- A morphism into an object killed by `n` is killed by `n`. -/
private theorem nsmul_eq_zero_of_nsmul_id_target {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) {n : ℕ} (h : n • 𝟙 B = 0) : n • g = 0 := by
  rw [← Category.comp_id g, ← Preadditive.comp_nsmul, h, comp_zero]

/-- A morphism out of an object killed by `n` is killed by `n`. -/
private theorem nsmul_eq_zero_of_nsmul_id_source {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) {n : ℕ} (h : n • 𝟙 A = 0) : n • g = 0 := by
  rw [← Category.id_comp g, ← Preadditive.nsmul_comp, h, zero_comp]

/-- **A presentation of a constructible sheaf killed by `n`**, from the presentation of Tag 095N
(`exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule`): a constructible
sheaf `ℱ` with `n • 𝟙 = 0` on a quasi-compact quasi-separated scheme is a quotient of a finite
direct sum of extensions by zero `e_! (Λ/nΛ)̲` along étale morphisms from affine schemes. Each map
`e_! Λ̲ ⟶ ℱ` factors through `e_! (Λ/nΛ)̲`, the image of the cokernel of `n` under the left
adjoint `e_! ∘ (-)̲`. -/
theorem exists_epi_sigma_etaleModuleExtensionByZero_quotientNSMul
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) {n : ℕ} (hn : n • 𝟙 F = 0) :
    ∃ (m : ℕ) (W : Fin m → Scheme.{u}) (e : ∀ i, W i ⟶ X) (_ : ∀ i, Etale (e i))
      (_ : ∀ i, IsAffine (W i))
      (p : (∐ fun i ↦ (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
        ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (quotientNSMul Λ n))) ⟶ F), Epi p := by
  classical
  obtain ⟨m, W, e, he, hW, p, hp⟩ :=
    exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule Λ F hF
  let f := n • 𝟙 (ModuleCat.of Λ Λ)
  let Ψ : ∀ i, ModuleCat.{u + 1} Λ ⥤ EtaleModules.{u, u + 1} Λ X := fun i ↦
    constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      etaleModuleExtensionByZero.{u, u + 1} Λ (e i)
  have hadj : ∀ i, (Ψ i).IsLeftAdjoint := fun i ↦
    ⟨_, ⟨(constantSheafAdj _ (ModuleCat.{u + 1} Λ) (etaleSiteTerminalIsTerminal (W i))).comp
      (etaleModuleExtensionByZeroAdj.{u, u + 1} Λ (e i))⟩⟩
  have : ∀ i, PreservesColimit (parallelPair f 0) (Ψ i) := fun i ↦ by
    have := hadj i
    infer_instance
  have hΨ : ∀ i, (Ψ i).map f = n • 𝟙 _ := fun i ↦ by
    simp only [f, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  let q : ∀ i, (Ψ i).obj (ModuleCat.of Λ Λ) ⟶ F := fun i ↦
    Sigma.ι (fun i ↦ (Ψ i).obj (ModuleCat.of Λ Λ)) i ≫ p
  have hq : ∀ i, (Ψ i).map f ≫ q i = 0 := fun i ↦ by
    simp only [q]
    rw [hΨ, Preadditive.nsmul_comp, Category.id_comp]
    exact nsmul_eq_zero_of_nsmul_id_target _ hn
  let q' : ∀ i, (Ψ i).obj (quotientNSMul Λ n) ⟶ F := fun i ↦
    (PreservesCokernel.iso (Ψ i) f).hom ≫ cokernel.desc _ (q i) (hq i)
  have hq' : ∀ i, (Ψ i).map (cokernel.π f) ≫ q' i = q i := fun i ↦ by
    simp only [q', ← π_comp_cokernelComparison, ← PreservesCokernel.iso_inv, Category.assoc,
      Iso.inv_hom_id_assoc, cokernel.π_desc]
  refine ⟨m, W, e, he, hW, Sigma.desc q', ?_⟩
  have hfac : Limits.Sigma.map (fun i ↦ (Ψ i).map (cokernel.π f)) ≫ Sigma.desc q' = p := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    simp only [Limits.Sigma.ι_map_assoc, Sigma.ι_comp_desc, hq']
    rfl
  rw [← hfac] at hp
  exact epi_of_epi (Limits.Sigma.map fun i ↦ (Ψ i).map (cokernel.π f)) (Limits.Sigma.desc q')

/-! ### The descending induction on the cohomological degree -/

open DerivedCategory Pretriangulated in
/-- **One step of the descending induction.** In a distinguished triangle `T` of
`D(Y_étale, Λ)` over a Noetherian scheme, if `H^q(T.obj₂)`, `H^{q+1}(T.obj₁)` and
`H^{q+1}(T.obj₂)` are constructible, so is `H^q(T.obj₃)`: in the exact sequence
`ker ⟶ H^q(T.obj₂) ⟶ H^q(T.obj₃) ⟶ H^{q+1}(T.obj₁) ⟶ H^{q+1}(T.obj₂)` the kernel is a
subsheaf of a constructible sheaf, hence constructible (Tag 09BH (3)), and constructible
sheaves form a weak Serre subcategory. -/
theorem isConstructibleEtaleModule_homology_obj₃_of_distinguished {Y : Scheme.{u}}
    [IsNoetherian Y] (T : Triangle (DerivedCategory (EtaleModules.{u, u + 1} Λ Y)))
    (hT : T ∈ distTriang _) (q : ℤ)
    (h₂ : IsConstructibleEtaleModule Λ ((homologyFunctor _ q).obj T.obj₂))
    (h₁' : IsConstructibleEtaleModule Λ ((homologyFunctor _ (q + 1)).obj T.obj₁))
    (h₂' : IsConstructibleEtaleModule Λ ((homologyFunctor _ (q + 1)).obj T.obj₂)) :
    IsConstructibleEtaleModule Λ ((homologyFunctor _ q).obj T.obj₃) := by
  set F := homologyFunctor (EtaleModules.{u, u + 1} Λ Y) 0 with hF
  have hB : WeakSerre.IsWeakSerre (IsConstructibleEtaleModule.{u, u + 1} Λ (X := Y)) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  let a := (F.shift q).map T.mor₂
  exact hB.mem_of_exact5
    { obj₀ := kernel a
      obj₁ := (F.shift q).obj T.obj₂
      obj₂ := (F.shift q).obj T.obj₃
      obj₃ := (F.shift (q + 1)).obj T.obj₁
      obj₄ := (F.shift (q + 1)).obj T.obj₂
      f₀ := kernel.ι a
      f₁ := a
      f₂ := F.homologySequenceδ T q (q + 1) rfl
      f₃ := (F.shift (q + 1)).map T.mor₁
      zero₀ := kernel.condition a
      zero₁ := F.comp_homologySequenceδ T hT q (q + 1) rfl
      zero₂ := F.homologySequenceδ_comp T hT q (q + 1) rfl
      exact₁ := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel a)
      exact₂ := F.homologySequence_exact₃ T hT q (q + 1) rfl
      exact₃ := F.homologySequence_exact₁ T hT q (q + 1) rfl }
    (isConstructibleEtaleModule_of_mono Λ (kernel.ι a) h₂) h₂ h₁' h₂'

/-! ### Constructibility of the good sheaves -/

/-- **Extension by zero along an étale morphism from an affine scheme preserves
constructibility**: by Zariski's main theorem `e = ι ≫ π` with `ι` a quasi-compact open immersion
and `π` finite of finite presentation, `e_! = π_* ∘ ι_!`, and `ι_!` (Tag 03S8 for an open
immersion) and `π_*` (Tag 095R) preserve constructibility. -/
theorem isConstructibleEtaleModule_etaleModuleExtensionByZero_of_etale
    {W X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (e : W ⟶ X) [Etale e]
    [IsAffine W] (G : EtaleModules.{u, u + 1} Λ W) (hG : IsConstructibleEtaleModule Λ G) :
    IsConstructibleEtaleModule Λ ((etaleModuleExtensionByZero.{u, u + 1} Λ e).obj G) := by
  have : LocallyOfFinitePresentation e := inferInstance
  have : QuasiCompact e := inferInstance
  obtain ⟨T, ι, π, hι, hιqc, hπ, hπfp, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization e
  have := hι
  have := hπ
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated π
  have : Etale (ι ≫ π) := hfac ▸ (inferInstance : Etale e)
  exact (IsConstructibleEtaleModule Λ).prop_of_iso (eqToIso (congrArg (fun F ↦ F.obj G)
    (etaleModuleExtensionByZero_congr Λ hfac)) ≪≫
      (etaleModuleExtensionByZeroCompIsoDirectImage Λ ι π).app G).symm
    (isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite Λ π hπfp _
      (isConstructibleEtaleModule_etaleModuleExtensionByZero Λ ι G hG))

/-- On a Noetherian scheme a quotient of a constructible sheaf is constructible. -/
instance isClosedUnderQuotients_isConstructibleEtaleModule {X : Scheme.{u}} [IsNoetherian X] :
    (IsConstructibleEtaleModule.{u, u + 1} Λ (X := X)).IsClosedUnderQuotients :=
  ⟨fun f _ hX ↦ isConstructibleEtaleModule_of_epi Λ f hX⟩

/-- On a Noetherian scheme a finite coproduct of constructible sheaves is constructible. -/
theorem isConstructibleEtaleModule_sigma {X : Scheme.{u}} [IsNoetherian X] {m : ℕ}
    (G : Fin m → EtaleModules.{u, u + 1} Λ X) (hG : ∀ i, IsConstructibleEtaleModule Λ (G i)) :
    IsConstructibleEtaleModule Λ (∐ G) :=
  (IsConstructibleEtaleModule Λ).prop_of_iso (biproduct.isoCoproduct G)
    (Stacks.ExtKilling.prop_biproduct G hG)

/-! ### Sheaves killed by `n` -/

omit [IsNoetherianRing Λ] in
/-- The extension by zero `e_! M̲` of a constant sheaf on a module killed by `n` is killed
by `n`. -/
theorem nsmul_id_etaleModuleExtensionByZero_constantSheaf_eq_zero {W X : Scheme.{u}}
    (e : W ⟶ X) [Etale e] (M : ModuleCat.{u + 1} Λ) {n : ℕ} (hM : ∀ m : M, n • m = 0) :
    n • 𝟙 ((etaleModuleExtensionByZero.{u, u + 1} Λ e).obj
      ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) = 0 := by
  have hM' : n • 𝟙 M = 0 := by
    ext x
    simpa using hM x
  have := (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    etaleModuleExtensionByZero.{u, u + 1} Λ e).map_nsmul (f := 𝟙 M) (n := n)
  rw [CategoryTheory.Functor.map_id, hM', Functor.map_zero] at this
  exact this.symm

/-! ### The theorem -/

/-- **`Rf_!` of a finite sum of étale extensions by zero `e_! M̲`**, granted Tags 095T and 0GKV:
under the hypotheses of
`isConstructibleEtaleComplex_derivedLowerShriekUnbounded_extensionByZero_constantSheaf`, `Rf_!`
of a finite direct sum of sheaves `e_! M̲` has constructible cohomology sheaves. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_sigma_extensionByZero
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] {n : ℕ} (hn0 : 0 < n)
    (hM : ∀ m : M, n • m = 0) {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [SmoothOfRelativeDimension 1 f] (J : CompactificationOf (Over.mk f))
    {m : ℕ} (W : Fin m → Scheme.{u}) (e : ∀ i, W i ⟶ X) [∀ i, Etale (e i)]
    [∀ i, IsAffine (W i)] :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        (∐ fun i ↦ (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
          ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, u + 1} Λ J.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, u + 1} Λ J.toBase
  have : (derivedLowerShriekUnbounded.{u, u + 1} f J Λ).Additive :=
    Functor.additive_of_iso (derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, u + 1} Λ J).symm
  intro q
  let Ψ := DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0 ⋙
    derivedLowerShriekUnbounded.{u, u + 1} f J Λ ⋙ DerivedCategory.homologyFunctor _ q
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    ((Ψ.mapIso (biproduct.isoCoproduct _)).symm ≪≫ Ψ.mapBiproduct _).symm
    (Stacks.ExtKilling.prop_biproduct _ fun i ↦
      isConstructibleEtaleComplex_derivedLowerShriekUnbounded_extensionByZero_constantSheaf Λ
        h095T h0GKV M hn0 hM f J (e i) q)

/-- **The long exact sequence of `Rf_!`.** For a short exact sequence `0 → 𝒦 → 𝒢 → ℱ → 0` of
sheaves on `X_étale` with `Y` Noetherian, if `R^q f_! 𝒢`, `R^{q+1} f_! 𝒦` and `R^{q+1} f_! 𝒢` are
constructible, so is `R^q f_! ℱ`. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriekUnbounded_of_shortExact
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y} (J : CompactificationOf (Over.mk f))
    {T : ShortComplex (EtaleModules.{u, u + 1} Λ X)} (hT : T.ShortExact) (q : ℤ)
    (h₂ : IsConstructibleEtaleModule Λ ((DerivedCategory.homologyFunctor _ q).obj
      ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
        ((DerivedCategory.singleFunctor _ 0).obj T.X₂))))
    (h₁' : IsConstructibleEtaleModule Λ ((DerivedCategory.homologyFunctor _ (q + 1)).obj
      ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
        ((DerivedCategory.singleFunctor _ 0).obj T.X₁))))
    (h₂' : IsConstructibleEtaleModule Λ ((DerivedCategory.homologyFunctor _ (q + 1)).obj
      ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
        ((DerivedCategory.singleFunctor _ 0).obj T.X₂)))) :
    IsConstructibleEtaleModule Λ ((DerivedCategory.homologyFunctor _ q).obj
      ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
        ((DerivedCategory.singleFunctor _ 0).obj T.X₃))) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, u + 1} Λ J.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, u + 1} Λ J.toBase
  let G' := (etaleModuleExtensionByZero.{u, u + 1} Λ J.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase
  let eΦ : derivedLowerShriekUnbounded.{u, u + 1} f J Λ ≅ G' :=
    derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, u + 1} Λ J
  let H := fun q : ℤ ↦ DerivedCategory.homologyFunctor (EtaleModules.{u, u + 1} Λ Y) q
  have ht : ∀ (q : ℤ) (K : DerivedCategory (EtaleModules.{u, u + 1} Λ X)),
      IsConstructibleEtaleModule Λ
        ((H q).obj ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj K)) →
      IsConstructibleEtaleModule Λ ((H q).obj (G'.obj K)) := fun q K ↦
    (IsConstructibleEtaleModule Λ).prop_of_iso ((H q).mapIso (eΦ.app K))
  have hT' := G'.map_distinguished _ hT.singleTriangle_distinguished
  exact (IsConstructibleEtaleModule Λ).prop_of_iso ((H q).mapIso (eΦ.app _)).symm
    (isConstructibleEtaleModule_homology_obj₃_of_distinguished Λ _ hT' q (ht q _ h₂)
      (ht (q + 1) _ h₁') (ht (q + 1) _ h₂'))

/-- **`Rf_!` of a constructible torsion sheaf on a smooth family of curves is constructible**,
granted Tags 095T, 0GKV and 095U. Let `Y` be Noetherian, `f : X ⟶ Y` separated, quasi-compact and
smooth of relative dimension one, `J` a compactification of `f` and `ℱ` a constructible torsion
sheaf of `Λ`-modules on `X_étale`. Then `Rf_!(ℱ[0])` has constructible cohomology sheaves.

The proof is by descending induction on the degree, over all constructible sheaves on `X` killed
by an integer `n` killing `ℱ`: `R^q f_! = 0` for `q` beyond the bound of Tag 0G2A (from
Tag 095U); a constructible sheaf killed by `n` is a quotient of a finite sum `𝒢` of `e_! (Λ/nΛ)̲`
with `e` étale from an affine scheme (Tag 095N); `Rf_! 𝒢` is constructible by Tag 0GKX applied to
`e ≫ f`; the kernel `𝒦` is again constructible and killed by `n`; and in the long exact sequence of
`0 → 𝒦 → 𝒢 → ℱ → 0` the sheaf `R^q f_! ℱ` sits between the image of `R^q f_! 𝒢`, a quotient of a
constructible sheaf, and the kernel of `R^{q+1} f_! 𝒦 → R^{q+1} f_! 𝒢`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant` from it);
`h095U` is Stacks Tag 095U. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_smoothOfRelativeDimension_one
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, u + 1} p).rightDerived q).obj F))
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (J : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, u + 1} Λ X) (hF : IsConstructibleEtaleModule Λ F)
    (hFt : IsTorsionEtaleModule Λ X F) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj F)) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨n, hn0, -, hn⟩ := exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule Λ 1 F hF
    ((isTorsionPrimeToEtaleModule_one_iff Λ X F).2 hFt)
  obtain ⟨N, hNall⟩ := exists_bound_derivedLowerShriekUnbounded.{u, u + 1} Λ h095U J
  let Φ := derivedLowerShriekUnbounded.{u, u + 1} f J Λ
  let S := DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0
  let H := fun q : ℤ ↦ DerivedCategory.homologyFunctor (EtaleModules.{u, u + 1} Λ Y) q
  -- the descending induction
  have key : ∀ k : ℕ, ∀ G : EtaleModules.{u, u + 1} Λ X, IsConstructibleEtaleModule Λ G →
      n • 𝟙 G = 0 → ∀ q : ℤ, (N : ℤ) + 1 - k ≤ q →
        IsConstructibleEtaleModule Λ ((H q).obj (Φ.obj (S.obj G))) := by
    intro k
    induction k with
    | zero =>
      intro G _ hG q hq
      -- vanishing above the bound
      exact (IsConstructibleEtaleModule Λ).prop_of_isZero <| DerivedCategory.isZero_of_isLE
        (hX := (hNall (S.obj G) (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
          (WeakSerre.isWeakSerre_of_isWeakSerreClass (IsTorsionEtaleModule.{u, u + 1} Λ X)) G
          (isTorsionEtaleModule_of_nsmul_id_eq_zero Λ hn0 hG))).2.2.2 0 inferInstance)
        _ (0 + N) q (by omega)
    | succ k ih =>
      intro G hGc hG q hq
      by_cases hq' : (N : ℤ) + 1 - k ≤ q
      · exact ih G hGc hG q hq'
      obtain ⟨m, W, e, he, hW, p, hp⟩ :=
        exists_epi_sigma_etaleModuleExtensionByZero_quotientNSMul Λ G hGc hG
      -- the good sheaves
      have hGt := isConstructibleEtaleComplex_derivedLowerShriekUnbounded_sigma_extensionByZero Λ
        h095T h0GKV _ hn0 (nsmul_quotientNSMul Λ n) f J W e
      have hKc : IsConstructibleEtaleModule Λ (kernel p) :=
        (IsConstructibleEtaleModule Λ).prop_kernel p (isConstructibleEtaleModule_sigma Λ _ fun i ↦
          isConstructibleEtaleModule_etaleModuleExtensionByZero_of_etale Λ (e i) _
            (isConstructibleEtaleModule_constantSheaf Λ (W i) _)) hGc
      let E : Fin m → EtaleModules.{u, u + 1} Λ X := fun i ↦
        (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
          ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (quotientNSMul Λ n))
      have hEn : ∀ i, n • 𝟙 (E i) = 0 := fun i ↦
        nsmul_id_etaleModuleExtensionByZero_constantSheaf_eq_zero Λ (e i) _
          (nsmul_quotientNSMul Λ n)
      have hGtn : n • 𝟙 (∐ E) = 0 := by
        refine Sigma.hom_ext _ _ fun i ↦ ?_
        rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
        exact nsmul_eq_zero_of_nsmul_id_source _ (hEn i)
      have hKn : n • 𝟙 (kernel p) = 0 := by
        rw [← cancel_mono (kernel.ι p), zero_comp, Preadditive.nsmul_comp, Category.id_comp]
        exact nsmul_eq_zero_of_nsmul_id_target _ hGtn
      exact isConstructibleEtaleModule_homology_derivedLowerShriekUnbounded_of_shortExact Λ J
        (T := ShortComplex.mk (kernel.ι p) p (kernel.condition p))
        (ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p))
          inferInstance hp) q (hGt q) (ih _ hKc hKn (q + 1) (by omega)) (hGt (q + 1))
  intro q
  by_cases hq : q < 0
  · refine (IsConstructibleEtaleModule Λ).prop_of_isZero ?_
    have : (Φ.obj (S.obj F)).IsGE 0 := isGE_derivedLowerShriekUnbounded_obj.{u, u + 1} Λ J _ 0
    exact DerivedCategory.isZero_of_isGE _ 0 q hq
  · exact key (N + 1 - q).toNat F hF hn q (by omega)

end Stacks.EtaleCohomology

end

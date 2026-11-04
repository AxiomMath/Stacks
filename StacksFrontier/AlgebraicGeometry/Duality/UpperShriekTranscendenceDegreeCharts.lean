module

import all StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModelAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTranscendenceDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHomRestrictKFlat
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulayDepth
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Serre.Localization
public import StacksFrontier.Topology.Noetherian.IrreducibleComponents

/-!
# Stalks of the cohomology sheaves of `f^!𝒪_Y` on affine charts

Let `f : X → Y` be a morphism of separated schemes of finite type over a Noetherian scheme `S`.
On an affine chart, the stalk at `x` of a cohomology sheaf of a tilde model is the extension of
scalars of the cohomology of the model to `𝒪_{X,x}`. This identifies the stalks of the cohomology
sheaves of `f^!𝒪_Y` with localizations of the cohomology of relative dualizing complexes, and
transfers the ring-level depth and `(S₂)` statements of [Stacks, Tag 0E9R] to `X`.

## Main results

* `nonempty_modulesStalk_homology_iso_extendScalars`: the stalk of `H^i(K)` at `x` is
  `𝒪_{X,x} ⊗ H^i(ω)` when `K|_U` is the associated sheaf of `ω`.
* `exists_chart_hypotheses_of_residueTrdeg_le`: an affine chart at `x` on which the hypotheses of
  [Stacks, Tag 0E9R] hold.
* `module_finite_modulesStalk_homology_upperShriek`: the stalks of the cohomology sheaves of
  `f^!𝒪_Y` are finite over the local rings of `X`.
* `propertySkModule_modulesStalk_homology_upperShriek_of_residueTrdeg_le`: the stalk
  `H^{-r}(f^!𝒪_Y)_x` satisfies `(S₂)` as an `𝒪_{X,x}`-module.
* `min_two_ringKrullDim_le_moduleDepth_modulesStalk_homology_upperShriek`: a nonzero stalk
  `H^{-r}(f^!𝒪_Y)_x` has depth at least `min(2, dim 𝒪_{X,x})`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

/-! ### The stalk of the cohomology of a tilde model -/

section StalkModel

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

end StalkModel

/-! ### The stalk of a cohomology sheaf of a tilde model, as a module -/

section StalkHomology

/-- **The stalk of a cohomology sheaf of a tilde model, as a module over the local ring.** If
`K|_U` is the associated sheaf of the complex `ω` over `Γ(X, U)` on an affine open `U ∋ x`, then
the stalk of `H^i(K)` at `x` is `𝒪_{X,x} ⊗ H^i(ω)` as an `𝒪_{X,x}`-module: taking stalks and
extending scalars along the localization `Γ(X, U) → 𝒪_{X,x}` are exact, so both commute with
cohomology, and the derived stalk of `K` is the extension of scalars of `ω`. -/
theorem nonempty_modulesStalk_homology_iso_extendScalars {X : Scheme.{u}}
    {K : DerivedCategory X.Modules} {U : X.Opens} (hU : IsAffineOpen U)
    {ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U))}
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)
    (x : X) (hx : x ∈ U) (i : ℤ) :
    Nonempty ((modulesStalkFunctor x).obj ((DerivedCategory.homologyFunctor X.Modules i).obj K) ≅
      (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) := by
  let g := affineGermRingHom hU x hx
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := g.toAlgebra
  have := isLocalization_affineGermRingHom hU x hx
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))
  let E₀ := DerivedCategory.Q.objPreimage K
  let e₀ : DerivedCategory.Q.obj E₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨dS⟩ := nonempty_derivedStalkOfComplex_iso_extendScalars_anyModel E₀ ⟨e₀⟩ hU x hx ω ⟨e⟩
  let F := modulesStalkFunctor x
  let G := ModuleCat.extendScalars.{u, u, u} g
  let I : F.mapDerivedCategory.obj K ≅ G.mapDerivedCategory.obj ω :=
    (F.mapDerivedCategory.mapIso e₀).symm ≪≫ F.mapDerivedCategoryFactors.app E₀ ≪≫ dS
  exact ⟨((F.mapDerivedCategoryHomologyIso i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso I ≪≫ (G.mapDerivedCategoryHomologyIso i).app ω⟩

end StalkHomology

/-- An open embedding sends generic points of irreducible components to generic points of
irreducible components. -/
private theorem closure_singleton_mem_irreducibleComponents_of_isOpenEmbedding {T T' : Type*}
    [TopologicalSpace T] [TopologicalSpace T'] {f : T → T'} (hf : Topology.IsOpenEmbedding f)
    {ξ : T} (hξ : closure {ξ} ∈ irreducibleComponents T) :
    closure {f ξ} ∈ irreducibleComponents T' := by
  obtain ⟨Z, hZ, hle⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure {f ξ}) (isIrreducible_singleton.closure)
  have hξZ : ξ ∈ f ⁻¹' Z := hle (subset_closure (Set.mem_singleton _))
  have hpre := preimage_mem_irreducibleComponents hZ hf ⟨f ξ, hξZ, ⟨ξ, rfl⟩⟩
  have hsub : closure {ξ} ⊆ f ⁻¹' Z :=
    closure_minimal (Set.singleton_subset_iff.mpr hξZ)
      ((isClosed_of_mem_irreducibleComponents Z hZ).preimage hf.continuous)
  have heq : f ⁻¹' Z = closure {ξ} := (hξ.2 hpre.1 hsub).antisymm hsub
  have hZle : Z ⊆ closure {f ξ} := by
    rw [← closure_image_preimage_of_isPreirreducible f hf.isOpenMap Z
      ⟨ξ, hξZ⟩ hZ.1.2 (isClosed_of_mem_irreducibleComponents Z hZ), heq,
      closure_image_closure hf.continuous, Set.image_singleton]
  exact (hle.antisymm hZle) ▸ hZ

/-- In a Noetherian space, every point `x` has an open neighbourhood `W` such that `x`
specializes from every generic point of an irreducible component lying in `W`. -/
private theorem exists_open_forall_generic_specializes {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] (x : T) :
    ∃ W : Opens T, x ∈ W ∧ ∀ ξ ∈ W, closure {ξ} ∈ irreducibleComponents T → x ∈ closure {ξ} := by
  let B := {Z ∈ irreducibleComponents T | x ∉ Z}
  have hB : B.Finite := NoetherianSpace.finite_irreducibleComponents.subset fun _ hZ => hZ.1
  have hclosed : IsClosed (⋃₀ B) := by
    rw [Set.sUnion_eq_biUnion]
    exact hB.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  refine ⟨⟨(⋃₀ B)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨Z, hZ, hxZ⟩
    exact hZ.2 hxZ
  · intro ξ hξ hcomp
    by_contra hx
    exact hξ (Set.mem_sUnion.mpr ⟨closure {ξ}, ⟨hcomp, hx⟩, subset_closure (Set.mem_singleton ξ)⟩)

/-- A minimal prime of a commutative ring is the generic point of an irreducible component
of its prime spectrum. -/
private theorem closure_singleton_mem_irreducibleComponents_of_mem_minimalPrimes {R : Type*}
    [CommRing R] (c : PrimeSpectrum R) (hc : c.asIdeal ∈ minimalPrimes R) :
    closure {c} ∈ irreducibleComponents (PrimeSpectrum R) := by
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
    (by rwa [c.isPrime.isRadical.radical])

/-! ### Tag 0E9V, the vanishing bound -/

section Shriek

open DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The chart data of [Stacks, Tag 0E9V].** Under the hypotheses of the tag, `x` has an affine
chart `U ⊆ f⁻¹(V)` with a presentation `p` of `Γ(Y, V) → Γ(X, U)` at which `f^!𝒪_Y` has the chart
description, together with a prime `𝔭` of `Γ(Y, V)` under the prime of `x` such that the
hypotheses of the ring-level [Stacks, Tag 0E9R] hold for `Γ(Y, V) → Γ(X, U)` at `𝔭`. -/
theorem exists_chart_hypotheses_of_residueTrdeg_le (x : X.left) (r : ℕ)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal)) :
    ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens) (hV : IsAffineOpen V)
      (hUV : U ≤ f.left ⁻¹ᵁ V) (hxU : x ∈ U)
      (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom),
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
          (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
        (tilde.functor Γ(X.left, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
            (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))) ∧
      letI := (f.left.appLE V U hUV).hom.toAlgebra
      letI : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
      ∃ (𝔭 : Ideal Γ(Y.left, V)) (_ : 𝔭.IsPrime),
        IsCohenMacaulayLocalRing (Localization.AtPrime 𝔭) ∧
        (∀ (q : Ideal Γ(X.left, U)) [q.IsPrime], q ∈ minimalPrimes Γ(X.left, U) →
          letI := Ideal.ResidueField.algebraOfLiesOver (q.under Γ(Y.left, V)) q
          Algebra.trdeg (q.under Γ(Y.left, V)).ResidueField q.ResidueField ≤ r) ∧
        Submonoid.map (algebraMap Γ(Y.left, V) Γ(X.left, U)) 𝔭.primeCompl ≤
          (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl := by
  have hSc : CompactSpace ((Functor.fromPUnit S).obj X.right) := inferInstanceAs (CompactSpace S)
  have hXc : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hXN : AlgebraicGeometry.IsNoetherian X.left := ⟨⟩
  obtain ⟨W, hxW, hW⟩ := exists_open_forall_generic_specializes x
  obtain ⟨U, hU, V, hV, hUV, hxU, hUW, p, he⟩ :=
    exists_chart_of_upperShriekStructureSheafCharts f j (upperShriekStructureSheafCharts f j) x W
      hxW
  refine ⟨U, hU, V, hV, hUV, hxU, p, he, ?_⟩
  let φ := f.left.appLE V U hUV
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := φ.hom.toAlgebra
  let : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hsq : hU.fromSpec ≫ f.left = Spec.map φ ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f.left hV hU hUV).symm
  let xu : U.toScheme := ⟨x, hxU⟩
  let q : Spec Γ(X.left, U) := hU.isoSpec.hom.base xu
  let b : Spec Γ(Y.left, V) := (Spec.map φ).base q
  have hqx : hU.fromSpec.base q = x := by
    have hcomp : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
      rw [← IsAffineOpen.isoSpec_inv_ι hU, Iso.hom_inv_id_assoc]
    exact congrArg (fun g : U.toScheme ⟶ X.left => g.base xu) hcomp
  have hby : hV.fromSpec.base b = f.left.base x := by
    rw [← hqx]
    exact (congrArg (fun g : Spec Γ(X.left, U) ⟶ Y.left => g.base q) hsq).symm
  refine ⟨b.asIdeal, b.isPrime, ?_, ?_, ?_⟩
  · have h1 : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (hV.fromSpec.base b)) :=
      (isCohenMacaulayLocalRing_iff_of_ringEquiv
        (Y.left.presheaf.stalkCongr (.of_eq hby)).commRingCatIsoToRingEquiv).mpr hCM
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv ((asIso (hV.fromSpec.stalkMap b) ≪≫
      Spec.stalkIso Γ(Y.left, V) b).commRingCatIsoToRingEquiv)).mp h1
  · intro q _ hq
    let a : Spec Γ(X.left, U) := ⟨q, inferInstance⟩
    have hmin : closure {a} ∈ irreducibleComponents (Spec Γ(X.left, U)) :=
      closure_singleton_mem_irreducibleComponents_of_mem_minimalPrimes a hq
    have hξc : closure {hU.fromSpec.base a} ∈ irreducibleComponents X.left :=
      closure_singleton_mem_irreducibleComponents_of_isOpenEmbedding
        hU.fromSpec.isOpenEmbedding hmin
    have hmemU : hU.fromSpec.base a ∈ U := by
      have h : hU.fromSpec.base a ∈ Set.range hU.fromSpec.base := ⟨a, rfl⟩
      rwa [hU.range_fromSpec] at h
    have heq := Stacks.Chow.residueTrdeg_eq_of_comp_eq_comp hU.fromSpec f.left
      (Spec.map φ) hV.fromSpec hsq a
    exact (trdeg_le_residueTrdeg_spec _ _ φ a).trans
      (heq ▸ htrdeg _ hξc (hW _ (hUW hmemU) hξc))
  · rintro _ ⟨s, hs, rfl⟩
    exact hs

/-- The stalks of the cohomology sheaves of `f^!𝒪_Y` are finite over the local rings of `X`. -/
theorem module_finite_modulesStalk_homology_upperShriek (x : X.left) (i : ℤ) :
    Module.Finite (X.left.presheaf.stalk x) ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj))) := by
  obtain ⟨U, hU, V, hV, hUV, hxU, -, p, ⟨e⟩⟩ := exists_chart_of_upperShriekStructureSheafCharts f j
    (upperShriekStructureSheafCharts f j) x ⊤ trivial
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨J⟩ := nonempty_modulesStalk_homology_iso_extendScalars hU e x hxU i
  have : Module.Finite Γ(X.left, U) ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} Γ(X.left, U)) i).obj
        (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))) :=
    Dualizing.finite_homology_upperShriekFunctor p i
  have := Stacks.DerivedTensorHomDiagonal.finite_extendScalars (affineGermRingHom hU x hxU)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) i).obj
      (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)))
  exact Module.Finite.equiv J.toLinearEquiv.symm

/-- The `(S₂)` property and the depth bound for the stalk `H^{-r}(f^!𝒪_Y)_x`, proved together from
the chart data of `exists_chart_hypotheses_of_residueTrdeg_le`. -/
private theorem propertySkModule_and_depth_modulesStalk_upperShriek
    (x : X.left) (r : ℕ)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal)) :
    (letI := module_finite_modulesStalk_homology_upperShriek f j x (-(r : ℤ))
    PropertySkModule (X.left.presheaf.stalk x) ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.left.Modules (-(r : ℤ))).obj
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj))) 2) ∧
    (Nontrivial ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.left.Modules (-(r : ℤ))).obj
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj))) →
      min (2 : ℕ∞) ((ringKrullDim (X.left.presheaf.stalk x)).unbotD 0) ≤
        moduleDepth (X.left.presheaf.stalk x) ((modulesStalkFunctor x).obj
          ((DerivedCategory.homologyFunctor X.left.Modules (-(r : ℤ))).obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj)))) := by
  let := module_finite_modulesStalk_homology_upperShriek f j x (-(r : ℤ))
  obtain ⟨U, hU, V, hV, hUV, hxU, p, ⟨e⟩, 𝔭, _, hCM', htr, hle⟩ :=
    exists_chart_hypotheses_of_residueTrdeg_le f j x r hCM htrdeg
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) (-(r : ℤ))).obj
    (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))
  have : Module.Finite Γ(X.left, U) H := Dualizing.finite_homology_upperShriekFunctor p _
  let Q := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  obtain ⟨J⟩ := nonempty_modulesStalk_homology_iso_extendScalars hU e x hxU (-(r : ℤ))
  let g := affineGermRingHom hU x hxU
  let : Algebra Γ(X.left, U) (X.left.presheaf.stalk x) := g.toAlgebra
  have : IsLocalization.AtPrime (X.left.presheaf.stalk x) Q :=
    isLocalization_affineGermRingHom hU x hxU
  let T := TensorProduct Γ(X.left, U) (X.left.presheaf.stalk x) H
  have := Stacks.DerivedTensorHomDiagonal.finite_extendScalars g H
  have hS2 : PropertySkModule (Localization.AtPrime Q) (LocalizedModule Q.primeCompl H) 2 :=
    propertySkModule_localizedModule_of_le hle H 2
      (Dualizing.propertySkModule_localizedModule_homology_relativeDualizingComplex
        p 𝔭 hCM' r htr)
  have hT : PropertySkModule (X.left.presheaf.stalk x) T 2 :=
    propertySkModule_of_isLocalizedModule_atPrime Q
      (TensorProduct.mk Γ(X.left, U) (X.left.presheaf.stalk x) H 1) 2 hS2
  refine ⟨propertySkModule_of_linearEquiv J.toLinearEquiv 2 hT, fun hnt => ?_⟩
  obtain ⟨hdep, hdim⟩ := moduleDepth_and_ringKrullDim_of_isLocalizedModule_atPrime Q
    (R' := X.left.presheaf.stalk x) (M' := T)
    (TensorProduct.mk Γ(X.left, U) (X.left.presheaf.stalk x) H 1)
  have hntT : Nontrivial T := J.toLinearEquiv.toEquiv.nontrivial_congr.mp hnt
  have hntH : Nontrivial (LocalizedModule.AtPrime Q H) :=
    (IsLocalizedModule.iso Q.primeCompl
      (TensorProduct.mk Γ(X.left, U) (X.left.presheaf.stalk x) H 1)).toEquiv.nontrivial_congr.mpr
      hntT
  have hq : Disjoint ((Submonoid.map (algebraMap Γ(Y.left, V) Γ(X.left, U)) 𝔭.primeCompl :
      Submonoid Γ(X.left, U)) : Set Γ(X.left, U)) (Q : Set Γ(X.left, U)) :=
    Set.disjoint_left.2 fun a ha haQ => hle ha haQ
  have h :=
    Dualizing.min_two_ringKrullDim_le_moduleDepth_localizedModule_homology_relativeDualizingComplex
      p 𝔭 hCM' r htr Q hq hntH
  rw [moduleDepth_eq_of_linearEquiv J.toLinearEquiv]
  show _ ≤ moduleDepth (X.left.presheaf.stalk x) T
  rwa [hdep, hdim]

/-- **Stacks Project, Tag 0E9V (Lemma 48.21.5), the `(S₂)` clause.** Under the hypotheses of the
tag, the stalk `H^{-r}(f^!𝒪_Y)_x` satisfies `(S₂)` as an `𝒪_{X,x}`-module, for every
compactification `j` defining `f^!`. On a chart the stalk is the localization of
`H^{-r}(ω^•_{A/R})` at the prime of `x`, which is `(S₂)` by the ring-level [Stacks, Tag 0E9R]. -/
@[stacks 0E9V "the (S_2) property of the stalk H^{-r}(f^! O_Y)_x as an O_{X,x}-module"]
theorem propertySkModule_modulesStalk_homology_upperShriek_of_residueTrdeg_le
    (x : X.left) (r : ℕ)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal)) :
    letI := module_finite_modulesStalk_homology_upperShriek f j x (-(r : ℤ))
    PropertySkModule (X.left.presheaf.stalk x) ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.left.Modules (-(r : ℤ))).obj
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj))) 2 := by
  exact (propertySkModule_and_depth_modulesStalk_upperShriek f j x r hCM htrdeg).1

/-- **The depth of `H^{-r}(f^!𝒪_Y)_x` against `dim 𝒪_{X,x}`.** Under the hypotheses of
[Stacks, Tag 0E9V], a nonzero stalk `H^{-r}(f^!𝒪_Y)_x` has depth at least `min(2, dim 𝒪_{X,x})`
over `𝒪_{X,x}`. On a chart this is the ring-level bound
`Dualizing.min_two_ringKrullDim_le_moduleDepth_localizedModule_homology_relativeDualizingComplex`.
-/
theorem min_two_ringKrullDim_le_moduleDepth_modulesStalk_homology_upperShriek
    (x : X.left) (r : ℕ)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal))
    (hnt : Nontrivial ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.left.Modules (-(r : ℤ))).obj
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj)))) :
    min (2 : ℕ∞) ((ringKrullDim (X.left.presheaf.stalk x)).unbotD 0) ≤
      moduleDepth (X.left.presheaf.stalk x) ((modulesStalkFunctor x).obj
        ((DerivedCategory.homologyFunctor X.left.Modules (-(r : ℤ))).obj
          (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj))) := by
  exact (propertySkModule_and_depth_modulesStalk_upperShriek f j x r hCM htrdeg).2 hnt

end Shriek

end Stacks.Duality

end

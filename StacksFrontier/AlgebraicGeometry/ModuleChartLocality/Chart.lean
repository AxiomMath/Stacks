module

public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.ProjShared.MapDomain
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartTranspose

/-!
# Invertibility of the module comparison is decided by the chart comparisons

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings with `ℬ₊ ≤ 𝒜₊.map ψ`, let `𝒨`
be a graded `𝒜`-module, `𝒩` a graded `ℬ`-module and `f : M → N` a `ψ`-semilinear map preserving
the gradings. `Stacks.ProjModuleComparison.moduleMap` is the canonical comparison

`(Proj.map ψ)^* M̃ ⟶ Ñ`.

This file proves that it is an isomorphism as soon as, for every homogeneous `a` of positive
degree, the coefficient extension `ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎ ⟶ N₍ψ a₎` of the algebraic chart
comparison is. It is the module companion of the chain
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartTranspose.lean` and
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean`, which treats the twisting
sheaves, and it is run for an arbitrary graded module.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleChartLocality.chartPushforwardModuleMap` and
  `Stacks.AlgebraicGeometry.ModuleChartLocality.chartAdjointModuleMap`: the chart form of the
  adjoint comparison, and its inverse adjoint transpose along the chart of `Proj 𝒜`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleChartLocality.pullback_awayι_map_moduleMap_eq`: the inverse
  image of the comparison along a chart spectrum of `Proj ℬ` is an inverse adjoint transpose
  along `Spec.map` of the chart ring homomorphism.
* `Stacks.AlgebraicGeometry.ModuleChartLocality.chartΓIso_moduleSpecΓ_chartAdjointModuleMap`:
  **the Γ bridge**: the global sections of that transpose are the algebraic chart comparison
  `Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroMap`.
* `Stacks.AlgebraicGeometry.ModuleChartLocality.isIso_moduleMap_of_isIso_extension`: **the
  comparison is an isomorphism once every coefficient extension of the chart comparison is.**

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.TwistChartLocality
open scoped ChangeOfRings TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ModuleChartLocality

attribute [local instance] instVAddNatIntModuleChart

variable {A B M N : Type u} {σ τ μ ν : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
  (f : M →ₛₗ[ψ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)
  {d : ℕ} (hd : 0 < d) {a : A} (ha : a ∈ 𝒜 d)

/-! ### The chart transpose -/

/-- The morphism out of `M̃` whose inverse adjoint transpose along the composite adjunction of the
chart square's bottom row is the chart inverse image of the module comparison: the explicit
pointwise comparison, followed by the unit of the chart adjunction of `Proj ℬ` and by the three
comparisons of direct images the chart square supplies. -/
public def chartPushforwardModuleMap :
    associatedModuleSheaf 𝒜 𝒨 ⟶
      (pushforward (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).obj
        ((pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ a)))).obj
          ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
            (associatedModuleSheaf ℬ 𝒩))) :=
  (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf ≫
      (pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map
        ((pullbackPushforwardAdjunction
          (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).unit.app
            (associatedModuleSheaf ℬ 𝒩))) ≫
    (pushforwardComp (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)
        (AlgebraicGeometry.Proj.map ψ hψ)).hom.app _ ≫
      (pushforwardCongr (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd a ha)).hom.app _ ≫
        (pushforwardComp (Spec.map (CommRingCat.ofHom (Away.map ψ a)))
            (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).inv.app _

/-- The inverse adjoint transpose, along the chart `AlgebraicGeometry.Proj.awayι 𝒜 a` of the
target, of `Stacks.AlgebraicGeometry.ModuleChartLocality.chartPushforwardModuleMap`. -/
public def chartAdjointModuleMap :
    (pullback (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).obj (associatedModuleSheaf 𝒜 𝒨) ⟶
      (pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ a)))).obj
        ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
          (associatedModuleSheaf ℬ 𝒩)) :=
  ((pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).homEquiv _ _).symm
    (chartPushforwardModuleMap ψ hψ f hf hd ha)

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
/-- **The chart inverse image of the module comparison is an inverse adjoint transpose along
`Spec.map` of the chart ring homomorphism**, preceded by the comparison of the inverse images
along the two factorizations of the chart square's diagonal. -/
public theorem pullback_awayι_map_moduleMap_eq :
    (pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).map
        (Stacks.ProjModuleComparison.moduleMap ψ hψ f hf) =
      (pullbackComp (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)
            (AlgebraicGeometry.Proj.map ψ hψ)).hom.app (associatedModuleSheaf 𝒜 𝒨) ≫
        (pullbackCongr
              (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd a ha)).hom.app
            (associatedModuleSheaf 𝒜 𝒨) ≫
          (pullbackComp (Spec.map (CommRingCat.ofHom (Away.map ψ a)))
                (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).inv.app
              (associatedModuleSheaf 𝒜 𝒨) ≫
            transpose (CommRingCat.ofHom (Away.map ψ a))
              ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).obj
                (associatedModuleSheaf 𝒜 𝒨))
              ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
                (associatedModuleSheaf ℬ 𝒩))
              (chartAdjointModuleMap ψ hψ f hf hd ha) := by
  have h1 : Stacks.ProjModuleComparison.moduleMap ψ hψ f hf =
      ((pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map ψ hψ)).homEquiv
        (associatedModuleSheaf 𝒜 𝒨) (associatedModuleSheaf ℬ 𝒩)).symm
          (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf) :=
    (Equiv.eq_symm_apply _).mpr (Stacks.ProjModuleComparison.homEquiv_moduleMap ψ hψ f hf)
  refine Eq.trans (congrArg (pullback
    (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).map h1) ?_
  refine Eq.trans (map_homEquiv_symm
    (pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map ψ hψ))
    (pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd))
    (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf)) ?_
  refine Eq.trans (Stacks.TransposeFactorization.homEquiv_symm_comp_eq
    (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd) (AlgebraicGeometry.Proj.map ψ hψ)
    (Spec.map (CommRingCat.ofHom (Away.map ψ a))) (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)
    (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd a ha) (associatedModuleSheaf 𝒜 𝒨) _ _) ?_
  refine congrArg _ ?_
  refine congrArg _ ?_
  refine congrArg _ ?_
  exact CategoryTheory.Adjunction.comp_homEquiv_symm_apply
    (pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd))
    (pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom (Away.map ψ a)))) _ _ _

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
/-- **The chart form of the invertibility question for the module comparison.** -/
public theorem isIso_pullback_awayι_map_moduleMap_iff :
    IsIso ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).map
        (Stacks.ProjModuleComparison.moduleMap ψ hψ f hf)) ↔
      IsIso (transpose (CommRingCat.ofHom (Away.map ψ a))
        ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).obj (associatedModuleSheaf 𝒜 𝒨))
        ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
          (associatedModuleSheaf ℬ 𝒩))
        (chartAdjointModuleMap ψ hψ f hf hd ha)) := by
  have := NatIso.isIso_app_of_isIso (pullbackComp
    (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)
    (AlgebraicGeometry.Proj.map ψ hψ)).hom (associatedModuleSheaf 𝒜 𝒨)
  have := NatIso.isIso_app_of_isIso (pullbackCongr
    (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd a ha)).hom (associatedModuleSheaf 𝒜 𝒨)
  have := NatIso.isIso_app_of_isIso (pullbackComp
    (Spec.map (CommRingCat.ofHom (Away.map ψ a)))
    (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).inv (associatedModuleSheaf 𝒜 𝒨)
  rw [pullback_awayι_map_moduleMap_eq ψ hψ f hf hd ha]
  simp only [isIso_comp_left_iff]

/-! ### The chart sections of the transpose -/

/-- **The fibre comparison is the algebraic map, on the whole localized module.** Pushing an
element of `M[1/a]` into the fibre at the point below and comparing is applying `f` to a
numerator and `ψ` to a denominator and then pushing into the fibre. -/
public theorem fibreMap_moduleToFiber {a : A}
    (y : ↥((ProjectiveSpectrum.basicOpen 𝒜 a).comap (ProjectiveSpectrum.comap ψ hψ)))
    (hy : y.1 ∈ ProjectiveSpectrum.basicOpen ℬ (ψ a))
    (w : LocalizedModule.Away (R := A) a M) :
    Stacks.ProjModuleComparison.fibreMap ψ hψ f y.1
        (moduleToFiber (M := M) 𝒜 a ⟨ProjectiveSpectrum.comapFun ψ hψ y.1, y.2⟩ w) =
      moduleToFiber (M := N) ℬ (ψ a) ⟨y.1, hy⟩ (moduleAwayMap ψ f a w) := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    rw [moduleToFiber_mk, Stacks.ProjModuleComparison.fibreMap_mk, moduleAwayMap_mk,
      moduleToFiber_mk]
    rfl

/-- **The explicit pointwise comparison carries the section attached to an element of `M₍a₎` to
the section attached to its image.** -/
public theorem pushforwardModuleMap_degreeZeroToSection {a : A}
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    Scheme.Modules.Hom.app (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf)
        (AlgebraicGeometry.Proj.basicOpen 𝒜 a) (degreeZeroToSection 𝒜 𝒨 a z) =
      degreeZeroToSection ℬ 𝒩 (ψ a) (moduleDegreeZeroMap ψ f hf a z) :=
  Subtype.ext (funext fun y => fibreMap_moduleToFiber ψ hψ f y y.2 z.1)

/-- **The explicit pointwise comparison is the algebraic map, in degree-zero coordinates.** -/
public theorem standardOpenEquiv_pushforwardModuleMap
    (x : (associatedModuleSheaf 𝒜 𝒨).val.obj (.op (ProjectiveSpectrum.basicOpen 𝒜 a))) :
    associatedModuleSheafStandardOpenEquiv ℬ 𝒩 (ψ.map_mem ha) hd
        (Scheme.Modules.Hom.app (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 a) x) =
      moduleDegreeZeroMap ψ f hf a (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 ha hd x) := by
  obtain ⟨z, rfl⟩ := degreeZeroToSection_surjective 𝒜 𝒨 ha hd x
  rw [pushforwardModuleMap_degreeZeroToSection ψ hψ f hf z,
    associatedModuleSheafStandardOpenEquiv_degreeZeroToSection]
  exact associatedModuleSheafStandardOpenEquiv_degreeZeroToSection ℬ 𝒩 (ψ.map_mem ha) hd _

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
/-- The morphism the chart square's composite adjunction transposes, on sections over `D₊(a)`:
the explicit pointwise comparison followed by the unit of the chart adjunction of `Proj ℬ`. -/
public theorem chartPushforwardModuleMap_app
    (w : Γ((show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨),
      AlgebraicGeometry.Proj.basicOpen 𝒜 a)) :
    Scheme.Modules.Hom.app (chartPushforwardModuleMap ψ hψ f hf hd ha)
        (AlgebraicGeometry.Proj.basicOpen 𝒜 a) w =
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
            (associatedModuleSheaf ℬ 𝒩)).presheaf.map
          (eqToHom (awayι_comp_map_preimage 𝒜 ℬ ψ hψ hd ha)).op
        (Scheme.Modules.Hom.app
          ((pullbackPushforwardAdjunction
              (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).unit.app
            (associatedModuleSheaf ℬ 𝒩))
            (AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 a)
          (Scheme.Modules.Hom.app (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf)
            (AlgebraicGeometry.Proj.basicOpen 𝒜 a) w)) :=
  rfl

omit [DirectSum.Decomposition 𝒨] in
/-- **The chart sections of the morphism the chart square's composite adjunction transposes**:
the explicit pointwise comparison on sections over `D₊(a)`. -/
public theorem chartΓIso_chartPushforwardModuleMap
    (x : Γ((show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨),
      AlgebraicGeometry.Proj.basicOpen 𝒜 a)) :
    (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).hom
        (((pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ a)))).obj
              ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
                (associatedModuleSheaf ℬ 𝒩))).presheaf.map
            (eqToHom (awayι_preimage_basicOpen_self 𝒜 ha hd).symm).op
          (Scheme.Modules.Hom.app (chartPushforwardModuleMap ψ hψ f hf hd ha)
            (AlgebraicGeometry.Proj.basicOpen 𝒜 a) x)) =
      associatedModuleSheafStandardOpenEquiv ℬ 𝒩 (ψ.map_mem ha) hd
        (Scheme.Modules.Hom.app (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 a) x) := by
  refine Eq.trans (chartΓIso_hom_apply ℬ 𝒩 (ψ.map_mem ha) hd _) ?_
  refine congrArg _ ?_
  exact collapse_unit_apply (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)
    (associatedModuleSheaf ℬ 𝒩) (AlgebraicGeometry.Proj.basicOpen ℬ (ψ a))
    (awayι_image_top ℬ (ψ.map_mem ha) hd)
    ((Spec.map (CommRingCat.ofHom (Away.map ψ a)) ≫
        AlgebraicGeometry.Proj.awayι 𝒜 a ha hd) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 a)
    (eqToHom (awayι_comp_map_preimage 𝒜 ℬ ψ hψ hd ha))
    (homOfLE (le_of_eq (comp_preimage_basicOpen_self 𝒜 ℬ ψ hd ha).symm))
    (Scheme.Modules.Hom.app (Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ f hf)
      (AlgebraicGeometry.Proj.basicOpen 𝒜 a) x)

/-- **THE Γ BRIDGE.** The global sections of
`Stacks.AlgebraicGeometry.ModuleChartLocality.chartAdjointModuleMap`, read through the chart
identifications of its source and target, are the algebraic chart comparison
`Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroMap`. -/
public theorem chartΓIso_moduleSpecΓ_chartAdjointModuleMap
    (y : (moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).obj
      ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).obj (associatedModuleSheaf 𝒜 𝒨))) :
    (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).hom
        ((moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).map
          (chartAdjointModuleMap ψ hψ f hf hd ha) y) =
      moduleDegreeZeroMap ψ f hf a ((chartΓIso 𝒜 𝒨 ha hd).hom y) := by
  have hg := homEquiv_symm_eq_restrict (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)
    (associatedModuleSheaf 𝒜 𝒨)
    ((pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ a)))).obj
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
        (associatedModuleSheaf ℬ 𝒩)))
    (chartPushforwardModuleMap ψ hψ f hf hd ha)
  have hinv : ∀ v, (imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)
      (show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨) ⊤
      (AlgebraicGeometry.Proj.basicOpen 𝒜 a) (awayι_image_top 𝒜 ha hd)).inv
      ((imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)
        (show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨) ⊤
        (AlgebraicGeometry.Proj.basicOpen 𝒜 a) (awayι_image_top 𝒜 ha hd)).hom v) = v := by
    intro v
    exact Iso.hom_inv_id_apply _ v
  refine Eq.trans (congrArg (ConcreteCategory.hom (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).hom)
    (congrArg (fun m => ConcreteCategory.hom (Scheme.Modules.Hom.app m ⊤) y) hg)) ?_
  refine Eq.trans (congrArg (fun w => ConcreteCategory.hom
      (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).hom
      (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (((restrictAdjunction (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).homEquiv _ _).symm
          (chartPushforwardModuleMap ψ hψ f hf hd ha)) ⊤) w))
    (hinv (ConcreteCategory.hom (Scheme.Modules.Hom.app
      ((restrictFunctorIsoPullback (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).inv.app
        (associatedModuleSheaf 𝒜 𝒨)) ⊤) y)).symm) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).hom)
    (restrictTranspose_app (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd) (associatedModuleSheaf 𝒜 𝒨)
      _ (chartPushforwardModuleMap ψ hψ f hf hd ha) ⊤
      (AlgebraicGeometry.Proj.basicOpen 𝒜 a) (awayι_image_top 𝒜 ha hd)
      (awayι_preimage_basicOpen_self 𝒜 ha hd) _)) ?_
  refine Eq.trans (chartΓIso_chartPushforwardModuleMap ψ hψ f hf hd ha _) ?_
  refine Eq.trans (standardOpenEquiv_pushforwardModuleMap ψ hψ f hf hd ha _) ?_
  exact congrArg _ (chartΓIso_hom_apply 𝒜 𝒨 ha hd y).symm

/-! ### Invertibility -/

/-- The inverse image of the sheaf attached to a graded module along a chart spectrum is
quasi-coherent. -/
public theorem isQuasicoherent_pullback_awayι_associatedModuleSheaf {R P : Type u} {ρ π : Type u}
    [CommRing R] [AddCommGroup P] [Module R P] [SetLike ρ R] [AddSubgroupClass ρ R]
    (ℛ : ℕ → ρ) [GradedRing ℛ] [SetLike π P] [AddSubgroupClass π P] (𝒬 : ℤ → π)
    [DirectSum.Decomposition 𝒬] [SetLike.GradedSMul ℛ 𝒬] {e : ℕ} (he : 0 < e) {b : R}
    (hb : b ∈ ℛ e) :
    ((pullback (AlgebraicGeometry.Proj.awayι ℛ b hb he)).obj
      (show (AlgebraicGeometry.Proj ℛ).Modules from
        associatedModuleSheaf ℛ 𝒬)).IsQuasicoherent := by
  have hqc : (show (AlgebraicGeometry.Proj ℛ).Modules from
      associatedModuleSheaf ℛ 𝒬).IsQuasicoherent :=
    ProjectiveSpectrum.Proj.associatedModuleSheaf_isQuasicoherent ℛ 𝒬
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion _ _

/-- **The chart transpose of the module comparison is invertible as soon as the coefficient
extension of the algebraic chart comparison is.** -/
public theorem isIso_transpose_chartAdjointModuleMap_of_isIso_extension
    (hext : IsIso (moduleDegreeZeroExtension ψ f hf a)) :
    IsIso (transpose (CommRingCat.ofHom (Away.map ψ a))
      ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 a ha hd)).obj (associatedModuleSheaf 𝒜 𝒨))
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).obj
        (associatedModuleSheaf ℬ 𝒩))
      (chartAdjointModuleMap ψ hψ f hf hd ha)) := by
  have := isQuasicoherent_pullback_awayι_associatedModuleSheaf 𝒜 𝒨 hd ha
  have := isQuasicoherent_pullback_awayι_associatedModuleSheaf ℬ 𝒩 hd (ψ.map_mem ha)
  have hinv : ∀ v, (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).inv
      ((chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).hom v) = v := by
    intro v
    exact Iso.hom_inv_id_apply _ v
  refine isIso_transpose_of_isIso_extension _ _ _ _
    ((ModuleCat.extendScalars (Away.map ψ a)).map (chartΓIso 𝒜 𝒨 ha hd).hom ≫
      moduleDegreeZeroExtension ψ f hf a ≫ (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).inv) ?_
  intro m
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).inv)
    (moduleDegreeZeroExtension_tmul ψ f hf a _)) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom (chartΓIso ℬ 𝒩 (ψ.map_mem ha) hd).inv)
    (chartΓIso_moduleSpecΓ_chartAdjointModuleMap ψ hψ f hf hd ha m).symm) ?_
  exact hinv _

/-- **The chart inverse image of the module comparison is invertible** at a homogeneous element of
positive degree whose coefficient extension is invertible. -/
public theorem isIso_pullback_awayι_map_moduleMap_of_isIso_extension
    (hext : IsIso (moduleDegreeZeroExtension ψ f hf a)) :
    IsIso ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ a) (ψ.map_mem ha) hd)).map
      (Stacks.ProjModuleComparison.moduleMap ψ hψ f hf)) :=
  (isIso_pullback_awayι_map_moduleMap_iff ψ hψ f hf hd ha).mpr
    (isIso_transpose_chartAdjointModuleMap_of_isIso_extension ψ hψ f hf hd ha hext)

omit hd ha in
/-- **The module comparison `(Proj.map ψ)^* M̃ ⟶ Ñ` is an isomorphism as soon as, at every
homogeneous element `a` of positive degree, the coefficient extension
`ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎ ⟶ N₍ψ a₎` of the algebraic chart comparison is.**

The domain of definition of `ψ` is all of `Proj ℬ` because `ℬ₊ ≤ 𝒜₊.map ψ`, so the charts
`D₊(ψ a)` cover `Proj ℬ`, and on each of them the comparison is the transpose whose global
sections are the coefficient extension. -/
public theorem isIso_moduleMap_of_isIso_extension
    (hext : ∀ (e : ℕ) (_ : 0 < e) (b : A) (_ : b ∈ 𝒜 e),
      IsIso (moduleDegreeZeroExtension ψ f hf b)) :
    IsIso (Stacks.ProjModuleComparison.moduleMap ψ hψ f hf) :=
  isIso_of_isIso_pullback_awayι_of_mapDomain_eq_top 𝒜 ℬ ψ
    (Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map 𝒜 ℬ ψ hψ) _
    fun e he b hb =>
      isIso_pullback_awayι_map_moduleMap_of_isIso_extension ψ hψ f hf he hb (hext e he b hb)

end Stacks.AlgebraicGeometry.ModuleChartLocality

end

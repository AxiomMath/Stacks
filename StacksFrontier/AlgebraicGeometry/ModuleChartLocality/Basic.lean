module

public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Comparison

/-!
# The module comparison over a standard chart, in degree-zero localizations

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, let `𝒨` be a graded module
over `𝒜`, `𝒩` a graded module over `ℬ`, and let `f : M → N` be a `ψ`-semilinear map carrying
`𝒨 i` into `𝒩 i`. For `a ∈ A` this file builds the algebraic chart comparison

`M₍a₎ ⟶ N₍ψ a₎`,  `m / a ^ k ↦ f m / (ψ a) ^ k`,

between the degree-zero localizations, together with its coefficient extension

`ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎ ⟶ N₍ψ a₎`.

These are the module companions of `Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap`,
`twistDegreeZeroMap` and `twistDegreeZeroExtension`, which are the case of a twist of the ring
itself.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleChartLocality.awayDenom`: the denominators `a ^ k` go to the
  denominators `(ψ a) ^ k`.
* `Stacks.AlgebraicGeometry.ModuleChartLocality.moduleAwayMap`: the map `M[1/a] ⟶ N[1/ψ a]`.
* `Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroMap`: **the algebraic chart
  comparison** `M₍a₎ ⟶ N₍ψ a₎`.
* `Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroExtension`: its coefficient
  extension, a morphism of modules over `ℬ₍ψ a₎`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroMap_smul`: the chart comparison
  is semilinear over `HomogeneousLocalization.Away.map ψ a`.
* `Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroExtension_tmul`: the coefficient
  extension sends `1 ⊗ z` to the image of `z`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped ChangeOfRings TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ModuleChartLocality

/-- Degrees of a graded ring act on degrees of a graded module over it by addition. -/
local instance instVAddNatIntModuleChart : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-- The degree-zero localization acts on the localized module through the ordinary localization;
this is the module structure the degree-zero part `GradedModuleDegreeZeroLocalization` is a
submodule for. -/
local instance awayModule {R P : Type u} {ρ : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    [SetLike ρ R] [AddSubgroupClass ρ R] (ℛ : ℕ → ρ) [GradedRing ℛ] (a : R) :
    Module (Away ℛ a) (LocalizedModule.Away (R := R) a P) :=
  Module.compHom _ (algebraMap (Away ℛ a) (Localization.Away a))

variable {A B M N : Type u} {σ τ μ ν : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩]
  (ψ : 𝒜 →+*ᵍ ℬ) (f : M →ₛₗ[ψ.toRingHom] N)

/-- The denominators: a power of `a` goes to the same power of `ψ a`. -/
public def awayDenom (a : A) : Submonoid.powers a →* Submonoid.powers (ψ a) where
  toFun s := ⟨ψ (s : A), by
    obtain ⟨k, hk⟩ := s.2
    exact ⟨k, by rw [← hk, map_pow]⟩⟩
  map_one' := Subtype.ext (map_one ψ)
  map_mul' _ _ := Subtype.ext (map_mul ψ _ _)

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The image of `s` under `awayDenom ψ a`, viewed as an element of `B`, is `ψ s`. -/
@[simp] public theorem coe_awayDenom (a : A) (s : Submonoid.powers a) :
    (awayDenom ψ a s : B) = ψ (s : A) := rfl

/-- **The map `M[1/a] ⟶ N[1/ψ a]` induced by `f`**: the fraction `m / s` goes to
`f m / ψ s`. -/
public def moduleAwayMap (a : A) :
    LocalizedModule.Away a M →+ LocalizedModule.Away (ψ a) N where
  toFun z := LocalizedModule.liftOn z
    (fun p => LocalizedModule.mk (f p.1) (awayDenom ψ a p.2)) (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨w, hw⟩
      refine LocalizedModule.mk_eq.mpr ⟨awayDenom ψ a w, ?_⟩
      simpa only [Submonoid.smul_def, coe_awayDenom, map_smulₛₗ,
        GradedRingHom.coe_toRingHom] using congrArg f hw)
  map_zero' := by
    rw [← LocalizedModule.zero_mk (1 : Submonoid.powers a)]
    rw [LocalizedModule.liftOn_mk, map_zero, LocalizedModule.zero_mk]
  map_add' z z' := by
    induction z, z' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk]
      rw [LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk,
        LocalizedModule.mk_add_mk]
      refine congrArg₂ LocalizedModule.mk ?_ (map_mul (awayDenom ψ a) s s')
      simp only [Submonoid.smul_def, coe_awayDenom, map_add, map_smulₛₗ,
        GradedRingHom.coe_toRingHom]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The induced map on a fraction: apply `f` to the numerator and `ψ` to the denominator. -/
@[simp] public theorem moduleAwayMap_mk (a : A) (m : M) (s : Submonoid.powers a) :
    moduleAwayMap ψ f a (LocalizedModule.mk m s) =
      LocalizedModule.mk (f m) (awayDenom ψ a s) :=
  rfl

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
  /-- The induced map sends `m / a ^ k` to `f m / (ψ a) ^ k`. -/
  private theorem moduleAwayMap_mk_pow (a : A) (k : ℕ) (m : M) :
    moduleAwayMap ψ f a (LocalizedModule.mk m (⟨a ^ k, k, rfl⟩ : Submonoid.powers a)) =
      LocalizedModule.mk (f m) (⟨ψ a ^ k, k, rfl⟩ : Submonoid.powers (ψ a)) :=
  congrArg (LocalizedModule.mk (f m)) (Subtype.ext (map_pow ψ a k))

/-- **The induced map is semilinear over `HomogeneousLocalization.Away.map`**, the degree-zero
ring acting on a localized module through `HomogeneousLocalization.val`. -/
public theorem moduleAwayMap_smul_val (a : A) (r : Away 𝒜 a) (z : LocalizedModule.Away a M) :
    moduleAwayMap ψ f a (r.val • z) =
      (HomogeneousLocalization.Away.map ψ a r).val • moduleAwayMap ψ f a z := by
  rw [Stacks.AlgebraicGeometry.TwistChartLocality.val_awayLocMap 𝒜 ℬ ψ a r]
  generalize r.val = q
  induction q using Localization.induction_on with
  | H p =>
    obtain ⟨x, t⟩ := p
    induction z using LocalizedModule.induction_on with
    | h m s =>
      rw [Stacks.AlgebraicGeometry.TwistChartLocality.awayLocMap_mk 𝒜 ℬ ψ a x t
          (awayDenom ψ a t).2]
      refine Eq.trans ?_ (LocalizedModule.mk_smul_mk (ψ x) (f m) (awayDenom ψ a t)
        (awayDenom ψ a s)).symm
      rw [LocalizedModule.mk_smul_mk, moduleAwayMap_mk, map_smulₛₗ, map_mul]
      rfl

variable (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)

include hf in
/-- **The induced map carries `M₍a₎` into `N₍ψ a₎`.** The degree-zero part is spanned by the
fractions `x / a ^ k` with `x` homogeneous of degree `k · deg a`, and such a fraction goes to
`f x / (ψ a) ^ k` with `f x` homogeneous of the same degree. -/
public theorem moduleAwayMap_mem (a : A) {z : LocalizedModule.Away (R := A) a M}
    (hz : z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    moduleAwayMap ψ f a z ∈ GradedModuleDegreeZeroLocalization ℬ 𝒩 (ψ a) := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨e, k, hae, x, hx, rfl⟩ := hw
      rw [moduleAwayMap_mk_pow]
      exact Submodule.subset_span ⟨e, k, ψ.map_mem hae, f x, hf _ hx, rfl⟩
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add z₁ z₂ _ _ h₁ h₂ => simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  | smul r z₁ _ h₁ =>
      change moduleAwayMap ψ f a (r.val • z₁) ∈ _
      rw [moduleAwayMap_smul_val]
      exact Submodule.smul_mem _ (HomogeneousLocalization.Away.map ψ a r) h₁

/-- **The algebraic chart comparison `M₍a₎ ⟶ N₍ψ a₎`**: apply `f` to a numerator and `ψ` to a
denominator. It is semilinear over `HomogeneousLocalization.Away.map ψ a` by
`moduleDegreeZeroMap_smul`. -/
public def moduleDegreeZeroMap (a : A) :
    GradedModuleDegreeZeroLocalization 𝒜 𝒨 a →+
      GradedModuleDegreeZeroLocalization ℬ 𝒩 (ψ a) where
  toFun z := ⟨moduleAwayMap ψ f a z.1, moduleAwayMap_mem ψ f hf a z.2⟩
  map_zero' := Subtype.ext (map_zero (moduleAwayMap ψ f a))
  map_add' z z' := Subtype.ext (map_add (moduleAwayMap ψ f a) z.1 z'.1)

/-- The chart comparison, on the underlying localized modules. -/
public theorem moduleDegreeZeroMap_val (a : A)
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    (moduleDegreeZeroMap ψ f hf a z).1 = moduleAwayMap ψ f a z.1 := rfl

/-- The chart comparison is semilinear over the ring homomorphism `𝒜₍a₎ ⟶ ℬ₍ψ a₎`. -/
public theorem moduleDegreeZeroMap_smul (a : A) (r : Away 𝒜 a)
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    moduleDegreeZeroMap ψ f hf a (r • z) =
      HomogeneousLocalization.Away.map ψ a r • moduleDegreeZeroMap ψ f hf a z :=
  Subtype.ext (moduleAwayMap_smul_val ψ f a r z.1)

/-- **The chart comparison on a homogeneous fraction**: `m / a ^ k` goes to
`f m / (ψ a) ^ k`. -/
public theorem moduleDegreeZeroMap_degreeZeroFraction {a : A} {d : ℕ} (ha : a ∈ 𝒜 d) (k : ℕ)
    (m : M) (hm : m ∈ 𝒨 (k • (d : ℤ))) :
    moduleDegreeZeroMap ψ f hf a (degreeZeroFraction 𝒜 𝒨 ha k m hm) =
      degreeZeroFraction ℬ 𝒩 (ψ.map_mem ha) k (f m) (hf _ hm) := by
  exact Subtype.ext (moduleAwayMap_mk_pow ψ f a k m)

/-- The chart comparison as a semilinear map: a morphism into the restriction of scalars of its
target along the chart ring homomorphism. -/
public def moduleDegreeZeroSemilinear (a : A) :
    ModuleCat.of (Away 𝒜 a) (GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) ⟶
      (ModuleCat.restrictScalars (Away.map ψ a)).obj
        (ModuleCat.of (Away ℬ (ψ a)) (GradedModuleDegreeZeroLocalization ℬ 𝒩 (ψ a))) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (Away.map ψ a)).obj
      (ModuleCat.of (Away ℬ (ψ a)) (GradedModuleDegreeZeroLocalization ℬ 𝒩 (ψ a))))
    { toFun := moduleDegreeZeroMap ψ f hf a
      map_add' := fun z z' => map_add (moduleDegreeZeroMap ψ f hf a) z z'
      map_smul' := moduleDegreeZeroMap_smul ψ f hf a }

/-- **The coefficient extension of the chart comparison**,
`ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎ ⟶ N₍ψ a₎`: the extension of scalars of the semilinear chart comparison
followed by the counit. -/
public def moduleDegreeZeroExtension (a : A) :
    (ModuleCat.extendScalars (Away.map ψ a)).obj
        (ModuleCat.of (Away 𝒜 a) (GradedModuleDegreeZeroLocalization 𝒜 𝒨 a)) ⟶
      ModuleCat.of (Away ℬ (ψ a)) (GradedModuleDegreeZeroLocalization ℬ 𝒩 (ψ a)) :=
  (ModuleCat.extendScalars (Away.map ψ a)).map (moduleDegreeZeroSemilinear ψ f hf a) ≫
    (ModuleCat.extendRestrictScalarsAdj (Away.map ψ a)).counit.app
      (ModuleCat.of (Away ℬ (ψ a)) (GradedModuleDegreeZeroLocalization ℬ 𝒩 (ψ a)))

/-- **The coefficient extension on a pure tensor**: `1 ⊗ z` goes to the image of `z`. -/
public theorem moduleDegreeZeroExtension_tmul (a : A)
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    moduleDegreeZeroExtension ψ f hf a ((1 : Away ℬ (ψ a)) ⊗ₜ[Away 𝒜 a, Away.map ψ a] z) =
      moduleDegreeZeroMap ψ f hf a z := by
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul (f := Away.map ψ a)
    (ModuleCat.of (Away ℬ (ψ a)) (GradedModuleDegreeZeroLocalization ℬ 𝒩 (ψ a)))
    (moduleDegreeZeroMap ψ f hf a z)

end Stacks.AlgebraicGeometry.ModuleChartLocality

end

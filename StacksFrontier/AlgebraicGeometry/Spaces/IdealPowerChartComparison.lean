module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.IdealSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections

/-!
# The sections of `ℐᵏ𝒢` over a general open of a chart's scheme

Let `F` be an algebraic space, let `ℐ ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals and `𝒢` a
quasi-coherent `𝒪_F`-module. This file describes the sections of `ℐᵏ𝒢` over a general open of a
chart's scheme in terms of the sections of `ℐᵏ𝒢` over the affine étale charts that the affine
opens inside it cut out.

A section of a module `F` on a scheme over an arbitrary open `U` lies in `I ^ n • F` exactly when
its restriction to every affine open `W` contained in `U` lies in `I(W) ^ n • Γ(F, W)`. Over an
affine open, the sections on the chart's scheme and on the space are related by an additive
comparison that is semilinear over a surjective ring map, and membership in `J ^ k • ⊤` descends
along such a comparison.

## Main definitions

* `Stacks.Submodule.mapSemilinear`: the image of a submodule under a semilinear additive
  isomorphism, as a submodule over the target ring.

## Main results

* `Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top`: membership in `J ^ k • ⊤`
  descends along a semilinear additive isomorphism over a surjective ring map.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.mem_obj_idealPowSmul_iff` and
  `Stacks.AlgebraicGeometry.IdealPowerSmul.mem_obj_idealPowSmul_of_forall_affineOpens`: a section
  of `F` over an arbitrary open lies in `I ^ n • F` exactly when its restriction to every affine
  open `W` inside it lies in `I(W) ^ n • Γ(F, W)`.
* `AlgebraicGeometry.Space.mem_pow_ideal_smul_top_of_mem_chartSubmodule`: a section whose
  comparison lies in the sections of `ℐᵏ𝒢` over an affine étale chart lies in `J ^ k • ⊤`, for
  any ideal `J` carried by the comparison onto the ideal of sections of `ℐ` over that chart.
* `AlgebraicGeometry.Space.mem_obj_idealPowSmul_of_forall_chart`: a section of a module on a
  chart's scheme over a general open lies in `I ^ k • ·` as soon as, over every affine open inside
  it, its comparison lies in the sections of `ℐᵏ𝒢` over the étale chart that affine open cuts
  out.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u m

namespace Stacks.Submodule

variable {R R' : Type*} [CommRing R] [CommRing R'] {M M' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']

/-- The image of an `R`-submodule of `M` under an additive isomorphism `e : M ≃+ M'` that is
semilinear over a surjective ring map `g : R →+* R'`, as an `R'`-submodule of `M'`. -/
def mapSemilinear (g : R →+* R') (hg : Function.Surjective g) (e : M ≃+ M')
    (he : ∀ (r : R) (x : M), e (r • x) = g r • e x) (N : Submodule R M) : Submodule R' M' where
  carrier := e '' (N : Set M)
  add_mem' := by
    rintro - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, N.add_mem ha hb, map_add e a b⟩
  zero_mem' := ⟨0, N.zero_mem, map_zero e⟩
  smul_mem' := by
    rintro c - ⟨a, ha, rfl⟩
    obtain ⟨r, rfl⟩ := hg c
    exact ⟨r • a, N.smul_mem r ha, he r a⟩

/-- If `e : M ≃+ M'` is semilinear over a surjective ring map `g : R →+* R'` and `e x` lies in
`(J.map g) ^ k • ⊤`, then `x` lies in `J ^ k • ⊤`. -/
theorem mem_pow_smul_top_of_mem_map_pow_smul_top (g : R →+* R') (hg : Function.Surjective g)
    (e : M ≃+ M') (he : ∀ (r : R) (x : M), e (r • x) = g r • e x) (J : Ideal R) (k : ℕ)
    {x : M} (hx : e x ∈ (J.map g) ^ k • (⊤ : Submodule R' M')) :
    x ∈ J ^ k • (⊤ : Submodule R M) := by
  have hle : (J.map g) ^ k • (⊤ : Submodule R' M') ≤
      mapSemilinear g hg e he (J ^ k • (⊤ : Submodule R M)) := by
    refine Submodule.smul_le.2 fun r hr y _ => ?_
    rw [← Ideal.map_pow] at hr
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective g hg).1 hr
    refine ⟨b • e.symm y, Submodule.smul_mem_smul hb Submodule.mem_top, ?_⟩
    rw [he b (e.symm y), e.apply_symm_apply]
  obtain ⟨z, hz, hez⟩ := hle hx
  rwa [e.injective hez] at hz

end Stacks.Submodule

namespace Stacks.AlgebraicGeometry.IdealPowerSmul

variable {T : Scheme.{u}}

/-! ### Membership in `I ^ n • F` at a general open -/

/-- A section of `F` over an arbitrary open `U` lies in `I ^ n • F` exactly when its restriction
to every affine open `W` inside `U` lies in `I(W) ^ n · Γ(F, W)`. -/
theorem mem_obj_idealPowSmul_iff (I : T.IdealSheafData) (n : ℕ) (F : T.Modules)
    [F.IsQuasicoherent] {U : T.Opens} (s : Γ(F, U)) :
    s ∈ (idealPowSmul I n F).toSubmodule.obj (op U) ↔
      ∀ (W : T.affineOpens) (h : W.1 ≤ U),
        F.presheaf.map (homOfLE h).op s
          ∈ I.ideal W ^ n • (⊤ : Submodule Γ(T, W.1) Γ(F, W.1)) := Iff.rfl

/-- A section over `U` whose restriction to every affine open `W` inside `U` lies in
`I(W) ^ n · Γ(F, W)` is a section of `I ^ n • F` over `U`. -/
theorem mem_obj_idealPowSmul_of_forall_affineOpens (I : T.IdealSheafData) (n : ℕ) (F : T.Modules)
    [F.IsQuasicoherent] {U : T.Opens} {s : Γ(F, U)}
    (h : ∀ (W : T.affineOpens) (hW : W.1 ≤ U),
      F.presheaf.map (homOfLE hW).op s
        ∈ I.ideal W ^ n • (⊤ : Submodule Γ(T, W.1) Γ(F, W.1))) :
    s ∈ (idealPowSmul I n F).toSubmodule.obj (op U) :=
  (mem_obj_idealPowSmul_iff I n F s).2 h

end Stacks.AlgebraicGeometry.IdealPowerSmul

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The transport step at an affine chart -/

/-- A section `x` of a module on a chart's scheme over an open `V` whose comparison lies in the
sections of `ℐᵏ𝒢` over an affine étale chart `P` lies in `J ^ k • ⊤`.

Here `P` is the étale chart which `V` cuts out, `g` is a surjective ring map from the functions on
`V` to the sections of `𝒪_F` over `P`, `e` is an additive comparison of the sections of the
module on `V` with the sections of `𝒢` over `P`, semilinear over `g`, and `J` is an ideal of the
functions on `V` carried by `g` onto the ideal of sections of `ℐ` over `P`. -/
theorem mem_pow_ideal_smul_top_of_mem_chartSubmodule
    (ℐ : IdealSheaves B S hS F hF) (hℐ : ℐ.toSheafOfModules.IsQuasicoherentOnSite)
    (𝒢 : Modules.{u, u} B S hS F hF) (h𝒢 : 𝒢.IsQuasicoherentOnSite) (k : ℕ)
    {T : Scheme.{u}} (Mc : T.Modules) {V : T.Opens}
    (P : SmallEtale B S hS F)
    (hP : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj P))
    (g : Γ(T, V) →+* chartRing B S hS F hF P) (hg : Function.Surjective g)
    (e : Γ(Mc, V) ≃+ 𝒢.val.obj (op P))
    (he : ∀ (r : Γ(T, V)) (y : Γ(Mc, V)), e (r • y) = g r • e y)
    (J : Ideal Γ(T, V)) (hJ : Ideal.map g J = chartSectionIdeal B S hS F hF ℐ P)
    {x : Γ(Mc, V)}
    (hx : e x ∈ chartSubmodule B S hS F hF (idealPowSubmodule ℐ k 𝒢) P) :
    x ∈ J ^ k • (⊤ : Submodule Γ(T, V) Γ(Mc, V)) := by
  refine Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top g hg e he J k ?_
  rwa [hJ, ← chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite B S hS F hF ℐ k 𝒢
    h𝒢 hℐ P hP]

/-! ### The two steps together -/

/-- A section of a module on a chart's scheme over an open `U` lies in `I ^ k • ·` as soon as,
for every affine open `W` inside `U`, its comparison lies in the sections of `ℐᵏ𝒢` over the
affine étale chart that `W` cuts out. The chart data is indexed by the affine opens contained in
`U`. -/
theorem mem_obj_idealPowSmul_of_forall_chart
    (ℐ : IdealSheaves B S hS F hF) (hℐ : ℐ.toSheafOfModules.IsQuasicoherentOnSite)
    (𝒢 : Modules.{u, u} B S hS F hF) (h𝒢 : 𝒢.IsQuasicoherentOnSite) (k : ℕ)
    {T : Scheme.{u}} (I : T.IdealSheafData) (Mc : T.Modules) [Mc.IsQuasicoherent]
    {U : T.Opens} {x : Γ(Mc, U)}
    (P : ∀ W : T.affineOpens, W.1 ≤ U → SmallEtale B S hS F)
    (hP : ∀ (W : T.affineOpens) (hW : W.1 ≤ U),
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (P W hW)))
    (g : ∀ (W : T.affineOpens) (hW : W.1 ≤ U),
      Γ(T, W.1) →+* chartRing B S hS F hF (P W hW))
    (hg : ∀ (W : T.affineOpens) (hW : W.1 ≤ U), Function.Surjective (g W hW))
    (e : ∀ (W : T.affineOpens) (hW : W.1 ≤ U), Γ(Mc, W.1) ≃+ 𝒢.val.obj (op (P W hW)))
    (he : ∀ (W : T.affineOpens) (hW : W.1 ≤ U) (r : Γ(T, W.1)) (y : Γ(Mc, W.1)),
      e W hW (r • y) = g W hW r • e W hW y)
    (hJ : ∀ (W : T.affineOpens) (hW : W.1 ≤ U),
      Ideal.map (g W hW) (I.ideal W) = chartSectionIdeal B S hS F hF ℐ (P W hW))
    (hx : ∀ (W : T.affineOpens) (hW : W.1 ≤ U),
      e W hW (Mc.presheaf.map (homOfLE hW).op x)
        ∈ chartSubmodule B S hS F hF (idealPowSubmodule ℐ k 𝒢) (P W hW)) :
    x ∈ (Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul I k Mc).toSubmodule.obj (op U) :=
  Stacks.AlgebraicGeometry.IdealPowerSmul.mem_obj_idealPowSmul_of_forall_affineOpens I k Mc
    fun W hW => mem_pow_ideal_smul_top_of_mem_chartSubmodule B S hS F hF ℐ hℐ 𝒢 h𝒢 k Mc
      (P W hW) (hP W hW) (g W hW) (hg W hW) (e W hW) (he W hW) (I.ideal W) (hJ W hW) (hx W hW)

end AlgebraicGeometry.Space

end

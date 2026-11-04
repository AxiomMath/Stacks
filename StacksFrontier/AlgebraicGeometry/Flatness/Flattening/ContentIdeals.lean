module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.Basic
public import StacksFrontier.Algebra.Module.ContentIdeal
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LocalizedModuleSpreadout

/-!
# Content ideals from a pure spreadout

In the finitely presented localized-module situation, the existence of a pure spreadout
implies that every element of the localized module has a content ideal over the base ring.

## Main results

* `AlgebraicGeometry.exists_isContentIdeal_of_pureSpreadout` gives a content ideal for each
  element of the localized module.

## Implementation notes

Existence of the pure spreadout is expressed by `Nonempty`. The conclusion uses the existing
predicate `IsContentIdeal` for the underlying module over the base ring.

The argument transports a content ideal along the localization map. Projectivity of the
spreadout module over the base supplies the Mittag-Leffler hypothesis that produces a content
ideal there, after an auxiliary `ULift` to place the module in the universe where
`IsMittagLeffler` is stated; the localization map is universally injective, which is what
makes the content ideal descend, and the denominator acts invertibly, which lets one pass
from a numerator to a general element.

## References

* [Stacks Project, Tag 0AT7](https://stacks.math.columbia.edu/tag/0AT7)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u v

namespace AlgebraicGeometry

open scoped TensorProduct

/-- A content ideal is preserved by a linear map that reflects membership in `J • ⊤`. -/
private lemma isContentIdeal_map_of_reflects {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) {x : M} {I : Ideal A}
    (hf : ∀ J : Ideal A, f x ∈ J • (⊤ : Submodule A N) → x ∈ J • (⊤ : Submodule A M))
    (hx : IsContentIdeal x I) : IsContentIdeal (f x) I :=
  ⟨Submodule.smul_top_le_comap_smul_top I f hx.1, fun J hJ ↦ hx.2 (hf J hJ)⟩

/-- A content ideal is preserved by a linear equivalence. -/
private lemma isContentIdeal_map_equiv {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) {x : M} {I : Ideal A} (hx : IsContentIdeal x I) :
    IsContentIdeal (e x) I :=
  isContentIdeal_map_of_reflects e.toLinearMap
    (fun J hJ ↦ by simpa using Submodule.smul_top_le_comap_smul_top J e.symm.toLinearMap hJ) hx

/-- A universally injective map stays injective after reduction modulo an ideal. -/
private lemma mapQ_injective_of_universallyInjective {A : Type u} [CommRing A]
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N)
    (hf : UniversallyInjectivePoly.{u, u, v, v} f) (I : Ideal A) :
    Function.Injective
      (Submodule.mapQ (I • (⊤ : Submodule A M)) (I • (⊤ : Submodule A N)) f
        (Submodule.smul_top_le_comap_smul_top I f)) := by
  intro x y hxy
  obtain ⟨x₀, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) x
  obtain ⟨y₀, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) y
  apply_fun (fun z => z -
    (Submodule.mapQ (I • (⊤ : Submodule A M)) (I • (⊤ : Submodule A N)) f
      (Submodule.smul_top_le_comap_smul_top I f)
      (Submodule.Quotient.mk y₀))) at hxy
  have hquot : (I • (⊤ : Submodule A N)).mkQ (f (x₀ - y₀)) = 0 := by
    simpa [Submodule.mapQ_apply, map_sub] using hxy
  let eM := TensorProduct.quotTensorEquivQuotSMul M I
  let eN := TensorProduct.quotTensorEquivQuotSMul N I
  let cM := TensorProduct.comm A M (A ⧸ I)
  let cN := TensorProduct.comm A N (A ⧸ I)
  let z : M ⊗[A] (A ⧸ I) := cM.symm (1 ⊗ₜ[A] (x₀ - y₀))
  have hz : f.rTensor (A ⧸ I) z = 0 := by
    apply cN.injective
    have hten : eN (1 ⊗ₜ[A] f (x₀ - y₀)) = 0 := by
      rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
      exact (Submodule.Quotient.mk_eq_zero _).2 ((Submodule.Quotient.mk_eq_zero _).1 hquot)
    simpa [z, cN, cM] using hten
  have hz0 : z = 0 := hf (A ⧸ I) hz
  have hclass : (I • (⊤ : Submodule A M)).mkQ (x₀ - y₀) = 0 := by
    simpa [z, cM, eM, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using
      congrArg eM (congrArg cM hz0)
  exact sub_eq_zero.mp (by simpa [map_sub] using hclass)

/-- A content ideal is preserved by a universally injective map. -/
private lemma isContentIdeal_map_of_universallyInjective {A : Type u} [CommRing A]
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N)
    (hf : UniversallyInjectivePoly.{u, u, v, v} f) {x : M} {I : Ideal A}
    (hx : IsContentIdeal x I) : IsContentIdeal (f x) I := by
  refine isContentIdeal_map_of_reflects f (fun J hJ ↦ ?_) hx
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply mapQ_injective_of_universallyInjective f hf J
  simpa [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] using hJ

/-- Scaling by an element of the localizing submonoid does not change the content ideal. -/
private lemma isContentIdeal_smul_of_localizedUnit
    {A B M₀ M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M₀] [Module B M₀]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (S : Submonoid B) (f : M₀ →ₗ[B] M) [IsLocalizedModule S f]
    (s : S) {x : M} {I : Ideal A} :
    IsContentIdeal x I ↔ IsContentIdeal (s • x) I := by
  let g : Module.End B M := algebraMap B (Module.End B M) (s : B)
  let eB : M ≃ₗ[B] M := LinearEquiv.ofBijective g
    ((Module.End.isUnit_iff g).mp (IsLocalizedModule.map_units f s))
  have he : eB x = s • x := by
    show eB x = (s : B) • x
    simp [eB, g, Module.algebraMap_end_apply]
  exact ⟨fun hx ↦ he ▸ isContentIdeal_map_equiv (eB.restrictScalars A) hx,
    fun hx ↦ by simpa [← he] using isContentIdeal_map_equiv (eB.symm.restrictScalars A) hx⟩

/-- **Stacks Project, Tag 0AT7.** If a pure spreadout exists, every element of the localized
module has a content ideal over the base ring. -/
@[stacks 0AT7 "content_ideals"]
theorem exists_isContentIdeal_of_pureSpreadout
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (hspread : Nonempty (PureSpreadout.{u₁, u₂, u₃, u₄, u₁} X)) (x : X.N) :
    ∃ I : Ideal X.A, IsContentIdeal x I := by
  obtain ⟨D⟩ := hspread
  let := D.commRingC
  let := D.algebraBC
  let := D.algebraAC
  let := D.isScalarTowerABC
  let := D.addCommGroupN'
  let := D.moduleCN'
  let := D.moduleBN'
  let := D.moduleAN'
  let := D.isScalarTowerBCN'
  let := D.isScalarTowerACN'
  let := D.moduleCN
  let := D.isScalarTowerCBₛN
  let := D.isScalarTowerBCN
  let := D.isScalarTowerACN
  let f := D.localizationMap
  have : Module.Projective X.A D.N' := D.projective
  let e : ULift.{u₁} D.N' ≃ₗ[X.A] D.N' := ULift.moduleEquiv
  have : Module.Projective X.A (ULift.{u₁} D.N') := Module.Projective.of_equiv e.symm
  have hML : IsMittagLeffler.{u₁, max u₁ u₄, max u₁ u₄, max u₁ u₄, max u₁ u₄}
      X.A (ULift.{u₁} D.N') :=
    (isMittagLeffler_def_iff X.A (ULift.{u₁} D.N')).2
      (Module.mittagLeffler_of_projective X.A (ULift.{u₁} D.N'))
  have : IsLocalizedModule X.S (f.restrictScalars X.B) := D.isLocalizedModule
  obtain ⟨⟨x', s⟩, hs⟩ := IsLocalizedModule.surj X.S (f.restrictScalars X.B) x
  obtain ⟨I, hI⟩ := exists_isContentIdeal_of_flat_isMittagLeffler hML (ULift.up x')
  have hI' : IsContentIdeal x' I := by
    simpa [e] using isContentIdeal_map_equiv e hI
  refine ⟨I, (isContentIdeal_smul_of_localizedUnit X.S
    (f.restrictScalars X.B) s).mpr ?_⟩
  rw [hs]
  exact isContentIdeal_map_of_universallyInjective (f.restrictScalars X.A)
    D.universallyInjective.{u₁, u₂, u₃, u₄, u₁} hI'

end AlgebraicGeometry

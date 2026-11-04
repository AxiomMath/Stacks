module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineBaseChangeAlong

/-!
# The kernel of the restriction of sections of a crystal along a morphism of `CRIS(X/S)`

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation of [Stacks, Tag 07MF] and let `g : (U', T', δ') ⟶ (U, T, δ)` be a morphism of
`CRIS(X/S)` whose restriction map on the sections of `𝒪_{X/S}`

`Γ(T, 𝒪_T) ⟶ Γ(T', 𝒪_{T'})`

is **surjective with principal kernel `(a)`** — the shape of a level drop
`T(n)_e ⟶ T(n)_{e + 1}` in the cosimplicial system of [Stacks, Proposition 60.20.1, Tag 07JN],
where the two rings are `D(n)/(p)^{N + e}` and `D(n)/(p)^{N + e + 1}` and `a = p^{N + e}`.

For a **crystal** on objects with affine ambient schemes and quasi-coherent `F_T` the sections
over `(U', T', δ')` are the base change of the sections over `(U, T, δ)`, by
`Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMapAlong`.  So the restriction
of sections along `g` is the map

`F(U, T, δ) ⟶ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ)`,  `x ↦ 1 ⊗ x`,

whose kernel is `a · F(U, T, δ)`: that is the right exactness of the tensor product, and is
`TensorProduct.one_tmul_eq_zero_iff_exists_smul` below.

This is the content the source's footnote at [Stacks, Lemma 60.19.3, Tag 07LF] points at — "we
don't know that `M(n)_e = M(n)_{e+1}/p^e M(n)_{e+1}`.  If `ℱ` is a crystal then this does hold"
— and it is the kernel clause of
`Crystalline.GlobalCrystallineSituation.SmallSite.IsCrystalLevelQuotient`, for a sheaf of modules
on the **big** crystalline site, at an arbitrary morphism.

## Main results

* `TensorProduct.one_tmul_eq_zero_iff_exists_smul` — **the kernel of `x ↦ 1 ⊗ x` into a base
  change along a surjective ring homomorphism with principal kernel `(a)` is the subgroup of
  `a`-multiples.**  Stated for the base ring acting through a ring homomorphism carried as a
  variable with a defining equation, which is how the actions of this chapter arrive.
* `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_eq_zero_iff_of_isSheafCrystal` —
  **the kernel clause for a crystal at an arbitrary morphism of `CRIS(X/S)`**: a section over the
  target restricts to zero over the source exactly when it is `a` times a section over the
  target.

## What is and is not proved

**No `@[stacks]` attribute is placed and no tag is proved here.**  The kernel clause is one
hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG], and the statement below is for a sheaf of
modules on `CRIS(X/S)`, while the coefficient sheaf of that proposition is a sheaf of modules on
`Cris(X/S)`.  See the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemFirstOrder.lean` for what
stands between the two sides.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace TensorProduct

/-- **The kernel of `x ↦ 1 ⊗ x` into a base change along a surjective ring homomorphism with
principal kernel is the subgroup of multiples of the generator.**

`f : R ⟶ R'` is surjective and `f b = 0` exactly when `a ∣ b`, so `f` presents `R'` as
`R/(a)`; the base change `R' ⊗_R N` is then `N/(a)N` by
`TensorProduct.quotTensorEquivQuotSMul`, and `1 ⊗ x` is the class of `x`.

The `R`-module structure on `R'` is carried as an instance argument with the defining equation
`hf` rather than as `Module.compHom`: the actions of the crystalline site arrive either as
`RingHom.toAlgebra` of a restriction map or as `Module.compHom` of a map on global sections, and
both satisfy `hf` by `rfl`. -/
theorem one_tmul_eq_zero_iff_exists_smul {R R' N : Type*} [CommRing R] [CommRing R']
    [Module R R'] [AddCommGroup N] [Module R N] (f : R →+* R')
    (hf : ∀ (r : R) (t : R'), r • t = f r * t) (hsurj : Function.Surjective f) (a : R)
    (hker : ∀ b : R, f b = 0 ↔ a ∣ b) (x : N) :
    (1 : R') ⊗ₜ[R] x = 0 ↔ ∃ y : N, x = a • y := by
  set I : Ideal R := Ideal.span {a}
  have hLsmul : ∀ r s : R, f (r • s) = r • f s := fun r s ↦ by rw [hf, smul_eq_mul, map_mul]
  let L : R →ₗ[R] R' := { toFun := f, map_add' := map_add f, map_smul' := hLsmul }
  let Q : (R ⧸ I) →ₗ[R] R' :=
    I.liftQ L ((Ideal.span_singleton_le_iff_mem _).2 ((hker a).2 dvd_rfl))
  have hQbij : Function.Bijective Q := by
    refine ⟨?_, fun t ↦ ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ fun r hr ↦
        Ideal.mem_span_singleton.2 ((hker r).1 (LinearMap.mem_ker.1 hr))
    · obtain ⟨r, rfl⟩ := hsurj t
      exact ⟨Submodule.Quotient.mk r, rfl⟩
  let T := TensorProduct.congr (LinearEquiv.ofBijective Q hQbij) (LinearEquiv.refl R N)
  have key : (1 : R') ⊗ₜ[R] x = T ((1 : R ⧸ I) ⊗ₜ[R] x) := by
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    refine congrArg (fun z ↦ z ⊗ₜ[R] x) ?_
    change (1 : R') = Q 1
    rw [← map_one (Ideal.Quotient.mk I)]
    exact (map_one f).symm
  rw [key, T.map_eq_zero_iff, ← (TensorProduct.quotTensorEquivQuotSMul N I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, _, h⟩ ↦ ⟨y, h.symm⟩, fun ⟨y, h⟩ ↦ ⟨y, Submodule.mem_top, h.symm⟩⟩

end TensorProduct

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A A' : Thickening S} (g : A' ⟶ A)

/-- **The restriction of a section along `g` is the base change `x ↦ 1 ⊗ x`.**  The base change
of sections carries `1 ⊗ x` to `1 · g^* x`. -/
theorem extensionSectionsMapAlong_one_tmul (x : M.val.obj (op A)) :
    extensionSectionsMapAlong M g ((1 : ringAlong g) ⊗ₜ[crysSheafRing S A] x) =
      moduleSiteRestrict M g x := by
  rw [extensionSectionsMapAlong_tmul]
  change (1 : crysSheafRing S A') • moduleSiteRestrict M g x = moduleSiteRestrict M g x
  exact one_smul _ _

section Affine

variable [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent]

/-- **A section over the target restricts to zero over the source exactly when the pure tensor
`1 ⊗ x` vanishes**, for a crystal on a pair of objects with affine ambient schemes and
quasi-coherent `F_T`: the base change of sections is injective and carries `1 ⊗ x` to the
restriction of `x`. -/
theorem moduleSiteRestrict_eq_zero_iff_one_tmul_eq_zero (hM : IsSheafCrystal M)
    (x : M.val.obj (op A)) :
    moduleSiteRestrict M g x = 0 ↔ (1 : ringAlong g) ⊗ₜ[crysSheafRing S A] x = 0 := by
  rw [← extensionSectionsMapAlong_one_tmul M g x]
  exact map_eq_zero_iff _ (bijective_extensionSectionsMapAlong M g hM).1

/-- **The kernel clause of the crystal property at an arbitrary morphism of `CRIS(X/S)`.**

Let `g : (U', T', δ') ⟶ (U, T, δ)` be a morphism whose restriction map on the sections of
`𝒪_{X/S}` is surjective with kernel the principal ideal `(a)`, let the two ambient schemes be
affine and let `F` be a crystal with quasi-coherent `F_T`.  Then a section of `F` over
`(U, T, δ)` restricts to zero over `(U', T', δ')` exactly when it is `a` times a section over
`(U, T, δ)`.

This is the shape in which the distinguishing hypothesis of
[Stacks, Proposition 60.21.3, Tag 07LG] is asked for over the cosimplicial system of
[Stacks, Proposition 60.20.1, Tag 07JN]: there `g` is a level drop `T(n)_e ⟶ T(n)_{e + 1}`, the
two section rings are `D(n)/(p)^{N + e}` and `D(n)/(p)^{N + e + 1}`, and `a = p^{N + e}`.

Both hypotheses on the ring map are genuinely needed and are not available in general: the
restriction map of `𝒪_{X/S}` along an arbitrary morphism of the site is neither surjective nor of
principal kernel.  The crystal hypothesis is what the source's footnote at
[Stacks, Lemma 60.19.3, Tag 07LF] says cannot be dispensed with. -/
theorem moduleSiteRestrict_eq_zero_iff_of_isSheafCrystal (hM : IsSheafCrystal M)
    (hsurj : Function.Surjective (crysSheafRingMap g)) (a : crysSheafRing S A)
    (hker : ∀ b : crysSheafRing S A, crysSheafRingMap g b = 0 ↔ a ∣ b) (x : M.val.obj (op A)) :
    moduleSiteRestrict M g x = 0 ↔ ∃ y, x = a • y := by
  rw [moduleSiteRestrict_eq_zero_iff_one_tmul_eq_zero M g hM x]
  exact TensorProduct.one_tmul_eq_zero_iff_exists_smul (R' := ringAlong g) (crysSheafRingMap g)
    (fun r t ↦ rfl) hsurj a hker x

end Affine

end Crystalline.GlobalCrystallineSituation

end

end

module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.TwistTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Ideal
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalkBasisGenericPoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.StalkIdeal
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelRank

/-!
# The section `T` of the projective completion is a regular section

Let `𝒞` be a finite locally free module on a scheme `X` and `E = Proj_X(Sym^*(𝒞)[T])` the
projective completion of its vector bundle, with twist `𝒪_E(1)` and the global section `T`, the
image of the unit of the summand `𝒪_X` of `𝒞 ⊕ 𝒪_X`. This file proves that multiplication by `T`,
`𝒪_E ⟶ 𝒪_E(1)`, is a monomorphism: `T` is a regular section, so its zero scheme is an effective
Cartier divisor (Stacks 0847), the hyperplane at infinity of the proof of Stacks 0ERW.

## Main results

* `Stacks.Chow.ProjectiveCompletion.notMem_supportSet_zeroSchemeOfSection_sectionT`: the section
  `(0, 1)` of `𝒞 ⊕ 𝒪_X` vanishes nowhere.
* `Stacks.Chow.ProjectiveCompletion.injective_smul_germ_coordT`: multiplication by the germ of
  `T` on the local rings of `E` is injective.
* `Stacks.Chow.ProjectiveCompletion.mono_mulT`: **multiplication by `T` is a monomorphism**.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped nonZeroDivisors

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

/-- The section `(0, 1)` of `𝒞 ⊕ 𝒪_X` vanishes nowhere. -/
theorem notMem_supportSet_zeroSchemeOfSection_sectionT (x : X) :
    x ∉ (zeroSchemeOfSection X (module 𝒞) (sectionT 𝒞)).supportSet := by
  obtain ⟨U, hU, hxU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let φ : Γ(module 𝒞, U) →ₗ[Γ(X, U)] Γ(X, U) := ((snd 𝒞).val.app (op U)).hom
  have hmem : (1 : Γ(X, U)) ∈ (zeroSchemeOfSection X (module 𝒞) (sectionT 𝒞)).ideal ⟨U, hU⟩ := by
    rw [SectionZeroScheme.zeroSchemeOfSection_ideal]
    refine Ideal.subset_span ⟨φ, ?_⟩
    have h1 : φ ((module 𝒞).presheaf.map (homOfLE le_top).op (sectionT 𝒞)) =
        X.presheaf.map (homOfLE le_top).op (((snd 𝒞).val.app (op ⊤)).hom (sectionT 𝒞)) :=
      PresheafOfModules.naturality_apply (snd 𝒞).val (homOfLE le_top).op (sectionT 𝒞)
    have h2 : ((snd 𝒞).val.app (op ⊤)).hom (sectionT 𝒞) = (1 : Γ(X, ⊤)) := by
      show ((snd 𝒞).val.app (op ⊤)).hom (((inr 𝒞).val.app (op ⊤)).hom (1 : Γ(X, ⊤))) = _
      exact congrArg (fun k : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ _ =>
        (k.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) (biprod.inr_snd : inr 𝒞 ≫ snd 𝒞 = 𝟙 _)
    rw [h1, h2, map_one]
  intro hx
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU,
    Scheme.mem_zeroLocus_iff] at hx
  exact hx 1 hmem (by rw [Scheme.basicOpen_one]; exact hxU)

/-- An invertible module on a scheme is trivialized near every point: there are an open `W ∋ y`
and a section `a` over it such that `c ↦ c • a|_V` is a bijection `Γ(Y, V) → Γ(L, V)` for every
open `V ≤ W`. -/
theorem _root_.Stacks.Divisors.exists_bijective_smul_of_isInvertible {Y : Scheme.{u}}
    (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L)
    (y : Y) :
    ∃ (W : Y.Opens) (_ : y ∈ W) (a : Γ(L, W)), ∀ (V : Y.Opens) (hV : V ≤ W),
      Function.Bijective fun c : Γ(Y, V) => c • L.presheaf.map (homOfLE hV).op a := by
  have hloc : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  have hinv : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  obtain ⟨W, hy, a, hbij⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (X := Y.toRingedSpace) L y
  exact ⟨W, hy, a, fun V hV => hbij V hV⟩

variable (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

include r in
/-- Multiplication by the germ of `T` on the local rings of `E` is injective. -/
theorem injective_smul_germ_coordT (ξ : space 𝒞) :
    Function.Injective fun c : (space 𝒞).presheaf.stalk ξ =>
      c • (twist 𝒞).presheaf.germ ⊤ ξ trivial (coordT 𝒞) := by
  by_cases hξ : ξ ∈ openT 𝒞
  · exact (isStalkBasis_coordT 𝒞 r ξ hξ).1
  have hsupp : ξ ∈ (Stacks.Divisors.zeroScheme _ (twist 𝒞) (coordT 𝒞)).support := by
    by_contra h
    exact hξ h
  obtain ⟨a₀, ha₀, haI₀⟩ := SectionZeroScheme.exists_nonZeroDivisor_mem_stalkIdeal_bundleSectionOf
    (module 𝒞) (bundlePieces (module 𝒞)) (sectionT 𝒞) ξ hsupp
    (notMem_supportSet_zeroSchemeOfSection_sectionT 𝒞 _)
  let a : (space 𝒞).presheaf.stalk ξ := a₀
  have ha : a ∈ nonZeroDivisors ((space 𝒞).presheaf.stalk ξ) := ha₀
  have haI : a ∈ Stacks.AlgebraicGeometry.stalkIdeal
      (Stacks.Divisors.zeroScheme (space 𝒞) (twist 𝒞) (coordT 𝒞)) ξ hsupp := haI₀
  obtain ⟨W, hξW, e, hbij⟩ := Stacks.Divisors.exists_bijective_smul_of_isInvertible (twist 𝒞)
    inferInstance ξ
  obtain ⟨U, hU, hξU, hUW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hξW
  replace hUW : U ≤ W := hUW
  set eU := (twist 𝒞).presheaf.map (homOfLE hUW).op e with heU
  obtain ⟨f, hf⟩ := (hbij U hUW).2 ((twist 𝒞).presheaf.map (homOfLE le_top).op (coordT 𝒞))
  replace hf : f • eU = (twist 𝒞).presheaf.map (homOfLE le_top).op (coordT 𝒞) := hf
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (twist 𝒞) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := isFiniteLocallyFreeOfRank_one_of_isInvertible (twist 𝒞))
  have hideal : (Stacks.Divisors.zeroScheme _ (twist 𝒞) (coordT 𝒞)).ideal ⟨U, hU⟩ ≤
      Ideal.span {f} := by
    rw [← zeroSchemeOfSection_eq_zeroScheme, SectionZeroScheme.zeroSchemeOfSection_ideal,
      Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    rw [← hf, φ.map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)
  rw [Stacks.AlgebraicGeometry.stalkIdeal_eq_map_germ _ ξ hsupp hU hξU] at haI
  have hspan := Ideal.map_mono (f := ((space 𝒞).presheaf.germ U ξ hξU).hom) hideal haI
  rw [Ideal.map_span, Set.image_singleton] at hspan
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hspan
  set gf := ((space 𝒞).presheaf.germ U ξ hξU).hom f with hgf
  have hgfnzd : ∀ x : (space 𝒞).presheaf.stalk ξ, x * gf = 0 → x = 0 := by
    intro x hx
    refine (mem_nonZeroDivisors_iff.mp ha).1 x ?_
    rw [← hc, mul_assoc, mul_comm gf x, hx, mul_zero]
  have he : Stacks.Divisors.IsStalkBasis (twist 𝒞) ξ ((twist 𝒞).presheaf.germ W ξ hξW e) :=
    Stacks.Divisors.isStalkBasis_germ_of_bijective_smul e hbij ξ hξW
  have hgerm : (twist 𝒞).presheaf.germ ⊤ ξ trivial (coordT 𝒞) =
      gf • (twist 𝒞).presheaf.germ W ξ hξW e := by
    rw [← (twist 𝒞).presheaf.germ_res_apply (homOfLE le_top) ξ hξU (coordT 𝒞), ← hf,
      Scheme.Modules.germ_smul (twist 𝒞) hξU, heU,
      (twist 𝒞).presheaf.germ_res_apply (homOfLE hUW) ξ hξU e]
  intro x y hxy
  replace hxy : x • (twist 𝒞).presheaf.germ ⊤ ξ trivial (coordT 𝒞) =
      y • (twist 𝒞).presheaf.germ ⊤ ξ trivial (coordT 𝒞) := hxy
  rw [hgerm, smul_smul, smul_smul] at hxy
  exact sub_eq_zero.mp (hgfnzd _ (by rw [sub_mul, he.1 hxy, sub_self]))

include r in
/-- Multiplication by `T`, `𝒪_E ⟶ 𝒪_E(1)`, is a monomorphism: `T` is a regular section of
`𝒪_E(1)`. -/
theorem mono_mulT : Mono (mulT 𝒞) := by
  refine (SheafOfModules.toSheaf (space 𝒞).ringCatSheaf).mono_of_mono_map
    ((TopCat.Presheaf.mono_iff_stalk_mono _).2 fun ξ => ?_)
  rw [AddCommGrpCat.mono_iff_injective]
  let O : (space 𝒞).Modules := SheafOfModules.unit (space 𝒞).ringCatSheaf
  have key : ∀ (U : (space 𝒞).Opens) (hξ : ξ ∈ U) (a : Γ(space 𝒞, U)),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat ξ).map
          ((SheafOfModules.toSheaf (space 𝒞).ringCatSheaf).map (mulT 𝒞)).hom
          (O.presheaf.germ U ξ hξ a) =
        (space 𝒞).presheaf.germ U ξ hξ a • (twist 𝒞).presheaf.germ ⊤ ξ trivial (coordT 𝒞) := by
    intro U hξ a
    have h1 := TopCat.Presheaf.stalkFunctor_map_germ_apply U ξ hξ
      ((SheafOfModules.toSheaf (space 𝒞).ringCatSheaf).map (mulT 𝒞)).hom a
    refine h1.trans ?_
    show (twist 𝒞).presheaf.germ U ξ hξ (((mulT 𝒞).val.app (op U)).hom a) = _
    rw [mulT_app, Scheme.Modules.germ_smul (twist 𝒞) hξ,
      (twist 𝒞).presheaf.germ_res_apply (homOfLE le_top) ξ hξ (coordT 𝒞)]
  intro y₁ y₂ hy
  obtain ⟨U₁, hξ₁, a₁, rfl⟩ := O.presheaf.exists_germ_eq y₁
  obtain ⟨U₂, hξ₂, a₂, rfl⟩ := O.presheaf.exists_germ_eq y₂
  have hy' := injective_smul_germ_coordT 𝒞 r ξ ((key U₁ hξ₁ a₁).symm.trans (hy.trans
    (key U₂ hξ₂ a₂)))
  obtain ⟨W, hξW, i₁, i₂, hW⟩ := (space 𝒞).presheaf.germ_eq ξ hξ₁ hξ₂ a₁ a₂ hy'
  rw [← O.presheaf.germ_res_apply i₁ ξ hξW a₁, ← O.presheaf.germ_res_apply i₂ ξ hξW a₂]
  exact congrArg (O.presheaf.germ W ξ hξW) hW

end Stacks.Chow.ProjectiveCompletion

end

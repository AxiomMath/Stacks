module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedChernCharacterKMap
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedTensorFormula
public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.SupportedProduct

/-!
# The localized Chern character map is multiplicative

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` with quasi-compact irreducible components and let `i : Z ⟶ X` be a closed
immersion. Remark 0FET says that the localized Chern character map

  `ch(Z ⟶ X, -) : K₀(D_{Z,perf}(𝒪_X)) ⟶ ∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`

(`Stacks.Chow.localizedChernCharKMap`) is multiplicative: the product on the left is induced by
the derived tensor product (Remark 0FDN, `AlgebraicGeometry.supportedPerfectNonUnitalCommRing`),
and `ch(Z ⟶ X, α β) = ch(Z ⟶ X, α) ch(Z ⟶ X, β)` by Lemma 0FBF.

The product on `∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐` is the Cauchy product of the components,
`(x y)_n = ∑_{p + q = n} x_p y_q`, the product of a class of degree `p` and one of degree `q`
being `res(c) ∘ c' ∈ A^{p+q}(Z ⟶ X)` (Stacks 0FA0), with `res : A^p(Z ⟶ X) ⟶ A^p(Z ×_X Z ⟶ Z)`
the restriction along `i` and `Z ×_X Z = Z`.

For `E, F ∈ D_{Z,perf}(𝒪_X)`, Lemma 0FBF at `Z₁ = Z₂ = Z` gives
`P_n(Z ×_X Z ⟶ X, E ⊗^L F) = ∑_{p + q = n} C(n, p) P_p(Z ⟶ X, E) P_q(Z ⟶ X, F)`; the class along
`Z` is the pushforward of the one along `Z ×_X Z` (Stacks 0FB7), that is its transport along
`Z ×_X Z ≅ Z`, and transport carries the product for the square `Z ×_X Z` to the product for the
square `Z = Z ×_X Z`. Dividing by `n! = p! q! C(n, p)` gives `ch(E ⊗^L F) = ch(E) ch(F)`, and the
identity on `K₀` follows by biadditivity.

## Main definitions

* `Stacks.Chow.rationalSupportedProductMul` — the product on `∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.supportedIntersectionMul_self_eq_supportedMul` — the product of Stacks 0FE5 for
  `Z ×_X Z = Z` is `res(c) ∘ c'` of Stacks 0FA0.
* `Stacks.Chow.supportedLocalizedPowerSum_derivedTensor` — Lemma 0FBF for the power sums of two
  perfect complexes supported on `Z`.
* `Stacks.Chow.supportedLocalizedChernChar_derivedTensor` — `ch(E ⊗^L F) = ch(E) ch(F)`.
* `Stacks.Chow.localizedChernCharKMap_mul` — `ch(Z ⟶ X, α β) = ch(Z ⟶ X, α) ch(Z ⟶ X, β)`.

## Implementation notes

The product of a class of degree `p` and one of degree `q` is the product of Stacks 0FE5
(`Stacks.Chow.supportedIntersectionMul`) for the two closed subschemes `Z, Z ⊆ X`, with
`Z ×_X Z` presented by the square whose two projections are the identity of `Z` (a closed
immersion is a monomorphism), the form in which Lemma 0FBF is proved; it is `res(c) ∘ c'` of
Stacks 0FA0 (`Stacks.Chow.supportedIntersectionMul_self_eq_supportedMul`).
Its extension of scalars to `𝐐` is `Stacks.Chow.rationalSupportedIntersectionMul`.

## References

* [Stacks Project, Tag 0FET](https://stacks.math.columbia.edu/tag/0FET)
* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TensorProduct Finset
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The product on `∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐` -/

section Product

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The product of Stacks 0FE5 for `Z ×_X Z = Z` is the third multiplication of Stacks 0FA0.**
For `c ∈ A^p(Z ⟶ X)` and `c' ∈ A^q(Z ⟶ X)`, the product `Stacks.Chow.supportedIntersectionMul`
for the square presenting `Z` as `Z ×_X Z` (both projections the identity) is
`res(c) ∘ c'` (`Stacks.Chow.supportedMul`): on a test scheme `T ⟶ X` both cap with `c'` and then
with `c` on `Z ×_X (Z ×_X T)`, and push forward along the same isomorphism to `Z ×_X T`. -/
theorem supportedIntersectionMul_self_eq_supportedMul {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl q) :
    supportedIntersectionMul C a i i (IsKernelPair.id_of_mono i) i (Category.id_comp i) c c' =
      supportedMul C (i ≫ a) a i rfl c c' := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} g _ k α ↦ ?_
  have hL := supportedIntersectionMul_cap C a i i (IsKernelPair.id_of_mono i) i
    (Category.id_comp i) c c' g k α
  have hR := supportedMul_cap C (i ≫ a) a i rfl c c' g k α
  refine eq_of_heq (hL.trans (HEq.trans (heq_of_eq ?_) hR.symm))
  refine chowPush_congr C _ _ ?_ _ _ _ _
  refine (cancel_mono (pullback.snd i g)).1 ?_
  rw [supportedIntersectionTestIso_hom_snd]

/-- **The product on `∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`**, `(x y)_n = ∑_{p + q = n} x_p y_q`, with the
product `A^p(Z ⟶ X) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)`, `(c, c') ↦ res(c) ∘ c'` of Stacks 0FA0
(`Stacks.Chow.supportedIntersectionMul` for `Z ×_X Z = Z`, which is `Stacks.Chow.supportedMul` by
`Stacks.Chow.supportedIntersectionMul_self_eq_supportedMul`), extended to `𝐐`. -/
def rationalSupportedProductMul :
    (∀ p : ℕ, ℚ ⊗[ℤ] BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl p) →ₗ[ℚ]
      (∀ p : ℕ, ℚ ⊗[ℤ] BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl p) →ₗ[ℚ]
        (∀ p : ℕ, ℚ ⊗[ℤ] BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl p) :=
  LinearMap.mk₂ ℚ
    (fun x y n ↦ ∑ q ∈ (antidiagonal n).attach,
      rationalBivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
        (rationalSupportedIntersectionMul C a i i (IsKernelPair.id_of_mono i) i
          (Category.id_comp i) (x q.1.1) (y q.1.2)))
    (fun x x' y ↦ funext fun n ↦ by
      simp only [Pi.add_apply, map_add, LinearMap.add_apply, sum_add_distrib])
    (fun c x y ↦ funext fun n ↦ by
      simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_sum])
    (fun x y y' ↦ funext fun n ↦ by
      simp only [Pi.add_apply, map_add, sum_add_distrib])
    (fun c x y ↦ funext fun n ↦ by
      simp only [Pi.smul_apply, map_smul, smul_sum])

/-- The components of the product on `∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐`. -/
theorem rationalSupportedProductMul_apply
    (x y : ∀ p : ℕ, ℚ ⊗[ℤ] BivariantClass C (gysinSystemOfInvertible C) (i ≫ a) a i rfl p)
    (n : ℕ) :
    rationalSupportedProductMul C a i x y n = ∑ q ∈ (antidiagonal n).attach,
      rationalBivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
        (rationalSupportedIntersectionMul C a i i (IsKernelPair.id_of_mono i) i
          (Category.id_comp i) (x q.1.1) (y q.1.2)) :=
  rfl

end Product

/-! ### Lemma 0FBF for perfect complexes supported on `Z` -/

section Tensor

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  {i : Z ⟶ X} [IsClosedImmersion i] (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- The second projection `Z ×_X Z ⟶ Z` of the self fibre product of a monomorphism is the inverse
of the identification `Z ≅ Z ×_X Z`. -/
theorem selfPullbackIso_inv {X Z : Scheme.{u}} (i : Z ⟶ X) [Mono i] :
    (selfPullbackIso i).inv = pullback.snd i i := by
  rw [← cancel_epi (selfPullbackIso i).hom, Iso.hom_inv_id, selfPullbackIso_hom_snd]

/-- A perfect complex supported on `Z` is supported on `Z ×_X Z`, the image of `Z ×_X Z ⟶ X` being
that of `Z`. -/
def supportedPerfectSelfPullback (E : supportedPerfectDerivedCategory i) :
    supportedPerfectDerivedCategory (pullback.snd i i ≫ i) :=
  ⟨E.obj, E.property.1, fun n ↦ (E.property.2 n).trans (by
    rintro _ ⟨z, rfl⟩
    exact ⟨(selfPullbackIso i).hom z, by
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, selfPullbackIso_hom_snd,
        Category.id_comp]⟩)⟩

/-- **Lemma 0FBF for the power sums of two perfect complexes supported on `Z`.** For
`E, F ∈ D_{Z,perf}(𝒪_X)`, in `A^n(Z ⟶ X)`,

  `P_n(Z ⟶ X, E ⊗^L F) = ∑_{p + q = n} C(n, p) P_p(Z ⟶ X, E) P_q(Z ⟶ X, F)`,

the product being `res(c) ∘ c'` (`Stacks.Chow.supportedIntersectionMul` for `Z ×_X Z = Z`). -/
theorem supportedLocalizedPowerSum_derivedTensor (E F : supportedPerfectDerivedCategory i)
    (n : ℕ) :
    (supportedPerfectData C a i (((supportedPerfectTensor i).obj E).obj F)).localizedPowerSum
        (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX _
          (((supportedPerfectTensor i).obj E).obj F).property.1)
        (supportedPerfectData_isZeroOnComplement C a _) n =
      ∑ q ∈ (antidiagonal n).attach, (n.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C a i i (IsKernelPair.id_of_mono i) i (Category.id_comp i)
            ((supportedPerfectData C a i E).localizedPowerSum
              (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj
                E.property.1)
              (supportedPerfectData_isZeroOnComplement C a E) q.1.1)
            ((supportedPerfectData C a i F).localizedPowerSum
              (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX F.obj
                F.property.1)
              (supportedPerfectData_isZeroOnComplement C a F) q.1.2)) := by
  let G := ((supportedPerfectTensor i).obj E).obj F
  have hd : ∀ E : supportedPerfectDerivedCategory i, HasDefinedChernClasses E.obj := fun E ↦
    hasDefinedChernClasses_of_isCompact_irreducibleComponents C a hX E.obj E.property.1
  have hgys : (gysinSystemOfInvertible C).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C
  have : IsIso (pullback.snd i i) := by
    rw [← selfPullbackIso_inv]
    infer_instance
  let θ : pullback i i ≅ Z := asIso (pullback.snd i i)
  have hθ : θ.hom ≫ i = pullback.snd i i ≫ i := rfl
  have h₀ := supportedLocalizedPowerSum_eq_bivariantProperPushforward C a
    (i := pullback.snd i i ≫ i) (i' := i) (j := pullback.snd i i) rfl hX
    (supportedPerfectSelfPullback G) G rfl n
  have hF := LocalizedChernData.localizedPowerSum_derivedTensorOfIsZero C a i i E.property.1
    F.property.1 (supportedPerfect_isZero_derivedPullback_compl i E)
    (supportedPerfect_isZero_derivedPullback_compl i F)
    (hd E) (hd F) (hd G) n
  let P := (supportedPerfectData C a (pullback.snd i i ≫ i)
      (supportedPerfectSelfPullback G)).localizedPowerSum
        (hd G) (supportedPerfectData_isZeroOnComplement C a _) n
  have htr := bivariantTransport_eq_bivariantProperPushforward_of_eq
    (sA := (pullback.snd i i ≫ i) ≫ a) (sW := a) (v := pullback.snd i i ≫ i) (u := i) θ hθ rfl rfl
    rfl P
    (P.congrHom hθ.symm (by rw [hθ])) (BivariantClass.congrHom_heq _ _ _)
  refine h₀.trans (htr.symm.trans ?_)
  have hT : ∀ c, bivariantTransport C (gysinSystemOfInvertible C) ((pullback.snd i i ≫ i) ≫ a)
      (i ≫ a) a (pullback.snd i i ≫ i) rfl i rfl θ hθ n hgys c =
        bivariantTransportAddHom C (gysinSystemOfInvertible C) ((pullback.snd i i ≫ i) ≫ a)
          (i ≫ a) a (pullback.snd i i ≫ i) rfl i rfl θ hθ n hgys c := fun _ ↦ rfl
  rw [hT]
  refine (congrArg _ hF).trans ?_
  rw [map_sum]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [map_zsmul, ← hT, bivariantTransport_bivariantClassDegreeCongr,
    bivariantTransport_supportedIntersectionMul C a i i (IsPullback.of_hasPullback i i)
      (IsKernelPair.id_of_mono i) _ rfl i (Category.id_comp i)]

/-- **`ch(Z ⟶ X, E ⊗^L F) = ch(Z ⟶ X, E) ch(Z ⟶ X, F)`** for `E, F ∈ D_{Z,perf}(𝒪_X)`, in
`∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐` (Lemma 0FBF): the power sum formula
`Stacks.Chow.supportedLocalizedPowerSum_derivedTensor` divided by `n! = p! q! C(n, p)`. -/
theorem supportedLocalizedChernChar_derivedTensor (E F : supportedPerfectDerivedCategory i) :
    supportedLocalizedChernChar C a hX (((supportedPerfectTensor i).obj E).obj F) =
      rationalSupportedProductMul C a i (supportedLocalizedChernChar C a hX E)
        (supportedLocalizedChernChar C a hX F) :=
  funext fun n ↦ tmul_eq_sum_rationalSupportedIntersectionMul_of_eq_sum_choose C a i i
    (IsKernelPair.id_of_mono i) i (Category.id_comp i) _ _ _ n
    (supportedLocalizedPowerSum_derivedTensor C a hX E F n)

end Tensor

/-! ### Multiplicativity on `K₀` -/

section KMap

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  {i : Z ⟶ X} [IsClosedImmersion i] (hX : ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- **The localized Chern character map is multiplicative.** For `X` with quasi-compact
irreducible components and `α, β ∈ K₀(D_{Z,perf}(𝒪_X))`, multiplied by the derived tensor product
(Remark 0FDN),

  `ch(Z ⟶ X, α β) = ch(Z ⟶ X, α) ch(Z ⟶ X, β)`

in `∏_{p ≥ 0} A^p(Z ⟶ X) ⊗ 𝐐` (`Stacks.Chow.rationalSupportedProductMul`). -/
@[stacks 0FET "localized_chern_character_k_multiplicative: ch(Z → X, αβ) = \
  ch(Z → X, α) ch(Z → X, β), the product on K_0(D_{Z,perf}(O_X)) being derived tensor product \
  (0FDN) and that on ∏ A^p(Z → X) ⊗ Q the Cauchy product of the products res(c) ∘ c' of 0FA0"]
theorem localizedChernCharKMap_mul (x y : K0 (supportedPerfectDerivedCategory i)) :
    localizedChernCharKMap C a hX (x * y) =
      rationalSupportedProductMul C a i (localizedChernCharKMap C a hX x)
        (localizedChernCharKMap C a hX y) := by
  have h₁ : ∀ E F : supportedPerfectDerivedCategory i,
      localizedChernCharKMap C a hX (K0.cls E * K0.cls F) =
        rationalSupportedProductMul C a i (localizedChernCharKMap C a hX (K0.cls E))
          (localizedChernCharKMap C a hX (K0.cls F)) := fun E F ↦ by
    simp only [supportedPerfect_cls_mul_cls, localizedChernCharKMap_cls]
    exact supportedLocalizedChernChar_derivedTensor C a hX E F
  have h₂ : ∀ (F : supportedPerfectDerivedCategory i) (x : K0 (supportedPerfectDerivedCategory i)),
      localizedChernCharKMap C a hX (x * K0.cls F) =
        rationalSupportedProductMul C a i (localizedChernCharKMap C a hX x)
          (localizedChernCharKMap C a hX (K0.cls F)) := fun F x ↦
    DFunLike.congr_fun (K0.hom_ext
      (f := (localizedChernCharKMap C a hX).comp ((supportedPerfectMul i).flip (K0.cls F)))
      (g := ((rationalSupportedProductMul C a i).flip
        (localizedChernCharKMap C a hX (K0.cls F))).toAddMonoidHom.comp
          (localizedChernCharKMap C a hX)) fun E ↦ h₁ E F) x
  exact DFunLike.congr_fun (K0.hom_ext
    (f := (localizedChernCharKMap C a hX).comp (supportedPerfectMul i x))
    (g := (rationalSupportedProductMul C a i (localizedChernCharKMap C a hX x)).toAddMonoidHom.comp
      (localizedChernCharKMap C a hX)) fun F ↦ h₂ F x) y

end KMap

end Stacks.Chow

end

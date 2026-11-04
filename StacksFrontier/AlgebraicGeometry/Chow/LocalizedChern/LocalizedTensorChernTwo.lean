module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.InfinityGysinProducts

/-!
# The second localized Chern class of a derived tensor product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z₁, Z₂ ⊆ X` be closed subschemes and let `F₁, F₂ ∈ D(𝒪_X)` be perfect
with `F_i|_{X ∖ Z_i}` zero. Lemma 0FBF computes the second localized Chern class of `F₁ ⊗^L F₂`:

  `c_2(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ c_2(Z₂ ⟶ X, F₂) + r₂ c_2(Z₁ ⟶ X, F₁) +
    C(r₁, 2) c_1(Z₂ ⟶ X, F₂)² + (r₁ r₂ - 1) c_1(Z₂ ⟶ X, F₂) c_1(Z₁ ⟶ X, F₁) +
    C(r₂, 2) c_1(Z₁ ⟶ X, F₁)²`

in `A^2(Z₁ ∩ Z₂ ⟶ X)`, with `r_i = P_0(Z_i ⟶ X, F_i)`.

The proof is that of the first Chern class
(`Stacks.Chow.modificationChernClass_one_derivedTensor`): on a modification `b : W ⟶ 𝐏¹_X` the
class `c'_2(Q₁ ⊗^L Q₂)` of Stacks 0F9K is the localization of the class of Stacks 0F9H on `W_∞`,
which Stacks 0FE5 expands; the localization of each product is the product of the localizations
(Stacks 0FE7), the classes `C(r'_i, 2)` on `W_∞` localize to `C(r_i, 2)`, Stacks 0FE8 identifies
the classes on the common modification of the graph constructions with the localized classes, and
the formula descends from an envelope.

## Main results

* `Stacks.Chow.modificationInfinityChernClass_two_derivedTensor` — Stacks 0FE5 on `W_∞` for
  `c'_2((Q₁ ⊗^L Q₂)|_{E₁ ∩ E₂})`.
* `Stacks.Chow.modificationChernClass_two_derivedTensor` — the formula for `c'_2(Q₁ ⊗^L Q₂)` on
  one modification.
* `Stacks.Chow.localizedChern_two_derivedTensor_of_isLocallyBoundedFiniteLocallyFree` — the
  formula when the three objects are complexes.
* `Stacks.Chow.LocalizedChernData.localizedChern_two_derivedTensorOfIsZero` — the formula for the
  classes of Remark 0GUK.
* `Stacks.Chow.bivariantTransport_supportedMul` — transport along an isomorphism of closed
  subschemes commutes with the third multiplication of Stacks 0FA0.

## Implementation notes

The squares `c_1²` are the products `res(c) ∘ c` of Stacks 0FA0 (`Stacks.Chow.supportedMul`), and
`(r₁ r₂ - 1) γ_{2,1} γ_{1,1}` is read as `(r₁ r₂) (γ_{2,1} γ_{1,1}) - γ_{2,1} γ_{1,1}`, as in
`Stacks.Chow.closedCoverChernClass_derivedTensor_two`. The product `(r₁ r₂) (γ_{2,1} γ_{1,1})` is
a product of two classes supported on `Z₁ ∩ Z₂`; to compare the presentations `Z ≅ Z₁ ×_X Z₂` of
the intersection it is transported, which commutes with the factors
(`Stacks.Chow.bivariantTransport_supportedMul`). On a modification its localization is the
product of the localizations by Stacks 0FE7 for one closed subscheme
(`Stacks.Chow.supportedMul_modificationLocalization`), the second factor preserving the image of
the Gysin map at infinity
(`Stacks.Chow.PreservesInfinityGysinImage.supportedIntersectionMul_flip`).

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Finset

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

open TotalChowClass

section TransportSupportedMul

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (y : Y ⟶ X) [IsClosedImmersion y] (y' : Y' ⟶ X) [IsClosedImmersion y'] (θ : Y ≅ Y')
  (hθ : θ.hom ≫ y' = y)

/-- Transport along `θ` commutes with differences. -/
theorem bivariantTransport_sub (G : GysinSystem C) {A B W : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA)
    (u : B ⟶ W) [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
    (p : ℤ) (hgys : G.IsNaturalUnderBaseChangeIso) (c d : BivariantClass C G sA sW v hv p) :
    bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys (c - d) =
      bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c -
        bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys d :=
  map_sub (bivariantTransportAddHom C G sA sB sW v hv u hu θ hθ p hgys) c d

/-- **Transport commutes with the third multiplication of Stacks 0FA0.** For an isomorphism
`θ : Y ≅ Y'` of closed subschemes of `X` over `X` and `c ∈ A^p(Y ⟶ X)`, `c' ∈ A^q(Y ⟶ X)`, the
transport of `res(c) ∘ c'` along `θ` is `res(θ_* c) ∘ θ_* c'`: on a test scheme `T ⟶ X` both cap
with `c'` and then with `c`, and push forward to `Y' ×_X T` along morphisms which agree. -/
theorem bivariantTransport_supportedMul {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) (y ≫ f) f y rfl p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (y ≫ f) f y rfl q) :
    bivariantTransport C (gysinSystemOfInvertible C) (y ≫ f) (y' ≫ f) f y rfl y' rfl θ hθ (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (supportedMul C (y ≫ f) f y rfl c c') =
      supportedMul C (y' ≫ f) f y' rfl
        (bivariantTransport C (gysinSystemOfInvertible C) (y ≫ f) (y' ≫ f) f y rfl y' rfl θ hθ p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
        (bivariantTransport C (gysinSystemOfInvertible C) (y ≫ f) (y' ≫ f) f y rfl y' rfl θ hθ q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c') := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} g _ k α ↦ eq_of_heq ?_
  have hκ : (transportPullbackIso y y' θ hθ g).hom ≫ pullback.fst y' g ≫ y' =
      pullback.fst y g ≫ y := by
    rw [transportPullbackIso_hom_fst_assoc, hθ]
  have hL := supportedMul_cap C (y ≫ f) f y rfl c c' g k α
  have hR := supportedMul_cap C (y' ≫ f) f y' rfl
    (bivariantTransport C (gysinSystemOfInvertible C) (y ≫ f) (y' ≫ f) f y rfl y' rfl θ hθ p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
    (bivariantTransport C (gysinSystemOfInvertible C) (y ≫ f) (y' ≫ f) f y rfl y' rfl θ hθ q
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c') g k α
  refine HEq.trans ?_ hR.symm
  rw [bivariantTransport_cap, bivariantTransportCap_apply]
  have hb := transportPullbackIso_hom_comp_base C (y ≫ f) (y' ≫ f) f y rfl y' rfl θ hθ g
  refine (chowPushforwardOfIso_heq (transportPullbackIso y y' θ hθ g).hom hb hb rfl rfl
    (by ring) hL).trans (heq_of_eq ?_)
  have hb' : (transportPullbackIso y y' θ hθ g).hom ≫ (pullback.fst y' g ≫ y') ≫ f =
      pullback.fst y g ≫ y ≫ f := by
    rw [← Category.assoc, hκ, Category.assoc]
  have E1 := chowGroupCongr_chowPushforwardOfIso_target C (pullback.fst y g ≫ y ≫ f)
    (Category.assoc (pullback.fst y' g) y' f).symm (transportPullbackIso y y' θ hθ g).hom hb hb'
    (k - q) (c'.cap g k α)
  have E2 := BivariantClass.cap_chowPushforwardOfIso c (pullback.fst y' g ≫ y')
    (transportPullbackIso y y' θ hθ g).hom (pullback.fst y g ≫ y) hκ (pullback.fst y g ≫ y ≫ f)
    (Category.assoc _ _ _).symm (k - q) hb' (c'.cap g k α) _ rfl
  simp only [bivariantTransport_cap, bivariantTransportCap_apply]
  rw [E1, E2, chowPushforwardOfIso_chowPush, chowPush_chowPushforwardOfIso,
    chowPush_chowPushforwardOfIso]
  · refine chowPush_congr C _ _ ?_ _ _ _ _
    simp
  all_goals simp [pullback.condition_assoc]

end TransportSupportedMul

section TensorChernTwo

variable (C : ChowSituation.{u}) {X W Z₁ Z₂ T₁ T₂ : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (z₁ : Z₁ ⟶ X) [IsClosedImmersion z₁] (z₂ : Z₂ ⟶ X) [IsClosedImmersion z₂]
  (t₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₁]
  (t₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₂]
  {Q₁ Q₂ : DerivedCategory W.Modules}
  (hQp₁ : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q₁)
  (hQp₂ : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q₂)
  (hQ₁ : HasDefinedChernClasses Q₁) (hQ₂ : HasDefinedChernClasses Q₂)
  (hT₁ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₁ → w ∈ Set.range t₁)
  (hT₂ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₂ → w ∈ Set.range t₂)
  (hzero₁ : IsZero ((derivedPullback
    (t₁ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₁))
  (hzero₂ : IsZero ((derivedPullback
    (t₂ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₂))

/-- **Stacks 0FE5 on `W_∞` for `c'_2((Q₁ ⊗^L Q₂)|_{E₁ ∩ E₂})`.** On the fibre at infinity, along
the closed cover `W_∞ = (T₁ ∪ T₂) ∪ (E₁ ∩ E₂)`, the class `c'_2((Q₁ ⊗^L Q₂)|_{E₁ ∩ E₂})` of
Stacks 0F9H is

  `r'₁ γ'_{2,2} + r'₂ γ'_{1,2} + C(r'₁, 2) γ'_{2,1}² + ((r'₁ r'₂) (γ'_{2,1} γ'_{1,1}) -
    γ'_{2,1} γ'_{1,1}) + C(r'₂, 2) γ'_{1,1}²`

with `r'_i = P'_0(Q_i|_{E_i})`, `γ'_{i,p} = c'_p(Q_i|_{E_i})` and `C(r'_i, 2)` the classes of
`Stacks.Chow.closedCoverRankChoose`; the products of a class on `E₂` with one on `E₁` are taken
for `E₁ ∩ E₂` presented as `E₂ ×_{W_∞} E₁`, and the squares are the products of
`Stacks.Chow.supportedMul`. -/
theorem modificationInfinityChernClass_two_derivedTensor :
    modificationInfinityChernClass C f b (pullback.fst z₁ z₂ ≫ z₁)
        (reducedUnionIdeal t₁ t₂).subschemeι
        (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
        (hasDefinedChernClasses_derivedTensor hQ₁ hQ₂) 2
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂)
          two_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (modificationInfinityMul C f b z₁ z₂
            (modificationInfinityPowerSum C f b z₁ t₁ hT₁ hQ₁ 0 hzero₁)
            (modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ 2
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
            (pullback.fst (modificationProjectionAtInfinity f b) z₂)
            (pullback.fst (modificationProjectionAtInfinity f b) z₁)
            (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z₂ z₁).flip
            (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z₁ z₂ ≫ z₁))
            (pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ _)
            (modificationInfinityPowerSum C f b z₂ t₂ hT₂ hQ₂ 0 hzero₂)
            (modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ 2
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (modificationInfinityMul C f b z₁ z₂
            (closedCoverRankChoose C (modificationProjectionAtInfinity f b ≫ f) t₁
              (pullback.fst (modificationProjectionAtInfinity f b) z₁)
              (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q₁ hQp₁)
              (range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁)
              (isZero_derivedPullback_inclusionAtInfinity C f b hzero₁) 2 two_pos)
            (supportedMul C (pullback.fst (modificationProjectionAtInfinity f b) z₂ ≫
                modificationProjectionAtInfinity f b ≫ f)
              (modificationProjectionAtInfinity f b ≫ f)
              (pullback.fst (modificationProjectionAtInfinity f b) z₂) rfl
              (modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ 1
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))
              (modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ 1
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos)))) +
        (bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedMul C (pullback.fst (modificationProjectionAtInfinity f b)
                (pullback.fst z₁ z₂ ≫ z₁) ≫ modificationProjectionAtInfinity f b ≫ f)
              (modificationProjectionAtInfinity f b ≫ f)
              (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z₁ z₂ ≫ z₁)) rfl
              (modificationInfinityMul C f b z₁ z₂
                (modificationInfinityPowerSum C f b z₁ t₁ hT₁ hQ₁ 0 hzero₁)
                (modificationInfinityPowerSum C f b z₂ t₂ hT₂ hQ₂ 0 hzero₂))
              (supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
                (pullback.fst (modificationProjectionAtInfinity f b) z₂)
                (pullback.fst (modificationProjectionAtInfinity f b) z₁)
                (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z₂ z₁).flip
                (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z₁ z₂ ≫ z₁))
                (pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ _)
                (modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ 1
                  (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))
                (modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ 1
                  (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos)))) -
          bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
              (pullback.fst (modificationProjectionAtInfinity f b) z₂)
              (pullback.fst (modificationProjectionAtInfinity f b) z₁)
              (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z₂ z₁).flip
              (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z₁ z₂ ≫ z₁))
              (pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ _)
              (modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ 1
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))
              (modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ 1
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
            (pullback.fst (modificationProjectionAtInfinity f b) z₂)
            (pullback.fst (modificationProjectionAtInfinity f b) z₁)
            (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z₂ z₁).flip
            (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z₁ z₂ ≫ z₁))
            (pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ _)
            (closedCoverRankChoose C (modificationProjectionAtInfinity f b ≫ f) t₂
              (pullback.fst (modificationProjectionAtInfinity f b) z₂)
              (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q₂ hQp₂)
              (range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂)
              (isZero_derivedPullback_inclusionAtInfinity C f b hzero₂) 2 two_pos)
            (supportedMul C (pullback.fst (modificationProjectionAtInfinity f b) z₁ ≫
                modificationProjectionAtInfinity f b ≫ f)
              (modificationProjectionAtInfinity f b ≫ f)
              (pullback.fst (modificationProjectionAtInfinity f b) z₁) rfl
              (modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ 1
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos))
              (modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ 1
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos)))) := by
  set π := modificationProjectionAtInfinity f b
  set ι := modificationInclusionAtInfinity f b
  set iW := pullback.fst π (pullback.fst z₁ z₂ ≫ z₁)
  have hQ := hasDefinedChernClasses_derivedTensor hQ₁ hQ₂
  have hP₁ : RingedSpace.IsPerfect.{u, u + 1} ((derivedPullback ι.toLRSHom.toShHom).obj Q₁) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q₁ hQp₁
  have hP₂ : RingedSpace.IsPerfect.{u, u + 1} ((derivedPullback ι.toLRSHom.toShHom).obj Q₂) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q₂ hQp₂
  have hiso := perfectChernClass_congr C (iW ≫ π ≫ f)
    ((hQ.derivedPullback ι).derivedPullback iW)
    ((hasDefinedChernClasses_derivedTensor (hQ₁.derivedPullback ι)
      (hQ₂.derivedPullback ι)).derivedPullback iW)
    ((derivedPullback iW.toLRSHom.toShHom).mapIso (derivedPullbackDerivedTensorIso ι Q₁ Q₂))
  have hcoverY : Set.range (reducedUnionIdeal t₁ t₂).subschemeι ∪ Set.range iW = Set.univ :=
    range_union_range_pullbackFst_eq_univ _ _
      (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
  refine IsClosedCoverExtension.eq hcoverY
    (isClosedCoverExtension_closedCoverChernClass C (π ≫ f) _ iW _ rfl _ _ _ _) ?_
  rw [hiso, perfectChernClass_two_derivedPullback_derivedTensor C (π ≫ f)
    (hQ₁.derivedPullback ι) (hQ₂.derivedPullback ι) hP₁ hP₂ iW]
  have hw₁ : ((pullbackFstTestIso π z₁ z₂).inv ≫ pullback.fst _ _) ≫ pullback.fst π z₁ = iW :=
    pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ π
  have hw₂ : ((pullbackFstTestIso π z₁ z₂).inv ≫ pullback.snd _ _) ≫ pullback.fst π z₂ = iW :=
    pullbackFstTestIso_inv_snd_fst π z₂ z₁
  have hcov₁ := range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁
  have hcov₂ := range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂
  have hz₁ := isZero_derivedPullback_of_isZero_of_comp_eq (pullback.condition (f := t₁)
    (g := pullback.fst π z₁)) (isZero_derivedPullback_inclusionAtInfinity C f b hzero₁)
  have hz₂ := isZero_derivedPullback_of_isZero_of_comp_eq (pullback.condition (f := t₂)
    (g := pullback.fst π z₂)) (isZero_derivedPullback_inclusionAtInfinity C f b hzero₂)
  have hcr₁ := isClosedCoverExtension_closedCoverPowerSum C (π ≫ f) t₁ (pullback.fst π z₁) _ rfl
    ((hQ₁.derivedPullback ι).derivedPullback (pullback.fst π z₁)) 0 hcov₁ hz₁
  have hcr₂ := isClosedCoverExtension_closedCoverPowerSum C (π ≫ f) t₂ (pullback.fst π z₂) _ rfl
    ((hQ₂.derivedPullback ι).derivedPullback (pullback.fst π z₂)) 0 hcov₂ hz₂
  have hcγ₁ := isClosedCoverExtension_closedCoverChernClassOfIsZero C (π ≫ f) t₁
    (pullback.fst π z₁) ((hQ₁.derivedPullback ι).derivedPullback (pullback.fst π z₁))
    hcov₁ hz₁
  have hcγ₂ := isClosedCoverExtension_closedCoverChernClassOfIsZero C (π ≫ f) t₂
    (pullback.fst π z₂) ((hQ₂.derivedPullback ι).derivedPullback (pullback.fst π z₂))
    hcov₂ hz₂
  have hdA₁ := isRestriction_res_res (perfectPowerSum C (π ≫ f) (hQ₁.derivedPullback ι) 0)
    (pullback.fst π z₁) _ iW hw₁ 0
  have hdA₂ := isRestriction_res_res (perfectPowerSum C (π ≫ f) (hQ₂.derivedPullback ι) 0)
    (pullback.fst π z₂) _ iW hw₂ 0
  have hdB₁ := isRestriction_res_res (perfectChernClass C (π ≫ f) (hQ₁.derivedPullback ι))
    (pullback.fst π z₁) _ iW hw₁
  have hdB₂ := isRestriction_res_res (perfectChernClass C (π ≫ f) (hQ₂.derivedPullback ι))
    (pullback.fst π z₂) _ iW hw₂
  have hdL₁ := isRestriction_res_res (ofLocallyConstant C (π ≫ f)
    ((perfectRank _ hP₁).map fun k ↦ Ring.choose k 2)) (pullback.fst π z₁) _ iW hw₁ 0
  have hdL₂ := isRestriction_res_res (ofLocallyConstant C (π ≫ f)
    ((perfectRank _ hP₂).map fun k ↦ Ring.choose k 2)) (pullback.fst π z₂) _ iW hw₂ 0
  rw [res_perfectPowerSum_derivedPullback C (π ≫ f) (hQ₁.derivedPullback ι) (pullback.fst π z₁)
    rfl ((hQ₁.derivedPullback ι).derivedPullback (pullback.fst π z₁))] at hdA₁
  rw [res_perfectPowerSum_derivedPullback C (π ≫ f) (hQ₂.derivedPullback ι) (pullback.fst π z₂)
    rfl ((hQ₂.derivedPullback ι).derivedPullback (pullback.fst π z₂))] at hdA₂
  rw [res_perfectChernClass_derivedPullback_of_comp_eq C (π ≫ f) (hQ₁.derivedPullback ι)
    (pullback.fst π z₁) rfl ((hQ₁.derivedPullback ι).derivedPullback (pullback.fst π z₁))] at hdB₁
  rw [res_perfectChernClass_derivedPullback_of_comp_eq C (π ≫ f) (hQ₂.derivedPullback ι)
    (pullback.fst π z₂) rfl ((hQ₂.derivedPullback ι).derivedPullback (pullback.fst π z₂))] at hdB₂
  have hY : Set.range (reducedUnionIdeal t₁ t₂).subschemeι ⊆ Set.range t₁ ∪ Set.range t₂ :=
    (range_subschemeι_reducedUnionIdeal t₁ t₂).subset
  have hY' : Set.range (reducedUnionIdeal t₁ t₂).subschemeι ⊆ Set.range t₂ ∪ Set.range t₁ :=
    hY.trans (Set.union_comm _ _).subset
  have hsq₁ := IsClosedCoverExtension.supportedMul C (π ≫ f) t₁ (pullback.fst π z₁) hcov₁
    (vanishesOver_perfectChernClass_of_isZero' C (π ≫ f) t₁ (pullback.fst π z₁) _ hz₁ 1 one_pos)
    (vanishesOver_perfectChernClass_of_isZero' C (π ≫ f) t₁ (pullback.fst π z₁) _ hz₁ 1 one_pos)
    (hcγ₁ 1 one_pos) (hcγ₁ 1 one_pos)
  have hsq₂ := IsClosedCoverExtension.supportedMul C (π ≫ f) t₂ (pullback.fst π z₂) hcov₂
    (vanishesOver_perfectChernClass_of_isZero' C (π ≫ f) t₂ (pullback.fst π z₂) _ hz₂ 1 one_pos)
    (vanishesOver_perfectChernClass_of_isZero' C (π ≫ f) t₂ (pullback.fst π z₂) _ hz₂ 1 one_pos)
    (hcγ₂ 1 one_pos) (hcγ₂ 1 one_pos)
  have hrr := IsClosedCoverExtension.supportedIntersectionMul
    (sq := isPullback_pullbackFstTestIso π z₂ z₁)
    (hW := pullbackFstTestIso_inv_snd_fst π z₂ z₁) _ hcr₁ hcr₂ hdA₁ hdA₂ hY
  have hγγ := IsClosedCoverExtension.supportedIntersectionMul
    (sq := (isPullback_pullbackFstTestIso π z₂ z₁).flip)
    (hW := pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ _) _ (hcγ₂ 1 one_pos) (hcγ₁ 1 one_pos)
    (hdB₂ 1) (hdB₁ 1) hY'
  refine IsClosedCoverExtension.add (IsClosedCoverExtension.add (IsClosedCoverExtension.add
    (IsClosedCoverExtension.add ?_ ?_) ?_) (IsClosedCoverExtension.sub C (π ≫ f) _ iW ?_ ?_)) ?_
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _
      (IsClosedCoverExtension.supportedIntersectionMul _ hcr₁
        (isClosedCoverExtension_closedCoverChernClass C (π ≫ f) t₂ (pullback.fst π z₂) _ rfl _ _
          hcov₂ _) hdA₁ (hdB₂ 2) hY)
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _
      (IsClosedCoverExtension.supportedIntersectionMul _ hcr₂
        (isClosedCoverExtension_closedCoverChernClass C (π ≫ f) t₁ (pullback.fst π z₁) _ rfl _ _
          hcov₁ _) hdA₂ (hdB₁ 2) hY')
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _
      (IsClosedCoverExtension.supportedIntersectionMul _
        (isClosedCoverExtension_closedCoverRankChoose C (π ≫ f) t₁ (pullback.fst π z₁) hP₁ hcov₁
          (isZero_derivedPullback_inclusionAtInfinity C f b hzero₁) 2 two_pos)
        hsq₂ hdL₁ ((hdB₂ 1).mulId (hdB₂ 1)) hY)
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _
      (IsClosedCoverExtension.supportedMul C (π ≫ f) _ iW hcoverY hrr.vanishesOver
        hγγ.vanishesOver hrr hγγ)
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _ hγγ
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _
      (IsClosedCoverExtension.supportedIntersectionMul _
        (isClosedCoverExtension_closedCoverRankChoose C (π ≫ f) t₂ (pullback.fst π z₂) hP₂ hcov₂
          (isZero_derivedPullback_inclusionAtInfinity C f b hzero₂) 2 two_pos)
        hsq₁ hdL₂ ((hdB₁ 1).mulId (hdB₁ 1)) hY')

variable (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- **The class `c'_2(Q₁ ⊗^L Q₂)` of Stacks 0F9K** (the second paragraph of the proof of
Stacks 0FBF). In the situation of `Stacks.Chow.modificationChernClass_one_derivedTensor`, write
`r'_i = P'_0(Q_i)` and `γ'_{i,p} = c'_p(Q_i)` for the classes of Stacks 0F9K, and `C(r'_i, 2)` for
the localization of the class `Stacks.Chow.closedCoverRankChoose` of `Q_i|_{W_∞}`. Then

  `c'_2(Q₁ ⊗^L Q₂) = r'₁ γ'_{2,2} + r'₂ γ'_{1,2} + C(r'₁, 2) γ'_{2,1}² +
    ((r'₁ r'₂) (γ'_{2,1} γ'_{1,1}) - γ'_{2,1} γ'_{1,1}) + C(r'₂, 2) γ'_{1,1}²`

in `A^2(Z₁ ∩ Z₂ ⟶ X)`, the products of a class supported on `Z₂` with one supported on `Z₁` taken
for `Z₁ ∩ Z₂` presented as `Z₂ ×_X Z₁` through the flipped square, and the squares being the
products of `Stacks.Chow.supportedMul`. -/
theorem modificationChernClass_two_derivedTensor
    (hres₁ : IsZero ((derivedPullback
      (W.toRingedSpace.ofRestrict (modificationComplementOpens b z₁).isOpenEmbedding)).obj Q₁))
    (hres₂ : IsZero ((derivedPullback
      (W.toRingedSpace.ofRestrict (modificationComplementOpens b z₂).isOpenEmbedding)).obj Q₂))
    (hfin₁ : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q₁)
    (hfin₂ : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q₂) :
    modificationChernClass C f b hA (pullback.fst z₁ z₂ ≫ z₁) (reducedUnionIdeal t₁ t₂).subschemeι
        (hasDefinedChernClasses_derivedTensor hQ₁ hQ₂) 2
        (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂)
          two_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₁ z₂ (IsPullback.of_hasPullback z₁ z₂)
            (pullback.fst z₁ z₂ ≫ z₁) pullback.condition.symm
            (modificationPowerSum C f b hA z₁ t₁ hQ₁ 0 hT₁ hzero₁)
            (modificationChernClass C f b hA z₂ t₂ hQ₂ 2 hT₂
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₂ z₁ (IsPullback.of_hasPullback z₁ z₂).flip
            (pullback.fst z₁ z₂ ≫ z₁) rfl
            (modificationPowerSum C f b hA z₂ t₂ hQ₂ 0 hT₂ hzero₂)
            (modificationChernClass C f b hA z₁ t₁ hQ₁ 2 hT₁
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₁ z₂ (IsPullback.of_hasPullback z₁ z₂)
            (pullback.fst z₁ z₂ ≫ z₁) pullback.condition.symm
            (modificationLocalization C f b hA z₁
              (closedCoverRankChoose C (modificationProjectionAtInfinity f b ≫ f) t₁
                (pullback.fst (modificationProjectionAtInfinity f b) z₁)
                (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q₁ hQp₁)
                (range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁)
                (isZero_derivedPullback_inclusionAtInfinity C f b hzero₁) 2 two_pos))
            (supportedMul C (z₂ ≫ f) f z₂ rfl
              (modificationChernClass C f b hA z₂ t₂ hQ₂ 1 hT₂
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))
              (modificationChernClass C f b hA z₂ t₂ hQ₂ 1 hT₂
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos)))) +
        (bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedMul C ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f (pullback.fst z₁ z₂ ≫ z₁) rfl
              (supportedIntersectionMul C f z₁ z₂ (IsPullback.of_hasPullback z₁ z₂)
                (pullback.fst z₁ z₂ ≫ z₁) pullback.condition.symm
                (modificationPowerSum C f b hA z₁ t₁ hQ₁ 0 hT₁ hzero₁)
                (modificationPowerSum C f b hA z₂ t₂ hQ₂ 0 hT₂ hzero₂))
              (supportedIntersectionMul C f z₂ z₁ (IsPullback.of_hasPullback z₁ z₂).flip
                (pullback.fst z₁ z₂ ≫ z₁) rfl
                (modificationChernClass C f b hA z₂ t₂ hQ₂ 1 hT₂
                  (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))
                (modificationChernClass C f b hA z₁ t₁ hQ₁ 1 hT₁
                  (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos)))) -
          bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedIntersectionMul C f z₂ z₁ (IsPullback.of_hasPullback z₁ z₂).flip
              (pullback.fst z₁ z₂ ≫ z₁) rfl
              (modificationChernClass C f b hA z₂ t₂ hQ₂ 1 hT₂
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))
              (modificationChernClass C f b hA z₁ t₁ hQ₁ 1 hT₁
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₂ z₁ (IsPullback.of_hasPullback z₁ z₂).flip
            (pullback.fst z₁ z₂ ≫ z₁) rfl
            (modificationLocalization C f b hA z₂
              (closedCoverRankChoose C (modificationProjectionAtInfinity f b ≫ f) t₂
                (pullback.fst (modificationProjectionAtInfinity f b) z₂)
                (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q₂ hQp₂)
                (range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂)
                (isZero_derivedPullback_inclusionAtInfinity C f b hzero₂) 2 two_pos))
            (supportedMul C (z₁ ≫ f) f z₁ rfl
              (modificationChernClass C f b hA z₁ t₁ hQ₁ 1 hT₁
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos))
              (modificationChernClass C f b hA z₁ t₁ hQ₁ 1 hT₁
                (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos)))) := by
  have hP₀₂ : PreservesInfinityGysinImage C f b z₂
      (modificationInfinityPowerSum C f b z₂ t₂ hT₂ hQ₂ 0 hzero₂) :=
    preservesInfinityGysinImage_modificationInfinityPowerSum C f b z₂ t₂ hT₂ hQ₂ 0
      hzero₂ hQp₂ hres₂ hfin₂
  have hγ₁ : ∀ p (hp : 0 < p), PreservesInfinityGysinImage C f b z₁
      (modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ p
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ hp)) := fun p hp ↦
    preservesInfinityGysinImage_modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ p _ hQp₁
      (exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _) hres₁ hp) hfin₁
  have hγ₂ : ∀ p (hp : 0 < p), PreservesInfinityGysinImage C f b z₂
      (modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ p
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ hp)) := fun p hp ↦
    preservesInfinityGysinImage_modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ p _ hQp₂
      (exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _) hres₂ hp) hfin₂
  refine (modificationChernClass_eq_modificationLocalization C f b hA _ _ _ 2 _ _).trans ?_
  refine (congrArg (modificationLocalization C f b hA (pullback.fst z₁ z₂ ≫ z₁))
    (modificationInfinityChernClass_two_derivedTensor C f b z₁ z₂ t₁ t₂ hQp₁ hQp₂ hQ₁ hQ₂ hT₁ hT₂
      hzero₁ hzero₂)).trans ?_
  rw [← modificationLocalizationAddHom_apply, map_add, map_add, map_add, map_add, map_sub]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_)
    (congrArg₂ (· - ·) ?_ ?_)) ?_
  · rw [modificationLocalizationAddHom_apply, modificationLocalization_bivariantClassDegreeCongr,
      modificationPowerSum_eq_modificationLocalization C f b hA z₁,
      modificationChernClass_eq_modificationLocalization C f b hA z₂,
      supportedIntersectionMul_modificationLocalization C f b hA z₁ z₂ _ _ (hγ₂ 2 two_pos)]
  · rw [modificationLocalizationAddHom_apply, modificationLocalization_bivariantClassDegreeCongr,
      modificationPowerSum_eq_modificationLocalization C f b hA z₂,
      modificationChernClass_eq_modificationLocalization C f b hA z₁,
      supportedIntersectionMul_flip_modificationLocalization C f b hA z₂ z₁ _ _ (hγ₁ 2 two_pos)]
  · rw [modificationLocalizationAddHom_apply, modificationLocalization_bivariantClassDegreeCongr,
      modificationChernClass_eq_modificationLocalization C f b hA z₂,
      supportedMul_modificationLocalization C f b hA z₂ _ _ (hγ₂ 1 one_pos),
      supportedIntersectionMul_modificationLocalization C f b hA z₁ z₂ _ _
        (PreservesInfinityGysinImage.supportedMul C f b z₂ (hγ₂ 1 one_pos) (hγ₂ 1 one_pos))]
  · rw [modificationLocalizationAddHom_apply, modificationLocalization_bivariantClassDegreeCongr,
      modificationPowerSum_eq_modificationLocalization C f b hA z₁,
      modificationPowerSum_eq_modificationLocalization C f b hA z₂,
      modificationChernClass_eq_modificationLocalization C f b hA z₂,
      modificationChernClass_eq_modificationLocalization C f b hA z₁,
      supportedIntersectionMul_modificationLocalization C f b hA z₁ z₂ _ _ hP₀₂,
      supportedIntersectionMul_flip_modificationLocalization C f b hA z₂ z₁ _ _ (hγ₁ 1 one_pos),
      supportedMul_modificationLocalization C f b hA (pullback.fst z₁ z₂ ≫ z₁) _ _
        (PreservesInfinityGysinImage.supportedIntersectionMul_flip C f b z₂ (hγ₂ 1 one_pos)
          (hγ₁ 1 one_pos))]
  · rw [modificationLocalizationAddHom_apply, modificationLocalization_bivariantClassDegreeCongr,
      modificationChernClass_eq_modificationLocalization C f b hA z₂,
      modificationChernClass_eq_modificationLocalization C f b hA z₁,
      supportedIntersectionMul_flip_modificationLocalization C f b hA z₂ z₁ _ _ (hγ₁ 1 one_pos)]
  · rw [modificationLocalizationAddHom_apply, modificationLocalization_bivariantClassDegreeCongr,
      modificationChernClass_eq_modificationLocalization C f b hA z₁,
      supportedMul_modificationLocalization C f b hA z₁ _ _ (hγ₁ 1 one_pos),
      supportedIntersectionMul_flip_modificationLocalization C f b hA z₂ z₁ _ _
        (PreservesInfinityGysinImage.supportedMul C f b z₁ (hγ₁ 1 one_pos) (hγ₁ 1 one_pos))]

end TensorChernTwo

section TensorFormulaChernTwo

variable (C : ChowSituation.{u}) {X Z₁ Z₂ Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (z₁ : Z₁ ⟶ X) [IsClosedImmersion z₁] (z₂ : Z₂ ⟶ X) [IsClosedImmersion z₂]
  {w₁ : Z ⟶ Z₁} {w₂ : Z ⟶ Z₂} (sq : IsPullback w₁ w₂ z₁ z₂) (z : Z ⟶ X) [IsClosedImmersion z]
  (hz : w₂ ≫ z₂ = z) {E₁ E₂ E : DerivedCategory X.Modules}
  (hE₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₁)
  (hE₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₂)
  (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
  (h₁ : IsZero ((derivedPullback (X.toRingedSpace.ofRestrict (⟨(Set.range z₁.base)ᶜ,
    z₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E₁))
  (h₂ : IsZero ((derivedPullback (X.toRingedSpace.ofRestrict (⟨(Set.range z₂.base)ᶜ,
    z₂.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E₂))
  (h : IsZero ((derivedPullback (X.toRingedSpace.ofRestrict (⟨(Set.range z.base)ᶜ,
    z.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E))
  (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₁))
  (hc₂ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₂))
  (hc : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E))
  (e : E ≅ ((derivedTensorProductFunctor X.sheaf).obj E₁).obj E₂)

/-- The transport along `Z ≅ Z₁ ×_X Z₂` of the product `res(a₁ a₂) ∘ (b₂ b₁)` of Stacks 0FA0 of two
products of Stacks 0FE5, the second for the flipped square, is the same product for the square
presenting `Z₁ ×_X Z₂`. -/
theorem bivariantTransport_supportedMul_supportedIntersectionMul {p₁ p₂ q₁ q₂ n : ℤ}
    (hn : p₁ + p₂ + (q₂ + q₁) = n)
    (a₁ : BivariantClass C (gysinSystemOfInvertible C) (z₁ ≫ f) f z₁ rfl p₁)
    (a₂ : BivariantClass C (gysinSystemOfInvertible C) (z₂ ≫ f) f z₂ rfl p₂)
    (b₂ : BivariantClass C (gysinSystemOfInvertible C) (z₂ ≫ f) f z₂ rfl q₂)
    (b₁ : BivariantClass C (gysinSystemOfInvertible C) (z₁ ≫ f) f z₁ rfl q₁) :
    bivariantTransport C (gysinSystemOfInvertible C) (z ≫ f) ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z
        rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback (isoPullback_hom_fst_comp_eq z₁ z₂ z sq hz)
        n (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantClassDegreeCongr C _ _ _ _ rfl hn
          (supportedMul C (z ≫ f) f z rfl (supportedIntersectionMul C f z₁ z₂ sq z hz a₁ a₂)
            (supportedIntersectionMul C f z₂ z₁ sq.flip z (sq.w.trans hz) b₂ b₁))) =
      bivariantClassDegreeCongr C _ _ _ _ rfl hn
        (supportedMul C ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f (pullback.fst z₁ z₂ ≫ z₁) rfl
          (supportedIntersectionMul C f z₁ z₂ (IsPullback.of_hasPullback z₁ z₂)
            (pullback.fst z₁ z₂ ≫ z₁) pullback.condition.symm a₁ a₂)
          (supportedIntersectionMul C f z₂ z₁ (IsPullback.of_hasPullback z₁ z₂).flip
            (pullback.fst z₁ z₂ ≫ z₁) rfl b₂ b₁)) := by
  have hθ := isoPullback_hom_fst_comp_eq z₁ z₂ z sq hz
  rw [bivariantTransport_bivariantClassDegreeCongr,
    bivariantTransport_supportedMul C f z (pullback.fst z₁ z₂ ≫ z₁) sq.isoPullback hθ,
    bivariantTransport_supportedIntersectionMul C f z₁ z₂ sq (IsPullback.of_hasPullback z₁ z₂)
      z hz _ pullback.condition.symm _ hθ,
    bivariantTransport_supportedIntersectionMul C f z₂ z₁ sq.flip
      (IsPullback.of_hasPullback z₁ z₂).flip z (sq.w.trans hz) _ rfl _ hθ]

include e in
/-- **The formula of Lemma 0FBF for `c_2` when the objects are complexes.** In the situation of
`Stacks.Chow.localizedChern_one_derivedTensor_of_isLocallyBoundedFiniteLocallyFree`, write
`r_i = P_0(Z_i ⟶ X, E_i)`, `γ_{i,p} = c_p(Z_i ⟶ X, E_i)` and `C(r_i, 2)` for the classes
`Stacks.Chow.LocalizedChernData.rankChoose`. Then

  `c_2(Z₁ ∩ Z₂ ⟶ X, E) = r₁ γ_{2,2} + r₂ γ_{1,2} + C(r₁, 2) γ_{2,1}² +
    ((r₁ r₂) (γ_{2,1} γ_{1,1}) - γ_{2,1} γ_{1,1}) + C(r₂, 2) γ_{1,1}²`

in `A^2(Z₁ ∩ Z₂ ⟶ X)`, the products of a class supported on `Z₂` with one supported on `Z₁` taken
for the flipped square, and the squares being the products of `Stacks.Chow.supportedMul`. -/
theorem localizedChern_two_derivedTensor_of_isLocallyBoundedFiniteLocallyFree :
    ((LocalizedChernData.ofIsZero C f z E hE h 2).toSituation hc).localizedChern
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z E hE h
          two_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₁ z₂ sq z hz
            (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).toSituation hc₁).localizedPowerSum
              h₁ 0)
            (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 2).toSituation hc₂).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂
                h₂ two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₂ z₁ sq.flip z (sq.w.trans hz)
            (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).toSituation hc₂).localizedPowerSum
              h₂ 0)
            (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 2).toSituation hc₁).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁
                h₁ two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₁ z₂ sq z hz
            ((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).rankChoose h₁ 2 two_pos)
            (supportedMul C (z₂ ≫ f) f z₂ rfl
              (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 1).toSituation hc₂).localizedChern
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂
                  h₂ one_pos))
              (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 1).toSituation hc₂).localizedChern
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂
                  h₂ one_pos)))) +
        (bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedMul C (z ≫ f) f z rfl
              (supportedIntersectionMul C f z₁ z₂ sq z hz
                (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).toSituation
                  hc₁).localizedPowerSum h₁ 0)
                (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).toSituation
                  hc₂).localizedPowerSum h₂ 0))
              (supportedIntersectionMul C f z₂ z₁ sq.flip z (sq.w.trans hz)
                (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 1).toSituation hc₂).localizedChern
                  (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂
                    h₂ one_pos))
                (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 1).toSituation hc₁).localizedChern
                  (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁
                    h₁ one_pos)))) -
          bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedIntersectionMul C f z₂ z₁ sq.flip z (sq.w.trans hz)
              (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 1).toSituation hc₂).localizedChern
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂
                  h₂ one_pos))
              (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 1).toSituation hc₁).localizedChern
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁
                  h₁ one_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₂ z₁ sq.flip z (sq.w.trans hz)
            ((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).rankChoose h₂ 2 two_pos)
            (supportedMul C (z₁ ≫ f) f z₁ rfl
              (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 1).toSituation hc₁).localizedChern
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁
                  h₁ one_pos))
              (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 1).toSituation hc₁).localizedChern
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁
                  h₁ one_pos)))) := by
  let S₁ := (LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).toSituation hc₁
  let S₂ := (LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).toSituation hc₂
  let b₁ := graphBlowupToBase f E₁ hE₁
  let b₂ := graphBlowupToBase f E₂ hE₂
  have hA : IsIso (pullback.snd (pullback.fst b₁ b₂ ≫ b₁) (projectiveLineAffineChart f)) :=
    isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart f b₁ b₂
      (isIso_pullback_snd_graphBlowupToBase f E₁ hE₁)
      (isIso_pullback_snd_graphBlowupToBase f E₂ hE₂)
  let b := pullback.fst b₁ b₂ ≫ b₁
  have : IsProper b₁ := isProper_graphBlowupToBase f E₁ hE₁
  have : IsProper b₂ := isProper_graphBlowupToBase f E₂ hE₂
  have : IsProper b := by
    dsimp only [b]
    infer_instance
  have hb₂ : pullback.snd b₁ b₂ ≫ b₂ = b := pullback.condition.symm
  have hfin₁ : LocalizedChernFiniteness C (modificationProjection f b ≫ f)
      ((derivedPullback (pullback.fst b₁ b₂).toLRSHom.toShHom).obj (graphObject f E₁ hE₁)) :=
    Or.inr (Or.inr (Or.inl (exists_isLocallyBoundedFiniteLocallyFree_derivedPullback _
      (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₁ hE₁ hc₁))))
  have hfin₂ : LocalizedChernFiniteness C (modificationProjection f b ≫ f)
      ((derivedPullback (pullback.snd b₁ b₂).toLRSHom.toShHom).obj (graphObject f E₂ hE₂)) :=
    Or.inr (Or.inr (Or.inl (exists_isLocallyBoundedFiniteLocallyFree_derivedPullback _
      (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₂ hE₂ hc₂))))
  let t₁ : _ ⟶ modificationFibreAtInfinity f b :=
    pullback.snd (S₁.graphZeroSubschemeι ≫ modificationInclusionAtInfinity f b₁)
      (modificationInclusionAtInfinity f b ≫ pullback.fst b₁ b₂)
  let t₂ : _ ⟶ modificationFibreAtInfinity f b :=
    pullback.snd (S₂.graphZeroSubschemeι ≫ modificationInclusionAtInfinity f b₂)
      (modificationInclusionAtInfinity f b ≫ pullback.snd b₁ b₂)
  have : IsClosedImmersion t₁ :=
    S₁.isClosedImmersion_pullbackSnd_graphZeroSubschemeι b (pullback.fst b₁ b₂)
  have : IsClosedImmersion t₂ :=
    S₂.isClosedImmersion_pullbackSnd_graphZeroSubschemeι b (pullback.snd b₁ b₂)
  have hT₁ := S₁.mem_range_pullbackSnd_graphZeroSubschemeι b _ rfl h₁
  have hT₂ := S₂.mem_range_pullbackSnd_graphZeroSubschemeι b _ hb₂ h₂
  have hzero₁ := S₁.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _ rfl
  have hzero₂ := S₂.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _ hb₂
  have key₁ : modificationPowerSum C f b hA z₁ t₁
      (S₁.hasDefinedChernClasses_graphObject.derivedPullback _) 0 hT₁ hzero₁ =
        S₁.localizedPowerSum h₁ 0 :=
    S₁.modificationPowerSum_derivedPullback_graphObject b hA (pullback.fst b₁ b₂) rfl hfin₁ h₁ 0
  have key₂ : modificationPowerSum C f b hA z₂ t₂
      (S₂.hasDefinedChernClasses_graphObject.derivedPullback _) 0 hT₂ hzero₂ =
        S₂.localizedPowerSum h₂ 0 :=
    S₂.modificationPowerSum_derivedPullback_graphObject b hA (pullback.snd b₁ b₂) hb₂ hfin₂ h₂ 0
  have key₁' : ∀ (p : ℕ) (hp : 0 < p), modificationChernClass C f b hA z₁ t₁
      (S₁.hasDefinedChernClasses_graphObject.derivedPullback _) p hT₁
      (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ hp) =
        ((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ p).toSituation hc₁).localizedChern
          (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁ h₁
            hp) := fun p hp ↦
    ((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ p).toSituation
      hc₁).modificationChernClass_derivedPullback_graphObject b hA (pullback.fst b₁ b₂) rfl hfin₁
      h₁ hp _
  have key₂' : ∀ (p : ℕ) (hp : 0 < p), modificationChernClass C f b hA z₂ t₂
      (S₂.hasDefinedChernClasses_graphObject.derivedPullback _) p hT₂
      (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ hp) =
        ((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ p).toSituation hc₂).localizedChern
          (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂ h₂
            hp) := fun p hp ↦
    ((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ p).toSituation
      hc₂).modificationChernClass_derivedPullback_graphObject b hA (pullback.snd b₁ b₂) hb₂ hfin₂
      h₂ hp _
  have hQp₁ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (pullback.fst b₁ b₂).toLRSHom.toShHom _ (isPerfect_graphObject C f E₁ hE₁)
  have hQp₂ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (pullback.snd b₁ b₂).toLRSHom.toShHom _ (isPerfect_graphObject C f E₂ hE₂)
  have hF₁ := nonempty_derivedPullback_affineChart_derivedPullback_iso f (pullback.fst b₁ b₂) rfl
    S₁.nonempty_derivedPullback_affineChart_graphObject
  have hF₂ := nonempty_derivedPullback_affineChart_derivedPullback_iso f (pullback.snd b₁ b₂) hb₂
    S₂.nonempty_derivedPullback_affineChart_graphObject
  have keyr₁ : modificationLocalization C f b hA z₁
      (closedCoverRankChoose C (modificationProjectionAtInfinity f b ≫ f) t₁
        (pullback.fst (modificationProjectionAtInfinity f b) z₁)
        (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ hQp₁)
        (range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁)
        (isZero_derivedPullback_inclusionAtInfinity C f b hzero₁) 2 two_pos) =
      (LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).rankChoose h₁ 2 two_pos :=
    S₁.toLocalizedChernData.modificationLocalization_closedCoverRankChoose h₁ b hA
      hQp₁ hF₁ 2 two_pos t₁ hT₁ hzero₁
  have keyr₂ : modificationLocalization C f b hA z₂
      (closedCoverRankChoose C (modificationProjectionAtInfinity f b ≫ f) t₂
        (pullback.fst (modificationProjectionAtInfinity f b) z₂)
        (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ hQp₂)
        (range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂)
        (isZero_derivedPullback_inclusionAtInfinity C f b hzero₂) 2 two_pos) =
      (LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).rankChoose h₂ 2 two_pos :=
    S₂.toLocalizedChernData.modificationLocalization_closedCoverRankChoose h₂ b hA
      hQp₂ hF₂ 2 two_pos t₂ hT₂ hzero₂
  have hres₁ := S₁.modificationRestriction_of_isZero b t₁ (modificationComplementOpens b z₁)
    (fun _ hw => S₁.modificationProjection_notMem_range hw) hQp₁ h₁ hF₁ hT₁ hzero₁
  have hres₂ := S₂.modificationRestriction_of_isZero b t₂ (modificationComplementOpens b z₂)
    (fun _ hw => S₂.modificationProjection_notMem_range hw) hQp₂ h₂ hF₂ hT₂ hzero₂
  have L2 := modificationChernClass_two_derivedTensor C f b z₁ z₂ t₁ t₂ hQp₁ hQp₂
    (S₁.hasDefinedChernClasses_graphObject.derivedPullback _)
    (S₂.hasDefinedChernClasses_graphObject.derivedPullback _) hT₁ hT₂ hzero₁ hzero₂ hA hres₁ hres₂
    hfin₁ hfin₂
  have htr := bivariantTransport_localizedChern_eq_modificationChernClass C f z₁ z₂ sq z hz hE hc
    e b hA t₁ t₂ hQp₁ hQp₂ (S₁.hasDefinedChernClasses_graphObject.derivedPullback _)
    (S₂.hasDefinedChernClasses_graphObject.derivedPullback _)
    (exists_isLocallyBoundedFiniteLocallyFree_derivedPullback _
      (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₁ hE₁ hc₁))
    (exists_isLocallyBoundedFiniteLocallyFree_derivedPullback _
      (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₂ hE₂ hc₂)) hF₁ hF₂
    hT₁ hT₂ hzero₁ hzero₂ two_pos h
  refine bivariantTransport_injective C (gysinSystemOfInvertible C) (z ≫ f)
    ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback
    (isoPullback_hom_fst_comp_eq z₁ z₂ z sq hz) _
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) ?_
  refine htr.trans (L2.trans ?_)
  simp only [bivariantTransport_add, bivariantTransport_sub,
    bivariantTransport_bivariantClassDegreeCongr_supportedIntersectionMul C f z₁ z₂ sq
      (IsPullback.of_hasPullback z₁ z₂) z hz _ pullback.condition.symm _ _ _ _ _,
    bivariantTransport_bivariantClassDegreeCongr_supportedIntersectionMul C f z₂ z₁ sq.flip
      (IsPullback.of_hasPullback z₁ z₂).flip z (sq.w.trans hz) (pullback.fst z₁ z₂ ≫ z₁) rfl
      _ _ _ _ _,
    bivariantTransport_supportedMul_supportedIntersectionMul C f z₁ z₂ sq z hz _ _ _ _ _,
    key₁, key₂, key₁' 1 one_pos, key₂' 1 one_pos, key₁' 2 two_pos, key₂' 2 two_pos]
  rw [← keyr₁, ← keyr₂]
  rfl

end TensorFormulaChernTwo

section DownstairsChernTwo

variable (C : ChowSituation.{u}) {X Z₁ Z₂ : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  (i₁ : Z₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₂]
  {F₁ F₂ : DerivedCategory X.Modules}
  (hF₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₁)
  (hF₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₂)
  (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₁.base)ᶜ,
        i₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₁))
  (h₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₂.base)ᶜ,
        i₂.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₂))
  (hE₁ : HasDefinedChernClasses F₁) (hE₂ : HasDefinedChernClasses F₂)
  (hE : HasDefinedChernClasses (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂))

/-- **The formula of Lemma 0FBF for `c_2`, for the classes of Remark 0GUK.** Let `Z₁, Z₂ ⊆ X` be
closed and `F₁, F₂ ∈ D(𝒪_X)` perfect with `F_i|_{X ∖ Z_i}` zero and with defined Chern classes,
and write `r_i = P_0(Z_i ⟶ X, F_i)`, `γ_{i,p} = c_p(Z_i ⟶ X, F_i)` and `C(r_i, 2)` for the classes
`Stacks.Chow.LocalizedChernData.rankChoose`. Then

  `c_2(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ γ_{2,2} + r₂ γ_{1,2} + C(r₁, 2) γ_{2,1}² +
    ((r₁ r₂) (γ_{2,1} γ_{1,1}) - γ_{2,1} γ_{1,1}) + C(r₂, 2) γ_{1,1}²`

in `A^2(Z₁ ∩ Z₂ ⟶ X)`, for `Z₁ ∩ Z₂ = Z₁ ×_X Z₂`, the products of a class supported on `Z₂` with
one supported on `Z₁` taken for `Z₁ ∩ Z₂` presented as `Z₂ ×_X Z₁` through the flipped square,
and the squares being the products of `Stacks.Chow.supportedMul`. -/
theorem LocalizedChernData.localizedChern_two_derivedTensorOfIsZero :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 2).localizedChern hE
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
          (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) two_pos) =
      ((bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ 0)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 2).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ 0)
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 2).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).rankChoose h₁ 2 two_pos)
            (supportedMul C (i₂ ≫ a) a i₂ rfl
              ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
              ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos)))) +
        (bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedMul C ((pullback.snd i₁ i₂ ≫ i₂) ≫ a) a (pullback.snd i₁ i₂ ≫ i₂) rfl
              (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ 0)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ 0))
              (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))) -
          bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).rankChoose h₂ 2 two_pos)
            (supportedMul C (i₁ ≫ a) a i₁ rfl
              ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos))
              ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))))) := by
  let H := hE₁.some.tensor hE₂.some
  have hc₁ := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree
    (hE₁.some.tensorLeft hE₂.some)
  have hc₂ := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree
    (hE₁.some.tensorRight hE₂.some)
  have hc := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree H
  have hY := localizedChern_two_derivedTensor_of_isLocallyBoundedFiniteLocallyFree C (H.f ≫ a)
      (pullback.snd i₁ H.f) (pullback.snd i₂ H.f)
      (isPullback_pullbackMap_of_isPullback i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
        (pullback.snd i₁ i₂ ≫ i₂) rfl H.f)
      (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) H.f) (by simp)
      (LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0 |>.pullback H.f).perfect
      (LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0 |>.pullback H.f).perfect
      (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0 |>.pullback H.f).perfect
      (LocalizedChernData.IsZeroOnComplement.pullback
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0) (f := H.f) h₁)
      (LocalizedChernData.IsZeroOnComplement.pullback
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0) (f := H.f) h₂)
      (LocalizedChernData.IsZeroOnComplement.pullback
        (D := LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0) (f := H.f)
        (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂)) hc₁ hc₂ hc
      (derivedPullbackDerivedTensorIso H.f F₁ F₂)
  refine localizedChern_two_derivedTensor_of_isEnvelope C a i₁ i₂ hF₁ hF₂ h₁ h₂ H.f hE₁ hE₂ hE
    H.envelope hc₁ hc₂ hc (hY.trans ?_)
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl rfl) rfl)
    (congrArg₂ (· - ·) rfl rfl)) rfl

end DownstairsChernTwo

end Stacks.Chow

end

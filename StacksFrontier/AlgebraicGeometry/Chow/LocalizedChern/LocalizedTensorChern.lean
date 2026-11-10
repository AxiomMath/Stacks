module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedTensorFormula

/-!
# The first localized Chern class of a derived tensor product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z₁, Z₂ ⊆ X` be closed subschemes and let `F₁, F₂ ∈ D(𝒪_X)` be perfect
with `F_i|_{X ∖ Z_i}` zero. Lemma 0FBF computes the first localized Chern class of `F₁ ⊗^L F₂`:

  `c_1(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ c_1(Z₂ ⟶ X, F₂) + r₂ c_1(Z₁ ⟶ X, F₁)`

in `A^1(Z₁ ∩ Z₂ ⟶ X)`, with `r_i = P_0(Z_i ⟶ X, F_i)`.

The proof is that of the power sum classes
(`StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedTensorFormula`): on a modification
`b : W ⟶ 𝐏¹_X` the class `c'_1(Q₁ ⊗^L Q₂)` of Stacks 0F9K is the localization of the class of
Stacks 0F9H on `W_∞`, which Stacks 0FE5 expands, and the localization of a product is the product
of the localizations (Stacks 0FE7); Stacks 0FE8 identifies the classes on the common modification
of the graph constructions with the localized classes, and the formula descends from an envelope.

## Main results

* `Stacks.Chow.modificationChernClass_one_derivedTensor` — the formula for `c'_1(Q₁ ⊗^L Q₂)` on
  one modification.
* `Stacks.Chow.localizedChern_one_derivedTensor_of_isLocallyBoundedFiniteLocallyFree` — the
  formula when the three objects are complexes.
* `Stacks.Chow.LocalizedChernData.localizedChern_one_derivedTensorOfIsZero` — the formula for the
  classes of Remark 0GUK.
* `Stacks.Chow.bivariantTransport_modificationLocalization` — the localization
  `a ↦ (E ⟶ Y)_* ∘ a ∘ C` commutes with transport along an isomorphism of closed subschemes.
* `Stacks.Chow.supportedIntersectionMul_flip_modificationLocalization` — Stacks 0FE7 for the
  flipped square.

## Implementation notes

The second summand `r₂ c_1(Z₁ ⟶ X, F₁)` is a product of a class supported on `Z₂` with one
supported on `Z₁`, so it is taken for `Z₁ ∩ Z₂` presented as `Z₂ ×_X Z₁` through the flip of the
square presenting `Z₁ ∩ Z₂`, as in `Stacks.Chow.localizedChern_one_derivedTensor_of_isEnvelope`.
Stacks 0FE7 is available for the standard square
(`Stacks.Chow.supportedIntersectionMul_modificationLocalization`); the flipped square is reached by
transporting along `Z₁ ×_X Z₂ ≅ Z₂ ×_X Z₁`, through which the localization and the products commute
(`Stacks.Chow.bivariantTransport_modificationLocalization`,
`Stacks.Chow.bivariantTransport_supportedIntersectionMul`).

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
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

section TransportProduct

variable (C : ChowSituation.{u}) {X Z₁ Z₂ W W' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] {w₁ : W ⟶ Z₁} {w₂ : W ⟶ Z₂} (sq : IsPullback w₁ w₂ f₁ f₂)
  {w₁' : W' ⟶ Z₁} {w₂' : W' ⟶ Z₂} (sq' : IsPullback w₁' w₂' f₁ f₂)
  (iW : W ⟶ X) [LocallyOfFiniteType iW] (hW : w₂ ≫ f₂ = iW)
  (iW' : W' ⟶ X) [LocallyOfFiniteType iW'] [Mono iW'] (hW' : w₂' ≫ f₂ = iW') {p q : ℤ}

/-- `Stacks.Chow.bivariantTransport_supportedIntersectionMul`, for the product read in an equal
degree. -/
theorem bivariantTransport_bivariantClassDegreeCongr_supportedIntersectionMul (θ : W ≅ W')
    (hθ : θ.hom ≫ iW' = iW) {r : ℤ} (hr : p + q = r)
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    bivariantTransport C (gysinSystemOfInvertible C) (iW ≫ sX) (iW' ≫ sX) sX iW rfl iW' rfl θ hθ r
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantClassDegreeCongr C _ _ _ _ rfl hr
          (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂)) =
      bivariantClassDegreeCongr C _ _ _ _ rfl hr
        (supportedIntersectionMul C sX f₁ f₂ sq' iW' hW' c₁ c₂) := by
  rw [bivariantTransport_bivariantClassDegreeCongr,
    bivariantTransport_supportedIntersectionMul C sX f₁ f₂ sq sq' iW hW iW' hW' θ hθ]

end TransportProduct

section LocalizationTransport

variable (C : ChowSituation.{u}) {X W Y Y' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (y : Y ⟶ X) [IsClosedImmersion y] (y' : Y' ⟶ X) [IsClosedImmersion y'] (θ : Y ≅ Y')
  (hθ : θ.hom ≫ y' = y)

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion y] [IsClosedImmersion y'] in
include hθ in
/-- The isomorphism `W_∞ ×_X Y ≅ W_∞ ×_X Y'` induced by `θ : Y ≅ Y'` over `X` lies over `W_∞`. -/
@[reassoc]
theorem pullbackSymmetry_transportPullbackIso_hom_fst :
    (pullbackSymmetry (modificationProjectionAtInfinity f b) y ≪≫
        transportPullbackIso y y' θ hθ (modificationProjectionAtInfinity f b) ≪≫
        (pullbackSymmetry (modificationProjectionAtInfinity f b) y').symm).hom ≫
        pullback.fst (modificationProjectionAtInfinity f b) y' =
      pullback.fst (modificationProjectionAtInfinity f b) y := by
  simp

/-- **Localization commutes with transport.** For an isomorphism `θ : Y ≅ Y'` of closed
subschemes of `X` over `X`, the transport along `θ` of the localization `(E ⟶ Y)_* ∘ a ∘ C` is the
localization of the transport of `a` along the induced `W_∞ ×_X Y ≅ W_∞ ×_X Y'`. -/
theorem bivariantTransport_modificationLocalization {m : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m) :
    bivariantTransport C (gysinSystemOfInvertible C) (y ≫ f) (y' ≫ f) f y rfl y' rfl θ hθ m
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (modificationLocalization C f b hA y a) =
      modificationLocalization C f b hA y'
        (bivariantTransport C (gysinSystemOfInvertible C) _ _ _ _ rfl _ rfl
          (pullbackSymmetry (modificationProjectionAtInfinity f b) y ≪≫
            transportPullbackIso y y' θ hθ (modificationProjectionAtInfinity f b) ≪≫
            (pullbackSymmetry (modificationProjectionAtInfinity f b) y').symm)
          (pullbackSymmetry_transportPullbackIso_hom_fst C f b y y' θ hθ) m
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {V} g _ k α ↦ ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply, modificationLocalization_cap,
    modificationLocalization_cap, bivariantTransport_cap, bivariantTransportCap_apply,
    chowGroupDegreeEquiv_chowPushforwardOfIso]
  change chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) =
    chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _)
  rw [chowPush_comp C _ _ _ _ _ _ rfl, chowPush_comp C _ _ _ _ _ _ rfl]
  · refine chowPush_congr C _ _ ?_ _ _ _ _
    refine pullback.hom_ext ?_ ?_
    · simp [transportPullbackIso]
    · simp [transportPullbackIso]
  all_goals first
    | rw [Category.assoc, transportPullbackIso_hom_fst_assoc, reassoc_of% hθ]
      exact pullbackFstTestMap_comp_over y g
    | rw [Category.assoc, pullbackFstTestMap_comp_over, transportPullbackIso_hom_fst_assoc,
        pullbackSymmetry_transportPullbackIso_hom_fst_assoc]

end LocalizationTransport

section FlippedSquare

/-- The second leg of the flipped square of `Stacks.Chow.isPullback_pullbackFstTestIso`, followed
by `A ×_X Y ⟶ A`, is `A ×_X (Y ×_X Z) ⟶ A`. -/
theorem pullbackFstTestIso_inv_fst_comp_fst {A X Y Z : Scheme.{u}} (y : Y ⟶ X) (z : Z ⟶ X)
    (w : A ⟶ X) :
    ((pullbackFstTestIso w y z).inv ≫ pullback.fst _ _) ≫ pullback.fst w y =
      pullback.fst w (pullback.fst y z ≫ y) := by
  rw [Category.assoc]
  exact pullbackFstTestIso_inv_fst_fst w y z

end FlippedSquare

section Localization

variable (C : ChowSituation.{u}) {X W Z Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- The class `c'_p(Q)` of Stacks 0F9K is the localization of the class `c'_p(Q|_E)` of
Stacks 0F9H. -/
theorem modificationChernClass_eq_modificationLocalization {T : Scheme.{u}} (z : Z ⟶ X)
    [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    modificationChernClass C f b hA z t hQ p hT hrank =
      modificationLocalization C f b hA z
        (modificationInfinityChernClass C f b z t hT hQ p hrank) :=
  (localizedModificationClass_eq_modificationLocalization C f b hA z t hT _).trans
    (by rw [modificationExtension_perfectChernClass])

/-- **The product of two localizations, for the flipped square** (Stacks 0FE7). As
`Stacks.Chow.supportedIntersectionMul_modificationLocalization`, for `Z ∩ Y` presented as
`Y ×_X Z` mapping to `X` through `Y`, and the product over `W_∞` for the corresponding square. -/
theorem supportedIntersectionMul_flip_modificationLocalization (z : Z ⟶ X) [IsClosedImmersion z]
    (y : Y ⟶ X) [IsClosedImmersion y] {p m : ℤ}
    (e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p)
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m)
    (ha : PreservesInfinityGysinImage C f b y a) :
    supportedIntersectionMul C f z y (IsPullback.of_hasPullback y z).flip (pullback.fst y z ≫ y)
        rfl (modificationLocalization C f b hA z e) (modificationLocalization C f b hA y a) =
      modificationLocalization C f b hA (pullback.fst y z ≫ y)
        (supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
          (pullback.fst (modificationProjectionAtInfinity f b) z)
          (pullback.fst (modificationProjectionAtInfinity f b) y)
          (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z y).flip
          (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst y z ≫ y))
          (pullbackFstTestIso_inv_fst_comp_fst y z _) e a) := by
  have hσ : (pullbackSymmetry z y).hom ≫ pullback.fst y z ≫ y = pullback.fst z y ≫ z := by
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]
  rw [← bivariantTransport_supportedIntersectionMul C f z y (IsPullback.of_hasPullback z y)
      (IsPullback.of_hasPullback y z).flip _ pullback.condition.symm _ rfl
      (pullbackSymmetry z y) hσ,
    supportedIntersectionMul_modificationLocalization C f b hA z y e a ha,
    bivariantTransport_modificationLocalization]
  congr 1
  exact bivariantTransport_supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) z)
    (pullback.fst (modificationProjectionAtInfinity f b) y)
    (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) y z)
    (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z y).flip
    (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z y ≫ z))
    (pullbackFstTestIso_inv_snd_fst (modificationProjectionAtInfinity f b) y z)
    (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst y z ≫ y))
    (pullbackFstTestIso_inv_fst_comp_fst y z _) _ _ e a

end Localization

/-- If `A` restricts along `f` to `A'`, then the component of degree `p` of the restriction of `A`
along `h = w ≫ f` restricts along `w` to the component of degree `p` of `A'`. -/
private theorem isRestriction_res_of_res_eq {C : ChowSituation.{u}} {X Z W : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] (A : TotalChowClass C sX) (f : Z ⟶ X)
    [LocallyOfFiniteType f] (w : W ⟶ Z) [LocallyOfFiniteType w] (h : W ⟶ X)
    [LocallyOfFiniteType h] (hw : w ≫ f = h) (p : ℕ) {A' : TotalChowClass C (f ≫ sX)}
    (hA : TotalChowClass.res f rfl A = A') :
    BivariantClass.IsRestriction (TotalChowClass.res h rfl A p) (A' p) w :=
  hA ▸ TotalChowClass.isRestriction_res_res A f w h hw p

section TensorChern

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
  (hzero₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (t₁ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₁))
  (hzero₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (t₂ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₂))

/-- **Stacks 0FE5 on `W_∞` for `c'_1((Q₁ ⊗^L Q₂)|_{E₁ ∩ E₂})`.** On the fibre at infinity, along
the closed cover `W_∞ = (T₁ ∪ T₂) ∪ (E₁ ∩ E₂)`, the class `c'_1((Q₁ ⊗^L Q₂)|_{E₁ ∩ E₂})` of
Stacks 0F9H is `P'_0(Q₁|_{E₁}) c'_1(Q₂|_{E₂}) + P'_0(Q₂|_{E₂}) c'_1(Q₁|_{E₁})`, the second product
taken for `E₁ ∩ E₂` presented as `E₂ ×_{W_∞} E₁`. -/
theorem modificationInfinityChernClass_one_derivedTensor :
    modificationInfinityChernClass C f b (pullback.fst z₁ z₂ ≫ z₁)
        (reducedUnionIdeal t₁ t₂).subschemeι
        (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
        (hasDefinedChernClasses_derivedTensor hQ₁ hQ₂) 1
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂)
          one_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (modificationInfinityMul C f b z₁ z₂
            (modificationInfinityPowerSum C f b z₁ t₁ hT₁ hQ₁ 0 hzero₁)
            (modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ 1
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
            (pullback.fst (modificationProjectionAtInfinity f b) z₂)
            (pullback.fst (modificationProjectionAtInfinity f b) z₁)
            (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z₂ z₁).flip
            (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z₁ z₂ ≫ z₁))
            (pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ _)
            (modificationInfinityPowerSum C f b z₂ t₂ hT₂ hQ₂ 0 hzero₂)
            (modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ 1
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos))) := by
  set π := modificationProjectionAtInfinity f b
  set ι := modificationInclusionAtInfinity f b
  set iW := pullback.fst π (pullback.fst z₁ z₂ ≫ z₁)
  have hQ := hasDefinedChernClasses_derivedTensor hQ₁ hQ₂
  have hsι : ι ≫ (modificationProjection f b ≫ f) = π ≫ f := (Category.assoc _ _ _).symm
  have hD : perfectChernClass C (iW ≫ π ≫ f) ((hQ.derivedPullback ι).derivedPullback iW) 1 =
      bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((TotalChowClass.res iW rfl (perfectPowerSum C (π ≫ f) (hQ₁.derivedPullback ι) 0)
            0).mulId C (iW ≫ π ≫ f)
            (TotalChowClass.res iW rfl (perfectChernClass C (π ≫ f) (hQ₂.derivedPullback ι)) 1)) +
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((TotalChowClass.res iW rfl (perfectPowerSum C (π ≫ f) (hQ₂.derivedPullback ι) 0)
            0).mulId C (iW ≫ π ≫ f)
            (TotalChowClass.res iW rfl (perfectChernClass C (π ≫ f) (hQ₁.derivedPullback ι))
              1)) := by
    rw [← res_perfectChernClass_derivedPullback_of_comp_eq C (π ≫ f) (hQ.derivedPullback ι) iW rfl,
      ← res_perfectChernClass_derivedPullback_of_comp_eq C (modificationProjection f b ≫ f) hQ ι
        hsι,
      ← TotalChowClass.res_homPart_apply_self, ← TotalChowClass.res_homComponent,
      perfectChernClass_derivedTensor_one C _ hQ₁ hQ₂ hQ, map_add, map_add,
      TotalChowClass.add_apply, map_mul, map_mul, map_mul, map_mul]
    simp only [TotalChowClass.res_homComponent]
    rw [res_perfectPowerSum_derivedPullback C _ hQ₁ ι hsι (hQ₁.derivedPullback ι),
      res_perfectPowerSum_derivedPullback C _ hQ₂ ι hsι (hQ₂.derivedPullback ι),
      res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ₁ ι hsι (hQ₁.derivedPullback ι),
      res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ₂ ι hsι (hQ₂.derivedPullback ι),
      ((isHomogeneous_perfectPowerSum C (π ≫ f) (hQ₁.derivedPullback ι) 0).res iW rfl).mul_apply
        _ (zero_add 1),
      ((isHomogeneous_perfectPowerSum C (π ≫ f) (hQ₂.derivedPullback ι) 0).res iW rfl).mul_apply
        _ (zero_add 1)]
    simp only [TotalChowClass.homComponent_apply, ite_eq_left]
  refine IsClosedCoverExtension.eq (range_union_range_pullbackFst_eq_univ _ _
      (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂))
    (isClosedCoverExtension_closedCoverChernClass C (π ≫ f) _ iW _ rfl _ _ _ _) ?_
  rw [hD]
  have hw₁ : ((pullbackFstTestIso π z₁ z₂).inv ≫ pullback.fst _ _) ≫ pullback.fst π z₁ = iW :=
    pullbackFstTestIso_inv_fst_comp_fst z₁ z₂ π
  have hw₂ : ((pullbackFstTestIso π z₁ z₂).inv ≫ pullback.snd _ _) ≫ pullback.fst π z₂ = iW :=
    pullbackFstTestIso_inv_snd_fst π z₂ z₁
  have hP₁ := isRestriction_res_of_res_eq _ _ _ iW hw₁ 0
    (res_perfectPowerSum_derivedPullback C (π ≫ f) (hQ₁.derivedPullback ι) (pullback.fst π z₁)
      rfl ((hQ₁.derivedPullback ι).derivedPullback (pullback.fst π z₁)) 0)
  have hP₂ := isRestriction_res_of_res_eq _ _ _ iW hw₂ 0
    (res_perfectPowerSum_derivedPullback C (π ≫ f) (hQ₂.derivedPullback ι) (pullback.fst π z₂)
      rfl ((hQ₂.derivedPullback ι).derivedPullback (pullback.fst π z₂)) 0)
  have hc₁ := isRestriction_res_of_res_eq _ _ _ iW hw₁ 1
    (res_perfectChernClass_derivedPullback_of_comp_eq C (π ≫ f) (hQ₁.derivedPullback ι)
      (pullback.fst π z₁) rfl ((hQ₁.derivedPullback ι).derivedPullback (pullback.fst π z₁)))
  have hc₂ := isRestriction_res_of_res_eq _ _ _ iW hw₂ 1
    (res_perfectChernClass_derivedPullback_of_comp_eq C (π ≫ f) (hQ₂.derivedPullback ι)
      (pullback.fst π z₂) rfl ((hQ₂.derivedPullback ι).derivedPullback (pullback.fst π z₂)))
  refine IsClosedCoverExtension.add
    (IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _ ?_)
    (IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _ ?_)
  · exact IsClosedCoverExtension.supportedIntersectionMul _
      (isClosedCoverExtension_closedCoverPowerSum C (π ≫ f) t₁ (pullback.fst π z₁) _ rfl _ _
        (range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁) _)
      (isClosedCoverExtension_closedCoverChernClass C (π ≫ f) t₂ (pullback.fst π z₂) _ rfl _ _
        (range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂) _) hP₁ hc₂
      (range_subschemeι_reducedUnionIdeal t₁ t₂).subset
  · exact IsClosedCoverExtension.supportedIntersectionMul _
      (isClosedCoverExtension_closedCoverPowerSum C (π ≫ f) t₂ (pullback.fst π z₂) _ rfl _ _
        (range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂) _)
      (isClosedCoverExtension_closedCoverChernClass C (π ≫ f) t₁ (pullback.fst π z₁) _ rfl _ _
        (range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁) _) hP₂ hc₁
      ((range_subschemeι_reducedUnionIdeal t₁ t₂).subset.trans (Set.union_comm _ _).subset)

variable (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- **The class `c'_1(Q₁ ⊗^L Q₂)` of Stacks 0F9K** (the second paragraph of the proof of
Stacks 0FBF). In the situation of `Stacks.Chow.modificationPowerSum_derivedTensor`, with both
`Q₁` and `Q₂` zero on `W ∖ W_{Z_i}` and satisfying condition (3) of Situation 0GUJ,

  `c'_1(Q₁ ⊗^L Q₂) = P'_0(Q₁) c'_1(Q₂) + P'_0(Q₂) c'_1(Q₁)`

in `A^1(Z₁ ∩ Z₂ ⟶ X)`, the second product taken for `Z₁ ∩ Z₂` presented as `Z₂ ×_X Z₁`
through the flipped square. -/
theorem modificationChernClass_one_derivedTensor
    (hres₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (W.toRingedSpace.ofRestrict (modificationComplementOpens b z₁).isOpenEmbedding)).obj Q₁))
    (hres₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (W.toRingedSpace.ofRestrict (modificationComplementOpens b z₂).isOpenEmbedding)).obj Q₂))
    (hfin₁ : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q₁)
    (hfin₂ : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q₂) :
    modificationChernClass C f b hA (pullback.fst z₁ z₂ ≫ z₁) (reducedUnionIdeal t₁ t₂).subschemeι
        (hasDefinedChernClasses_derivedTensor hQ₁ hQ₂) 1
        (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂)
          one_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₁ z₂ (IsPullback.of_hasPullback z₁ z₂)
            (pullback.fst z₁ z₂ ≫ z₁) pullback.condition.symm
            (modificationPowerSum C f b hA z₁ t₁ hQ₁ 0 hT₁ hzero₁)
            (modificationChernClass C f b hA z₂ t₂ hQ₂ 1 hT₂
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₂ one_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₂ z₁ (IsPullback.of_hasPullback z₁ z₂).flip
            (pullback.fst z₁ z₂ ≫ z₁) rfl
            (modificationPowerSum C f b hA z₂ t₂ hQ₂ 0 hT₂ hzero₂)
            (modificationChernClass C f b hA z₁ t₁ hQ₁ 1 hT₁
              (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero₁ one_pos))) := by
  refine (modificationChernClass_eq_modificationLocalization C f b hA _ _ _ 1 _ _).trans ?_
  refine (congrArg (modificationLocalization C f b hA (pullback.fst z₁ z₂ ≫ z₁))
    (modificationInfinityChernClass_one_derivedTensor C f b z₁ z₂ t₁ t₂ hQp₁ hQp₂ hQ₁ hQ₂ hT₁ hT₂
      hzero₁ hzero₂)).trans ?_
  rw [← modificationLocalizationAddHom_apply, map_add,
    modificationLocalizationAddHom_apply, modificationLocalizationAddHom_apply,
    modificationLocalization_bivariantClassDegreeCongr,
    modificationLocalization_bivariantClassDegreeCongr,
    modificationPowerSum_eq_modificationLocalization C f b hA z₁,
    modificationPowerSum_eq_modificationLocalization C f b hA z₂,
    modificationChernClass_eq_modificationLocalization C f b hA z₁,
    modificationChernClass_eq_modificationLocalization C f b hA z₂,
    supportedIntersectionMul_modificationLocalization C f b hA z₁ z₂ _ _
      (preservesInfinityGysinImage_modificationInfinityChernClass C f b z₂ t₂ hT₂ hQ₂ 1 _ hQp₂
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _) hres₂ one_pos) hfin₂),
    supportedIntersectionMul_flip_modificationLocalization C f b hA z₂ z₁ _ _
      (preservesInfinityGysinImage_modificationInfinityChernClass C f b z₁ t₁ hT₁ hQ₁ 1 _ hQp₁
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _) hres₁ one_pos) hfin₁)]

end TensorChern

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) {W : Scheme.{u}} (b : W ⟶ projectiveLineProduct S.a)
  [IsProper b] (hA : IsIso (pullback.snd b (projectiveLineAffineChart S.a)))
  (g : W ⟶ graphBlowup S.a S.E S.perfect) (hb : g ≫ graphBlowupToBase S.a S.E S.perfect = b)
  (hfin : LocalizedChernFiniteness S.base (modificationProjection S.a b ≫ S.a)
    ((derivedPullback g.toLRSHom.toShHom).obj (graphObject S.a S.E S.perfect)))

include hb hfin in
/-- **The class `c_p(Z ⟶ X, E)` of Stacks 0FB2 on a modification dominating the graph
construction** (Stacks 0FE8), when `E|_{X ∖ Z}` is zero and `p ≥ 1`: as
`Stacks.Chow.LocalizedSituation.modificationPowerSum_derivedPullback_graphObject`, for the
class `c'_p` of Stacks 0F9K. -/
theorem modificationChernClass_derivedPullback_graphObject (h : S.IsZeroOnComplement)
    (hp : 0 < S.p) (h' : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    modificationChernClass S.base S.a b hA S.i
        (pullback.snd (S.graphZeroSubschemeι ≫
          modificationInclusionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect))
          (modificationInclusionAtInfinity S.a b ≫ g))
        (S.hasDefinedChernClasses_graphObject.derivedPullback g) S.p
        (S.mem_range_pullbackSnd_graphZeroSubschemeι b g hb h)
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (S.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b g) hp) =
      S.localizedChern h' :=
  S.modificationChernClass_eq_localizedChern b hA _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _
      (isPerfect_graphObject S.base S.a S.E S.perfect)) hfin
    (nonempty_derivedPullback_affineChart_derivedPullback_iso S.a g hb
      S.nonempty_derivedPullback_affineChart_graphObject) _ _ h'

end LocalizedSituation

section TensorSide

variable (C : ChowSituation.{u}) {X Z₁ Z₂ Z W T₁ T₂ : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f]
  (z₁ : Z₁ ⟶ X) [IsClosedImmersion z₁] (z₂ : Z₂ ⟶ X) [IsClosedImmersion z₂]
  {w₁ : Z ⟶ Z₁} {w₂ : Z ⟶ Z₂} (sq : IsPullback w₁ w₂ z₁ z₂) (z : Z ⟶ X) [IsClosedImmersion z]
  (hz : w₂ ≫ z₂ = z) {E₁ E₂ E : DerivedCategory X.Modules}
  (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
  (hc : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E))
  (e : E ≅ ((derivedTensorProductFunctor X.sheaf).obj E₁).obj E₂)
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (t₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₁]
  (t₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₂]
  {Q₁ Q₂ : DerivedCategory W.Modules}
  (hQp₁ : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q₁)
  (hQp₂ : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q₂)
  (hQ₁ : HasDefinedChernClasses Q₁) (hQ₂ : HasDefinedChernClasses Q₂)
  (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} W.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ Q₁))
  (hc₂ : ∃ P : CochainComplex (OXMod.{u, u, u} W.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ Q₂))
  (hF₁ : Nonempty ((derivedPullback
      (pullback.fst b (projectiveLineAffineChart f)).toLRSHom.toShHom).obj Q₁ ≅
    (derivedPullback (pullback.fst b (projectiveLineAffineChart f) ≫
      modificationProjection f b).toLRSHom.toShHom).obj E₁))
  (hF₂ : Nonempty ((derivedPullback
      (pullback.fst b (projectiveLineAffineChart f)).toLRSHom.toShHom).obj Q₂ ≅
    (derivedPullback (pullback.fst b (projectiveLineAffineChart f) ≫
      modificationProjection f b).toLRSHom.toShHom).obj E₂))
  (hT₁ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₁ → w ∈ Set.range t₁)
  (hT₂ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₂ → w ∈ Set.range t₂)
  (hzero₁ : IsZero ((derivedPullback
    (t₁ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₁))
  (hzero₂ : IsZero ((derivedPullback
    (t₂ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₂))

omit [IsClosedImmersion z₁] [IsClosedImmersion z₂] [IsClosedImmersion z] in
/-- The comparison `Z ≅ Z₁ ×_X Z₂` of a pullback square is an isomorphism over `X`, the fibre
product mapping to `X` through `Z₁`. -/
theorem isoPullback_hom_fst_comp_eq (sq : IsPullback w₁ w₂ z₁ z₂) (hz : w₂ ≫ z₂ = z) :
    sq.isoPullback.hom ≫ pullback.fst z₁ z₂ ≫ z₁ = z := by
  rw [IsPullback.isoPullback_hom_fst_assoc, sq.w, hz]

include e hc₁ hc₂ hF₁ hF₂ in
/-- **`c_p(Z₁ ∩ Z₂ ⟶ X, E)` for `E ≅ E₁ ⊗^L E₂` on a common modification** (Stacks 0FE8). Let
`b : W ⟶ 𝐏¹_X`, `Q_i` and `T_i` be data of Stacks 0F9K for `E_i`, with `Q_i` represented by
locally bounded complexes of finite locally free modules. The transport of the localized Chern
class `c_p(Z₁ ∩ Z₂ ⟶ X, E)` of Stacks 0FB2 along `Z₁ ∩ Z₂ ≅ Z₁ ×_X Z₂` is the class `c'_p` of
Stacks 0F9K of `Q₁ ⊗^L Q₂` and `T₁ ∪ T₂`. -/
theorem bivariantTransport_localizedChern_eq_modificationChernClass {p : ℕ} (hp : 0 < p)
    (h : IsZero ((derivedPullback (X.toRingedSpace.ofRestrict (⟨(Set.range z.base)ᶜ,
      z.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E)) :
    bivariantTransport C (gysinSystemOfInvertible C) (z ≫ f) ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z
        rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback
        (isoPullback_hom_fst_comp_eq z₁ z₂ z sq hz) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (((LocalizedChernData.ofIsZero C f z E hE h p).toSituation hc).localizedChern
          (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z E hE h hp)) =
      modificationChernClass C f b hA (pullback.fst z₁ z₂ ≫ z₁) (reducedUnionIdeal t₁ t₂).subschemeι
        (hasDefinedChernClasses_derivedTensor hQ₁ hQ₂) p
        (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂)
          hp) := by
  let S := (LocalizedChernData.ofIsZero C f z E hE h p).toSituation hc
  have hθ := isoPullback_hom_fst_comp_eq z₁ z₂ z sq hz
  have hS : S.IsFiniteLocallyFreeOfRankLTOnComplement :=
    LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z E hE h hp
  let S' := S.withLargerClosed (pullback.fst z₁ z₂ ≫ z₁) sq.isoPullback.hom hθ
  have h' : S'.IsFiniteLocallyFreeOfRankLTOnComplement :=
    LocalizedSituation.IsFiniteLocallyFreeOfRankLTOnComplement.withLargerClosed (S := S) hS
  have hF : Nonempty _ := (nonempty_derivedPullback_derivedTensor_iso _ _ hF₁ hF₂).map
    (· ≪≫ (derivedPullback _).mapIso e.symm)
  have : IsProper (show _ ⟶ projectiveLineProduct S'.a from b) := ‹IsProper b›
  have : IsClosedImmersion (show _ ⟶ modificationFibreAtInfinity S'.a b from
    (reducedUnionIdeal t₁ t₂).subschemeι) :=
    inferInstanceAs (IsClosedImmersion (reducedUnionIdeal t₁ t₂).subschemeι)
  have key := S'.modificationChernClass_eq_localizedChern b hA
    (reducedUnionIdeal t₁ t₂).subschemeι
    (RingedSpace.isPerfect_canonicalDerivedTensorProduct W.toRingedSpace Q₁ Q₂ hQp₁ hQp₂)
    (Or.inr (Or.inr (Or.inl (exists_isLocallyBoundedFiniteLocallyFree_derivedTensor hc₁ hc₂)))) hF
    (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
    (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
      (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂) hp) h'
  have h7 := LocalizedSituation.localizedChern_withLargerClosed (S := S)
    (i' := pullback.fst z₁ z₂ ≫ z₁) (j := sq.isoPullback.hom) (hj := hθ)
    hS
  exact ((bivariantTransport_eq_bivariantProperPushforward_of_eq sq.isoPullback hθ rfl rfl
      (by rw [← Category.assoc, hθ]) _
      ((S.localizedChern hS).congrHom hθ.symm (by rw [hθ]))
      (BivariantClass.congrHom_heq _ _ _)).trans h7.symm).trans key.symm

end TensorSide

section TensorFormulaChern

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

include e in
/-- **The formula of Lemma 0FBF for `c_1` when the objects are complexes.** In the situation of
`Stacks.Chow.localizedPowerSum_derivedTensor_of_isLocallyBoundedFiniteLocallyFree`, with
`r_i = P_0(Z_i ⟶ X, E_i)`,

  `c_1(Z₁ ∩ Z₂ ⟶ X, E) = r₁ c_1(Z₂ ⟶ X, E₂) + r₂ c_1(Z₁ ⟶ X, E₁)`

in `A^1(Z₁ ∩ Z₂ ⟶ X)`, the second product taken for the flipped square. -/
theorem localizedChern_one_derivedTensor_of_isLocallyBoundedFiniteLocallyFree :
    ((LocalizedChernData.ofIsZero C f z E hE h 1).toSituation hc).localizedChern
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z E hE h
          one_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₁ z₂ sq z hz
            (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).toSituation hc₁).localizedPowerSum
              h₁ 0)
            (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 1).toSituation hc₂).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂
                h₂ one_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C f z₂ z₁ sq.flip z (sq.w.trans hz)
            (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).toSituation hc₂).localizedPowerSum
              h₂ 0)
            (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 1).toSituation hc₁).localizedChern
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁
                h₁ one_pos))) := by
  let S₁ := (LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).toSituation hc₁
  let S₂ := (LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).toSituation hc₂
  let S₁' := (LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 1).toSituation hc₁
  let S₂' := (LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 1).toSituation hc₂
  let S := (LocalizedChernData.ofIsZero C f z E hE h 1).toSituation hc
  let b₁ := graphBlowupToBase f E₁ hE₁
  let b₂ := graphBlowupToBase f E₂ hE₂
  have hA : IsIso (pullback.snd (pullback.fst b₁ b₂ ≫ b₁) (projectiveLineAffineChart f)) :=
    isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart f b₁ b₂
      (isIso_pullback_snd_graphBlowupToBase f E₁ hE₁)
      (isIso_pullback_snd_graphBlowupToBase f E₂ hE₂)
  let b := pullback.fst b₁ b₂ ≫ b₁
  have : IsProper b₁ := isProper_graphBlowupToBase f E₁ hE₁
  have : IsProper b₂ := isProper_graphBlowupToBase f E₂ hE₂
  have : IsProper b := by dsimp only [b]; infer_instance
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
  have key₁ : modificationPowerSum C f b hA z₁ t₁
      (S₁.hasDefinedChernClasses_graphObject.derivedPullback _) 0
      (S₁.mem_range_pullbackSnd_graphZeroSubschemeι b _ rfl h₁)
      (S₁.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _) =
        S₁.localizedPowerSum h₁ 0 :=
    S₁.modificationPowerSum_derivedPullback_graphObject b hA (pullback.fst b₁ b₂) rfl hfin₁ h₁ 0
  have key₂ : modificationPowerSum C f b hA z₂ t₂
      (S₂.hasDefinedChernClasses_graphObject.derivedPullback _) 0
      (S₂.mem_range_pullbackSnd_graphZeroSubschemeι b _ hb₂ h₂)
      (S₂.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _) =
        S₂.localizedPowerSum h₂ 0 :=
    S₂.modificationPowerSum_derivedPullback_graphObject b hA (pullback.snd b₁ b₂) hb₂ hfin₂ h₂ 0
  have key₁' : modificationChernClass C f b hA z₁ t₁
      (S₁.hasDefinedChernClasses_graphObject.derivedPullback _) 1
      (S₁.mem_range_pullbackSnd_graphZeroSubschemeι b _ rfl h₁)
      (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
        (S₁.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _) one_pos) =
        S₁'.localizedChern
          (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₁ E₁ hE₁ h₁
            one_pos) :=
    S₁'.modificationChernClass_derivedPullback_graphObject b hA (pullback.fst b₁ b₂) rfl hfin₁ h₁
      one_pos _
  have key₂' : modificationChernClass C f b hA z₂ t₂
      (S₂.hasDefinedChernClasses_graphObject.derivedPullback _) 1
      (S₂.mem_range_pullbackSnd_graphZeroSubschemeι b _ hb₂ h₂)
      (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
        (S₂.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _) one_pos) =
        S₂'.localizedChern
          (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C f z₂ E₂ hE₂ h₂
            one_pos) :=
    S₂'.modificationChernClass_derivedPullback_graphObject b hA (pullback.snd b₁ b₂) hb₂ hfin₂ h₂
      one_pos _
  have hQp₁ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (pullback.fst b₁ b₂).toLRSHom.toShHom _ (isPerfect_graphObject C f E₁ hE₁)
  have hQp₂ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (pullback.snd b₁ b₂).toLRSHom.toShHom _ (isPerfect_graphObject C f E₂ hE₂)
  have hF₁ := nonempty_derivedPullback_affineChart_derivedPullback_iso f (pullback.fst b₁ b₂) rfl
    S₁.nonempty_derivedPullback_affineChart_graphObject
  have hF₂ := nonempty_derivedPullback_affineChart_derivedPullback_iso f (pullback.snd b₁ b₂) hb₂
    S₂.nonempty_derivedPullback_affineChart_graphObject
  have hres₁ := S₁.modificationRestriction_of_isZero b t₁ (modificationComplementOpens b z₁)
    (fun _ hw => S₁.modificationProjection_notMem_range hw) hQp₁ h₁ hF₁
    (S₁.mem_range_pullbackSnd_graphZeroSubschemeι b _ rfl h₁)
    (S₁.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _)
  have hres₂ := S₂.modificationRestriction_of_isZero b t₂ (modificationComplementOpens b z₂)
    (fun _ hw => S₂.modificationProjection_notMem_range hw) hQp₂ h₂ hF₂
    (S₂.mem_range_pullbackSnd_graphZeroSubschemeι b _ hb₂ h₂)
    (S₂.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _)
  have L1 := modificationChernClass_one_derivedTensor C f b z₁ z₂ t₁ t₂ hQp₁ hQp₂
    (S₁.hasDefinedChernClasses_graphObject.derivedPullback _)
    (S₂.hasDefinedChernClasses_graphObject.derivedPullback _)
    (S₁.mem_range_pullbackSnd_graphZeroSubschemeι b _ rfl h₁)
    (S₂.mem_range_pullbackSnd_graphZeroSubschemeι b _ hb₂ h₂)
    (S₁.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _)
    (S₂.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _) hA hres₁ hres₂ hfin₁ hfin₂
  have hθ := isoPullback_hom_fst_comp_eq z₁ z₂ z sq hz
  have hgys : (gysinSystemOfInvertible C).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C
  have htr := bivariantTransport_localizedChern_eq_modificationChernClass C f z₁ z₂ sq z hz hE hc
    e b hA t₁ t₂ hQp₁ hQp₂ (S₁.hasDefinedChernClasses_graphObject.derivedPullback _)
    (S₂.hasDefinedChernClasses_graphObject.derivedPullback _)
    (exists_isLocallyBoundedFiniteLocallyFree_derivedPullback _
      (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₁ hE₁ hc₁))
    (exists_isLocallyBoundedFiniteLocallyFree_derivedPullback _
      (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₂ hE₂ hc₂)) hF₁ hF₂
    (S₁.mem_range_pullbackSnd_graphZeroSubschemeι b _ rfl h₁)
    (S₂.mem_range_pullbackSnd_graphZeroSubschemeι b _ hb₂ h₂)
    (S₁.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _)
    (S₂.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b _) one_pos h
  refine bivariantTransport_injective C (gysinSystemOfInvertible C) (z ≫ f)
    ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback hθ _
    hgys ?_
  refine htr.trans (L1.trans ?_)
  refine Eq.trans ?_
    (bivariantTransport_add C (gysinSystemOfInvertible C) _ _ _ _ _ _ _ _ _ _ _ _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans ?_
      (bivariantTransport_bivariantClassDegreeCongr_supportedIntersectionMul C f z₁ z₂ sq
        (IsPullback.of_hasPullback z₁ z₂) z hz _ pullback.condition.symm _ _ _ _ _).symm
    rw [key₁, key₂']
  · refine Eq.trans ?_
      (bivariantTransport_bivariantClassDegreeCongr_supportedIntersectionMul C f z₂ z₁ sq.flip
        (IsPullback.of_hasPullback z₁ z₂).flip z (sq.w.trans hz) (pullback.fst z₁ z₂ ≫ z₁) rfl
        _ _ _ _ _).symm
    rw [key₂, key₁']

end TensorFormulaChern

section DownstairsChern

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

/-- **The formula of Lemma 0FBF for `c_1`, for the classes of Remark 0GUK.** Let
`Z₁, Z₂ ⊆ X` be closed and `F₁, F₂ ∈ D(𝒪_X)` perfect with `F_i|_{X ∖ Z_i}` zero and with defined
Chern classes, and write `r_i = P_0(Z_i ⟶ X, F_i)`. Then

  `c_1(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ c_1(Z₂ ⟶ X, F₂) + r₂ c_1(Z₁ ⟶ X, F₁)`

in `A^1(Z₁ ∩ Z₂ ⟶ X)`, for `Z₁ ∩ Z₂ = Z₁ ×_X Z₂`, the second product taken for `Z₁ ∩ Z₂`
presented as `Z₂ ×_X Z₁` through the flipped square. -/
theorem LocalizedChernData.localizedChern_one_derivedTensorOfIsZero :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 1).localizedChern hE
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
          (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) one_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ 0)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ 0)
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos))) := by
  let H := hE₁.some.tensor hE₂.some
  have hc₁ := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree
    (hE₁.some.tensorLeft hE₂.some)
  have hc₂ := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree
    (hE₁.some.tensorRight hE₂.some)
  have hc := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree H
  have hY := localizedChern_one_derivedTensor_of_isLocallyBoundedFiniteLocallyFree C (H.f ≫ a)
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
  refine localizedChern_one_derivedTensor_of_isEnvelope C a i₁ i₂ hF₁ hF₂ h₁ h₂ H.f hE₁ hE₂ hE
    H.envelope hc₁ hc₂ hc (hY.trans ?_)
  exact congrArg₂ (· + ·) rfl rfl

end DownstairsChern

end Stacks.Chow

end

module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedTensorChern
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedChernCharacterRing

/-!
# Products over the fibre at infinity that preserve the image of the Gysin map

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `b : W ⟶ 𝐏¹_X` be proper. A class `a ∈ A^m(W_∞ ×_X Y ⟶ W_∞)`,
`Y ⊆ X` closed, preserves the image of the Gysin map `i_∞^*` at infinity
(`Stacks.Chow.PreservesInfinityGysinImage`) when it carries classes of the form `i_∞^* β` to
classes of this form after every base change. This file shows that the property survives the
following operations:

* transport along an isomorphism `Y ≅ Y'` of closed subschemes over `X`;
* the third multiplication `res(e) ∘ a` of Stacks 0FA0 of two classes supported on one closed
  subscheme;
* the product of Stacks 0FE5 for the flipped square presenting `W_∞ ×_X (Y ×_X Z)`.

## Main results

* `Stacks.Chow.PreservesInfinityGysinImage.bivariantTransport`
* `Stacks.Chow.PreservesInfinityGysinImage.supportedMul`
* `Stacks.Chow.PreservesInfinityGysinImage.supportedIntersectionMul_flip`

## References

* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

section PreservesTransport

variable (C : ChowSituation.{u}) {X W Y Y' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (y : Y ⟶ X) [IsClosedImmersion y] (y' : Y' ⟶ X) [IsClosedImmersion y'] (θ : Y ≅ Y')
  (hθ : θ.hom ≫ y' = y)

/-- **Transport preserves the property of preserving the image of the Gysin map at infinity.**
For an isomorphism `θ : Y ≅ Y'` of closed subschemes of `X` over `X`, if `a ∈ A^m(W_∞ ×_X Y ⟶ W_∞)`
preserves the image of `i_∞^*`, so does its transport along `W_∞ ×_X Y ≅ W_∞ ×_X Y'`. -/
theorem PreservesInfinityGysinImage.bivariantTransport {m : ℤ}
    {a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m}
    (ha : PreservesInfinityGysinImage C f b y a) :
    PreservesInfinityGysinImage C f b y'
      (bivariantTransport C (gysinSystemOfInvertible C) _ _ _ _ rfl _ rfl
        (pullbackSymmetry (modificationProjectionAtInfinity f b) y ≪≫
          transportPullbackIso y y' θ hθ (modificationProjectionAtInfinity f b) ≪≫
          (pullbackSymmetry (modificationProjectionAtInfinity f b) y').symm)
        (pullbackSymmetry_transportPullbackIso_hom_fst C f b y y' θ hθ) m
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) := by
  intro V g _ k β
  obtain ⟨β', hβ'⟩ := ha g k β
  have hT : (transportPullbackIso y y' θ hθ g).hom ≫ (pullback.fst y' g ≫ y') =
      pullback.fst y g ≫ y := by
    rw [transportPullbackIso_hom_fst_assoc, hθ]
  refine ⟨chowPush C _ _ (testBaseChangeMapOfEq (modificationProjection f b) _ _ _ hT)
    (testBaseChangeMapOfEq_modificationBaseChangeOver _ _ _ hT) _ β', ?_⟩
  rw [modificationInfinityGysin_chowPush_testBaseChangeMapOfEq, ← hβ', bivariantTransport_cap,
    bivariantTransportCap_apply]
  show chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) =
    chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _)
  rw [chowPush_comp C _ _ _ _ _ _ rfl, chowPush_comp C _ _ _ _ _ _ rfl]
  · refine chowPush_congr C _ _ ?_ _ _ _ _
    refine pullback.hom_ext ?_ ?_
    · simp [transportPullbackIso]
    · refine pullback.hom_ext ?_ ?_
      · simp [transportPullbackIso]
      · simp [transportPullbackIso]
  all_goals first
    | simp [transportPullbackIso]; done
    | (have hc := pullback.condition (f := pullback.fst (modificationProjectionAtInfinity f b) y)
          (g := pullback.fst (modificationProjectionAtInfinity f b) g)
       simp only [modificationProjectionAtInfinity, modificationProjection] at hc ⊢
       simp [transportPullbackIso, reassoc_of% hc])

end PreservesTransport

section PreservesMul

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (z : Z ⟶ X) [IsClosedImmersion z]

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The comparison `Z ×_X Z ≅ Z` for a monomorphism `z : Z ⟶ X` lies over `X`. -/
theorem isKernelPair_isoPullback_inv_comp :
    (IsKernelPair.id_of_mono z).isoPullback.symm.hom ≫ z = pullback.fst z z ≫ z := by
  rw [Iso.symm_hom, ← IsPullback.isoPullback_inv_fst (IsKernelPair.id_of_mono z),
    Category.comp_id]

/-- **The third multiplication of Stacks 0FA0 preserves the image of the Gysin map at infinity**:
if `e` and `a` do, so does `res(e) ∘ a`. -/
theorem PreservesInfinityGysinImage.supportedMul {p m : ℤ}
    {e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p}
    {a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl m}
    (he : PreservesInfinityGysinImage C f b z e) (ha : PreservesInfinityGysinImage C f b z a) :
    PreservesInfinityGysinImage C f b z
      (supportedMul C (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f) (modificationProjectionAtInfinity f b ≫ f)
        (pullback.fst (modificationProjectionAtInfinity f b) z) rfl e a) := by
  have hθ := isKernelPair_isoPullback_inv_comp z
  rw [← supportedIntersectionMul_self_eq_supportedMul,
    ← bivariantTransport_supportedIntersectionMul C _ _ _
      (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z z)
      (IsKernelPair.id_of_mono _) _
      (pullbackFstTestIso_inv_snd_fst (modificationProjectionAtInfinity f b) z z) _
      (Category.id_comp _) _
      (pullbackSymmetry_transportPullbackIso_hom_fst C f b _ z _ hθ)]
  have h : PreservesInfinityGysinImage C f b z _ :=
    PreservesInfinityGysinImage.bivariantTransport C f b (pullback.fst z z ≫ z) z _ hθ
    (PreservesInfinityGysinImage.modificationInfinityMul C f b he ha)
  exact @h

/-- **The product of Stacks 0FE5 over `W_∞` for the flipped square preserves the image of the
Gysin map at infinity** when both factors do. -/
theorem PreservesInfinityGysinImage.supportedIntersectionMul_flip {Y : Scheme.{u}}
    {y : Y ⟶ X} [IsClosedImmersion y] {p m : ℤ}
    {e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p}
    {a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m}
    (he : PreservesInfinityGysinImage C f b z e) (ha : PreservesInfinityGysinImage C f b y a) :
    PreservesInfinityGysinImage C f b (pullback.fst y z ≫ y)
      (supportedIntersectionMul C (modificationProjectionAtInfinity f b ≫ f)
        (pullback.fst (modificationProjectionAtInfinity f b) z)
        (pullback.fst (modificationProjectionAtInfinity f b) y)
        (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z y).flip
        (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst y z ≫ y))
        (pullbackFstTestIso_inv_fst_comp_fst y z _) e a) := by
  have hσ : (pullbackSymmetry z y).hom ≫ pullback.fst y z ≫ y = pullback.fst z y ≫ z := by
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]
  rw [← bivariantTransport_supportedIntersectionMul C _ _ _
      (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) y z)
      (isPullback_pullbackFstTestIso (modificationProjectionAtInfinity f b) z y).flip _
      (pullbackFstTestIso_inv_snd_fst (modificationProjectionAtInfinity f b) y z) _
      (pullbackFstTestIso_inv_fst_comp_fst y z _) _
      (pullbackSymmetry_transportPullbackIso_hom_fst C f b _ _ _ hσ)]
  have h : PreservesInfinityGysinImage C f b (pullback.fst y z ≫ y) _ :=
    PreservesInfinityGysinImage.bivariantTransport C f b (pullback.fst z y ≫ z) _ _ hσ
    (PreservesInfinityGysinImage.modificationInfinityMul C f b he ha)
  exact @h

end PreservesMul

end Stacks.Chow

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.Integral
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallySubmersive
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallySeparatedFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SyntomicFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitePresentationFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitenessFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalHomeomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyInjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyMono

/-!
# Properties of morphisms representable by algebraic spaces (Stacks 04XB)

Section 04XB of Properties of Stacks sets up, for a property `P` of morphisms of algebraic spaces
which is fppf local on the target and preserved by arbitrary base change, the notion of a
1-morphism representable by algebraic spaces *having `P`* (Algebraic Stacks, Definition 03YK,
here `AlgebraicGeometry.Stack.HasRelativeProperty`), and then asserts:

1. the notion is preserved by base change along any 1-morphism (Algebraic Stacks, Lemmas 0302 and
   045C);
2. if `P` is stable under composition, so is the notion (Lemmas 0301 and 045B), and so is it
   under products (Lemma 045E);
3. an implication `P ⇒ P'` between two such properties gives the same implication between the
   notions (Lemma 045F);
4. the discussion applies to each of the thirty-one properties it lists, i.e. each of them is
   preserved by arbitrary base change and fppf local on the target (Morphisms of Spaces and
   Descent on Spaces, Lemmas 03HF, 041L, …, 03KL, 042F).

`AlgebraicGeometry.Stack.representableMorphismProperties` states all four assertions in one
theorem. Each part is assembled from the library: the general assertions from the theorems of
Stacks 0302/045C, 0301/045B, 0303/045E and 045F, and every entry of the list from the
corresponding base-change instance and the corresponding fpqc (or fppf) locality statement of
Descent on Spaces, the fpqc ones being moved to the fppf precoverage along Stacks 0DFQ
(`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`).

## Main results

* `AlgebraicGeometry.Stack.representableMorphismProperties`: **Stacks 04XB**.

## Implementation notes

The base-change assertion is stated for an arbitrary 2-fibre product square of categories fibred
in groupoids over the big fppf site, so in particular for any 1-morphism `𝒴' ⟶ 𝒴` of algebraic
stacks. The representability of the base change, of the composite and of the product (Stacks
0302, 0301, 0303) is stated as the existence of a representability witness, and the relative
property is asserted at it; a representability witness is a proof of a proposition, so which one
is chosen does not matter.

The entry "(locally) quasi-finite" of the list is two entries, locally quasi-finite and
quasi-finite, and both are stated.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045E](https://stacks.math.columbia.edu/tag/045E)
* [Stacks Project, Tag 045F](https://stacks.math.columbia.edu/tag/045F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CatFiberedInGroupoids

universe u v w t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of algebraic spaces local at the target for the fpqc precoverage is
local at the target for the fppf precoverage. -/
private theorem isLocalAtTarget_fppf_of_fpqc (P : MorphismProperty (AlgebraicSpaces B S hS))
    (h : P.IsLocalAtTarget (Space.Topology.fpqc.precoverage.{u, t} B S hS)) :
    P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS) :=
  h.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, t} B S hS)

/-- **Stacks 04XB.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
preserved by arbitrary base change and local on the target for the fppf precoverage, and let a
1-morphism of categories fibred in groupoids over the big fppf site of `S` representable by
algebraic spaces *have `P`* in the sense of Stacks 03YK
(`AlgebraicGeometry.Stack.HasRelativeProperty`). Then:

1. in a 2-fibre product square over `g : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴` with `f` representable by
   algebraic spaces and having `P`, the projection to `𝒵` is representable by algebraic spaces
   and has `P`;
2. if `P` is moreover stable under composition, a composite of two 1-morphisms representable by
   algebraic spaces having `P` is representable by algebraic spaces and has `P`, and so is a
   product `𝒳₁ × 𝒳₂ ⟶ 𝒴₁ × 𝒴₂` of two such 1-morphisms;
3. if `P ≤ P'` for a second such property `P'`, a 1-morphism representable by algebraic spaces
   having `P` has `P'`;
4. each of the following properties of morphisms of algebraic spaces is preserved by arbitrary
   base change and local on the target for the fppf precoverage, so that 1-3 apply to it:
   quasi-compact, quasi-separated, universally closed, universally open, universally
   submersive, universal homeomorphism, surjective, universally injective, locally of finite
   type, locally of finite presentation, finite type, finite presentation, flat, open
   immersion, isomorphism, affine, closed immersion, separated, proper, quasi-affine, integral,
   finite, locally quasi-finite, quasi-finite, syntomic, smooth, unramified, étale, finite
   locally free, monomorphism, immersion, locally separated. -/
@[stacks 04XB]
theorem representableMorphismProperties :
    (∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
        [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)],
      (∀ (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
            (BigFppfOver B S hS))
          (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (R : Bicategory.TwoCommSq g f)
          (_ : Bicategory.IsTwoFibreProduct R)
          (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom),
          HasRelativeProperty.{u, _, _, t} B S hS P f hf →
          ∃ h : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom,
            HasRelativeProperty.{u, _, _, t} B S hS P R.fst h) ∧
      (P.IsStableUnderComposition →
        (∀ (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
            (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
            (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
            (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom),
            HasRelativeProperty.{u, _, _, t} B S hS P f hf →
            HasRelativeProperty.{u, _, _, t} B S hS P g hg →
            ∃ h : IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom,
              HasRelativeProperty.{u, _, _, t} B S hS P (f ≫ g) h) ∧
        (∀ (𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
              (BigFppfOver B S hS))
            (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂)
            (hf₁ : IsRepresentableByAlgebraicSpaces B S hS f₁.hom)
            (hf₂ : IsRepresentableByAlgebraicSpaces B S hS f₂.hom),
            HasRelativeProperty.{u, _, _, t} B S hS P f₁ hf₁ →
            HasRelativeProperty.{u, _, _, t} B S hS P f₂ hf₂ →
            ∃ h : IsRepresentableByAlgebraicSpaces B S hS (productMap f₁ f₂).hom,
              HasRelativeProperty.{u, _, _, t} B S hS P (productMap f₁ f₂) h))) ∧
    (∀ (P P' : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
        [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
        [P'.IsStableUnderBaseChange]
        [P'.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)],
      P ≤ P' →
      ∀ (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)
        (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom),
        HasRelativeProperty.{u, _, _, t} B S hS P f hf →
        HasRelativeProperty.{u, _, _, t} B S hS P' f hf) ∧
    (∀ P ∈ ({Space.quasiCompactProperty B S hS,
        Space.quasiSeparatedProperty B S hS,
        Space.universallyClosedProperty B S hS,
        Space.universallyOpenMorphismProperty B S hS,
        Space.universallySubmersiveMorphismProperty B S hS,
        Space.universalHomeomorphismMorphismProperty B S hS,
        Space.surjectiveMorphismProperty B S hS,
        Space.universallyInjectiveMorphismProperty B S hS,
        fun _ _ f => Space.IsLocallyOfFiniteType B S hS f.hom,
        fun _ _ f => Space.IsLocallyOfFinitePresentation B S hS f.hom,
        Space.finiteTypeProperty B S hS,
        fun _ _ f => Space.IsFinitePresentation B S hS f.hom,
        fun _ _ f => Space.IsFlat B S hS f.hom,
        Space.openImmersionProperty B S hS,
        MorphismProperty.isomorphisms (AlgebraicSpaces B S hS),
        fun _ _ f => Space.IsAffineHom B S hS f.hom,
        Space.closedImmersionProperty B S hS,
        Space.separatedProperty B S hS,
        Space.properProperty B S hS,
        fun _ _ f => Space.IsQuasiAffineHom B S hS f.hom,
        Space.integralMorphismProperty B S hS,
        Space.finiteMorphismProperty B S hS,
        fun _ _ f => Space.IsLocallyQuasiFinite B S hS f.hom,
        fun _ _ f => Space.IsQuasiFinite B S hS f.hom,
        fun _ _ f => Space.IsSyntomic B S hS f.hom,
        Space.smoothMorphismProperty B S hS,
        fun _ _ f => Space.IsUnramified B S hS f.hom,
        fun _ _ f => Space.IsEtale B S hS f.hom,
        Space.finiteLocallyFreeMorphismProperty B S hS,
        MorphismProperty.monomorphisms (AlgebraicSpaces B S hS),
        Space.immersionProperty B S hS,
        Space.locallySeparatedMorphismProperty B S hS} :
          Set (MorphismProperty (AlgebraicSpaces B S hS))),
      P.IsStableUnderBaseChange ∧
        P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)) := by
  refine ⟨fun P _ _ => ⟨fun 𝒳 𝒴 𝒵 f g R hR hf hPf => ⟨_,
      hasRelativeProperty_baseChange B S hS P 𝒳 𝒴 𝒵 f g R hR hf hPf⟩,
      fun _ => ⟨fun 𝒳 𝒴 𝒵 f g hf hg hPf hPg => ⟨_,
        hasRelativeProperty_comp B S hS P f g hf hg hPf hPg⟩,
      fun 𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ f₁ f₂ hf₁ hf₂ hP₁ hP₂ => ⟨_,
        hasRelativeProperty_productMap B S hS P f₁ f₂ hf₁ hf₂ hP₁ hP₂⟩⟩⟩,
    fun P P' _ _ _ _ hPP' 𝒳 𝒴 f hf hP => hasRelativeProperty_mono B S hS hPP' hf hP, ?_⟩
  have hflat := Space.isFlat_isStableUnderBaseChange B S hS
  have hfpqc := isLocalAtTarget_fppf_of_fpqc.{u, t} B S hS
  intro P hP
  simp only [Set.mem_insert_iff] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  -- the entries in the order of the list
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · refine ⟨?_, hfpqc _ inferInstance⟩
    have heq : Space.universallySubmersiveMorphismProperty B S hS =
        (Space.isSubmersiveProperty B S hS).universally := by
      funext X T g
      exact propext (Space.universallySubmersive_iff_universally_isSubmersive B S hS g)
    rw [heq]
    infer_instance
  · refine ⟨?_, hfpqc _ inferInstance⟩
    have heq : Space.universallyInjectiveMorphismProperty B S hS =
        (Space.injectiveOnPointsProperty B S hS).universally := by
      funext X T g
      exact propext (Space.universallyInjective_iff_universally_injectiveOnPoints B S hS g)
    have hui : MorphismProperty.IsStableUnderBaseChange (fun ⦃X Y : AlgebraicSpaces B S hS⦄
        (f : X ⟶ Y) => Space.UniversallyInjective B S hS f.hom) := by
      change (Space.universallyInjectiveMorphismProperty B S hS).IsStableUnderBaseChange
      rw [heq]
      infer_instance
    have huo : (Space.universallyOpenMorphismProperty B S hS).IsStableUnderBaseChange := by
      have heq : Space.universallyOpenMorphismProperty B S hS =
          (Space.isOpenMorphismProperty B S hS).universally := by
        funext X T g
        exact propext (Space.universallyOpen_iff_universally_isOpenMorphism B S hS g)
      rw [heq]
      infer_instance
    have hs : (Space.surjectiveMorphismProperty B S hS).IsStableUnderBaseChange := inferInstance
    rw [Space.universalHomeomorphismMorphismProperty_eq_inf]
    exact @MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _
      (@MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _ hs hui) huo
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · refine ⟨?_, hfpqc _ inferInstance⟩
    have heq : Space.universallyInjectiveMorphismProperty B S hS =
        (Space.injectiveOnPointsProperty B S hS).universally := by
      funext X T g
      exact propext (Space.universallyInjective_iff_universally_injectiveOnPoints B S hS g)
    rw [heq]
    infer_instance
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨hflat, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨⟨fun sq hf => Space.isAffineHom_hom_of_isPullback sq hf⟩,
      hfpqc _ (Space.isLocalAtTarget_isAffineHom_fpqc B S hS)⟩
  · exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨⟨fun sq hf => Space.IsQuasiAffineHom.hom_of_isPullback sq hf⟩,
      hfpqc _ (Space.isLocalAtTarget_isQuasiAffineHom_fpqc B S hS)⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨Space.isSyntomic_isStableUnderBaseChange B S hS, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨Space.isUnramified_isStableUnderBaseChange B S hS, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · refine ⟨?_, hfpqc _ inferInstance⟩
    have hfin : (Space.finiteMorphismProperty B S hS).IsStableUnderBaseChange := inferInstance
    have hlfp : MorphismProperty.IsStableUnderBaseChange (fun ⦃X Y : AlgebraicSpaces B S hS⦄
        (f : X ⟶ Y) => Space.IsLocallyOfFinitePresentation B S hS f.hom) := inferInstance
    rw [Space.finiteLocallyFreeMorphismProperty_eq_inf]
    exact @MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _
      (@MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _ hfin hflat) hlfp
  · exact ⟨inferInstance, hfpqc _ inferInstance⟩
  · exact ⟨inferInstance, Space.isImmersion_isLocalAtTarget_fppf B S hS⟩
  · exact ⟨inferInstance, Space.locallySeparated_isLocalAtTarget_fppf B S hS⟩

end AlgebraicGeometry.Stack

end

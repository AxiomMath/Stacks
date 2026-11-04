module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletionChart
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LargerClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.NormalLineConeZeroSectionGysin
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformation
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ChowCohomologyRestriction

/-!
# The classes `c'_t(Q)` of the deformation of `i_*𝒪_Z` to the normal cone

Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre at infinity `W_∞`, let
`z : Z ⟶ X` be a closed immersion, `E = W_∞ ×_X Z`, and let `T ⊆ W_∞` be closed and contain every
point of `W_∞` over `X ∖ Z`. The class `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C` of Stacks 0F9K is
built from `c_p(Q) ∈ A^p(W)` through its restriction to `E` only: the extension `c'_p(Q|_E)` of
Stacks 0F9H is that of `c_p(Q)|_E` along the closed cover `W_∞ = T ∪ E`. Hence `c'_p(Q)` vanishes
as soon as `c_p(Q)|_E = c_p(Q|_E)` does, `Q|_E` being the derived pullback of `Q` along
`E ⟶ W_∞ ⟶ W`.

In the proof of Stacks 0FEG, for a regular closed immersion `i : Z ⟶ X` of codimension `r`, `W` is
the blowup of `𝐏¹_X` in `∞(Z)` and `Q = i'_*𝒪_{𝐏¹_Z}`; there `Q|_E` is the pushforward of the
structure sheaf along the zero section `Z ⟶ E ≅ 𝐏(𝒞_{Z/X} ⊕ 𝒪_Z)`, whose Chern classes of
degree `0 < t < r` vanish by Stacks 0FEF.

## Main definitions

* `Stacks.Chow.exceptionalDivisorToFibreAtInfinity` — the exceptional divisor `E ⟶ W_∞` of the
  blowup at infinity as a closed subscheme of the fibre at infinity.

## Main results

* `Stacks.Chow.modificationExtension_eq_zero_of_restriction_eq_zero` — the extension `(q|_E)'`
  vanishes when `q|_E` does.
* `Stacks.Chow.localizedModificationClass_eq_zero_of_restriction_eq_zero` — so does the localized
  class `q'`.
* `Stacks.Chow.modificationChernClass_eq_zero_of_perfectChernClass_derivedPullback_eq_zero` — the
  class `c'_p(Q)` of Stacks 0F9K vanishes when `c_p(Q|_E)` does, and
  `Stacks.Chow.modificationChernClass_eq_zero_of_derivedPullback_iso` — it vanishes when `Q|_E` is
  the pullback of an object whose `c_p` vanishes.
* `Stacks.Chow.isPullback_exceptionalDivisorToFibreAtInfinity` — for the blowup of `𝐏¹_X` in
  `∞(Z)`, the exceptional divisor is `W_∞ ×_X Z`.
* `Stacks.Chow.isPullback_lineToBlowupAtInfinity_exceptionalIdealAtInfinity` — the base change of
  `𝐏¹_Z ⟶ W` along `E ⟶ W` is the vertex `Z ⟶ C_ZX ⟶ E` of the normal cone.

## Implementation notes

The scheme `E` of Stacks 0F9K is the fibre product `W_∞ ×_X Z`; for the blowup at infinity it is
the exceptional divisor `(exceptionalIdealAtInfinity (ker i)).subscheme`, through the cartesian
square `Stacks.Chow.isPullback_exceptionalDivisorToFibreAtInfinity`.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Vanishing of the localized class through the restriction to `E` -/

section Vanishing

/-- Composing the zero class on the left gives the zero class (Stacks 0B75: the composition is
bilinear). -/
theorem bivariantCompositeOfInvertible_zero_left (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p q : ℤ)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q 0 b = 0 := by
  rw [← bivariantCompositeBilinearOfInvertible_apply, map_zero, AddMonoidHom.zero_apply]

/-- A Chow cohomology class heterogeneously equal to the zero class of an equal structure morphism
is zero. -/
theorem chowCohomologyComponent_eq_zero_of_heq {C : ChowSituation.{u}} {G : GysinSystem C}
    {Y : Scheme.{u}} {s s' : Y ⟶ C.S} [LocallyOfFiniteType s] [LocallyOfFiniteType s'] {p : ℤ}
    (hs : s = s') {a : chowCohomologyComponent C G s p} {a' : chowCohomologyComponent C G s' p}
    (h : a ≍ a') (h' : a' = 0) : a = 0 := by
  subst hs
  exact (eq_of_heq h).trans h'

/-- The extension along a closed cover of a class equal to zero is zero. -/
theorem closedCoverExtension_eq_zero_of_eq_zero (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
    [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂)
    {p : ℤ} {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) (h : a = 0) :
    closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha = 0 := by
  subst h
  exact closedCoverExtension_zero hcover

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  (D : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA)
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {p : ℤ}
  {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}

/-- **The extension `(q|_E)'` vanishes when `q|_E` does**: the class of Stacks 0F9H extended
along the closed cover `W_∞ = T ∪ E` is the extension of `q|_E`, and the extension of the zero
class is zero. -/
theorem modificationExtension_eq_zero_of_restriction_eq_zero
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (h : Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) = 0) :
    modificationExtension z t hT hq = 0 := by
  unfold modificationExtension
  exact closedCoverExtension_eq_zero_of_eq_zero C _ t _ _ rfl _
    (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)) h

/-- **The localized class `q'` vanishes when `q|_E` does**, for `E = W_∞ ×_X Z`: it is
`(E ⟶ Z)_* ∘ (q|_E)' ∘ C`, and `(q|_E)'` vanishes. -/
theorem localizedModificationClass_eq_zero_of_restriction_eq_zero
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (h : Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) = 0) :
    localizedModificationClass D z t hT hq = 0 := by
  unfold localizedModificationClass
  rw [modificationExtension_eq_zero_of_restriction_eq_zero z t hT hq h,
    bivariantCompositeOfInvertible_zero_left, BivariantClass.copy_zero,
    bivariantProperPushforwardOfInvertible_zero]

end Vanishing

/-! ### The class `c'_p(Q)` vanishes when `c_p(Q|_E)` does -/

section ChernVanishing

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q)

/-- **`c'_p(Q)` vanishes when `c_p(Q|_E)` does.** In the situation of
`Stacks.Chow.modificationChernClass`, with `E = W_∞ ×_X Z` and `e : E ⟶ W_∞ ⟶ W`, if the Chern
class `c_p(Le^*Q) ∈ A^p(E)` vanishes then so does `c'_p(Q) ∈ A^p(Z ⟶ X)`: the restriction of
`c_p(Q)` to `E` is `c_p(Le^*Q)`. -/
theorem modificationChernClass_eq_zero_of_perfectChernClass_derivedPullback_eq_zero (p : ℕ)
    (hQE : HasDefinedChernClasses ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (hp : perfectChernClass C (pullback.fst (modificationProjectionAtInfinity f b) z ≫
      modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f) hQE p = 0)
    (hT hrank) :
    modificationChernClass C f b hA z t hQ p hT hrank = 0 := by
  have hs : (pullback.fst (modificationProjectionAtInfinity f b) z ≫
      modificationInclusionAtInfinity f b) ≫ modificationProjection f b ≫ f =
      pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f :=
    Category.assoc _ _ _
  have hres := congrFun (res_perfectChernClass_derivedPullback_of_comp_eq C
    (modificationProjection f b ≫ f) hQ _ hs hQE) p
  rw [TotalChowClass.res_apply_eq_bivariantClassCongrBase] at hres
  have h0 : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationInclusionAtInfinity f b) (p : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (perfectChernClass C (modificationProjection f b ≫ f) hQ p) = 0 := by
    rw [← map_eq_zero_iff _ (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 _) hs hs
      (hv := Category.id_comp _) (hv' := Category.id_comp _) (p : ℤ)).injective]
    exact hres.trans hp
  have h1 := chowCohomologyComponent_eq_zero_of_heq hs.symm
    (chowCohomologyRestriction_chowCohomologyRestriction (modificationProjection f b ≫ f)
      (modificationInclusionAtInfinity f b) (pullback.fst (modificationProjectionAtInfinity f b) z)
      (perfectChernClass C (modificationProjection f b ≫ f) hQ p)) h0
  unfold modificationChernClass
  exact localizedModificationClass_eq_zero_of_restriction_eq_zero _ z t hT
    (vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hrank) h1

/-- **`c'_p(Q)` vanishes when `Q|_E` is pulled back from an object with vanishing `c_p`.** In the
situation of `Stacks.Chow.modificationChernClass`, with `E = W_∞ ×_X Z` and `e : E ⟶ W_∞ ⟶ W`,
let `φ : E ⟶ P` be locally of finite type and `G ∈ D(𝒪_P)` with defined Chern classes and
`c_p(G) = 0`. If `Le^*Q ≅ Lφ^*G`, then `c'_p(Q) = 0`: `c_p(Le^*Q) = c_p(Lφ^*G)` is the
restriction of `c_p(G)` along `φ`. -/
theorem modificationChernClass_eq_zero_of_derivedPullback_iso (p : ℕ) {P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (φ : pullback (modificationProjectionAtInfinity f b) z ⟶ P) [LocallyOfFiniteType φ]
    (hφ : φ ≫ sP = pullback.fst (modificationProjectionAtInfinity f b) z ≫
      modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f)
    {G : DerivedCategory P.Modules} (hG : HasDefinedChernClasses G)
    (hp : perfectChernClass C sP hG p = 0)
    (e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback φ.toLRSHom.toShHom).obj G)
    (hT hrank) :
    modificationChernClass C f b hA z t hQ p hT hrank = 0 := by
  have hQE := hQ.derivedPullback (pullback.fst (modificationProjectionAtInfinity f b) z ≫
    modificationInclusionAtInfinity f b)
  refine modificationChernClass_eq_zero_of_perfectChernClass_derivedPullback_eq_zero C f b hA z t
    hQ p hQE ?_ hT hrank
  rw [perfectChernClass_congr C _ hQE (hG.derivedPullback φ) e,
    ← res_perfectChernClass_derivedPullback_of_comp_eq C sP hG φ hφ (hG.derivedPullback φ),
    TotalChowClass.res_apply_eq_bivariantClassCongrBase, hp, map_zero, map_zero]

end ChernVanishing

/-! ### The exceptional divisor as `W_∞ ×_X Z` -/

section ExceptionalDivisor

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The exceptional divisor `E ⟶ W_∞` as a closed subscheme of the fibre at infinity** of the
blowup at infinity, read as a modification of `X ×_S 𝐏¹_S`. -/
def exceptionalDivisorToFibreAtInfinity :
    (exceptionalIdealAtInfinity i.ker).subscheme ⟶
      modificationFibreAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) :=
  Scheme.IdealSheafData.inclusion (fibreIdealAtInfinity_le_exceptionalIdealAtInfinity i.ker) ≫
    (modificationFibreAtInfinityIso i.ker f).inv

/-- The morphism `exceptionalDivisorToFibreAtInfinity f i` is a closed immersion. -/
instance isClosedImmersion_exceptionalDivisorToFibreAtInfinity :
    IsClosedImmersion (exceptionalDivisorToFibreAtInfinity f i) := by
  unfold exceptionalDivisorToFibreAtInfinity
  infer_instance

omit [IsClosedImmersion i] in
/-- Composing `exceptionalDivisorToFibreAtInfinity f i` with the inclusion of the fibre at
infinity gives the inclusion of the exceptional divisor into the blowup at infinity. -/
@[reassoc (attr := simp)]
theorem exceptionalDivisorToFibreAtInfinity_inclusion :
    exceptionalDivisorToFibreAtInfinity f i ≫
        modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
      (exceptionalIdealAtInfinity i.ker).subschemeι := by
  rw [exceptionalDivisorToFibreAtInfinity, Category.assoc,
    modificationFibreAtInfinityIso_inv_inclusion, Scheme.IdealSheafData.inclusion_subschemeι]

/-- **`E = W_∞ ×_X Z`**: the exceptional divisor of the blowup at infinity is the inverse image of
`Z` in the fibre at infinity, the square `E ⟶ W_∞`, `E ⟶ Z`, `W_∞ ⟶ X`, `Z ⟶ X` being cartesian.
The ideal of `E` in `W` is that of `∞(Z) = Z ×_X (𝐏¹_X)_∞`, pulled back, so its ideal in `W_∞` is
that of `Z` pulled back. -/
theorem isPullback_exceptionalDivisorToFibreAtInfinity :
    IsPullback (exceptionalDivisorToFibreAtInfinity f i) (exceptionalDivisorToCentre i)
      (modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f)) i := by
  set ι := modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f)
  refine isPullback_of_isClosedImmersion _ _ _ _ ?_ ?_
  · rw [exceptionalDivisorToCentre_comp_toX, modificationProjectionAtInfinity,
      exceptionalDivisorToFibreAtInfinity_inclusion_assoc,
      modificationProjection_blowupAtInfinityToProjectiveLineProduct]
  · rw [ker_eq_comap_ker_of_comp_eq ι _ _ (exceptionalDivisorToFibreAtInfinity_inclusion f i),
      Scheme.IdealSheafData.ker_subschemeι, modificationProjectionAtInfinity,
      modificationProjection_blowupAtInfinityToProjectiveLineProduct,
      Scheme.IdealSheafData.comap_comp]
    have hE : exceptionalIdealAtInfinity i.ker =
        i.ker.comap (blowupAtInfinityToBase i.ker) ⊔ fibreIdealAtInfinity i.ker := by
      show (infinityCentreIdeal i.ker).comap (blowupAtInfinityToLine i.ker) = _
      rw [infinityCentreIdeal_eq_sup, Scheme.IdealSheafData.comap_sup,
        ← Scheme.IdealSheafData.comap_comp]
      rfl
    rw [hE, Scheme.IdealSheafData.comap_sup, ← ker_modificationInclusionAtInfinity_blowupAtInfinity
      i.ker f, ker_comap_self, sup_bot_eq]

/-- **The base change of `𝐏¹_Z ⟶ W` along `E ⟶ W` is `Z ⟶ C_ZX ⟶ E`**, the vertex of the
normal cone followed by the open immersion `C_ZX ⟶ E` of Stacks 0FBH: the exceptional divisor
pulls back to the divisor at infinity `(𝐏¹_Z)_∞ = Z` of `𝐏¹_Z` (the proof of Stacks 0FE9). -/
theorem isPullback_lineToBlowupAtInfinity_exceptionalIdealAtInfinity :
    IsPullback (i.toImage ≫ lineInfinitySection i.ker.subscheme)
      (normalConeZeroSection i ≫ normalConeToExceptionalDivisor i)
      (lineToBlowupAtInfinity i.ker) (exceptionalIdealAtInfinity i.ker).subschemeι := by
  refine isPullback_of_isClosedImmersion _ _ _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc]
    exact lineInfinitySection_lineToBlowupAtInfinity i
  · rw [Scheme.IdealSheafData.ker_subschemeι,
      comap_exceptionalIdealAtInfinity_lineToBlowupAtInfinity, Scheme.Hom.ker_comp_of_isIso,
      lineInfinityDivisor]

end ExceptionalDivisor

end Stacks.Chow

end

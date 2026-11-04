module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionOfComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionExcess
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionBlowup

/-!
# The reduction of Stacks 0FEC to an integral test scheme

Stacks 0FEC asserts `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')` for a conormal-compatible triple
of virtual normal bundles. Its proof opens: *the assumptions remain satisfied after any base
change by a morphism `X' ⟶ X` which is locally of finite type ... Thus to check the equality of
bivariant classes we may use Lemma 02UC. ... By Lemma 02UC it even suffices to prove the result
after blowing up `X`.* This file carries out that reduction for the classes at constant rank.

## Main results

* `Stacks.Chow.BivariantClass.eq_of_forall_birational_cap_eq` — Stacks 02UC, (3) ⇒ (1), for the
  difference of two classes: two bivariant classes are equal as soon as every integral test
  scheme admits a proper birational modification on whose fundamental class they agree.
* `Stacks.Chow.BivariantClass.cap_comp_eq_of_bivariantRestriction_cap_eq` — the caps of two
  classes along `t ≫ g` are those of their restrictions along `g`, along `t`.
* `Stacks.Chow.compositionFormulaAt_of_testBaseChange` — the composition formula for `D` along
  `t ≫ g` is the formula for the base change of `D` over `g`, along `t`.
* `Stacks.Chow.CompositionIsoCase`, `Stacks.Chow.CompositionCartierCase` — the two cases of the
  source's proof: `Y = X`, and `Y` an effective Cartier divisor, on the fundamental class of an
  integral `X`.
* `Stacks.Chow.virtualNormalGysinClass_eq_compositeVirtualNormalGysinClass_of_cases` — **the
  reduction**: the two cases imply the composition formula at constant rank, as classes.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Stacks 02UC for the difference of two classes -/

section Criterion

variable (C : ChowSituation.{u}) {W Y : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : W ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sW) (p : ℤ)

/-- **Stacks 02UC, (3) ⇒ (1), for two classes.** Two bivariant classes in `A^p(W ⟶ Y)` are equal
as soon as every integral scheme `T` locally of finite type over `Y` admits a proper birational
`T' ⟶ T` on whose fundamental class they agree, in every degree. -/
theorem BivariantClass.eq_of_forall_birational_cap_eq
    {c d : BivariantClass C (gysinSystemOfInvertible C) sW sY f hf p}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] [IsIntegral T],
      ∃ (T' : Scheme.{u}) (b : T' ⟶ T) (hb : IsProper b),
        letI := hb
        AlgebraicGeometry.IsBirational b ∧
          ∀ k : ℤ, c.cap (b ≫ g) k (fundamentalChowClass C ((b ≫ g) ≫ sY) k) =
            d.cap (b ≫ g) k (fundamentalChowClass C ((b ≫ g) ≫ sY) k)) :
    c = d := by
  refine eq_of_sub_eq_zero ?_
  refine ((BivariantClass.eq_zero_tfae_canonical C sW sY f hf p (c - d)).out 1 3).2 ?_
  intro T g _ _
  obtain ⟨T', b, hb, hbir, hcap⟩ := h g
  refine ⟨T', b, hb, hbir, fun k ↦ ?_⟩
  rw [BivariantClass.sub_cap, hcap k, sub_self]

end Criterion

/-! ### Caps along a morphism are caps of restrictions at the identity -/

section Restriction

variable (C : ChowSituation.{u}) {W Y T : Scheme.{u}} {sW : W ⟶ C.S} [LocallyOfFiniteType sW]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : W ⟶ Y} [LocallyOfFiniteType f]
  {hf : f ≫ sY = sW} {p : ℤ} (g : T ⟶ Y) [LocallyOfFiniteType g]

/-- **The caps of two classes along `t ≫ g` agree as soon as those of their restrictions along
`g : T ⟶ Y` (Stacks 0F9Z) agree along `t`.** -/
theorem BivariantClass.cap_comp_eq_of_bivariantRestriction_cap_eq
    {c d : BivariantClass C (gysinSystemOfInvertible C) sW sY f hf p} {T' : Scheme.{u}}
    (t : T' ⟶ T) [LocallyOfFiniteType t] (k : ℤ) (β : chowGroup C ((t ≫ g) ≫ sY) k)
    (h : (bivariantRestriction C (gysinSystemOfInvertible C) sW sY f hf g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).cap t k
        (chowGroupCongr C (Category.assoc t g sY) k β) =
      (bivariantRestriction C (gysinSystemOfInvertible C) sW sY f hf g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d).cap t k
        (chowGroupCongr C (Category.assoc t g sY) k β)) :
    c.cap (t ≫ g) k β = d.cap (t ≫ g) k β := by
  rw [bivariantRestriction_cap, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    bivariantRestrictionCap_apply] at h
  have h' := chowPushforwardOfIso_injective C _ _ _ _ (k - p) h
  rw [chowGroupCongr_chowGroupCongr] at h'
  exact h'

end Restriction

/-! ### The composition formula at constant rank, and its base change to a test scheme -/

section Composition

variable (C : ChowSituation.{u}) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {i : Z ⟶ Y} {j : Y ⟶ X} [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ)
  (hj : j ≫ sX = sY) (D : ConormalCompatibleVirtualNormalBundles i j) (p q : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]

/-- The composite `c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')` of the classes at constant ranks `p` and `q`,
read in degree `p + q`, the degree of `c(Z ⟶ X, 𝒩)`. -/
abbrev compositeVirtualNormalGysinClass :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX (i ≫ j)
      (comp_comp_structureMorphism_eq hi hj) ((p + q : ℕ) : ℤ) :=
  BivariantClass.copy C (gysinSystemOfInvertible C) sZ sX rfl
    (comp_comp_structureMorphism_eq hi hj) (comp_comp_structureMorphism_eq hi hj)
    (by push_cast; ring)
    (bivariantCompositeOfInvertible C sZ sY sX i j hi hj (p : ℤ) (q : ℤ)
      (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
      (virtualNormalBundleClass C sY sX j hj D.bundleYX q))

/-- **The composition formula of Stacks 0FEC on a cap**: `c(Z ⟶ X, 𝒩)` and
`c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')` agree on `α` along the test morphism `t`. -/
def CompositionFormulaAt {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) : Prop :=
  (virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) D.bundleZX
      (p + q)).cap t k α =
    (compositeVirtualNormalGysinClass C sZ sY sX hi hj D p q).cap t k α

variable {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]

/-- **The base change of the triple `D` to a test scheme `g : T ⟶ X`**, for the chosen fibre
products `Y_T = Y ×_X T` and `Z_T = Z ×_Y Y_T`. -/
abbrev testBaseChange :
    ConormalCompatibleVirtualNormalBundles (pullback.snd i (pullback.fst j g))
      (pullback.snd j g) :=
  D.baseChange _ _ (pullback.fst i (pullback.fst j g)) (pullback.fst j g) g
    (isPullback_pullbackSnd j g) (isPullback_pullbackSnd i (pullback.fst j g))

/-- The bundle of `Z_T ⟶ Y_T` in the base-changed triple is finite locally free of rank `p`. -/
instance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (testBaseChange D g).bundleZY.bundle p :=
  isFiniteLocallyFreeOfRank_modulePullback _ _ p inferInstance

/-- The bundle of `Y_T ⟶ T` in the base-changed triple is finite locally free of rank `q`. -/
instance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (testBaseChange D g).bundleYX.bundle q :=
  isFiniteLocallyFreeOfRank_modulePullback _ _ q inferInstance

/-- **The reduction to a test scheme.** If the composition formula holds for the base-changed
triple over `T` along `t : T' ⟶ T`, it holds for `D` along `t ≫ g`. This is the source's use of
the base-change clause of Stacks 0FBK together with the restriction of composites. -/
theorem compositionFormulaAt_of_testBaseChange {T' : Scheme.{u}} (t : T' ⟶ T)
    [LocallyOfFiniteType t] (k : ℤ) (β : chowGroup C ((t ≫ g) ≫ sX) k)
    (h : CompositionFormulaAt C (pullback.fst i (pullback.fst j g) ≫ sZ)
      (pullback.fst j g ≫ sY) (g ≫ sX)
      (pullbackSnd_comp_structureMorphism_eq C sZ sY i hi (pullback.fst j g))
      (pullbackSnd_comp_structureMorphism_eq C sY sX j hj g) (testBaseChange D g) p q t k
      (chowGroupCongr C (Category.assoc t g sX) k β)) :
    CompositionFormulaAt C sZ sY sX hi hj D p q (t ≫ g) k β := by
  refine BivariantClass.cap_comp_eq_of_bivariantRestriction_cap_eq C g t k β ?_
  have sqZ := isPullback_pullbackSnd i (pullback.fst j g)
  have sqY := isPullback_pullbackSnd j g
  have sqP := IsPullback.paste_horiz sqZ sqY
  have hZT : (pullback.snd i (pullback.fst j g) ≫ pullback.snd j g) ≫ (g ≫ sX) =
      pullback.fst i (pullback.fst j g) ≫ sZ :=
    comp_comp_structureMorphism_eq
      (pullbackSnd_comp_structureMorphism_eq C sZ sY i hi (pullback.fst j g))
      (pullbackSnd_comp_structureMorphism_eq C sY sX j hj g)
  -- the restriction of `c(Z ⟶ X, 𝒩)` is the class of the base-changed triple
  have hA := bivariantTransport_bivariantRestriction_virtualNormalGysinClass C sZ sX (i ≫ j)
    (comp_comp_structureMorphism_eq hi hj) _ (pullback.fst i (pullback.fst j g)) g sqP D.bundleZX
    (p + q) (pullback.fst i (pullback.fst j g) ≫ sZ) hZT
  have hA' := congrArg (fun c ↦ BivariantClass.cap c t k
    (chowGroupCongr C (Category.assoc t g sX) k β)) hA
  simp only [bivariantTransport_cap, bivariantTransportCap_apply] at hA'
  -- the restriction of the composite is the composite of the restrictions
  have hB := bivariantRestriction_copy_bivariantCompositeOfInvertible C sZ sY sX i j hi hj g
    (by push_cast; ring : (p : ℤ) + q = ((p + q : ℕ) : ℤ))
    (virtualNormalBundleClass C sZ sY i hi D.bundleZY p)
    (virtualNormalBundleClass C sY sX j hj D.bundleYX q)
  rw [bivariantRestriction_virtualNormalGysinClass, bivariantRestriction_virtualNormalGysinClass]
    at hB
  rw [hB, bivariantTransport_cap, bivariantTransportCap_apply]
  unfold CompositionFormulaAt compositeVirtualNormalGysinClass at h
  simp only [testBaseChange, ConormalCompatibleVirtualNormalBundles.baseChange_bundleZX,
    ConormalCompatibleVirtualNormalBundles.baseChange_bundleZY,
    ConormalCompatibleVirtualNormalBundles.baseChange_bundleYX] at h
  rw [← h, ← hA', chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) ?_ _ (Category.id_comp _),
    chowPushforwardOfIso_id]
  have hθρ : sqP.flip.isoPullback.inv ≫ (pullbackRightPullbackFstIso j g i).hom = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, transportPullbackIso_hom_fst, transportPullbackIso_hom_fst_assoc,
      Category.id_comp, Iso.symm_hom, hθρ, Category.comp_id]
  · simp

end Composition

/-! ### The two cases of the proof, and the reduction to them -/

section Cases

variable (C : ChowSituation.{u})

/-- **The case `Y = X` of the proof of Stacks 0FEC**: the composition formula on the fundamental
class of an integral scheme `X`, for a closed immersion `Y ⟶ X` which is an isomorphism. -/
def CompositionIsoCase : Prop :=
  ∀ {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {i : Z ⟶ Y} {j : Y ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ) (hj : j ≫ sX = sY)
    (D : ConormalCompatibleVirtualNormalBundles i j) (p q : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]
    [IsIntegral X] [IsIso j] (k : ℤ),
    CompositionFormulaAt C sZ sY sX hi hj D p q (𝟙 X) k (fundamentalChowClass C (𝟙 X ≫ sX) k)

/-- **The case `Y` an effective Cartier divisor of the proof of Stacks 0FEC**: the composition
formula on the fundamental class of an integral scheme `X` in which `Y` is an effective Cartier
divisor. -/
def CompositionCartierCase : Prop :=
  ∀ {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {i : Z ⟶ Y} {j : Y ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ) (hj : j ≫ sX = sY)
    (D : ConormalCompatibleVirtualNormalBundles i j) (p q : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]
    [IsIntegral X] (_ : Stacks.Divisors.IsEffectiveCartierDivisor j.ker) (k : ℤ),
    CompositionFormulaAt C sZ sY sX hi hj D p q (𝟙 X) k (fundamentalChowClass C (𝟙 X ≫ sX) k)

variable {C} {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {i : Z ⟶ Y} {j : Y ⟶ X} [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ)
  (hj : j ≫ sX = sY) (D : ConormalCompatibleVirtualNormalBundles i j) (p q : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]

/-- The composition formula on a fundamental class only depends on the test morphism. -/
theorem compositionFormulaAt_fundamental_congr {T : Scheme.{u}} {t t' : T ⟶ X}
    [LocallyOfFiniteType t] [LocallyOfFiniteType t'] (e : t = t') (k : ℤ)
    (h : CompositionFormulaAt C sZ sY sX hi hj D p q t k (fundamentalChowClass C (t ≫ sX) k)) :
    CompositionFormulaAt C sZ sY sX hi hj D p q t' k (fundamentalChowClass C (t' ≫ sX) k) := by
  subst e
  exact h

/-- **The reduction of Stacks 0FEC to its two cases.** By Stacks 02UC it suffices to compare the
two classes on the fundamental class of an integral `T` over `X`, after a proper birational
modification. If `Y ×_X T = T` there is nothing to modify; otherwise the blowup of `T` in the
ideal of `Y ×_X T` makes it an effective Cartier divisor (Stacks 02OS). In both cases the formula
for `D` along `T' ⟶ X` is the formula for the base-changed triple over `T'` (Stacks 0FBK and the
restriction of composites), which is one of the two cases. -/
theorem virtualNormalGysinClass_eq_compositeVirtualNormalGysinClass_of_cases
    (hiso : CompositionIsoCase C) (hcart : CompositionCartierCase C) :
    virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) D.bundleZX
        (p + q) =
      compositeVirtualNormalGysinClass C sZ sY sX hi hj D p q := by
  refine BivariantClass.eq_of_forall_birational_cap_eq C sZ sX (i ≫ j) _ _ ?_
  intro T g _ _
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  -- the formula along `b ≫ g` from the formula for the base change over `T'`
  have key : ∀ {T' : Scheme.{u}} (b : T' ⟶ T) [LocallyOfFiniteType b] [IsIntegral T'],
      (IsIso (pullback.snd j (b ≫ g)) ∨
        Stacks.Divisors.IsEffectiveCartierDivisor (pullback.snd j (b ≫ g)).ker) →
      ∀ k : ℤ, CompositionFormulaAt C sZ sY sX hi hj D p q (b ≫ g) k
        (fundamentalChowClass C ((b ≫ g) ≫ sX) k) := by
    intro T' b _ _ hcase k
    have h := compositionFormulaAt_of_testBaseChange C sZ sY sX hi hj D p q (b ≫ g) (𝟙 T') k
      (fundamentalChowClass C ((𝟙 T' ≫ b ≫ g) ≫ sX) k)
    rw [chowGroupCongr_fundamentalChowClass] at h
    have h' : CompositionFormulaAt C sZ sY sX hi hj D p q (𝟙 T' ≫ b ≫ g) k
        (fundamentalChowClass C ((𝟙 T' ≫ b ≫ g) ≫ sX) k) := by
      rcases hcase with hcase | hcase
      · exact h (hiso _ _ _ _ _ _ p q k)
      · exact h (hcart _ _ _ _ _ _ p q hcase k)
    exact compositionFormulaAt_fundamental_congr sZ sY sX hi hj D p q (Category.id_comp _) k h'
  by_cases hT : IsIso (pullback.snd j g)
  · refine ⟨T, 𝟙 T, inferInstance, isBirational_id T, fun k ↦ key (𝟙 T) (Or.inl ?_) k⟩
    rw [Category.id_comp]
    exact hT
  · obtain ⟨T', b, hb, hbir, hint, hcart'⟩ :=
      exists_isProper_isBirational_isEffectiveCartierDivisor_ker_pullbackSnd (pullback.snd j g) hT
    refine ⟨T', b, hb, hbir, fun k ↦ key b (Or.inr ?_) k⟩
    rw [← Scheme.Hom.ker_comp_of_isIso (pullbackLeftPullbackSndIso j g b).hom,
      pullbackLeftPullbackSndIso_hom_snd]
    exact hcart'

end Cases

end Stacks.Chow

end

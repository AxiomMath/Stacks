module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonicalSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRuleDifferenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackContained
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinMemberRuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeMaximality

/-!
# Bivariant classes commute with first Chern classes

In Situation 0EDT let `f : X ⟶ Y` be a morphism of good algebraic spaces over the base and let
`c ∈ A^p(X ⟶ Y)` be a bivariant class (Stacks 0ERJ).  For a good test space `Y' ⟶ Y`, with
`X' = Y' ×_Y X`, and an invertible `𝒪_{Y'}`-module `ℳ` with inverse image `𝒩` on `X'`,

  `c ∩ (c₁(ℳ) ∩ α) = c₁(𝒩) ∩ (c ∩ α)`  in  `CH_{k-p}(X')`,  for every `α ∈ CH_{k+1}(Y')`.

This is axiom (3) of Stacks 0ERJ for the triple `(ℳ, 0, D' → Y')` whose section is zero.

## Main definitions

* `AlgebraicGeometry.Space.BivariantClassCanonical.compCap`: the cap operation
  `α ↦ c ∩ (d ∩ α)` of the composite `c ∘ d` of two bivariant classes for the identity of `X`.

## Main results

* `AlgebraicGeometry.Space.vanishingLocus_zero`: the vanishing locus of the zero section is the
  whole space.
* `AlgebraicGeometry.Space.chowClassCanonical_properCyclePushforward_gysinCycleMap_of_eq_top`:
  for a section whose vanishing locus is the whole space, the Gysin map of Stacks 0ER1 pushed
  forward to the space is the cap product with the first Chern class (Stacks 0EQJ) in the Chow
  group of Stacks 0EQ6.
* `AlgebraicGeometry.Space.BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward`:
  the axiom (1) of Stacks 0ERJ on Chow groups, `c ∩ h_*x = h'_*(c ∩ x)` for every class `x`,
  through the descent of proper pushforward to Chow groups (Stacks 0EQC).
* `AlgebraicGeometry.Space.BivariantClassCanonical.cap_canonicalFirstChernCapCanonicalChowMap`:
  `c ∩ (c₁(ℳ) ∩ x) = c₁(𝒩) ∩ (c ∩ x)` for every class `x`.
* `BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward_inv_pullbackSnd`:
  for the identity of `X`, the cap operations on a test space `Y'` and on `X ×_X Y'` agree along
  the identification `Y' ≅ X ×_X Y'`.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonicalChowMap_congr_iso`: Stacks 0EPT on Chow
  groups, isomorphic invertible modules have the same cap product.

## References

* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### The zero section -/

section ZeroSection

variable {X : D.Ambient} (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)

/-- The vanishing locus of the zero section of a sheaf of modules is the whole space. -/
theorem vanishingLocus_zero : (vanishingLocus D p hp L 0).1 = ⊤ := by
  refine le_antisymm le_top ?_
  refine le_zeroSchemeSubfunctor D.site D.base D.base_mem ⟨X, hp.1⟩ L 0
    ⟨⊤, isClosedSubspace_top D.site D.base D.base_mem _⟩ fun U _ => ?_
  rw [sectionEvaluationIdealAt]
  refine (Ideal.span_le.2 ?_).trans bot_le
  rintro _ ⟨l, rfl⟩
  show l 0 ∈ (⊥ : Ideal _)
  rw [map_zero]
  exact Submodule.zero_mem _

/-- **The Gysin map of a section vanishing everywhere is the cap product with `c₁`.** Let `σ` be
a global section of an invertible `ℒ` on a good `X/B` whose vanishing locus `E = Z(σ)` is all
of `X`. Then the refined Gysin map of Stacks 0ER1, pushed forward along `i : E ⟶ X`, is the cap
product `c₁(ℒ) ∩ α` of Stacks 0EQJ in `CH_k(X)`:

`[i_*(i^*α)] = c₁(ℒ) ∩ α`  for every `α ∈ Z_{k+1}(X)`. -/
theorem chowClassCanonical_properCyclePushforward_gysinCycleMap_of_eq_top (σ : L.sections)
    (hσ : (vanishingLocus D p hp L σ).1 = ⊤) (hL : IsInvertibleSheaf D p hp L)
    (hLm : IsInvertibleModule (B := D.site) ⟨X, hp.1⟩ L) (k : ℤ) (α : CycleGroup D p (k + 1)) :
    chowClassCanonical.{u + 1} D p hp k
        (properCyclePushforward D ((vanishingLocus D p hp L σ).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L σ) p hp rfl
          (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem
            (vanishingLocus D p hp L σ).2.2) k
          (gysinCycleMap D p (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
            (sectionGysinRule D p hp L σ k hL) α)) =
      canonicalFirstChernCapCanonical.{u + 1} D p hp L hLm k α := by
  rw [properCyclePushforward_ι_eq_cycleGroupClosedPushforward D p hp _
      (vanishingLocus D p hp L σ).2, sectionGysinRule,
    cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D p hp L σ hL k,
    canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  refine (isRationallyEquivalentToZeroWithinCanonical_univ_iff D p hp k _).1
    (isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub D p hp k _ _ α
      Set.univ fun W hW _ _ => ⟨?_, Set.subset_univ _⟩)
  rw [restrictedSectionChernRule_of_le D p hp L σ hL k _ hW (by rw [hσ]; exact le_top)]
  exact isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_sub_canonicalFirstChernRule D p hp L
    hL k W hW

end ZeroSection

/-! ### Transport along equalities of degrees and isomorphisms -/

section Transport

variable {Z : D.Ambient} (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ)

/-- Transporting a Chow class along two equalities of degrees in turn is transporting it along
their composite. -/
theorem chowGroupCanonicalDegreeCongr_trans {a b c : ℤ} (h₁ : a = b) (h₂ : b = c)
    (z : chowGroupCanonical.{u + 1} D sZ hZ a) :
    chowGroupCanonicalDegreeCongr D sZ hZ h₂ (chowGroupCanonicalDegreeCongr D sZ hZ h₁ z) =
      chowGroupCanonicalDegreeCongr D sZ hZ (h₁.trans h₂) z := by
  subst h₁ h₂
  rfl

/-- The cap product with a first Chern class of Stacks 0EQY commutes with the transport along an
equality of degrees. -/
theorem chowGroupCanonicalDegreeCongr_canonicalFirstChernCapCanonicalChowMap
    (N : Modules.{u, u} D.site D.base D.base_mem Z hZ.1)
    (hN : IsInvertibleModule (B := D.site) ⟨Z, hZ.1⟩ N) {a b n : ℤ} (h : a = b)
    (h₁ : n = a + 1) (h₂ : n = b + 1) (z : chowGroupCanonical.{u + 1} D sZ hZ n) :
    chowGroupCanonicalDegreeCongr D sZ hZ h
        (canonicalFirstChernCapCanonicalChowMap D sZ hZ a N hN
          (chowGroupCanonicalDegreeCongr D sZ hZ h₁ z)) =
      canonicalFirstChernCapCanonicalChowMap D sZ hZ b N hN
        (chowGroupCanonicalDegreeCongr D sZ hZ h₂ z) := by
  subst h
  rfl

/-- **Stacks 0EPT on Chow groups.** Isomorphic invertible modules have the same cap product with
the first Chern class, `CH_{k+1}(Z) ⟶ CH_k(Z)`. -/
theorem canonicalFirstChernCapCanonicalChowMap_congr_iso
    (N N' : Modules.{u, u} D.site D.base D.base_mem Z hZ.1)
    (hN : IsInvertibleModule (B := D.site) ⟨Z, hZ.1⟩ N)
    (hN' : IsInvertibleModule (B := D.site) ⟨Z, hZ.1⟩ N') (e : N ≅ N') (k : ℤ)
    (z : chowGroupCanonical.{u + 1} D sZ hZ (k + 1)) :
    canonicalFirstChernCapCanonicalChowMap D sZ hZ k N hN z =
      canonicalFirstChernCapCanonicalChowMap D sZ hZ k N' hN' z := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
  exact canonicalFirstChernCapCanonical_congr_iso hZ N N' hN hN' e k α

end Transport

/-! ### Bivariant classes on Chow groups -/

section Bivariant

variable {X Y : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space}
  {hY : D.IsGood sY} {f : X ⟶ Y} {hf : f ≫ sY = sX} {p : ℤ}

/-- **Stacks 0ERJ (1) on Chow groups.** For a bivariant class `c`, good test spaces
`h : Y'' ⟶ Y'` and `g : Y' ⟶ Y` with `h` proper, and the induced proper morphism
`h' : Y'' ×_Y X ⟶ Y' ×_Y X`, `c ∩ h_*x = h'_*(c ∩ x)` for every class `x ∈ CH_k(Y'')`.  The
proper pushforward is the one of Stacks 0EQC on the Chow groups of Stacks 0EQ6; the test space
`Y''` is given through any morphism `g₂` equal to `h ≫ g`. -/
theorem BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward
    (c : BivariantClassCanonical.{u + 1} D sX hX sY hY f hf p) {Y' Y'' : D.Ambient} (g : Y' ⟶ Y)
    (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX)) (h : Y'' ⟶ Y')
    {g₂ : Y'' ⟶ Y} (hg₂ : h ≫ g = g₂) (hY'' : D.IsGood (g₂ ≫ sY))
    (hX'' : D.IsGood (pullback.fst f g₂ ≫ sX)) (hh : IsProper D.site D.base D.base_mem h)
    (h' : pullback f g₂ ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f g₂) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f g₂)
    (hh' : IsProper D.site D.base D.base_mem h') (k : ℤ)
    (x : chowGroupCanonical.{u + 1} D (g₂ ≫ sY) hY'' k) :
    c.cap g hY' hX' k (chowGroupCanonicalProperPushforward.{u + 1} D (g₂ ≫ sY) hY'' (g ≫ sY) hY'
        (by rw [← hg₂, Category.assoc]) hh k x) =
      chowGroupCanonicalProperPushforward.{u + 1} D (pullback.fst f g₂ ≫ sX) hX''
        (pullback.fst f g ≫ sX) hX' (by rw [← Category.assoc, hfst]) hh' (k - p)
        (c.cap g₂ hY'' hX'' k x) := by
  subst hg₂
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  obtain ⟨β, h₁, h₂⟩ := c.proper_naturality g hY' hX' h hY'' hX'' hh h' sq hfst hh' k α
  show c.cap g hY' hX' k (chowGroupCanonicalProperPushforward.{u + 1} D _ hY'' _ hY' _ hh k
      (chowClassCanonical.{u + 1} D _ hY'' k α)) =
    chowGroupCanonicalProperPushforward.{u + 1} D _ hX'' _ hX' _ hh' (k - p)
      (c.cap (h ≫ g) hY'' hX'' k (chowClassCanonical.{u + 1} D _ hY'' k α))
  rw [chowGroupCanonicalProperPushforward_chowClassCanonical, h₂, h₁,
    chowGroupCanonicalProperPushforward_chowClassCanonical]

/-- The cap operation of a bivariant class commutes with the transport along an equality of
degrees. -/
theorem BivariantClassCanonical.cap_chowGroupCanonicalDegreeCongr
    (c : BivariantClassCanonical.{u + 1} D sX hX sY hY f hf p) {Y' : D.Ambient} (g : Y' ⟶ Y)
    (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX)) {k l : ℤ} (h : k = l)
    (y : chowGroupCanonical.{u + 1} D (g ≫ sY) hY' k) :
    c.cap g hY' hX' l (chowGroupCanonicalDegreeCongr D (g ≫ sY) hY' h y) =
      chowGroupCanonicalDegreeCongr D (pullback.fst f g ≫ sX) hX' (by rw [h])
        (c.cap g hY' hX' k y) := by
  subst h
  rfl

/-- Transporting the class of a transported cycle back along an equality of degrees recovers the
class of the cycle. -/
theorem chowGroupCanonicalDegreeCongr_chowClassCanonical_cycleGroupDegreeCongr {Z : D.Ambient}
    (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) {k l : ℤ} (h₁ : l = k) (h₂ : k = l)
    (β : CycleGroup D sZ l) :
    chowGroupCanonicalDegreeCongr D sZ hZ h₂
        (chowClassCanonical.{u + 1} D sZ hZ k (cycleGroupDegreeCongr D sZ h₁ β)) =
      chowClassCanonical.{u + 1} D sZ hZ l β := by
  subst h₁
  rfl

/-- **A bivariant class commutes with the first Chern class of a pulled-back invertible sheaf.**
Let `c ∈ A^p(X ⟶ Y)` be a bivariant class (Stacks 0ERJ), `g : Y' ⟶ Y` a good test space with
`X' = Y' ×_Y X`, and `ℳ` an invertible `𝒪_{Y'}`-module with inverse image `𝒩` on `X'`.  Then

`c ∩ (c₁(ℳ) ∩ x) = c₁(𝒩) ∩ (c ∩ x)`  in  `CH_{k-p}(X')`  for every `x ∈ CH_{k+1}(Y')`,

the cap products with first Chern classes being those of Stacks 0EQY on the Chow groups of
Stacks 0EQ6. -/
theorem BivariantClassCanonical.cap_canonicalFirstChernCapCanonicalChowMap
    (c : BivariantClassCanonical.{u + 1} D sX hX sY hY f hf p) {Y' : D.Ambient} (g : Y' ⟶ Y)
    (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX))
    (M : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y', hY'.1⟩ M) (k : ℤ)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sY) hY' (k + 1)) :
    c.cap g hY' hX' k (canonicalFirstChernCapCanonicalChowMap D (g ≫ sY) hY' k M hM x) =
      canonicalFirstChernCapCanonicalChowMap D (pullback.fst f g ≫ sX) hX' (k - p)
        (bivariantPullbackSheaf D sX sY f g hY' hX' M)
        (modulePullbackInvertible (bivariantTestProjection D sX sY f g hY' hX') M hM)
        (chowGroupCanonicalDegreeCongr D (pullback.fst f g ≫ sX) hX' (by omega)
          (c.cap g hY' hX' (k + 1) x)) := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  show c.cap g hY' hX' k (canonicalFirstChernCapCanonicalChowMap D (g ≫ sY) hY' k M hM
      (chowClassCanonical.{u + 1} D (g ≫ sY) hY' (k + 1) α)) =
    canonicalFirstChernCapCanonicalChowMap D (pullback.fst f g ≫ sX) hX' (k - p)
      (bivariantPullbackSheaf D sX sY f g hY' hX' M)
      (modulePullbackInvertible (bivariantTestProjection D sX sY f g hY' hX') M hM)
      (chowGroupCanonicalDegreeCongr D (pullback.fst f g ≫ sX) hX' (by omega)
        (c.cap g hY' hX' (k + 1) (chowClassCanonical.{u + 1} D (g ≫ sY) hY' (k + 1) α)))
  have hMs : IsInvertibleSheaf D (g ≫ sY) hY' M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM
  have hE : (vanishingLocus D (g ≫ sY) hY' M 0).1 = ⊤ := vanishingLocus_zero D (g ≫ sY) hY' M
  have : IsIso (vanishingLocus D (g ≫ sY) hY' M 0).1.ι := (Subfunctor.eq_top_iff_isIso _).mp hE
  have hEg : D.IsGood (((vanishingLocus D (g ≫ sY) hY' M 0).1.ι ≫ g) ≫ sY) :=
    isGood_vanishingLocus_comp D sY g hY' M 0
  have hXd := isGood_pullback_fst D hX hY f ((vanishingLocus D (g ≫ sY) hY' M 0).1.ι ≫ g) hEg
  have hisoX := bivariantPullbackVanishingLocusIso_hom_ι D sX sY f g hY' hX' M 0 hMs
  have hbaseX : (bivariantPullbackVanishingLocusIso D sX sY f g hY' hX' M 0 hMs).hom ≫
      ((bivariantPullbackVanishingLocus D sX sY f g hY' hX' M 0).1.ι ≫ pullback.fst f g ≫ sX) =
      pullback.fst f ((vanishingLocus D (g ≫ sY) hY' M 0).1.ι ≫ g) ≫ sX := by
    rw [reassoc_of% hisoX]
    simp [bivariantBaseChangeMap]
  have hP : ∀ {A B : D.Ambient} (u : A ⟶ B) [IsIso u], IsProper D.site D.base D.base_mem u :=
    fun u _ => isProper_of_isIso D.site D.base D.base_mem u
  obtain ⟨β, γ, e₁, e₂, e₃⟩ := c.gysin_naturality g hY' hX' M 0 hMs hXd
    (bivariantPullbackVanishingLocusIso D sX sY f g hY' hX' M 0 hMs) hisoX hbaseX
    (hP _) k α
  have hsq := isPullback_bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' M 0).1.ι
  have : IsIso (bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' M 0).1.ι) :=
    hsq.isIso_snd_of_isIso
  have hfst : bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' M 0).1.ι ≫
      pullback.fst f g = pullback.fst f ((vanishingLocus D (g ≫ sY) hY' M 0).1.ι ≫ g) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hfst' : bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' M 0).1.ι ≫
      pullback.fst f g ≫ sX = pullback.fst f ((vanishingLocus D (g ≫ sY) hY' M 0).1.ι ≫ g) ≫ sX :=
    by rw [← Category.assoc, hfst]
  have hprop := BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward D c g hY' hX'
    (vanishingLocus D (g ≫ sY) hY' M 0).1.ι rfl hEg hXd (hP _) _ hsq hfst (hP _) k
    (chowClassCanonical.{u + 1} D _ hEg k
      (gysinCycleMap D (g ≫ sY) (vanishingLocus D (g ≫ sY) hY' M 0)
        (isGood_vanishingLocus D (g ≫ sY) hY' M 0) k (sectionGysinRule D (g ≫ sY) hY' M 0 k hMs)
        α))
  have hz := chowClassCanonical_properCyclePushforward_gysinCycleMap_of_eq_top D (g ≫ sY) hY' M 0
    hE hMs hM k α
  have hleft : c.cap g hY' hX' k (canonicalFirstChernCapCanonical.{u + 1} D (g ≫ sY) hY' M hM k α) =
      chowClassCanonical.{u + 1} D (pullback.fst f g ≫ sX) hX' (k - p)
        (properCyclePushforward D _ hXd _ hX' hfst' (hP _).2.1.2 (k - p) γ) :=
    ((congrArg (c.cap g hY' hX' k) hz.symm).trans hprop).trans
      (congrArg (chowGroupCanonicalProperPushforward.{u + 1} D _ hXd _ hX' hfst' (hP _) (k - p))
        e₂)
  have hE' : (bivariantPullbackVanishingLocus D sX sY f g hY' hX' M 0).1 = ⊤ := by
    refine (congrArg Subtype.val (pullbackDivisor_eq_vanishingLocus D (g ≫ sY) hY'
      (pullback.fst f g ≫ sX) hX' (bivariantTestProjection D sX sY f g hY' hX') M 0 hMs)).symm.trans
      ?_
    show (vanishingLocus D (g ≫ sY) hY' M 0).1.preimage (pullback.snd f g) = ⊤
    rw [hE]
    rfl
  have : IsIso (bivariantPullbackVanishingLocus D sX sY f g hY' hX' M 0).1.ι :=
    (Subfunctor.eq_top_iff_isIso _).mp hE'
  have hz' := chowClassCanonical_properCyclePushforward_gysinCycleMap_of_eq_top D _ hX'
    (bivariantPullbackSheaf D sX sY f g hY' hX' M)
    (bivariantPullbackSection D sX sY f g hY' hX' M 0) hE'
    (isInvertibleSheaf_bivariantPullbackSheaf D sX sY f g hY' hX' M hMs)
    (modulePullbackInvertible (bivariantTestProjection D sX sY f g hY' hX') M hM) (k - p) β
  have h₃ := congrArg (chowGroupCanonicalProperPushforward.{u + 1} D _
    (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX'
      (bivariantPullbackSheaf D sX sY f g hY' hX' M)
      (bivariantPullbackSection D sX sY f g hY' hX' M 0)) _ hX' rfl
    (hP _) (k - p)) e₃
  have hR : canonicalFirstChernCapCanonicalChowMap D (pullback.fst f g ≫ sX) hX' (k - p)
      (bivariantPullbackSheaf D sX sY f g hY' hX' M)
      (modulePullbackInvertible (bivariantTestProjection D sX sY f g hY' hX') M hM)
      (chowGroupCanonicalDegreeCongr D (pullback.fst f g ≫ sX) hX' (by omega)
        (c.cap g hY' hX' (k + 1) (chowClassCanonical.{u + 1} D (g ≫ sY) hY' (k + 1) α))) =
      canonicalFirstChernCapCanonical.{u + 1} D (pullback.fst f g ≫ sX) hX'
        (bivariantPullbackSheaf D sX sY f g hY' hX' M)
        (modulePullbackInvertible (bivariantTestProjection D sX sY f g hY' hX') M hM) (k - p)
        β := by
    rw [e₁, chowGroupCanonicalDegreeCongr_chowClassCanonical_cycleGroupDegreeCongr]
    rfl
  have hX := congrArg (chowClassCanonical.{u + 1} D (pullback.fst f g ≫ sX) hX' (k - p))
    ((properCyclePushforward_congr D _ hXd _ hX' hisoX.symm hfst'
      (hP _).2.1.2 _ _ _ γ).trans
      (properCyclePushforward_comp D _ _ _ hXd
        (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX'
          (bivariantPullbackSheaf D sX sY f g hY' hX' M)
          (bivariantPullbackSection D sX sY f g hY' hX' M 0)) hX' hbaseX rfl (hP _) (hP _)
        (k - p) γ).symm)
  exact hleft.trans (hX.trans ((h₃.trans hz').trans hR.symm))

/-- For the identity of `X` the test space `g : Y' ⟶ X` and the test space
`X' = X ×_X Y' ⟶ X` are identified by the inverse of the second projection, and the cap
operations of a bivariant class on the two agree along it: `c ∩ e_*x = e'_*(c ∩ x)`, where
`e : Y' ≅ X'` and `e' : X' ≅ X ×_X X'` are the inverses of the second projections.  This
is axiom (1) of Stacks 0ERJ along the isomorphism `e`. -/
theorem BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward_inv_pullbackSnd
    {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}
    (c : BivariantClassCanonical.{u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) p)
    {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (hX'' : D.IsGood (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) g) ≫ sX)) (k : ℤ)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    c.cap (pullback.fst (𝟙 X) g) hX' hX'' k
        (chowGroupCanonicalProperPushforward.{u + 1} D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX)
          hX' (by rw [← Category.assoc, (IsIso.inv_comp_eq _).2
            ((Category.comp_id _).symm.trans pullback.condition)])
          (isProper_of_isIso D.site D.base D.base_mem (inv (pullback.snd (𝟙 X) g))) k x) =
      chowGroupCanonicalProperPushforward.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX'
        (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) g) ≫ sX) hX''
        (by rw [← Category.assoc, (IsIso.inv_comp_eq _).2
            ((Category.comp_id _).symm.trans pullback.condition)])
        (isProper_of_isIso D.site D.base D.base_mem
          (inv (pullback.snd (𝟙 X) (pullback.fst (𝟙 X) g)))) (k - p) (c.cap g hY' hX' k x) := by
  have hinv : ∀ {W : D.Ambient} (g : W ⟶ X),
      inv (pullback.snd (𝟙 X) g) ≫ pullback.fst (𝟙 X) g = g := fun g =>
    (IsIso.inv_comp_eq _).2 ((Category.comp_id _).symm.trans pullback.condition)
  refine BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward D c
    (pullback.fst (𝟙 X) g) hX' hX'' (inv (pullback.snd (𝟙 X) g)) (hinv g) hY' hX'
    (isProper_of_isIso D.site D.base D.base_mem _)
    (inv (pullback.snd (𝟙 X) (pullback.fst (𝟙 X) g))) (IsPullback.of_vert_isIso ⟨?_⟩) ?_
    (isProper_of_isIso D.site D.base D.base_mem _) k x
  · simp
  · exact hinv _

/-- **The cap operation of a composite of bivariant classes for the identity.** For bivariant
classes `c ∈ A^p(X)` and `d ∈ A^q(X)` of the identity of `X` (Stacks 0ERJ), the composite
`c ∘ d ∈ A^{p+q}(X)` defined after Stacks 0ERJ caps a class `α` on a test space `g : Y' ⟶ X` as

  `(c ∘ d) ∩ α = c ∩ (d ∩ α)`,

where `d ∩ α` lies on `X' = X ×_X Y'` and `c` is applied at the test space
`X' ⟶ X`, landing on `X ×_X X'`. -/
def BivariantClassCanonical.compCap {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}
    {q : ℤ} (c : BivariantClassCanonical.{u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) p)
    (d : BivariantClassCanonical.{u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) q)
    {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k →+
      chowGroupCanonical.{u + 1} D (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) g) ≫ sX)
        (isGood_pullback_fst D hX hX (𝟙 X) (pullback.fst (𝟙 X) g)
          (isGood_pullback_fst D hX hX (𝟙 X) g hY')) (k - q - p) :=
  (c.cap (pullback.fst (𝟙 X) g) (isGood_pullback_fst D hX hX (𝟙 X) g hY')
      (isGood_pullback_fst D hX hX (𝟙 X) (pullback.fst (𝟙 X) g)
        (isGood_pullback_fst D hX hX (𝟙 X) g hY')) (k - q)).comp
    (d.cap g hY' (isGood_pullback_fst D hX hX (𝟙 X) g hY') k)

/-- The cap operation of the composite `c ∘ d` sends `α` to `c ∩ (d ∩ α)`. -/
theorem BivariantClassCanonical.compCap_apply {X : D.Ambient} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {q : ℤ}
    (c : BivariantClassCanonical.{u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) p)
    (d : BivariantClassCanonical.{u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) q)
    {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k : ℤ)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    BivariantClassCanonical.compCap D c d g hY' k x =
      c.cap (pullback.fst (𝟙 X) g) (isGood_pullback_fst D hX hX (𝟙 X) g hY')
        (isGood_pullback_fst D hX hX (𝟙 X) (pullback.fst (𝟙 X) g)
          (isGood_pullback_fst D hX hX (𝟙 X) g hY')) (k - q)
        (d.cap g hY' (isGood_pullback_fst D hX hX (𝟙 X) g hY') k x) :=
  rfl

end Bivariant

end AlgebraicGeometry.Space

end

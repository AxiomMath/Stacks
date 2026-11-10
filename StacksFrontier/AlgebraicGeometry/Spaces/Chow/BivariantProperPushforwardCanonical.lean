module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCapCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSides
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinProperPushforward

/-!
# Proper pushforward of bivariant classes

In the situation of Stacks 0EDT let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of good algebraic
spaces over the base `B`, with `f` proper, and let `c ∈ A^p(X ⟶ Z)` be a bivariant class of
degree `p` for the composite (Stacks 0ERJ).  For a test space `Z' ⟶ Z` write
`f' : Z' ×_Z X ⟶ Z' ×_Z Y` for the base change of `f`.  **Stacks 0ERQ** asserts that the rule

  `α ↦ f'_*(c ∩ α)`,  `CH_k(Z') ⟶ CH_{k-p}(Z' ×_Z Y)`,

is a bivariant class of degree `p` for `g`, that is, an element `f_* ∘ c ∈ A^p(Y ⟶ Z)`.  The
source's proof runs the three axioms of Stacks 0ERJ through Stacks 0EP2 (functoriality of proper
pushforward), Stacks 0EPD (proper pushforward commutes with flat pullback in a cartesian square)
and Stacks 0ER5 (the refined Gysin map commutes with proper pushforward).  This file follows it.

## Main definitions

* `AlgebraicGeometry.Space.BivariantClassCanonical.properPushforward` — **Stacks 0ERQ**, the
  class `f_* ∘ c ∈ A^p(Y ⟶ Z)` over the Chow groups `AlgebraicGeometry.Space.chowGroupCanonical`.
* `AlgebraicGeometry.Space.BivariantClassCanonical.properPushforwardCap` — its cap operation, the
  rule `α ↦ f'_*(c ∩ α)`.
* `AlgebraicGeometry.Space.bivariantPullbackVanishingLocusIso` — for a test space `Y' ⟶ Y` of a
  morphism `X ⟶ Y` and an invertible sheaf with a section on `Y'` vanishing along `D' ⊆ Y'`, the
  identification of `D' ×_Y X` with the vanishing locus of the pulled-back section on
  `Y' ×_Y X` (Stacks 0ER3).

## Main results

* `AlgebraicGeometry.Space.BivariantClassCanonical.properPushforward_cap_apply` — **Stacks 0ERQ**,
  the class `f_* ∘ c` caps by the rule `α ↦ f'_*(c ∩ α)`.
* `AlgebraicGeometry.Space.isGood_pullback_fst` — a fibre product of good algebraic spaces over
  a good algebraic space is good.
* `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_properCyclePushforward_of_comp_eq` —
  Stacks 0ER5 in `CH_k` for a section pulled back along a composite `X'' ⟶ X' ⟶ X`, the refined
  Gysin map on `X''` being that of the section pulled back in one step.
* `AlgebraicGeometry.Space.isPullback_bivariantBaseChangeMap_bivariantPushforwardBaseChange` — the
  base changes of `f` over two test spaces and the base changes of the morphism between them form
  a cartesian square.

## Implementation notes

The bivariant classes are `AlgebraicGeometry.Space.BivariantClassCanonical`, whose cap operations
take values in the Chow groups of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK and whose
axioms are stated through cycle representatives; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical`.

The Chow groups `AlgebraicGeometry.Space.chowGroupCanonical.{w}` carry the universe `w` of the
index types of the locally finite families of principal divisors presenting rational
equivalence.  The construction is stated at every level `w = max (u + 1) v`, where `u` is the
universe of the algebraic spaces; these are the levels at which every locally finite family of
integral closed subspaces is available, so the relation is the source's.  Stacks 0ER5
(`AlgebraicGeometry.Space.chowClassCanonical_sectionGysin_properPushforward_eq`) is stated at the
level `u + 1`, and is carried to `max (u + 1) v` by
`AlgebraicGeometry.Space.chowClassCanonical_eq_uliftIndex`.

Every input of the axioms of `c` is produced, not assumed.  Goodness of the fibre products
`Z' ×_Z X` is `AlgebraicGeometry.Space.isGood_pullback_fst`; properness, flatness and relative
dimension of the base changes are Stacks 0EPD; the identification of `D' ×_Z X` with the
vanishing locus of the pulled-back section that the Gysin axiom of `c` asks for is
`AlgebraicGeometry.Space.bivariantPullbackVanishingLocusIso`.

In the Gysin axiom the section on `Z' ×_Z X` is pulled back from `Z'` in one step, while Stacks
0ER5 along `f' : Z' ×_Z X ⟶ Z' ×_Z Y` pulls it back in two steps, through `Z' ×_Z Y`.  The two
vanishing loci agree and the two refined Gysin maps agree in `CH_k`, by the comparison
`a^*(b^*ℒ) ≅ (a ≫ b)^*ℒ` of
`Space.isCanonicallyRationallyEquivalentToZeroWithin_closedPushforward_sectionGysinRule_comp_sub`;
that is
`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_properCyclePushforward_of_comp_eq`.

## References

* [Stacks Project, Tag 0ERQ](https://stacks.math.columbia.edu/tag/0ERQ)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### Goodness of fibre products -/

/-- The fibre product `Z' ×_Z X` of good algebraic spaces over the base is good over the base,
through its projection to `X`. -/
theorem isGood_pullback_fst {X Z Z' : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    {sZ : Z ⟶ D.space} (hZ : D.IsGood sZ) (f : X ⟶ Z) (q : Z' ⟶ Z) (hZ' : D.IsGood (q ≫ sZ)) :
    D.IsGood (pullback.fst f q ≫ sX) := by
  have hP : IsAlgebraicSpace D.site D.base D.base_mem (pullback f q) :=
    isAlgebraicSpace_pullback D.site D.base D.base_mem f q hX.1 hZ'.1 hZ.1
  have hqQS : IsQuasiSeparated D.site D.base D.base_mem q :=
    isQuasiSeparated_of_comp D.site D.base D.base_mem q sZ hZ'.2.1
  have hqLFT : IsLocallyOfFiniteType D.site D.base D.base_mem q :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hZ'.1 hZ.1 D.isAlgebraicSpace q sZ
      hZ'.2.2
  refine ⟨hP, ?_, ?_⟩
  · exact isQuasiSeparated_comp D.site D.base D.base_mem hP hX.1 _ _
      (isQuasiSeparated_of_isPullback D.site D.base D.base_mem
        (IsPullback.of_hasPullback f q).flip hqQS) hX.2.1
  · exact isLocallyOfFiniteType_comp D.site D.base D.base_mem hP hX.1 D.isAlgebraicSpace _ _
      (IsLocallyOfFiniteType.of_isPullback D.site D.base D.base_mem
        (IsPullback.of_hasPullback f q) hZ'.1 hZ.1 hqLFT) hX.2.2

/-! ### The base change of a vanishing locus -/

/-- Equal closed subspaces have isomorphic underlying functors, compatibly with their
inclusions. -/
theorem eqToIso_hom_ι_closedSubspaces {X : D.Ambient}
    {E F : ClosedSubspaces D.site D.base D.base_mem X} (h : E = F) :
    (eqToIso (congrArg (fun E : ClosedSubspaces D.site D.base D.base_mem X => E.1.toFunctor)
      h)).hom ≫ F.1.ι = E.1.ι := by
  subst h
  simp

/-- Equal closed subspaces have isomorphic underlying functors, compatibly with their inclusions:
the inverse direction. -/
theorem eqToIso_inv_ι_closedSubspaces {X : D.Ambient}
    {E F : ClosedSubspaces D.site D.base D.base_mem X} (h : E = F) :
    (eqToIso (congrArg (fun E : ClosedSubspaces D.site D.base D.base_mem X => E.1.toFunctor)
      h)).inv ≫ E.1.ι = F.1.ι := by
  subst h
  simp

section VanishingLocusPullback

variable {X Y Y' : D.Ambient} (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (f : X ⟶ Y) (g : Y' ⟶ Y)
  (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX))
  (L : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (t : L.sections)
  (hL : IsInvertibleSheaf D (g ≫ sY) hY' L)

/-- **Stacks 0ER3 for a test space.** For a test space `g : Y' ⟶ Y` of `f : X ⟶ Y` and an
invertible `ℒ'` on `Y'` with a section `s'` vanishing along `D' ⊆ Y'`, the base change
`D' ×_Y X` is the vanishing locus `E' ⊆ Y' ×_Y X` of the pulled-back section. -/
def bivariantPullbackVanishingLocusIso :
    pullback f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≅
      (bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.toFunctor :=
  (isPullback_bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' L t).1.ι).isoIsPullback
      _ _ (pullbackDivisor_isPullback D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
        (bivariantTestProjection D sX sY f g hY' hX') L t) ≪≫
    eqToIso (congrArg
      (fun E : ClosedSubspaces D.site D.base D.base_mem (pullback f g) => E.1.toFunctor)
      (pullbackDivisor_eq_vanishingLocus D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
        (bivariantTestProjection D sX sY f g hY' hX') L t hL))

/-- The identification `D' ×_Y X ≅ E'` is compatible with the maps to `Y' ×_Y X`. -/
@[reassoc (attr := simp)]
theorem bivariantPullbackVanishingLocusIso_hom_ι :
    (bivariantPullbackVanishingLocusIso D sX sY f g hY' hX' L t hL).hom ≫
        (bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.ι =
      bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' L t).1.ι := by
  rw [bivariantPullbackVanishingLocusIso, Iso.trans_hom, Category.assoc,
    eqToIso_hom_ι_closedSubspaces, IsPullback.isoIsPullback_hom_snd]
  exact pullbackDivisor_eq_vanishingLocus D _ _ _ _ _ L t hL

end VanishingLocusPullback

/-! ### Pushing forward from equal closed subspaces -/

section ClosedSubspacePushforward

variable {X' X'' : D.Ambient} {p' : X' ⟶ D.space} (hp' : D.IsGood p') {p'' : X'' ⟶ D.space}
  (hp'' : D.IsGood p'') {a : X'' ⟶ X'} (hab : a ≫ p' = p'')
  (ha : IsProper D.site D.base D.base_mem a)

/-- Let `a : X'' ⟶ X'` be proper, `E ⊆ E''` closed subspaces of `X''` and `E'` a closed subspace
of `X'`, with morphisms `g : E'' ⟶ E'` and `m : E ⟶ E'` over `a`.  Pushing a cycle on `E` forward
to `E''` and then along `g` is pushing it forward along `m`. -/
theorem properCyclePushforward_cycleGroupClosedPushforward_homOfLe
    {E E'' : ClosedSubspaces D.site D.base D.base_mem X''} (hle : E.1 ≤ E''.1)
    {E' : ClosedSubspaces D.site D.base D.base_mem X'}
    {gE : E''.1.toFunctor ⟶ E'.1.toFunctor} (hgE : gE ≫ E'.1.ι = E''.1.ι ≫ a)
    {m : E.1.toFunctor ⟶ E'.1.toFunctor} (hm : m ≫ E'.1.ι = E.1.ι ≫ a) (k : ℤ)
    (y : CycleGroup D (E.1.ι ≫ p'') k) :
    properCyclePushforward D (E''.1.ι ≫ p'') (isGood_closedSubspace D p'' hp'' E'')
        (E'.1.ι ≫ p') (isGood_closedSubspace D p' hp' E')
        (comp_structure_of_comp_ι_eq_comp_ι D hab hgE)
        (isQuasiCompact_of_comp_ι_eq_comp_ι D hp' hp'' ha.2.1.2 hgE) k
        (cycleGroupClosedPushforward D E''.2.1 E.2.1
          (D.isDecentSpace_of_isGood _ (isGood_closedSubspace D p'' hp'' E''))
          (isClosedImmersion_homOfLe' D.site D.base D.base_mem E.2.2 hle) _
          (isGood_closedSubspace D p'' hp'' E'').2.2 _
          (by rw [← Category.assoc, Subfunctor.homOfLe_ι]) k y) =
      properCyclePushforward D (E.1.ι ≫ p'') (isGood_closedSubspace D p'' hp'' E)
        (E'.1.ι ≫ p') (isGood_closedSubspace D p' hp' E')
        (comp_structure_of_comp_ι_eq_comp_ι D hab hm)
        (isQuasiCompact_of_comp_ι_eq_comp_ι D hp' hp'' ha.2.1.2 hm) k y := by
  apply injective_cycleGroupClosedPushforward D hp'.1 E'.2.1 (D.isDecentSpace_of_isGood p' hp')
    E'.2.2 p' hp'.2.2 (E'.1.ι ≫ p') rfl k
  rw [← properCyclePushforward_cycleGroupClosedPushforward_of_comp_eq D hp'' hp'
      (isGood_closedSubspace D p'' hp'' E'') (isGood_closedSubspace D p' hp' E') E''.2.2 rfl
      E'.2.2 rfl hgE hab ha.2.1.2,
    cycleGroupClosedPushforward_cycleGroupClosedPushforward D hp''.1 E''.2.1 E.2.1
      (D.isDecentSpace_of_isGood p'' hp'')
      (D.isDecentSpace_of_isGood _ (isGood_closedSubspace D p'' hp'' E''))
      (Subfunctor.homOfLe_ι hle) (isClosedImmersion_homOfLe' D.site D.base D.base_mem E.2.2 hle)
      E''.2.2 E.2.2 p'' hp''.2.2 _ (isGood_closedSubspace D p'' hp'' E'').2.2 _ rfl _ rfl,
    properCyclePushforward_cycleGroupClosedPushforward_of_comp_eq D hp'' hp'
      (isGood_closedSubspace D p'' hp'' E) (isGood_closedSubspace D p' hp' E') E.2.2 rfl
      E'.2.2 rfl hm hab ha.2.1.2]

end ClosedSubspacePushforward

/-! ### Stacks 0ER5 along a section pulled back in two steps -/

/-- Two cycles whose difference is canonically rationally equivalent to zero within some set of
points have the same class in `CH_k`. -/
theorem chowClassCanonical_eq_of_isCanonicallyRationallyEquivalentToZeroWithin_sub
    {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX} {k : ℤ} {α β : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k (α - β) T) :
    chowClassCanonical.{v} D sX hX k α = chowClassCanonical.{v} D sX hX k β := by
  rw [← sub_eq_zero, ← map_sub, chowClassCanonical_eq_zero_iff]
  exact h.isRationallyEquivalentToZeroCanonical

/-- Two cycles with the same class in `CH_k` at the universe level `u + 1` of the index types of
the families presenting rational equivalence have the same class at every level `max (u + 1) v`:
a presenting family indexed in `u + 1` is reindexed along `ULift`
(`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical.uliftIndex`). -/
theorem chowClassCanonical_eq_uliftIndex
    {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX} {k : ℤ} {α β : CycleGroup D sX k}
    (h : chowClassCanonical.{u + 1} D sX hX k α = chowClassCanonical.{u + 1} D sX hX k β) :
    chowClassCanonical.{max (u + 1) v} D sX hX k α =
      chowClassCanonical.{max (u + 1) v} D sX hX k β := by
  rw [← sub_eq_zero, ← map_sub, chowClassCanonical_eq_zero_iff] at h ⊢
  exact h.uliftIndex

section CompositeGysin

variable {X X' X'' : D.Ambient}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (p'' : X'' ⟶ D.space) (hp'' : D.IsGood p'')
    (a : (⟨X'', hp''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X', hp'.1⟩)
    (b : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (c : (⟨X'', hp''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (hL : IsInvertibleSheaf D p hp L)
    (s : L.sections)

/-- **Stacks 0ER5 for a section pulled back in two steps.** Let `b : X' ⟶ X` and a proper
`a : X'' ⟶ X'` be morphisms of good algebraic spaces over the base, `c = a ≫ b`, and let `ℒ` be
invertible on `X` with a global section `s`.  Write `E' = Z(b^*s) ⊆ X'` and
`E'' = Z(c^*s) ⊆ X''`, and let `m : E'' ⟶ E'` lie over `a`.  For every `(k+1)`-cycle `β` on
`X''`,

  `i'^* a_* β = m_* (i'')^* β`  in `CH_k(E')`,

the refined Gysin maps being those of Stacks 0ER1 for `(b^*ℒ, b^*s)` on `X'` and for
`(c^*ℒ, c^*s)` on `X''`. -/
theorem chowClassCanonical_gysinCycleMap_properCyclePushforward_of_comp_eq
    (habc : a ≫ b = c) (hab : a.hom ≫ p' = p'') (ha : IsProper D.site D.base D.base_mem a.hom)
    {m : (vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
        (pullbackGlobalSection D p hp p'' hp'' c L s)).1.toFunctor ⟶
      (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
        (pullbackGlobalSection D p hp p' hp' b L s)).1.toFunctor}
    (hm : m ≫ (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
        (pullbackGlobalSection D p hp p' hp' b L s)).1.ι =
      (vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
        (pullbackGlobalSection D p hp p'' hp'' c L s)).1.ι ≫ a.hom)
    (k : ℤ) (β : CycleGroup D p'' (k + 1)) :
    chowClassCanonical.{max (u + 1) v} D
        ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
          (pullbackGlobalSection D p hp p' hp' b L s)).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) k
        (gysinCycleMap D p' (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
            (pullbackGlobalSection D p hp p' hp' b L s))
          (isGood_vanishingLocus D p' hp' _ _) k
          (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' b L)
            (pullbackGlobalSection D p hp p' hp' b L s) k
            (isInvertibleSheaf_pullbackSheaf D p hp p' hp' b L hL))
          (properCyclePushforward D p'' hp'' p' hp' hab ha.2.1.2 (k + 1) β)) =
      chowClassCanonical.{max (u + 1) v} D
        ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
          (pullbackGlobalSection D p hp p' hp' b L s)).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) k
        (properCyclePushforward D
          ((vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
            (pullbackGlobalSection D p hp p'' hp'' c L s)).1.ι ≫ p'')
          (isGood_vanishingLocus D p'' hp'' _ _)
          ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
            (pullbackGlobalSection D p hp p' hp' b L s)).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _) (comp_structure_of_comp_ι_eq_comp_ι D hab hm)
          (isQuasiCompact_of_comp_ι_eq_comp_ι D hp' hp'' ha.2.1.2 hm) k
          (gysinCycleMap D p'' (vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
              (pullbackGlobalSection D p hp p'' hp'' c L s))
            (isGood_vanishingLocus D p'' hp'' _ _) k
            (sectionGysinRule D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
              (pullbackGlobalSection D p hp p'' hp'' c L s) k
              (isInvertibleSheaf_pullbackSheaf D p hp p'' hp'' c L hL)) β)) := by
  subst habc
  have hbL := isInvertibleSheaf_pullbackSheaf D p hp p' hp' b L hL
  have hgE := pullbackVanishingLocusProjection_comm D p' hp' p'' hp'' a
    (pullbackSheaf D p hp p' hp' b L) (pullbackGlobalSection D p hp p' hp' b L s) hbL
  have hgEP := isProper_pullbackVanishingLocusProjection D p' hp' p'' hp'' a
    (pullbackSheaf D p hp p' hp' b L) (pullbackGlobalSection D p hp p' hp' b L s) hbL ha
  have R2 :=
    isCanonicallyRationallyEquivalentToZeroWithin_closedPushforward_sectionGysinRule_comp_sub.{v}
      D p hp p' hp' p'' hp'' a b L s k hL β
  rw [chowClassCanonical_eq_uliftIndex D
      (chowClassCanonical_sectionGysin_properPushforward_eq D p' hp' p'' hp'' a hab ha
        (pullbackSheaf D p hp p' hp' b L) (pullbackGlobalSection D p hp p' hp' b L s) hbL k β),
    ← chowGroupCanonicalProperPushforward_chowClassCanonical.{max (u + 1) v} D _
      (isGood_vanishingLocus D p'' hp'' _ _) _ (isGood_vanishingLocus D p' hp' _ _)
      (comp_structure_of_comp_ι_eq_comp_ι D hab hgE) hgEP k,
    ← chowClassCanonical_eq_of_isCanonicallyRationallyEquivalentToZeroWithin_sub D R2,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_cycleGroupClosedPushforward_homOfLe D hp' hp'' hab ha _ hgE hm]

/-- **The Gysin axiom of Stacks 0ERJ transported along a proper morphism.** In the situation of
`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_properCyclePushforward_of_comp_eq`, let
`Q ≅ E''` and `e' : Q' ⟶ E'` be identifications of the two vanishing loci with spaces `Q`, `Q'`,
and `φ : Q ⟶ Q'` a proper morphism lying over `a`.  If `e_* γ = (i'')^* β` in `CH_k(E'')` for a
`k`-cycle `γ` on `Q`, then `e'_* φ_* γ = i'^* a_* β` in `CH_k(E')`. -/
theorem chowClassCanonical_properCyclePushforward_eq_gysinCycleMap_properCyclePushforward
    (habc : a ≫ b = c) (hab : a.hom ≫ p' = p'') (ha : IsProper D.site D.base D.base_mem a.hom)
    {Q Q' : D.Ambient} {q : Q ⟶ D.space} (hq : D.IsGood q) {q' : Q' ⟶ D.space} (hq' : D.IsGood q')
    {φ : Q ⟶ Q'} (hφB : φ ≫ q' = q) (hφ : IsProper D.site D.base D.base_mem φ)
    (eX : Q ≅ (vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
        (pullbackGlobalSection D p hp p'' hp'' c L s)).1.toFunctor)
    (heXB : eX.hom ≫ ((vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
        (pullbackGlobalSection D p hp p'' hp'' c L s)).1.ι ≫ p'') = q)
    {eY : Q' ⟶ (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
        (pullbackGlobalSection D p hp p' hp' b L s)).1.toFunctor}
    (heYB : eY ≫ ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
        (pullbackGlobalSection D p hp p' hp' b L s)).1.ι ≫ p') = q')
    (heY : IsProper D.site D.base D.base_mem eY)
    (hsq : eX.hom ≫ (vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
        (pullbackGlobalSection D p hp p'' hp'' c L s)).1.ι ≫ a.hom =
      φ ≫ eY ≫ (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
        (pullbackGlobalSection D p hp p' hp' b L s)).1.ι)
    (k : ℤ) (β : CycleGroup D p'' (k + 1)) (γ : CycleGroup D q k)
    (e : chowClassCanonical.{max (u + 1) v} D
        ((vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
          (pullbackGlobalSection D p hp p'' hp'' c L s)).1.ι ≫ p'')
        (isGood_vanishingLocus D p'' hp'' _ _) k
        (properCyclePushforward D q hq _ (isGood_vanishingLocus D p'' hp'' _ _) heXB
          (isProper_of_isIso D.site D.base D.base_mem eX.hom).2.1.2 k γ) =
      chowClassCanonical.{max (u + 1) v} D
        ((vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
          (pullbackGlobalSection D p hp p'' hp'' c L s)).1.ι ≫ p'')
        (isGood_vanishingLocus D p'' hp'' _ _) k
        (gysinCycleMap D p'' (vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
            (pullbackGlobalSection D p hp p'' hp'' c L s))
          (isGood_vanishingLocus D p'' hp'' _ _) k
          (sectionGysinRule D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
            (pullbackGlobalSection D p hp p'' hp'' c L s) k
            (isInvertibleSheaf_pullbackSheaf D p hp p'' hp'' c L hL)) β)) :
    chowClassCanonical.{max (u + 1) v} D
        ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
          (pullbackGlobalSection D p hp p' hp' b L s)).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) k
        (properCyclePushforward D q' hq' _ (isGood_vanishingLocus D p' hp' _ _) heYB heY.2.1.2 k
          (properCyclePushforward D q hq q' hq' hφB hφ.2.1.2 k γ)) =
      chowClassCanonical.{max (u + 1) v} D
        ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
          (pullbackGlobalSection D p hp p' hp' b L s)).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) k
        (gysinCycleMap D p' (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
            (pullbackGlobalSection D p hp p' hp' b L s))
          (isGood_vanishingLocus D p' hp' _ _) k
          (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' b L)
            (pullbackGlobalSection D p hp p' hp' b L s) k
            (isInvertibleSheaf_pullbackSheaf D p hp p' hp' b L hL))
          (properCyclePushforward D p'' hp'' p' hp' hab ha.2.1.2 (k + 1) β)) := by
  have hE := isGood_vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
    (pullbackGlobalSection D p hp p'' hp'' c L s)
  have hE' := isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
    (pullbackGlobalSection D p hp p' hp' b L s)
  have hm : (eX.inv ≫ φ ≫ eY) ≫ (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' b L)
        (pullbackGlobalSection D p hp p' hp' b L s)).1.ι =
      (vanishingLocus D p'' hp'' (pullbackSheaf D p hp p'' hp'' c L)
        (pullbackGlobalSection D p hp p'' hp'' c L s)).1.ι ≫ a.hom := by
    rw [Category.assoc, Category.assoc, ← hsq, Iso.inv_hom_id_assoc]
  have hmP : IsProper D.site D.base D.base_mem (eX.inv ≫ φ ≫ eY) :=
    isProper_comp D.site D.base D.base_mem hE.1 hq.1 hE'.1 _ _
      (isProper_of_isIso D.site D.base D.base_mem _)
      (isProper_comp D.site D.base D.base_mem hq.1 hq'.1 hE'.1 _ _ hφ heY)
  rw [chowClassCanonical_gysinCycleMap_properCyclePushforward_of_comp_eq D p hp p' hp' p'' hp'' a b
      c
      L hL s habc hab ha hm k β,
    ← chowGroupCanonicalProperPushforward_chowClassCanonical.{max (u + 1) v} D _ hE _ hE'
      (comp_structure_of_comp_ι_eq_comp_ι D hab hm) hmP k, ← e,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_comp D _ _ _ hq hE hE' heXB (comp_structure_of_comp_ι_eq_comp_ι D hab hm)
      (isProper_of_isIso D.site D.base D.base_mem eX.hom) hmP,
    properCyclePushforward_comp D _ _ _ hq hq' hE' hφB heYB hφ heY]
  exact congrArg _ (properCyclePushforward_congr D _ _ _ _ (by simp) _ _ _ _ _ _)

end CompositeGysin

/-! ### The base change of the proper morphism along a morphism of test spaces -/

section BaseChange

variable {X Y Z Z' Z'' : D.Ambient} (f : X ⟶ Y) (g : Y ⟶ Z) (z : Z' ⟶ Z) (h : Z'' ⟶ Z')

/-- The square formed by the base changes of `f` along `Z'' ⟶ Z' ⟶ Z` and the two base-change
maps of test spaces commutes. -/
theorem bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange
    {h' : pullback g (h ≫ z) ⟶ pullback g z}
    (hfst : h' ≫ pullback.fst g z = pullback.fst g (h ≫ z))
    (hsnd : h' ≫ pullback.snd g z = pullback.snd g (h ≫ z) ≫ h) :
    bivariantBaseChangeMap D (f ≫ g) z h ≫ bivariantPushforwardBaseChange D f g z =
      bivariantPushforwardBaseChange D f g (h ≫ z) ≫ h' := by
  apply pullback.hom_ext
  · simp [bivariantBaseChangeMap, hfst]
  · simp [bivariantBaseChangeMap, hsnd]

/-- The square formed by the base changes of `f` along `Z'' ⟶ Z' ⟶ Z` and the two base-change
maps of test spaces is cartesian. -/
theorem isPullback_bivariantBaseChangeMap_bivariantPushforwardBaseChange
    {h' : pullback g (h ≫ z) ⟶ pullback g z}
    (sq : IsPullback (pullback.snd g (h ≫ z)) h' h (pullback.snd g z))
    (hfst : h' ≫ pullback.fst g z = pullback.fst g (h ≫ z)) :
    IsPullback (bivariantBaseChangeMap D (f ≫ g) z h) (bivariantPushforwardBaseChange D f g (h ≫ z))
      (bivariantPushforwardBaseChange D f g z) h' := by
  have s : IsPullback (bivariantBaseChangeMap D (f ≫ g) z h)
      (bivariantPushforwardBaseChange D f g (h ≫ z) ≫ pullback.snd g (h ≫ z))
      (bivariantPushforwardBaseChange D f g z ≫ pullback.snd g z) h := by
    rw [bivariantPushforwardBaseChange_snd, bivariantPushforwardBaseChange_snd]
    exact (isPullback_bivariantBaseChangeMap D (f ≫ g) z h).flip
  exact IsPullback.of_bot s
    (bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange D f g z h hfst sq.w.symm) sq.flip

end BaseChange

/-- Proper pushforward of cycles commutes with the transport of cycles along an equality of
degrees. -/
theorem properCyclePushforward_cycleGroupDegreeCongr {X Y : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) {k l : ℤ} (h : k = l)
    (α : CycleGroup D sX k) :
    properCyclePushforward D sX hX sY hY hfB hf l (cycleGroupDegreeCongr D sX h α) =
      cycleGroupDegreeCongr D sY h (properCyclePushforward D sX hX sY hY hfB hf k α) := by
  subst h
  rfl

/-! ### The pushforward of a bivariant class -/

section ProperPushforward

variable {X Y Z : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space}
  (hY : D.IsGood sY) {sZ : Z ⟶ D.space} {hZ : D.IsGood sZ} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (hfP : IsProper D.site D.base D.base_mem f) {p : ℤ}
  (c : BivariantClassCanonical.{max (u + 1) v} D sX hX sZ hZ (f ≫ g)
    (((Category.assoc f g sZ).trans (congrArg (f ≫ ·) hg)).trans hf) p)

/-- The rule of Stacks 0ERQ: for a test space `z : Z' ⟶ Z`, the map
`CH_k(Z') ⟶ CH_{k-p}(Z' ×_Z Y)`, `α ↦ f'_*(c ∩ α)`, where `f' : Z' ×_Z X ⟶ Z' ×_Z Y` is the base
change of `f`. -/
def BivariantClassCanonical.properPushforwardCap {Z' : D.Ambient} (z : Z' ⟶ Z)
    (hZ' : D.IsGood (z ≫ sZ)) (hY' : D.IsGood (pullback.fst g z ≫ sY)) (k : ℤ) :
    chowGroupCanonical.{max (u + 1) v} D (z ≫ sZ) hZ' k →+
      chowGroupCanonical.{max (u + 1) v} D (pullback.fst g z ≫ sY) hY' (k - p) :=
  (chowGroupCanonicalProperPushforward.{max (u + 1) v} D (pullback.fst (f ≫ g) z ≫ sX)
    (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') (pullback.fst g z ≫ sY) hY'
    (bivariantPushforwardBaseChange_comp_structure D hf g z)
    (isProper_bivariantPushforwardBaseChange D f g z hX.1 hY.1
      (isGood_pullback_fst D hX hZ (f ≫ g) z hZ').1 hY'.1 hfP) (k - p)).comp
    (c.cap z hZ' (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') k)

/-- The cap operation `AlgebraicGeometry.Space.BivariantClassCanonical.properPushforwardCap` is
`α ↦ f'_*(c ∩ α)`. -/
theorem BivariantClassCanonical.properPushforwardCap_apply {Z' : D.Ambient} (z : Z' ⟶ Z)
    (hZ' : D.IsGood (z ≫ sZ)) (hY' : D.IsGood (pullback.fst g z ≫ sY)) (k : ℤ)
    (α : chowGroupCanonical.{max (u + 1) v} D (z ≫ sZ) hZ' k) :
    BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c z hZ' hY' k α =
      chowGroupCanonicalProperPushforward.{max (u + 1) v} D (pullback.fst (f ≫ g) z ≫ sX)
        (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') (pullback.fst g z ≫ sY) hY'
        (bivariantPushforwardBaseChange_comp_structure D hf g z)
        (isProper_bivariantPushforwardBaseChange D f g z hX.1 hY.1
          (isGood_pullback_fst D hX hZ (f ≫ g) z hZ').1 hY'.1 hfP) (k - p)
        (c.cap z hZ' (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') k α) :=
  rfl

/-- If `c ∩ x` is the class of a cycle `β`, then the rule of Stacks 0ERQ sends `x` to the class
of the proper pushforward of `β`. -/
private theorem properPushforwardCap_eq_of_cap_eq {Z' : D.Ambient} {z : Z' ⟶ Z}
    {hZ' : D.IsGood (z ≫ sZ)} {hY' : D.IsGood (pullback.fst g z ≫ sY)} {k : ℤ}
    {x : chowGroupCanonical.{max (u + 1) v} D (z ≫ sZ) hZ' k}
    {β : CycleGroup D (pullback.fst (f ≫ g) z ≫ sX) (k - p)}
    (e : c.cap z hZ' (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') k x =
      chowClassCanonical.{max (u + 1) v} D (pullback.fst (f ≫ g) z ≫ sX)
        (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') (k - p) β) :
    BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c z hZ' hY' k x =
      chowClassCanonical.{max (u + 1) v} D (pullback.fst g z ≫ sY) hY' (k - p)
        (properCyclePushforward D (pullback.fst (f ≫ g) z ≫ sX)
          (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') (pullback.fst g z ≫ sY) hY'
          (bivariantPushforwardBaseChange_comp_structure D hf g z)
          (isProper_bivariantPushforwardBaseChange D f g z hX.1 hY.1
            (isGood_pullback_fst D hX hZ (f ≫ g) z hZ').1 hY'.1 hfP).2.1.2 (k - p) β) := by
  rw [BivariantClassCanonical.properPushforwardCap_apply, e,
    chowGroupCanonicalProperPushforward_chowClassCanonical]

/-- The rule of Stacks 0ERQ commutes with proper pushforward: axiom (1) of Stacks 0ERJ, from
that axiom for `c` and Stacks 0EP2. -/
theorem BivariantClassCanonical.properPushforwardCap_proper_naturality {Z' Z'' : D.Ambient}
    (z : Z' ⟶ Z) (hZ' : D.IsGood (z ≫ sZ)) (hY' : D.IsGood (pullback.fst g z ≫ sY))
    (h : Z'' ⟶ Z') (hZ'' : D.IsGood ((h ≫ z) ≫ sZ))
    (hY'' : D.IsGood (pullback.fst g (h ≫ z) ≫ sY)) (hh : IsProper D.site D.base D.base_mem h)
    (h' : pullback g (h ≫ z) ⟶ pullback g z)
    (sq : IsPullback (pullback.snd g (h ≫ z)) h' h (pullback.snd g z))
    (hfst : h' ≫ pullback.fst g z = pullback.fst g (h ≫ z))
    (hh' : IsProper D.site D.base D.base_mem h') (k : ℤ) (α : CycleGroup D ((h ≫ z) ≫ sZ) k) :
    ∃ β : CycleGroup D (pullback.fst g (h ≫ z) ≫ sY) (k - p),
      BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c (h ≫ z) hZ'' hY'' k
          (chowClassCanonical.{max (u + 1) v} D ((h ≫ z) ≫ sZ) hZ'' k α) =
          chowClassCanonical.{max (u + 1) v} D (pullback.fst g (h ≫ z) ≫ sY) hY'' (k - p) β ∧
        BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c z hZ' hY' k
            (chowClassCanonical.{max (u + 1) v} D (z ≫ sZ) hZ' k
              (properCyclePushforward D ((h ≫ z) ≫ sZ) hZ'' (z ≫ sZ) hZ'
                (Category.assoc h z sZ).symm hh.2.1.2 k α)) =
          chowClassCanonical.{max (u + 1) v} D (pullback.fst g z ≫ sY) hY' (k - p)
            (properCyclePushforward D (pullback.fst g (h ≫ z) ≫ sY) hY''
              (pullback.fst g z ≫ sY) hY' (by rw [← Category.assoc, hfst]) hh'.2.1.2 (k - p)
              β) := by
  have hXz := isGood_pullback_fst D hX hZ (f ≫ g) z hZ'
  have hXz'' := isGood_pullback_fst D hX hZ (f ≫ g) (h ≫ z) hZ''
  have hbcP := isProper_bivariantBaseChangeMap D (f ≫ g) z h hZ'.1 hZ''.1 hXz.1 hXz''.1 hh
  have hfz := isProper_bivariantPushforwardBaseChange D f g z hX.1 hY.1 hXz.1 hY'.1 hfP
  have hfhz := isProper_bivariantPushforwardBaseChange D f g (h ≫ z) hX.1 hY.1 hXz''.1 hY''.1 hfP
  obtain ⟨β, e1, e2⟩ := c.proper_naturality z hZ' hXz h hZ'' hXz'' hh
    (bivariantBaseChangeMap D (f ≫ g) z h) (isPullback_bivariantBaseChangeMap D (f ≫ g) z h)
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) hbcP k α
  refine ⟨properCyclePushforward D (pullback.fst (f ≫ g) (h ≫ z) ≫ sX) hXz''
    (pullback.fst g (h ≫ z) ≫ sY) hY''
    (bivariantPushforwardBaseChange_comp_structure D hf g (h ≫ z))
    hfhz.2.1.2 (k - p) β, ?_, ?_⟩
  · exact properPushforwardCap_eq_of_cap_eq D hY hf hg hfP c e1
  · rw [properPushforwardCap_eq_of_cap_eq D hY hf hg hfP c e2]
    congr 1
    rw [properCyclePushforward_comp D _ _ _ hXz'' hXz hY' _
        (bivariantPushforwardBaseChange_comp_structure D hf g z) hbcP hfz,
      properCyclePushforward_comp D _ _ _ hXz'' hY'' hY'
        (bivariantPushforwardBaseChange_comp_structure D hf g (h ≫ z)) _ hfhz hh']
    exact properCyclePushforward_congr D _ _ _ _
      (bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange D f g z h hfst sq.w.symm) _ _ _ _
      _ _

/-- The rule of Stacks 0ERQ commutes with flat pullback of fixed relative dimension: axiom (2) of
Stacks 0ERJ, from that axiom for `c` and the third assertion of Stacks 0EPD. -/
theorem BivariantClassCanonical.properPushforwardCap_flat_naturality {Z' Z'' : D.Ambient}
    (z : Z' ⟶ Z) (hZ' : D.IsGood (z ≫ sZ)) (hY' : D.IsGood (pullback.fst g z ≫ sY))
    (h : Z'' ⟶ Z') (hZ'' : D.IsGood ((h ≫ z) ≫ sZ))
    (hY'' : D.IsGood (pullback.fst g (h ≫ z) ≫ sY)) (hh : IsFlat D.site D.base D.base_mem h)
    (r : ℕ) (hr : HasRelativeDimension r D.site D.base D.base_mem h)
    (h' : pullback g (h ≫ z) ⟶ pullback g z)
    (sq : IsPullback (pullback.snd g (h ≫ z)) h' h (pullback.snd g z))
    (hfst : h' ≫ pullback.fst g z = pullback.fst g (h ≫ z))
    (hh' : IsFlat D.site D.base D.base_mem h')
    (hr' : HasRelativeDimension r D.site D.base D.base_mem h') (k : ℤ)
    (α : CycleGroup D (z ≫ sZ) k) :
    ∃ β : CycleGroup D (pullback.fst g z ≫ sY) (k - p),
      BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c z hZ' hY' k
          (chowClassCanonical.{max (u + 1) v} D (z ≫ sZ) hZ' k α) =
          chowClassCanonical.{max (u + 1) v} D (pullback.fst g z ≫ sY) hY' (k - p) β ∧
        BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c (h ≫ z) hZ'' hY''
            (k + (r : ℤ))
            (chowClassCanonical.{max (u + 1) v} D ((h ≫ z) ≫ sZ) hZ'' (k + (r : ℤ))
              (flatPullbackMap D ((h ≫ z) ≫ sZ) hZ'' (z ≫ sZ) hZ' h
                (Category.assoc h z sZ).symm r hh hr k (k + (r : ℤ)) rfl α)) =
          chowClassCanonical.{max (u + 1) v} D (pullback.fst g (h ≫ z) ≫ sY) hY''
            (k + (r : ℤ) - p)
            (flatPullbackMap D (pullback.fst g (h ≫ z) ≫ sY) hY'' (pullback.fst g z ≫ sY) hY'
              h' (by rw [← Category.assoc, hfst]) r hh' hr' (k - p) (k + (r : ℤ) - p)
              (by omega) β) := by
  have hXz := isGood_pullback_fst D hX hZ (f ≫ g) z hZ'
  have hXz'' := isGood_pullback_fst D hX hZ (f ≫ g) (h ≫ z) hZ''
  have hfz := isProper_bivariantPushforwardBaseChange D f g z hX.1 hY.1 hXz.1 hY'.1 hfP
  have hfstX : bivariantBaseChangeMap D (f ≫ g) z h ≫ pullback.fst (f ≫ g) z =
      pullback.fst (f ≫ g) (h ≫ z) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hflX := isFlat_and_hasRelativeDimension_of_isPullback D _ hXz'' _ hXz _ hZ'' _ hZ'
    (by rw [← Category.assoc, hfstX]) (Category.assoc h z sZ).symm
    (isPullback_bivariantBaseChangeMap D (f ≫ g) z h).flip r hh hr
  obtain ⟨β, e1, e2⟩ := c.flat_naturality z hZ' hXz h hZ'' hXz'' hh r hr
    (bivariantBaseChangeMap D (f ≫ g) z h) (isPullback_bivariantBaseChangeMap D (f ≫ g) z h)
    hfstX hflX.2.1 hflX.2.2 k α
  refine ⟨properCyclePushforward D (pullback.fst (f ≫ g) z ≫ sX) hXz (pullback.fst g z ≫ sY) hY'
    (bivariantPushforwardBaseChange_comp_structure D hf g z) hfz.2.1.2 (k - p) β, ?_, ?_⟩
  · exact properPushforwardCap_eq_of_cap_eq D hY hf hg hfP c e1
  · rw [properPushforwardCap_eq_of_cap_eq D hY hf hg hfP c e2]
    congr 1
    exact (flatPullback_properPushforward_unconditional D _ hXz'' _ hXz _ hY'' _ hY'
      (by rw [← Category.assoc, hfstX])
      (bivariantPushforwardBaseChange_comp_structure D hf g (h ≫ z))
      (bivariantPushforwardBaseChange_comp_structure D hf g z) (by rw [← Category.assoc, hfst])
      r hh' hr' (isPullback_bivariantBaseChangeMap_bivariantPushforwardBaseChange D f g z h sq hfst)
      hfz (k - p) (k + (r : ℤ) - p) (by omega) β).symm

/-- The rule of Stacks 0ERQ commutes with the refined Gysin maps: axiom (3) of Stacks 0ERJ, from
that axiom for `c`, the identification of the pulled-back vanishing loci (Stacks 0ER3) and
Stacks 0ER5. -/
theorem BivariantClassCanonical.properPushforwardCap_gysin_naturality {Z' : D.Ambient}
    (z : Z' ⟶ Z) (hZ' : D.IsGood (z ≫ sZ)) (hY' : D.IsGood (pullback.fst g z ≫ sY))
    (L : Modules.{u, u} D.site D.base D.base_mem Z' hZ'.1) (t : L.sections)
    (hL : IsInvertibleSheaf D (z ≫ sZ) hZ' L)
    (hYd : D.IsGood (pullback.fst g ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) ≫ sY))
    (isoY : pullback g ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) ≅
      (bivariantPullbackVanishingLocus D sY sZ g z hZ' hY' L t).1.toFunctor)
    (hisoY : isoY.hom ≫ (bivariantPullbackVanishingLocus D sY sZ g z hZ' hY' L t).1.ι =
      bivariantBaseChangeMap D g z (vanishingLocus D (z ≫ sZ) hZ' L t).1.ι)
    (hbaseY : isoY.hom ≫ ((bivariantPullbackVanishingLocus D sY sZ g z hZ' hY' L t).1.ι ≫
        pullback.fst g z ≫ sY) =
      pullback.fst g ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) ≫ sY)
    (hisoYP : IsProper D.site D.base D.base_mem isoY.hom) (k : ℤ)
    (α : CycleGroup D (z ≫ sZ) (k + 1)) :
    ∃ (β : CycleGroup D (pullback.fst g z ≫ sY) (k - p + 1))
      (γ : CycleGroup D (pullback.fst g ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) ≫ sY)
        (k - p)),
      BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c z hZ' hY' (k + 1)
            (chowClassCanonical.{max (u + 1) v} D (z ≫ sZ) hZ' (k + 1) α) =
          chowClassCanonical.{max (u + 1) v} D (pullback.fst g z ≫ sY) hY' (k + 1 - p)
            (cycleGroupDegreeCongr D (pullback.fst g z ≫ sY) (by omega) β) ∧
        BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c
              ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z)
              (isGood_vanishingLocus D (z ≫ sZ) hZ' L t) hYd k
              (chowClassCanonical.{max (u + 1) v} D
                ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z ≫ sZ)
                (isGood_vanishingLocus D (z ≫ sZ) hZ' L t) k
                (gysinCycleMap D (z ≫ sZ) (vanishingLocus D (z ≫ sZ) hZ' L t)
                  (isGood_vanishingLocus D (z ≫ sZ) hZ' L t) k
                  (sectionGysinRule D (z ≫ sZ) hZ' L t k hL) α)) =
            chowClassCanonical.{max (u + 1) v} D
              (pullback.fst g ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) ≫ sY) hYd (k - p)
              γ ∧
          chowClassCanonical.{max (u + 1) v} D
              ((bivariantPullbackVanishingLocus D sY sZ g z hZ' hY' L t).1.ι ≫
                pullback.fst g z ≫ sY)
              (isGood_vanishingLocus D (pullback.fst g z ≫ sY) hY'
                (bivariantPullbackSheaf D sY sZ g z hZ' hY' L)
                (bivariantPullbackSection D sY sZ g z hZ' hY' L t)) (k - p)
              (properCyclePushforward D
                (pullback.fst g ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) ≫ sY) hYd
                ((bivariantPullbackVanishingLocus D sY sZ g z hZ' hY' L t).1.ι ≫
                  pullback.fst g z ≫ sY)
                (isGood_vanishingLocus D (pullback.fst g z ≫ sY) hY'
                  (bivariantPullbackSheaf D sY sZ g z hZ' hY' L)
                  (bivariantPullbackSection D sY sZ g z hZ' hY' L t)) hbaseY
                hisoYP.2.1.2 (k - p) γ) =
            chowClassCanonical.{max (u + 1) v} D
              ((bivariantPullbackVanishingLocus D sY sZ g z hZ' hY' L t).1.ι ≫
                pullback.fst g z ≫ sY)
              (isGood_vanishingLocus D (pullback.fst g z ≫ sY) hY'
                (bivariantPullbackSheaf D sY sZ g z hZ' hY' L)
                (bivariantPullbackSection D sY sZ g z hZ' hY' L t)) (k - p)
              (gysinCycleMap D (pullback.fst g z ≫ sY)
                (bivariantPullbackVanishingLocus D sY sZ g z hZ' hY' L t)
                (isGood_vanishingLocus D (pullback.fst g z ≫ sY) hY'
                  (bivariantPullbackSheaf D sY sZ g z hZ' hY' L)
                  (bivariantPullbackSection D sY sZ g z hZ' hY' L t)) (k - p)
                (sectionGysinRule D (pullback.fst g z ≫ sY) hY'
                  (bivariantPullbackSheaf D sY sZ g z hZ' hY' L)
                  (bivariantPullbackSection D sY sZ g z hZ' hY' L t) (k - p)
                  (isInvertibleSheaf_bivariantPullbackSheaf D sY sZ g z hZ' hY' L hL)) β) := by
  have hXz := isGood_pullback_fst D hX hZ (f ≫ g) z hZ'
  have hXd := isGood_pullback_fst D hX hZ (f ≫ g)
    ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) (isGood_vanishingLocus D (z ≫ sZ) hZ' L t)
  have hfz := isProper_bivariantPushforwardBaseChange D f g z hX.1 hY.1 hXz.1 hY'.1 hfP
  have hfd := isProper_bivariantPushforwardBaseChange D f g
    ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) hX.1 hY.1 hXd.1 hYd.1 hfP
  have hisoX := bivariantPullbackVanishingLocusIso_hom_ι D sX sZ (f ≫ g) z hZ' hXz L t hL
  have hbaseX : (bivariantPullbackVanishingLocusIso D sX sZ (f ≫ g) z hZ' hXz L t hL).hom ≫
      ((bivariantPullbackVanishingLocus D sX sZ (f ≫ g) z hZ' hXz L t).1.ι ≫
        pullback.fst (f ≫ g) z ≫ sX) =
      pullback.fst (f ≫ g) ((vanishingLocus D (z ≫ sZ) hZ' L t).1.ι ≫ z) ≫ sX := by
    rw [reassoc_of% hisoX]
    simp [bivariantBaseChangeMap]
  obtain ⟨β, γ, e1, e2, e3⟩ := c.gysin_naturality z hZ' hXz L t hL hXd
    (bivariantPullbackVanishingLocusIso D sX sZ (f ≫ g) z hZ' hXz L t hL) hisoX hbaseX
    (isProper_of_isIso D.site D.base D.base_mem _) k α
  refine ⟨properCyclePushforward D (pullback.fst (f ≫ g) z ≫ sX) hXz (pullback.fst g z ≫ sY) hY'
    (bivariantPushforwardBaseChange_comp_structure D hf g z) hfz.2.1.2 (k - p + 1) β,
    properCyclePushforward D _ hXd _ hYd
      (bivariantPushforwardBaseChange_comp_structure D hf g _) hfd.2.1.2 (k - p) γ, ?_, ?_, ?_⟩
  · refine (properPushforwardCap_eq_of_cap_eq D hY hf hg hfP c e1).trans (congrArg _ ?_)
    exact properCyclePushforward_cycleGroupDegreeCongr D _ hXz _ hY'
      (bivariantPushforwardBaseChange_comp_structure D hf g z) hfz.2.1.2 (by omega) β
  · exact properPushforwardCap_eq_of_cap_eq D hY hf hg hfP c e2
  · exact chowClassCanonical_properCyclePushforward_eq_gysinCycleMap_properCyclePushforward D
      (X := Z') (X' := pullback g z) (X'' := pullback (f ≫ g) z)
      (z ≫ sZ) hZ' (pullback.fst g z ≫ sY) hY' (pullback.fst (f ≫ g) z ≫ sX) hXz
      (ObjectProperty.homMk (bivariantPushforwardBaseChange D f g z) :
        (⟨pullback (f ≫ g) z, hXz.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨pullback g z, hY'.1⟩)
      (bivariantTestProjection D sY sZ g z hZ' hY')
      (bivariantTestProjection D sX sZ (f ≫ g) z hZ' hXz) L hL t
      (ObjectProperty.hom_ext _ (bivariantPushforwardBaseChange_snd D f g z))
      (bivariantPushforwardBaseChange_comp_structure D hf g z) hfz hXd hYd
      (bivariantPushforwardBaseChange_comp_structure D hf g _) hfd
      (bivariantPullbackVanishingLocusIso D sX sZ (f ≫ g) z hZ' hXz L t hL) hbaseX hbaseY hisoYP
      (by
        rw [reassoc_of% hisoX, hisoY]
        exact bivariantBaseChangeMap_comp_bivariantPushforwardBaseChange D f g z _
          ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) (pullback.lift_snd _ _ _))
      (k - p) β γ e3


/-- **Stacks 0ERQ.** In Situation 0EDT let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of good
algebraic spaces over the base, with `f` proper, and let `c ∈ A^p(X ⟶ Z)`.  The rule which to a
test space `Z' ⟶ Z` assigns `α ↦ f'_*(c ∩ α)`, for `f' : Z' ×_Z X ⟶ Z' ×_Z Y` the base change of
`f`, is a bivariant class of degree `p` for `g`; this is that class `f_* ∘ c ∈ A^p(Y ⟶ Z)`, and
`AlgebraicGeometry.Space.BivariantClassCanonical.properPushforward_cap_apply` says that it caps by
the rule. -/
@[stacks 0ERQ "the rule α ↦ f'_*(c ∩ α) is a bivariant class of degree p for g: the class \
f_* ∘ c ∈ A^p(Y → Z) over the constructed Chow groups and operations, with its three axioms \
proved from those of c, Stacks 0EP2, 0EPD and 0ER5"]
def BivariantClassCanonical.properPushforward :
    BivariantClassCanonical.{max (u + 1) v} D sY hY sZ hZ g hg p where
  cap := BivariantClassCanonical.properPushforwardCap D hY hf hg hfP c
  proper_naturality :=
    BivariantClassCanonical.properPushforwardCap_proper_naturality D hY hf hg hfP c
  flat_naturality := BivariantClassCanonical.properPushforwardCap_flat_naturality D hY hf hg hfP c
  gysin_naturality :=
    BivariantClassCanonical.properPushforwardCap_gysin_naturality D hY hf hg hfP c

/-- **Stacks 0ERQ.** The class `f_* ∘ c` caps by the rule of the source: on a test space
`z : Z' ⟶ Z`, `(f_* ∘ c) ∩ α = f'_*(c ∩ α)` in `CH_{k-p}(Z' ×_Z Y)`. -/
@[stacks 0ERQ "the class caps by the rule α ↦ f'_*(c ∩ α)"]
theorem BivariantClassCanonical.properPushforward_cap_apply {Z' : D.Ambient} (z : Z' ⟶ Z)
    (hZ' : D.IsGood (z ≫ sZ)) (hY' : D.IsGood (pullback.fst g z ≫ sY)) (k : ℤ)
    (α : chowGroupCanonical.{max (u + 1) v} D (z ≫ sZ) hZ' k) :
    (BivariantClassCanonical.properPushforward D hY hf hg hfP c).cap z hZ' hY' k α =
      chowGroupCanonicalProperPushforward.{max (u + 1) v} D (pullback.fst (f ≫ g) z ≫ sX)
        (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') (pullback.fst g z ≫ sY) hY'
        (bivariantPushforwardBaseChange_comp_structure D hf g z)
        (isProper_bivariantPushforwardBaseChange D f g z hX.1 hY.1
          (isGood_pullback_fst D hX hZ (f ≫ g) z hZ').1 hY'.1 hfP) (k - p)
        (c.cap z hZ' (isGood_pullback_fst D hX hZ (f ≫ g) z hZ') k α) :=
  rfl

end ProperPushforward

end AlgebraicGeometry.Space

end

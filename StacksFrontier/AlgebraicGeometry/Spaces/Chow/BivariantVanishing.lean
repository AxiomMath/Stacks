module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Vanishing of a bivariant class on the fundamental classes of integral spaces

In the situation of Stacks 0EDT let `X/B` be good and let `c ∈ A^p(X)`. **Stacks 0ERS** says
that `c` is zero if and only if `c ∩ [Y] = 0` in `CH_*(Y)` for every integral algebraic space
`Y` locally of finite type over `X`.

The forward implication is the vanishing of the zero bivariant class. For the converse, a class
`α ∈ CH_k(X')` on a good test space is written as the class of a cycle `∑ n_i [Z_i]` over the
integral closed subspaces `Z_i ⊆ X'` of δ-dimension `k`, and each `c ∩ [Z_i]` is computed by
pushing forward along the closed immersion `Z_i ⟶ X'`, where the hypothesis applies to the
integral space `Z_i`.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.whole` — an integral closed subspace, read as
  an integral closed subspace of itself.
* `AlgebraicGeometry.Space.integralClosedSubspaceCycle` — the cycle `[Z]` of an integral closed
  subspace, in the group of `k`-cycles.
* `AlgebraicGeometry.Space.ChowGroupSystem.IsInducedByClosedCyclePushforward` — compatibility of
  the parameterized proper pushforward with the pushforward of cycles along a closed immersion.
* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.HasGoodSubspaceBaseChanges` — goodness and
  properness of the fibre products of the integral closed subspaces of a test space.
* `AlgebraicGeometry.Space.BivariantClass.CapsFundamentalClassesToZero` — the condition
  `c ∩ [Y] = 0` for every integral algebraic space `Y` locally of finite type over `X`.

## Main results

* `AlgebraicGeometry.Space.eq_sum_integralClosedSubspaceCycle` — a cycle with finite support is
  the sum of its coefficients times the cycles of the subspaces in its support.
* `AlgebraicGeometry.Space.zero_capsFundamentalClassesToZero` — **Stacks 0ERS**, the forward
  implication.
* `AlgebraicGeometry.Space.cap_integralClosedSubspaceCycle_eq_zero` — **Stacks 0ERS**, the
  content of the converse: capping with `c` kills the cycle of every integral closed subspace of
  every good test space.
* `AlgebraicGeometry.Space.eq_zero_iff_capsFundamentalClassesToZero` — **Stacks 0ERS**.

## Implementation notes

### An integral space over `X`, and its fundamental class

An integral algebraic space `Y` locally of finite type over `X` is presented as a good test space
`g : Y ⟶ X` over the base together with an integral closed subspace of `Y` whose set of points is
all of `|Y|`. For a good algebraic space over the base, having such a subspace is integrality:
goodness gives decency, and Stacks 0ENF matches the integral closed subspaces with the
irreducible closed subsets of the space of points, so the subspace with full point set exists
exactly when `|Y|` is irreducible and the reduced induced structure on it is `Y`, which by
Stacks 0EDV is integrality. That subspace is
`AlgebraicGeometry.Space.IntegralClosedSubspace.whole` when `Y` is itself presented as an
integral closed subspace of something, and `[Y]` is the cycle
`AlgebraicGeometry.Space.integralClosedSubspaceCycle` of it. The cycle of a subspace is defined
at every degree `k` and is zero when the δ-dimension of the subspace is not `k`, so no
δ-dimension hypothesis is carried by the statements.

### What the converse is assumed, and what it proves

Rational equivalence on an algebraic space is not available in this repository, so the Chow
groups and their three operations are the parameter
`AlgebraicGeometry.Space.ChowGroupSystem`, which carries no axiom relating them to cycles; see
the implementation notes of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant`. The step of
the source proof which computes `c ∩ [Z]` by proper pushforward from `Z` therefore needs the
compatibility `AlgebraicGeometry.Space.ChowGroupSystem.IsInducedByClosedCyclePushforward`: the
class of a cycle pushed forward along a closed immersion is the pushforward of its class. That
is how the proper pushforward of Stacks 82.15 is constructed, and it is not derivable from the
fields of a `ChowGroupSystem`. Goodness of the fibre products that the naturality axiom of
Stacks 0ERJ quantifies over, and properness of the base change of a closed immersion, are
likewise hypotheses, bundled as
`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.HasGoodSubspaceBaseChanges`; they are
hypotheses throughout this development, the theorems supplying them for algebraic spaces not
being available.

Given those, `AlgebraicGeometry.Space.cap_integralClosedSubspaceCycle_eq_zero` is the content of
the converse: `c ∩ [Z] = 0` for every integral closed subspace `Z` of every good test space. It
upgrades to `c = 0` for a class `α ∈ CH_k(X')` which is the class of a cycle with *finite*
support, since such a cycle is a finite sum of the cycles `[Z]`. The source handles an arbitrary,
merely locally finite, cycle `∑ n_i [Z_i]` by passing to `X'' = ∐ Z_i`, using that `X'' ⟶ X'` is
proper, that `CH_{k-p}(X'') = ∏ CH_{k-p}(Z_i)` and that the projections of that product are flat
pullbacks. None of the coproduct `∐ Z_i` as a good algebraic space over the base, the properness
of `∐ Z_i ⟶ X'`, nor the product decomposition of the Chow groups is available here — the last
is Stacks 0ES2, which
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClopenDecomposition` has for cycles only, again for
want of rational equivalence. So `AlgebraicGeometry.Space.eq_zero_iff_capsFundamentalClassesToZero`
carries the hypothesis that every Chow class on a good test space over `X` is the class of a
cycle with finite support, and the `@[stacks 0ERS]` attribute says so.

## References

* [Stacks Project, Tag 0ERS](https://stacks.math.columbia.edu/tag/0ERS)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0ES2](https://stacks.math.columbia.edu/tag/0ES2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### An integral closed subspace as an integral closed subspace of itself -/

section Whole

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An integral closed subspace `Z`, read as an integral closed subspace of itself: the reduced
closed subspace on all of `|Z|`, which is irreducible and closed because `Z` is integral. -/
def IntegralClosedSubspace.whole (Z : IntegralClosedSubspace B S hS X) :
    IntegralClosedSubspace B S hS Z.subspace.toFunctor :=
  letI := Z.isIntegralSpace.2.2
  integralClosedSubspaceOfPoints B S hS Z.isClosedSubspace.1 Z.isIntegralSpace.2.1
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ (points B S hS Z.subspace.toFunctor),
      isClosed_univ⟩

/-- The set of points of an integral closed subspace, read inside itself, is everything. -/
@[simp]
theorem IntegralClosedSubspace.subspacePointSet_whole (Z : IntegralClosedSubspace B S hS X) :
    subspacePointSet B S hS Z.subspace.toFunctor (Z.whole B S hS).subspace = Set.univ :=
  subspacePointSet_integralClosedSubspaceOfPoints B S hS Z.isClosedSubspace.1
    Z.isIntegralSpace.2.1 _

/-- Pushing an integral closed subspace, read inside itself, forward along its own inclusion
returns it: the two have the same set of points. -/
theorem IntegralClosedSubspace.pushforward_whole (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (Z : IntegralClosedSubspace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z.subspace.toFunctor) :
    IntegralClosedSubspace.pushforward B S hS hX hZ hXdec Z.isClosedSubspace.2
        (Z.whole B S hS) = Z := by
  refine injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext ?_)
  show subspacePointSet B S hS X
      (IntegralClosedSubspace.pushforward B S hS hX hZ hXdec Z.isClosedSubspace.2
        (Z.whole B S hS)).subspace =
    subspacePointSet B S hS X Z.subspace
  rw [IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_whole, Set.image_univ]

end Whole

/-! ### The cycle of an integral closed subspace -/

section Cycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The δ-dimension of an integral closed subspace, read inside itself, is its δ-dimension in
the ambient space: the inclusion is a closed immersion over the base and pushing forward does
not change the δ-dimension. -/
theorem deltaDimension_whole (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : IsAlgebraicSpace D.site D.base D.base_mem Z.subspace.toFunctor)
    (sZ : Z.subspace.toFunctor ⟶ D.space) (hic : Z.subspace.ι ≫ sX = sZ) :
    deltaDimension D sZ (Z.whole D.site D.base D.base_mem) = deltaDimension D sX Z := by
  subst hic
  rw [← IntegralClosedSubspace.deltaDimension_pushforward D sX hsX hX hZ hXdec
      Z.isClosedSubspace.2 (Z.whole D.site D.base D.base_mem),
    IntegralClosedSubspace.pushforward_whole D.site D.base D.base_mem hX hXdec Z hZ]

open scoped Classical in
/-- The coefficient family of the cycle `[Z]` of an integral closed subspace in degree `k`:
`1` at `Z` and `0` elsewhere when the δ-dimension of `Z` is `k`, and the zero family
otherwise. -/
def integralClosedSubspaceCycleCoeff (sX : X ⟶ D.space)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  fun W => if W = Z ∧ deltaDimension D sX Z = k then 1 else 0

variable (sX : X ⟶ D.space) (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)

/-- A nonzero coefficient of the cycle of an integral closed subspace sits at that subspace, and
its δ-dimension is the degree. -/
theorem eq_and_deltaDimension_eq_of_integralClosedSubspaceCycleCoeff_ne_zero
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : integralClosedSubspaceCycleCoeff D sX Z k W ≠ 0) :
    W = Z ∧ deltaDimension D sX Z = k := by
  classical
  by_contra h
  exact hW (ite_eq_right_iff.2 fun hp => absurd hp h)

/-- The coefficient of the cycle of an integral closed subspace at that subspace is `1`, as soon
as the δ-dimension is the degree. -/
@[simp]
theorem integralClosedSubspaceCycleCoeff_self (hk : deltaDimension D sX Z = k) :
    integralClosedSubspaceCycleCoeff D sX Z k Z = 1 := by
  classical
  exact ite_eq_left_iff.2 fun h => absurd ⟨rfl, hk⟩ h

/-- The coefficient of the cycle of an integral closed subspace away from that subspace is
zero. -/
@[simp]
theorem integralClosedSubspaceCycleCoeff_of_ne
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hW : W ≠ Z) :
    integralClosedSubspaceCycleCoeff D sX Z k W = 0 := by
  classical
  exact ite_eq_right_iff.2 fun h => absurd h.1 hW

/-- The cycle of an integral closed subspace is a `k`-cycle: its support is the single subspace,
so it is locally finite, and the δ-dimension there is `k` whenever the coefficient is
nonzero. -/
theorem integralClosedSubspaceCycleCoeff_mem_cyclesOfDimension :
    integralClosedSubspaceCycleCoeff D sX Z k ∈ cyclesOfDimension D sX k := by
  refine ⟨fun x => ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton Z).subset ?_⟩, ?_⟩
  · intro W hW
    obtain ⟨q, hq, -⟩ := hW
    by_cases hc : integralClosedSubspaceCycleCoeff D sX Z k W = 0
    · simp [hc] at hq
    · exact (eq_and_deltaDimension_eq_of_integralClosedSubspaceCycleCoeff_ne_zero D sX Z k hc).1
  · intro W hW
    obtain ⟨rfl, hk⟩ :=
      eq_and_deltaDimension_eq_of_integralClosedSubspaceCycleCoeff_ne_zero D sX Z k hW
    exact hk

/-- **Stacks 0EDZ for a single subspace.** The cycle `[Z]` of an integral closed subspace of a
good algebraic space over the base, as an element of `Z_k(X)`. It is zero unless the
δ-dimension of `Z` is `k`. -/
def integralClosedSubspaceCycle : CycleGroup D sX k :=
  ⟨integralClosedSubspaceCycleCoeff D sX Z k,
    integralClosedSubspaceCycleCoeff_mem_cyclesOfDimension D sX Z k⟩

/-- The coefficient function of the cycle `[Z]` is `integralClosedSubspaceCycleCoeff`. -/
@[simp]
theorem integralClosedSubspaceCycle_coe :
    (integralClosedSubspaceCycle D sX Z k).1 = integralClosedSubspaceCycleCoeff D sX Z k :=
  rfl

end Cycle

/-! ### A cycle with finite support is a finite sum of cycles of subspaces -/

section Sum

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A `k`-cycle whose support is contained in a finite set of integral closed subspaces is the
sum, over that set, of its coefficients times the cycles of those subspaces. -/
theorem eq_sum_integralClosedSubspaceCycle (sX : X ⟶ D.space) (k : ℤ)
    (β : CycleGroup D sX k)
    (s : Finset (IntegralClosedSubspace D.site D.base D.base_mem X))
    (hs : ∀ Z, β.1 Z ≠ 0 → Z ∈ s) :
    β = ∑ Z ∈ s, β.1 Z • integralClosedSubspaceCycle D sX Z k := by
  refine Subtype.ext (funext fun W => ?_)
  have hcoe : (∑ Z ∈ s, β.1 Z • integralClosedSubspaceCycle D sX Z k).1 W =
      ∑ Z ∈ s, β.1 Z * integralClosedSubspaceCycleCoeff D sX Z k W := by
    rw [AddSubmonoidClass.coe_finsetSum]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun Z _ => by
      simp
  rw [hcoe, Finset.sum_eq_single W
    (fun Z _ hZW => by rw [integralClosedSubspaceCycleCoeff_of_ne D sX Z k (Ne.symm hZW), mul_zero])
    fun hW => by rw [of_not_not (mt (hs W) hW), zero_mul]]
  by_cases hβW : β.1 W = 0
  · rw [hβW, zero_mul]
  · rw [integralClosedSubspaceCycleCoeff_self D sX W k (β.2.2 W hβW), mul_one]

end Sum

/-! ### Goodness and properness of an integral closed subspace -/

section Good

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- An integral closed subspace of a good algebraic space over the base is again good over the
base: its inclusion is a closed immersion, hence quasi-separated and locally of finite type, and
both properties are stable under composition. -/
theorem isGood_integralClosedSubspace (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    D.IsGood (Z.subspace.ι ≫ sX) :=
  ⟨Z.isClosedSubspace.1,
    isQuasiSeparated_comp D.site D.base D.base_mem Z.isClosedSubspace.1 hX.1 _ _
      (isQuasiSeparated_of_isClosedImmersion D.site D.base D.base_mem Z.isClosedSubspace.2)
      hX.2.1,
    isLocallyOfFiniteType_comp D.site D.base D.base_mem Z.isClosedSubspace.1 hX.1
      D.isAlgebraicSpace _ _
      (isLocallyOfFiniteType_of_isClosedImmersion D.site D.base D.base_mem _
        Z.isClosedSubspace.2) hX.2.2⟩

/-- **Stacks 04XZ for an integral closed subspace.** The inclusion of an integral closed subspace
is proper, being a closed immersion. -/
theorem isProper_integralClosedSubspace_ι (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsProper D.site D.base D.base_mem Z.subspace.ι :=
  isProper_of_isClosedImmersion D.site D.base D.base_mem Z.isClosedSubspace.1 hX _
    Z.isClosedSubspace.2

/-- The cycle of an integral closed subspace is the pushforward along its inclusion of its own
cycle, read inside itself: at the image of a subspace the coefficient is unchanged, pushing
forward is injective and carries the whole of `Z` to `Z`, and the δ-dimension is unchanged. -/
theorem cycleGroupClosedPushforward_cycle_whole (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : IsAlgebraicSpace D.site D.base D.base_mem Z.subspace.toFunctor)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (sZ : Z.subspace.toFunctor ⟶ D.space) (hic : Z.subspace.ι ≫ sX = sZ) (k : ℤ) :
    cycleGroupClosedPushforward D hX.1 hZ hXdec Z.isClosedSubspace.2 sX hX.2.2 sZ hic k
        (integralClosedSubspaceCycle D sZ (Z.whole D.site D.base D.base_mem) k) =
      integralClosedSubspaceCycle D sX Z k := by
  classical
  have hdim : deltaDimension D sZ (Z.whole D.site D.base D.base_mem) = deltaDimension D sX Z :=
    deltaDimension_whole D sX hX.2.2 hX.1 hXdec Z hZ sZ hic
  have hpw : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hZ hXdec
      Z.isClosedSubspace.2 (Z.whole D.site D.base D.base_mem) = Z :=
    IntegralClosedSubspace.pushforward_whole D.site D.base D.base_mem hX.1 hXdec Z hZ
  refine Subtype.ext (funext fun W => ?_)
  show cycleClosedPushforward D hX.1 hZ hXdec Z.isClosedSubspace.2
      (integralClosedSubspaceCycleCoeff D sZ (Z.whole D.site D.base D.base_mem) k) W =
    integralClosedSubspaceCycleCoeff D sX Z k W
  by_cases hW : ∃ V, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hZ hXdec
      Z.isClosedSubspace.2 V = W
  · obtain ⟨V, rfl⟩ := hW
    rw [cycleClosedPushforward_apply_pushforward]
    unfold integralClosedSubspaceCycleCoeff
    refine if_congr (Iff.intro ?_ ?_) rfl rfl
    · rintro ⟨rfl, hk⟩
      exact ⟨hpw, hdim.symm.trans hk⟩
    · rintro ⟨hVZ, hk⟩
      refine ⟨IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 hZ
        hXdec Z.isClosedSubspace.2 (hVZ.trans hpw.symm), hdim.trans hk⟩
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hZ hXdec Z.isClosedSubspace.2 _ W
      fun V hV => hW ⟨V, hV⟩]
    refine (integralClosedSubspaceCycleCoeff_of_ne D sX Z k ?_).symm
    intro hWZ
    exact hW ⟨Z.whole D.site D.base D.base_mem, hpw.trans hWZ.symm⟩

end Good

/-! ### Stacks 0ERS -/

section Vanishing

/-- Compatibility of the parameterized proper pushforward of a Chow-group system with the
pushforward of cycles along a closed immersion over the base: the pushforward of the class of a
cycle is the class of the pushed-forward cycle. -/
def ChowGroupSystem.IsInducedByClosedCyclePushforward {D : BaseSpaceDimensionSituation.{u}}
    (G : ChowGroupSystem D) : Prop :=
  ∀ {X Z : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (sZ : Z ⟶ D.space)
    (hZ : D.IsGood sZ) {i : Z ⟶ X} (hic : IsClosedImmersion D.site D.base D.base_mem i)
    (hi : i ≫ sX = sZ) (hproper : IsProper D.site D.base D.base_mem i) (k : ℤ)
    (β : CycleGroup D sZ k),
    G.properPushforward sZ hZ sX hX i hi hproper k (G.cycleClass sZ hZ k β) =
      G.cycleClass sX hX k
        (cycleGroupClosedPushforward D hX.1 hZ.1 (D.isDecentSpace_of_isGood sX hX) hic sX hX.2.2
          sZ hi k β)

/-- Goodness and properness of the fibre products appearing in the proper naturality axiom of
Stacks 0ERJ at the inclusion of an integral closed subspace: for every test space `g : X' ⟶ X`
and every integral closed subspace `Z ⊆ X'`, the fibre product `X ×_X Z` is good over the base
and the base change of the inclusion of `Z` to it is proper. -/
structure BaseSpaceDimensionSituation.HasGoodSubspaceBaseChanges
    (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space) : Prop where
  /-- The fibre product `X ×_X Z` is good over the base. -/
  isGood : ∀ {X' : D.Ambient} (g : X' ⟶ X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X'),
    D.IsGood (pullback.fst (𝟙 X) (Z.subspace.ι ≫ g) ≫ sX)
  /-- The base change of the inclusion of `Z` is proper. -/
  isProper : ∀ {X' : D.Ambient} (g : X' ⟶ X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X'),
    IsProper D.site D.base D.base_mem (bivariantBaseChangeMap D (𝟙 X) g Z.subspace.ι)

variable (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D) {X : D.Ambient}
  (sX : X ⟶ D.space) (hX : D.IsGood sX) (p : ℤ)

/-- The condition of Stacks 0ERS on a class `c ∈ A^p(X)`: `c ∩ [Y] = 0` in `CH_*(Y)` for every
integral algebraic space `Y` locally of finite type over `X`. Such a `Y` is presented as a good
test space `g : Y ⟶ X` over the base together with an integral closed subspace of `Y` whose set
of points is all of `|Y|`, and `[Y]` is the cycle of that subspace. -/
def BivariantClass.CapsFundamentalClassesToZero (c : chowCohomologyComponent D G sX hX p) :
    Prop :=
  ∀ {Y : D.Ambient} (g : Y ⟶ X) (hg : D.IsGood (g ≫ sX))
    (hpb : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (_hW : subspacePointSet D.site D.base D.base_mem Y W.subspace = Set.univ) (k : ℤ)
    (_hk : deltaDimension D (g ≫ sX) W = k),
    c.cap g hg hpb k
      (G.cycleClass (g ≫ sX) hg k (integralClosedSubspaceCycle D (g ≫ sX) W k)) = 0

/-- **Stacks 0ERS, the forward implication.** The zero class of `A^p(X)` caps the fundamental
class of every integral algebraic space locally of finite type over `X` to zero. -/
@[stacks 0ERS "the forward implication"]
theorem zero_capsFundamentalClassesToZero :
    BivariantClass.CapsFundamentalClassesToZero D G sX hX p 0 := by
  intro Y g hg hpb W _hW k _hk
  exact BivariantClass.zero_cap D G sX hX sX hX (𝟙 X) (Category.id_comp sX) p g hg hpb _ _

/-- **Stacks 0ERS, the content of the converse.** If `c ∈ A^p(X)` caps the fundamental class of
every integral algebraic space locally of finite type over `X` to zero, then it caps the cycle
of every integral closed subspace of every good test space over `X` to zero: push forward along
the inclusion of the subspace, where the hypothesis applies. -/
@[stacks 0ERS "the converse on the cycle of an integral closed subspace"]
theorem cap_integralClosedSubspaceCycle_eq_zero
    (hpp : G.IsInducedByClosedCyclePushforward) (hbc : D.HasGoodSubspaceBaseChanges sX)
    (c : chowCohomologyComponent D G sX hX p)
    (hc : BivariantClass.CapsFundamentalClassesToZero D G sX hX p c)
    {X' : D.Ambient} (g : X' ⟶ X) (hg : D.IsGood (g ≫ sX))
    (hpb : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X') (k : ℤ)
    (hk : deltaDimension D (g ≫ sX) Z = k) :
    c.cap g hg hpb k
      (G.cycleClass (g ≫ sX) hg k (integralClosedSubspaceCycle D (g ≫ sX) Z k)) = 0 := by
  have hZgood : D.IsGood ((Z.subspace.ι ≫ g) ≫ sX) := by
    rw [Category.assoc]
    exact isGood_integralClosedSubspace D (g ≫ sX) hg Z
  have hassoc : Z.subspace.ι ≫ g ≫ sX = (Z.subspace.ι ≫ g) ≫ sX :=
    (Category.assoc Z.subspace.ι g sX).symm
  have hdim : deltaDimension D ((Z.subspace.ι ≫ g) ≫ sX)
      (Z.whole D.site D.base D.base_mem) = deltaDimension D (g ≫ sX) Z :=
    deltaDimension_whole D (g ≫ sX) hg.2.2 hg.1 (D.isDecentSpace_of_isGood (g ≫ sX) hg) Z
      Z.isClosedSubspace.1 _ hassoc
  have hvanish := hc (Z.subspace.ι ≫ g) hZgood (hbc.isGood g Z)
    (Z.whole D.site D.base D.base_mem)
    (IntegralClosedSubspace.subspacePointSet_whole D.site D.base D.base_mem Z) k
    (hdim.trans hk)
  have hcomm : pullback.snd (𝟙 X) (Z.subspace.ι ≫ g) ≫ Z.subspace.ι =
      bivariantBaseChangeMap D (𝟙 X) g Z.subspace.ι ≫ pullback.snd (𝟙 X) g :=
    (pullback.lift_snd _ _ _).symm
  have hfst : bivariantBaseChangeMap D (𝟙 X) g Z.subspace.ι ≫ pullback.fst (𝟙 X) g =
      pullback.fst (𝟙 X) (Z.subspace.ι ≫ g) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hnat := c.proper_naturality g hg hpb Z.subspace.ι hZgood (hbc.isGood g Z)
    (isProper_integralClosedSubspace_ι D hg.1 Z)
    (bivariantBaseChangeMap D (𝟙 X) g Z.subspace.ι)
    (IsPullback.of_horiz_isIso ⟨hcomm⟩) hfst (hbc.isProper g Z)
    k
    (G.cycleClass ((Z.subspace.ι ≫ g) ≫ sX) hZgood k
      (integralClosedSubspaceCycle D ((Z.subspace.ι ≫ g) ≫ sX)
        (Z.whole D.site D.base D.base_mem) k))
  rw [hpp (g ≫ sX) hg ((Z.subspace.ι ≫ g) ≫ sX) hZgood Z.isClosedSubspace.2 hassoc
      (isProper_integralClosedSubspace_ι D hg.1 Z) _ _,
    cycleGroupClosedPushforward_cycle_whole D (g ≫ sX) hg Z Z.isClosedSubspace.1
      (D.isDecentSpace_of_isGood (g ≫ sX) hg) _ hassoc] at hnat
  rw [hnat, hvanish, map_zero]

/-- **Stacks 0ERS.** A class `c ∈ A^p(X)` is zero if and only if `c ∩ [Y] = 0` in `CH_*(Y)` for
every integral algebraic space `Y` locally of finite type over `X`. -/
@[stacks 0ERS "for Chow classes of cycles of finite support, over a cycle-induced pushforward"]
theorem eq_zero_iff_capsFundamentalClassesToZero
    (hpp : G.IsInducedByClosedCyclePushforward) (hbc : D.HasGoodSubspaceBaseChanges sX)
    (hfin : ∀ {X' : D.Ambient} (g : X' ⟶ X) (hg : D.IsGood (g ≫ sX)) (k : ℤ)
      (α : G.chow (g ≫ sX) hg k), ∃ β : CycleGroup D (g ≫ sX) k,
        (Function.support β.1).Finite ∧ G.cycleClass (g ≫ sX) hg k β = α)
    (c : chowCohomologyComponent D G sX hX p) :
    c = 0 ↔ BivariantClass.CapsFundamentalClassesToZero D G sX hX p c := by
  refine ⟨fun h => h ▸ zero_capsFundamentalClassesToZero D G sX hX p, fun hc => ?_⟩
  refine BivariantClass.ext D G sX hX sX hX (𝟙 X) (Category.id_comp sX) p ?_
  intro X' g hg hpb k α
  rw [BivariantClass.zero_cap]
  obtain ⟨β, hβfin, rfl⟩ := hfin g hg k α
  rw [eq_sum_integralClosedSubspaceCycle D (g ≫ sX) k β hβfin.toFinset
      fun Z hZ => hβfin.mem_toFinset.2 hZ,
    map_sum, map_sum]
  refine Finset.sum_eq_zero fun Z hZ => ?_
  rw [map_zsmul, map_zsmul,
    cap_integralClosedSubspaceCycle_eq_zero D G sX hX p hpp hbc c hc g hg hpb Z k
      (β.2.2 Z (hβfin.mem_toFinset.1 hZ)),
    smul_zero]

end Vanishing

end AlgebraicGeometry.Space

end

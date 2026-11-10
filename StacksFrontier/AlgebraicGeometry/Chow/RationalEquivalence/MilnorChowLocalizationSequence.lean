module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainDivisorCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChowGroupOne
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwisePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# The six-term localization sequence of Stacks 0GUA

Let `(S, δ)` be the base situation of chapter 42, let `p : X ⟶ S` be locally of finite type, let
`V ⊆ X` be an open subscheme and let `i : Y ⟶ X` be a closed immersion whose image is the
complement of `V`. Stacks 0GUA asserts the exact sequence

`CH^M_k(Y, 1) ⟶ CH^M_k(X, 1) ⟶ CH^M_k(V, 1) ⟶ CH_k(Y) ⟶ CH_k(X) ⟶ CH_k(V) ⟶ 0`

obtained by applying the snake lemma to the degreewise split short exact sequences of locally
finite Milnor K-chains of that tag, which are compatible with both differentials of the complex
of Stacks 0GU9.

## The construction

The three degreewise sequences are split (`Stacks.Chow.milnorChainLocalizationSplitting`), so the
section `s` and the retraction `r` are available as honest homomorphisms and no choices are
needed. The connecting map is therefore the *composite*

`Stacks.Chow.milnorChainPreBoundary = q₀ ∘ d_X ∘ s₁`,

where `s₁` is extension by zero from `V` in Milnor degree one, `d_X` the divisor differential of
Stacks 0GU3 on `X`, and `q₀` restriction to `Y` in Milnor degree zero; it kills the tame-symbol
boundary outright, because the tame-symbol square for `s₁` turns it into the composite of the two
differentials of Stacks 0GU9, which vanishes. Composing with the presentation
`Stacks.Chow.pointwiseChowClass` of the Chow group of `Y` and descending gives
`Stacks.Chow.milnorChowBoundary`.

The six-term sequence then has three new exactness assertions, each a chase using only the two
splitting identities and the four squares; the exactness at `CH_k(X)` and the surjectivity onto
`CH_k(V)` are Stacks 02RX, already available as
`Stacks.Chow.exact_chowPushforward_chowGroupOpensRestrict` and
`Stacks.Chow.surjective_chowGroupOpensRestrictOfIsOpenImmersion`. The one geometric input is
`Stacks.Chow.pointwiseChowClass_milnorChainExtend`: extension by zero of a locally finite
degree-zero Milnor K-chain *is* proper pushforward of cycles along the closed immersion, the
fibre of a closed immersion being a single point of residue degree one.

## Main definitions

* `Stacks.Chow.milnorChowGroupOneExtend`, `Stacks.Chow.milnorChowGroupOneComap` — the two maps of
  first higher Chow groups induced by the extension-by-zero and restriction maps of chains.
* `Stacks.Chow.milnorChainPreBoundary` — the connecting map at the level of chains.
* `Stacks.Chow.milnorChowBoundary` — the connecting map `CH^M_k(V, 1) ⟶ CH_k(Y)`.

## Main results

* `Stacks.Chow.pointwiseChowClass_milnorChainExtend` — extension by zero of a degree-zero chain is
  proper pushforward of cycles.
* `Stacks.Chow.exact_milnorChowGroupOneExtend_milnorChowGroupOneComap`,
  `Stacks.Chow.exact_milnorChowGroupOneComap_milnorChowBoundary`,
  `Stacks.Chow.exact_milnorChowBoundary_chowPushforward` — the three new exactness assertions.
* `Stacks.Chow.milnorChowLocalization_exact` — **Stacks 0GUA**: the six-term exact sequence.

## References

* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The group structure of locally finite Milnor K-chains, stated once so that instance search
does not rediscover it through the subgroup coercion. -/
instance (priority := high) addCommGroupMilnorChainGroup_milnorChowLocalizationSequence
    {C : ChowSituation.{u}} {X : Scheme.{u}} (p : X ⟶ C.S) (m : ℤ) (n : ℕ) :
    AddCommGroup (MilnorChainGroup C p m n) :=
  inferInstance

/-- The group structure of pointwise Milnor K₁-chains, stated once for the same reason. -/
instance (priority := high) addCommGroupPointwiseKOneGroup_milnorChowLocalizationSequence
    {C : ChowSituation.{u}} {X : Scheme.{u}} (p : X ⟶ C.S) (k : ℤ) :
    AddCommGroup (PointwiseKOneGroup C p k) :=
  inferInstance

/-- The additive unital structure of locally finite Milnor K-chains, read off the group
structure above, so that instance search does not descend into the ambient product. -/
instance (priority := high) addZeroClassMilnorChainGroup_milnorChowLocalizationSequence
    {C : ChowSituation.{u}} {X : Scheme.{u}} (p : X ⟶ C.S) (m : ℤ) (n : ℕ) :
    AddZeroClass (MilnorChainGroup C p m n) :=
  AddMonoid.toAddZeroClass

/-- The additive unital structure of pointwise Milnor K₁-chains, for the same reason. -/
instance (priority := high) addZeroClassPointwiseKOneGroup_milnorChowLocalizationSequence
    {C : ChowSituation.{u}} {X : Scheme.{u}} (p : X ⟶ C.S) (k : ℤ) :
    AddZeroClass (PointwiseKOneGroup C p k) :=
  AddMonoid.toAddZeroClass

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (i : Y ⟶ X) [IsClosedImmersion i] (V : X.Opens)

/-! ### The four chain maps of the degreewise localization sequence -/

/-- Extension by zero of locally finite Milnor K-chains from the closed subscheme. -/
abbrev closedChainExtend (m : ℤ) (n : ℕ) :
    MilnorChainGroup C (i ≫ p) m n →+ MilnorChainGroup C p m n :=
  milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
    (bijective_residueFieldMap_closedImmersion i) inferInstance m n

/-- Restriction of locally finite Milnor K-chains to the closed subscheme: the retraction of the
degreewise localization sequence. -/
abbrev closedChainComap (m : ℤ) (n : ℕ) :
    MilnorChainGroup C p m n →+ MilnorChainGroup C (i ≫ p) m n :=
  milnorChainComap C p i (injective_base_of_isClosedImmersion i)
    (bijective_residueFieldMap_closedImmersion i) m n

/-- Restriction of locally finite Milnor K-chains to the open subscheme. -/
abbrev openChainComap (m : ℤ) (n : ℕ) :
    MilnorChainGroup C p m n →+ MilnorChainGroup C (V.ι ≫ p) m n :=
  milnorChainComap C p V.ι (injective_base_of_isOpenImmersion V.ι)
    (bijective_residueFieldMap_openImmersion V.ι) m n

/-- Extension by zero of locally finite Milnor K-chains from the open subscheme: the section of
the degreewise localization sequence. -/
abbrev openChainExtend (m : ℤ) (n : ℕ) :
    MilnorChainGroup C (V.ι ≫ p) m n →+ MilnorChainGroup C p m n :=
  milnorChainExtend C p V.ι (injective_base_of_isOpenImmersion V.ι)
    (bijective_residueFieldMap_openImmersion V.ι)
    (quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType p V.ι) m n

/-! ### Extension by zero of a cycle is proper pushforward -/

/-- **Extension by zero of a locally finite degree-zero Milnor K-chain is proper pushforward of
cycles along the closed immersion.** Both sides vanish off the image, and at a point of the image
the fibre of the closed immersion is the single point above it, of residue degree one. -/
theorem pointwiseCycleEquiv_symm_closedChainExtend (k : ℤ)
    (b : PointwiseCycleGroup C (i ≫ p) k) :
    (pointwiseCycleEquiv C p k).symm (closedChainExtend C p i k 0 b) =
      properPushforward C (i ≫ p) p i rfl k ((pointwiseCycleEquiv C (i ≫ p) k).symm b) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  have hdim : ∀ z : Y, (i.base z ∈ pointsOfDimension C p k) ↔
      z ∈ pointsOfDimension C (i ≫ p) k := by
    intro z
    rw [mem_pointsOfDimension, mem_pointsOfDimension,
      relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction i p z
        (bijective_residueFieldMap_closedImmersion i z)]
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    rw [pointwiseCycleEquiv_symm_apply,
      properPushforward_apply_image_of_isClosedImmersion C (i ≫ p) p i rfl k,
      pointwiseCycleEquiv_symm_apply]
    by_cases hz : z ∈ pointsOfDimension C (i ≫ p) k
    · rw [pointwiseCoeff_of_mem C p _ ((hdim z).mpr hz), pointwiseCoeff_of_mem C (i ≫ p) b hz,
        milnorChainExtend_apply_immersionPoint C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance k 0 b ⟨z, hz⟩,
        milnorKTheoryZeroAddEquiv_milnorKTransport]
    · rw [pointwiseCoeff_of_not_mem C p _ (fun hcon ↦ hz ((hdim z).mp hcon)),
        pointwiseCoeff_of_not_mem C (i ≫ p) b hz]
  · rw [pointwiseCycleEquiv_symm_apply,
      properPushforward_apply_of_notMem_range C (i ≫ p) p i rfl k _ hx]
    by_cases hxd : x ∈ pointsOfDimension C p k
    · rw [pointwiseCoeff_of_mem C p _ hxd, milnorChainExtend_apply,
        milnorChainExtendAtHom_of_notMem_range C p i
          (bijective_residueFieldMap_closedImmersion i) ⟨x, hxd⟩ hx,
        AddMonoidHom.zero_apply, map_zero]
    · rw [pointwiseCoeff_of_not_mem C p _ hxd]

/-- **The class of an extension by zero is the proper pushforward of the class.** -/
theorem pointwiseChowClass_milnorChainExtend (k : ℤ) (b : PointwiseCycleGroup C (i ≫ p) k) :
    pointwiseChowClass C p k (closedChainExtend C p i k 0 b) =
      chowPushforwardOfIsClosedImmersion C (i ≫ p) p i rfl k
        (pointwiseChowClass C (i ≫ p) k b) := by
  change QuotientAddGroup.mk' (rationalEquivalences C p k)
      ((pointwiseCycleEquiv C p k).symm (closedChainExtend C p i k 0 b)) = _
  rw [pointwiseCycleEquiv_symm_closedChainExtend]
  exact (chowPushforwardOfIsClosedImmersion_mk C (i ≫ p) p i rfl k _).symm

/-! ### The presentation of the Chow group, read as a kernel -/

/-- A pointwise cycle has class zero in the Chow group exactly when it is the divisor of a
pointwise Milnor K₁-chain. This is
`Stacks.Chow.pointwiseDivisorDifferential_range_eq_ker_pointwiseChowClass` in the form the chases
below use. -/
theorem pointwiseChowClass_eq_zero_iff (k : ℤ) (c : PointwiseCycleGroup C p k) :
    pointwiseChowClass C p k c = 0 ↔
      ∃ w : PointwiseKOneGroup C p k, pointwiseDivisorDifferential C p k w = c := by
  rw [← AddMonoidHom.mem_ker, ← pointwiseDivisorDifferential_range_eq_ker_pointwiseChowClass]
  exact AddMonoidHom.mem_range

/-- The divisor of a pointwise Milnor K₁-chain has class zero in the Chow group. -/
theorem pointwiseChowClass_pointwiseDivisorDifferential (k : ℤ)
    (w : PointwiseKOneGroup C p k) :
    pointwiseChowClass C p k (pointwiseDivisorDifferential C p k w) = 0 :=
  (pointwiseChowClass_eq_zero_iff C p k _).mpr ⟨w, rfl⟩

/-! ### The splitting identities -/

omit [LocallyOfFiniteType p] in
/-- Restricting to the closed subscheme an extension by zero from it returns the chain. -/
theorem closedChainComap_closedChainExtend (m : ℤ) (n : ℕ)
    (b : MilnorChainGroup C (i ≫ p) m n) :
    closedChainComap C p i m n (closedChainExtend C p i m n b) = b :=
  DFunLike.congr_fun (milnorChainComap_milnorChainExtend C p i
    (injective_base_of_isClosedImmersion i) (bijective_residueFieldMap_closedImmersion i)
    inferInstance m n) b

omit [LocallyOfFiniteType p] in
/-- Extension by zero from the closed subscheme is injective. -/
theorem closedChainExtend_injective (m : ℤ) (n : ℕ) :
    Function.Injective (closedChainExtend C p i m n) := fun b b' h ↦ by
  rw [← closedChainComap_closedChainExtend C p i m n b,
    ← closedChainComap_closedChainExtend C p i m n b', h]

/-- Restricting to the open subscheme an extension by zero from it returns the chain. -/
theorem openChainComap_openChainExtend (m : ℤ) (n : ℕ)
    (b : MilnorChainGroup C (V.ι ≫ p) m n) :
    openChainComap C p V m n (openChainExtend C p V m n b) = b :=
  DFunLike.congr_fun (milnorChainComap_milnorChainExtend C p V.ι
    (injective_base_of_isOpenImmersion V.ι) (bijective_residueFieldMap_openImmersion V.ι)
    (quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType p V.ι) m n) b

section Complementary

variable (hcomp : Set.range i.base = (Set.range V.ι.base)ᶜ)

include hcomp

omit [LocallyOfFiniteType p] in
/-- An extension by zero from the closed subscheme restricts to zero on the open subscheme. -/
theorem openChainComap_closedChainExtend (m : ℤ) (n : ℕ)
    (b : MilnorChainGroup C (i ≫ p) m n) :
    openChainComap C p V m n (closedChainExtend C p i m n b) = 0 :=
  milnorChainComap_milnorChainExtend_eq_zero C p i V.ι hcomp m n b

/-- **The two extensions are complementary**, in applied form. -/
theorem closedChainExtend_add_openChainExtend (m : ℤ) (n : ℕ)
    (a : MilnorChainGroup C p m n) :
    closedChainExtend C p i m n (closedChainComap C p i m n a) +
        openChainExtend C p V m n (openChainComap C p V m n a) = a :=
  milnorChainExtend_milnorChainComap_add C p i V.ι hcomp m n a

/-- A chain restricting to zero on the open subscheme is an extension by zero from the closed
subscheme. -/
theorem closedChainExtend_closedChainComap_of_openChainComap_eq_zero (m : ℤ) (n : ℕ)
    {a : MilnorChainGroup C p m n} (ha : openChainComap C p V m n a = 0) :
    closedChainExtend C p i m n (closedChainComap C p i m n a) = a := by
  have h := closedChainExtend_add_openChainExtend C p i V hcomp m n a
  rwa [ha, map_zero, add_zero] at h

/-- The part of a chain supported on the closed subscheme, read as the complement of the part
supported on the open subscheme. -/
theorem closedChainExtend_closedChainComap_eq_sub (m : ℤ) (n : ℕ)
    (a : MilnorChainGroup C p m n) :
    closedChainExtend C p i m n (closedChainComap C p i m n a) =
      a - openChainExtend C p V m n (openChainComap C p V m n a) :=
  eq_sub_of_add_eq (closedChainExtend_add_openChainExtend C p i V hcomp m n a)

/-- The part of a chain supported on the open subscheme, read as the complement of the part
supported on the closed subscheme. -/
theorem openChainExtend_openChainComap_eq_sub (m : ℤ) (n : ℕ) (a : MilnorChainGroup C p m n) :
    openChainExtend C p V m n (openChainComap C p V m n a) =
      a - closedChainExtend C p i m n (closedChainComap C p i m n a) :=
  eq_sub_of_add_eq' (closedChainExtend_add_openChainExtend C p i V hcomp m n a)

end Complementary

/-! ### The four squares, in applied form -/

/-- The divisor differential of Stacks 0GU3 commutes with extension by zero from the closed
subscheme. -/
theorem pointwiseDivisorDifferential_closedChainExtend (k : ℤ)
    (b : PointwiseKOneGroup C (i ≫ p) k) :
    pointwiseDivisorDifferential C p k (closedChainExtend C p i (k + 1) 1 b) =
      closedChainExtend C p i k 0 (pointwiseDivisorDifferential C (i ≫ p) k b) :=
  DFunLike.congr_fun (pointwiseDivisorDifferential_milnorChainExtend C p i k) b

/-- The divisor differential of Stacks 0GU3 commutes with restriction to the open subscheme. -/
theorem pointwiseDivisorDifferential_openChainComap (k : ℤ) (a : PointwiseKOneGroup C p k) :
    pointwiseDivisorDifferential C (V.ι ≫ p) k (openChainComap C p V (k + 1) 1 a) =
      openChainComap C p V k 0 (pointwiseDivisorDifferential C p k a) :=
  DFunLike.congr_fun (milnorChainComap_pointwiseDivisorDifferential C p V.ι k) a

/-- The tame-symbol differential of Stacks 0GU9 commutes with extension by zero from the closed
subscheme. -/
theorem pointwiseMilnorBoundary_closedChainExtend (k : ℤ)
    (ξ : PointwiseKTwoGroup C (i ≫ p) k) :
    pointwiseMilnorBoundary C p k (closedChainExtend C p i (k + 2) 2 ξ) =
      closedChainExtend C p i (k + 1) 1 (pointwiseMilnorBoundary C (i ≫ p) k ξ) :=
  DFunLike.congr_fun (pointwiseMilnorBoundary_milnorChainExtend C p i k) ξ

/-- The tame-symbol differential of Stacks 0GU9 commutes with restriction to the open
subscheme. -/
theorem pointwiseMilnorBoundary_openChainComap (k : ℤ) (ξ : PointwiseKTwoGroup C p k) :
    pointwiseMilnorBoundary C (V.ι ≫ p) k (openChainComap C p V (k + 2) 2 ξ) =
      openChainComap C p V (k + 1) 1 (pointwiseMilnorBoundary C p k ξ) :=
  DFunLike.congr_fun (milnorChainComap_pointwiseMilnorBoundary C p V.ι k) ξ

/-! ### The two maps of first higher Chow groups -/

/-- Extension by zero from the closed subscheme carries Milnor K₁-cycles to Milnor K₁-cycles. -/
theorem closedChainExtend_mem_milnorChowCycleGroup (k : ℤ)
    (b : ↥(milnorChowCycleGroup C (i ≫ p) k)) :
    closedChainExtend C p i (k + 1) 1 b.1 ∈ milnorChowCycleGroup C p k := by
  rw [milnorChowCycleGroup, AddMonoidHom.mem_ker,
    pointwiseDivisorDifferential_closedChainExtend,
    AddMonoidHom.mem_ker.mp b.2, map_zero]

/-- Extension by zero from the closed subscheme, on Milnor K₁-cycles. -/
def closedCycleExtend (k : ℤ) :
    ↥(milnorChowCycleGroup C (i ≫ p) k) →+ ↥(milnorChowCycleGroup C p k) :=
  AddMonoidHom.codRestrict
    ((closedChainExtend C p i (k + 1) 1).comp (milnorChowCycleGroup C (i ≫ p) k).subtype) _
    (closedChainExtend_mem_milnorChowCycleGroup C p i k)

/-- The underlying chain of the extension by zero of a Milnor K₁-cycle is the extension by zero
of its underlying chain. -/
@[simp]
theorem closedCycleExtend_coe (k : ℤ) (b : ↥(milnorChowCycleGroup C (i ≫ p) k)) :
    (closedCycleExtend C p i k b).1 = closedChainExtend C p i (k + 1) 1 b.1 :=
  rfl

/-- **Extension by zero from the closed subscheme, on first higher Chow groups.** -/
def milnorChowGroupOneExtend (k : ℤ) :
    milnorChowGroupOne C (i ≫ p) k →+ milnorChowGroupOne C p k :=
  QuotientAddGroup.map (milnorChowBoundarySubgroup C (i ≫ p) k)
    (milnorChowBoundarySubgroup C p k) (closedCycleExtend C p i k) (by
      intro b hb
      obtain ⟨ξ, hξ⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_addSubgroupOf.mp hb)
      rw [AddSubgroup.mem_comap]
      refine AddSubgroup.mem_addSubgroupOf.mpr (AddMonoidHom.mem_range.mpr
        ⟨closedChainExtend C p i (k + 2) 2 ξ, ?_⟩)
      rw [pointwiseMilnorBoundary_closedChainExtend, hξ, closedCycleExtend_coe])

/-- Extension by zero on first higher Chow groups sends the class of a Milnor K₁-cycle to the
class of its extension by zero. -/
@[simp]
theorem milnorChowGroupOneExtend_mk (k : ℤ) (b : ↥(milnorChowCycleGroup C (i ≫ p) k)) :
    milnorChowGroupOneExtend C p i k (milnorChowClassOne C (i ≫ p) k b) =
      milnorChowClassOne C p k (closedCycleExtend C p i k b) :=
  rfl

/-- Restriction to the open subscheme carries Milnor K₁-cycles to Milnor K₁-cycles. -/
theorem openChainComap_mem_milnorChowCycleGroup (k : ℤ)
    (a : ↥(milnorChowCycleGroup C p k)) :
    openChainComap C p V (k + 1) 1 a.1 ∈ milnorChowCycleGroup C (V.ι ≫ p) k := by
  rw [milnorChowCycleGroup, AddMonoidHom.mem_ker, pointwiseDivisorDifferential_openChainComap,
    AddMonoidHom.mem_ker.mp a.2, map_zero]

/-- Restriction to the open subscheme, on Milnor K₁-cycles. -/
def openCycleComap (k : ℤ) :
    ↥(milnorChowCycleGroup C p k) →+ ↥(milnorChowCycleGroup C (V.ι ≫ p) k) :=
  AddMonoidHom.codRestrict
    ((openChainComap C p V (k + 1) 1).comp (milnorChowCycleGroup C p k).subtype) _
    (openChainComap_mem_milnorChowCycleGroup C p V k)

/-- The underlying chain of the restriction of a Milnor K₁-cycle is the restriction of its
underlying chain. -/
@[simp]
theorem openCycleComap_coe (k : ℤ) (a : ↥(milnorChowCycleGroup C p k)) :
    (openCycleComap C p V k a).1 = openChainComap C p V (k + 1) 1 a.1 :=
  rfl

/-- **Restriction to the open subscheme, on first higher Chow groups.** -/
def milnorChowGroupOneComap (k : ℤ) :
    milnorChowGroupOne C p k →+ milnorChowGroupOne C (V.ι ≫ p) k :=
  QuotientAddGroup.map (milnorChowBoundarySubgroup C p k)
    (milnorChowBoundarySubgroup C (V.ι ≫ p) k) (openCycleComap C p V k) (by
      intro a ha
      obtain ⟨ξ, hξ⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_addSubgroupOf.mp ha)
      rw [AddSubgroup.mem_comap]
      refine AddSubgroup.mem_addSubgroupOf.mpr (AddMonoidHom.mem_range.mpr
        ⟨openChainComap C p V (k + 2) 2 ξ, ?_⟩)
      rw [pointwiseMilnorBoundary_openChainComap, hξ, openCycleComap_coe])

/-- Restriction on first higher Chow groups sends the class of a Milnor K₁-cycle to the class
of its restriction. -/
@[simp]
theorem milnorChowGroupOneComap_mk (k : ℤ) (a : ↥(milnorChowCycleGroup C p k)) :
    milnorChowGroupOneComap C p V k (milnorChowClassOne C p k a) =
      milnorChowClassOne C (V.ι ≫ p) k (openCycleComap C p V k a) :=
  rfl

/-! ### The connecting map -/

/-- **The connecting map of the snake lemma, at the level of chains.** A Milnor K₁-chain on the
open subscheme is extended by zero to the ambient scheme, its divisor is taken there, and the
result is restricted to the closed subscheme. No choice is involved: the degreewise localization
sequence is split, so the lift is the section of the splitting. -/
def milnorChainPreBoundary (k : ℤ) :
    MilnorChainGroup C (V.ι ≫ p) (k + 1) 1 →+ PointwiseCycleGroup C (i ≫ p) k :=
  (closedChainComap C p i k 0).comp
    ((pointwiseDivisorDifferential C p k).comp (openChainExtend C p V (k + 1) 1))

/-- The chain-level connecting map is the restriction to the closed subscheme of the divisor, on
the ambient scheme, of the extension by zero. -/
@[simp]
theorem milnorChainPreBoundary_apply (k : ℤ) (a : MilnorChainGroup C (V.ι ≫ p) (k + 1) 1) :
    milnorChainPreBoundary C p i V k a =
      closedChainComap C p i k 0
        (pointwiseDivisorDifferential C p k (openChainExtend C p V (k + 1) 1 a)) :=
  rfl

section Complementary

variable (hcomp : Set.range i.base = (Set.range V.ι.base)ᶜ)

include hcomp

/-- **On a Milnor K₁-cycle the connecting map loses nothing.** The divisor on the ambient scheme
of the extension by zero of a cycle is supported on the closed subscheme, because its restriction
to the open subscheme is the divisor of the cycle, which vanishes. -/
theorem closedChainExtend_milnorChainPreBoundary (k : ℤ)
    (a : MilnorChainGroup C (V.ι ≫ p) (k + 1) 1)
    (ha : pointwiseDivisorDifferential C (V.ι ≫ p) k a = 0) :
    closedChainExtend C p i k 0 (milnorChainPreBoundary C p i V k a) =
      pointwiseDivisorDifferential C p k (openChainExtend C p V (k + 1) 1 a) := by
  refine closedChainExtend_closedChainComap_of_openChainComap_eq_zero C p i V hcomp k 0 ?_
  rw [AddMonoidHom.comp_apply, ← pointwiseDivisorDifferential_openChainComap,
    openChainComap_openChainExtend, ha]

/-- The connecting map applied to a restriction to the open subscheme: the restriction to the
closed subscheme of the divisor, minus the divisor of the restriction to the closed subscheme. -/
theorem milnorChainPreBoundary_openChainComap (k : ℤ) (v : PointwiseKOneGroup C p k) :
    milnorChainPreBoundary C p i V k (openChainComap C p V (k + 1) 1 v) =
      closedChainComap C p i k 0 (pointwiseDivisorDifferential C p k v) -
        pointwiseDivisorDifferential C (i ≫ p) k (closedChainComap C p i (k + 1) 1 v) := by
  rw [milnorChainPreBoundary_apply,
    openChainExtend_openChainComap_eq_sub C p i V hcomp (k + 1) 1 v, map_sub, map_sub,
    pointwiseDivisorDifferential_closedChainExtend, closedChainComap_closedChainExtend]

/-- Correcting a chain `a` by the boundary of the extension by zero of a witness `ξ` that `a`
restricts to a boundary on the open subscheme leaves a chain supported on the closed subscheme,
whose divisor there, pushed forward, is the divisor of `a`. -/
private theorem closedChainExtend_divisor_closedChainComap_sub_boundary (k : ℤ)
    (a : MilnorChainGroup C p (k + 1) 1) (ξ : PointwiseKTwoGroup C (V.ι ≫ p) k)
    (h : pointwiseMilnorBoundary C (V.ι ≫ p) k ξ = openChainComap C p V (k + 1) 1 a) :
    closedChainExtend C p i k 0 (pointwiseDivisorDifferential C (i ≫ p) k
      (closedChainComap C p i (k + 1) 1
        (a - pointwiseMilnorBoundary C p k (openChainExtend C p V (k + 2) 2 ξ)))) =
      pointwiseDivisorDifferential C p k a := by
  have hr : openChainComap C p V (k + 1) 1
      (a - pointwiseMilnorBoundary C p k (openChainExtend C p V (k + 2) 2 ξ)) = 0 := by
    rw [map_sub, ← pointwiseMilnorBoundary_openChainComap, openChainComap_openChainExtend, h,
      sub_self]
  rw [← pointwiseDivisorDifferential_closedChainExtend,
    closedChainExtend_closedChainComap_of_openChainComap_eq_zero C p i V hcomp (k + 1) 1 hr,
    map_sub, pointwiseDivisorDifferential_pointwiseMilnorBoundary, sub_zero]

/-- **The connecting map kills the tame-symbol boundary, up to a rational equivalence.** The
extension by zero of a boundary differs from the boundary of the extension by zero by a chain
supported on the closed subscheme, whose divisor is therefore a rational equivalence there. -/
theorem pointwiseChowClass_milnorChainPreBoundary_pointwiseMilnorBoundary (k : ℤ)
    (ξ : PointwiseKTwoGroup C (V.ι ≫ p) k) :
    pointwiseChowClass C (i ≫ p) k
      (milnorChainPreBoundary C p i V k (pointwiseMilnorBoundary C (V.ι ≫ p) k ξ)) = 0 := by
  rw [milnorChainPreBoundary_apply,
    ← closedChainExtend_divisor_closedChainComap_sub_boundary C p i V hcomp k _ ξ
      (openChainComap_openChainExtend C p V (k + 1) 1 _).symm,
    closedChainComap_closedChainExtend]
  exact pointwiseChowClass_pointwiseDivisorDifferential C (i ≫ p) k _

/-- **The connecting map of the six-term exact sequence of Stacks 0GUA**,
`CH^M_k(V, 1) ⟶ CH_k(Y)`: the class in the Chow group of the closed subscheme of the divisor,
taken on the ambient scheme, of the extension by zero of a Milnor K₁-cycle on the open
subscheme. -/
def milnorChowBoundary (k : ℤ) :
    milnorChowGroupOne C (V.ι ≫ p) k →+ chowGroup C (i ≫ p) k :=
  QuotientAddGroup.lift (milnorChowBoundarySubgroup C (V.ι ≫ p) k)
    ((pointwiseChowClass C (i ≫ p) k).comp
      ((milnorChainPreBoundary C p i V k).comp
        (milnorChowCycleGroup C (V.ι ≫ p) k).subtype)) (by
      intro a ha
      obtain ⟨ξ, hξ⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_addSubgroupOf.mp ha)
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        AddSubgroup.coe_subtype, ← hξ]
      exact pointwiseChowClass_milnorChainPreBoundary_pointwiseMilnorBoundary C p i V hcomp k ξ)

/-- The connecting map sends the class of a Milnor K₁-cycle to the Chow class of its image under
the chain-level connecting map `milnorChainPreBoundary`. -/
@[simp]
theorem milnorChowBoundary_mk (k : ℤ) (a : ↥(milnorChowCycleGroup C (V.ι ≫ p) k)) :
    milnorChowBoundary C p i V hcomp k (milnorChowClassOne C (V.ι ≫ p) k a) =
      pointwiseChowClass C (i ≫ p) k (milnorChainPreBoundary C p i V k a.1) :=
  rfl

/-! ### The three new exactness assertions -/

/-- **Exactness at the first higher Chow group of the ambient scheme.** A Milnor K₁-cycle on `X`
restricting to a tame-symbol boundary on `V` differs from an extension by zero from `Y` by a
tame-symbol boundary on `X`: correct the cycle by the boundary of the extension by zero of the
witness, and what remains restricts to zero on `V`, hence is supported on `Y`. -/
theorem exact_milnorChowGroupOneExtend_milnorChowGroupOneComap (k : ℤ) :
    Function.Exact (milnorChowGroupOneExtend C p i k) (milnorChowGroupOneComap C p V k) := by
  intro γ
  constructor
  · intro h0
    obtain ⟨a, rfl⟩ := milnorChowClassOne_surjective C p k γ
    rw [milnorChowGroupOneComap_mk, milnorChowClassOne_eq_zero_iff] at h0
    obtain ⟨ξ, hξ⟩ := h0
    obtain ⟨w, hw⟩ : ∃ w, w = (a : PointwiseKOneGroup C p k) -
        pointwiseMilnorBoundary C p k (openChainExtend C p V (k + 2) 2 ξ) := ⟨_, rfl⟩
    have hrw : openChainComap C p V (k + 1) 1 w = 0 := by
      rw [hw, map_sub,
        ← pointwiseMilnorBoundary_openChainComap C p V k (openChainExtend C p V (k + 2) 2 ξ),
        openChainComap_openChainExtend C p V (k + 2) 2 ξ, hξ, openCycleComap_coe C p V k a,
        sub_self]
    have hwe : closedChainExtend C p i (k + 1) 1 (closedChainComap C p i (k + 1) 1 w) = w :=
      closedChainExtend_closedChainComap_of_openChainComap_eq_zero C p i V hcomp (k + 1) 1 hrw
    have hb : closedChainComap C p i (k + 1) 1 w ∈ milnorChowCycleGroup C (i ≫ p) k := by
      rw [milnorChowCycleGroup, AddMonoidHom.mem_ker]
      refine closedChainExtend_injective C p i k 0 ?_
      rw [hw, closedChainExtend_divisor_closedChainComap_sub_boundary C p i V hcomp k _ ξ
          (by rw [hξ, openCycleComap_coe]),
        AddMonoidHom.mem_ker.mp a.2, map_zero]
    refine ⟨milnorChowClassOne C (i ≫ p) k ⟨_, hb⟩, ?_⟩
    rw [milnorChowGroupOneExtend_mk, ← sub_eq_zero, ← map_sub, milnorChowClassOne_eq_zero_iff]
    refine ⟨-openChainExtend C p V (k + 2) 2 ξ, ?_⟩
    rw [map_neg, AddSubgroup.coe_sub, closedCycleExtend_coe C p i k ⟨_, hb⟩, hwe, hw]
    abel
  · rintro ⟨β, hβ⟩
    rw [← hβ]
    obtain ⟨b, rfl⟩ := milnorChowClassOne_surjective C (i ≫ p) k β
    rw [milnorChowGroupOneExtend_mk, milnorChowGroupOneComap_mk, milnorChowClassOne_eq_zero_iff]
    refine ⟨0, ?_⟩
    rw [map_zero, openCycleComap_coe C p V k (closedCycleExtend C p i k b),
      closedCycleExtend_coe C p i k b,
      openChainComap_closedChainExtend C p i V hcomp (k + 1) 1 b.1]

/-- **Exactness at the first higher Chow group of the open subscheme.** If the connecting map
kills a Milnor K₁-cycle on `V`, correct the extension by zero of that cycle by the extension by
zero from `Y` of the witnessing K₁-chain: the result is a Milnor K₁-cycle on `X` restricting to
the given one. Conversely the connecting map applied to a restriction is the divisor of a chain
on `Y`, hence a rational equivalence there. -/
theorem exact_milnorChowGroupOneComap_milnorChowBoundary (k : ℤ) :
    Function.Exact (milnorChowGroupOneComap C p V k) (milnorChowBoundary C p i V hcomp k) := by
  intro γ
  constructor
  · intro h0
    obtain ⟨a, rfl⟩ := milnorChowClassOne_surjective C (V.ι ≫ p) k γ
    rw [milnorChowBoundary_mk, pointwiseChowClass_eq_zero_iff] at h0
    obtain ⟨c, hc⟩ := h0
    obtain ⟨t, ht⟩ : ∃ t, t = openChainExtend C p V (k + 1) 1 a.1 -
        closedChainExtend C p i (k + 1) 1 c := ⟨_, rfl⟩
    have hrt : openChainComap C p V (k + 1) 1 t = a.1 := by
      rw [ht, map_sub, openChainComap_openChainExtend C p V (k + 1) 1 a.1,
        openChainComap_closedChainExtend C p i V hcomp (k + 1) 1 c, sub_zero]
    have hdt : pointwiseDivisorDifferential C p k t = 0 := by
      rw [ht, map_sub, pointwiseDivisorDifferential_closedChainExtend C p i k c, hc,
        closedChainExtend_milnorChainPreBoundary C p i V hcomp k a.1
          (AddMonoidHom.mem_ker.mp a.2), sub_self]
    refine ⟨milnorChowClassOne C p k ⟨t, AddMonoidHom.mem_ker.mpr hdt⟩, ?_⟩
    rw [milnorChowGroupOneComap_mk]
    exact congrArg (milnorChowClassOne C (V.ι ≫ p) k) (Subtype.ext hrt)
  · rintro ⟨β, hβ⟩
    rw [← hβ]
    obtain ⟨w, rfl⟩ := milnorChowClassOne_surjective C p k β
    rw [milnorChowGroupOneComap_mk, milnorChowBoundary_mk, openCycleComap_coe C p V k w]
    have hval : milnorChainPreBoundary C p i V k (openChainComap C p V (k + 1) 1 w.1) =
        -pointwiseDivisorDifferential C (i ≫ p) k (closedChainComap C p i (k + 1) 1 w.1) := by
      rw [milnorChainPreBoundary_openChainComap C p i V hcomp k w.1,
        AddMonoidHom.mem_ker.mp w.2, map_zero, zero_sub]
    rw [hval, map_neg, pointwiseChowClass_pointwiseDivisorDifferential, neg_zero]

/-- **Exactness at the Chow group of the closed subscheme.** A cycle class on `Y` dying in the
Chow group of `X` is the connecting map of the restriction to `V` of the witnessing K₁-chain on
`X`; conversely the extension by zero of the connecting map of a cycle is the divisor of a chain
on `X`, hence a rational equivalence there. -/
theorem exact_milnorChowBoundary_chowPushforward (k : ℤ) :
    Function.Exact (milnorChowBoundary C p i V hcomp k)
      (chowPushforwardOfIsClosedImmersion C (i ≫ p) p i rfl k) := by
  intro γ
  constructor
  · intro h0
    obtain ⟨c, rfl⟩ := pointwiseChowClass_surjective C (i ≫ p) k γ
    rw [← pointwiseChowClass_milnorChainExtend C p i k c, pointwiseChowClass_eq_zero_iff] at h0
    obtain ⟨v, hv⟩ := h0
    obtain ⟨a, ha⟩ : ∃ a, a = openChainComap C p V (k + 1) 1 v := ⟨_, rfl⟩
    have hda : pointwiseDivisorDifferential C (V.ι ≫ p) k a = 0 := by
      rw [ha, pointwiseDivisorDifferential_openChainComap C p V k v, hv,
        openChainComap_closedChainExtend C p i V hcomp k 0 c]
    refine ⟨milnorChowClassOne C (V.ι ≫ p) k ⟨a, AddMonoidHom.mem_ker.mpr hda⟩, ?_⟩
    rw [milnorChowBoundary_mk]
    have hδ : milnorChainPreBoundary C p i V k a =
        c - pointwiseDivisorDifferential C (i ≫ p) k (closedChainComap C p i (k + 1) 1 v) := by
      rw [ha, milnorChainPreBoundary_openChainComap C p i V hcomp k v, hv,
        closedChainComap_closedChainExtend]
    rw [hδ, map_sub, pointwiseChowClass_pointwiseDivisorDifferential, sub_zero]
  · rintro ⟨α, hα⟩
    rw [← hα]
    obtain ⟨a, rfl⟩ := milnorChowClassOne_surjective C (V.ι ≫ p) k α
    rw [milnorChowBoundary_mk, ← pointwiseChowClass_milnorChainExtend C p i k,
      closedChainExtend_milnorChainPreBoundary C p i V hcomp k a.1
        (AddMonoidHom.mem_ker.mp a.2),
      pointwiseChowClass_pointwiseDivisorDifferential]

/-! ### The six-term exact sequence -/

/-- **Stacks 0GUA.** The six-term exact sequence

`CH^M_k(Y, 1) ⟶ CH^M_k(X, 1) ⟶ CH^M_k(V, 1) ⟶ CH_k(Y) ⟶ CH_k(X) ⟶ CH_k(V) ⟶ 0`

attached to an open subscheme `V` of `X` and a closed immersion `i : Y ⟶ X` with complementary
image. The first three maps are those induced by the extension-by-zero and restriction maps of
the degreewise localization sequence of the tag, together with the connecting map
`Stacks.Chow.milnorChowBoundary`; the last two are the proper pushforward and the restriction to
an open subscheme of Stacks 02RX, whose exactness and surjectivity are
`Stacks.Chow.exact_chowPushforward_chowGroupOpensRestrict` and
`Stacks.Chow.surjective_chowGroupOpensRestrictOfIsOpenImmersion`. -/
@[stacks 0GUA "the six-term exact sequence of the tag, the main claim of the remark: for an open \
subscheme V of a scheme X locally of finite type over a Chow situation and a closed immersion i \
of Y into X whose image is the complement of V, the sequence of the first higher Chow groups of \
Y, X and V, followed by the Chow groups of Y, X and V and ending in zero, is exact. The first \
two maps are induced on the first higher Chow groups of Stacks 0GU9 by the extension-by-zero and \
restriction maps of the degreewise localization sequence of the tag; the third is the connecting \
map of the snake lemma, formed from the splitting of that sequence; the last two are the proper \
pushforward along the closed immersion and the restriction to the open subscheme of \
Stacks 02RX"]
theorem milnorChowLocalization_exact (k : ℤ) :
    Function.Exact (milnorChowGroupOneExtend C p i k) (milnorChowGroupOneComap C p V k) ∧
      Function.Exact (milnorChowGroupOneComap C p V k) (milnorChowBoundary C p i V hcomp k) ∧
      Function.Exact (milnorChowBoundary C p i V hcomp k)
        (chowPushforwardOfIsClosedImmersion C (i ≫ p) p i rfl k) ∧
      Function.Exact (chowPushforwardOfIsClosedImmersion C (i ≫ p) p i rfl k)
        (chowGroupOpensRestrictOfIsOpenImmersion C p V k) ∧
      Function.Surjective (chowGroupOpensRestrictOfIsOpenImmersion C p V k) :=
  ⟨exact_milnorChowGroupOneExtend_milnorChowGroupOneComap C p i V hcomp k,
    exact_milnorChowGroupOneComap_milnorChowBoundary C p i V hcomp k,
    exact_milnorChowBoundary_chowPushforward C p i V hcomp k,
    exact_chowPushforward_chowGroupOpensRestrict C p (i ≫ p) i rfl V hcomp k,
    surjective_chowGroupOpensRestrictOfIsOpenImmersion C p V k⟩

end Complementary

end Stacks.Chow

end

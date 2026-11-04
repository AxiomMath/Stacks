module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Length
public import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.WeilDivisors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cycle associated to a closed subscheme

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 and let
`i : Z ⟶ X` be a closed immersion. Each irreducible component of `Z` carries a multiplicity: at
its generic point `ξ` the stalk `𝒪_{Z,ξ}` is a module over `𝒪_{X,i ξ}` of finite length, and
that length is `m_{Z,ξ}`. The cycle associated to `Z` in dimension `k` is
`[Z]_k = ∑ m_{Z,ξ} [closure {i ξ}]`, the sum running over those components whose image has
delta-dimension `k`.

Local finiteness of this family of coefficients is exactly Stacks 0BE1: on a locally Noetherian
scheme the images of the irreducible components of a closed subscheme form a locally finite
family, and the generic points of the components inject into the components
(`TopologicalSpace.genericPoints.component_injective`), so the coefficient function has locally
finite support.

Stacks 02QU bounds the delta-dimension of `Z` by `k`; that bound is not needed to construct the
cycle, and the construction below is given for every `k`, so the bounded case is a special case.

## Main definitions

* `Stacks.Chow.componentMultiplicity` — the multiplicity `m_{Z,ξ}` of an irreducible component
  of a closed subscheme (Stacks 02QU, part (1)).
* `Stacks.Chow.closedSubschemeCycleCoeff`, `Stacks.Chow.closedSubschemeCycle` — the coefficient
  function and the locally finite cycle it defines.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme` — the `k`-cycle `[Z]_k` (Stacks 02QU,
  part (2)).

## Main results

* `Stacks.Chow.closedSubschemeCycleCoeff_locallyFiniteSupport` — the coefficient function has
  locally finite support.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply` — at the image of the generic point of a
  component of delta-dimension `k`, the coefficient of `[Z]_k` is that component's
  multiplicity.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero` — every other coefficient
  vanishes.

## Implementation notes

A closed subscheme is represented by a closed immersion `i : Z ⟶ X`, and the generic points of
its irreducible components by Mathlib's `TopologicalSpace.genericPoints Z`. The module structure
making `𝒪_{Z,ξ}` an `𝒪_{X,i ξ}`-module is restriction of scalars along the stalk map of `i`.
`Module.length` is `ℕ∞`-valued, and `ENat.toNat` lands the multiplicity in `ℤ`; on a component
of a closed subscheme of a locally Noetherian scheme the length is finite, so no information is
lost.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0BE1](https://stacks.math.columbia.edu/tag/0BE1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 02QU.** The multiplicity of an irreducible component of a closed subscheme,
computed at its generic point as the length of the stalk of the subscheme over the stalk of the
ambient scheme. -/
@[stacks 02QU "part (1): multiplicity"]
def componentMultiplicity {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (ξ : genericPoints Z) : ℤ :=
  letI : Module (X.presheaf.stalk (i ξ.1)) (Z.presheaf.stalk ξ.1) :=
    Module.compHom (Z.presheaf.stalk ξ.1) (i.stalkMap ξ.1).hom
  (Module.length (X.presheaf.stalk (i ξ.1)) (Z.presheaf.stalk ξ.1)).toNat

/-- The coefficient function of the cycle associated to a closed subscheme, before bundling its
locally finite support: the multiplicity of a component of delta-dimension `k` at the image of
its generic point, and zero elsewhere. -/
def closedSubschemeCycleCoeff (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ) (x : X) : ℤ :=
  open Classical in
  if h : ∃ ξ : genericPoints Z,
      i ξ.1 = x ∧ relativeDimension C.dimensionFunction f x = k then
    componentMultiplicity i (Classical.choose h)
  else 0

/-- A nonzero coefficient is witnessed by a generic point of the right delta-dimension. -/
private theorem exists_generic_point_of_closedSubschemeCycleCoeff_ne_zero (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) {x : X} (h : closedSubschemeCycleCoeff C f i k x ≠ 0) :
    ∃ ξ : genericPoints Z, i ξ.1 = x ∧ relativeDimension C.dimensionFunction f x = k :=
  not_not.1 fun hx ↦ h (by simp [closedSubschemeCycleCoeff, hx])

/-- The coefficient function of a closed subscheme is locally finitely supported: this is the
local finiteness of the images of the irreducible components, Stacks 0BE1, transported along the
injection of generic points into components. -/
theorem closedSubschemeCycleCoeff_locallyFiniteSupport (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) :
    LocallyFiniteSupport (closedSubschemeCycleCoeff C f i k) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro x
  obtain ⟨U, hU, hfin⟩ := (locallyFinite_irreducibleComponents_image i).comp_injective
    genericPoints.component_injective x
  refine ⟨U, hU, ?_⟩
  apply (hfin.image fun ξ : genericPoints Z => i ξ.1).subset
  intro y ⟨hyU, hyne⟩
  obtain ⟨ξ, hξ, -⟩ := exists_generic_point_of_closedSubschemeCycleCoeff_ne_zero C f i k hyne
  exact ⟨_, ⟨y, ⟨_, subset_closure (by simp), hξ⟩, hyU⟩, hξ⟩

/-- The cycle associated to a closed subscheme, before imposing its dimension condition. -/
def closedSubschemeCycle (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ) :
    AlgebraicCycle X ℤ where
  toFun := closedSubschemeCycleCoeff C f i k
  supportWithinDomain' := by intro x _; trivial
  supportLocallyFiniteWithinDomain' x _ := closedSubschemeCycleCoeff_locallyFiniteSupport C f i k x

/-- The cycle associated to a closed subscheme has delta-dimension `k`. -/
theorem closedSubschemeCycle_mem_cyclesOfDimension (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ) :
    closedSubschemeCycle C f i k ∈ cyclesOfDimension C f k := by
  rw [mem_cyclesOfDimension]
  intro Z' hne
  exact (exists_generic_point_of_closedSubschemeCycleCoeff_ne_zero C f i k hne).choose_spec.2

/-- **Stacks 02QU.** The `k`-cycle `[Z]_k` associated to a closed subscheme `i : Z ⟶ X`: the
coefficient of each irreducible component of delta-dimension `k` is its multiplicity. -/
@[stacks 02QU "part (2): associated cycle"]
def cycleAssociatedToClosedSubscheme (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ) : CycleGroup C f k :=
  ⟨closedSubschemeCycle C f i k, closedSubschemeCycle_mem_cyclesOfDimension C f i k⟩

/-- **Stacks 02QU.** At the image of the generic point of a component of delta-dimension `k`,
the associated cycle has that component's multiplicity as coefficient. -/
@[stacks 02QU "coefficient formula"]
theorem cycleAssociatedToClosedSubscheme_apply (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (ξ : genericPoints Z)
    (hξ : relativeDimension C.dimensionFunction f (i ξ.1) = k) :
    (cycleAssociatedToClosedSubscheme C f i k).1 (i ξ.1) = componentMultiplicity i ξ := by
  classical
  show closedSubschemeCycleCoeff C f i k (i ξ.1) = componentMultiplicity i ξ
  unfold closedSubschemeCycleCoeff
  have hExists : ∃ η : genericPoints Z,
      i η.1 = i ξ.1 ∧ relativeDimension C.dimensionFunction f (i ξ.1) = k := ⟨ξ, rfl, hξ⟩
  rw [dite_eq_left hExists]
  congr 1
  exact Subtype.ext (i.isClosedEmbedding.injective (Classical.choose_spec hExists).1)

/-- **Stacks 02QU.** A point that is not the image of the generic point of a component of
delta-dimension `k` has coefficient zero in the associated cycle. -/
@[stacks 02QU "zero coefficients"]
theorem cycleAssociatedToClosedSubscheme_apply_eq_zero (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) (x : X)
    (hx : ¬ ∃ ξ : genericPoints Z,
      i ξ.1 = x ∧ relativeDimension C.dimensionFunction f x = k) :
    (cycleAssociatedToClosedSubscheme C f i k).1 x = 0 := by
  simp [cycleAssociatedToClosedSubscheme, closedSubschemeCycle, closedSubschemeCycleCoeff, hx]


/-! ### Rational equivalence -/

/-- The principal divisor of the inverse of a nonzero rational function is the negative of its
principal divisor. -/
theorem principalCycle_inv (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {f : X.functionField} (hf : f ≠ 0) :
    principalCycle X f⁻¹ = -principalCycle X f := by
  have hone : ∀ z : X, X.ord (1 : X.functionField) z = 0 := by
    intro z
    have h := X.ord_mul (x := z) (one_ne_zero (α := X.functionField))
      (one_ne_zero (α := X.functionField))
    rw [one_mul] at h
    omega
  apply Function.locallyFinsuppWithin.ext
  intro z
  have h := X.ord_mul (x := z) (inv_ne_zero hf) hf
  rw [inv_mul_cancel₀ hf, hone z] at h
  show X.ord f⁻¹ z = -X.ord f z
  omega

/-- The cycle on `X` obtained by pushing forward, along an integral closed subscheme `V ⊆ X`,
the principal divisor of a nonzero rational function on `V`. -/
def principalDivisorPushforward (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g : (rationalFunctions V.subscheme)ˣ) : AlgebraicCycle X ℤ :=
  haveI : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  AlgebraicCycle.map V.subschemeι
    (relativeDimension C.dimensionFunction (V.subschemeι ≫ p))
    (relativeDimension C.dimensionFunction p)
    (principalCycle V.subscheme
      ((rationalFunctionsEquivFunctionField V.subscheme).1 (g : rationalFunctions V.subscheme)))

/-- `AlgebraicCycle.map`, the weighted pushforward of cycles, respects negation. -/
theorem algebraicCycle_map_neg {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (wx : X → ℤ) (wy : Y → ℤ) (c : AlgebraicCycle X ℤ) :
    AlgebraicCycle.map f wx wy (-c) = -AlgebraicCycle.map f wx wy c := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  show (AlgebraicCycle.map f wx wy (-c)) y = -((AlgebraicCycle.map f wx wy c) y)
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply]
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_set_coe_eq_finsum_mem, ← finsum_neg_distrib]
  exact finsum_congr fun z ↦ by simp [neg_mul]

/-- The principal divisor of the inverse of a nonzero rational function on a closed subscheme
pushes forward to the negative of the pushforward of its principal divisor. -/
theorem principalDivisorPushforward_inv (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g : (rationalFunctions V.subscheme)ˣ) :
    principalDivisorPushforward C p V hV g⁻¹ = -principalDivisorPushforward C p V hV g := by
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  set e := (rationalFunctionsEquivFunctionField V.subscheme).1 with he
  have hg : e (g : rationalFunctions V.subscheme) ≠ 0 := fun h ↦
    g.ne_zero (e.injective (h.trans (map_zero e).symm))
  have hinv : e ((g⁻¹ : (rationalFunctions V.subscheme)ˣ) : rationalFunctions V.subscheme) =
      (e (g : rationalFunctions V.subscheme))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    simp
  show AlgebraicCycle.map _ _ _ (principalCycle V.subscheme (e _)) = _
  rw [hinv, principalCycle_inv V.subscheme hg, algebraicCycle_map_neg]
  rfl

/-! ### Locally finite families of principal divisors -/

/-- The pushforward of the principal divisor of a rational function on a closed subscheme is
supported on that closed subscheme. -/
theorem support_principalDivisorPushforward_subset (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g : (rationalFunctions V.subscheme)ˣ) :
    Function.support (principalDivisorPushforward C p V hV g) ⊆ (V.support : Set X) := by
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  exact Function.locallyFinsupp.support_map_subset_of_forall_mem V.subschemeι.isSpectralMap
    (fun z ↦ (AlgebraicCycle.mapCoeff V.subschemeι
      (relativeDimension C.dimensionFunction (V.subschemeι ≫ p))
      (relativeDimension C.dimensionFunction p) z : ℤ)) _ Set.univ (V.support : Set X)
    (by simp) (by
      intro z _ _
      rw [← V.range_subschemeι]
      exact ⟨z, rfl⟩)

/-- At a single point, only finitely many members of a locally finite family of supports
contribute. -/
theorem finite_support_of_locallyFinite {ι : Type*} {Z : Type*} [TopologicalSpace Z]
    (E : ι → Set Z) (hE : LocallyFinite E) (c : ι → Z → ℤ)
    (hsub : ∀ i, Function.support (c i) ⊆ E i) (z : Z) :
    (Function.support fun i ↦ c i z).Finite := by
  obtain ⟨U, hU, hK⟩ := hE z
  refine hK.subset fun i hi ↦ ⟨z, hsub i ?_, mem_of_mem_nhds hU⟩
  simpa [Function.mem_support] using hi

/-- A sum over a disjoint union splits as the sum of the two partial sums. -/
theorem finsum_sum_elim {ι κ : Type*} {M : Type*} [AddCommMonoid M] (f : ι → M) (g : κ → M)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    (∑ᶠ s : ι ⊕ κ, Sum.elim f g s) = (∑ᶠ i, f i) + (∑ᶠ j, g j) := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := hf.toFinset.disjSum hg.toFinset)
      (by rintro (i | j) hz <;> simpa using hz),
    Finset.sum_disjSum, finsum_eq_sum f hf, finsum_eq_sum g hg]
  rfl

/-- The disjoint union of two locally finite families is locally finite. -/
theorem locallyFinite_sum_elim {ι κ : Type*} {Z : Type*} [TopologicalSpace Z]
    (E : ι → Set Z) (F : κ → Set Z) (hE : LocallyFinite E) (hF : LocallyFinite F) :
    LocallyFinite (Sum.elim E F) := by
  intro x
  obtain ⟨U, hU, hEU⟩ := hE x
  obtain ⟨V, hV, hFV⟩ := hF x
  refine ⟨U ∩ V, Filter.inter_mem hU hV,
    ((hEU.image Sum.inl).union (hFV.image Sum.inr)).subset ?_⟩
  rintro (i | j) ⟨y, hy, hyU, hyV⟩
  · exact Or.inl ⟨i, ⟨y, hy, hyU⟩, rfl⟩
  · exact Or.inr ⟨j, ⟨y, hy, hyV⟩, rfl⟩

/-- The coefficient at `x` of the sum of the principal divisors of a family of nonzero rational
functions on a family of integral closed subschemes. -/
def principalDivisorFamilyCoefficient (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : X) : ℤ :=
  ∑ᶠ j : J, principalDivisorPushforward C p (W j) (hW j) (g j) x

/-- The coefficient function of a disjoint union of two locally finite families is the sum of
the two coefficient functions. -/
theorem principalDivisorFamilyCoefficient_sum (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {J K : Type u}
    (W : J → X.IdealSheafData) (V : K → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme) (hV : ∀ l, IsIntegral (V l).subscheme)
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ)
    (h : ∀ l, (rationalFunctions (V l).subscheme)ˣ)
    (hLocalW : LocallyFinite fun j ↦ ((W j).support : Set X))
    (hLocalV : LocallyFinite fun l ↦ ((V l).support : Set X)) (x : X) :
    principalDivisorFamilyCoefficient C p (Sum.elim W V)
      (fun s ↦ match s with | .inl j => hW j | .inr l => hV l)
      (fun s ↦ match s with | .inl j => g j | .inr l => h l) x =
      principalDivisorFamilyCoefficient C p W hW g x +
        principalDivisorFamilyCoefficient C p V hV h x := by
  have hfin : ∀ {ι : Type u} (W : ι → X.IdealSheafData) (hW : ∀ i, IsIntegral (W i).subscheme)
      (g : ∀ i, (rationalFunctions (W i).subscheme)ˣ),
      LocallyFinite (fun i ↦ ((W i).support : Set X)) →
      (Function.support fun i ↦ principalDivisorPushforward C p (W i) (hW i) (g i) x).Finite :=
    fun W hW g hL ↦ finite_support_of_locallyFinite _ hL _
      (fun i ↦ support_principalDivisorPushforward_subset C p (W i) (hW i) (g i)) x
  show (∑ᶠ s : J ⊕ K, _) = _
  rw [show (fun s : J ⊕ K ↦ principalDivisorPushforward C p (Sum.elim W V s)
        (match s with | .inl j => hW j | .inr l => hV l)
        (match s with | .inl j => g j | .inr l => h l) x) =
      Sum.elim (fun j ↦ principalDivisorPushforward C p (W j) (hW j) (g j) x)
        (fun l ↦ principalDivisorPushforward C p (V l) (hV l) (h l) x) from
      funext fun s ↦ by cases s <;> rfl]
  exact finsum_sum_elim _ _ (hfin W hW g hLocalW) (hfin V hV h hLocalV)

/-! ### Rational equivalence and the Chow group -/

/-- **Stacks 02RW.** A `k`-cycle is rationally equivalent to zero when its coefficients are the
locally finite sum of the pushforwards of the principal divisors of nonzero rational functions
on a locally finite family of integral closed subschemes of delta-dimension `k + 1`. -/
@[stacks 02RW "rationally equivalent to zero"]
def IsRationallyEquivalentToZero (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (α : CycleGroup C p k) : Prop :=
  ∃ (J : Type u) (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (_ : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
    (LocallyFinite fun j ↦ ((W j).support : Set X)) ∧
      ∃ g : ∀ j, (rationalFunctions (W j).subscheme)ˣ,
        ∀ x : X, α.1 x = principalDivisorFamilyCoefficient C p W hW g x

/-- A cycle is rationally equivalent to zero exactly when it is the locally finite sum of
pushforwards of principal divisors of rational functions on integral closed subschemes. -/
theorem isRationallyEquivalentToZero_iff (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (α : CycleGroup C p k) :
    IsRationallyEquivalentToZero C p k α ↔
      ∃ (J : Type u) (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
        (_ : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
        (LocallyFinite fun j ↦ ((W j).support : Set X)) ∧
          ∃ g : ∀ j, (rationalFunctions (W j).subscheme)ˣ,
            ∀ x : X, α.1 x = principalDivisorFamilyCoefficient C p W hW g x :=
  Iff.rfl

/-- **Stacks 02RW.** The zero cycle is rationally equivalent to zero, via the empty family. -/
@[stacks 02RW "zero family"]
theorem rationallyEquivalentToZero_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) :
    IsRationallyEquivalentToZero C p k 0 := by
  refine ⟨PEmpty.{u + 1}, (fun j ↦ nomatch j), (fun j ↦ nomatch j), (fun j ↦ nomatch j),
    fun _ ↦ ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩, (fun j ↦ nomatch j), fun x ↦ ?_⟩
  show (0 : AlgebraicCycle X ℤ) x = _
  simp [principalDivisorFamilyCoefficient, finsum_of_isEmpty]

/-- **Stacks 02RW.** The sum of two cycles rationally equivalent to zero is rationally
equivalent to zero, via the disjoint union of the two families. -/
@[stacks 02RW "closure under addition"]
theorem rationallyEquivalentToZero_add (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α β : CycleGroup C p k}
    (hα : IsRationallyEquivalentToZero C p k α)
    (hβ : IsRationallyEquivalentToZero C p k β) :
    IsRationallyEquivalentToZero C p k (α + β) := by
  obtain ⟨J, W, hW, hDimW, hLocalW, g, hg⟩ := hα
  obtain ⟨K, V, hV, hDimV, hLocalV, h, hh⟩ := hβ
  refine ⟨J ⊕ K, Sum.elim W V,
    (fun s ↦ match s with | .inl j => hW j | .inr l => hV l),
    (fun s ↦ match s with | .inl j => hDimW j | .inr l => hDimV l), ?_,
    (fun s ↦ match s with | .inl j => g j | .inr l => h l), fun x ↦ ?_⟩
  · have hsets : (fun s : J ⊕ K ↦ ((Sum.elim W V s).support : Set X)) =
        Sum.elim (fun j ↦ ((W j).support : Set X)) (fun l ↦ ((V l).support : Set X)) :=
      funext fun s ↦ by cases s <;> rfl
    rw [hsets]
    exact locallyFinite_sum_elim _ _ hLocalW hLocalV
  · show α.1 x + β.1 x = _
    rw [hg x, hh x]
    exact (principalDivisorFamilyCoefficient_sum C p W V hW hV g h hLocalW hLocalV x).symm

/-- **Stacks 02RW.** The negative of a cycle rationally equivalent to zero is rationally
equivalent to zero, via the inverses of the same rational functions. -/
@[stacks 02RW "closure under negation"]
theorem rationallyEquivalentToZero_neg (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α : CycleGroup C p k}
    (hα : IsRationallyEquivalentToZero C p k α) :
    IsRationallyEquivalentToZero C p k (-α) := by
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  refine ⟨J, W, hW, hDim, hLocal, fun j ↦ (g j)⁻¹, fun x ↦ ?_⟩
  show -α.1 x = principalDivisorFamilyCoefficient C p W hW (fun j ↦ (g j)⁻¹) x
  rw [hg x]
  unfold principalDivisorFamilyCoefficient
  rw [← finsum_neg_distrib]
  refine finsum_congr fun j ↦ ?_
  rw [principalDivisorPushforward_inv]
  rfl

/-- **Stacks 02RW.** The subgroup of `k`-cycles rationally equivalent to zero. -/
@[stacks 02RW "cycles rationally equivalent to zero"]
def rationalEquivalences (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) : AddSubgroup (CycleGroup C p k) where
  carrier := IsRationallyEquivalentToZero C p k
  zero_mem' := rationallyEquivalentToZero_zero C p k
  add_mem' := rationallyEquivalentToZero_add C p k
  neg_mem' := rationallyEquivalentToZero_neg C p k

/-- Membership in the subgroup of cycles rationally equivalent to zero. -/
@[simp]
theorem mem_rationalEquivalences (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (α : CycleGroup C p k) :
    α ∈ rationalEquivalences C p k ↔ IsRationallyEquivalentToZero C p k α :=
  Iff.rfl

/-- **Stacks 02RW.** Two `k`-cycles are rationally equivalent when their difference is a locally
finite sum of pushforwards of principal divisors. -/
@[stacks 02RW "rational equivalence"]
abbrev RationallyEquivalent (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (α β : CycleGroup C p k) : Prop :=
  α - β ∈ rationalEquivalences C p k

/-- **Stacks 02RW.** The Chow group `A_k(X)` of `k`-cycles modulo rational equivalence. -/
@[stacks 02RW "Chow group", sga "6 XIV 4.1" "partial"]
abbrev chowGroup (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) : Type u :=
  (CycleGroup C p k) ⧸ rationalEquivalences C p k

end Stacks.Chow

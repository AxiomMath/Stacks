module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# The cycle associated to a coherent sheaf

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `F` be a coherent `𝒪_X`-module. Each irreducible component `Z' ⊆ Supp(F)` carries
a multiplicity: at its generic point `ξ` the stalk `F_ξ` is an `𝒪_{X,ξ}`-module of finite length,
and that length is `m_{Z',F}`. The cycle associated to `F` in dimension `k` is
`[F]_k = ∑ m_{Z',F} [Z']`, the sum running over those components of delta-dimension `k`.

As in the source, `[F]_k` is formed only when the delta-dimension of the support does not exceed
`k`; that bound is what makes every point of the support contributing a nonzero coefficient the
generic point of a component, so that the coefficient family has locally finite support.

## Main definitions

* `Stacks.Chow.sheafMultiplicity` — the multiplicity `m_{Z',F}`, read at a point of `X` as the
  length of the stalk there (Stacks 02QX, part (1)).
* `Stacks.Chow.coherentSheafCycle` — the cycle `[F]_k`, before recording its delta-dimension.
* `Stacks.Chow.cycleAssociatedToCoherentSheaf` — the `k`-cycle `[F]_k` (Stacks 02QX, part (2)).

## Main results

* `Stacks.Chow.locallyFiniteSupport_sheafCycleCoeff` — the coefficient family has locally finite
  support.
* `Stacks.Chow.cycleAssociatedToCoherentSheaf_apply` — the coefficients of `[F]_k`.
* `Stacks.Chow.exists_cycleAssociatedToCoherentSheaf` — the coefficient formula does define a
  `k`-cycle (Stacks 02QX, part (2)).

## Implementation notes

The multiplicity is defined at every point of `X`, as the length of the stalk there; it is the
multiplicity of the source exactly at a generic point of a component of the support, where the
length is finite by `Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp`.
`Module.length` is `ℕ∞`-valued and `ENat.toNat` lands the multiplicity in `ℤ`, so no information
is lost at such a point.

Mathlib's `AlgebraicGeometry.AlgebraicCycle` indexes a prime cycle by the generic point of its
support, so the condition "the component has delta-dimension `k`" is recorded at a point `x` as
`Stacks.Chow.relativeDimension C.dimensionFunction f x = k`, the delta-dimension of `closure {x}`.
This is the same convention as `Stacks.Chow.closedSubschemeCycleCoeff`, the corresponding
coefficient function for a closed subscheme.

## References

* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **Stacks 02QX.** The length of the stalk of a sheaf of modules at a point, as an integer. At
a generic point of an irreducible component of the support of a coherent sheaf this length is
finite and is the multiplicity of that component in the sheaf. -/
@[stacks 02QX "part (1): multiplicity"]
def sheafMultiplicity (F : X.Modules) (x : X) : ℤ :=
  (Module.length (X.presheaf.stalk x) (F.presheaf.stalk x)).toNat

/-- Away from the support of a sheaf of modules its multiplicity vanishes: the stalk is zero, so
its length is zero. -/
theorem sheafMultiplicity_eq_zero_of_notMem_supp (F : X.Modules) {x : X}
    (hx : x ∉ SheafOfModules.supp F) : sheafMultiplicity F x = 0 := by
  have : Subsingleton (F.presheaf.stalk x) :=
    not_nontrivial_iff_subsingleton.mp fun hn ↦
      hx ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr hn)
  simp [sheafMultiplicity]

/-- The coefficient function of the cycle of a coherent sheaf: the multiplicity of the sheaf at a
point of the support whose closure has delta-dimension `k`, and zero elsewhere. -/
def sheafCycleCoeff (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsCoherent] (k : ℤ) (x : X) : ℤ :=
  open Classical in
  if x ∈ SheafOfModules.supp F ∧ relativeDimension C.dimensionFunction f x = k then
    sheafMultiplicity F x
  else 0

/-- A point with nonzero coefficient lies in the support and has relative dimension `k`. -/
private theorem mem_supp_and_relativeDimension_eq_of_sheafCycleCoeff_ne_zero
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (k : ℤ) {x : X} (h : sheafCycleCoeff C f F k x ≠ 0) :
    x ∈ SheafOfModules.supp F ∧ relativeDimension C.dimensionFunction f x = k := by
  classical
  simp only [sheafCycleCoeff, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
  exact h.1

/-- The coefficient function of a coherent sheaf has locally finite support once the support of
the sheaf has delta-dimension at most `k`: every point carrying a nonzero coefficient is then the
generic point of an irreducible component of the support, and those components form a locally
finite family. -/
theorem locallyFiniteSupport_sheafCycleCoeff (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    LocallyFiniteSupport (sheafCycleCoeff C f F k) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro x
  obtain ⟨t, htx, hfin⟩ := locallyFinite_irreducibleComponents_supp F x
  refine ⟨t, htx, ?_⟩
  set points : Set X := t ∩ Function.support (sheafCycleCoeff C f F k)
  have hcond (y : points) : y.1 ∈ SheafOfModules.supp F ∧
      relativeDimension C.dimensionFunction f y.1 = k :=
    mem_supp_and_relativeDimension_eq_of_sheafCycleCoeff_ne_zero C f F k y.2.2
  have hgen (y : points) :
      ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
        IsGenericPoint y.1 (Subtype.val '' Z.1 : Set X) :=
    isGenericPoint_component_supp_of_relativeDimension_eq C f F k y.1 hFk
      (hcond y).1 (hcond y).2
  set K : Set (irreducibleComponents (SheafOfModules.supp F : Set X)) :=
    {Z | ((Subtype.val '' Z.1 : Set X) ∩ t).Nonempty}
  have : Finite K := hfin.to_subtype
  have hinj : Function.Injective fun y : points ↦
      (⟨(hgen y).choose, ⟨y.1, (hgen y).choose_spec.mem, y.2.1⟩⟩ : K) := by
    intro y z hyz
    have hcomp : (hgen y).choose = (hgen z).choose := congrArg Subtype.val hyz
    exact Subtype.ext ((hgen y).choose_spec.eq (hcomp ▸ (hgen z).choose_spec))
  have : Finite points := Finite.of_injective _ hinj
  exact Set.toFinite points

/-- The cycle of a coherent sheaf whose support has delta-dimension at most `k`, before recording
that it has delta-dimension `k`. -/
def coherentSheafCycle (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    AlgebraicCycle X ℤ where
  toFun := sheafCycleCoeff C f F k
  supportWithinDomain' _ _ := trivial
  supportLocallyFiniteWithinDomain' x _ := locallyFiniteSupport_sheafCycleCoeff C f F k hFk x

/-- The cycle of a coherent sheaf has delta-dimension `k`: by construction a point carrying a
nonzero coefficient has relative dimension `k`. -/
theorem coherentSheafCycle_mem_cyclesOfDimension (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    coherentSheafCycle C f F k hFk ∈ cyclesOfDimension C f k := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  exact fun x hx ↦
    (mem_supp_and_relativeDimension_eq_of_sheafCycleCoeff_ne_zero C f F k hx).2

/-- **Stacks 02QX.** The `k`-cycle `[F]_k` associated to a coherent sheaf whose support has
delta-dimension at most `k`: the coefficient at a point of the support whose closure has
delta-dimension `k` is the length of the stalk there. -/
@[stacks 02QX "part (2): associated cycle"]
def cycleAssociatedToCoherentSheaf (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    CycleGroup C f k :=
  ⟨coherentSheafCycle C f F k hFk, coherentSheafCycle_mem_cyclesOfDimension C f F k hFk⟩

/-- The coefficient of `[F]_k` at a point is the multiplicity of the sheaf there exactly when the
point lies in the support and its closure has delta-dimension `k`, and is zero otherwise. -/
theorem cycleAssociatedToCoherentSheaf_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) (x : X) :
    (cycleAssociatedToCoherentSheaf C f F k hFk).1 x =
      open Classical in
      if x ∈ SheafOfModules.supp F ∧ relativeDimension C.dimensionFunction f x = k then
        sheafMultiplicity F x
      else 0 :=
  rfl

/-- **Stacks 02QX.** The coefficient formula for the cycle of a coherent sheaf does define a
`k`-cycle when the support of the sheaf has delta-dimension at most `k`. -/
@[stacks 02QX "part (2): existence of the associated cycle"]
theorem exists_cycleAssociatedToCoherentSheaf (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    ∃ c : CycleGroup C f k, ∀ x : X, (c : AlgebraicCycle X ℤ) x =
      open Classical in
      if x ∈ SheafOfModules.supp F ∧ relativeDimension C.dimensionFunction f x = k then
        sheafMultiplicity F x
      else 0 :=
  ⟨cycleAssociatedToCoherentSheaf C f F k hFk, cycleAssociatedToCoherentSheaf_apply C f F k hFk⟩

/-- At a point whose closure has delta-dimension `k`, the coefficient of `[F]_k` is the
multiplicity of the sheaf, with no condition on the support: off the support the multiplicity is
already zero. -/
theorem cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) {x : X}
    (hx : relativeDimension C.dimensionFunction f x = k) :
    (cycleAssociatedToCoherentSheaf C f F k hFk).1 x = sheafMultiplicity F x := by
  classical
  rw [cycleAssociatedToCoherentSheaf_apply]
  by_cases hsupp : x ∈ SheafOfModules.supp F
  · simp [hsupp, hx]
  · simp [hsupp, sheafMultiplicity_eq_zero_of_notMem_supp F hsupp]

/-- At a point whose closure does not have delta-dimension `k`, the coefficient of `[F]_k`
vanishes. -/
theorem cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) {x : X}
    (hx : relativeDimension C.dimensionFunction f x ≠ k) :
    (cycleAssociatedToCoherentSheaf C f F k hFk).1 x = 0 := by
  classical
  rw [cycleAssociatedToCoherentSheaf_apply]
  simp [hx]

end Stacks.Chow

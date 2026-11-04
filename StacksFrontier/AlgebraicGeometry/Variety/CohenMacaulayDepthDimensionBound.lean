module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.CohenMacaulayRegular
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerAlgebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The depth–dimension bound on a Cohen–Macaulay variety

Let `X` be an irreducible scheme locally of finite type over a field `k` and let `𝓔` be a finite
locally free `𝒪_X`-module. At every point `x` of `X`,

`depth(𝓔_x) + dim({x}‾) ≥ dim(X)`

as soon as `X` is Cohen–Macaulay.

## Main results

* `Stacks.Algebraization.ringKrullDim_stalk_add_dimClosureAt` — the dimension formula
  `dim(𝒪_{X,x}) + dim({x}‾) = dim(X)` on an irreducible scheme locally of finite type over a
  field.
* `Stacks.Algebraization.depth_stalk_le_sheafDepthAt` — the depth of the local ring bounds the
  depth of the stalk of a finite locally free module.
* `Stacks.Algebraization.intCast_le_sheafDepthAt_add_dimClosureAt_of_isCohenMacaulay` — the
  bound `depth(𝓔_x) + dim({x}‾) ≥ d`, in the extended integers in which [Stacks, Tag 0EL1]
  states its hypothesis.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), the dimension formula.
* [Stacks Project, Tag 0342](https://stacks.math.columbia.edu/tag/0342), Cohen–Macaulay through
  Serre's conditions.
* [Stacks Project, Tag 00LX](https://stacks.math.columbia.edu/tag/00LX), depth in a short exact
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### The dimension formula at a point -/

/-- **The dimension formula on an irreducible scheme locally of finite type over a field.** At
every point, the dimension of the local ring and the dimension of the closure of the point add
up to the dimension of the scheme. -/
theorem ringKrullDim_stalk_add_dimClosureAt
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + dimClosureAt X x = topologicalKrullDim X := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hclosure : dimClosureAt X x =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) :=
    topologicalKrullDim_closure_singleton_eq_trdeg k X f x
  rw [hclosure, add_comm, topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x,
    topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x]

/-! ### The stalk of a finite locally free module -/

/-- **The depth of the local ring bounds the depth of the stalk of a finite locally free
module.** -/
@[sga "2 X 2.1" "inequality depth O_{U"]
theorem depth_stalk_le_sheafDepthAt {X : Scheme.{u}} [IsLocallyNoetherian X] (E : X.Modules)
    [hE : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (x : X) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≤ sheafDepthAt E x := by
  let : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) E.val x
  obtain ⟨-, hfreeAll⟩ :=
    ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae E).out 4 2).mp hE
  obtain ⟨-, hftE⟩ :=
    ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae E).out 4 3).mp hE
  have hfree : Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) := hfreeAll x
  have hft : E.IsFiniteType := hftE
  have hfin : Module.Finite (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk X.sheaf E x
  exact _root_.AlgebraicGeometry.depth_le_depth_of_free _ _

/-! ### The arithmetic of the truncation -/

/-- In `ℕ∞`, a lower bound on `a + c` survives truncating `a` at it. -/
private lemma natCast_le_min_add {d a c : ℕ∞} (h : d ≤ a + c) : d ≤ min d a + c := by
  rcases le_total d a with hd | hd
  · rw [min_eq_left hd]; exact le_self_add
  · rw [min_eq_right hd]; exact h

/-- From `a + c = D` with `d ≤ D` and `min(d, a) ≤ e` one gets `d ≤ e + c`. -/
private lemma natCast_le_add_of_min_le {d : ℕ} {a c D e : WithBot ℕ∞} (hsum : a + c = D)
    (hD : ((d : ℕ) : WithBot ℕ∞) ≤ D) (he : min ((d : ℕ) : WithBot ℕ∞) a ≤ e) :
    ((d : ℕ) : WithBot ℕ∞) ≤ e + c := by
  subst hsum
  cases a using WithBot.recBotCoe with
  | bot => rw [WithBot.bot_add] at hD; exact absurd hD (by simp)
  | coe aa =>
  cases c using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at hD; exact absurd hD (by simp)
  | coe cc =>
  have hcast : ((d : ℕ) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) := by simp
  rw [hcast, ← WithBot.coe_add, WithBot.coe_le_coe] at hD
  cases e using WithBot.recBotCoe with
  | bot =>
    rw [hcast, ← WithBot.coe_min, le_bot_iff] at he
    exact absurd he WithBot.coe_ne_bot
  | coe ee =>
  rw [hcast, ← WithBot.coe_min, WithBot.coe_le_coe] at he
  rw [hcast, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact (natCast_le_min_add hD).trans (add_le_add he (le_refl cc))

/-- The comparison in `WithBot ℕ∞` of a natural number with a depth plus a dimension, read in
the extended integers. -/
private lemma intCast_le_enatToEInt_add_krullDimToEInt {d : ℕ} {a : ℕ∞} {c : WithBot ℕ∞}
    (h : ((d : ℕ) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) + c) :
    ((d : ℤ) : EInt) ≤ enatToEInt a + krullDimToEInt c := by
  cases c with
  | bot =>
    rw [WithBot.add_bot] at h
    exact absurd h (by simp)
  | coe m =>
    cases a <;> cases m <;> try exact le_top.trans_eq rfl
    rename_i aa mm
    have hsum : enatToEInt ((aa : ℕ) : ℕ∞) +
        krullDimToEInt (((mm : ℕ) : ℕ∞) : WithBot ℕ∞) = (((aa + mm : ℕ) : ℤ) : EInt) := by
      change ((aa : ℤ) : EInt) + ((mm : ℤ) : EInt) = _
      push_cast
      rfl
    rw [hsum]
    have hd : d ≤ aa + mm := by
      have hcast : ((d : ℕ) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) := by simp
      rw [hcast, show ((((aa : ℕ) : ℕ∞) : WithBot ℕ∞) + (((mm : ℕ) : ℕ∞) : WithBot ℕ∞)) =
        (((aa + mm : ℕ) : ℕ∞) : WithBot ℕ∞) by push_cast; rfl, WithBot.coe_le_coe] at h
      exact_mod_cast h
    exact WithBotTop.coe_le_coe.mpr (by exact_mod_cast hd)

/-! ### The bound on a Cohen–Macaulay variety -/

/-- **The depth–dimension bound on a Cohen–Macaulay variety.** Let `X` be an irreducible scheme
locally of finite type over a field `k` which is Cohen–Macaulay and of dimension at least `d`,
and let `𝓔` be a finite locally free `𝒪_X`-module. Then

`depth(𝓔_x) + dim({x}‾) ≥ d`

at every point `x` of `X`, in the extended integers in which [Stacks, Tag 0EL1] states its
hypothesis. -/
theorem intCast_le_sheafDepthAt_add_dimClosureAt_of_isCohenMacaulay
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] (E : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hCM : AlgebraicGeometry.IsCohenMacaulay X) (d : ℕ)
    (hdim : ((d : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) (x : X) :
    ((d : ℤ) : EInt) ≤ enatToEInt (sheafDepthAt E x) + krullDimToEInt (dimClosureAt X x) := by
  obtain ⟨hLN, -⟩ := ((isCohenMacaulay_tfae_stalk X).out 1 2).mp hCM
  have hSk : HasPropertySk X d := (isCohenMacaulay_iff_forall_hasPropertySk X).mp hCM d
  refine intCast_le_enatToEInt_add_krullDimToEInt ?_
  refine natCast_le_add_of_min_le (ringKrullDim_stalk_add_dimClosureAt k X f x) hdim ?_
  exact (hSk x).trans (WithBot.coe_le_coe.mpr (depth_stalk_le_sheafDepthAt E x))

end Stacks.Algebraization

end

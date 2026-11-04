module

public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth and Serre's condition for reflexive modules on a scheme

A coherent reflexive module on a locally Noetherian scheme has depth at least two at every
point where the structure sheaf does, and it satisfies Serre's condition `(S₂)` as soon as the
scheme does.  These are the two parts of [Stacks, Tag 0EBI].

Both are purely local statements, and the local algebra is already available:
`StacksFrontier.Algebra.Module.Reflexive` proves them for a finite reflexive module over a
Noetherian local ring ([Stacks, Tag 0AV5] and [Stacks, Tag 0EBA]).  What this file supplies is
the passage from the sheaf to its stalks.  Reflexivity of the stalks comes from
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_stalk_of_isReflexive`
([Stacks, Tag 0AY3] (1) ⇒ (2)), finiteness of the stalks from
`Stacks.SheafOfModules.finite_stalk`, and the depth bound is then
[Stacks, Tag 0AV5] applied to `Hom(F_x^∨, 𝒪_{X,x})` transported along the evaluation
isomorphism `F_x ≅ F_x^∨∨`.

## Main results

* `depth_stalk_ge_two_of_isReflexive` — part (1): the depth bound on stalks.
* `sheafHasPropertySk_two_of_isReflexive` — part (2): Serre's condition `(S₂)` for the module.
* `isFinitePresentation_dualSheaf` — [Stacks, Tag 01Y2] for the dual: the dual of a coherent
  module on a locally Noetherian scheme is of finite presentation.
* `sheafHasPropertySk_of_forall` and `min_supportDim_le_depth_of_sheafHasPropertySk` — the two
  directions of the transport between `AlgebraicGeometry.SheafHasPropertySk` and its pointwise
  form in the stalk module structure that instance search finds.

## Implementation notes

The stalk criterion of
`StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion` asks for
`(dualSheaf F).IsFinitePresentation` alongside `F.IsFinitePresentation`.  For a coherent module
on a locally Noetherian scheme that is automatic — it is [Stacks, Tag 01Y2], coherence of the
internal hom — and `isFinitePresentation_dualSheaf` below discharges it from
`Stacks.SheafOfModules.InternalHom.isFinitePresentation_sheafInternalHom`
([Stacks, Tag 01CQ]) together with coherence of the structure sheaf.  Both parts below are
therefore unconditional, and carry the tag.

The source states both parts for an *integral* locally Noetherian scheme.  Integrality is not
used anywhere in the argument — the reflexivity of `F_x` is what the proof needs, and the
algebraic input `one_le_depth_and_two_le_depth_linearMap` asks only for a Noetherian local ring
— so the statements here omit it, which is a generalization and not a weakening.

`AlgebraicGeometry.SheafHasPropertySk` is stated with the module structure on a stalk at the
ringed-space spelling of [Stacks, Tag 01CB], whereas instance search on a `Scheme.Modules` finds
Mathlib's at the scheme spelling; the two are the same instance
(`Stacks.SheafOfModules.stalkModule_eq`, which is `rfl`), and `sheafHasPropertySk_of_forall`
passes between the spellings.

## References

* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0AV5](https://stacks.math.columbia.edu/tag/0AV5)
* [Stacks Project, Tag 0EBA](https://stacks.math.columbia.edu/tag/0EBA)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

private lemma min_supportDim_le_depth_congr {R M : Type u} [CommRing R] [AddCommGroup M]
    (m₁ m₂ : Module R M) (hm : m₁ = m₂) (I : Ideal R) (k : ℕ)
    (h : min (k : WithBot ℕ∞) (@Module.supportDim R ‹CommRing R› M ‹AddCommGroup M› m₂) ≤
      (@Module.depth R ‹CommRing R› I M ‹AddCommGroup M› m₂ : WithBot ℕ∞)) :
    min (k : WithBot ℕ∞) (@Module.supportDim R ‹CommRing R› M ‹AddCommGroup M› m₁) ≤
      (@Module.depth R ‹CommRing R› I M ‹AddCommGroup M› m₁ : WithBot ℕ∞) := by
  cases hm
  exact h

variable {X : Scheme.{u}}

/-- The module structure on a stalk used in Tag 01CB, in which the sheaf form of Serre's
condition is stated, is the one `instance` search finds for a module on a scheme. -/
private lemma stalkModule_eq_presheafInstance (F : X.Modules) (x : X) :
    (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toSheafedSpace F.val x :
        Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) =
      AlgebraicGeometry.Scheme.Modules.moduleStalk F x :=
  Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace F.val x

/-- Serre's condition for a module on a scheme, in the pointwise form in which the local
algebra supplies it.  `min_supportDim_le_depth_of_sheafHasPropertySk` is the converse. -/
public lemma sheafHasPropertySk_of_forall (F : X.Modules) (k : ℕ)
    (h : ∀ x : X, min (k : WithBot ℕ∞)
        (Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (F.presheaf.stalk x) : WithBot ℕ∞)) :
    SheafHasPropertySk X F k := by
  intro x
  exact min_supportDim_le_depth_congr _ _ (stalkModule_eq_presheafInstance F x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) k (h x)

/-- Serre's condition for a module on a scheme, read off at a point in the spelling that the
local algebra uses.  This is the converse transport to `sheafHasPropertySk_of_forall`. -/
public lemma min_supportDim_le_depth_of_sheafHasPropertySk (F : X.Modules) (k : ℕ)
    (h : SheafHasPropertySk X F k) (x : X) :
    min (k : WithBot ℕ∞)
        (Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (F.presheaf.stalk x) : WithBot ℕ∞) :=
  min_supportDim_le_depth_congr _ _ (stalkModule_eq_presheafInstance F x).symm
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) k (h x)

/-- **[Stacks, Tag 01Y2] for the dual.** The dual `F^∨ = SheafHom(F, 𝒪_X)` of a coherent module
on a locally Noetherian scheme is of finite presentation: `F` itself is of finite presentation,
the structure sheaf is coherent, and the internal hom between such modules is of finite
presentation by [Stacks, Tag 01CQ]. -/
public lemma isFinitePresentation_dualSheaf [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] : (dualSheaf F).IsFinitePresentation :=
  have finitePresentation : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have coherentUnit : _root_.SheafOfModules.IsCoherent
      (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.InternalHom.spaceRingedSite X.sheaf).O)) :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  @Stacks.SheafOfModules.InternalHom.isFinitePresentation_sheafInternalHom.{u}
    X inferInstance X.sheaf F
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.InternalHom.spaceRingedSite X.sheaf).O))
    finitePresentation coherentUnit

/-- Depth at least one (resp. two) of the structure sheaf at `x` passes to a coherent reflexive
module, via the evaluation isomorphism `F_x ≅ F_x^∨∨`. -/
private lemma le_depth_stalk_of_le_depth [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F) (x : X) :
    ((1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) ∧
    ((2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) := by
  have : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have : (dualSheaf F).IsFinitePresentation := isFinitePresentation_dualSheaf F
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  have : Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    isReflexive_stalk_of_isReflexive F hF x
  have key := one_le_depth_and_two_le_depth_linearMap
    (R := X.presheaf.stalk x) (M := Module.Dual (X.presheaf.stalk x) (F.presheaf.stalk x))
    (N := X.presheaf.stalk x)
  rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (Module.evalEquiv (X.presheaf.stalk x) (F.presheaf.stalk x))]
  exact key

/-- **[Stacks, Tag 0EBI], part (1).** A coherent reflexive module on a locally Noetherian
scheme has depth at least two at every point where the local ring does. -/
@[stacks 0EBI "part (1)"]
public theorem depth_stalk_ge_two_of_isReflexive [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F]
    (hF : IsReflexive F) (x : X)
    (hx : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x) :=
  (le_depth_stalk_of_le_depth F hF x).2 hx

/-- In `WithBot ℕ∞`, an element below `n + 1` is at most `n`. -/
private lemma withBot_lt_succ_le {d : WithBot ℕ∞} {n : ℕ} (h : d < ((n + 1 : ℕ) : WithBot ℕ∞)) :
    d ≤ n := by
  cases d with
  | bot => simp
  | coe d =>
    cases d with
    | top => simp at h
    | coe m =>
      have : m < n + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.mp this

/-- In `WithBot ℕ∞`, an element below `2` is at most `1`. -/
public lemma withBot_lt_two_le_one {d : WithBot ℕ∞} (h : d < 2) : d ≤ 1 :=
  withBot_lt_succ_le (n := 1) (by simpa using h)

/-- In `WithBot ℕ∞`, an element below `1` is at most `0`. -/
public lemma withBot_lt_one_le_zero {d : WithBot ℕ∞} (h : d < 1) : d ≤ 0 :=
  withBot_lt_succ_le (n := 0) (by simpa using h)

/-- The pointwise content of [Stacks, Tag 0EBI], part (2): at every point, the minimum of two
and the dimension of the support of the stalk is at most the depth of the stalk. -/
private lemma min_two_supportDim_le_depth_of_isReflexive [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (hF : IsReflexive F) (hX : HasPropertySk X 2) (x : X) :
    min (2 : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (F.presheaf.stalk x) : WithBot ℕ∞) := by
  have hSupport : Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)
      ≤ ringKrullDim (X.presheaf.stalk x) :=
    Module.supportDim_le_ringKrullDim (X.presheaf.stalk x) (F.presheaf.stalk x)
  have hxRing : min (2 : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) : WithBot ℕ∞) := hX x
  -- if the support has dimension at least `n ≤ 2`, so does the ring, hence its depth is `≥ n`
  have hdepthR : ∀ n : ℕ, n ≤ 2 →
      (n : ℕ∞) ≤ Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x) →
      (n : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
    fun n hn h => WithBot.coe_le_coe.mp
      ((le_min (WithBot.coe_le_coe.mpr (by exact_mod_cast hn))
        (by exact_mod_cast h.trans hSupport)).trans hxRing)
  have hbound := le_depth_stalk_of_le_depth F hF x
  by_cases htwo : (2 : ℕ∞) ≤ Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)
  · exact le_trans (min_le_left (2 : WithBot ℕ∞) _)
      (WithBot.coe_le_coe.mpr (hbound.2 (hdepthR 2 le_rfl htwo)))
  · by_cases hone : (1 : ℕ∞) ≤ Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)
    · have hdimM : Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)
          ≤ (1 : WithBot ℕ∞) :=
        withBot_lt_two_le_one (lt_of_not_ge (by exact_mod_cast htwo))
      exact (min_le_iff).2 (Or.inr (hdimM.trans
        (WithBot.coe_le_coe.mpr (hbound.1 (hdepthR 1 (by norm_num) hone)))))
    · have hdimM : Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x) ≤ 0 :=
        withBot_lt_one_le_zero (lt_of_not_ge (by exact_mod_cast hone))
      exact (min_le_right _ _).trans
        (hdimM.trans (WithBot.coe_le_coe.mpr (show (0 : ℕ∞) ≤
          Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (F.presheaf.stalk x) from by simp)))

/-- **[Stacks, Tag 0EBI], part (2).** On a locally Noetherian scheme satisfying Serre's
condition `(S₂)`, every coherent reflexive module satisfies `(S₂)`. -/
@[stacks 0EBI "part (2)"]
public theorem sheafHasPropertySk_two_of_isReflexive [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F]
    (hF : IsReflexive F) (hX : HasPropertySk X 2) :
    SheafHasPropertySk X F 2 :=
  sheafHasPropertySk_of_forall F 2 (min_two_supportDim_le_depth_of_isReflexive F hF hX)

end Stacks.AlgebraicGeometry.ReflexiveModules

end

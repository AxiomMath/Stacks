module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.SheafHomOnSections

/-!
# Depth and Serre's conditions for the internal hom of coherent modules

Let `X` be a locally Noetherian scheme and let `F` and `G` be coherent `𝒪_X`-modules. The
internal hom `SheafHom(F, G)` inherits from `G` both of the lowest depth bounds at a point
([Stacks, Tag 0EBC]) and Serre's conditions `(S₁)` and `(S₂)` ([Stacks, Tag 0AXQ]).

Everything is local and rests on one input: for `F` of finite presentation the stalk of
`SheafHom(F, G)` at `x` is the module of `𝒪_{X,x}`-linear maps `F_x → G_x`, which is
[Stacks, Tag 01CP] (`Stacks.SheafOfModules.SheafHomStalk`). Under that identification the depth
bounds are the algebraic statement that `Hom_R(M, N)` inherits depth one and depth two from `N`
([Stacks, Tag 0AV5], `one_le_depth_and_two_le_depth_linearMap`), and the support of the stalk is
contained in the support of `G_x` because an element annihilating `G_x` annihilates every map
into it.

## Main results

* `AlgebraicGeometry.support_stalk_internalHom_subset` and
  `AlgebraicGeometry.supportDim_stalk_internalHom_le`: the support of the stalk of the internal
  hom sits inside the support of the target stalk, hence has no larger dimension.
* `AlgebraicGeometry.one_le_depth_stalk_internalHom` and
  `AlgebraicGeometry.two_le_depth_stalk_internalHom`: the two parts of [Stacks, Tag 0EBC].
* `AlgebraicGeometry.sheafHasPropertySk_one_internalHom` and
  `AlgebraicGeometry.sheafHasPropertySk_two_internalHom`: the two parts of
  [Stacks, Tag 0AXQ].

## Implementation notes

The internal hom appears as an arbitrary representative `H : SheafHom X.sheaf F G`, the
characterised datum of [Stacks, Tag 01CO]: an `𝒪_X`-module together with an identification of
its sections over every open `U` with the `𝒪_U`-linear maps `F|_U → G|_U`, compatible with
restriction and with the action of the structure sheaf. This is the form in which Tag 01CP is
available, and it makes the statements apply to every construction of the internal hom rather
than to one chosen model. The hypothesis is satisfiable — `sheafHomRepresentative` exhibits a
representative — so none of the statements below is vacuous.

Serre's condition is `AlgebraicGeometry.SheafHasPropertySk`, which is stated with the stalk
module structure of [Stacks, Tag 01CB]; the pointwise inequalities are proved in the module
structure that instance search finds on a `Scheme.Modules`, and
`Stacks.AlgebraicGeometry.ReflexiveModules.sheafHasPropertySk_of_forall` and
`min_supportDim_le_depth_of_sheafHasPropertySk` are the transports between the two spellings.

Depth takes values in `ℕ∞` and support dimension in `WithBot ℕ∞`, so the case analysis in the
two Serre statements compares `min k (dim)` with the coerced depth in the latter type.

No coherence of the internal hom is needed anywhere: the source only has to be of finite
presentation for Tag 01CP, and the target only finite over the local ring.

## References

* [Stacks Project, Tag 0AXQ](https://stacks.math.columbia.edu/tag/0AXQ)
* [Stacks Project, Tag 0EBC](https://stacks.math.columbia.edu/tag/0EBC)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0AV5](https://stacks.math.columbia.edu/tag/0AV5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A representative of the internal hom of two modules on a scheme, in the sense of
[Stacks, Tag 01CO]: the construction of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.SheafHomOnSections` is one.

This returns the datum rather than its `Nonempty`, so that the statements below which quantify
over a representative are visibly satisfiable by a named term. -/
public noncomputable def sheafHomRepresentative (F G : X.Modules) : SheafHom X.sheaf F G :=
  Stacks.Cohomology.SheafHomComplex.sheafHom X.sheaf F G

/-- The internal hom carried by a representative `H` in the sense of [Stacks, Tag 01CO], as a
module on the scheme `X`.  This is `H.obj`, with its type spelled so that the `Scheme.Modules`
API — in particular the stalks and their module structures — applies to it. -/
public abbrev internalHomOf {F G : X.Modules} (H : SheafHom X.sheaf F G) : X.Modules := H.obj

/-- **[Stacks, Tag 01CP] for a module on a scheme.** For `F` of finite presentation the stalk
of the internal hom `SheafHom(F, G)` at `x` is the module of `𝒪_{X,x}`-linear maps from `F_x`
to `G_x`. -/
public noncomputable def internalHomStalkEquiv (F G : X.Modules) [F.IsFinitePresentation]
    (H : SheafHom X.sheaf F G) (x : X) :
    (internalHomOf H).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (F.presheaf.stalk x →ₗ[X.presheaf.stalk x] G.presheaf.stalk x) :=
  (sheafHomStalkLinearEquivOfFinitePresentation H x).equiv

/-- **The support of the stalk of an internal hom lies in the support of the target stalk.**
For coherent modules on a locally Noetherian scheme, every prime of `𝒪_{X,x}` in the support of
`SheafHom(F, G)_x` is in the support of `G_x`. -/
public theorem support_stalk_internalHom_subset [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) (x : X) :
    Module.support (X.presheaf.stalk x) ((internalHomOf H).presheaf.stalk x) ⊆
      Module.support (X.presheaf.stalk x) (G.presheaf.stalk x) := by
  have : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  have : Module.Finite (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent G x
  rw [(internalHomStalkEquiv F G H x).support_eq]
  exact support_linearMap_subset

/-- **The stalk of an internal hom has support of no larger dimension than the target stalk.**
-/
public theorem supportDim_stalk_internalHom_le [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) (x : X) :
    Module.supportDim (X.presheaf.stalk x) ((internalHomOf H).presheaf.stalk x) ≤
      Module.supportDim (X.presheaf.stalk x) (G.presheaf.stalk x) :=
  Order.krullDim_le_of_strictMono
    (Set.inclusion (support_stalk_internalHom_subset F G H x)) fun _ _ h ↦ h

/-- The depth bounds of Tag 0EBC, as a conjunction: the stalk of `SheafHom(F, G)` at `x` has depth
at least `n` as soon as `G_x` does, for `n = 1` and `n = 2`. -/
private theorem one_le_and_two_le_depth_stalk_internalHom [IsLocallyNoetherian X]
    (F G : X.Modules) [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) (x : X) :
    ((1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (G.presheaf.stalk x) →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ((internalHomOf H).presheaf.stalk x)) ∧
    ((2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (G.presheaf.stalk x) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ((internalHomOf H).presheaf.stalk x)) := by
  have : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  have : Module.Finite (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent G x
  rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (internalHomStalkEquiv F G H x)]
  exact one_le_depth_and_two_le_depth_linearMap (R := X.presheaf.stalk x)
    (M := F.presheaf.stalk x) (N := G.presheaf.stalk x)

/-- **[Stacks, Tag 0EBC], part (1).** For coherent modules on a locally Noetherian scheme, the
stalk of `SheafHom(F, G)` at `x` has depth at least one as soon as `G_x` does. -/
@[stacks 0EBC "part (1)"]
public theorem one_le_depth_stalk_internalHom [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) (x : X)
    (hx : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (G.presheaf.stalk x)) :
    (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      ((internalHomOf H).presheaf.stalk x) :=
  (one_le_and_two_le_depth_stalk_internalHom F G H x).1 hx

/-- **[Stacks, Tag 0EBC], part (2).** For coherent modules on a locally Noetherian scheme, the
stalk of `SheafHom(F, G)` at `x` has depth at least two as soon as `G_x` does. -/
@[stacks 0EBC "part (2)"]
public theorem two_le_depth_stalk_internalHom [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) (x : X)
    (hx : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (G.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      ((internalHomOf H).presheaf.stalk x) :=
  (one_le_and_two_le_depth_stalk_internalHom F G H x).2 hx

/-- The numerical core of the two Serre statements: if `dH ≤ dG`, `min k dG ≤ a`, and the depth
bounds one and two transfer from `a` to `b`, then `min k dH ≤ b`, for `k ≤ 2`. -/
private theorem min_le_of_depth_transfer {k : ℕ} (hk : k ≤ 2) {dH dG : WithBot ℕ∞} {a b : ℕ∞}
    (hdim : dH ≤ dG) (hG : min (k : WithBot ℕ∞) dG ≤ a)
    (h1 : 1 ≤ a → 1 ≤ b) (h2 : 2 ≤ a → 2 ≤ b) : min (k : WithBot ℕ∞) dH ≤ b := by
  have key (j : ℕ) (hj : j ≤ k) (hjd : (j : WithBot ℕ∞) ≤ dH) : (j : ℕ∞) ≤ a :=
    WithBot.coe_le_coe.mp ((le_min (by exact_mod_cast hj) (hjd.trans hdim)).trans hG)
  have hb : (0 : WithBot ℕ∞) ≤ b := WithBot.coe_le_coe.mpr (by simp)
  interval_cases k
  · exact (min_le_left _ _).trans hb
  · by_cases hone : (1 : WithBot ℕ∞) ≤ dH
    · exact (min_le_left _ _).trans (WithBot.coe_le_coe.mpr (h1 (key 1 le_rfl hone)))
    · exact (min_le_right _ _).trans ((withBot_lt_one_le_zero (lt_of_not_ge hone)).trans hb)
  · by_cases htwo : (2 : WithBot ℕ∞) ≤ dH
    · exact (min_le_left _ _).trans (WithBot.coe_le_coe.mpr (h2 (key 2 le_rfl htwo)))
    · refine (min_le_right _ _).trans ?_
      by_cases hone : (1 : WithBot ℕ∞) ≤ dH
      · exact (withBot_lt_two_le_one (lt_of_not_ge htwo)).trans
          (WithBot.coe_le_coe.mpr (h1 (key 1 (by norm_num) hone)))
      · exact (withBot_lt_one_le_zero (lt_of_not_ge hone)).trans hb

/-- **[Stacks, Tag 0AXQ], part (1).** On a locally Noetherian scheme the internal hom of
coherent modules into a module satisfying Serre's condition `(S₁)` satisfies `(S₁)`. -/
@[stacks 0AXQ "hom_into_s1"]
public theorem sheafHasPropertySk_one_internalHom [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) (hG : SheafHasPropertySk X G 1) :
    SheafHasPropertySk X (internalHomOf H) 1 :=
  sheafHasPropertySk_of_forall _ 1 fun x ↦
    min_le_of_depth_transfer (by norm_num) (supportDim_stalk_internalHom_le F G H x)
      (min_supportDim_le_depth_of_sheafHasPropertySk G 1 hG x)
      (one_le_depth_stalk_internalHom F G H x) (two_le_depth_stalk_internalHom F G H x)

/-- **[Stacks, Tag 0AXQ], part (2).** On a locally Noetherian scheme the internal hom of
coherent modules into a module satisfying Serre's condition `(S₂)` satisfies `(S₂)`. -/
@[stacks 0AXQ "hom_into_s2"]
public theorem sheafHasPropertySk_two_internalHom [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (H : SheafHom X.sheaf F G) (hG : SheafHasPropertySk X G 2) :
    SheafHasPropertySk X (internalHomOf H) 2 :=
  sheafHasPropertySk_of_forall _ 2 fun x ↦
    min_le_of_depth_transfer le_rfl (supportDim_stalk_internalHom_le F G H x)
      (min_supportDim_le_depth_of_sheafHasPropertySk G 2 hG x)
      (one_le_depth_stalk_internalHom F G H x) (two_le_depth_stalk_internalHom F G H x)

end AlgebraicGeometry

end

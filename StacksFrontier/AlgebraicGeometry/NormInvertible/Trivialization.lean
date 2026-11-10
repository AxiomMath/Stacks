module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Reconstruction
public import StacksFrontier.CategoryTheory.Monoidal.UnitEndomorphism
public import StacksFrontier.Topology.Sheaves.Functors.Module.UnitEndomorphismSections

/-!
# Trivializations of a sheaf of modules over an open, and the generators they produce

A sheaf of `𝒪_X`-modules `L` on a ringed space is *trivialized over an open* `U` by an
isomorphism `e : L|_U ≅ 𝒪_U` of sheaves of modules on the localized site `Over U`. This file
bridges that datum to the generator calculus of
`StacksFrontier/AlgebraicGeometry/NormInvertible/Generators.lean`, which works with a section
`s ∈ L(U)` such that multiplication by `s` is bijective over every smaller open.

The bridge has four parts, and the middle two are what a chart construction actually consumes.

* `Stacks.SheafOfModules.generatorOfOverIso`: the generator produced by a trivialization — the
  image of the unit section under `e⁻¹`.
* `Stacks.SheafOfModules.generatorOfOverIso_restrict`: **the restriction law.** Restricting the
  generator is the generator of the restricted trivialization.
* `Stacks.SheafOfModules.generatorRatioUnit_generatorOfOverIso`: **the ratio law.** The
  transition unit of the generators of two trivializations over the same open is the unit of the
  ring of sections attached to the automorphism of `𝒪_U` comparing them.
* `Stacks.SheafOfModules.overIsoOfGenerator`: **the converse**, so that the bridge is a genuine
  two-sided correspondence rather than one direction. The round trip is
  `Stacks.SheafOfModules.generatorOfOverIso_overIsoOfGenerator`, and
  `Stacks.SheafOfModules.generatorRatioUnit_eq_unitAutValue` is what it buys: the comparison
  units of trivializations are exactly the transition units of generators, so the hypothesis
  below is neither vacuous nor automatic.

With the two laws, a family of trivializations on a covering family has a transition cocycle
computed entirely in the isomorphism calculus, and
`Stacks.SheafOfModules.isoOfTransitionEq` applies. That is packaged as
`Stacks.SheafOfModules.isoOfOverIsoAutEq`: **two modules trivialized on a common covering family
with the same comparison automorphisms on the pairwise intersections are isomorphic.**

Trivializing two modules on a *common* cover is not enough on its own — on `ℙ¹` both `𝒪` and
`𝒪(1)` are trivial on the standard two-element cover — so the comparison automorphisms carry the
whole content.

## Main definitions

* `Stacks.SheafOfModules.overIsoRestrict` and `Stacks.SheafOfModules.overIsoSection`: the
  restriction of a trivialization to a smaller open, and the section it picks out.
* `Stacks.SheafOfModules.overUnitHomApply`: the value of a morphism from the unit module of the
  localized site, typed in the base spelling.
* `Stacks.SheafOfModules.generatorOfOverIso`: the generator produced by a trivialization.
* `Stacks.SheafOfModules.overIsoOfGenerator`: the trivialization produced by a generator.

## Main results

* `Stacks.SheafOfModules.overUnitHomApply_eq_smul`: a morphism out of the unit module is
  multiplication by the section it carries the unit section to, with the scalar action read on
  the base side. This is the one computation the rest of the file runs on.
* `Stacks.SheafOfModules.overIsoSection_restrict` and
  `Stacks.SheafOfModules.generatorOfOverIso_restrict`: the restriction law, on sections and on
  generators.
* `Stacks.SheafOfModules.bijective_smul_overIsoSection`: multiplication by the section of a
  trivialization is bijective.
* `Stacks.SheafOfModules.generatorRatioUnit_generatorOfOverIso`: the ratio law.
* `Stacks.SheafOfModules.generatorCoord_restrictLe`: the coordinate of a section in a restricted
  frame, with the containment supplied rather than composed.
* `Stacks.SheafOfModules.generatorOfOverIso_overIsoOfGenerator`: the round trip, so the bridge is
  two-sided.
* `Stacks.SheafOfModules.generatorRatioUnit_eq_unitAutValue`: every transition unit of two
  generators is the comparison unit of two trivializations.
* `Stacks.SheafOfModules.isoOfTransitionEqInf`: the transition units of two families of
  generators need only be compared on the pairwise intersections `U i ⊓ U j`, not on every open
  contained in two charts.
* `Stacks.SheafOfModules.isoOfOverIsoAutEq`: the conclusion of the three above.

## Implementation notes

**The comparison unit of two trivializations is not built here.**
`Stacks.SheafOfModules.unitAutValue`
(`StacksFrontier/Topology/Sheaves/Functors/Module/UnitEndomorphismSections.lean`) already sends an
automorphism of the free sheaf of rank one to a unit of the ring of sections, with
`unitAutValue_autPow` carrying `CategoryTheory.Iso.autPow a n` to the `n`th power of that unit,
and `unitHom_val_app_apply` — stated for a morphism into an *arbitrary* module on an *arbitrary*
site — is the multiplication computation this whole file runs on. Both are used rather than
re-derived; the only thing added on that side is
`Stacks.SheafOfModules.overUnitHomApply_eq_smul`, which is `unitHom_val_app_apply` with the
scalar action read on the base side of the spelling crossing described below.

**That is what makes the tensor-power comparison compose.** `trivPow_trans_aut` says that changing
a trivialization of `L` by an automorphism `a` changes the induced trivialization of `L^{⊗ n}` by
`CategoryTheory.Iso.autPow a n`. The ratio law turns a comparison automorphism into a transition
unit, and `unitAutValue_autPow` turns `a.autPow n` into the `n`th power of that unit — which is
how an equality of comparison automorphisms upstairs becomes the hypothesis `isoOfTransitionEq`
consumes. Note that `tensorPower` has no sectionwise description anywhere, so a transition-unit
law about a tensor power cannot be obtained on sections; it has to arrive through the isomorphism
calculus, which is the shape `isoOfOverIsoAutEq` accepts.

**What this adds to the two places the forward direction already appeared.** Neither of them
leaves a usable declaration, and the ratio law is the reason it matters.
`Stacks.Cohomology.Generators.exists_generator_section`
(`StacksFrontier/Topology/Sheaves/Cohomology/Torsors/GeneratorsOfARankOneModule.lean`) builds this
generator from a trivialization inside its own tactic block and concludes only
`Nonempty (GeneratorSections X L U)`.
`Stacks.SheafOfModules.exists_smulSectionMap_bijective_of_over_iso_unit`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne/Unconditional.lean`) states the
same construction for a general site, but existentially: `∃ e, ∀ V, Bijective (smulSectionMap …)`.
A transition unit is a function of the *section*, so an existential statement cannot be composed
into one — `Classical.choose` forgets which trivialization the section came from, and the ratio
law becomes unstatable. `Stacks.SheafOfModules.generatorOfIso`
(`NormInvertible/Generators.lean`) is a named construction but takes a **global** trivialization
`L ≅ 𝒪_X`, which is not what a trivializing cover supplies. Hence a named `generatorOfOverIso`
here.

**Two spellings of the ring of sections, and why every proof here is in term mode.** The generator
calculus states its scalars in `(structureSheaf X.sheaf).obj.obj (op U)`, while a morphism of
modules on the localized site has its scalars in
`((structureSheaf X.sheaf).over U).obj.obj (op (Over.mk (𝟙 U)))`. The two rings are definitionally
equal and are not the same term. Elaboration crosses that boundary freely — which is why
`overIsoSection` can be *stated* at the first spelling and *defined* through the second — but
instance search does not, so `r • x` across the boundary fails to synthesize `HSMul`, and `rw`
does not, because it builds its motive at `implicit` transparency. For the first, a type
*ascription* is not enough: an ascribed
`(φ.val.app _ 1 : L.val.obj (op U))` still elaborates at the slice spelling and the `•` beside it
then fails to synthesize, which is why `overUnitHomApply` exists as a `def` — a definition's
declared type does pin the side, and instantiating it later does not re-run synthesis. For the
second, `rw [h1] at h` for `h1 : r • (1 : 𝒪_U(Over.mk (𝟙 U))) = r` reports *did not find an
occurrence of the pattern* on a hypothesis that visibly contains it, while `congrArg` applied to
the same equation crosses it. Every proof below is therefore an `Eq.trans`/`congrArg` chain. The
one `rw` that survives, in `bijective_smul_overIsoSection`, rewrites a function equality in the
goal and not across the boundary.

**The restriction of a trivialization is evaluation at the inclusion.** `overIsoRestrict` is built
from `SheafOfModules.overMap` and `SheafOfModules.overMapUnitIso`, and the latter is `Iso.refl`,
so the composite's inverse evaluated at the terminal object `Over.mk (𝟙 V)` of the smaller slice
is, **by `rfl`**, the original inverse evaluated at `Over.mk (homOfLE h)`. The restriction law is
therefore one naturality square of `e.inv` plus `PresheafOfModules.unit_map_one`, rather than a
comparison of two restriction functors.

**Why `isoOfTransitionEqInf` is worth stating.** `isoOfTransitionEq` quantifies its hypothesis
over *every* open contained in two charts. `generatorRatioUnit_restrict` makes that hypothesis
follow from its value at `U i ⊓ U j`, since any such open factors through the intersection. The
reduction costs two applications of `generatorRestrict_trans` and is what makes the hypothesis
checkable: a comparison automorphism is produced on the intersection, not on an arbitrary
subopen.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe v u

namespace Stacks.SheafOfModules

/-! ### Trivializations over an open -/

variable {X : RingedSpace.{u, u}}
  (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))

/-- The restriction of a trivialization of `L` over `U` to a smaller open. `overMapUnitIso` is
`Iso.refl`, so this composite's inverse at the terminal object of the smaller slice is, by `rfl`,
the original inverse at the inclusion `V ⟶ U`. -/
noncomputable def overIsoRestrict {U V : Opens X.carrier} (h : V ≤ U)
    (e : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    L.over V ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over V) :=
  (_root_.SheafOfModules.overMap (structureSheaf X.sheaf) (homOfLE h)).mapIso e ≪≫
    _root_.SheafOfModules.overMapUnitIso (homOfLE h)

/-- The value of a morphism from the unit module of the localized site at a section of `𝒪_U`,
typed in the base spelling `L.val.obj (op U)`. Both sides of
`Stacks.SheafOfModules.overUnitHomApply_eq_smul` are stated through this definition: an ascription
alone does not keep the scalar action on the base side, where `HSMul` is the instance that
synthesizes. -/
noncomputable def overUnitHomApply {U : Opens X.carrier}
    (φ : _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U) ⟶ L.over U)
    (r : (structureSheaf X.sheaf).obj.obj (op U)) : L.val.obj (op U) :=
  φ.val.app (op (Over.mk (𝟙 U))) r

/-- **A morphism out of the unit module of the localized site is multiplication by the section it
carries the unit section to**, with both sides read in the base spelling. The computation itself
is `Stacks.SheafOfModules.unitHom_val_app_apply`, for an arbitrary target on an arbitrary site;
what this adds is only that the scalar action is the one on `L.val.obj (op U)`, which is the side
`Stacks.SheafOfModules.generatorRatioUnit_eq` consumes. -/
theorem overUnitHomApply_eq_smul {U : Opens X.carrier}
    (φ : _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U) ⟶ L.over U)
    (r : (structureSheaf X.sheaf).obj.obj (op U)) :
    overUnitHomApply L φ r = r • overUnitHomApply L φ 1 :=
  unitHom_val_app_apply φ (op (Over.mk (𝟙 U))) r

/-- The section of `L` over `U` that a trivialization of `L` over `U` carries the unit section
to. -/
noncomputable def overIsoSection {U : Opens X.carrier}
    (e : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    L.val.obj (op U) :=
  overUnitHomApply L e.inv 1

/-- The inclusion `V ⟶ U`, read as a morphism of the localized site into its terminal object. -/
noncomputable abbrev overTerminalHom {U V : Opens X.carrier} (h : V ≤ U) :
    (Over.mk (homOfLE h) : Over U) ⟶ Over.mk (𝟙 U) :=
  Over.homMk (homOfLE h) (by simp)

/-- **The restriction law for the section of a trivialization.** -/
theorem overIsoSection_restrict {U V : Opens X.carrier} (h : V ≤ U)
    (e : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    L.val.map (homOfLE h).op (overIsoSection L e) =
      overIsoSection L (overIsoRestrict L h e) := by
  have hnat := PresheafOfModules.naturality_apply e.inv.val (overTerminalHom (X := X) h).op
    ((1 : (structureSheaf X.sheaf).obj.obj (op U)) :
      (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
        (op (Over.mk (𝟙 U))))
  have hone : (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.map
      (overTerminalHom (X := X) h).op
      ((1 : (structureSheaf X.sheaf).obj.obj (op U)) :
        (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
          (op (Over.mk (𝟙 U))))
      = ((1 : (structureSheaf X.sheaf).obj.obj (op V)) :
        (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
          (op (Over.mk (homOfLE h)))) :=
    PresheafOfModules.unit_map_one (R := ((structureSheaf X.sheaf).over U).obj)
      (overTerminalHom (X := X) h).op
  exact hnat.symm.trans
    (congrArg (fun z => e.inv.val.app (op (Over.mk (homOfLE h))) z) hone)

/-- Multiplication by the section of a trivialization is bijective on the open the trivialization
lives on. -/
theorem bijective_smul_overIsoSection {U : Opens X.carrier}
    (e : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    Function.Bijective
      (fun r : (structureSheaf X.sheaf).obj.obj (op U) => r • overIsoSection L e) := by
  let m := (_root_.SheafOfModules.evaluation ((structureSheaf X.sheaf).over U)
    (op (Over.mk (𝟙 U)))).map e.inv
  have hm : Function.Bijective m := ConcreteCategory.bijective_of_isIso m
  have hfun : (fun r : (structureSheaf X.sheaf).obj.obj (op U) => r • overIsoSection L e)
      = fun r => m r := by
    funext r
    have h1 : (r • (((1 : (structureSheaf X.sheaf).obj.obj (op U)) :
          (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
            (op (Over.mk (𝟙 U))))) :
          (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
            (op (Over.mk (𝟙 U))))
        = ((r : (structureSheaf X.sheaf).obj.obj (op U)) :
          (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
            (op (Over.mk (𝟙 U)))) := mul_one r
    have h := m.hom.map_smul r (((1 : (structureSheaf X.sheaf).obj.obj (op U)) :
      (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
        (op (Over.mk (𝟙 U)))))
    exact h.symm.trans (congrArg (fun x => m.hom x) h1)
  rw [hfun]
  exact hm

/-- **A trivialization of `L` over `U` is a generator of `L` on `U`.** -/
noncomputable def generatorOfOverIso {U : Opens X.carrier}
    (e : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    GeneratorSections X L U :=
  ⟨overIsoSection L e, fun V h => by
    have hbij := bijective_smul_overIsoSection L (overIsoRestrict L h e)
    refine (funext fun r => ?_ : (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
      r • L.val.restrictₛₗ (homOfLE h).op (overIsoSection L e)) = _) ▸ hbij
    exact congrArg (fun z => r • z) (overIsoSection_restrict L h e)⟩

/-- The underlying section of the generator of a trivialization is its section
`overIsoSection L e`. -/
@[simp]
theorem generatorOfOverIso_val {U : Opens X.carrier}
    (e : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    (generatorOfOverIso L e).val = overIsoSection L e := rfl

/-- **The restriction law.** The generator of a trivialization restricts to the generator of the
restricted trivialization. -/
theorem generatorOfOverIso_restrict {U V : Opens X.carrier} (h : V ≤ U)
    (e : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    generatorRestrict L h (generatorOfOverIso L e) =
      generatorOfOverIso L (overIsoRestrict L h e) :=
  Subtype.ext (overIsoSection_restrict L h e)

/-! ### The converse: a generator trivializes the module -/

/-- The coordinate of a section in a restricted frame, with the containment `W ≤ U` supplied
rather than composed from `W ≤ V ≤ U`, so that a consumer can use the proof term its own goal
carries. This is the shape the naturality square of `overIsoOfGenerator` presents. -/
theorem generatorCoord_restrictLe {U V W : Opens X.carrier} (hV : V ≤ U) (hW : W ≤ U) (k : W ≤ V)
    (s : GeneratorSections X L U) (x : L.val.obj (op V)) :
    generatorCoord L (generatorRestrict L hW s) (L.val.map (homOfLE k).op x) =
      (structureSheaf X.sheaf).obj.map (homOfLE k).op
        (generatorCoord L (generatorRestrict L hV s) x) := by
  have h := generatorCoord_restrict L k (generatorRestrict L hV s) x
  rwa [generatorRestrict_trans L hV k s] at h

/-- **A generator of `L` on `U` trivializes `L` over `U`.** The component over an object
`V ⟶ U` of the localized site is the coordinate in the restricted frame, and its naturality is
`generatorCoord_restrictLe`. Together with `generatorOfOverIso` and the round trip
`generatorOfOverIso_overIsoOfGenerator` this makes the bridge two-sided. -/
noncomputable def overIsoOfGenerator {U : Opens X.carrier} (s : GeneratorSections X L U) :
    L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U) := by
  apply (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk
    (fun V => (generatorCoord L (generatorRestrict L V.unop.hom.le s)).toModuleIso) ?_
  exact fun V W g ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
    generatorCoord_restrictLe L V.unop.hom.le W.unop.hom.le g.unop.left.le s x)

/-- The section of the trivialization built from a generator is that generator. -/
theorem overIsoSection_overIsoOfGenerator {U : Opens X.carrier}
    (s : GeneratorSections X L U) :
    overIsoSection L (overIsoOfGenerator L s) = s.val :=
  Eq.trans (rfl : overIsoSection L (overIsoOfGenerator L s) =
      (1 : (structureSheaf X.sheaf).obj.obj (op U)) •
        (generatorRestrict L (Over.mk (CategoryTheory.CategoryStruct.id U)).hom.le s).val)
    ((one_smul _ _).trans (congrArg Subtype.val (generatorRestrict_self L U s)))

/-- **The bridge is two-sided**: the generator of the trivialization built from a generator is
that generator. -/
theorem generatorOfOverIso_overIsoOfGenerator {U : Opens X.carrier}
    (s : GeneratorSections X L U) :
    generatorOfOverIso L (overIsoOfGenerator L s) = s :=
  Subtype.ext (overIsoSection_overIsoOfGenerator L s)

/-- **The ratio law.** The transition unit of the generators of two trivializations of `L` over
`U` is the unit attached to the automorphism of `𝒪_U` comparing them. -/
theorem generatorRatioUnit_generatorOfOverIso {U : Opens X.carrier}
    (e e' : L.over U ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)) :
    generatorRatioUnit L U (generatorOfOverIso L e') (generatorOfOverIso L e) =
      unitAutValue (e.symm ≪≫ e') (op (Over.mk (𝟙 U))) := by
  refine generatorRatioUnit_eq L U _ _ _ ?_
  have hfac : e.inv = (e.inv ≫ e'.hom) ≫ e'.inv := by
    rw [Category.assoc, e'.hom_inv_id, Category.comp_id]
  have hval := congrArg (fun φ => φ.val.app (op (Over.mk (𝟙 U)))
    ((1 : (structureSheaf X.sheaf).obj.obj (op U)) :
      (_root_.SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val.obj
        (op (Over.mk (𝟙 U))))) hfac
  exact hval.trans (overUnitHomApply_eq_smul L e'.inv
    (unitAutValue (e.symm ≪≫ e') (op (Over.mk (𝟙 U)))).val)

/-- **Every transition unit of two generators is the comparison unit of two trivializations.**
With the ratio law this says the two descriptions of a transition unit — as a ratio of sections
and as an automorphism of `𝒪_U` — have the same range, so the hypothesis of
`isoOfOverIsoAutEq` is no weaker than the hypothesis of `isoOfTransitionEq`. In particular
`unitAutValue` is constant only if `L` has a single generator on `U`: by
`generatorRatio_spec` and `one_smul`, the left side is `1` exactly when `s` and `t` agree. -/
theorem generatorRatioUnit_eq_unitAutValue {U : Opens X.carrier}
    (s t : GeneratorSections X L U) :
    generatorRatioUnit L U s t =
      unitAutValue
        ((overIsoOfGenerator L t).symm ≪≫ overIsoOfGenerator L s) (op (Over.mk (𝟙 U))) :=
  (congrArg₂ (generatorRatioUnit L U) (generatorOfOverIso_overIsoOfGenerator L s).symm
        (generatorOfOverIso_overIsoOfGenerator L t).symm).trans
    (generatorRatioUnit_generatorOfOverIso L (overIsoOfGenerator L t) (overIsoOfGenerator L s))

/-! ### Comparing two modules through their trivializations -/

section Charts

variable {ι : Type u} {U : ι → Opens X.carrier}

/-- **The transition units of two families of generators need only be compared on the pairwise
intersections.** Any open contained in two charts factors through their intersection, and
`generatorRatioUnit_restrict` transports the comparison along that factorization. -/
noncomputable def isoOfTransitionEqInf
    {M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (g : ∀ i, GeneratorSections X L (U i)) (k : ∀ i, GeneratorSections X M (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    (heq : ∀ i j : ι,
      generatorRatioUnit L (U i ⊓ U j)
          (generatorRestrict L (inf_le_right : U i ⊓ U j ≤ U j) (g j))
          (generatorRestrict L (inf_le_left : U i ⊓ U j ≤ U i) (g i)) =
        generatorRatioUnit M (U i ⊓ U j)
          (generatorRestrict M (inf_le_right : U i ⊓ U j ≤ U j) (k j))
          (generatorRestrict M (inf_le_left : U i ⊓ U j ≤ U i) (k i))) :
    L ≅ M :=
  isoOfTransitionEq L g k hU fun i j V hi hj => by
    have hV : V ≤ U i ⊓ U j := le_inf hi hj
    have hL := (congrArg₂ (generatorRatioUnit L V)
          (generatorRestrict_trans L (inf_le_right : U i ⊓ U j ≤ U j) hV (g j))
          (generatorRestrict_trans L (inf_le_left : U i ⊓ U j ≤ U i) hV (g i))).symm.trans
        (generatorRatioUnit_restrict L hV
          (generatorRestrict L (inf_le_right : U i ⊓ U j ≤ U j) (g j))
          (generatorRestrict L (inf_le_left : U i ⊓ U j ≤ U i) (g i)))
    have hM := (congrArg₂ (generatorRatioUnit M V)
          (generatorRestrict_trans M (inf_le_right : U i ⊓ U j ≤ U j) hV (k j))
          (generatorRestrict_trans M (inf_le_left : U i ⊓ U j ≤ U i) hV (k i))).symm.trans
        (generatorRatioUnit_restrict M hV
          (generatorRestrict M (inf_le_right : U i ⊓ U j ≤ U j) (k j))
          (generatorRestrict M (inf_le_left : U i ⊓ U j ≤ U i) (k i)))
    refine hL.trans (Eq.trans ?_ hM.symm)
    exact congrArg _ (heq i j)

/-- **Two modules trivialized on a common covering family, with the same comparison automorphisms
on the pairwise intersections, are isomorphic.**

This is the form in which a construction carried out chart by chart is transported back to the
modules it came from: the comparison automorphism of two trivializations is produced in the
isomorphism calculus, where a tensor-power or pullback comparison lives, rather than on sections.
Trivializing both modules on a *common* cover is not enough — the automorphisms are the
content. -/
noncomputable def isoOfOverIsoAutEq
    {M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (e : ∀ i, L.over (U i) ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over (U i)))
    (f : ∀ i, M.over (U i) ≅ _root_.SheafOfModules.unit ((structureSheaf X.sheaf).over (U i)))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    (heq : ∀ i j : ι,
      unitAutValue
          ((overIsoRestrict L (inf_le_left : U i ⊓ U j ≤ U i) (e i)).symm ≪≫
            overIsoRestrict L (inf_le_right : U i ⊓ U j ≤ U j) (e j))
          (op (Over.mk (𝟙 (U i ⊓ U j)))) =
        unitAutValue
          ((overIsoRestrict M (inf_le_left : U i ⊓ U j ≤ U i) (f i)).symm ≪≫
            overIsoRestrict M (inf_le_right : U i ⊓ U j ≤ U j) (f j))
          (op (Over.mk (𝟙 (U i ⊓ U j))))) :
    L ≅ M :=
  isoOfTransitionEqInf L (fun i => generatorOfOverIso L (e i))
    (fun i => generatorOfOverIso M (f i)) hU fun i j => by
      have hL := (congrArg₂ (generatorRatioUnit L (U i ⊓ U j))
            (generatorOfOverIso_restrict L (inf_le_right : U i ⊓ U j ≤ U j) (e j))
            (generatorOfOverIso_restrict L (inf_le_left : U i ⊓ U j ≤ U i) (e i))).trans
          (generatorRatioUnit_generatorOfOverIso L
            (overIsoRestrict L (inf_le_left : U i ⊓ U j ≤ U i) (e i))
            (overIsoRestrict L (inf_le_right : U i ⊓ U j ≤ U j) (e j)))
      have hM := (congrArg₂ (generatorRatioUnit M (U i ⊓ U j))
            (generatorOfOverIso_restrict M (inf_le_right : U i ⊓ U j ≤ U j) (f j))
            (generatorOfOverIso_restrict M (inf_le_left : U i ⊓ U j ≤ U i) (f i))).trans
          (generatorRatioUnit_generatorOfOverIso M
            (overIsoRestrict M (inf_le_left : U i ⊓ U j ≤ U i) (f i))
            (overIsoRestrict M (inf_le_right : U i ⊓ U j ≤ U j) (f j)))
      exact hL.trans ((heq i j).trans hM.symm)

end Charts

end Stacks.SheafOfModules

end

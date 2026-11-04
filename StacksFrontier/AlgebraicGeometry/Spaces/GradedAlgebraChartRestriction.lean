module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.SheafifyRestrict
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Restricting a graded algebra on an algebraic space to an étale scheme chart

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `𝒜` be a graded
`𝒪_X`-algebra, with its homogeneous pieces living on the small étale site of `X`.  An étale chart
`V` of `X` has an underlying scheme, and this file restricts `𝒜` to that scheme, producing a
graded algebra `𝒜|_V` in the sense of Situation 01NN — the form in which the results on the
relative Proj of a *scheme* are stated.

This is the operation that lets a statement about the relative Proj of an algebraic space be
reduced to the case of schemes on an étale chart.  Before this file the single-module half of the
restriction was available as `AlgebraicGeometry.Space.restrictToChartScheme`, but its graded
companion was not, so no reduction could be carried out.

The restriction is built in three steps, none of which is a sheafification of the
multiplication.  The homogeneous pieces are restricted along the chart as presheaves of modules:
the sections are first raised in universe, then reindexed along
`AlgebraicGeometry.Space.openChartFunctor`, which reads a Zariski open of the chart's scheme as an
étale chart of `X`.  Both operations are objectwise on sections, so the multiplication, the unit
and the associativity and unit laws of `𝒜` transport across them verbatim.  Only then is the
result sheafified for the Zariski topology, by `Stacks.GradedAlgebra.sheafify`, which already
extends a multiplication along the sheafification units.

## Main definitions

* `AlgebraicGeometry.Space.chartAlgebraPiece`: the degree-`n` piece of `𝒜`, restricted to the
  chart as a presheaf of modules on the Zariski site of the chart's scheme.
* `AlgebraicGeometry.Space.chartAlgebraMul` and `AlgebraicGeometry.Space.chartAlgebraOne`: the
  multiplication and unit of `𝒜`, read on the opens of the chart.
* `AlgebraicGeometry.Space.chartPresheafAlgebra`: the restricted pieces as a graded algebra of
  presheaves of modules.
* `AlgebraicGeometry.Space.chartSheafAlgebra`: its Zariski sheafification, a sheaf of graded
  algebras on the chart's scheme.
* `AlgebraicGeometry.Space.relativeProjChartAlgebra`: **the restriction `𝒜|_V` as graded algebra
  data in the sense of Situation 01NN**, which is what the scheme-level theory consumes.

## Main results

* `AlgebraicGeometry.Space.chartSheafAlgebra_piece`: the homogeneous pieces of the restricted
  graded algebra are exactly the module restrictions
  `AlgebraicGeometry.Space.restrictToChartScheme` of the pieces of `𝒜`.  This holds by
  definition, and it is what lets a hypothesis about the module restrictions be used for the
  graded one.
* `AlgebraicGeometry.Space.restrictToChartScheme_section_eq_zero`: a module whose sections all
  vanish has a chart restriction whose sections all vanish.  The sheafification is not injective
  on sections, so this is proved by descending along the sheafification unit, which is locally
  surjective.
* `AlgebraicGeometry.Space.chartSheafAlgebra_isCommutative` and
  `AlgebraicGeometry.Space.chartSheafAlgebra_vanishesInNegativeDegrees`: commutativity and
  concentration in nonnegative degrees pass to the restriction.

## Implementation notes

**Why the pieces are restricted as presheaves and sheafified only at the end.**  Transporting a
graded algebra along a composite of functors of sheaves of modules would need that composite to
be lax monoidal, which is what `Stacks.GradedAlgebra.transport` asks for; no such structure is
available for the two functors here, and supplying one would mean building the monoidal
comparison for a change of site together with a universe lift.  None of that is needed: a
presheaf-level restriction is objectwise on sections, so the bilinear multiplication of `𝒜` can
simply be evaluated at the open read as an étale chart, and the heterogeneous associativity and
unit laws transport by `AlgebraicGeometry.Space.heq_ulift_up`.  The one genuinely non-objectwise
step, extending the multiplication along the sheafification units, is already done once and for
all by `Stacks.GradedAlgebra.sheafify`.

**The two carried inputs, and why they are inputs.**  `relativeProjChartAlgebra` takes
quasi-coherence of the module restrictions of the pieces as a hypothesis, `hqc`.  Quasi-coherence
of the pieces of `𝒜` is quasi-coherence on the *small étale site* of `X`; the restriction lives on
the *Zariski* site of the chart's scheme, and passing between them is the étale-to-Zariski
direction of Descent, Stacks 03DX, together with a drop of the presentation index types from
`Type (u + 1)` to `Type u`.  That direction is not in this library — the two clauses of
Stacks 03DX which are, `hasGlobalPresentation_of_isQuasicoherentOnSite` and
`isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, are a statement about an affine scheme's
own Zariski site and a statement about the small étale site of a space, neither of which
compares the two.  Carrying it is the library's established device in this situation: the
neighbouring `AlgebraicGeometry.Space.isLocallyProjective_restrictToChartScheme_of_isSurjective`
takes exactly this hypothesis, under the same name, and still carries its `stacks` attribute.  It
is an input and not a disguised conclusion: it speaks only of the pieces of `𝒜`, mentions no
chart-level statement, and is a property of a single module.

**Commutativity is a hypothesis on `𝒜`, not a field of it.**  `SheafOfModules.GradedAlgebra` is
not assumed commutative; commutativity, concentration in nonnegative degrees and quasi-coherence
are fields of `AlgebraicGeometry.Space.RelativeProjSituation` rather than of the bare algebra.
So the three appear here as explicit hypotheses, in the section-level form that the situation
supplies them.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

universe u

namespace AlgebraicGeometry.Space

/-- A heterogeneous equality of local sections is preserved by the universe lift of the
sections.  The two sides of every law of a graded algebra lie in the pieces of two degrees which
agree only propositionally, so the laws of the restricted algebra are obtained from those of the
original one through this transport. -/
theorem heq_ulift_up {α β : Type u} {a : α} {b : β} (h : HEq a b) :
    HEq (ULift.up.{u} a) (ULift.up.{u} b) := by
  obtain rfl := type_eq_of_heq h
  obtain rfl := eq_of_heq h
  rfl

section ChartRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS}

/-! ### The restricted pieces, as presheaves of modules on the chart -/

/-- The degree-`n` homogeneous piece of a graded algebra on an algebraic space, restricted to an
étale chart as a presheaf of modules on the Zariski site of the chart's scheme: the sections are
raised in universe and then reindexed along `AlgebraicGeometry.Space.openChartFunctor`, which
reads a Zariski open of the chart's scheme as an étale chart of the space.

Both steps are objectwise on sections, which is what lets the multiplication be transported
without any sheafification. -/
def chartAlgebraPiece
    (A : SheafOfModules.GradedAlgebra.{u, u, u, u + 1} (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1) (n : ℤ) :
    PresheafOfModules.{u} ((chartScheme V).ringCatSheaf.obj) :=
  (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 V)).obj
    ((SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} (A.piece n)).val)

variable (A : SheafOfModules.GradedAlgebra.{u, u, u, u + 1} (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1)

/-- The multiplication of a graded algebra on an algebraic space, read on the opens of an étale
chart: the bilinear multiplication of `𝒜` evaluated at the open regarded as an étale chart, with
the universe lift carried along.  Bilinearity over the structure sheaf of the chart's scheme
holds because the scalars act through
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`. -/
def chartAlgebraMul (i j : ℤ) :
    Stacks.BilinearMap (chartAlgebraPiece A V i) (chartAlgebraPiece A V j)
      (chartAlgebraPiece A V (i + j)) where
  app _ :=
    AddMonoidHom.mk'
      (fun x => AddMonoidHom.mk'
        (fun y => ULift.up ((A.mul i j).app _ x.down y.down))
        (fun y z => congrArg ULift.up (map_add ((A.mul i j).app _ x.down) y.down z.down)))
      (fun x z => by
        ext y
        exact congrArg ULift.up
          (DFunLike.congr_fun (map_add ((A.mul i j).app _) x.down z.down) y.down))
  map_smul_left _ _ x y :=
    congrArg ULift.up ((A.mul i j).map_smul_left _ _ x.down y.down)
  map_smul_right _ _ x y :=
    congrArg ULift.up ((A.mul i j).map_smul_right _ _ x.down y.down)
  naturality f x y :=
    congrArg ULift.up ((A.mul i j).naturality ((openChartFunctor B S hS X.1 V).op.map f)
      x.down y.down)

/-- The unit of a graded algebra on an algebraic space, read on the opens of an étale chart: the
global unit of `𝒜` evaluated at each open regarded as an étale chart.  It is compatible with
restriction because the unit of `𝒜` is. -/
def chartAlgebraOne : (chartAlgebraPiece A V 0).sections :=
  PresheafOfModules.sectionsMk
    (fun Y => ULift.up (A.one.eval ((openChartFunctor B S hS X.1 V).op.obj Y)))
    (fun {_ _} f => congrArg ULift.up
      (PresheafOfModules.sections_property A.one ((openChartFunctor B S hS X.1 V).op.map f)))

/-- **The restriction of a graded algebra to an étale chart, before sheafification.**  The
restricted pieces, with the restricted multiplication and unit, form a graded algebra of
presheaves of modules on the Zariski site of the chart's scheme.  Associativity and the two unit
laws are those of `𝒜`, transported by `AlgebraicGeometry.Space.heq_ulift_up`. -/
def chartPresheafAlgebra : Stacks.GradedAlgebra (chartAlgebraPiece A V) where
  mul i j := chartAlgebraMul A V i j
  one := chartAlgebraOne A V
  mul_assoc i j k _ x y z := heq_ulift_up (A.mul_assoc i j k _ x.down y.down z.down)
  one_mul i _ x := heq_ulift_up (A.one_mul i _ x.down)
  mul_one i _ x := heq_ulift_up (A.mul_one i _ x.down)

/-! ### Sheafifying for the Zariski topology -/

/-- **The restriction of a graded algebra on an algebraic space to an étale scheme chart.**  The
Zariski sheafification of the restricted presheaf graded algebra, by
`Stacks.GradedAlgebra.sheafify`, which extends the restricted multiplication along the
sheafification units of the pieces. -/
def chartSheafAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (chartScheme V).ringCatSheaf :=
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  (chartPresheafAlgebra A V).sheafify (𝟙 ((chartScheme V).ringCatSheaf.obj))

/-- The homogeneous pieces of the restricted graded algebra are the module restrictions of the
homogeneous pieces of `𝒜`.  This holds by definition: both are the Zariski sheafification of the
same reindexed, universe-lifted presheaf.  It is what lets a hypothesis about
`AlgebraicGeometry.Space.restrictToChartScheme` be used for the graded restriction. -/
theorem chartSheafAlgebra_piece (n : ℤ) :
    (chartSheafAlgebra A V).piece n =
      restrictToChartScheme B S hS X.1 X.2 (A.piece n) V :=
  rfl

/-! ### The properties of Situation 01NN, transported -/

/-- **A module all of whose sections vanish has a chart restriction all of whose sections
vanish.**  The restriction is a sheafification, which is not injective on sections, so this is
proved by descending along the sheafification unit: that unit is locally surjective, so every
section of the restriction locally comes from a section of the restricted presheaf, and those all
vanish. -/
theorem restrictToChartScheme_section_eq_zero (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ) (y : M.val.obj W), y = 0)
    (Y : ((chartScheme V).Opens)ᵒᵖ)
    (x : (restrictToChartScheme B S hS X.1 X.2 M V).val.obj Y) : x = 0 := by
  refine Stacks.eq_of_forall_lift
    ((restrictToChartScheme B S hS X.1 X.2 M V).isSheaf.isSeparated)
    (PresheafOfModules.sheafifyUnit (𝟙 (chartScheme V).ringCatSheaf.obj)
      ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS X.1 V)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val)) x x 0 ?_
  intro Z f m hm
  have hm0 : m = 0 := by
    refine (congrArg ULift.up (hM _ m.down)).trans ?_
    rfl
  rw [hm0, map_zero] at hm
  exact hm.symm.trans (map_zero _).symm

/-- **Commutativity passes to the chart restriction.**  The restricted presheaf multiplication is
commutative because that of `𝒜` is, and commutativity transfers along the sheafification units by
`Stacks.GradedAlgebra.heq_sheafify_mul_comm`. -/
theorem chartSheafAlgebra_isCommutative
    (hcomm : ∀ (i j : ℤ) (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) :
    IsCommutative (chartSheafAlgebra A V) := by
  intro i j U a b
  exact Stacks.GradedAlgebra.heq_sheafify_mul_comm
    (𝟙 ((chartScheme V).ringCatSheaf.obj)) (chartPresheafAlgebra A V)
    (fun i' j' _ x y => heq_ulift_up (hcomm i' j' _ x.down y.down)) i j U.unop a b

/-- **Concentration in nonnegative degrees passes to the chart restriction**, by
`AlgebraicGeometry.Space.restrictToChartScheme_section_eq_zero` applied to each piece of negative
degree. -/
theorem chartSheafAlgebra_vanishesInNegativeDegrees
    (hneg : ∀ (n : ℤ), n < 0 → ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (y : (A.piece n).val.obj W), y = 0) :
    VanishesInNegativeDegrees (chartSheafAlgebra A V) :=
  fun n hn U x =>
    restrictToChartScheme_section_eq_zero V (A.piece n) (hneg n hn) U x

/-! ### The restriction as graded algebra data of Situation 01NN -/

/-- **The restriction `𝒜|_V` of a graded algebra on an algebraic space to an étale scheme chart,
as graded algebra data in the sense of Situation 01NN.**  This is the object the scheme-level
theory of the relative Proj consumes, so it is what makes a reduction to the case of schemes on
an étale chart possible.

Commutativity and concentration in nonnegative degrees are transported from `𝒜`.  Quasi-coherence
of the restricted pieces is the hypothesis `hqc`; see the implementation notes for why it is
carried and why it is an input rather than a disguised conclusion. -/
@[stacks 01NN "the restriction of a graded algebra on an algebraic space to an étale scheme \
chart, as graded algebra data on the chart; granted quasi-coherence of the module restrictions \
of the homogeneous pieces, which is the étale-to-Zariski direction of Descent 03DX and is \
carried here in the same form as in the neighbouring Tag 060Q"]
def relativeProjChartAlgebra
    (hcomm : ∀ (i j : ℤ) (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hneg : ∀ (n : ℤ), n < 0 → ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (y : (A.piece n).val.obj W), y = 0)
    (hqc : ∀ n : ℤ, (restrictToChartScheme B S hS X.1 X.2 (A.piece n) V).IsQuasicoherent) :
    SheafGradedAlgebra (chartScheme V) :=
  toSheafGradedAlgebra (chartSheafAlgebra A V)
    (chartSheafAlgebra_isCommutative A V hcomm)
    (chartSheafAlgebra_vanishesInNegativeDegrees A V hneg)
    (fun n => hqc n)

/-- The homogeneous pieces of the restriction of Situation 01NN are the module restrictions of
the pieces of `𝒜`. -/
theorem relativeProjChartAlgebra_piece
    (hcomm : ∀ (i j : ℤ) (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hneg : ∀ (n : ℤ), n < 0 → ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (y : (A.piece n).val.obj W), y = 0)
    (hqc : ∀ n : ℤ, (restrictToChartScheme B S hS X.1 X.2 (A.piece n) V).IsQuasicoherent)
    (n : ℤ) :
    (relativeProjChartAlgebra A V hcomm hneg hqc).piece n =
      restrictToChartScheme B S hS X.1 X.2 (A.piece n) V :=
  rfl

end ChartRestriction

end AlgebraicGeometry.Space

end

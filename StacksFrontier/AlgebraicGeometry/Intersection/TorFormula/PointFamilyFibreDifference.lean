module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.AmbientFibreDifference
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSectionRationalEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# The graph construction of Tag 02RQ at an arbitrary pair of points of the projective line

The graph construction of Tag 02RQ attaches to a section `s` on an open `U` of a scheme `X` over
`S` the closure `Y` of the graph of the attached morphism `U ⟶ ℙ¹_S`, with its projections
`p : Y ⟶ X` and `q : Y ⟶ ℙ¹_S`, and reads off the identity

  `div_X(f) = [Y₀ ⊆ X]_{n-1} - [Y_∞ ⊆ X]_{n-1}`

at the two distinguished points `0` and `∞` of `ℙ¹_S` — part (6) of the tag, which is
`Stacks.Chow.principalDivisorCycle_eq_sub_imageCycles`. This file does the same at an arbitrary
pair of points `a`, `b` of the affine chart, attached to global functions `t`, `t'` on the base,
and uses it to *produce* the subvariety whose fibre difference at that pair is a given principal
divisor. That production is what part (3) of Tag 0B07 needs and what part (2) does not give:
part (2) says every such difference is rationally equivalent to zero, part (3) must exhibit, for
a cycle rationally equivalent to zero, subvarieties whose fibre differences at `a` and `b` it is.

## The shape of the argument

Let `g` be a unit section on `U`. The rational map `φ = (t - g t')/(1 - g) : U ⇢ ℙ¹_S` is the
unique one with `(φ - t)/(φ - t') = g`; it is `Stacks.Chow.mobiusSection`, and
`Stacks.Chow.mul_mobiusSection_sub` is that defining relation. Write `W` for the closure of its
graph. Then on `W`

* `div_W(z - t) = [W_t] - [W_∞]` and `div_W(z - t') = [W_{t'}] - [W_∞]`, the existing
  `Stacks.Chow.principalDivisorCycle_eq_sub_linePointFibreCycles` applied to `q`; subtracting
  cancels the two infinity terms, so no local equation at infinity is ever needed;
* the pullback of `g` along `p` is `(z - t)/(z - t')`, which is
  `Stacks.Chow.linePointFunction_graphLineProjection` — the shifted analogue of
  `Stacks.Chow.res_appLE_lineChartCoordinate` — together with
  `Stacks.Chow.germToFunctionField_graphProjection_app`;
* part (5) of the tag for an *arbitrary* rational function,
  `Stacks.Chow.principalDivisorCycle_eq_properPushforward_of_functionField`, pushes the identity
  down to `X`.

That gives part (6) at the pair, `Stacks.Chow.principalDivisorCycle_eq_sub_pointImageCycles`.
Transporting it from an integral closed subscheme `V ⊆ X` into `X ×_S ℙ¹_S` along
`V ×_S ℙ¹_S ⟶ X ×_S ℙ¹_S` gives `Stacks.Chow.exists_pointGraphFamilyMember`, the arbitrary-pair
analogue of `Stacks.Chow.exists_graphFamilyMember`.

### Where distinctness of the two points does its work

In exactly one place: `Stacks.Chow.isUnit_mobiusSection_sub_left` and
`Stacks.Chow.isUnit_mobiusSection_sub_right`, which compute

  `φ - t = g (t - t')/(1 - g)`,  `φ - t' = (t - t')/(1 - g)`

and conclude that both are invertible *because `t - t'` is*. Invertibility of `t - t'` is the
source's `a ≠ b`: over an algebraically closed field `Γ(S, ⊤)` is the ground field and the two
agree, which is `Stacks.Chow.isUnit_baseSectionOn_sub`. It is not decoration. The two
invertibilities are what put the graph of `φ` off the sections at `t` and at `t'`, so that the
two fibre cycles are defined at all, and for `t = t'` the conclusion is false: the right-hand
side of the fibre-difference identity vanishes for every `W`, while a principal divisor need not.

## Main definitions

* `Stacks.Chow.baseSectionOn` — a global function on the base, read on an open of `X`.
* `Stacks.Chow.mobiusSection` — the section `φ = (t - g t')/(1 - g)`.

## Main results

The shifted coordinate on the graph closure:

* `Stacks.Chow.graphLineProjection_comp_over` — the two projections agree over the base.
* `Stacks.Chow.res_appTop_baseSectionOn` — the pullback of a base function along `q`, restricted
  to `p⁻¹(U)`, is its pullback along `p`.
* `Stacks.Chow.lineChartFunction_graphLineProjection`,
  `Stacks.Chow.lineBaseFunction_graphLineProjection` and
  `Stacks.Chow.linePointFunction_graphLineProjection` — **`z - t` on the graph closure is the
  pullback of `s - t`.**

The fibre at an arbitrary point:

* `Stacks.Chow.isClosedImmersion_graphPointFiber_comp` — `Y_t ⟶ Y` is a closed immersion.
* `Stacks.Chow.pointFiber_graphFamilyMember` and
  `Stacks.Chow.cycleAssociatedToClosedSubscheme_pointFiber_graphFamilyMember` — **the fibre at
  `t` of the graph family member**, with its cycle.
* `Stacks.Chow.notMem_support_lineSectionKer_sectionToLine` and
  `Stacks.Chow.notMem_support_comap_lineSectionKer_genericPoint` — the graph of a section `s`
  with `s - t` invertible misses the section at `t`.
* `Stacks.Chow.range_pointSection_eq_preimage` and
  `Stacks.Chow.notSubset_range_pointSection_graphFamilyMember` — the member meets the section at
  `t` properly.

Parts (5) and (6) at the pair:

* `Stacks.Chow.principalDivisorCycle_mul` — the principal divisor of a product.
* `Stacks.Chow.principalDivisorCycle_eq_properPushforward_of_functionField` — **part (5) of Tag
  02RQ for an arbitrary rational function on `X`.**
* `Stacks.Chow.principalDivisorCycle_eq_sub_pointImageCycles` — **part (6) of Tag 02RQ at an
  arbitrary pair of points of the affine chart.**
* `Stacks.Chow.principalDivisorCycle_eq_sub_pointImageCycles_mobius` — the same for the Möbius
  section, where the hypothesis relating the rational function to the section is discharged.
* `Stacks.Chow.principalDivisorPushforward_eq_sub_pointFibreCycles` — the identity carried from
  `V` to `X`.
* `Stacks.Chow.exists_pointGraphFamilyMember` — **the subvariety of `X ×_S ℙ¹_S` realising
  `pr_{X,*}(div_V(g))` as `[W_t]_k - [W_{t'}]_k`.**

## Implementation notes

As throughout Tag 02RQ every statement about the graph closure carries `[QuasiCompact U.ι]`; see
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles`.

The identities about the shifted coordinate are proved on sections over `p⁻¹(U)` and only then
read at the generic point: the two sections `z - t` and `p^♯(s - t)` agree on `p⁻¹(U)` already,
and `TopCat.Presheaf.germ_res_apply` moves that to the function field. Nothing is done at the
level of stalks.

`Stacks.Chow.principalDivisorCycle_eq_sub_pointImageCycles` takes the rational function `a` as a
variable subject to `a (g - t') = g - t` rather than constructing it from `g`. That is what lets
`Stacks.Chow.principalDivisorPushforward_eq_sub_pointFibreCycles` be applied with the Möbius
section as the section the graph is built from and the *original* rational function as `a`; the
`(0, ∞)` statements can take the rational function to be the one the graph was built from, and
at an arbitrary pair that is exactly what fails.

### How part (3) of Tag 0B07 at an arbitrary pair uses this file

`Stacks.Chow.exists_pointGraphFamilyMember` produces the subvariety from three invertibility
hypotheses: `t - t'`, which is the source's `a ≠ b`; and `1 - g₀` and `t - g₀ t'`, which are
*not* the source's and which the source does not need, because it works with the full rational
map `φ` while the graph construction of Tag 02RQ, as the repository has it, starts from a unit
*section*. Those two are discharged in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointFamilyFibreDifferenceExistence`, by
shrinking `U` to the basic open of `(1 - g₀)(t - g₀ t')` — again affine, and nonempty hence
dense unless one factor vanishes identically — together with the two degenerate cases `g₀ = 1`
and `t = g₀ t'`, in both of which `div_V(g₀) = 0`.

That file also assembles the members into a locally finite family and identifies the group they
generate with the cycles rationally equivalent to zero, which is Tag 0AZI at the pair; and
`Stacks.Chow.PointCycle.isPointFibreIntersectionDifference_of_mem_rationalEquivalences` restates
the conclusion with the Section 43.14 products of Tag 0AZR, which is the shape of
`Stacks.Chow.IsFibreIntersectionDifference`. What is still missing from part (3) at a genuinely
arbitrary pair of closed points is the pair with one point at infinity: everything above is for
two points of the affine chart. No tag is registered on anything in this file.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 0AZI](https://stacks.math.columbia.edu/tag/0AZI)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- Every open is contained in the inverse image of the whole target. -/
private theorem le_preimage_top {A B : Scheme.{u}} (f : A ⟶ B) (V : A.Opens) :
    V ≤ f ⁻¹ᵁ ⊤ := by simp

/-- Pulling a global section back to the whole source is `Scheme.Hom.appTop`. -/
private theorem appLE_top_eq_appTop {A B : Scheme.{u}} (f : A ⟶ B)
    (e : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ e = f.appTop := by
  have h : f.appLE (⊤ : B.Opens) (⊤ : A.Opens) e =
      f.appTop ≫ A.presheaf.map (𝟙 (Opposite.op (⊤ : A.Opens))) :=
    congrArg (fun φ => f.appTop ≫ A.presheaf.map φ) (Subsingleton.elim _ _)
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### A global function on the base, read on an open of `X` -/

/-- A global function on the base, pulled back along `sX` and restricted to an open of `X`. -/
def baseSectionOn {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (t : Γ(S, ⊤)) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (sX.appTop t)

section Graph

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) (t : Γ(S, ⊤))

/-- The two projections of the graph closure agree over the base. -/
theorem graphLineProjection_comp_over :
    graphLineProjection sX U s ≫ (relativeProjectiveLine S ↘ S) =
      graphProjection sX U s ≫ sX := by
  rw [show graphLineProjection sX U s = graphClosureι sX U s ≫
      pullback.snd sX (relativeProjectiveLine S ↘ S) from rfl,
    show graphProjection sX U s = graphClosureι sX U s ≫
      pullback.fst sX (relativeProjectiveLine S ↘ S) from rfl,
    Category.assoc, Category.assoc, pullback.condition]

/-- The pullback of a global function on the base along the structure morphism of the graph
closure, restricted to `p⁻¹(U)`, is the pullback along `p` of that function read on `U`. -/
theorem res_appTop_baseSectionOn :
    (graphClosure sX U s).presheaf.map
        (homOfLE (le_top : graphPreimage sX U s ≤ ⊤)).op
        ((graphBaseMorphism sX U s).appTop t) =
      ((graphProjection sX U s).app U) (baseSectionOn sX U t) := by
  have h1 : (graphBaseMorphism sX U s).appTop ≫ (graphClosure sX U s).presheaf.map
        (homOfLE (le_top : graphPreimage sX U s ≤ ⊤)).op =
      (graphBaseMorphism sX U s).appLE ⊤ (graphPreimage sX U s)
        (le_preimage_top (graphProjection sX U s ≫ sX) (graphPreimage sX U s)) := by
    rw [← appLE_top_eq_appTop (graphBaseMorphism sX U s)
      (le_preimage_top (graphProjection sX U s ≫ sX) ⊤), Scheme.Hom.appLE_map]
  have h2 : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (graphProjection sX U s).app U =
      (graphProjection sX U s).appLE ⊤ (graphPreimage sX U s)
        (le_preimage_top (graphProjection sX U s) (graphPreimage sX U s)) := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.map_appLE]
  rw [show (graphClosure sX U s).presheaf.map (homOfLE (le_top : graphPreimage sX U s ≤ ⊤)).op
        ((graphBaseMorphism sX U s).appTop t) =
      ((graphBaseMorphism sX U s).appTop ≫ (graphClosure sX U s).presheaf.map
        (homOfLE (le_top : graphPreimage sX U s ≤ ⊤)).op) t from
      (ConcreteCategory.comp_apply _ _ _).symm, h1, baseSectionOn,
    show ((graphProjection sX U s).app U)
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (sX.appTop t)) =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (graphProjection sX U s).app U)
        (sX.appTop t) from (ConcreteCategory.comp_apply _ _ _).symm, h2,
    Scheme.Hom.comp_appLE (graphProjection sX U s) sX ⊤ (graphPreimage sX U s)
      (le_preimage_top (graphProjection sX U s ≫ sX) (graphPreimage sX U s)),
    ConcreteCategory.comp_apply]
  rfl

end Graph

/-! ### The shifted chart coordinate on the graph closure -/

section Function

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (g : (Γ(X, U))ˣ) [QuasiCompact U.ι]
  [IsIntegral (graphClosure sX U ↑g)] [Nonempty (graphPreimage sX U ↑g)]

/-- **The coordinate `z` of the first chart, read as a rational function on the graph closure, is
the pullback along `p` of the section the graph was built from.** -/
theorem lineChartFunction_graphLineProjection
    (hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g)
    (hη1 : genericPoint (graphClosure sX U ↑g) ∈
      graphLineProjection sX U ↑g ⁻¹ᵁ chartOpen S) :
    lineChartFunction (graphLineProjection sX U ↑g) hη1 =
      (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
        (((graphProjection sX U ↑g).app U) (g : Γ(X, U))) := by
  have hWA : graphPreimage sX U ↑g ≤ graphLineProjection sX U ↑g ⁻¹ᵁ (affineChart S ''ᵁ ⊤) :=
    graphPreimage_le_preimage_image_chart sX U g (affineChart S) (g : Γ(X, U)) rfl
  have : Nonempty (graphLineProjection sX U ↑g ⁻¹ᵁ chartOpen S) := ⟨⟨_, hη1⟩⟩
  rw [← res_appLE_lineChartCoordinate sX U g (affineChart S) (g : Γ(X, U)) rfl hWA]
  exact ((graphClosure sX U ↑g).presheaf.germ_res_apply (homOfLE hWA)
    (genericPoint (graphClosure sX U ↑g)) hηW _).symm

omit [QuasiCompact U.ι] in
/-- A global function on the base, read as a rational function on the graph closure, is the
pullback along `p` of that function read on `U`. -/
theorem lineBaseFunction_graphLineProjection (t : Γ(S, ⊤))
    (hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g) :
    lineBaseFunction (graphLineProjection sX U ↑g) t =
      (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
        (((graphProjection sX U ↑g).app U) (baseSectionOn sX U t)) := by
  have h2 : lineBaseFunction (graphLineProjection sX U ↑g) t =
      (graphClosure sX U ↑g).presheaf.germ ⊤ (genericPoint (graphClosure sX U ↑g)) trivial
        ((graphBaseMorphism sX U ↑g).appTop t) := by
    rw [show graphBaseMorphism sX U (g : Γ(X, U)) =
      graphLineProjection sX U ↑g ≫ (relativeProjectiveLine S ↘ S) from
      (graphLineProjection_comp_over sX U (g : Γ(X, U))).symm]
    rfl
  rw [h2, ← res_appTop_baseSectionOn sX U (g : Γ(X, U)) t]
  exact ((graphClosure sX U ↑g).presheaf.germ_res_apply
    (homOfLE (le_top : graphPreimage sX U ↑g ≤ ⊤))
    (genericPoint (graphClosure sX U ↑g)) hηW _).symm

/-- **The shifted analogue of `Stacks.Chow.res_appLE_lineChartCoordinate`.** The rational
function `z - t` on the graph closure is the pullback along `p` of the section `g - t` on `U`.
At `t = 0` it is `Stacks.Chow.lineChartFunction_graphLineProjection`. -/
theorem linePointFunction_graphLineProjection (t : Γ(S, ⊤))
    (hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g)
    (hη1 : genericPoint (graphClosure sX U ↑g) ∈
      graphLineProjection sX U ↑g ⁻¹ᵁ chartOpen S) :
    linePointFunction (graphLineProjection sX U ↑g) t hη1 =
      (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
        (((graphProjection sX U ↑g).app U) ((g : Γ(X, U)) - baseSectionOn sX U t)) := by
  rw [linePointFunction_eq_sub, lineChartFunction_graphLineProjection sX U g hηW hη1,
    lineBaseFunction_graphLineProjection sX U g t hηW, map_sub, map_sub]

end Function

/-! ### The fibre of the graph family member at an arbitrary point -/

/-- `Y_t ⟶ Y` is a closed immersion: the fibre of the graph closure at the point attached to
`t` is a closed subscheme of the scheme the graph was taken over. This is the arbitrary-point
analogue of `Stacks.Chow.isClosedImmersion_graphZeroFiber_comp`. -/
instance isClosedImmersion_graphPointFiber_comp {Y S : Scheme.{u}} (sY : Y ⟶ S) (U : Y.Opens)
    (s : Γ(Y, U)) (t : Γ(S, ⊤)) :
    IsClosedImmersion
      (((lineSection S t).ker.comap (graphLineProjection sY U s)).subschemeι ≫
        graphProjection sY U s) :=
  isClosedImmersion_comap_sectionKer_comp (lineSection S t) sY (lineSection_comp S t)
    (graphClosureι sY U s)

section PointFiber

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsClosedImmersion i] (U : Y.Opens)
  (s : Γ(Y, U)) (t : Γ(S, ⊤))

/-- **The fibre at `t` of the graph family member is the fibre at `t` of the graph closure, read
in `X`.** This is the arbitrary-point analogue of `Stacks.Chow.zeroFiber_graphFamilyMember`. -/
theorem pointFiber_graphFamilyMember :
    pointFiber f t (graphFamilyMember f i U s) =
      ((lineSection S t).ker.comap (graphLineProjection (i ≫ f) U s)).map
        (graphProjection (i ≫ f) U s ≫ i) := by
  rw [pointFiber, graphFamilyMember,
    comap_ker_section_eq_map f (pointSection f t) (pointSection_comp_fst f t)
      (graphFamilyInclusion f i U s),
    ker_pointSection, ← Scheme.IdealSheafData.comap_comp,
    graphFamilyInclusion_comp_fst, graphFamilyInclusion_comp_snd]

end PointFiber

/-- The cycle of the fibre at `t` of the graph family member is the cycle of the fibre at `t` of
the graph closure, read as a closed subscheme of `X`. -/
theorem cycleAssociatedToClosedSubscheme_pointFiber_graphFamilyMember
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (U : Y.Opens) (s : Γ(Y, U))
    (t : Γ(C.S, ⊤)) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C f
        ((((lineSection C.S t).ker.comap (graphLineProjection (i ≫ f) U s)).subschemeι ≫
          graphProjection (i ≫ f) U s) ≫ i) k =
      cycleAssociatedToClosedSubscheme C f
        (pointFiber f t (graphFamilyMember f i U s)).subschemeι k := by
  have hker : Scheme.Hom.ker
      ((((lineSection C.S t).ker.comap (graphLineProjection (i ≫ f) U s)).subschemeι ≫
        graphProjection (i ≫ f) U s) ≫ i) = pointFiber f t (graphFamilyMember f i U s) := by
    rw [Category.assoc, pointFiber_graphFamilyMember]
    rfl
  rw [cycleAssociatedToClosedSubscheme_ker C f
    ((((lineSection C.S t).ker.comap (graphLineProjection (i ≫ f) U s)).subschemeι ≫
      graphProjection (i ≫ f) U s) ≫ i) k, hker]

/-! ### The graph misses the section at an arbitrary point -/

section Nondegenerate

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) (t : Γ(S, ⊤))

/-- The morphism `U ⟶ 𝔸¹_S` attached to a section lies over `S`. -/
theorem sectionToAffineLine_comp :
    sectionToAffineLine sX U s ≫ affineLineOverHom S = U.ι ≫ sX :=
  pullback.lift_fst _ _ _

/-- The pullback of a global function on the base along `U ⟶ 𝔸¹_S` is that function read on
`U`. -/
theorem sectionToAffineLine_appTop_base :
    (sectionToAffineLine sX U s).appTop ((affineLineOverHom S).appTop t) =
      U.topIso.inv (baseSectionOn sX U t) := by
  have hL : (sectionToAffineLine sX U s).appTop ((affineLineOverHom S).appTop t) =
      U.ι.appTop (sX.appTop t) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, sectionToAffineLine_comp,
      Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  have key : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ U.topIso.inv = U.ι.appTop := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact (X.presheaf.map_comp _ _).symm.trans
      (congrArg X.presheaf.map (Subsingleton.elim _ _))
  rw [hL, baseSectionOn,
    show U.topIso.inv
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (sX.appTop t)) =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ U.topIso.inv) (sX.appTop t) from
      (ConcreteCategory.comp_apply _ _ _).symm, key]

/-- **The pullback of `z - t` along the morphism `U ⟶ 𝔸¹_S` attached to a section `s` is
`s - t`.** -/
theorem sectionToAffineLine_appTop_pointCoordinate :
    (sectionToAffineLine sX U s).appTop
        (affineCoordinate S - (affineLineOverHom S).appTop t) =
      U.topIso.inv (s - baseSectionOn sX U t) := by
  rw [map_sub, map_sub, sectionToAffineLine_appTop_affineCoordinate,
    sectionToAffineLine_appTop_base]

/-- The shifted coordinate does not vanish anywhere on the image of `U ⟶ 𝔸¹_S` attached to a
section `s` with `s - t` invertible: that coordinate pulls back to `s - t`. This is the
arbitrary-point analogue of `Stacks.Chow.mem_basicOpen_affineCoordinate`. -/
theorem mem_basicOpen_affinePointCoordinate (hu : IsUnit (s - baseSectionOn sX U t))
    (x : U.toScheme) :
    (sectionToAffineLine sX U s).base x ∈
      (affineLineOver S).basicOpen (affineCoordinate S - (affineLineOverHom S).appTop t) := by
  have h := Scheme.preimage_basicOpen_top (sectionToAffineLine sX U s)
    (affineCoordinate S - (affineLineOverHom S).appTop t)
  rw [sectionToAffineLine_appTop_pointCoordinate] at h
  have hx : x ∈ U.toScheme.basicOpen (U.topIso.inv (s - baseSectionOn sX U t)) := by
    rw [Scheme.basicOpen_of_isUnit _ (IsUnit.map U.topIso.inv.hom hu)]
    trivial
  rw [← h] at hx
  exact hx

/-- **The divisor at `t` does not meet the image of the morphism `U ⟶ ℙ¹_S` attached to a
section `s` with `s - t` invertible**: on the affine chart that divisor is cut out by `z - t`,
which pulls back to `s - t`. This is the arbitrary-point analogue of
`Stacks.Chow.notMem_support_lineZeroDivisor_sectionToLine`. -/
theorem notMem_support_lineSectionKer_sectionToLine (hu : IsUnit (s - baseSectionOn sX U t))
    (x : U.toScheme) :
    (sectionToLine sX U s).base x ∉
      ((lineSection S t).ker.support : Set (relativeProjectiveLine S)) := by
  intro hx
  have hz : (sectionToAffineLine sX U s).base x ∈
      ((lineSection S t).ker.comap (affineChart S)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  obtain ⟨B, hzB⟩ := Stacks.Divisors.exists_affineOpens_mem
    ((sectionToAffineLine sX U s).base x)
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hzB,
    lineSectionKer_ideal_comap_affineChart S t, Scheme.mem_zeroLocus_iff] at hz
  refine hz _ (Ideal.subset_span rfl) ?_
  rw [Scheme.basicOpen_res]
  exact ⟨hzB, mem_basicOpen_affinePointCoordinate sX U s t hu x⟩

end Nondegenerate

/-- **The generic point of the graph closure is not in the fibre at `t`**, as soon as `g - t` is
invertible on `U`: that generic point is the image of the generic point of `U`, whose image in
`ℙ¹_S` misses the divisor at `t`. This is the arbitrary-point analogue of
`Stacks.Chow.notMem_support_graphZeroFiber_genericPoint`. -/
theorem notMem_support_comap_lineSectionKer_genericPoint {X S : Scheme.{u}} (sX : X ⟶ S)
    (U : X.Opens) (g : (Γ(X, U))ˣ) [IsIntegral X] [QuasiCompact U.ι] [Nonempty U.toScheme]
    [IsIntegral (graphClosure sX U ↑g)] (t : Γ(S, ⊤))
    (hu : IsUnit ((g : Γ(X, U)) - baseSectionOn sX U t)) :
    genericPoint (graphClosure sX U ↑g) ∉
      (((lineSection S t).ker.comap (graphLineProjection sX U ↑g)).support :
        Set (graphClosure sX U ↑g)) := by
  rw [← genericPoint_graphClosure sX U ↑g, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage]
  intro h
  refine notMem_support_lineSectionKer_sectionToLine sX U (g : Γ(X, U)) t hu
    (genericPoint U.toScheme) ?_
  rw [← graphInclusion_comp_graphLineProjection sX U ↑g]
  exact h

/-! ### Part (5) of Tag 02RQ for an arbitrary rational function -/

/-- The principal divisor of a product of nonzero rational functions is the sum of the principal
divisors. This is `Stacks.Chow.principalCycle_mul` read in the group of cycles. -/
theorem principalDivisorCycle_mul (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C sX = (n : EInt)) {a b : X.functionField}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    principalDivisorCycle C sX hn (a * b) =
      principalDivisorCycle C sX hn a + principalDivisorCycle C sX hn b := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine Subtype.ext ?_
  rw [AddSubgroup.coe_add]
  exact principalCycle_mul X ha hb

section Dominant

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (g : (Γ(X, U))ˣ) [IsIntegral X]
  [QuasiCompact U.ι] [Nonempty U.toScheme] [IsIntegral (graphClosure sX U ↑g)]
  [Nonempty (graphPreimage sX U ↑g)]

/-- The pullback along `p` of a section on `U`, read as a rational function on the graph closure,
is the image of its rational function on `X` under the function-field map of `p`. -/
theorem germToFunctionField_graphProjection_app (a : Γ(X, U)) :
    (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
        (((graphProjection sX U ↑g).app U) a) =
      dominantFunctionFieldMap (graphProjection sX U ↑g) (X.germToFunctionField U a) := by
  have h := DFunLike.congr_fun (appLE_germToFunctionField_commutes (graphProjection sX U ↑g) U
    (graphPreimage sX U ↑g) le_rfl) a
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

end Dominant

/-- **Part (5) of Tag 02RQ for an arbitrary rational function on `X`.** The principal divisor of
any nonzero rational function on `X` is the proper pushforward along `p : Y ⟶ X` of the principal
divisor of its pullback to the graph closure.

`Stacks.Chow.principalDivisorCycle_eq_properPushforward` is this for the one rational function
the graph was built from; the proof is the same, Tag 02RT applied to `p`, whose function-field
extension has degree one, so that the norm occurring there is the identity
(`Stacks.Chow.norm_dominantFunctionFieldMap_graphProjection`). -/
theorem principalDivisorCycle_eq_properPushforward_of_functionField (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens)
    [QuasiCompact U.ι] [Nonempty U.toScheme] (g : (Γ(X, U))ˣ) {n : ℤ}
    (hn : schemeDeltaDimension C sX = (n : EInt)) (a : X.functionField) (ha : a ≠ 0)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g)) :
    letI : IsIntegral (graphClosure sX U ↑g) := hYint
    letI : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) := hYft
    ∀ hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt),
      principalDivisorCycle C sX hn a =
        properPushforward C (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl (n - 1)
          (principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
            (dominantFunctionFieldMap (graphProjection sX U ↑g) a)) := by
  intro hYdim
  have := hYint
  have := hYft
  have : IsProper (graphProjection sX U ↑g) := graphProjection_isProper sX U ↑g
  have hane : dominantFunctionFieldMap (graphProjection sX U ↑g) a ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap (graphProjection sX U ↑g)).injective).2 ha
  rw [properPushforward_principalDivisorCycle C (graphBaseMorphism sX U ↑g) sX hYdim hn
    (graphProjection sX U ↑g) rfl _ hane]
  exact (congrArg (principalDivisorCycle C sX hn)
    (norm_dominantFunctionFieldMap_graphProjection sX U ↑g a)).symm

/-! ### Part (6) of Tag 02RQ at an arbitrary pair of points of the affine chart -/

/-- **The principal divisor on `X` as a difference of the two fibre cycles at an arbitrary pair
of points of the affine chart.** Let `U ⊆ X` be a dense open on which `g` is invertible, and let
`t`, `t'` be global functions on the base with `g - t` and `g - t'` invertible on `U` — that is,
the graph of `g` meets neither the section at `t` nor the section at `t'`. Then for every nonzero
rational function `a` on `X` satisfying `a · (g - t') = g - t`,

  `div_X(a) = [Y_t ⊆ X]_{n-1} - [Y_{t'} ⊆ X]_{n-1}`,

where `Y_t = q⁻¹D_t` is the fibre of the graph closure at `t`, read in `X` through `p`.

This is `Stacks.Chow.principalDivisorCycle_eq_sub_imageCycles` — part (6) of Tag 02RQ — at an
arbitrary pair of points in place of `0` and `∞`. The three steps are the same: the fibre
difference identity of
`Stacks.Chow.principalDivisorCycle_eq_sub_linePointFibreCycles` at `t` and at `t'`, whose
infinity terms cancel on subtraction; the identification of `a` pulled back to `Y` with
`(z - t)/(z - t')`, which is `Stacks.Chow.linePointFunction_graphLineProjection`; and part (5)
for an arbitrary rational function,
`Stacks.Chow.principalDivisorCycle_eq_properPushforward_of_functionField`, followed by the
closed-immersion case of Stacks 02R6. -/
theorem principalDivisorCycle_eq_sub_pointImageCycles (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens) [QuasiCompact U.ι]
    [Nonempty U.toScheme] (g : (Γ(X, U))ˣ) (t t' : Γ(C.S, ⊤)) {n : ℤ}
    (hn : schemeDeltaDimension C sX = (n : EInt)) (hU : Dense (U : Set X))
    (hu : IsUnit ((g : Γ(X, U)) - baseSectionOn sX U t))
    (hu' : IsUnit ((g : Γ(X, U)) - baseSectionOn sX U t'))
    (a : X.functionField) (ha : a ≠ 0)
    (hrel : a * X.germToFunctionField U ((g : Γ(X, U)) - baseSectionOn sX U t') =
      X.germToFunctionField U ((g : Γ(X, U)) - baseSectionOn sX U t)) :
    principalDivisorCycle C sX hn a =
      cycleAssociatedToClosedSubscheme C sX
          (((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι ≫
            graphProjection sX U ↑g) (n - 1) -
        cycleAssociatedToClosedSubscheme C sX
          (((lineSection C.S t').ker.comap (graphLineProjection sX U ↑g)).subschemeι ≫
            graphProjection sX U ↑g) (n - 1) := by
  have hYint : IsIntegral (graphClosure sX U ↑g) := isIntegral_graphClosure sX U ↑g hU
  have hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) :=
    locallyOfFiniteType_graphBaseMorphism sX U ↑g
  have hLNY : IsLocallyNoetherian (graphClosure sX U ↑g) :=
    LocallyOfFiniteType.isLocallyNoetherian (graphBaseMorphism sX U ↑g)
  have hd : GraphPreimageDense sX U ↑g := dense_graphPreimage sX U ↑g
  have hWne : Nonempty (graphPreimage sX U ↑g) := Set.nonempty_coe_sort.mpr hd.nonempty
  have hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g :=
    ((genericPoint_spec (graphClosure sX U ↑g)).mem_open_set_iff
      (graphPreimage sX U ↑g).2).mpr (by simpa using hd.nonempty)
  have hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt) :=
    schemeDeltaDimension_graphClosure C sX U g n hn hU hYft
  have hWA : graphPreimage sX U ↑g ≤ graphLineProjection sX U ↑g ⁻¹ᵁ chartOpen C.S :=
    graphPreimage_le_preimage_image_chart sX U g (affineChart C.S) (g : Γ(X, U)) rfl
  have hη1 : genericPoint (graphClosure sX U ↑g) ∈
      graphLineProjection sX U ↑g ⁻¹ᵁ chartOpen C.S := hWA hηW
  have hgenInf : genericPoint (graphClosure sX U ↑g) ∉ Set.range
      ((lineInfinityDivisor C.S).comap (graphLineProjection sX U ↑g)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact notMem_support_graphInfinityFiber_genericPoint sX U g
  have hpt : ∀ (t : Γ(C.S, ⊤)), IsUnit ((g : Γ(X, U)) - baseSectionOn sX U t) →
      linePointFunction (graphLineProjection sX U ↑g) t hη1 ≠ 0 ∧
      principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
          (linePointFunction (graphLineProjection sX U ↑g) t hη1) =
        cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          ((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          ((lineInfinityDivisor C.S).comap (graphLineProjection sX U ↑g)).subschemeι (n - 1) :=
    fun t hu => by
      have hgen : genericPoint (graphClosure sX U ↑g) ∉ Set.range
          ((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι.base := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact notMem_support_comap_lineSectionKer_genericPoint sX U g t hu
      exact ⟨linePointFunction_ne_zero _ t hη1 hgen,
        principalDivisorCycle_eq_sub_linePointFibreCycles C (graphBaseMorphism sX U ↑g)
          (graphLineProjection sX U ↑g) t hYdim hη1 hgen hgenInf⟩
  obtain ⟨hTne, hDT⟩ := hpt t hu
  obtain ⟨hT'ne, hDT'⟩ := hpt t' hu'
  have hane : dominantFunctionFieldMap (graphProjection sX U ↑g) a ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap (graphProjection sX U ↑g)).injective).2 ha
  have hφrel : dominantFunctionFieldMap (graphProjection sX U ↑g) a *
      linePointFunction (graphLineProjection sX U ↑g) t' hη1 =
      linePointFunction (graphLineProjection sX U ↑g) t hη1 := by
    rw [linePointFunction_graphLineProjection sX U g t hηW hη1,
      linePointFunction_graphLineProjection sX U g t' hηW hη1,
      germToFunctionField_graphProjection_app sX U g
        ((g : Γ(X, U)) - baseSectionOn sX U t),
      germToFunctionField_graphProjection_app sX U g
        ((g : Γ(X, U)) - baseSectionOn sX U t'),
      ← map_mul, hrel]
  have hmul := principalDivisorCycle_mul C (graphBaseMorphism sX U ↑g) hYdim hane hT'ne
  rw [hφrel] at hmul
  have hdiff : principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
        (dominantFunctionFieldMap (graphProjection sX U ↑g) a) =
      cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          ((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
          ((lineSection C.S t').ker.comap (graphLineProjection sX U ↑g)).subschemeι (n - 1) := by
    have hsub : principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
          (dominantFunctionFieldMap (graphProjection sX U ↑g) a) =
        principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
            (linePointFunction (graphLineProjection sX U ↑g) t hη1) -
          principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
            (linePointFunction (graphLineProjection sX U ↑g) t' hη1) := by
      rw [hmul]
      abel
    rw [hsub, hDT, hDT']
    abel
  have hpush : ∀ t : Γ(C.S, ⊤), properPushforward C (graphBaseMorphism sX U ↑g) sX
        (graphProjection sX U ↑g) rfl (n - 1) (cycleAssociatedToClosedSubscheme C
          (graphBaseMorphism sX U ↑g)
          ((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι (n - 1)) =
      cycleAssociatedToClosedSubscheme C sX
        (((lineSection C.S t).ker.comap (graphLineProjection sX U ↑g)).subschemeι ≫
          graphProjection sX U ↑g) (n - 1) := fun t =>
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl _ (n - 1)
  rw [principalDivisorCycle_eq_properPushforward_of_functionField C sX U g hn a ha hYint hYft
      hYdim, hdiff, properPushforward_sub,
    hpush t, hpush t']

/-! ### The Möbius section -/

section Mobius

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (g : (Γ(X, U))ˣ) (t t' : Γ(S, ⊤))

/-- **The Möbius section `φ = (t - g t')/(1 - g)`**, the unique section with
`(φ - t)/(φ - t') = g`. It is the section whose graph closure realises the principal divisor of
`g` as a difference of fibre cycles at the two points `t` and `t'`. -/
def mobiusSection (hw : IsUnit (1 - (g : Γ(X, U))))
    (hφ : IsUnit (baseSectionOn sX U t - (g : Γ(X, U)) * baseSectionOn sX U t')) :
    (Γ(X, U))ˣ :=
  hφ.unit * hw.unit⁻¹

variable (hw : IsUnit (1 - (g : Γ(X, U))))
  (hφ : IsUnit (baseSectionOn sX U t - (g : Γ(X, U)) * baseSectionOn sX U t'))

/-- `φ - c = (t - g t' - c (1 - g))/(1 - g)` for every `c`. -/
private theorem mobiusSection_sub_eq (c : Γ(X, U)) :
    (mobiusSection sX U g t t' hw hφ : Γ(X, U)) - c =
      (baseSectionOn sX U t - (g : Γ(X, U)) * baseSectionOn sX U t' - c * (1 - (g : Γ(X, U)))) *
        ((hw.unit⁻¹ : (Γ(X, U))ˣ) : Γ(X, U)) := by
  have h : (hw.unit : Γ(X, U)) * ((hw.unit⁻¹ : (Γ(X, U))ˣ) : Γ(X, U)) = 1 := hw.unit.mul_inv
  calc (mobiusSection sX U g t t' hw hφ : Γ(X, U)) - c
      = (hφ.unit : Γ(X, U)) * ((hw.unit⁻¹ : (Γ(X, U))ˣ) : Γ(X, U)) -
          c * ((hw.unit : Γ(X, U)) * ((hw.unit⁻¹ : (Γ(X, U))ˣ) : Γ(X, U))) := by
        rw [h, mul_one]
        rfl
    _ = _ := by
      rw [hφ.unit_spec, hw.unit_spec]
      ring

/-- `φ - t' = (t - t')/(1 - g)`. -/
theorem mobiusSection_sub_right :
    (mobiusSection sX U g t t' hw hφ : Γ(X, U)) - baseSectionOn sX U t' =
      (baseSectionOn sX U t - baseSectionOn sX U t') * ((hw.unit⁻¹ : (Γ(X, U))ˣ) : Γ(X, U)) := by
  rw [mobiusSection_sub_eq]
  ring

/-- `φ - t = g (t - t')/(1 - g)`. -/
theorem mobiusSection_sub_left :
    (mobiusSection sX U g t t' hw hφ : Γ(X, U)) - baseSectionOn sX U t =
      (g : Γ(X, U)) * ((baseSectionOn sX U t - baseSectionOn sX U t') *
        ((hw.unit⁻¹ : (Γ(X, U))ˣ) : Γ(X, U))) := by
  rw [mobiusSection_sub_eq]
  ring

/-- **`g (φ - t') = φ - t`**: the defining property of the Möbius section. -/
theorem mul_mobiusSection_sub :
    (g : Γ(X, U)) * ((mobiusSection sX U g t t' hw hφ : Γ(X, U)) - baseSectionOn sX U t') =
      (mobiusSection sX U g t t' hw hφ : Γ(X, U)) - baseSectionOn sX U t := by
  rw [mobiusSection_sub_right, mobiusSection_sub_left]

/-- **`φ - t` is invertible when `t - t'` is.** This is the one place distinctness of the two
points does any work: `φ - t = g (t - t')/(1 - g)`, a product of units exactly when `t - t'` is
one. -/
theorem isUnit_mobiusSection_sub_left
    (he : IsUnit (baseSectionOn sX U t - baseSectionOn sX U t')) :
    IsUnit ((mobiusSection sX U g t t' hw hφ : Γ(X, U)) - baseSectionOn sX U t) := by
  rw [mobiusSection_sub_left]
  exact g.isUnit.mul (he.mul (hw.unit⁻¹ : (Γ(X, U))ˣ).isUnit)

/-- **`φ - t'` is invertible when `t - t'` is**, for the same reason. -/
theorem isUnit_mobiusSection_sub_right
    (he : IsUnit (baseSectionOn sX U t - baseSectionOn sX U t')) :
    IsUnit ((mobiusSection sX U g t t' hw hφ : Γ(X, U)) - baseSectionOn sX U t') := by
  rw [mobiusSection_sub_right]
  exact he.mul (hw.unit⁻¹ : (Γ(X, U))ˣ).isUnit

end Mobius

/-! ### The principal divisor of a unit section at an arbitrary pair of points -/

/-- **The principal divisor of a unit section on a dense open is the difference of the fibre
cycles at an arbitrary pair of points of the affine chart.** For `g` invertible on a dense open
`U ⊆ X` and `t`, `t'` global functions on the base, let `φ = (t - g t')/(1 - g)` be the Möbius
section and `Y` the closure of its graph. Then

  `div_X(g) = [Y_t ⊆ X]_{n-1} - [Y_{t'} ⊆ X]_{n-1}`.

The three invertibility hypotheses are exactly what the construction needs: `1 - g` and
`t - g t'` so that `φ` is a section of `U` and a unit there, and `t - t'` — **the distinctness of
the two points** — so that `φ` meets neither the section at `t` nor the section at `t'`. Without
the last one the statement is false: for `t = t'` the right-hand side is zero for every `Y`,
while the left-hand side is not. -/
theorem principalDivisorCycle_eq_sub_pointImageCycles_mobius (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens)
    [QuasiCompact U.ι] [Nonempty U.toScheme] (g : (Γ(X, U))ˣ) (t t' : Γ(C.S, ⊤)) {n : ℤ}
    (hn : schemeDeltaDimension C sX = (n : EInt)) (hU : Dense (U : Set X))
    (hw : IsUnit (1 - (g : Γ(X, U))))
    (hφ : IsUnit (baseSectionOn sX U t - (g : Γ(X, U)) * baseSectionOn sX U t'))
    (he : IsUnit (baseSectionOn sX U t - baseSectionOn sX U t')) :
    principalDivisorCycle C sX hn (X.germToFunctionField U (g : Γ(X, U))) =
      cycleAssociatedToClosedSubscheme C sX
          (((lineSection C.S t).ker.comap (graphLineProjection sX U
              ↑(mobiusSection sX U g t t' hw hφ))).subschemeι ≫
            graphProjection sX U ↑(mobiusSection sX U g t t' hw hφ)) (n - 1) -
        cycleAssociatedToClosedSubscheme C sX
          (((lineSection C.S t').ker.comap (graphLineProjection sX U
              ↑(mobiusSection sX U g t t' hw hφ))).subschemeι ≫
            graphProjection sX U ↑(mobiusSection sX U g t t' hw hφ)) (n - 1) := by
  refine principalDivisorCycle_eq_sub_pointImageCycles C sX U
    (mobiusSection sX U g t t' hw hφ) t t' hn hU
    (isUnit_mobiusSection_sub_left sX U g t t' hw hφ he)
    (isUnit_mobiusSection_sub_right sX U g t t' hw hφ he)
    (X.germToFunctionField U (g : Γ(X, U)))
    (IsUnit.map (X.germToFunctionField U).hom g.isUnit).ne_zero ?_
  rw [← map_mul, mul_mobiusSection_sub]

/-! ### The pushforward of the principal divisor as a fibre difference of the family member -/

/-- **The pushforward of the principal divisor of a rational function on an integral closed
subscheme `V ⊆ X` is the fibre difference of the graph member at an arbitrary pair of points.**

This is `Stacks.Chow.principalDivisorPushforward_eq_sub_fibreCycles` at an arbitrary pair in
place of `0` and `∞`: part (6) at that pair, which is
`Stacks.Chow.principalDivisorCycle_eq_sub_pointImageCycles`, gives the identity on `V`, proper
pushforward along the closed immersion `V ⟶ X` carries it to `X`, and
`Stacks.Chow.cycleAssociatedToClosedSubscheme_pointFiber_graphFamilyMember` identifies the two
fibres of the member with the images of the two fibres of the graph closure.

Unlike the `(0, ∞)` statement this one does not need the rational function to be the one the
graph was built from: it takes any `gg` satisfying the Möbius relation against the section `σ`,
which is what makes an arbitrary pair reachable. -/
theorem principalDivisorPushforward_eq_sub_pointFibreCycles (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (gg : (rationalFunctions V.subscheme)ˣ) (U : V.subscheme.Opens) [QuasiCompact U.ι]
    [Nonempty U.toScheme] (hU : Dense (U : Set V.subscheme)) (σ : (Γ(V.subscheme, U))ˣ)
    (t t' : Γ(C.S, ⊤))
    (hu : IsUnit ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t))
    (hu' : IsUnit ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t'))
    (hrel : (rationalFunctionsEquivFunctionField V.subscheme).1
          (gg : rationalFunctions V.subscheme) *
        V.subscheme.germToFunctionField U
          ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t') =
      V.subscheme.germToFunctionField U
        ((σ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t)) :
    principalDivisorPushforward C f V hV gg =
      (cycleAssociatedToClosedSubscheme C f
          (pointFiber f t (graphFamilyMember f V.subschemeι U
            (σ : Γ(V.subscheme, U)))).subschemeι k).1 -
        (cycleAssociatedToClosedSubscheme C f
          (pointFiber f t' (graphFamilyMember f V.subschemeι U
            (σ : Γ(V.subscheme, U)))).subschemeι k).1 := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  have hk : (k + 1 - 1 : ℤ) = k := by ring
  have hane : (rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme) ≠ 0 :=
    (gg.isUnit.map (rationalFunctionsEquivFunctionField V.subscheme).1.toRingHom).ne_zero
  have h6 := principalDivisorCycle_eq_sub_pointImageCycles C (V.subschemeι ≫ f) U σ t t' hdim hU
    hu hu' ((rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme)) hane hrel
  have h6' : principalCycle V.subscheme ((rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme)) =
      (cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          (((lineSection C.S t).ker.comap (graphLineProjection (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U)))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) (k + 1 - 1)).1 -
        (cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          (((lineSection C.S t').ker.comap (graphLineProjection (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U)))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) (k + 1 - 1)).1 := by
    have h := congrArg Subtype.val h6
    rw [AddSubgroup.coe_sub] at h
    exact h
  rw [hk] at h6'
  have hmem : principalCycle V.subscheme ((rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme)) ∈ cyclesOfDimension C (V.subschemeι ≫ f) k := by
    have h := principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ f) hdim
      ((rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme))
    rwa [hk] at h
  have hc : (⟨_, hmem⟩ : CycleGroup C (V.subschemeι ≫ f) k) =
      cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          (((lineSection C.S t).ker.comap (graphLineProjection (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U)))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k -
        cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          (((lineSection C.S t').ker.comap (graphLineProjection (V.subschemeι ≫ f) U
              (σ : Γ(V.subscheme, U)))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k := by
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_sub]
    exact h6'
  have hpush := congrArg Subtype.val
    (congrArg (properPushforward C (V.subschemeι ≫ f) f V.subschemeι rfl k) hc)
  rw [properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (V.subschemeι ≫ f) f V.subschemeι rfl
      (((lineSection C.S t).ker.comap (graphLineProjection (V.subschemeι ≫ f) U
          (σ : Γ(V.subscheme, U)))).subschemeι ≫
        graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (V.subschemeι ≫ f) f V.subschemeι rfl
      (((lineSection C.S t').ker.comap (graphLineProjection (V.subschemeι ≫ f) U
          (σ : Γ(V.subscheme, U)))).subschemeι ≫
        graphProjection (V.subschemeι ≫ f) U (σ : Γ(V.subscheme, U))) k,
    cycleAssociatedToClosedSubscheme_pointFiber_graphFamilyMember C f V.subschemeι U
      (σ : Γ(V.subscheme, U)) t k,
    cycleAssociatedToClosedSubscheme_pointFiber_graphFamilyMember C f V.subschemeι U
      (σ : Γ(V.subscheme, U)) t' k, AddSubgroup.coe_sub] at hpush
  exact hpush

/-! ### The member meets the section at an arbitrary point properly -/

/-- The image of the section at `t` of `X ×_S ℙ¹_S ⟶ X` is the preimage of the divisor at `t`
under the second projection. This is the arbitrary-point analogue of
`Stacks.Chow.range_zeroSection_eq_preimage`. -/
theorem range_pointSection_eq_preimage {X S : Scheme.{u}} (f : X ⟶ S) (t : Γ(S, ⊤)) :
    Set.range (pointSection f t) =
      pullback.snd f (relativeProjectiveLine S ↘ S) ⁻¹' Set.range (lineSection S t) := by
  have h := Scheme.Hom.support_ker (pointSection f t)
  rw [ker_pointSection, Scheme.IdealSheafData.support_comap] at h
  rw [← (pointSection f t).isClosedEmbedding.isClosed_range.closure_eq, ← h,
    Closeds.coe_preimage, Scheme.Hom.support_ker,
    IsClosed.closure_eq (lineSection S t).isClosedEmbedding.isClosed_range]

/-- **The graph family member is not contained in the image of the section at `t`**, as soon as
`g - t` is invertible on `U`: its generic point is the image of the generic point of the graph
closure, which lies off the fibre at `t`. This is the arbitrary-point analogue of
`Stacks.Chow.notSubset_range_zeroSection_graphFamilyMember`. -/
theorem notSubset_range_pointSection_graphFamilyMember {X Y S : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y] (U : Y.Opens) [QuasiCompact U.ι]
    [Nonempty U.toScheme] (g : (Γ(Y, U))ˣ) [IsIntegral (graphClosure (i ≫ f) U ↑g)]
    (t : Γ(S, ⊤)) (hu : IsUnit ((g : Γ(Y, U)) - baseSectionOn (i ≫ f) U t)) :
    ¬ Set.range (graphFamilyMember f i U (g : Γ(Y, U))).subschemeι ⊆
      Set.range (pointSection f t) := by
  intro h
  refine notMem_support_comap_lineSectionKer_genericPoint (i ≫ f) U g t hu ?_
  have hx : graphFamilyInclusion f i U (g : Γ(Y, U))
      (genericPoint (graphClosure (i ≫ f) U (g : Γ(Y, U)))) ∈
      Set.range (graphFamilyMember f i U (g : Γ(Y, U))).subschemeι := by
    rw [range_graphFamilyMember_subschemeι]
    exact Set.mem_range_self _
  have hmem := h hx
  rw [range_pointSection_eq_preimage, Set.mem_preimage] at hmem
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Set.mem_preimage, Scheme.Hom.support_ker,
    IsClosed.closure_eq (lineSection S t).isClosedEmbedding.isClosed_range,
    ← graphFamilyInclusion_comp_snd f i U (g : Γ(Y, U))]
  simpa only [Scheme.Hom.comp_apply] using hmem

/-! ### A global function on the base read on an open -/

section BaseSectionUnits

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)

/-- Reading a global function on an open of `X` is additive. -/
theorem baseSectionOn_sub (t t' : Γ(S, ⊤)) :
    baseSectionOn sX U (t - t') = baseSectionOn sX U t - baseSectionOn sX U t' := by
  rw [baseSectionOn, baseSectionOn, baseSectionOn, map_sub, map_sub]

/-- A global unit on the base stays a unit on every open of `X`. -/
theorem isUnit_baseSectionOn {t : Γ(S, ⊤)} (ht : IsUnit t) : IsUnit (baseSectionOn sX U t) :=
  IsUnit.map (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
    (IsUnit.map sX.appTop.hom ht)

/-- **The distinctness of the two points, in the form the construction consumes.** If `t - t'` is
invertible on the base — for `S = Spec k` with `k` a field exactly `t ≠ t'` — then `t - t'` is
invertible on every open of every `X` over `S`. -/
theorem isUnit_baseSectionOn_sub {t t' : Γ(S, ⊤)} (ht : IsUnit (t - t')) :
    IsUnit (baseSectionOn sX U t - baseSectionOn sX U t') := by
  rw [← baseSectionOn_sub]
  exact isUnit_baseSectionOn sX U ht

end BaseSectionUnits

/-! ### The member of Tag 02S4 part (3) at an arbitrary pair of points -/

/-- **The subvariety of `X ×_S ℙ¹_S` realising the principal divisor of a rational function as a
fibre difference at an arbitrary pair of points.** Let `V ⊆ X` be an integral closed subscheme of
delta-dimension `k + 1`, let `gg` be a nonzero rational function on `V` represented by a unit
section `g₀` on a dense open `U`, and let `t`, `t'` be two points of the affine chart. Suppose
`t - t'`, `1 - g₀` and `t - g₀ t'` are invertible. Then the closure `W` of the graph of the
Möbius section `φ = (t - g₀ t')/(1 - g₀)`, read inside `X ×_S ℙ¹_S`, has every property Tag 02S4
part (3) asks of a family member at the pair `(t, t')` — it is integral, of relative dimension
`k + 1` at its generic points, contained in neither section, and supported over `V` — and

  `pr_{X,*}(div_V(gg)) = [W_t]_k - [W_{t'}]_k`.

This is `Stacks.Chow.exists_graphFamilyMember` at an arbitrary pair in place of `0` and `∞`, and
it is the production step of part (3) of Tag 0B07 at that pair. Invertibility of `t - t'` is
where distinctness of the two points does its work:
`Stacks.Chow.isUnit_mobiusSection_sub_left` fails without it, and for `t = t'` the conclusion is
false. -/
theorem exists_pointGraphFamilyMember (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (gg : (rationalFunctions V.subscheme)ˣ) (U : V.subscheme.Opens) [QuasiCompact U.ι]
    [Nonempty U.toScheme] (hU : Dense (U : Set V.subscheme)) (g₀ : (Γ(V.subscheme, U))ˣ)
    (hg₀ : ofSection V.subscheme ⟨U, hU⟩ (g₀ : Γ(V.subscheme, U)) =
      (gg : rationalFunctions V.subscheme))
    (t t' : Γ(C.S, ⊤)) (hne : IsUnit (t - t'))
    (hw : IsUnit (1 - (g₀ : Γ(V.subscheme, U))))
    (hφ : IsUnit (baseSectionOn (V.subschemeι ≫ f) U t -
      (g₀ : Γ(V.subscheme, U)) * baseSectionOn (V.subschemeι ≫ f) U t')) :
    ∃ W : (projectiveLineProduct f).IdealSheafData,
      IsIntegral W.subscheme ∧
      (∀ ξ : genericPoints W.subscheme,
        relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1) ∧
      ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t) ∧
      ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t') ∧
      ((W.support : Set (projectiveLineProduct f)) ⊆
        pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ⁻¹' (V.support : Set X)) ∧
      (∀ x : X, principalDivisorPushforward C f V hV gg x =
        (cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k).1 x -
          (cycleAssociatedToClosedSubscheme C f (pointFiber f t' W).subschemeι k).1 x) := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  set ψ := mobiusSection (V.subschemeι ≫ f) U g₀ t t' hw hφ with hψdef
  have he : IsUnit (baseSectionOn (V.subschemeι ≫ f) U t -
      baseSectionOn (V.subschemeι ≫ f) U t') :=
    isUnit_baseSectionOn_sub (V.subschemeι ≫ f) U hne
  have hu : IsUnit ((ψ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t) :=
    isUnit_mobiusSection_sub_left (V.subschemeι ≫ f) U g₀ t t' hw hφ he
  have hu' : IsUnit ((ψ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t') :=
    isUnit_mobiusSection_sub_right (V.subschemeι ≫ f) U g₀ t t' hw hφ he
  have hYint : IsIntegral (graphClosure (V.subschemeι ≫ f) U (ψ : Γ(V.subscheme, U))) :=
    isIntegral_graphClosure (V.subschemeι ≫ f) U (ψ : Γ(V.subscheme, U)) hU
  have hηU : genericPoint V.subscheme ∈ U :=
    ((genericPoint_spec V.subscheme).mem_open_set_iff U.2).mpr
      (by simpa using ‹Nonempty U.toScheme›)
  have hgf : (rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme) =
      V.subscheme.germToFunctionField U (g₀ : Γ(V.subscheme, U)) := by
    rw [← hg₀]
    exact (rationalFunctionsEquivFunctionField V.subscheme).2 ⟨U, hU⟩
      (g₀ : Γ(V.subscheme, U)) hηU
  have hrel : (rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme) *
      V.subscheme.germToFunctionField U
        ((ψ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t') =
      V.subscheme.germToFunctionField U
        ((ψ : Γ(V.subscheme, U)) - baseSectionOn (V.subschemeι ≫ f) U t) := by
    rw [hgf, ← map_mul, hψdef, mul_mobiusSection_sub]
  refine ⟨graphFamilyMember f V.subschemeι U (ψ : Γ(V.subscheme, U)),
    isIntegral_graphFamilyMember f V.subschemeι U (ψ : Γ(V.subscheme, U)),
    fun ξ => relativeDimension_familyBase_graphFamilyMember C f V.subschemeι U ψ hU hdim ξ,
    notSubset_range_pointSection_graphFamilyMember f V.subschemeι U ψ t hu,
    notSubset_range_pointSection_graphFamilyMember f V.subschemeι U ψ t' hu', ?_, fun x => ?_⟩
  · refine (support_graphFamilyMember_subset f V.subschemeι U
      (ψ : Γ(V.subscheme, U))).trans ?_
    rw [V.range_subschemeι]
  · have h := principalDivisorPushforward_eq_sub_pointFibreCycles C f k V hV hdim gg U hU ψ t t'
      hu hu' hrel
    simpa using congrArg (fun c : AlgebraicCycle X ℤ => c x) h

end Stacks.Chow

end

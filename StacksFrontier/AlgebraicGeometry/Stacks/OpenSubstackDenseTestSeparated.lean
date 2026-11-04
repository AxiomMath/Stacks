module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuativeSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism

/-!
# The refined valuative criterion of separation on an open substack

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, locally of finite type and
quasi-separated, with `𝒴` locally Noetherian, and let `𝒲 ⊆ 𝒳` be an open substack. To show that
the restriction `𝒲 ⟶ 𝒴` of `f` is separated, Stacks 0E95 may be applied to the inclusion of any
open substack `𝒰 ⊆ 𝒲` with dense set of points: all the preliminary assumptions of Stacks 0E95
hold, and what is left is the uniqueness hypothesis for valuative squares over discrete valuation
rings whose generic point lies in `𝒰`.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.isFiniteType_inclusion`: the inclusion of an open
  substack of a locally Noetherian algebraic stack is of finite type (Stacks 0CPM).
* `AlgebraicGeometry.Stack.OpenSubstack.isSeparated_inclusion_comp_of_denseTestUniqueness`:
  `𝒲 ⟶ 𝒴` is separated as soon as the uniqueness hypothesis of Stacks 0E95 holds for valuative
  squares over discrete valuation rings whose generic point lies in `𝒰`.

## References

* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace OpenSubstack

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The inclusion of an open substack of a locally Noetherian algebraic stack is of finite
type.** -/
theorem isFiniteType_inclusion (W : OpenSubstack 𝒳)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳) :
    AlgebraicStacks.IsFiniteType B S hS W.inclusion := by
  have himm := AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS W.inclusion W.isOpenImmersion
  exact ⟨AlgebraicStacks.isLocallyOfFiniteType_of_isOpenImmersion B S hS W.inclusion
      W.isOpenImmersion,
    (isQuasiCompact_iff_baseChange_quasiCompact B S hS W.inclusion himm.1).mp
      (AlgebraicStacks.hasRelativeProperty_quasiCompact_of_isImmersion B S hS W.inclusion himm
        h𝒳)⟩

/-- **Objects of an open substack whose points lie in a second open substack.** Let `𝒲` and `𝒱`
be open substacks of `𝒳`. An object of `𝒲` all of whose points map into `|𝒱|` under
`|𝒲| ⟶ |𝒳|` lies in `𝒱`. -/
theorem property_of_pointsInProperty_preimage (W V : OpenSubstack 𝒳)
    {x : W.toAlgebraicStack.val.val.obj}
    (hx : pointsInProperty (AlgebraicStacks.pointsMap B S hS W.inclusion ⁻¹' V.pointSet B S hS) x) :
    V.property x.obj := by
  rw [← congrArg OpenSubstack.property (ofIsOpen_pointSet B S hS V)]
  rintro p ⟨m⟩
  let pW : FieldValuedPoint B S hS W.toAlgebraicStack.val.val :=
    { carrier := p.carrier
      field := p.field
      base := p.base
      isSpec := p.isSpec
      obj := ⟨p.obj, W.prop_of_hom B S hS m x.property⟩
      «over» := p.over }
  exact hx pW ⟨ObjectProperty.homMk m⟩

/-- **The refined valuative criterion of separation on an open substack.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`, locally of finite type and quasi-separated, with `𝒴`
locally Noetherian, let `𝒲 ⊆ 𝒳` be an open substack and `T ⊆ |𝒲|` an open dense set of points,
with open substack `𝒰 ⊆ 𝒲`. If for every valuative square for `𝒲 ⟶ 𝒴` over a discrete valuation
ring whose generic point lies in `𝒰` the category of dotted arrows is either empty or a setoid
with exactly one isomorphism class, then `𝒲 ⟶ 𝒴` is separated. -/
theorem isSeparated_inclusion_comp_of_denseTestUniqueness (f : 𝒳 ⟶ 𝒴) (W : OpenSubstack 𝒳)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (T : Set (AlgebraicStacks.points B S hS W.toAlgebraicStack))
    (hTo : @IsOpen _ (pointTopology B S hS W.toAlgebraicStack.val) T)
    (hTd : @Dense _ (pointTopology B S hS W.toAlgebraicStack.val) T)
    (hu : ValuativeCriterion.DenseTestUniqueness B S hS (ofIsOpen B S hS T hTo).inclusion
      (W.inclusion ≫ f)) :
    AlgebraicStacks.IsSeparated B S hS (W.inclusion ≫ f) := by
  have hWft : AlgebraicStacks.IsLocallyOfFiniteType B S hS (W.inclusion ≫ f) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ _
      (AlgebraicStacks.isLocallyOfFiniteType_of_isOpenImmersion B S hS W.inclusion
        W.isOpenImmersion) hft
  have hWqs : AlgebraicStacks.IsQuasiSeparated B S hS (W.inclusion ≫ f) :=
    AlgebraicStacks.isQuasiSeparated_comp B S hS _ _
      (AlgebraicStacks.isQuasiSeparated_of_isMonomorphism B S hS W.inclusion
        (AlgebraicStacks.isMonomorphism_of_isOpenImmersion B S hS W.inclusion
          W.isOpenImmersion)) hqs
  have hWN := AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS _ hWft h𝒴
  refine AlgebraicStacks.isSeparated_of_denseTestUniqueness B S hS (W.inclusion ≫ f)
    (ofIsOpen B S hS T hTo).inclusion h𝒴 hWft hWqs
    ((ofIsOpen B S hS T hTo).isFiniteType_inclusion B S hS hWN) ?_ hu
  let := pointTopology B S hS W.toAlgebraicStack.val
  exact hTd.mono (pointSet_ofIsOpen T hTo).ge

end OpenSubstack

end AlgebraicGeometry.Stack

end

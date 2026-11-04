module

public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOnOpen0BF3
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
import all StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier

/-!
# The two distinguished divisors of `ℙ¹_S` as zero schemes of sections

Let `S` be a scheme and let `D₀, D_∞ ⊆ ℙ¹_S` be the zero and infinity divisors, the closed
subschemes cut out by the kernel ideal sheaves of the two constant sections. Both are effective
Cartier divisors, so each is the zero scheme of the canonical global section `1_D` of its
invertible sheaf `𝒪(D)`; this file records that presentation.

## Main results

* `Stacks.Chow.zeroScheme_lineZeroDivisor` and `Stacks.Chow.zeroScheme_lineInfinityDivisor` —
  each of `D₀`, `D_∞` is the zero scheme of a global section of an invertible module.

## Implementation notes

The source presents `D₀` and `D_∞` as the zero schemes of the two homogeneous coordinates `T₁`,
`T₀`, viewed as global sections of `𝒪(1)`. The presentation recorded here is the intrinsic one:
the invertible module is `𝒪(D)` and the section is `1_D`, which for `D = D₀` is `T₁` read through
`𝒪(D₀) = 𝒪(1)`. It is this form that the Gysin constructions consume, since
`Stacks.Divisors.zeroScheme` is what both [Stacks, Tag 02T8] and [Stacks, Tag 0B6Z] are stated
over, and it needs no construction of `𝒪(1)` on the two-chart gluing of `ℙ¹_ℤ`.

The effective-Cartier hypothesis of `Stacks.Divisors.isInvertible_divisorSheaf` is supplied as a
local instance from the two theorems of
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier` and
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier`, so the statements
below are unconditional.

## References

* [Stacks Project, Tag 0F93](https://stacks.math.columbia.edu/tag/0F93)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Chow

attribute [local instance] lineZeroDivisor_isEffectiveCartierDivisor
  lineInfinityDivisor_isEffectiveCartierDivisor

/-- **Stacks 0F93, the zero divisor as a zero scheme.** `D₀ ⊆ ℙ¹_S` is the zero scheme of a
global section of an invertible module, namely of the canonical section `1_{D₀}` of
`𝒪(D₀)`. -/
@[stacks 0F93 "D₀ is the zero scheme of a global section of an invertible module"]
theorem zeroScheme_lineZeroDivisor (S : Scheme.{u}) :
    Stacks.Divisors.zeroScheme (relativeProjectiveLine S)
        (Stacks.Divisors.divisorSheaf (lineZeroDivisor S))
        (Stacks.Divisors.divisorSheafGlobalSection (lineZeroDivisor S)) =
      lineZeroDivisor S :=
  Stacks.Divisors.zeroScheme_canonicalSection (lineZeroDivisor S)

/-- **Stacks 0F93, the infinity divisor as a zero scheme.** `D_∞ ⊆ ℙ¹_S` is the zero scheme of a
global section of an invertible module, namely of the canonical section `1_{D_∞}` of
`𝒪(D_∞)`. -/
@[stacks 0F93 "D_∞ is the zero scheme of a global section of an invertible module"]
theorem zeroScheme_lineInfinityDivisor (S : Scheme.{u}) :
    Stacks.Divisors.zeroScheme (relativeProjectiveLine S)
        (Stacks.Divisors.divisorSheaf (lineInfinityDivisor S))
        (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor S)) =
      lineInfinityDivisor S :=
  Stacks.Divisors.zeroScheme_canonicalSection (lineInfinityDivisor S)

/-! ### The affine coordinate as a global section of the unit module -/

/-- The structure sheaf of a scheme, viewed as a module over itself, is invertible. Instance
search does not see through `AlgebraicGeometry.Scheme.ringCatSheaf` to find this, so it is
supplied explicitly where needed below. -/
theorem isInvertible_unitModule (A : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      (Scheme.unitModule A) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit A.sheaf.obj A.ringCatSheaf.property)

attribute [local instance] isInvertible_unitModule

/-- The coordinate `T₁/T₀` of `𝔸¹_S`, read as a global section of the structure sheaf regarded
as a module over itself. -/
def affineCoordinateSection (S : Scheme.{u}) :
    SheafOfModules.sections (Scheme.unitModule (affineLineOver S)) :=
  Stacks.Divisors.sectionsOfTop (Scheme.unitModule (affineLineOver S)) (affineCoordinate S)

/-- The affine coordinate section evaluates to the affine coordinate. -/
@[simp]
theorem affineCoordinateSection_eval_top (S : Scheme.{u}) :
    (affineCoordinateSection S).eval (op ⊤) = affineCoordinate S :=
  Stacks.Divisors.sectionsOfTop_eval_top _ _

/-- **A divisor of a chart of `ℙ¹_S` cut out by the coordinate is the zero scheme of the
coordinate.** Both `D₀` and `D_∞` meet their chart in a divisor whose ideal is generated by the
coordinate on every affine open, and that is exactly the condition identifying it with the zero
scheme of the coordinate read as a section of the unit module. -/
theorem zeroScheme_affineCoordinateSection_eq
    (S : Scheme.{u}) (D : (affineLineOver S).IdealSheafData)
    (hD : ∀ V : (affineLineOver S).affineOpens, D.ideal V =
      Ideal.span {(affineLineOver S).presheaf.map (homOfLE le_top).op (affineCoordinate S)}) :
    AlgebraicGeometry.zeroScheme (affineLineOver S) (Scheme.unitModule (affineLineOver S))
        ((affineCoordinateSection S).eval (op ⊤)) = D := by
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  rw [hD V]
  refine AlgebraicGeometry.zeroScheme_ideal_of_trivialization (affineLineOver S)
    (Scheme.unitModule (affineLineOver S)) _ V (LinearEquiv.refl _ _) _ ?_
  rw [affineCoordinateSection_eval_top]
  rfl

/-! ### Triviality of the invertible sheaf on a chart -/

/-- **A divisor cut out on a chart by a regular global function has trivial invertible sheaf
there.** If the inverse image of `D` in an open `A ⊆ P` is the zero scheme of a global section
`t` of the structure sheaf of `A`, then `𝒪_P(D)` pulled back to `A` is trivial: the pullback is
`𝒪_A(D ∩ A)` by Stacks 0C4U, and `t` is a regular section because `D ∩ A` is an effective
Cartier divisor, so Stacks 01X0 identifies `𝒪_A(D ∩ A)` with the structure sheaf itself. -/
theorem isTrivial_pullback_divisorSheaf_of_zeroScheme
    {P A : Scheme.{u}} (c : A ⟶ P) [IsOpenImmersion c] (D : P.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (t : SheafOfModules.sections (Scheme.unitModule A))
    (ht : AlgebraicGeometry.zeroScheme A (Scheme.unitModule A) (t.eval (op ⊤)) = D.comap c) :
    AlgebraicGeometry.SheafOfModules.IsTrivial A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback c).obj (Stacks.Divisors.divisorSheaf D)) := by
  have := hD
  have hpb : Stacks.Divisors.IsPullbackDefined c D :=
    Stacks.Divisors.isPullbackDefined_of_flat c D hD
  have hreg : IsRegularSection A.sheaf.obj A.ringCatSheaf.property t :=
    (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection A
      (Scheme.unitModule A) t).mp (by rw [ht]; exact hpb)
  have h := (AlgebraicGeometry.existsUnique_invertibleSheafIso_zeroScheme A
    (Scheme.unitModule A) t hreg).exists
  rw [ht] at h
  obtain ⟨e, -⟩ := h
  exact ⟨Stacks.Divisors.invertibleSheafPullbackIso c D ≪≫ e⟩

/-- **Triviality on a chart containing the divisor propagates to the divisor itself.** The
closed immersion of `D` factors through any open containing its support, so the pullback of
`𝒪_P(D)` to `D` is the pullback along that factorization of its pullback to the open. -/
theorem isTrivial_pullback_divisorSheaf_subschemeι
    {P A : Scheme.{u}} (c : A ⟶ P) [IsOpenImmersion c] (D : P.IdealSheafData)
    (hsupp : Set.range D.subschemeι.base ⊆ Set.range c.base)
    (hchart : AlgebraicGeometry.SheafOfModules.IsTrivial A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback c).obj (Stacks.Divisors.divisorSheaf D))) :
    AlgebraicGeometry.SheafOfModules.IsTrivial D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.divisorSheaf D)) :=
  AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_scheme_of_comp
    (IsOpenImmersion.lift c D.subschemeι hsupp) c D.subschemeι
    (IsOpenImmersion.lift_fac c D.subschemeι hsupp) hchart

/-- **A trivial normal bundle stays trivial on an inverse image.** If `𝒪_P(D)` restricts
trivially to `D` and the inverse image of `D` along `f : P' ⟶ P` is defined, then
`𝒪_{P'}(f⁻¹D)` restricts trivially to `f⁻¹D`.

The closed immersion of `f⁻¹D` composed with `f` factors through `D` by the cartesian square of
Stacks 0B6Y, which gives triviality of the pullback of `𝒪_P(D)` along that composite; and that
pullback is the pullback of `𝒪_{P'}(f⁻¹D)` by Stacks 0C4U. -/
theorem isTrivial_pullback_divisorSheaf_comap
    {P P' : Scheme.{u}} (f : P' ⟶ P) (D : P.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hpb : Stacks.Divisors.IsPullbackDefined f D)
    (h : AlgebraicGeometry.SheafOfModules.IsTrivial D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.divisorSheaf D))) :
    AlgebraicGeometry.SheafOfModules.IsTrivial (D.comap f).subscheme.sheaf.obj
      (D.comap f).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (D.comap f).subschemeι).obj
        (Stacks.Divisors.divisorSheaf (D.comap f))) := by
  have := hD
  have := hpb
  have hc : ((D.comapIso f).hom ≫ Limits.pullback.snd f D.subschemeι) ≫ D.subschemeι =
      (D.comap f).subschemeι ≫ f := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have hcomp := AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_scheme_of_comp
    ((D.comapIso f).hom ≫ Limits.pullback.snd f D.subschemeι) D.subschemeι
    ((D.comap f).subschemeι ≫ f) hc h
  obtain ⟨φ⟩ := hcomp
  exact ⟨((Scheme.Modules.pullback (D.comap f).subschemeι).mapIso
      (Stacks.Divisors.invertibleSheafPullbackIso f D)).symm ≪≫
    (Scheme.Modules.pullbackComp (D.comap f).subschemeι f).app
      (Stacks.Divisors.divisorSheaf D) ≪≫ φ⟩

/-- A divisor cut out by the coordinate on a chart `𝔸¹_S ⟶ ℙ¹_S` containing its support has
trivial normal bundle. -/
private theorem isTrivial_pullback_divisorSheaf_of_affineChart (S : Scheme.{u})
    (c : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion c]
    (D : (relativeProjectiveLine S).IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hsupp : Set.range D.subschemeι.base ⊆ Set.range c.base)
    (hideal : ∀ V : (affineLineOver S).affineOpens, (D.comap c).ideal V =
      Ideal.span {(affineLineOver S).presheaf.map (homOfLE le_top).op (affineCoordinate S)}) :
    AlgebraicGeometry.SheafOfModules.IsTrivial D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.divisorSheaf D)) :=
  isTrivial_pullback_divisorSheaf_subschemeι c D hsupp
    (isTrivial_pullback_divisorSheaf_of_zeroScheme c D hD (affineCoordinateSection S)
      (zeroScheme_affineCoordinateSection_eq S _ hideal))

/-! ### The normal bundles of the two divisors are trivial -/

/-- **Stacks 0F93, the trivial normal bundle of `D₀`.** The invertible module `𝒪(D₀)` restricts
trivially to `D₀`: the support of `D₀` lies in the chart `𝔸¹_S`, where `D₀` is cut out by the
coordinate, a regular global function. -/
@[stacks 0F93 "the normal bundle of D₀ is trivial"]
theorem isTrivial_pullback_divisorSheaf_lineZeroDivisor (S : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (lineZeroDivisor S).subscheme.sheaf.obj (lineZeroDivisor S).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (lineZeroDivisor S).subschemeι).obj
        (Stacks.Divisors.divisorSheaf (lineZeroDivisor S))) := by
  refine isTrivial_pullback_divisorSheaf_of_affineChart S (affineChart S) (lineZeroDivisor S)
    (lineZeroDivisor_isEffectiveCartierDivisor S) ?_ (zeroDivisor_ideal_comap_affineChart S)
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_lineZeroDivisor]
  exact range_lineZeroSection_subset_range_affineChart S

/-- **Stacks 0F93, the trivial normal bundle of `D_∞`.** The invertible module `𝒪(D_∞)`
restricts trivially to `D_∞`: the support of `D_∞` lies in the second chart, where `D_∞` is cut
out by the coordinate of that chart, a regular global function. -/
@[stacks 0F93 "the normal bundle of D_∞ is trivial"]
theorem isTrivial_pullback_divisorSheaf_lineInfinityDivisor (S : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (lineInfinityDivisor S).subscheme.sheaf.obj
      (lineInfinityDivisor S).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (lineInfinityDivisor S).subschemeι).obj
        (Stacks.Divisors.divisorSheaf (lineInfinityDivisor S))) := by
  refine isTrivial_pullback_divisorSheaf_of_affineChart S (affineYChart S)
    (lineInfinityDivisor S) (lineInfinityDivisor_isEffectiveCartierDivisor S) ?_
    (infinityDivisor_ideal_comap_affineYChart S)
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_lineInfinityDivisor]
  exact range_lineInfinitySection_subset_range_affineYChart S

end Stacks.Chow

end

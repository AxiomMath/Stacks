module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Vanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishing

/-!
# A quasi-coherent module on an algebraic space with no weakly associated point vanishes

Let `X` be an algebraic space over a scheme `S` and let `F` be a quasi-coherent
`𝒪_X`-module.  Stacks 0CU0 asserts `F = 0 ⟺ WeakAss(F) = ∅`.  The forward direction is
`AlgebraicGeometry.Space.weaklyAssociatedPoints_eq_empty_of_isZero`; this file proves the
converse and assembles the equivalence.

The proof is the source's: the question is read on the étale scheme charts of `X`.  On the
scheme of a chart `U`, the restriction `F|_U` is quasi-coherent, and a point of that scheme
weakly associated to `F|_U` maps to a point of `X` weakly associated to `F` (Stacks 0CTW).  So
`F|_U` has no weakly associated point, hence vanishes by the scheme case, Stacks 05AP.  The
sections of `F` over `U` are the sections of `F|_U` over the whole scheme of the chart, so they
vanish as well.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_restrictToChart_eq_empty`: the restriction of
  a quasi-coherent module without weakly associated points to an étale scheme chart has no
  weakly associated point.
* `AlgebraicGeometry.Space.isZero_of_weaklyAssociatedPoints_eq_empty`: a quasi-coherent
  `𝒪_X`-module with no weakly associated point is zero.
* `AlgebraicGeometry.Space.isZero_iff_weaklyAssociatedPoints_eq_empty`: **Stacks 0CU0.**

## References

* [Stacks Project, Tag 0CU0](https://stacks.math.columbia.edu/tag/0CU0)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 05AP](https://stacks.math.columbia.edu/tag/05AP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- If a quasi-coherent `𝒪_X`-module has no weakly associated point, neither has its
restriction to the scheme of an étale chart: a weakly associated point of the restriction maps
to a weakly associated point of the module by Stacks 0CTW. -/
theorem weaklyAssociatedPoints_restrictToChart_eq_empty (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (h : weaklyAssociatedPoints B S hS X F = ∅)
    (U : SmallEtale B S hS X.1) :
    Stacks.Divisors.weaklyAssociatedPoints (restrictToChart B S hS X.2 F U) = ∅ :=
  Set.eq_empty_of_forall_notMem fun u hu =>
    Set.eq_empty_iff_forall_notMem.mp h _
      ((isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X F U u).mp hu)

/-- The sections of a quasi-coherent `𝒪_X`-module with no weakly associated point over an
étale chart `U` form a subsingleton.

The restriction of the module to the scheme of `U` vanishes by Stacks 05AP, and its sections
over the whole scheme are the sections of the module over the chart that the whole scheme cuts
out, which is `U` itself. -/
theorem subsingleton_sections_of_weaklyAssociatedPoints_eq_empty
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (h : weaklyAssociatedPoints B S hS X F = ∅) (U : SmallEtale B S hS X.1) :
    Subsingleton (F.val.obj (op U)) := by
  have : (restrictToChart B S hS X.2 F U).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F ‹_› U
  have hz : IsZero (chartRestrictionSheaf B S hS X F U) :=
    ((_root_.AlgebraicGeometry.isZero_iff_weaklyAssociatedPoints_eq_empty _).mpr
      (weaklyAssociatedPoints_restrictToChart_eq_empty B S hS X F h U)).of_iso
      (restrictToChartIsoChartRestrictionSheaf B S hS X F U).symm
  have htop : Subsingleton ((chartRestrictionSheaf B S hS X F U).val.obj (op ⊤)) :=
    AddCommGrpCat.subsingleton_of_isZero
      (Functor.map_isZero ((evaluation _ _).obj (op ⊤))
        (Functor.map_isZero (PresheafOfModules.toPresheaf.{u} _)
          (Functor.map_isZero (SheafOfModules.forget _) hz)))
  have hinj : Function.Injective
      (F.val.presheaf.map (chartOpensTopHom B S hS X U).op) :=
    (ConcreteCategory.bijective_of_isIso
      (F.val.presheaf.mapIso (asIso (chartOpensTopHom B S hS X U)).op).hom).1
  refine ⟨fun a b => hinj ?_⟩
  exact ULift.up_injective (htop.elim (ULift.up _) (ULift.up _))

/-- **Stacks 0CU0, the substantive direction.** A quasi-coherent `𝒪_X`-module on an algebraic
space with no weakly associated point is zero. -/
theorem isZero_of_weaklyAssociatedPoints_eq_empty (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (h : weaklyAssociatedPoints B S hS X F = ∅) : IsZero F := by
  refine (IsZero.iff_id_eq_zero F).mpr ?_
  ext U s
  exact (subsingleton_sections_of_weaklyAssociatedPoints_eq_empty B S hS X F h U.unop).elim _ _

/-- **Stacks 0CU0.** A quasi-coherent `𝒪_X`-module on an algebraic space is zero if and only if
it has no weakly associated point. -/
@[stacks 0CU0]
theorem isZero_iff_weaklyAssociatedPoints_eq_empty (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] : IsZero F ↔ weaklyAssociatedPoints B S hS X F = ∅ :=
  ⟨weaklyAssociatedPoints_eq_empty_of_isZero B S hS X F,
    isZero_of_weaklyAssociatedPoints_eq_empty B S hS X F⟩

end AlgebraicGeometry.Space

end

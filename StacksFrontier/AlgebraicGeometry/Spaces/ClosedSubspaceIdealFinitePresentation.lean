module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.IdealSheafFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed subspace with finitely generated defining ideal is of finite presentation

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S` contained in a big
fppf site `B`.  The inclusion `i : Z ⟶ X` is of finite presentation as soon as the defining
ideal `𝓘_Z` of Stacks 083B is finitely generated over every *affine* étale chart of `X`.

This is the criterion that the finite-presentation clauses of the Fitting stratification
consume, and it is proved here with nothing assumed.  It is **not** the hypothesis `hchart` of
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`:
that hypothesis compares finite type of `𝓘_Z` *as a module on the small étale site* with finite
generation of the chart-level ideals, a comparison which is still missing.  Finite generation
over the affine charts is the right-hand side of that comparison on its own, and it is all the
criterion of Stacks 084Q needs.

## Main results

* `AlgebraicGeometry.Space.locallyOfFinitePresentation_rep_snd_of_fg_definingIdealAt`: over an
  affine étale chart, the base-changed closed immersion of schemes is locally of finite
  presentation when the defining ideal there is finitely generated.
* `AlgebraicGeometry.Space.locallyOfFinitePresentation_rep_snd_of_forall_fg_definingIdealAt`:
  the same over an arbitrary étale chart, by Zariski locality at the target.
* `AlgebraicGeometry.Space.isFinitePresentation_subspaceInclusion_of_forall_fg_definingIdealAt`:
  **the inclusion of a closed subspace whose defining ideal is finitely generated over every
  affine étale chart is of finite presentation.**

## Implementation notes

Over an affine étale chart `U` the ideal sheaf cut out by the base change `Z ×_X U ⟶ U` is the
ideal sheaf of the global-sections ideal `𝓘_Z(U)`, which is
`AlgebraicGeometry.Space.ker_rep_snd_eq_ofIdealTop_definingIdealAt`.  Finite generation of a
sheaf of ideals over one affine open covering the scheme gives it over every affine open
(`Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover`), so the case of schemes
`AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker` applies.

An arbitrary étale chart `q : h_V ⟶ X` is cut into the affine opens of `V`.  Each affine open
`A` of `V` is again an object of the site (`AlgebraicGeometry.Space.openSiteObject`) and
`A ⟶ V ⟶ X` is again an étale chart, so the affine case applies to it; and the base change of
`Z` over that chart is the restriction of the base change over `q` to `A`, because the chart
square over `A` is obtained from the one over `V` by pasting with the pullback square of the
open immersion.  Local finite presentation is Zariski local at the target, which assembles the
pieces.

From the chart condition to the morphism of spaces is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_forall_etale_chart`: a representable morphism
whose represented base change to every étale chart of the target has an étale-local property has
it on every chart square.  The remaining two conjuncts of finite presentation hold for every
closed immersion.

## References

* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

private instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Over an affine étale chart a closed subspace with finitely generated defining ideal is
cut out by a locally finitely presented closed immersion of schemes.**  The ideal sheaf of the
base change `Z ×_X U ⟶ U` is the ideal sheaf of the global-sections ideal `𝓘_Z(U)`, so finite
generation of that ideal gives finite generation over every affine open of `U`. -/
@[sga "3 XI 6.4" "special case"]
theorem locallyOfFinitePresentation_rep_snd_of_fg_definingIdealAt
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (U : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)]
    (hfg : (definingIdealAt B S hS X Z (op U)).FG) :
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)) := by
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)) := Z.2.2.property_snd _
  rw [_root_.AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker]
  have htop : (⊤ : ((BigFppfOver.toScheme B S hS).obj U.1.left).Opens) ∈
      ((BigFppfOver.toScheme B S hS).obj U.1.left).affineOpens := isAffineOpen_top _
  rw [definingIdealAt_eq_ker, Scheme.Γ_map_op] at hfg
  refine Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover _
    (fun _ : Unit => (⟨⊤, htop⟩ :
      ((BigFppfOver.toScheme B S hS).obj U.1.left).affineOpens)) (by simp) ?_
  intro _
  rw [Scheme.Hom.ker_apply]
  exact hfg

/-- **The base change of a closed subspace over an arbitrary étale chart is locally of finite
presentation** when the defining ideal is finitely generated over every affine étale chart: the
chart is cut into its affine opens, each of which is again an affine étale chart, and the base
change over an affine open is the restriction of the base change over the chart. -/
theorem locallyOfFinitePresentation_rep_snd_of_forall_fg_definingIdealAt
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (hfg : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        (definingIdealAt B S hS X Z (op U)).FG)
    {V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ X.1)
    (hq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hmul := isMultiplicative_presheaf_etale B S hS
  have := hmul.toIsStableUnderComposition
  have _ : _root_.AlgebraicGeometry.IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) :=
    _root_.AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  refine _root_.AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    (fun A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens => (A : _))
    (_root_.AlgebraicGeometry.iSup_affineOpens_eq_top _) ?_
  intro A
  set iA : openSiteObject B S hS V A.1 ⟶ V := openSiteObjectHom B S hS V A.1
  have hjA : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map iA ≫ q) :=
    MorphismProperty.comp_mem _ _ _
      (presheaf_etale_yonedaMap_openSiteObjectHom B S hS V A.1) hq
  set U' : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map iA ≫ q), hjA⟩ with hU'
  have hU'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj U'.1.left) := by
    have : (BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS V A.1) =
        (A.1 : ((BigFppfOver.toScheme B S hS).obj V).Opens).toScheme := rfl
    rw [hU']
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS V A.1))
    rw [this]
    exact A.2
  have hP' := locallyOfFinitePresentation_rep_snd_of_fg_definingIdealAt B S hS X Z U'
    (hfg U' hU'aff)
  -- the chart square over the affine open is the chart square over `V` restricted to it
  set k : U' ⟶ (⟨CostructuredArrow.mk q, hq⟩ : SmallEtale B S hS X.1) :=
    ObjectProperty.homMk (CostructuredArrow.homMk iA rfl)
  set ℓ := Z.2.2.rep.lift (Z.2.2.rep.fst U'.1.hom)
    (Z.2.2.rep.snd U'.1.hom ≫ k.hom.left)
    (representablePullback_lift_cond B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep k)
  have htop : IsPullback ℓ (Z.2.2.rep.snd (yoneda.map iA ≫ q))
      (Z.2.2.rep.snd q) iA :=
    IsPullback.of_map_of_faithful yoneda (representablePullback_isPullback B S hS
      (subspaceInclusion B S hS X Z) Z.2.2.rep k)
  have hmapiA : (BigFppfOver.toScheme B S hS).map iA =
      (A.1 : ((BigFppfOver.toScheme B S hS).obj V).Opens).ι :=
    map_openSiteObjectHom B S hS V A.1
  have hsq : IsPullback
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (yoneda.map iA ≫ q)))
      ((BigFppfOver.toScheme B S hS).map ℓ)
      (A.1 : ((BigFppfOver.toScheme B S hS).obj V).Opens).ι
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)) := by
    rw [← hmapiA]
    exact (htop.map (BigFppfOver.toScheme B S hS)).flip
  have hiso := IsPullback.isoIsPullback_hom_fst _ _
    (_root_.AlgebraicGeometry.isPullback_morphismRestrict
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)) A.1) hsq
  rw [← hiso]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) _ _).mpr hP'

/-- **The inclusion of a closed subspace whose defining ideal is finitely generated over every
affine étale chart is of finite presentation.**  This is the criterion of Stacks 084Q in the
form the Fitting stratification supplies it, with nothing assumed.

The chart condition of Stacks 03MJ is reached through
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_forall_etale_chart`: a closed immersion is
representable, and its represented base change to every étale chart of the target is locally of
finite presentation by
`AlgebraicGeometry.Space.locallyOfFinitePresentation_rep_snd_of_forall_fg_definingIdealAt`.  The
remaining two conjuncts of finite presentation hold for every closed immersion. -/
@[sga "3 XI 6.4" "partial"]
theorem isFinitePresentation_subspaceInclusion_of_forall_fg_definingIdealAt
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (hfg : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        (definingIdealAt B S hS X Z (op U)).FG) :
    IsFinitePresentation B S hS (subspaceInclusion B S hS X Z).hom := by
  refine (isFinitePresentation_iff_isLocallyOfFinitePresentation B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).mpr ?_
  exact holdsOnEveryEtaleChart_of_forall_etale_chart B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    Z.2.1 X.2 (subspaceInclusion B S hS X Z).hom Z.2.2.rep
    fun _ q hq =>
      locallyOfFinitePresentation_rep_snd_of_forall_fg_definingIdealAt B S hS X Z hfg q hq

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport

/-!
# The chart comparisons of Stacks 0GC0, on weakly admissible presentations

The chart-tested conditions of **Stacks 0GC0** agree with those of **Stacks 0ANW** under
`AlgebraicGeometry.FormalSpace.ChartPresentationIsAdicStarOfWeaklyAdmissible`: every weakly
admissible topological ring presenting an affine chart of a locally adic\* formal algebraic space
is adic\*. This is implied by `AlgebraicGeometry.FormalSpace.ChartPresentationIsAdicStar`, which
asks the same of every presenting topological ring.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ChartPresentationIsAdicStarOfWeaklyAdmissible`: the chart-type
  input on weakly admissible presentations.

## Main results

* `AlgebraicGeometry.FormalSpace.isAdicStar_presentation`: every weakly admissible topological
  ring presenting an adic\* affine formal algebraic space is adic\*.
* `chartPresentationIsAdicStarOfWeaklyAdmissible_of_chartPresentationIsAdicStar`:
  the chart-type input on every presentation implies the one on weakly admissible ones.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_adicStar_iff_of_isWeaklyAdmissible`:
  the equivalence of conditions (1) and (2) of **Stacks 0GBW**, read on charts.
* `hasPropertyOnEveryAffineEtaleDiagram_adicStar_iff_of_isWeaklyAdmissible`,
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_adicStar_iff_of_isWeaklyAdmissible`
  and
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_adicStar_iff_of_isWeaklyAdmissible`:
  conditions (1), (2) and (3) of Stacks 0GC0 agree with those of Stacks 0ANW.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GC0](https://stacks.math.columbia.edu/tag/0GC0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart-type input on weakly admissible presentations -/

/-- Every weakly admissible topological ring presenting an affine formal algebraic space
representable étale over a locally adic\* formal algebraic space over `S` is adic and has a
finitely generated ideal of definition. -/
abbrev ChartPresentationIsAdicStarOfWeaklyAdmissible : Prop :=
  ∀ (Z : FppfSheaf B S hS), IsLocallyAdicStar B S hS Z →
    ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a →
      ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [IsLinearTopology A A], TopologicalRing.IsWeaklyAdmissible A →
        ∀ (E : QuotientSystem B S hS A), (U ≅ formalSpectrum E) →
        TopologicalRing.IsAdicStar A

variable {B S hS}

/-- **Every weakly admissible topological ring presenting an adic\* affine formal algebraic
space is adic\*.** -/
theorem isAdicStar_presentation {U : FppfSheaf B S hS} (hU : IsAdicStar B S hS U)
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (hR : TopologicalRing.IsWeaklyAdmissible R)
    (E : QuotientSystem B S hS R) (e : U ≅ formalSpectrum E) :
    TopologicalRing.IsAdicStar R := by
  obtain ⟨-, A, _, _, _, _, hApres, hAadic, hAfg⟩ := hU
  obtain ⟨φ, hφ, hφ'⟩ := exists_continuous_ringEquiv_of_isPresentingRing hApres
    (isPresentingRing_of_spfPresentation B S hS ⟨R, E, ⟨e⟩⟩ hR)
  exact ⟨TopologicalRing.isAdic_of_ringEquiv φ hφ hφ' hAadic,
    TopologicalRing.exists_fg_isIdealOfDefinition_of_ringEquiv φ hφ hφ' hAfg⟩

/-- The chart-type input on every presentation implies the one on weakly admissible
presentations. -/
theorem chartPresentationIsAdicStarOfWeaklyAdmissible_of_chartPresentationIsAdicStar
    (hchart : ChartPresentationIsAdicStar B S hS) :
    ChartPresentationIsAdicStarOfWeaklyAdmissible B S hS :=
  fun Z hZ U a hU ha A _ _ _ _ _ E e ↦ hchart Z hZ U a hU ha A E e

/-! ### Stacks 0GBW on charts -/

/-- **The equivalence of conditions (1) and (2) of Stacks 0GBW, read on charts.** Let
`t : U ⟶ V` be a map of affine formal algebraic spaces over `S` all of whose presenting
topological rings are adic\*. Then `t` corresponds to an adic, topologically of finite type
arrow of `WAdm^{adic*}` exactly when it corresponds to a taut, topologically of finite type
arrow of `WAdm^{count}`. -/
theorem hasPropertyOnAffineChartMap_adicStar_iff_of_isWeaklyAdmissible
    {U V : FppfSheaf B S hS} (t : U ⟶ V)
    (hU : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], TopologicalRing.IsWeaklyAdmissible R →
      ∀ (E : QuotientSystem B S hS R), (U ≅ formalSpectrum E) →
      TopologicalRing.IsAdicStar R)
    (hV : ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A], TopologicalRing.IsWeaklyAdmissible A →
      ∀ (D : QuotientSystem B S hS A), (V ≅ formalSpectrum D) →
      TopologicalRing.IsAdicStar A) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom t ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom t := by
  constructor
  · intro h A R _ _ _ _ _ _ _ _ hAcount hRcount hA D E eU eV g hg
    have hAstar := hV A hAcount.1 D eV
    have hRstar := hU R hRcount.1 E eU
    exact ((Rig.adicFiniteType_tfae g.toRingHom hAstar.1 hRstar.1
      hAstar.2 hRstar.2).out 1 2).mp (h A R hAstar hRstar hA D E eU eV g hg)
  · intro h A R _ _ _ _ _ _ _ _ hAstar hRstar hA D E eU eV g hg
    exact ((Rig.adicFiniteType_tfae g.toRingHom hAstar.1 hRstar.1
      hAstar.2 hRstar.2).out 1 2).mpr (h A R
        (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hAstar)
        (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hRstar) hA D E eU eV g hg)

/-- The chart comparison of `hasPropertyOnAffineChartMap_adicStar_iff_of_isWeaklyAdmissible` for
a map between an affine representable étale chart of a locally adic\* formal algebraic space `X`
and one of a locally adic\* formal algebraic space `Y`, whose weakly admissible presenting rings
are adic\* by `hchart`. -/
theorem hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale_of_isWeaklyAdmissible
    (hchart : ChartPresentationIsAdicStarOfWeaklyAdmissible B S hS) {X Y : FppfSheaf B S hS}
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    {U V : FppfSheaf B S hS} (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom t ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom t :=
  hasPropertyOnAffineChartMap_adicStar_iff_of_isWeaklyAdmissible t
    (fun R _ _ _ _ hR E e ↦ hchart X hX U a hU ha R hR E e)
    (fun A _ _ _ _ hA D e ↦ hchart Y hY V b hV hb A hA D e)

/-! ### The three chart-tested conditions -/

/-- Condition (1) of **Stacks 0GC0** agrees with condition (1) of **Stacks 0ANW**: on the
charts of a square over `f`, being adic and topologically of finite type on `WAdm^{adic*}` is
being taut and topologically of finite type on `WAdm^{count}`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_adicStar_iff_of_isWeaklyAdmissible
    (hchart : ChartPresentationIsAdicStarOfWeaklyAdmissible B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f :=
  forall₅_congr fun _ _ a b t ↦ forall₄_congr fun hU hV ha hb ↦ imp_congr_right fun _ ↦
    hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale_of_isWeaklyAdmissible
      hchart hX hY a b t hU hV ha hb

/-- Condition (2) of **Stacks 0GC0** agrees with condition (2) of **Stacks 0ANW**. -/
theorem hasPropertyAfterTargetCover_adicStar_iff_of_isWeaklyAdmissible
    (hchart : ChartPresentationIsAdicStarOfWeaklyAdmissible B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f ↔
      HasPropertyAfterTargetCover B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f :=
  exists₃_congr fun _ _ v ↦ and_congr_right fun hVcover ↦ forall_congr' fun j ↦
    exists₃_congr fun _ _ w ↦ and_congr_right fun hUcover ↦ forall_congr' fun i ↦
      hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale_of_isWeaklyAdmissible
        hchart hX hY (w i ≫ pullback.snd (v j) f) (v j) (w i ≫ pullback.fst (v j) f)
        (hUcover.1 i) (hVcover.1 j)
        (IsRepresentableEtale.comp B S hS (hUcover.2.1 i)
          (isRepresentableEtale_pullback_snd B S hS (v j) f (hVcover.2.1 j)))
        (hVcover.2.1 j)

/-- Condition (3) of **Stacks 0GC0** agrees with condition (3) of **Stacks 0ANW**. -/
theorem hasPropertyAfterSourceCover_adicStar_iff_of_isWeaklyAdmissible
    (hchart : ChartPresentationIsAdicStarOfWeaklyAdmissible B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f ↔
      HasPropertyAfterSourceCover B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f :=
  exists₃_congr fun _ _ u ↦ and_congr_right fun hUcover ↦ forall_congr' fun i ↦
    exists₃_congr fun _ v t ↦ and_congr_right fun hV ↦ and_congr_right fun hv ↦
      and_congr_right fun _ ↦
        hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale_of_isWeaklyAdmissible
          hchart hX hY (u i) v t (hUcover.1 i) hV (hUcover.2.1 i) hv

end AlgebraicGeometry.FormalSpace

end

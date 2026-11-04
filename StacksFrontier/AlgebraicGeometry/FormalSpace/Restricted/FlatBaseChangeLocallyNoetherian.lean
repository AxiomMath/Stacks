module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeChartConditionDirections
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsChartMaps
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChangeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteTypeRefined
public import StacksFrontier.RingTheory.Rig.FlatBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalPropertyRefined

/-!
# Base change of a flat morphism of locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCE** says:

1. if `f` is flat and `g_red : Z_red ⟶ Y_red` is locally of finite type, then the base change
   `X ×_Y Z ⟶ Z` is flat;
2. if `f` is flat and locally of finite type, then `X ×_Y Z ⟶ Z` is flat and locally of finite
   type.

## Main results

* `isFlat_pullback_snd_of_isLocallyOfFiniteTypeOnReductions_of_isLocallyNoetherian`:
  **Stacks 0GCE, part (1)**.
* `isFlat_and_isLocallyOfFiniteType_pullback_snd`: **Stacks 0GCE, part (2)**.

## Implementation notes

All names below are in the namespace `AlgebraicGeometry.FormalSpace`. The proof is the one of the
source. Flatness in the sense of Definition 0GCC is condition (1) of Stacks 0ANG for flat maps of
Noetherian adic rings (`isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`), so both parts are
Stacks 0GBG (`conditions_pullback_snd_of_isStableUnderBaseChangeBy`, for locally Noetherian
formal algebraic spaces) applied to a ring-level stability statement of Stacks 0GCA:

* for part (1), flatness is stable under base change by arrows of finite type on reductions
  (Stacks 0GCA (1)), and the hypothesis on `g_red` is turned into the chart condition by the
  implication (4) ⟹ (1) of Stacks 0GC7
  (`hasPropertyOnEveryAffineEtaleDiagram_of_isLocallyOfFiniteTypeOnReductions`), a Noetherian
  adic ring being countably indexed weakly admissible;
* for part (2), flatness together with being adic and topologically of finite type is stable
  under arbitrary base change (Stacks 0GCA (2), Remark 0GBF), the hypotheses on `f` give the chart
  condition by Stacks 0GC0 read at `WAdm^{Noeth}`
  (`hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_of_isLocallyOfFiniteType`),
  and the second conclusion is also Stacks 0AQ5.

The invariance of the ring properties under isomorphism of source and target, which Situation
0CBA asks of a property of arrows, is supplied from the library's presentation-independence
lemmas.

## References

* [Stacks Project, Tag 0GBF](https://stacks.math.columbia.edu/tag/0GBF)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GC0](https://stacks.math.columbia.edu/tag/0GC0)
* [Stacks Project, Tag 0GC7](https://stacks.math.columbia.edu/tag/0GC7)
* [Stacks Project, Tag 0GCA](https://stacks.math.columbia.edu/tag/0GCA)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCE](https://stacks.math.columbia.edu/tag/0GCE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Flatness together with being adic and topologically of finite type is independent of the
presentations of the source and the target of an arrow of `WAdm^{Noeth}`. -/
theorem isFlatAdicOfFiniteTypeHom_isomorphismInvariant :
    TopologicalRing.IsomorphismInvariant.{u} IsFlatAdicOfFiniteTypeHom
      TopologicalRing.IsNoetherianAdic :=
  TopologicalRing.IsomorphismInvariant.and (TopologicalRing.flat_isomorphismInvariant _)
    (TopologicalRing.IsomorphismInvariant.and (TopologicalRing.isAdic_isomorphismInvariant _)
      (TopologicalRing.isTopologicallyOfFiniteType_isomorphismInvariant _))

/-- A Noetherian adic topological ring is countably weakly admissible. -/
private theorem isCountablyWeaklyAdmissible_of_isNoetherianAdic {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsNoetherianAdic A) : TopologicalRing.IsCountablyWeaklyAdmissible A :=
  ⟨hA.1.isWeaklyAdmissible, Rig.countablyGenerated_nhds_of_isAdicRing hA.1⟩

/-- A Noetherian adic topological ring has a finitely generated ideal of definition. -/
private theorem exists_isIdealOfDefinition_fg_of_isNoetherianAdic {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsNoetherianAdic A) :
    ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG := by
  have : IsNoetherianRing A := hA.2
  obtain ⟨⟨I, hIdef, -⟩, -⟩ := hA.1
  exact ⟨I, hIdef, Ideal.fg_of_isNoetherianRing I⟩

/-- **Stacks 0GCE, part (1).** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally
Noetherian formal algebraic spaces over `S`. If `f` is flat (Definition 0GCC) and the morphism
of reductions `g_red : Z_red ⟶ Y_red` is locally of finite type, then the base change
`X ×_Y Z ⟶ Z` is flat.

Flatness of arrows of `WAdm^{Noeth}` is stable under base change by arrows of finite type on
reductions (Stacks 0GCA, part (1)); the hypothesis on `g_red` gives that property on every affine
étale chart map of `g` by the implication (4) ⟹ (1) of Stacks 0GC7, and Stacks 0GBG transfers
flatness to the second projection. -/
@[stacks 0GCE "part (1)"]
theorem isFlat_pullback_snd_of_isLocallyOfFiniteTypeOnReductions_of_isLocallyNoetherian
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsFlat B S hS f) (hg : IsLocallyOfFiniteTypeOnReductions B S hS g) :
    IsFlat B S hS (pullback.snd f g) := by
  have hg' := hasPropertyOnEveryAffineEtaleDiagram_of_isLocallyOfFiniteTypeOnReductions B S hS g
    (isLocallyCountablyIndexed_of_isLocallyNoetherian' hZ)
    (isLocallyCountablyIndexed_of_isLocallyNoetherian' hY) hg
  refine (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr
    (conditions_pullback_snd_of_isStableUnderBaseChangeBy B S hS TopologicalRing.IsFlatHom
      TopologicalRing.FiniteTypeOnReductionsProperty
      TopologicalRing.flat_isStableUnderBaseChangeByFiniteTypeOnReductions
      (TopologicalRing.flat_isomorphismInvariant _) f g hX hY hZ
      ((isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf) ?_).1
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hR hwa D E eU eV φ hφ
  exact hg' U V a b t hU hV ha hb hsq A R
    (isCountablyWeaklyAdmissible_of_isNoetherianAdic hA)
    (isCountablyWeaklyAdmissible_of_isNoetherianAdic hR) hwa D E eU eV φ hφ

/-- **Stacks 0GCE, part (2).** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally
Noetherian formal algebraic spaces over `S`. If `f` is flat (Definition 0GCC) and locally of
finite type (Stacks 0AM4), then the base change `X ×_Y Z ⟶ Z` is flat and locally of finite
type.

Flatness together with being adic and topologically of finite type is stable under arbitrary
base change of arrows of `WAdm^{Noeth}` (Stacks 0GCA, part (2)); the hypotheses on `f` give that
property on every affine étale chart map of `f` (Stacks 0GC0 read at `WAdm^{Noeth}`), Stacks 0GBF
transfers it to the second projection, and flatness is read off its first conjunct. The second
conclusion is Stacks 0AQ5, which needs neither flatness nor the Noetherian hypotheses. -/
@[stacks 0GCE "part (2)"]
theorem isFlat_and_isLocallyOfFiniteType_pullback_snd {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f) :
    IsFlat B S hS (pullback.snd f g) ∧ IsLocallyOfFiniteType B S hS (pullback.snd f g) := by
  -- `f` has flatness together with the property of Stacks 0GBW on its Noetherian charts: the
  -- first conjunct is Definition 0GCC, the second is Stacks 0ANW (4) ⟹ (1) followed by the
  -- equivalence of conditions (1) and (2) of Stacks 0GBW for Noetherian adic rings.
  have hfchart : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom f := by
    have hP := (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf
    have hT :=
      hasPropertyOnEveryAffineEtaleDiagram_tautTopologicallyOfFiniteType_of_isLocallyOfFiniteType
        f hft
    intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
    refine ⟨hP U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ,
      ((Rig.adicFiniteType_tfae φ.toRingHom φ.continuous hA.1 hRc.1
        (exists_isIdealOfDefinition_fg_of_isNoetherianAdic hA)
        (exists_isIdealOfDefinition_fg_of_isNoetherianAdic hRc)).out 2 1).mp ?_⟩
    exact hT U V a b t hU hV ha hb hsq A R
      (isCountablyWeaklyAdmissible_of_isNoetherianAdic hA)
      (isCountablyWeaklyAdmissible_of_isNoetherianAdic hRc) hwa D E eU eV φ hφ
  have h := (conditions_pullback_snd_of_isStableUnderBaseChangeNoetherian B S hS
    IsFlatAdicOfFiniteTypeHom TopologicalRing.flatAdicFiniteType_isStableUnderBaseChange
    isFlatAdicOfFiniteTypeHom_isomorphismInvariant f g hX hY hZ hfchart).1
  refine ⟨(isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr ?_,
    isLocallyOfFiniteType_pullback_snd_of_isLocallyOfFiniteType f g hft⟩
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hR hwa D E eU eV φ hφ
  exact (h U V a b t hU hV ha hb hsq A R hA hR hwa D E eU eV φ hφ).1

end AlgebraicGeometry.FormalSpace

end

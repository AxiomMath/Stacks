module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.PicardLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGeneratorSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocalFirstOrder
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneratorMultiple
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupFirstCohomologyNaturality

/-!
# Lifting invertible modules along a first-order thickening of algebraic spaces

Let `G ⊂ X` be a first-order thickening of algebraic spaces with ideal sheaf `𝓘` and inclusion
`i : G ⟶ X`. This file proves that if `H²(X, 𝓘) = 0` then every invertible `𝒪_G`-module is
isomorphic to `i^*L` for an invertible `𝒪_X`-module `L`. This is the step of the proof of
Stacks 0DPJ that cites Stacks 0DNM.

The sequence of Stacks 0DNM is the long exact cohomology sequence of
`0 → 𝓘 → 𝒪_X^* → (i_*𝒪_G)^* → 0` on the small étale site of `X`, and its map on `H¹` is restriction
of units. What has to be supplied is that this map is pullback of invertible modules: the map
`H¹(X, 𝒪_X^*) ⟶ H¹(X, (i_*𝒪_G)^*)` carries the class of `L` (Tag 040E) to the class of `i^*L`, read
on the small étale site of `X` as a module over `i_*𝒪_G`. That is the naturality of Tag 040E along
the structure map `𝒪_X ⟶ i_*𝒪_G` (the theorem
`sheafH_map_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm` in the namespace
`Stacks.Cohomology.Torsors.Generators`), applied to the chart components of the unit of the
adjunction of Stacks 03D7 over the squares `V ×_X G ⟶ V`, which are natural, semilinear and carry
free generators to free generators.

## Main definitions

* `AlgebraicGeometry.Space.thickeningChartDiagram`: the square `V ×_X G ⟶ V` of étale charts
  over the inclusion of a thickening.
* `AlgebraicGeometry.Space.thickeningRestrictPullback`: `i^*L`, read on the small étale site of
  `X` as a module over `i_*𝒪_G`.

## Main results

* `AlgebraicGeometry.Space.sheafH_map_thickeningUnitsRestriction_classOf`: restriction of units
  carries the class of `L` to the class of `i^*L`.
* `AlgebraicGeometry.Space.exists_isInvertibleModule_modulePullback_iso_of_subsingleton`: if
  `H²(X, 𝓘) = 0`, every invertible module on `G` is `i^*L` for an invertible `L` on `X`.

No declaration here carries a tag: these are steps of the proof of Stacks 0DPJ.

## References

* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DNM](https://stacks.math.columbia.edu/tag/0DNM)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors.Generators

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- The square of étale scheme charts over the inclusion of a thickening `G ⊂ X` at a chart `V`
of `X`: the base change `V ×_X G` above `V`. -/
abbrev thickeningChartDiagram (hG : IsThickening B S hS X G) (V : SmallEtale B S hS X.1) :
    ChartDiagram B S hS (IsThickening.space B S hS hG).1 X.1
      (IsThickening.inclusion B S hS hG).hom where
  U := (thickeningChartBaseChange B S hS hG).obj V
  V := V
  g := (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom
  comm := ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.isPullback V.1.hom).w

/-- The inverse image `i^*L` of an `𝒪_X`-module along the inclusion of a first-order thickening
`G ⊂ X`, read on the small étale site of `X` as a module over `i_*𝒪_G`: its sections over a chart
`V` of `X` are the sections of `i^*L` over `V ×_X G`. -/
abbrev thickeningRestrictPullback (hG : IsFirstOrderThickening B S hS X G)
    (L : Modules.{u, u} B S hS X.1 X.2) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (thickeningRestrictRingedSite B S hS hG).O) :=
  haveI : (thickeningChartBaseChange B S hS hG.1).IsDenseSubsite
      (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
        (IsThickening.space B S hS hG.1).2).J :=
    thickeningChartBaseChange_isDenseSubsite B S hS hG.1
  (RingedSite.denseRestrictModules (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
      (IsThickening.space B S hS hG.1).2)
    (thickeningChartBaseChange B S hS hG.1)).obj
    ((modulePullback B S hS (IsThickening.inclusion B S hS hG.1)).obj L)

/-- The inverse image of sections along the inclusion of a thickening is natural in the chart. -/
theorem thickeningChartSection_naturality (hG : IsThickening B S hS X G)
    (L : Modules.{u, u} B S hS X.1 X.2) {V W : SmallEtale B S hS X.1} (k : W ⟶ V)
    (s : L.val.obj (op V)) :
    modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG) L
        (thickeningChartDiagram B S hS hG W) (L.val.map k.op s) =
      ((modulePullback B S hS (IsThickening.inclusion B S hS hG)).obj L).val.map
        ((thickeningChartBaseChange B S hS hG).map k).op
        (modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG) L
          (thickeningChartDiagram B S hS hG V) s) := by
  have h := (modulePullbackChartFMap B S hS (IsThickening.inclusion B S hS hG) L).naturality
    (thickeningChartDiagram B S hS hG V) (thickeningChartDiagram B S hS hG W)
    ((thickeningChartBaseChange B S hS hG).map k) k
    ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.lift_snd _ _ _) s
  exact (modulePullbackChartFMap_app B S hS _ L _ _).symm.trans
    (h.trans (congrArg _ (modulePullbackChartFMap_app B S hS _ L _ _)))

/-- **The inverse image of a free generator along the inclusion of a thickening is a free
generator.** Let `L` be an invertible `𝒪_X`-module and `t` a section of `L` over a chart `V`
which generates `L` freely over every chart over `V`. Then its inverse image generates `i^*L`
freely over the base-changed chart `V ×_X G`. -/
theorem bijective_smul_thickeningChartSection (hG : IsThickening B S hS X G)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L)
    (V : SmallEtale B S hS X.1) (t : L.val.obj (op V))
    (ht : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦
        r • @id (L.val.obj (op W)) ((L.val.map k.op).hom t)) :
    Function.Bijective fun r : chartRing B S hS (IsThickening.space B S hS hG).1
        (IsThickening.space B S hS hG).2 ((thickeningChartBaseChange B S hS hG).obj V) ↦
      r • (modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG) L
        (thickeningChartDiagram B S hS hG V) t :
          ((modulePullback B S hS (IsThickening.inclusion B S hS hG)).obj L).val.obj
            (op ((thickeningChartBaseChange B S hS hG).obj V))) := by
  obtain ⟨T, hT, hloc⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS
    (IsThickening.inclusion B S hS hG) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)
    (thickeningChartDiagram B S hS hG V)
    (fun W k ↦ ((L.val.map k.op).hom t : L.val.obj (op W)))
    (fun W W' k g ↦ by
      show (L.val.map g.op).hom ((L.val.map k.op).hom t) = (L.val.map (g ≫ k).op).hom t
      rw [op_comp]
      exact (L.val.map_comp_apply k.op g.op t).symm)
    ht
  refine bijective_smul_of_sieve B S hS (IsThickening.space B S hS hG)
    ((modulePullback B S hS (IsThickening.inclusion B S hS hG)).obj L)
    ((thickeningChartBaseChange B S hS hG).obj V) _ T hT fun W₂ k hk ↦ ?_
  have h1 : (L.val.map (𝟙 V).op).hom t = t := by
    show (L.val.map (𝟙 (op V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ))).hom t = t
    rw [PresheafOfModules.map_id]
    rfl
  have hEq : (chartRestrictLinear
        ((modulePullback B S hS (IsThickening.inclusion B S hS hG)).obj L) k)
        ((modulePullbackChartFMap B S hS (IsThickening.inclusion B S hS hG) L).app
          (thickeningChartDiagram B S hS hG V) t) =
      modulePullbackChartSectionRestrict B S hS (IsThickening.inclusion B S hS hG) L
        (thickeningChartDiagram B S hS hG V) ((L.val.map (𝟙 V).op).hom t) (𝟙 W₂ ≫ k) := by
    rw [h1]
    unfold modulePullbackChartSectionRestrict
    simp only
    rfl
  rw [← modulePullbackChartFMap_app]
  rw [hEq]
  exact hloc k hk W₂ (𝟙 W₂)

/-- The small étale site of the ambient member of a first-order thickening, ringed by `i_*𝒪_G`,
is locally ringed. -/
theorem thickeningRestrictRingedSite_isLocallyRinged (hG : IsFirstOrderThickening B S hS X G) :
    RingedSite.IsLocallyRinged (thickeningRestrictRingedSite B S hS hG) :=
  @RingedSite.isLocallyRinged_denseRestrict _ _ (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
      (IsThickening.space B S hS hG.1).2)
    (thickeningChartBaseChange B S hS hG.1)
    (thickeningChartBaseChange_isDenseSubsite B S hS hG.1)
    (smallEtaleRingedSite_isLocallyRinged B S hS _ _)

/-- The inverse image of an invertible module, read on the ambient site over `i_*𝒪_G`, is
invertible. -/
theorem isInvertible_thickeningRestrictPullback (hG : IsFirstOrderThickening B S hS X G)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L) :
    Stacks.SheafOfModules.IsInvertible (thickeningRestrictRingedSite B S hS hG).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (thickeningRestrictRingedSite B S hS hG).O).2
      (thickeningRestrictPullback B S hS hG L) :=
  @RingedSite.isInvertible_denseRestrictModules_obj _ _ (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
      (IsThickening.space B S hS hG.1).2)
    (thickeningChartBaseChange B S hS hG.1)
    (thickeningChartBaseChange_isDenseSubsite B S hS hG.1) _ _ _ _ _
    (modulePullbackInvertible (IsThickening.inclusion B S hS hG.1) L hL)

/-- The inverse image of sections along the inclusion of a first-order thickening is semilinear
over the structure map `𝒪_X ⟶ i_*𝒪_G`, for the action of units. -/
theorem thickeningChartSection_smul (hG : IsFirstOrderThickening B S hS X G)
    (L : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (v : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op V))ˣ)
    (s : L.val.obj (op V)) :
    modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG.1) L
        (thickeningChartDiagram B S hS hG.1 V) (v.val • s) =
      @HSMul.hSMul ((Stacks.SheafOfModules.Tensor.ringSheaf
          (thickeningRestrictRingedSite B S hS hG).O).obj.obj (op V))
        ((thickeningRestrictPullback B S hS hG L).val.obj (op V))
        ((thickeningRestrictPullback B S hS hG L).val.obj (op V)) _
        (Units.map ((thickeningStructureSharp B S hS hG).hom.app (op V)).hom.toMonoidHom v).val
        (modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG.1) L
          (thickeningChartDiagram B S hS hG.1 V) s) := by
  have h := modulePullbackChartSection_smul B S hS (IsThickening.inclusion B S hS hG.1) L
    (thickeningChartDiagram B S hS hG.1 V) (@id (chartRing B S hS X.1 X.2 V) v.val) s
  exact h

/-- **Restriction of units along a first-order thickening carries the class of `L` to the class
of `i^*L`.** Let `G ⊂ X` be a first-order thickening of algebraic spaces and `L` an invertible
`𝒪_X`-module. The map `H¹(X, 𝒪_X^*) ⟶ H¹(X, (i_*𝒪_G)^*)` induced by restriction of units
carries the class of `L` (Tag 040E) to the class of the inverse image `i^*L`, read on the small
étale site of `X` as a module over `i_*𝒪_G`.

This is Tag 040E's naturality along the structure map `𝒪_X ⟶ i_*𝒪_G`, applied to the chart
components of the unit of the adjunction of Stacks 03D7, which are semilinear and carry free
generators to free generators. -/
theorem sheafH_map_thickeningUnitsRestriction_classOf (hG : IsFirstOrderThickening B S hS X G)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L) :
    haveI := smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2
    haveI : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}) :=
      hasExt_sheaf_smallEtale B S hS X.1
    haveI : HasExt.{u + 1} (Sheaf (RingedSite.smallTopology
      (smallEtaleRingedSite B S hS X.1 X.2)) AddCommGrpCat.{u}) := HasExt.standard _
    Sheaf.H.map.{u + 1} (thickeningUnitsRestriction B S hS hG) 1
        ((h1UnitsAddEquivPicardGroupOfEssentiallySmall (smallEtaleRingedSite B S hS X.1 X.2)
          (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)).symm
          (Stacks.SheafOfModules.Picard.classOf _ _ L hL)) =
      (h1UnitsAddEquivPicardGroupOfEssentiallySmall
          { smallEtaleRingedSite B S hS X.1 X.2 with
            O := (thickeningRestrictRingedSite B S hS hG).O }
          (thickeningRestrictRingedSite_isLocallyRinged B S hS hG)).symm
        (Stacks.SheafOfModules.Picard.classOf _ _ (thickeningRestrictPullback B S hS hG L)
          (isInvertible_thickeningRestrictPullback B S hS hG L hL)) := by
  have := smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2
  have : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}) :=
    hasExt_sheaf_smallEtale B S hS X.1
  have : HasExt.{u + 1} (Sheaf (RingedSite.smallTopology
    (smallEtaleRingedSite B S hS X.1 X.2)) AddCommGrpCat.{u}) := HasExt.standard _
  refine sheafH_map_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm
    (smallEtaleRingedSite B S hS X.1 X.2) (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)
    (thickeningRestrictRingedSite B S hS hG).O
    (thickeningRestrictRingedSite_isLocallyRinged B S hS hG)
    (thickeningStructureSharp B S hS hG) (thickeningUnitsRestriction B S hS hG)
    ?_ L hL
    (thickeningRestrictPullback B S hS hG L)
    (isInvertible_thickeningRestrictPullback B S hS hG L hL)
    (fun U s ↦ modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG.1) L
      (thickeningChartDiagram B S hS hG.1 U.unop) s) ?_ ?_ ?_
  · exact fun U v ↦ thickeningUnitsRestriction_app B S hS hG U v
  · exact fun {U V} f s ↦ thickeningChartSection_naturality B S hS hG.1 L f.unop s
  · rintro ⟨V⟩ v s
    exact thickeningChartSection_smul B S hS hG L V v s
  · rintro ⟨V⟩ s hs W f
    have hnat : ((thickeningRestrictPullback B S hS hG L).val.restrictₛₗ f.op)
        (modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG.1) L
          (thickeningChartDiagram B S hS hG.1 V) s) =
        modulePullbackChartSection B S hS (IsThickening.inclusion B S hS hG.1) L
          (thickeningChartDiagram B S hS hG.1 W) ((L.val.map f.op).hom s) :=
      (thickeningChartSection_naturality B S hS hG.1 L f s).symm
    have h' := bijective_smul_thickeningChartSection B S hS hG.1 L hL W ((L.val.map f.op).hom s)
      fun W' k ↦ by
        exact L.val.map_comp_apply f.op k.op s ▸ hs W' (k ≫ f)
    rw [← hnat] at h'
    exact h'

/-- **Invertible modules lift along a first-order thickening when `H²(X, 𝓘) = 0`.** Let
`G ⊂ X` be a first-order thickening of algebraic spaces with ideal sheaf `𝓘`, and suppose that
the second cohomology of `𝓘` on the small étale site of `X` vanishes. Then every invertible
module `M` on `G` is isomorphic to the inverse image `i^*L` of an invertible `𝒪_X`-module `L`.

The class of `M`, read on the small étale site of `X` as a class in `H¹(X, (i_*𝒪_G)^*)`, has
vanishing boundary in `H²(X, 𝓘)` (the sequence of Stacks 0DNM), so it is the restriction of a
class in `H¹(X, 𝒪_X^*) = Pic(X)`; that class is the class of some invertible `L`, and restriction
of units carries it to the class of `i^*L`
(`AlgebraicGeometry.Space.sheafH_map_thickeningUnitsRestriction_classOf`). Restriction to the
dense subsite of étale charts of `X` is fully faithful, so `i^*L ≅ M`. -/
theorem exists_isInvertibleModule_modulePullback_iso_of_subsingleton
    (hG : IsFirstOrderThickening B S hS X G)
    (h2 : Subsingleton (Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS hG).X₁ 2))
    (M : Modules.{u, u} B S hS (IsThickening.space B S hS hG.1).1
      (IsThickening.space B S hS hG.1).2)
    (hM : IsInvertibleModule (IsThickening.space B S hS hG.1) M) :
    ∃ (L : Modules.{u, u} B S hS X.1 X.2) (_ : IsInvertibleModule X L),
      Nonempty ((modulePullback B S hS (IsThickening.inclusion B S hS hG.1)).obj L ≅ M) := by
  have := smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2
  have : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}) :=
    hasExt_sheaf_smallEtale B S hS X.1
  have : HasExt.{u + 1} (Sheaf (RingedSite.smallTopology
    (smallEtaleRingedSite B S hS X.1 X.2)) AddCommGrpCat.{u}) := HasExt.standard _
  have : (thickeningChartBaseChange B S hS hG.1).IsDenseSubsite
      (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
        (IsThickening.space B S hS hG.1).2).J :=
    thickeningChartBaseChange_isDenseSubsite B S hS hG.1
  let R : RingedSite.{u + 1, u, u} :=
    { smallEtaleRingedSite B S hS X.1 X.2 with O := (thickeningRestrictRingedSite B S hS hG).O }
  let F := RingedSite.denseRestrictModules (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
      (IsThickening.space B S hS hG.1).2)
    (thickeningChartBaseChange B S hS hG.1)
  have hN : Stacks.SheafOfModules.IsInvertible R.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R.O).2 (F.obj M) :=
    RingedSite.isInvertible_denseRestrictModules_obj (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
        (IsThickening.space B S hS hG.1).2)
      (thickeningChartBaseChange B S hS hG.1) M hM
  let c := (h1UnitsAddEquivPicardGroupOfEssentiallySmall R
    (thickeningRestrictRingedSite_isLocallyRinged B S hS hG)).symm
      (Stacks.SheafOfModules.Picard.classOf _ _ (F.obj M) hN)
  obtain ⟨y, hy⟩ := ((exact_unitsRestrictionCohomology B S hS hG 1) c).mp
    (Subsingleton.elim _ _)
  obtain ⟨L, hL, hLy⟩ := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _
    ((h1UnitsAddEquivPicardGroupOfEssentiallySmall (smallEtaleRingedSite B S hS X.1 X.2)
      (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)) y)
  refine ⟨L, hL, ?_⟩
  have hy' : y = (h1UnitsAddEquivPicardGroupOfEssentiallySmall
      (smallEtaleRingedSite B S hS X.1 X.2)
      (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)).symm
        (Stacks.SheafOfModules.Picard.classOf _ _ L hL) :=
    ((h1UnitsAddEquivPicardGroupOfEssentiallySmall (smallEtaleRingedSite B S hS X.1 X.2)
      (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)).symm_apply_apply y).symm.trans
        (congrArg _ hLy.symm)
  have key := sheafH_map_thickeningUnitsRestriction_classOf B S hS hG L hL
  have hcl := (h1UnitsAddEquivPicardGroupOfEssentiallySmall R
    (thickeningRestrictRingedSite_isLocallyRinged B S hS hG)).symm.injective
      (key.symm.trans ((congrArg (Sheaf.H.map.{u + 1} (thickeningUnitsRestriction B S hS hG) 1)
        hy'.symm).trans hy))
  obtain ⟨e⟩ := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ _).mp hcl
  have : F.Full := RingedSite.full_denseRestrictModules _ _ _
  have : F.Faithful := RingedSite.faithful_denseRestrictModules _ _ _
  exact ⟨F.preimageIso e⟩

end AlgebraicGeometry.Space

end

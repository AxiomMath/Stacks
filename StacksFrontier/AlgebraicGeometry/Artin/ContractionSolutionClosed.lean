module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Closedness of the contracted locus of a solution obtained from a functorial bijection

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`,
let `T ⊆ |X|` be the subset `AlgebraicGeometry.Artin.ContractionSituation.contractedLocus` that
Stacks 0GHC attaches to a functorial bijection `F(V) = Mor_S(V, X)`. When `X` is an algebraic
space locally of finite type over `S`, `T` is closed in the point space `|X|` of Stacks 03BY.

## Main results

* `AlgebraicGeometry.Space.locallyOfFiniteType_hom_of_presheafEtale`: an étale chart of a
  presheaf locally of finite type over `S` is locally of finite type over `S` as a scheme.
* `AlgebraicGeometry.Space.isLocallyNoetherian_of_presheafEtale`: over a locally Noetherian
  base, such a chart is a locally Noetherian scheme.
* `AlgebraicGeometry.Artin.ContractionSituation.isClosed_contractedLocus`: the subset
  `T ⊆ |X|` of Stacks 0GHC is closed.

## References

* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale chart of a presheaf locally of finite type over `S` is locally of finite type
over `S`: the structural morphism of the object of the site carrying the chart has that
property. -/
theorem locallyOfFiniteType_hom_of_presheafEtale
    (hft : IsLocallyOfFiniteType B S hS (terminal.from X)) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    LocallyOfFiniteType (B.inclusion.map U.hom) := by
  have hterm : IsTerminal (yoneda.obj (⊤_ (BigFppfOver B S hS))) :=
    isTerminal_yoneda_obj_terminal B S hS
  have hft' : HoldsOnEveryEtaleChart B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (hterm.from X) :=
    holdsOnEveryEtaleChart_of_isTerminal B S hS terminalIsTerminal hterm
      (terminal.from X) (hterm.from X) hft
  have hmap : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (terminal.from U)) :=
    hft' U (⊤_ (BigFppfOver B S hS)) a (yoneda.map (𝟙 _)) (terminal.from U) ha
      (presheaf_yoneda_map_id_etale B S hS _) (hterm.hom_ext _ _)
  rw [← toScheme_map_terminal_from B S hS U]
  infer_instance

/-- An étale chart of a presheaf locally of finite type over a locally Noetherian base is a
locally Noetherian scheme, by Stacks 01T8. -/
theorem isLocallyNoetherian_of_presheafEtale [IsLocallyNoetherian S]
    (hft : IsLocallyOfFiniteType B S hS (terminal.from X)) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
  have _ := locallyOfFiniteType_hom_of_presheafEtale B S hS hft U a ha
  have _ : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map U.hom)

end Space

namespace Artin

attribute [local instance] Space.pointTopology

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)

/-- If `X` is an algebraic space locally of finite type over `S`, the subset `T ⊆ |X|` of
Stacks 0GHC is closed in the point space of Stacks 03BY. -/
theorem isClosed_contractedLocus (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    IsClosed (contractedLocus c α) := by
  have _ : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  have hq := Space.isQuotientMap_pointsMap_of_presheafEtale B S hS a haEtale
    ((Space.surjective_iff_surjective_pointsMap B S hS X hX U a).mp haSurj)
  rw [← hq.isCoinducing.isClosed_preimage]
  exact isClosed_preimage_contractedLocus c α
    ⟨U, Space.isLocallyNoetherian_of_presheafEtale B S hS hft U a haEtale⟩ a

end ContractionSituation

end Artin

end AlgebraicGeometry

end

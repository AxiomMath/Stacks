module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# The global functions of a representable algebraic space

For an object `T` of the big fppf site of `S`, restriction of global regular functions from the
presheaf `yoneda.obj T` to the identity chart is a ring isomorphism

`Γ(yoneda.obj T, 𝒪) ≅ Γ(T, 𝒪_T)`.

## Main definitions

* `AlgebraicGeometry.Space.yonedaEtaleChart`: the identity chart of a representable presheaf, as
  an object of its small étale site.
* `AlgebraicGeometry.Space.yonedaGlobalFunctions`: the global function of `yoneda.obj T`
  attached to a regular function on `T`.
* `AlgebraicGeometry.Space.globalFunctionsYonedaEquiv`: the resulting ring isomorphism.

## Main results

* `AlgebraicGeometry.Space.bijective_globalFunctionsChartRestriction_yonedaEtaleChart`:
  restriction of global functions from `yoneda.obj T` to the identity chart is bijective.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity chart of the representable presheaf `yoneda.obj T`, as an object of its small
étale site. -/
def yonedaEtaleChart (T : BigFppfOver B S hS) : SmallEtale B S hS (yoneda.obj T) :=
  ⟨CostructuredArrow.mk (𝟙 (yoneda.obj T)),
    show (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T)) by
      simpa using (presheaf_yoneda_map_etale_iff B S hS (𝟙 T)).2 inferInstance⟩

/-- A morphism `g : k ⟶ j` of étale charts of `yoneda.obj T`, read as a morphism of the site,
commutes with the morphisms of the site into `T` underlying the two charts. -/
theorem toOver_map_comp_yoneda_preimage (T : BigFppfOver B S hS)
    {j k : SmallEtale B S hS (yoneda.obj T)} (g : k ⟶ j) :
    (SmallEtale.toOver B S hS (yoneda.obj T)).map g ≫ yoneda.preimage j.1.hom
      = yoneda.preimage k.1.hom := by
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
  exact CostructuredArrow.w ((SmallEtale.inclusion B S hS (yoneda.obj T)).map g)

/-- The global function of `yoneda.obj T` attached to a regular function `s` on `T`: at an étale
chart it is the pullback of `s` along the morphism of the site underlying the chart. -/
noncomputable def yonedaGlobalFunctions (T : BigFppfOver B S hS)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    globalFunctions B S hS (yoneda.obj T) :=
  ⟨fun j => (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage j.unop.1.hom)))).hom s, by
    intro j k g
    have h := gamma_map_comp
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (yoneda.obj T)).map g.unop))
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage j.unop.1.hom)) s
    rwa [← Functor.map_comp, toOver_map_comp_yoneda_preimage B S hS T g.unop] at h⟩

/-- Restriction of the global function attached to a regular function on the representing object,
back to the identity chart, is that function. -/
theorem globalFunctionsChartRestriction_yonedaGlobalFunctions (T : BigFppfOver B S hS)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    globalFunctionsChartRestriction B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
        (yonedaEtaleChart B S hS T) (yonedaGlobalFunctions B S hS T s) = s := by
  change (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
    (yoneda.preimage (𝟙 (yoneda.obj T)))))).hom s = s
  have h : yoneda.preimage (𝟙 (yoneda.obj T)) = 𝟙 T := by
    apply yoneda.map_injective
    rw [Functor.map_preimage, CategoryTheory.Functor.map_id]
  rw [h]
  simp
  rfl

/-- Restriction of global functions from `yoneda.obj T` to the identity chart is bijective. -/
theorem bijective_globalFunctionsChartRestriction_yonedaEtaleChart (T : BigFppfOver B S hS) :
    Function.Bijective (globalFunctionsChartRestriction B S hS
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ (yonedaEtaleChart B S hS T)) := by
  refine ⟨injective_globalFunctionsChartRestriction_of_isSurjective B S hS _ _ fun x => ⟨x, ?_⟩,
    fun s => ⟨yonedaGlobalFunctions B S hS T s,
      globalFunctionsChartRestriction_yonedaGlobalFunctions B S hS T s⟩⟩
  change pointsMap B S hS (yoneda.obj T) (𝟙 (yoneda.obj T)) x = x
  rw [pointsMap_id, id_eq]

/-- The ring of global functions of `yoneda.obj T` is isomorphic, by restriction to the identity
chart, to the ring of regular functions on `T`. -/
noncomputable def globalFunctionsYonedaEquiv (T : BigFppfOver B S hS) :
    globalFunctions B S hS (yoneda.obj T) ≃+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  RingEquiv.ofBijective _ (bijective_globalFunctionsChartRestriction_yonedaEtaleChart B S hS T)

end AlgebraicGeometry.Space

end

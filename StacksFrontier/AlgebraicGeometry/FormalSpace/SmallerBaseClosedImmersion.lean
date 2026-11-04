module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseSheaves

/-!
# Closed immersions of formal algebraic spaces and a change of base

Let `g : V ⟶ S` be a morphism of the big fppf site. Fppf sheaves of `Type (u + 1)` on the big fppf
site of `V` are fppf sheaves on the big fppf site of `S` over the representable sheaf of `g`
(Stacks 04SG, `AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor`). This file shows that a
closed immersion of formal algebraic spaces (Stacks 0ANP) can be checked after this change of base.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_of_relative_smallerBaseULiftMap`: a property of
  morphisms of schemes holding for every represented base change of the attached morphism over `S`
  holds for every represented base change of the morphism over `V`; the converse of
  `AlgebraicGeometry.FormalSpace.relative_smallerBaseULiftMap`.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_smallerBaseSheafFunctor_map`: a morphism of
  fppf sheaves over `V` whose attached morphism over `S` is a closed immersion is a closed
  immersion.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- **A relative property descends along the change of base.** If every represented base change
of the attached morphism `k_S` on the big fppf site of `S` has a property `Q` of morphisms of
schemes, then so does every represented base change of `k` on the big fppf site of `V`. This
is the converse of `AlgebraicGeometry.FormalSpace.relative_smallerBaseULiftMap`. -/
theorem relative_of_relative_smallerBaseULiftMap (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q] {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (k : G ⟶ G')
    (hk : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative
      uliftYoneda.{u + 1} (smallerBaseULiftMap B V S hV hS g k)) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B V hV)).relative
      uliftYoneda.{u + 1} k := by
  refine MorphismProperty.relative.of_exists (F := uliftYoneda.{u + 1}) ?_
  intro U₀ ξ₀
  have hpull := hk.1.isPullback (smallerBaseChart B V S hV hS g ξ₀)
  have hQ := hk.property_snd (smallerBaseChart B V S hV hS g ξ₀)
  set T' := hk.1.pullback (smallerBaseChart B V S hV hS g ξ₀)
  set snd' := hk.1.snd (smallerBaseChart B V S hV hS g ξ₀)
  set fst' := hk.1.fst (smallerBaseChart B V S hV hS g ξ₀)
  obtain ⟨ψ, hψ, a₀, ha₀⟩ := exists_smallerBaseChart B V S hV hS g T' fst'
  have hw : snd'.left ≫ U₀.hom = ψ := by
    have h1 := congrArg (· ≫ smallerBaseULiftHom B V S hV hS g G') hpull.w
    simp only [Category.assoc, smallerBaseULiftMap_comp_hom, smallerBaseChart_comp_hom] at h1
    rw [ha₀, Category.assoc, smallerBaseChart_comp_hom, ← Functor.map_comp,
      ← Functor.map_comp] at h1
    have h2 := congrArg (fun m => m.left) (uliftYoneda.{u + 1}.map_injective h1)
    simpa [relocalizeBaseHom, relocalizeOverHom] using h2.symm
  let p : (Over.mk ψ : BigFppfOver B V hV) ⟶ U₀ := Over.homMk snd'.left hw
  refine ⟨Over.mk ψ, a₀, p, ?_, hQ⟩
  refine isPullback_of_isPullback_smallerBaseULiftMap B V S hV hS g ?_
  refine hpull.of_iso
    (uliftYoneda.{u + 1}.mapIso (asIso (relocalizeBaseHom B V S hV hS g hψ)) ≪≫
      (smallerBaseULiftYonedaIso B V S hV hS g _).symm)
    (Iso.refl _) (smallerBaseULiftYonedaIso B V S hV hS g U₀).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [ha₀]
    exact (Category.comp_id _).trans (Category.assoc _ _ _).symm
  · have hnat := smallerBaseULiftYonedaIso_hom_naturality B V S hV hS g p
    have hnat' : (smallerBaseULiftYonedaIso B V S hV hS g (Over.mk ψ)).inv ≫
        smallerBaseULiftMap B V S hV hS g (uliftYoneda.{u + 1}.map p) =
        uliftYoneda.{u + 1}.map ((Over.map g).map p) ≫
          (smallerBaseULiftYonedaIso B V S hV hS g U₀).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have hrel : relocalizeBaseHom B V S hV hS g hψ ≫ (Over.map g).map p = snd' :=
      Over.OverMorphism.ext (by simp [relocalizeBaseHom, p])
    simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Category.assoc, hnat',
      ← Functor.map_comp_assoc, hrel]
  · simp
  · simp [smallerBaseChart]

/-- **Closed immersions descend along the change of base.** A morphism of fppf sheaves over `V`
whose attached morphism over `S` is a closed immersion of formal algebraic spaces (Stacks
0ANP) is a closed immersion over `V`. -/
theorem isClosedImmersion_of_smallerBaseSheafFunctor_map {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    (h : IsClosedImmersion B S hS ((smallerBaseSheafFunctor B V S hV hS g).map f)) :
    IsClosedImmersion B V hV f := by
  obtain ⟨hrep, hprop⟩ := h
  refine ⟨(isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V S hV hS g f.hom).mp
    hrep, fun U₀ ξ₀ => ?_⟩
  let Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hQ : Q.relative uliftYoneda.{u + 1}
      (pullback.fst (smallerBaseChart B V S hV hS g ξ₀)
        (smallerBaseULiftMap B V S hV hS g f.hom)) :=
    hprop _ (smallerBaseChart B V S hV hS g ξ₀)
  have : (Q.relative uliftYoneda.{u + 1}).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange Q).respectsIso
  have hsq := isPullback_smallerBaseChart_pullback B V S hV hS g f.hom ξ₀
  have hQ' : Q.relative uliftYoneda.{u + 1}
      (smallerBaseULiftMap B V S hV hS g (pullback.fst ξ₀ f.hom)) := by
    refine (MorphismProperty.cancel_right_of_respectsIso (Q.relative uliftYoneda.{u + 1}) _
      (smallerBaseULiftYonedaIso B V S hV hS g U₀).hom).1 ?_
    rw [← hsq.isoPullback_hom_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso (Q.relative uliftYoneda.{u + 1}) _ _).2 hQ
  exact relative_of_relative_smallerBaseULiftMap B V S hV hS g _ _ hQ'

end AlgebraicGeometry.FormalSpace

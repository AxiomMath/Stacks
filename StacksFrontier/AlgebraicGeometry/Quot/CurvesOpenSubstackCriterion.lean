module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayDimOne
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Classifying morphisms factoring through an open substack of curves, up to 2-isomorphism

Let `P` be a property of families of curves satisfying condition (o) of Section 0E0E
(`AlgebraicGeometry.IsOpenCurvesLocus`), so that the families having `P` form an open substack
`Curves^P` of `Curves` (`AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion`). The
classifying morphism `S → Curves` of a family of curves `X → S` is determined only up to
2-isomorphism. This file states the universal properties (1) and (2) of Stacks 0E0E for every
classifying morphism, with factorizations through `Curves^P` taken up to a 2-isomorphism over
the site:

* (1) the classifying morphism of `X → S` factors through `Curves^P` if and only if `X → S` has
  `P`;
* (2) given a proper scheme `X` of dimension `≤ 1` over a field `k`, the classifying morphism
  `Spec(k) → Curves` factors through `Curves^P` if and only if `X → Spec(k)` has `P`.

## Main results

* `AlgebraicGeometry.Stack.exists_factorization_objectPropertyInclusion_iff`: a 1-morphism over
  the site factors through a strictly full subcategory, up to 2-isomorphism, exactly when its
  image lies in it.
* `AlgebraicGeometry.factorsThrough_curvesSubstack_iff`: universal property (1).
* `AlgebraicGeometry.factorsThrough_curvesSubstack_over_field_iff`: universal property (2).

## Implementation notes

A classifying morphism of a family of curves `X → S` is a scheme-valued point
`z : (Sch/S) → Curves` together with an isomorphism `z(S) ≅ X`. A factorization through
`Curves^P` is a 1-morphism into `Curves^P` over the site whose composite with the inclusion is
2-isomorphic to `z`.

In (2) the family of curves attached to `X → Spec(k)` is
`AlgebraicGeometry.curveFamilyOfSchemeMorphism`; its flatness and finite presentation hold over
a field, and its quasi-compactness, separatedness and quasi-separatedness are those of the proper
morphism `X → Spec(k)`, so the hypotheses are exactly those of the source.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u v₂ u₂

namespace Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A 1-morphism factors through a strictly full subcategory exactly when its image lies in
it.** For a property `Q` of the objects of a category `𝒟` over the big fppf site, closed under
isomorphisms, a 1-morphism `f : 𝒞 → 𝒟` over the site factors through the full subcategory on
`Q`, up to a 2-isomorphism over the site, if and only if every object in the image of `f` has
`Q`. -/
theorem exists_factorization_objectPropertyInclusion_iff
    {𝒟 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)} {Q : ObjectProperty 𝒟.obj}
    (hiso : Q.IsClosedUnderIsomorphisms) {𝒞 : BasedCategory (BigFppfOver B S hS)}
    (f : 𝒞 ⥤ᵇ 𝒟) :
    (∃ g : 𝒞 ⥤ᵇ objectPropertySubcategory B S hS 𝒟 Q,
        Nonempty (g.comp (objectPropertyInclusion B S hS 𝒟 Q) ≅ f)) ↔
      ∀ Y : 𝒞.obj, Q (f.obj Y) := by
  constructor
  · rintro ⟨g, ⟨α⟩⟩ Y
    exact hiso.of_iso (((BasedNatTrans.forgetful _ _).mapIso α).app Y) (g.obj Y).property
  · intro h
    exact ⟨⟨Q.lift f.toFunctor h, f.w⟩, ⟨BasedNatIso.id _⟩⟩

end Stack

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  {P : ObjectProperty (CurveFamily B hZ)}

/-- **Universal property (1) of Stacks 0E0E, up to 2-isomorphism.** Let `X → S` be a family of
curves and let `z : (Sch/S) → Curves` be a classifying morphism for it, that is a scheme-valued
point of `Curves` with values in `S` together with an isomorphism `z(S) ≅ X`. Under condition
(o), `z` factors through `Curves^P`, over the site and up to a 2-isomorphism, if and only if
`X → S` has `P`.

A factorization is the condition that every value of `z` has `P`; the value at `S` is isomorphic
to `X`, and every other value maps to it. -/
theorem factorsThrough_curvesSubstack_iff (hP : IsOpenCurvesLocus B hZ P)
    (S : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B S.left.1 S.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map S.hom)
    (X : CurveFamily B hZ) (ξ : z.obj (Over.mk (𝟙 S.left)) ≅ X) :
    (∃ g : BasedCategory.ofFunctor (Over.map S.hom) ⥤ᵇ
          Stack.objectPropertySubcategory B integerBase hZ (curvesFiberedCategory B hZ).val P,
        Nonempty (g.comp (Stack.objectPropertyInclusion B integerBase hZ
          (curvesFiberedCategory B hZ).val P) ≅ { toFunctor := z, w := hz })) ↔ P X := by
  refine (Stack.exists_factorization_objectPropertyInclusion_iff
    (𝒟 := (curvesFiberedCategory B hZ).val) (Q := P) hP.isClosedUnderIsomorphisms
    (𝒞 := BasedCategory.ofFunctor (Over.map S.hom)) { toFunctor := z, w := hz }).trans ?_
  refine ⟨fun hall => hP.prop_of_hom ξ.inv (hall (Over.mk (𝟙 S.left))), fun hX T => ?_⟩
  exact hP.prop_of_hom (z.map (Over.mkIdTerminal.from T)) (hP.prop_of_hom ξ.hom hX)

/-- **Universal property (2) of Stacks 0E0E, up to 2-isomorphism.** Let `X → Spec(k)` be a proper
morphism of schemes whose target is the spectrum of a field and whose source has dimension at
most one, and let `z : (Sch/Spec(k)) → Curves` classify its family of curves. Under condition
(o), `z` factors through `Curves^P` if and only if the family of curves `X → Spec(k)` has `P`. -/
theorem factorsThrough_curvesSubstack_over_field_iff (hP : IsOpenCurvesLocus B hZ P)
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ (curvesFiberedCategory B hZ).val.obj)
    (hz : z ⋙ (curvesFiberedCategory B hZ).val.p = Over.map W.hom)
    (ξ : z.obj (Over.mk (𝟙 W.left)) ≅ curveFamilyOfSchemeMorphism B hZ g
      (flat_of_eq_spec_field _ k hW) hproper
      (locallyOfFinitePresentation_of_eq_spec_field _ k hW)
      (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
      ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
      ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) :
    (∃ q : BasedCategory.ofFunctor (Over.map W.hom) ⥤ᵇ
          Stack.objectPropertySubcategory B integerBase hZ (curvesFiberedCategory B hZ).val P,
        Nonempty (q.comp (Stack.objectPropertyInclusion B integerBase hZ
          (curvesFiberedCategory B hZ).val P) ≅ { toFunctor := z, w := hz })) ↔
      P (curveFamilyOfSchemeMorphism B hZ g
        (flat_of_eq_spec_field _ k hW) hproper
        (locallyOfFinitePresentation_of_eq_spec_field _ k hW)
        (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
        ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
        ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim) :=
  factorsThrough_curvesSubstack_iff hP W z hz _ ξ

end AlgebraicGeometry

end

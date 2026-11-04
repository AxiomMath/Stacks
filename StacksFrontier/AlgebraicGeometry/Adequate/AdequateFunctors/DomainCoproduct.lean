module

public import StacksFrontier.Algebra.Module.Adequate.Colimit
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainRestriction

/-!
# Coproducts of linearly adequate functors on a restricted domain of algebras

[Stacks, Tag 06UX] says that an adequate module-valued functor is a pointwise quotient of a
coproduct of linearly adequate ones. The statement
`AdequateFunctor.exists_coproduct_linearlyAdequate_surjective` fixes the domain to be all
commutative `A`-algebras. This file carries it to any domain `ι : C ⥤ CommAlgCat A`.

Unlike the closure properties of adequacy, this transport is immediate: 06UX has adequacy as a
hypothesis rather than as its conclusion, so `AdequateFunctor.IsAdequate.exists_extension` may
be applied to it without circularity. That writes the given functor as the restriction of an
adequate functor on all algebras, where 06UX applies; restricting the resulting coproduct back
needs only that reindexing a presheaf of modules preserves coproducts, which holds because
colimits of presheaves of modules are computed objectwise.

## Main results

* `AdequateFunctor.exists_coproduct_linearlyAdequate_surjective_on` — [Stacks, Tag 06UX] on any
  domain of algebras.

## Implementation notes

No `@[stacks]` attribute is placed here: the tagged statement of 06UX is
`AdequateFunctor.exists_coproduct_linearlyAdequate_surjective`, over all commutative algebras,
and this is that statement transported to a restricted domain.

## References

* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u u₁ v₁

namespace AdequateFunctor

/-- An adequate module-valued functor on any domain of algebras `ι : C ⥤ CommAlgCat A` is a
pointwise quotient of a coproduct of linearly adequate ones: [Stacks, Tag 06UX] on a restricted
domain of algebras. -/
public theorem exists_coproduct_linearlyAdequate_surjective_on
    {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
    (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w, v} ι) (hF : IsAdequate.{w, v} ι F) :
    ∃ (J : Type (max u v w)) (L : J → ModuleValuedFunctorOn.{max u v w, v} ι),
      (∀ j, IsLinearlyAdequate.{max u v w, v} ι (L j)) ∧
        ∃ f : (∐ L) ⟶ (presheafOfModulesUliftFunctor.{max u v, w}
            (algebraRingDiagramOn.{v} ι)).obj F,
          ∀ X, Function.Surjective (f.app X) := by
  classical
  obtain ⟨G, hG, ⟨eG⟩⟩ := IsAdequate.exists_extension.{w} ι F hF
  obtain ⟨J, L₀, hL₀, f₀, hf₀⟩ :=
    exists_coproduct_linearlyAdequate_surjective G hG
  let R := AdequateFunctor.restrictDomain.{max u v w, v} ι (𝟭 (CommAlgCat.{max u v} A))
  let uG := presheafOfModulesUliftIso.{max u v, max u v w} (algebraRingDiagram.{v} A) G
  let f₁ : (∐ L₀) ⟶ G := f₀ ≫ uG.hom
  have hf₁ : ∀ Y, Function.Surjective (f₁.app Y) := by
    intro Y y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (uG.hom.app Y)) y
    obtain ⟨t, ht⟩ := hf₀ Y z
    exact ⟨t, by simp [f₁, ht, hz]⟩
  let L : J → ModuleValuedFunctorOn.{max u v w, v} ι := fun j => R.obj (L₀ j)
  have : PreservesColimitsOfShape (Discrete J) R :=
    pushforward₀_preservesColimitsOfShape.{max u v w} ι.op (algebraRingDiagram.{v} A) (Discrete J)
  let eD : Discrete.functor L ≅ Discrete.functor L₀ ⋙ R :=
    Discrete.natIso fun j => Iso.refl _
  let compIso : (∐ L) ≅ R.obj (∐ L₀) :=
    HasColimit.isoOfNatIso eD ≪≫ (preservesColimitIso R (Discrete.functor L₀)).symm
  refine ⟨J, L, fun j => ?_, compIso.hom ≫ R.map f₁ ≫ eG.inv, fun X y => ?_⟩
  · exact IsLinearlyAdequate.restrictDomain.{max u v w} ι (𝟭 _) (L₀ j) (hL₀ j)
  · obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (eG.inv.app X)) y
    obtain ⟨t, ht⟩ := hf₁ (ι.op.op.obj X) z
    obtain ⟨s, hs⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (compIso.hom.app X)) t
    refine ⟨s, ?_⟩
    have h : (R.map f₁).app X (compIso.hom.app X s) = z := by
      show f₁.app (ι.op.op.obj X) (compIso.hom.app X s) = z
      rw [hs]
      exact ht
    show eG.inv.app X ((R.map f₁).app X (compIso.hom.app X s)) = y
    rw [h, hz]

end AdequateFunctor

end

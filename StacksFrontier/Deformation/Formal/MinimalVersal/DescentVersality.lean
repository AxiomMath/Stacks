module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.MinimalVersal.BaseRetraction
public import StacksFrontier.Deformation.FormalObject.AssociatedMorphismMap
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# A smallest descent of a versal formal object is versal (Stacks 06T3)

Let `ξ` be a versal formal object of a category `F` cofibered in groupoids over `𝒞_Λ` and let
`ξ' → ξ` be a smallest descent of it, lying over `R' ⊂ R = ξ.base` as constructed in Stacks
06T2. Then `ξ'` is again a versal formal object.

## Main results

* `Deformation.essSurj_restrictedRepresentableMap_of_retraction`: a map of complete local
  algebras with a left inverse induces an essentially surjective morphism of restricted
  representable categories.
* `Deformation.isVersal_smallestDescent`: a smallest descent of a versal formal object is
  versal.

## References

* [Stacks Project, Tag 06T3](https://stacks.math.columbia.edu/tag/06T3)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w uF vF u₁ v₁ u₂ v₂

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism of complete local algebras with a left inverse induces an essentially
surjective morphism of restricted representable categories. -/
public theorem essSurj_restrictedRepresentableMap_of_retraction
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) (r : S ⟶ R) (hfr : f ≫ r = 𝟙 R) :
    (restrictedRepresentableMap f).toFunctor.EssSurj := by
  refine Functor.essSurj_of_surj fun z => ⟨⟨(restrictedCoyonedaMap r).app z.obj z.val⟩,
    Functor.Elements.ext (F := restrictedCoyoneda R) _ z rfl
      (CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun x => ?_))⟩
  change z.val.hom ((r.hom.comp f.hom) x) = z.val.hom x
  rw [show r.hom.comp f.hom = AlgHom.id Λ R by
    simpa using congrArg (fun g : R ⟶ R ↦ g.hom) hfr]
  rfl

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A smallest descent of a versal formal object of a category cofibered in groupoids is again a
versal formal object. -/
@[stacks 06T3 "descended object versal"]
public theorem isVersal_smallestDescent
    (hp : IsCofiberedInGroupoids p) {ξ : FormalObject p} (hξ : IsVersal hp ξ)
    (d : SmallestDescent ξ) : IsVersal hp d.object := by
  intro pushforwards
  let φ := restrictedRepresentableMap d.inclusion.base
  obtain ⟨r, hr⟩ := exists_retraction_of_smallestDescent hp ξ hξ d
  have : φ.toFunctor.EssSurj :=
    essSurj_restrictedRepresentableMap_of_retraction d.inclusion.base r hr
  obtain ⟨τ, _⟩ := associatedMorphism_map hp d.inclusion pushforwards
  exact isSmooth_of_essSurj_comp
    φ (associatedMorphism hp d.object pushforwards).toBasedFunctor
    (isSmooth_of_iso τ (hξ pushforwards))

end

end Deformation

end

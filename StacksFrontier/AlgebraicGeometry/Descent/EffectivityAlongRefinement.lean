module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackFpqcRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum

/-!
# Effectivity of a descent datum from effectivity of its pullback to a refinement

Let `𝒰 = {U i ⟶ S}` be a family of morphisms of schemes with fixed target and let
`𝒱 = {V j ⟶ S}` refine it, that is, let `α` be a morphism of families over the identity of `S`
going from `𝒱` to `𝒰`. Pulling descent data back along `α` is a functor from the descent data
relative to `𝒰` to the descent data relative to `𝒱`. When that functor is fully faithful and
carries the canonical descent datum of a scheme over `S` to the canonical descent datum of the
same scheme, it reflects effectivity: a descent datum relative to `𝒰` whose pullback to `𝒱` is
effective is itself effective.

## Main results

* `CategoryTheory.Functor.essImage_of_essImage_comp_obj`: a fully faithful functor reflects
  essential images.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_pullback`: effectivity of a descent datum
  follows from effectivity of its pullback along a refinement, given full faithfulness of the
  pullback functor and its compatibility with the canonical descent data.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_pullback_of_fpqcRefinement`: the same with
  full faithfulness replaced by the fibrewise fpqc hypothesis which implies it.

## References

* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02VZ](https://stacks.math.columbia.edu/tag/02VZ)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
-/

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- A fully faithful functor reflects essential images: if `G` is fully faithful and `G.obj Y`
lies in the essential image of `F ⋙ G`, then `Y` lies in the essential image of `F`. -/
theorem essImage_of_essImage_comp_obj (F : C ⥤ D) (G : D ⥤ E) [G.Full] [G.Faithful] {Y : D}
    (h : (F ⋙ G).essImage (G.obj Y)) : F.essImage Y := by
  obtain ⟨A, ⟨e⟩⟩ := h
  exact ⟨A, ⟨G.preimageIso e⟩⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry

open CategoryTheory

variable {S : Scheme.{u}} {U V : PreZeroHypercover.{u} S}

/-- A refinement of the family `V` by the family `U`, read as a morphism of families of
morphisms of schemes with fixed target over the identity of the common target. -/
abbrev MorphismOfSchemeFamilies.ofRefinement (α : U.HomOver V (𝟙 S)) :
    MorphismOfSchemeFamilies.{u} where
  sourceBase := S
  targetBase := S
  sourceFamily := U
  targetFamily := V
  baseHom := 𝟙 S
  familyHom := α

namespace DescentData

/-- **Effectivity descends along a refinement.** Let the family `U` refine the family `V` by
`α`, suppose that pulling descent data back along `α` is fully faithful, and suppose that it
carries the canonical descent datum relative to `V` of a scheme over the base to the canonical
descent datum of that scheme relative to `U`. Then a descent datum relative to `V` whose
pullback along `α` is effective is itself effective. -/
theorem isFamilyEffective_of_pullback (α : U.HomOver V (𝟙 S))
    (hff : (MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRefinement α)).functor.FullyFaithful)
    (hcan : (canonicalFamilyDescentFunctor V.f).functor ⋙
        (MorphismOfSchemeFamilies.pullbackFunctor
          (MorphismOfSchemeFamilies.ofRefinement α)).functor ≅
      (canonicalFamilyDescentFunctor U.f).functor)
    {D : DescentData V.f}
    (h : ((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRefinement α)).functor.obj D).IsFamilyEffective) :
    D.IsFamilyEffective := by
  have := hff.full
  have := hff.faithful
  exact Functor.essImage_of_essImage_comp_obj _ _ (Functor.essImage.ofNatIso hcan.symm h)

/-- **Effectivity descends along an fpqc refinement.** Let the family `U` refine the family `V`
by `α` so that the members of `U` lying above each member of `V` form an fpqc covering of it, and
suppose that pulling descent data back along `α` carries the canonical descent datum relative to
`V` of a scheme over the base to the canonical descent datum of that scheme relative to `U`. Then
a descent datum relative to `V` whose pullback along `α` is effective is itself effective. -/
theorem isFamilyEffective_of_pullback_of_fpqcRefinement (α : U.HomOver V (𝟙 S))
    (hfpqc : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.fpqcPrecoverage (V.X j))
    (hcan : (canonicalFamilyDescentFunctor V.f).functor ⋙
        (MorphismOfSchemeFamilies.pullbackFunctor
          (MorphismOfSchemeFamilies.ofRefinement α)).functor ≅
      (canonicalFamilyDescentFunctor U.f).functor)
    {D : DescentData V.f}
    (h : ((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRefinement α)).functor.obj D).IsFamilyEffective) :
    D.IsFamilyEffective :=
  have ⟨hff⟩ := pullbackFunctor_fullyFaithful_of_fpqcRefinement U V α hfpqc
  isFamilyEffective_of_pullback α hff hcan h

end DescentData

end AlgebraicGeometry

end

end

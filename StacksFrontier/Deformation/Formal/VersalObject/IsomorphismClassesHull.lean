module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClasses
public import StacksFrontier.Deformation.Schlessinger.MiniversalExistence
public import StacksFrontier.Deformation.Schlessinger.MiniversalSeparable

/-!
# A hull for the functor of isomorphism classes (Stacks 06IZ)

Let `𝓕` be a predeformation category over `𝒞_Λ` satisfying Schlessinger's conditions (S1) and
(S2), with finite-dimensional tangent space, and let `k` be separable over the image field of
`Λ`. Then `𝓕` has a formal object `ξ` which is versal with bijective differential, and the
image of `ξ` in the associated functor of isomorphism classes is again versal with bijective
differential — that is, it is a hull of that functor.

## Main definitions

* `Deformation.IsHull`: a hull is a versal formal object whose differential is an isomorphism.

## Main results

* `Deformation.exists_hull_isomorphismClasses`: the functor of isomorphism classes of a
  predeformation category satisfying Schlessinger's conditions has a hull, given by the image
  of a minimal versal formal object.

## References

* [Stacks Project, Tag 06IZ](https://stacks.math.columbia.edu/tag/06IZ)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w uF vF

/-- A *hull* of a category cofibered in groupoids over `𝒞_Λ` is a versal formal object whose
differential `dξ : T\underline{R}|_{𝒞_Λ} → T𝓕` is an isomorphism. -/
@[stacks 06IY "hull"]
public abbrev IsHull {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) : Prop :=
  IsVersal hp ξ ∧ HasBijectiveDifferential hp ξ

/-- A predeformation category satisfying Schlessinger's conditions (S1) and (S2), with
finite-dimensional tangent space and separable residue field extension, has a versal formal
object with bijective differential whose image in the associated functor of isomorphism classes
is again versal with bijective differential, hence a hull of that functor. -/
@[stacks 06IZ "existence of a hull", sga "7 VI 1.20" "existence"]
public theorem exists_hull_isomorphismClasses
    (Λ : Type u) (k : Type w) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] [Algebra.IsSeparable (residueImageField Λ k) k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (hS1 : SchlessingerConditionS1 𝓕.p)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    (hfin :
      letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨hpre⟩
      letI : Fact (SchlessingerConditionS2
          (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered))) :=
        ⟨schlessingerConditionS2_of_isIsomorphismClasses 𝓕 hpre.cofibered hS2 (Or.inl hpre)⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses 𝓕 hpre.cofibered))) :
    ∃ ξ : FormalObject 𝓕.p,
      IsHull hpre.cofibered ξ ∧
      IsHull
        (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
        (imageInIsomorphismClasses 𝓕 hpre ξ) := by
  obtain ⟨ξ, hminimal, hbijective⟩ :=
    exists_minimalVersal_hasBijectiveDifferential_of_separable 𝓕 hpre
      (exists_minimalVersal_hasBijectiveDifferentialOnDerivationOrbits Λ k 𝓕 hpre hS1 hS2 hfin)
  exact ⟨ξ, ⟨hminimal.1, hbijective⟩,
    isVersal_imageInIsomorphismClasses 𝓕 hpre ξ hminimal.1,
    hasBijectiveDifferential_imageInIsomorphismClasses 𝓕 hpre ξ hbijective⟩

end Deformation

end

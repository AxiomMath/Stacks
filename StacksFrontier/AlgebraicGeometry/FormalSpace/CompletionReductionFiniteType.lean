module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Reduced algebraic spaces over a completion are locally of finite type

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S` and
let `T ⊆ |X|` be a closed subset, with completion `X_{/T}`. Let `E ⟶ X_{/T}` be a morphism of fppf
sheaves which is representable, with represented base changes locally of finite type, and let
`E_r ⟶ E` be a representable closed immersion (for instance the inclusion of a reduction) from a
reduced algebraic space. Then `E_r ⟶ X` is representable with represented base changes locally of
finite type.

This is the argument showing that the reduction of the formal algebraic space `E_W` of Stacks 0GHD
is locally of finite type over the base: the morphism `E_r ⟶ X_{/T}` factors through the
reduction `Z` of `X_{/T}`, the reduced induced closed subspace of `X` supported on `T`
(Stacks 0GB9); the base change `P = Z ×_{X_{/T}} E` is locally of finite type over `Z`, and
`E_r ⟶ P` is a closed immersion, being the base change of `E_r ⟶ E` along the monomorphism
`P ⟶ E`; finally `Z ⟶ X` is a closed immersion.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_locallyOfFiniteType_comp_completionSheafToAmbient`: the
  statement above.
* `AlgebraicGeometry.Space.isLocallyOfFiniteTypeULift_of_relative`: a morphism into a
  universe-lifted representable presheaf which is representable with represented base changes
  locally of finite type is locally of finite type in the sense of Stacks 03XF.
* `AlgebraicGeometry.Space.completionSheafInclusion_comp_sheafifiedULiftIso_inv`: the two
  morphisms from the completion to the ambient sheaf agree.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 0GB9](https://stacks.math.columbia.edu/tag/0GB9)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism `X_{/T} ⟶ X` through the sheafification of the universe lift of `X` is the
morphism `AlgebraicGeometry.Space.completionSheafToAmbient` into the universe lift itself, once
the universe lift of `X` is an fppf sheaf. -/
theorem completionSheafInclusion_comp_sheafifiedULiftIso_inv
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (points B S hS X)) :
    (completionSheafInclusion B S hS X T).hom ≫ (sheafifiedULiftIso B S hS X hX).inv =
      completionSheafToAmbient B S hS X hX' T := by
  let J := BigFppfOver.topology B S hS
  refine J.sheafify_hom_ext _ _ hX' ?_
  rw [toSheafify_comp_completionSheafToAmbient]
  have hA : J.toSheafify (completionSubfunctor B S hS X T).toFunctor ≫
      (completionSheafInclusion B S hS X T).hom =
      (completionSubfunctor B S hS X T).ι ≫ J.toSheafify _ :=
    (J.toSheafify_naturality _).symm
  have hC : J.toSheafify (X ⋙ uliftFunctor.{u + 1}) ≫ (sheafifiedULiftIso B S hS X hX).inv =
      𝟙 _ :=
    (sheafifiedULiftIso B S hS X hX).hom_inv_id
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hA).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hC).trans (Category.comp_id _)

/-- **Stacks 03XF from representability, over a representable target.** A morphism `f` from a
presheaf with values in `Type (u + 1)` to a universe-lifted representable presheaf, which is
representable with every represented base change locally of finite type, is locally of finite
type on every commuting square of étale charts: the composite of the chart of the source with
`f` is again representable and locally of finite type, so the morphism of the site it
represents is locally of finite type, and the chart of the target is étale. -/
theorem isLocallyOfFiniteTypeULift_of_relative {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {Y : BigFppfOver B S hS} (f : F ⟶ uliftYoneda.{u + 1}.obj Y)
    (hf : (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} f) :
    IsLocallyOfFiniteTypeULift.{u + 1} B S hS f := by
  intro U V a b h ha _ hsq
  obtain ⟨β, rfl⟩ : ∃ β : V ⟶ Y, uliftYoneda.{u + 1}.map β = b :=
    ⟨uliftYoneda.{u + 1}.preimage b, by simp⟩
  let L := MorphismProperty.inverseImage
    (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let _ : L.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : (L.relative uliftYoneda.{u + 1}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition L
  have hle : MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤ L := fun _ _ k hk ↦ by
    have : Etale ((BigFppfOver.toScheme B S hS).map k) := hk
    exact (inferInstance : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k))
  have hcomp : L.relative uliftYoneda.{u + 1} (uliftYoneda.{u + 1}.map (h ≫ β)) := by
    rw [Functor.map_comp, hsq]
    exact MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_monotone (F := uliftYoneda.{u + 1}) hle _ ha) hf
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (h ≫ β)) :=
    (MorphismProperty.of_relative_map (P := L) hcomp : L (h ≫ β))
  rw [Functor.map_comp] at hlft
  exact locallyOfFiniteType_of_comp _ ((BigFppfOver.toScheme B S hS).map β)

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (T : Set (Space.points B S hS X)) (hT : IsClosed T)

include hT in
/-- **A reduced algebraic space over a completion is locally of finite type over the ambient
space.** Let `X` be an algebraic space over `S`, `T ⊆ |X|` closed, `ι : E ⟶ X_{/T}` representable
with represented base changes locally of finite type, and `r : E_r ⟶ E` a representable closed
immersion from a reduced algebraic space. Then `E_r ⟶ E ⟶ X_{/T} ⟶ X` is representable with
represented base changes locally of finite type.

The morphism `E_r ⟶ X_{/T}` factors through the reduction `Z` of `X_{/T}` (Stacks 0GB9); the
factorization `E_r ⟶ Z ×_{X_{/T}} E` is the base change of `r` along the monomorphism
`Z ×_{X_{/T}} E ⟶ E`, hence a closed immersion; `Z ×_{X_{/T}} E ⟶ Z` is a base change of `ι`, and
`Z ⟶ X` is a closed immersion. -/
theorem relative_locallyOfFiniteType_comp_completionSheafToAmbient {E Er : FppfSheaf B S hS}
    (ι : E ⟶ Space.completionSheaf B S hS X T)
    (hι : (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} ι.hom)
    (r : Er ⟶ E) (hEr : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Er.obj)
    (hEr' : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS Er.obj
      (fun T : Scheme.{u} ↦ IsReduced T))
    (hr : (MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} r.hom) :
    (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
      (r.hom ≫ ι.hom ≫ Space.completionSheafToAmbient B S hS X
        (isSheaf_comp_uliftFunctor B S hS hX) T) := by
  let L := MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let CI := MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : L.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : (L.relative uliftYoneda.{u + 1}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition L
  have hZ := isReduction_completionSheaf B S hS hX T hT
  obtain ⟨k₀, hk₀, -⟩ := hZ.universal Er hEr hEr' (r ≫ ι)
  let j := reducedClosedSubsetToCompletionSheaf B S hS hX T hT
  have : Mono j.hom := mono_hom_of_isReduction B S hS hZ
  have hk₀' : k₀.hom ≫ j.hom = r.hom ≫ ι.hom := congrArg (·.hom) hk₀
  let k := pullback.lift k₀.hom r.hom hk₀'
  have hfst : L.relative uliftYoneda.{u + 1} (pullback.fst j.hom ι.hom) :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{u + 1}) L).of_isPullback
      (IsPullback.of_hasPullback j.hom ι.hom).flip hι
  have hsq : IsPullback (𝟙 Er.obj) k r.hom (pullback.snd j.hom ι.hom) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, pullback.lift_snd]⟩
  have hkCI : CI.relative uliftYoneda.{u + 1} k :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{u + 1}) CI).of_isPullback
      hsq hr
  have hCL : CI ≤ L := fun _ _ m hm ↦ by
    have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map m) := hm
    exact (inferInstance : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m))
  have hk : L.relative uliftYoneda.{u + 1} k :=
    MorphismProperty.relative_monotone (F := uliftYoneda.{u + 1}) hCL _ hkCI
  have hj : L.relative uliftYoneda.{u + 1}
      (j.hom ≫
        Space.completionSheafToAmbient B S hS X (isSheaf_comp_uliftFunctor B S hS hX) T) := by
    rw [reducedClosedSubsetToCompletionSheaf_comp_completionSheafToAmbient]
    exact relative_uliftFunctor_of_presheaf L _
      (MorphismProperty.relative_monotone (F := yoneda) hCL _
        (Space.isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).2)
  have heq : r.hom ≫ ι.hom ≫ Space.completionSheafToAmbient B S hS X
      (isSheaf_comp_uliftFunctor B S hS hX) T = k ≫ pullback.fst j.hom ι.hom ≫ j.hom ≫
        Space.completionSheafToAmbient B S hS X (isSheaf_comp_uliftFunctor B S hS hX) T := by
    rw [pullback.lift_fst_assoc, ← Category.assoc k₀.hom, hk₀', Category.assoc]
  rw [heq]
  exact MorphismProperty.comp_mem _ _ _ hk (MorphismProperty.comp_mem _ _ _ hfst hj)

end FormalSpace

end AlgebraicGeometry

end

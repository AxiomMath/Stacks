module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Separatedness from a cover by two open subschemes

A morphism of schemes is separated as soon as its source is covered by two open subschemes
that are separated over the base and whose intersection is closed in the fibre product of
the two opens over the base.

## Main results

* `AlgebraicGeometry.isSeparated_of_sup_eq_top_of_isClosedImmersion_mapDesc`: the two-open
  criterion for separatedness.

## Implementation notes

The pullback of the two open inclusions is canonically their intersection, and
`CategoryTheory.Limits.pullback.mapDesc U.ι V.ι f` is its canonical morphism to the fibre
product of the two opens over the base.

Separatedness is local on the target, so it suffices to check that the diagonal becomes a
closed immersion over each of the four pieces of the induced cover of `X ×_S X` by products
of cover members. The two diagonal pieces are handled by the separatedness of the two opens
over the base, and the two off-diagonal pieces by the hypothesis and its mirror image under
the symmetry of the fibre product.

## References

* [Stacks Project, Tag 0F3U](https://stacks.math.columbia.edu/tag/0F3U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0F3U.** Two separated open subschemes covering the source, whose
overlap is closed in their fibre product over the base, give a separated morphism. -/
@[stacks 0F3U]
theorem isSeparated_of_sup_eq_top_of_isClosedImmersion_mapDesc
    {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤)
    [IsSeparated (U.ι ≫ f)] [IsSeparated (V.ι ≫ f)]
    (hUV : IsClosedImmersion (pullback.mapDesc U.ι V.ι f)) :
    IsSeparated f := by
  let W : Bool → X.Opens := fun b => if b then U else V
  have hW : TopologicalSpace.IsOpenCover W := by
    apply TopologicalSpace.IsOpenCover.mk
    simpa [W, iSup_bool_eq] using hcover
  let 𝒰 := Scheme.openCoverOfIsOpenCover X W hW
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f f
  have hself (A : X.Opens) [IsSeparated (A.ι ≫ f)] :
      IsClosedImmersion (pullback.mapDesc A.ι A.ι f) := by
    have hp : pullback.mapDesc A.ι A.ι f =
        pullback.fst A.ι A.ι ≫ pullback.diagonal (A.ι ≫ f) := by
      apply pullback.hom_ext
      · simp only [pullback.mapDesc, pullback.map]
        rw [pullback.lift_fst]
        simp
      · simp only [pullback.mapDesc, pullback.map]
        rw [pullback.lift_snd]
        simpa only [Category.comp_id, Category.assoc, pullback.diagonal_snd] using
          (fst_eq_snd_of_mono_eq A.ι).symm
    rw [hp]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) _
      (pullback.diagonal (A.ι ≫ f))).2 inferInstance
  have h𝒱f (i j : Bool) : 𝒱.f (i, j) =
      pullback.map (𝒰.f i ≫ f) (𝒰.f j ≫ f) f f (𝒰.f i) (𝒰.f j) (𝟙 S)
        (by simp) (by simp) := Scheme.Pullback.openCoverOfLeftRight_f 𝒰 𝒰 f f (i, j)
  have hVU : IsClosedImmersion (pullback.mapDesc V.ι U.ι f) := by
    refine (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
      (Arrow.isoMk (pullbackSymmetry V.ι U.ι) (pullbackSymmetry (V.ι ≫ f) (U.ι ≫ f)) ?_)).mpr hUV
    change (pullbackSymmetry V.ι U.ι).hom ≫ pullback.mapDesc U.ι V.ι f =
      pullback.mapDesc V.ι U.ι f ≫ (pullbackSymmetry (V.ι ≫ f) (U.ι ≫ f)).hom
    apply pullback.hom_ext <;>
      simp [pullback.mapDesc, pullback.map,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  have hpiece (i : 𝒱.I₀) :
      IsClosedImmersion (pullback.snd (pullback.diagonal f) (𝒱.f i)) := by
    obtain ⟨i, j⟩ := i
    have hmap : IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) f) := by
      cases i <;> cases j
      exacts [hself V, hVU, hUV, hself U]
    have hp : IsPullback (pullback.fst _ _ ≫ 𝒰.f i)
        (pullback.mapDesc (𝒰.f i) (𝒰.f j) f) (pullback.diagonal f)
        (pullback.map _ _ _ _ (𝒰.f i) (𝒰.f j) (𝟙 S) (by simp) (by simp)) :=
      pullback_map_diagonal_isPullback (𝒰.f i) (𝒰.f j) f
    have hq : IsClosedImmersion (pullback.snd (pullback.diagonal f)
        (pullback.map (𝒰.f i ≫ f) (𝒰.f j ≫ f) f f (𝒰.f i) (𝒰.f j) (𝟙 S)
          (by simp) (by simp))) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
          hp.isoPullback.hom, IsPullback.isoPullback_hom_snd]
      exact hmap
    rw [h𝒱f i j]
    exact hq
  constructor
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (fun i : 𝒱.I₀ => (𝒱.f i).opensRange) 𝒱.iSup_opensRange]
  exact fun i => (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
      (morphismRestrictOpensRange (pullback.diagonal f) (𝒱.f i))).mpr (hpiece i)

end AlgebraicGeometry

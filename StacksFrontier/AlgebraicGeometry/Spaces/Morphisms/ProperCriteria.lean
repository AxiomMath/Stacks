module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# Local criteria for properness of a morphism of algebraic spaces

Properness of a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is the conjunction
of three conditions (Stacks 03ZM): separatedness, finite type and universal closedness. Each of
the three can be tested locally on the target, and this file assembles those three criteria
into the one criterion for properness, Stacks 083R: `f` is proper exactly when its base change
along every morphism to `Y` from a scheme over `S` is proper, exactly when the same holds for
the affine schemes, exactly when it holds for one surjective étale scheme chart of `Y`, and
exactly when it holds over the members of a Zariski covering of `Y`.

## Main results

* `AlgebraicGeometry.Space.isProper_tfae`: **Stacks 083R**, the five equivalent conditions.
* `AlgebraicGeometry.Space.isProper_pullback_fst` is the implication (1) ⇒ (2), which is
  **Stacks 04WP** read at the chosen fibre product of presheaves.
* `AlgebraicGeometry.Space.isSeparated_pullback_fst_of_snd` and
  `AlgebraicGeometry.Space.isSeparated_pullback_snd_of_fst` exchange the two projections of a
  fibre product of presheaves, for separatedness.

## Implementation notes

The proof is conjunct by conjunct, from the local criteria for the three conjuncts of
properness:
`AlgebraicGeometry.Space.isSeparated_iff_affine`,
`AlgebraicGeometry.Space.isSeparated_of_etaleChart` and
`AlgebraicGeometry.Space.isSeparated_of_zariskiCover` of Stacks 03KM,
`AlgebraicGeometry.Space.isLocallyOfFiniteType_tfae` of Stacks 040Y,
`AlgebraicGeometry.Space.isQuasiCompact_tfae` of Stacks 03KG and
`AlgebraicGeometry.Space.universallyClosed_tfae` of Stacks 03IT.

Two differences of shape are absorbed. Separatedness is stated in Stacks 03KM on the
*second* projection `X ×_Y Z ⟶ Z` of a fibre product, where the other three conjuncts are
stated on the first projection `Z ×_Y X ⟶ Z`; the two are exchanged by composing with
`CategoryTheory.Limits.pullbackSymmetry`, which is separated because it is an isomorphism.
And the Zariski criterion of Stacks 040Y quantifies over coverings of the inverse images in
`X` of the members of a covering of `Y`, rather than over the base changes of `f`; the inverse
image is the fibre product by Stacks 083Q, so the base change over a member is locally of
finite type exactly when the canonical morphism out of the inverse image is, and the trivial
covering of that inverse image by itself finishes the comparison.

## References

* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Exchanging the two projections of a fibre product -/

/-- Separatedness of the first projection `Z ×_Y X ⟶ Z` of a fibre product of presheaves on
the big fppf site of `S`, from separatedness of the second projection `X ×_Y Z ⟶ Z` of the
symmetric fibre product. -/
theorem isSeparated_pullback_fst_of_snd (f : X ⟶ Y) (g : Z ⟶ Y)
    (h : IsSeparated B S hS (pullback.snd f g)) :
    IsSeparated B S hS (pullback.fst g f) := by
  have h' := isSeparated_comp B S hS (pullbackSymmetry g f).hom (pullback.snd f g)
    (isSeparated_of_isIso B S hS _) h
  rwa [pullbackSymmetry_hom_comp_snd] at h'

/-- Separatedness of the second projection `X ×_Y Z ⟶ Z` of a fibre product of presheaves on
the big fppf site of `S`, from separatedness of the first projection `Z ×_Y X ⟶ Z` of the
symmetric fibre product. -/
theorem isSeparated_pullback_snd_of_fst (f : X ⟶ Y) (g : Z ⟶ Y)
    (h : IsSeparated B S hS (pullback.fst g f)) :
    IsSeparated B S hS (pullback.snd f g) := by
  have h' := isSeparated_comp B S hS (pullbackSymmetry f g).hom (pullback.fst g f)
    (isSeparated_of_isIso B S hS _) h
  rwa [pullbackSymmetry_hom_comp_fst] at h'

/-! ### The base change of a proper morphism -/

/-- **Stacks 083R, (1) implies (2).** The base change of a proper morphism of algebraic spaces
over `S` along an arbitrary morphism from an algebraic space over `S` is proper.

This is **Stacks 04WP**, which is stated in the category of algebraic spaces over `S`, read at
the chosen fibre product of presheaves. -/
theorem isProper_pullback_fst (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y) (hf : IsProper B S hS f) :
    IsProper B S hS (pullback.fst g f) :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hf

/-! ### Comparison of shapes for the other three conjuncts -/

/-- A quasi-compact base change of `f : X ⟶ Y` along a morphism from a presheaf represented by
an object of the site with affine underlying scheme has quasi-compact source: the represented
presheaf is a quasi-compact algebraic space, so it is an admissible test object for
quasi-compactness in the sense of Stacks 03HE. -/
private theorem isQuasiCompactSpace_pullback_of_isQuasiCompact (f : X ⟶ Y)
    (W : BigFppfOver B S hS) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (g : yoneda.obj W ⟶ Y) (h : IsQuasiCompact B S hS (pullback.fst g f)) :
    IsQuasiCompactSpace B S hS (pullback g f) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hW
  exact isQuasiCompactSpace_of_iso B S hS
    (asIso (pullback.snd (𝟙 (yoneda.obj W)) (pullback.fst g f)))
    (h (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
      ((isQuasiCompactSpace_iff_compactSpace_points B S hS _
        (isAlgebraicSpace_yoneda B S hS W)).mpr (compactSpace_points_yoneda B S hS W)) (𝟙 _))

/-- **Stacks 083R, the finite-type half of (5) implies (1).** If the base change of
`f : X ⟶ Y` over each member of a Zariski covering of `Y` is locally of finite type, then `f`
is locally of finite type.

This is the Zariski criterion of Stacks 040Y, whose inner covering of the inverse image of a
member is taken to be the trivial covering by the inverse image itself. -/
private theorem isLocallyOfFiniteType_of_isZariskiCover (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {I : Type u} (U : I → Subfunctor Y)
    (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, IsLocallyOfFiniteType B S hS (pullback.fst (U i).ι f)) :
    IsLocallyOfFiniteType B S hS f := by
  refine ((isLocallyOfFiniteType_tfae B S hS hX hY f).out 9 1).mp ?_
  refine ⟨I, U, hU, fun i ↦ ?_⟩
  have hsq := Subfunctor.isPullback_preimage f (U i)
  have hPB : IsAlgebraicSpace B S hS (pullback (U i).ι f) :=
    isAlgebraicSpace_pullback B S hS (U i).ι f (hU.1 i).1 hX hY
  have hP : IsAlgebraicSpace B S hS ((U i).preimage f).toFunctor :=
    hPB.of_iso hsq.isoPullback.symm
  have hfp : IsLocallyOfFiniteType B S hS ((U i).fromPreimage f) := by
    rw [← hsq.isoPullback_hom_fst]
    exact isLocallyOfFiniteType_comp B S hS hP hPB (hU.1 i).1 _ _
      (isLocallyOfFiniteType_of_isEtale B S hS hPB (isEtale_of_isIso B S hS _)) (h i)
  refine ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hP, fun _ ↦ ?_⟩
  exact isLocallyOfFiniteType_comp B S hS (isOpenSubspace_top hP).1 hP (hU.1 i).1 _ _
    (isLocallyOfFiniteType_of_isEtale B S hS hP (isEtale_of_isIso B S hS _)) hfp

/-! ### Stacks 083R -/

/-- **Stacks 083R.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are
equivalent: `f` is proper; the base change of `f` along every morphism to `Y` from a presheaf
represented by an object of the site is proper; the same for the objects with affine underlying
scheme; the base change of `f` along some surjective étale morphism to `Y` from a represented
presheaf is proper; and there is a Zariski covering of `Y` along each member of which the base
change of `f` is proper. -/
@[stacks 083R]
theorem isProper_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [IsProper B S hS f,
        ∀ (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ Y),
          IsProper B S hS (pullback.fst g f),
        ∀ (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
            IsProper B S hS (pullback.fst g f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            IsProper B S hS (pullback.fst g f),
        ∃ (I : Type u) (U : I → Subfunctor Y) (_ : IsZariskiCover B S hS I U),
          ∀ i, IsProper B S hS (pullback.fst (U i).ι f)] := by
  tfae_have 1 → 2 := fun hf W g ↦
    isProper_pullback_fst B S hS hX hY (isAlgebraicSpace_yoneda B S hS W) f g hf
  tfae_have 2 → 3 := fun hf W g _ ↦ hf W g
  tfae_have 3 → 1 := fun hf ↦
    ⟨(isSeparated_iff_affine B S hS hX f).2 fun W hW g ↦
        isSeparated_pullback_snd_of_fst B S hS f g (hf W g hW).1,
      ⟨isLocallyOfFiniteType_of_pullback_fst_of_isAffine B S hS hX hY f
          fun W g hW ↦ (hf W g hW).2.1.1,
        isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hX hY f
          fun W hW g ↦ isQuasiCompactSpace_pullback_of_isQuasiCompact B S hS f W hW g
            (hf W g hW).2.1.2⟩,
      ((universallyClosed_tfae B S hS hX hY f).out 3 1).mp fun W g hW ↦
        isClosed_of_universallyClosed B S hS (isAlgebraicSpace_yoneda B S hS W) _
          (hf W g hW).2.2⟩
  tfae_have 1 → 4 := fun hf ↦ by
    obtain ⟨V, g, hgsurj, hgetale⟩ := hY.exists_atlas
    exact ⟨V, g, (surjective_iff_surjective_pointsMap B S hS Y hY V g).mp hgsurj,
      isEtale_of_presheaf_etale B S hS hgetale,
      isProper_pullback_fst B S hS hX hY (isAlgebraicSpace_yoneda B S hS V) f g hf⟩
  tfae_have 4 → 1 := fun hf ↦ by
    obtain ⟨V, g, hgsurj, hgetale, hp⟩ := hf
    exact ⟨isSeparated_of_etaleChart B S hS hX
        ((surjective_iff_surjective_pointsMap B S hS Y hY V g).mpr hgsurj)
        (presheaf_etale_of_isEtale B S hS hgetale)
        (isSeparated_pullback_snd_of_fst B S hS f g hp.1),
      ⟨((isLocallyOfFiniteType_tfae B S hS hX hY f).out 5 1).mp
          (by exact ⟨V, g, hgsurj, hgetale, hp.2.1.1⟩),
        ((isQuasiCompact_tfae B S hS hX hY f).out 4 1).mp
          (by exact ⟨V, g, hgsurj, hgetale, hp.2.1.2⟩)⟩,
      ((universallyClosed_tfae B S hS hX hY f).out 4 1).mp
        (by exact ⟨V, g, hgsurj, hgetale, hp.2.2⟩)⟩
  tfae_have 1 → 5 := fun hf ↦
    ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
      fun _ ↦ isProper_pullback_fst B S hS hX hY (isOpenSubspace_top hY).1 f _ hf⟩
  tfae_have 5 → 1 := fun hf ↦ by
    obtain ⟨I, U, hU, hp⟩ := hf
    exact ⟨isSeparated_of_zariskiCover B S hS hX hU
        fun i ↦ isSeparated_pullback_snd_of_fst B S hS f (U i).ι (hp i).1,
      ⟨isLocallyOfFiniteType_of_isZariskiCover B S hS hX hY f U hU
          fun i ↦ (hp i).2.1.1,
        ((isQuasiCompact_tfae B S hS hX hY f).out 6 1).mp
          (by exact ⟨I, U, hU, fun i ↦ (hp i).2.1.2⟩)⟩,
      ((universallyClosed_tfae B S hS hX hY f).out 5 1).mp
        (by exact ⟨I, U, hU, fun i ↦ (hp i).2.2⟩)⟩
  tfae_finish

end AlgebraicGeometry.Space

end

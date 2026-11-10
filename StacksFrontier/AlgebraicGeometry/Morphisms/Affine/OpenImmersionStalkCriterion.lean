module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineRelativeSpec
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-compact open immersion is affine when the maximal ideals blow up outside its image

Let `f : Y ⟶ X` be a quasi-compact open immersion of schemes.  The canonical morphism
`can : Y ⟶ Spec_X(f_*𝒪_Y)` of [Stacks, Tag 01LY] is then an open immersion
(`AlgebraicGeometry.isOpenImmersion_canonicalMorphism`, a quasi-compact open immersion being
quasi-affine), and its image consists of the points of the relative spectrum lying over the image
of `f`.  So `can` is an isomorphism as soon as every point of the relative spectrum lies over the
image of `f`, and then `f = can ≫ π` is affine because the structure morphism `π` of a relative
spectrum is.

A point `y` of the relative spectrum lying over `x ∈ X` forces
`𝔪_x · (f_*𝒪_Y)_x ≠ (f_*𝒪_Y)_x`: the stalk map of `π` at `y` factors the comorphism of `f` at
`x`, and the maximal ideal of a local ring has proper extension along a local homomorphism.  So
the hypothesis

`𝔪_x · (f_*𝒪_Y)_x = (f_*𝒪_Y)_x` for every `x` outside the image of `f`

makes `can` surjective, and that is the criterion proved here.

This is the second half of the proof of [Stacks, Tag 0EBR] carried out without higher direct
images: the source argues by the cohomological criterion [Stacks, Tag 0EBE] and an induction on
the dimension of the local ring, which needs the stalk of a higher direct image
([Stacks, Tag 02KH] outside the affine case); the relative-spectrum argument below needs neither.

## Main results

* `AlgebraicGeometry.Scheme.isQuasiAffine_preimage_of_isAffineOpen`: the inverse image of an
  affine open under a quasi-compact open immersion is quasi-affine.
* `AlgebraicGeometry.isQuasiAffineHom_of_isOpenImmersion`: a quasi-compact open immersion is
  quasi-affine.
* `AlgebraicGeometry.mem_range_canonicalMorphism_iff`: a point of `Spec_X(f_*𝒪_Y)` is in the
  image of the canonical morphism exactly when its image in `X` is in the image of `f`.
* `AlgebraicGeometry.map_maximalIdeal_pushforwardStalkMap_ne_top`: at a point of `X` in the
  image of the relative spectrum, the maximal ideal does not generate the unit ideal in
  `(f_*𝒪_Y)_x`.
* `AlgebraicGeometry.isAffineHom_of_forall_map_maximalIdeal_eq_top`: **the criterion.**

## References

* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 0EBR](https://stacks.math.columbia.edu/tag/0EBR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u

namespace AlgebraicGeometry

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- **The inverse image of an affine open under a quasi-compact open immersion is
quasi-affine.**  The restriction of `f` over the affine open is a quasi-compact immersion into a
compact space, so its source is compact, and a compact scheme with an immersion into an affine
scheme is quasi-affine. -/
@[ega "II 5.1.2" "b) ⇒ a)"]
theorem Scheme.isQuasiAffine_preimage_of_isAffineOpen [IsOpenImmersion f] [QuasiCompact f]
    (V : X.Opens) (hV : IsAffineOpen V) : Scheme.IsQuasiAffine (f ⁻¹ᵁ V).toScheme := by
  let : IsAffine V.toScheme := hV
  let : CompactSpace V.toScheme := inferInstance
  let : QuasiCompact (morphismRestrict f V) := inferInstance
  let : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (morphismRestrict f V)
  let : IsImmersion (morphismRestrict f V) := inferInstance
  exact Scheme.IsQuasiAffine.of_isImmersion (morphismRestrict f V)

/-- **A quasi-compact open immersion is quasi-affine**, by
`AlgebraicGeometry.Scheme.isQuasiAffine_preimage_of_isAffineOpen`. -/
instance isQuasiAffineHom_of_isOpenImmersion [IsOpenImmersion f] [QuasiCompact f] :
    IsQuasiAffineHom f :=
  ⟨fun V hV => Scheme.isQuasiAffine_preimage_of_isAffineOpen f V hV⟩

section

variable [IsOpenImmersion f] [QuasiCompact f] [QuasiSeparated f]

/-- **A point of `Spec_X(f_*𝒪_Y)` is in the image of the canonical morphism exactly when its
image in `X` is in the image of `f`.**  One direction is `canonicalMorphism_comp_toBase`.  For
the other, choose an affine open `V` of `X` containing the image of the point and inside the
range of `f`; then `f⁻¹V` is affine, so `(f⁻¹V).toSpecΓ` is an isomorphism, and the chart of `V`
covers the part of the relative spectrum over `V` (`Stacks.RelativeSpec.chart_opensRange`). -/
theorem mem_range_canonicalMorphism_iff (y : (pushforwardSpectrum f).scheme) :
    y ∈ Set.range (canonicalMorphism f) ↔
      (pushforwardSpectrum f).toBase y ∈ Set.range f.base := by
  refine ⟨?_, fun hy => ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, (congrArg (fun k : Y ⟶ X => k.base z) (canonicalMorphism_comp_toBase f)).symm⟩
  · obtain ⟨V, hV, hyV, hVf⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := f.opensRange) hy
    have hP : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage_of_isOpenImmersion f hVf
    have : IsAffine (f ⁻¹ᵁ V).toScheme := hP
    have : IsIso (f ⁻¹ᵁ V).toSpecΓ := by
      change IsIso ((f ⁻¹ᵁ V).toScheme.toSpecΓ ≫ Spec.map (f ⁻¹ᵁ V).topIso.inv)
      infer_instance
    have hy' : y ∈ Set.range ((pushforwardSpectrum f).chart ⟨V, hV⟩) := by
      have hr := chart_opensRange (pushforwardSituation f) ⟨V, hV⟩
      exact congrArg (fun W : (pushforwardSpectrum f).scheme.Opens => (y ∈ W)) hr ▸ hyV
    obtain ⟨z, hz⟩ := hy'
    obtain ⟨t, ht⟩ := (f ⁻¹ᵁ V).toSpecΓ.surjective z
    refine ⟨(f ⁻¹ᵁ V).ι.base t, ?_⟩
    show (canonicalMorphism f).base ((f ⁻¹ᵁ V).ι.base t) = y
    rw [← Scheme.Hom.comp_apply, ι_toRelativeSpec f ⟨V, hV⟩]
    change (pushforwardSpectrum f).chart ⟨V, hV⟩ ((f ⁻¹ᵁ V).toSpecΓ.base t) = y
    rw [ht, hz]

omit [IsOpenImmersion f] in
/-- **At a point of `X` lying under the relative spectrum the maximal ideal does not generate
the unit ideal in `(f_*𝒪_Y)_x`.**  The stalk map of the structure morphism `π` at the point
factors the stalk of the comorphism of `f`, and a local homomorphism never carries the maximal
ideal onto the unit ideal. -/
theorem map_maximalIdeal_pushforwardStalkMap_ne_top (y : (pushforwardSpectrum f).scheme) :
    Ideal.map ((TopCat.Presheaf.stalkFunctor CommRingCat.{u}
        ((pushforwardSpectrum f).toBase.base y)).map
          (pushforwardSituation f).algebra.hom.hom).hom
      (IsLocalRing.maximalIdeal
        (X.presheaf.stalk ((pushforwardSpectrum f).toBase.base y))) ≠ ⊤ := by
  let a := universalAlgebraMap (pushforwardSituation f)
  let SF := TopCat.Presheaf.stalkFunctor CommRingCat.{u} ((pushforwardSpectrum f).toBase.base y)
  let b := SF.map a.right ≫
    TopCat.Presheaf.stalkPushforward CommRingCat.{u} (pushforwardSpectrum f).toBase.base
      (pushforwardSpectrum f).scheme.presheaf y
  have ha : (pushforwardSituation f).algebra.hom.hom ≫ a.right =
      (pushforwardSpectrum f).toBase.c := Under.w a
  have h1 : SF.map (pushforwardSituation f).algebra.hom.hom ≫ SF.map a.right =
      SF.map (pushforwardSpectrum f).toBase.c := (SF.map_comp _ _).symm.trans (congrArg _ ha)
  have hcomp : SF.map (pushforwardSituation f).algebra.hom.hom ≫ b =
      (pushforwardSpectrum f).toBase.stalkMap y :=
    (Category.assoc (SF.map (pushforwardSituation f).algebra.hom.hom) (SF.map a.right)
      (TopCat.Presheaf.stalkPushforward CommRingCat.{u} (pushforwardSpectrum f).toBase.base
        (pushforwardSpectrum f).scheme.presheaf y)).symm.trans
      ((congrArg (fun k => k ≫ TopCat.Presheaf.stalkPushforward CommRingCat.{u}
        (pushforwardSpectrum f).toBase.base
        (pushforwardSpectrum f).scheme.presheaf y) h1).trans rfl)
  intro htop
  have h2 : Ideal.map b.hom (Ideal.map
        (SF.map (pushforwardSituation f).algebra.hom.hom).hom
        (IsLocalRing.maximalIdeal
          (X.presheaf.stalk ((pushforwardSpectrum f).toBase.base y)))) =
      Ideal.map (b.hom.comp (SF.map (pushforwardSituation f).algebra.hom.hom).hom)
        (IsLocalRing.maximalIdeal
          (X.presheaf.stalk ((pushforwardSpectrum f).toBase.base y))) :=
    Ideal.map_map _ _
  have h4 : b.hom.comp (SF.map (pushforwardSituation f).algebra.hom.hom).hom =
      ((pushforwardSpectrum f).toBase.stalkMap y).hom :=
    (CommRingCat.hom_comp (SF.map (pushforwardSituation f).algebra.hom.hom) b).symm.trans
      (congrArg CommRingCat.Hom.hom hcomp)
  have key : Ideal.map ((pushforwardSpectrum f).toBase.stalkMap y).hom
      (IsLocalRing.maximalIdeal
        (X.presheaf.stalk ((pushforwardSpectrum f).toBase.base y))) = ⊤ :=
    (congrArg (fun φ => Ideal.map φ (IsLocalRing.maximalIdeal
        (X.presheaf.stalk ((pushforwardSpectrum f).toBase.base y)))) h4).symm.trans
      (h2.symm.trans ((congrArg (Ideal.map b.hom) htop).trans (Ideal.map_top _)))
  exact (IsLocalRing.maximalIdeal.isMaximal
      ((pushforwardSpectrum f).scheme.presheaf.stalk y)).ne_top
    (top_unique (key ▸ IsLocalRing.map_maximalIdeal_le
      ((pushforwardSpectrum f).toBase.stalkMap y).hom))

omit [IsOpenImmersion f] in
/-- The structure morphism of the quasi-coherent algebra `f_*𝒪_Y` is the comorphism of `f`. -/
theorem pushforwardSituation_algebra_hom_hom :
    (pushforwardSituation f).algebra.hom.hom = f.c := rfl

/-- **A quasi-compact open immersion whose complement sees the maximal ideals blow up is
affine.**

If `𝔪_x` generates the unit ideal of `(f_*𝒪_Y)_x` at every point `x` outside the image of `f`,
then the canonical morphism `can : Y ⟶ Spec_X(f_*𝒪_Y)` is surjective by
`AlgebraicGeometry.map_maximalIdeal_pushforwardStalkMap_ne_top` together with
`AlgebraicGeometry.mem_range_canonicalMorphism_iff`; it is an open immersion because `f` is
quasi-affine, hence an isomorphism; and `f = can ≫ π` with `π` affine. -/
theorem isAffineHom_of_forall_map_maximalIdeal_eq_top
    (h : ∀ x : X, x ∉ Set.range f.base →
      Ideal.map (f.pushforwardStalkMap x).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) = ⊤) :
    IsAffineHom f := by
  have : Surjective (canonicalMorphism f) := ⟨fun y => by
    refine (mem_range_canonicalMorphism_iff f y).2 ?_
    by_contra hy
    refine map_maximalIdeal_pushforwardStalkMap_ne_top f y ?_
    rw [pushforwardSituation_algebra_hom_hom]
    exact h ((pushforwardSpectrum f).toBase.base y) hy⟩
  have : IsIso (canonicalMorphism f) :=
    (isIso_iff_isOpenImmersion_and_surjective (canonicalMorphism f)).2
      ⟨inferInstance, inferInstance⟩
  rw [← canonicalMorphism_comp_toBase f]
  exact inferInstanceAs (IsAffineHom (canonicalMorphism f ≫ (pushforwardSpectrum f).toBase))

end

end AlgebraicGeometry

end

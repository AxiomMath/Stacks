module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedConormalSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalFirstMapRetraction

/-!
# Stacks 06BJ: the conormal sequence of a formally unramified morphism with formally smooth source

Let `B` be a big fppf site over a scheme `S`, let `Y` be an algebraic space (the base, written `B`
in the source; the letter `B` is taken here by the site), and let `h : Z ⟶ X` be a formally
unramified morphism of algebraic spaces over `Y` such that `Z` is formally smooth over `Y`.
[Stacks Project, Tag 06BJ] asserts that the canonical exact sequence
```
  0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of [Stacks Project, Tag 060F] is short exact.

The situation is presented exactly as for Stacks 060F in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallyUnramifiedConormalSequence.lean`: by a universal
first order thickening `hZ` of a subfunctor `Z` of `Z'` over `h' : Z' ⟶ X` and a morphism
`p : X ⟶ Y`, the morphism `h` of the source being `ι ≫ h'` for the inclusion `ι : Z ⟶ Z'`.  For
a formally unramified `h` such a datum exists by Stacks 0606
(`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`), and the sequence is
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.conormalSequence`, which Stacks 060F
(`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_conormalSequence_exact`) shows
to be exact at the middle and on the right, unconditionally.

What Stacks 06BJ adds is **injectivity of the first arrow**.  The source's proof: formal
smoothness of `Z` over `Y` gives, étale locally on `Z'`, a left inverse `Z' ⟶ Z` over `Y` of
`ι`.  Here `AlgebraicGeometry.Space.exists_retraction_of_formallySmooth` is that step on an affine
étale chart, `AlgebraicGeometry.Space.exists_chartRetraction_of_formallySmooth` rewrites it as a
retraction of the chart onto the preimage of `Z`, and
`AlgebraicGeometry.Space.mono_conormalSequenceIdealPullbackMap_of_retractions` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalFirstMapRetraction.lean` turns those
retractions into injectivity of the first arrow of Stacks 05ZA for `Z ⊂ Z'`.  The first arrow of
Stacks 060F followed by the isomorphism of Stacks 060E is that arrow
(`AlgebraicGeometry.Space.thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap`), so
it is injective too.

## Main results

* `AlgebraicGeometry.Space.mono_conormalSequenceFirstMap_of_formallySmooth`: the first arrow
  `𝒞_{Z/Z'} ⟶ ι^*Ω_{Z'/Y}` of Stacks 05ZA at the universal first order thickening is a
  monomorphism when `Z` is formally smooth over `Y`.
* `IsUniversalFirstOrderThickening.conormalSequence_shortExact_of_formallySmooth`, in the
  namespace `AlgebraicGeometry.Space`: **Stacks 06BJ**, the sequence of Stacks 060F is short exact.

## References

* [Stacks Project, Tag 06BJ](https://stacks.math.columbia.edu/tag/06BJ)
* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-- **The step of the proof of Stacks 06BJ that uses formal smoothness.**  Let `Z ⊂ Z'` be the
universal first order thickening of `h = ι ≫ h'` over `X`, with `Z` formally smooth over `Y`.  Let
`Vs` be an affine object of the big fppf site over `Z'`, let `t : Us ⟶ Vs` be a square-zero closed
immersion of objects of the site and let `u : Us ⟶ Z` be étale, with `t` lying over `ι` through
the commuting square `hsq`.  Then `t` has a left inverse `g : Vs ⟶ Us` over `Y`.

`Us` is affine, being a closed subscheme of the affine `Vs`; `u` is étale, hence formally étale
(Stacks 04AL), so `Us ⟶ Y` is formally smooth (Stacks 049T); and formal smoothness of `Us ⟶ Y`
lifts the identity of `Us` across `t` over `Y`. -/
theorem exists_retraction_of_formallySmooth
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (hsm : FormallySmooth (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom)
    {Vs Us : BigFppfOver B S hS} (t : Us ⟶ Vs) (v : yoneda.obj Vs ⟶ Z'.obj)
    (u : yoneda.obj Us ⟶ Z.toFunctor) (hsq : yoneda.map t ≫ v = u ≫ Z.ι)
    (ht : IsSquareZeroClosedImmersion B S hS t) (hu : IsEtale B S hS u)
    (hVs : IsAffine ((BigFppfOver.toScheme B S hS).obj Vs)) :
    ∃ g : yoneda.obj Vs ⟶ yoneda.obj Us, yoneda.map t ≫ g = 𝟙 (yoneda.obj Us) ∧
      g ≫ yoneda.map t ≫ v ≫ (h' ≫ p).hom = v ≫ (h' ≫ p).hom := by
  have hciU : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map t) := ht.1
  have hUs : IsAffine ((BigFppfOver.toScheme B S hS).obj Us) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map t)
  have hsmU : FormallySmooth (u ≫ (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom) :=
    FormallySmooth.comp u _ (fun P Q hP hQ i hi x y hxy =>
      (formallyEtale_of_etale B S hS u ((isEtale_iff_presheaf_of_yoneda B S hS u).1 hu)
        P Q hP hQ i hi x y hxy).exists) hsm
  have hι : (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom = Z.ι ≫ (h' ≫ p).hom := rfl
  have hsq' : 𝟙 (yoneda.obj Us) ≫ u ≫ (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom =
      yoneda.map t ≫ v ≫ (h' ≫ p).hom := by
    rw [Category.id_comp, hι, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨z, hz₁, hz₂⟩ := hsmU Us Vs hUs hVs t ht (yonedaEquiv (𝟙 (yoneda.obj Us)))
    (yonedaEquiv (v ≫ (h' ≫ p).hom))
    (calc _ = yonedaEquiv (𝟙 (yoneda.obj Us) ≫
            u ≫ (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom) :=
          (yonedaEquiv_comp _ _).symm
      _ = yonedaEquiv (yoneda.map t ≫ v ≫ (h' ≫ p).hom) := congrArg _ hsq'
      _ = _ := (yonedaEquiv_naturality _ _).symm)
  refine ⟨yonedaEquiv.symm z, ?_, ?_⟩
  · rw [yonedaEquiv_symm_naturality_left, hz₁, Equiv.symm_apply_apply]
  · rw [← Category.assoc (yoneda.map t) v, hsq, Category.assoc, ← hι,
      yonedaEquiv_symm_naturality_right, hz₂, Equiv.symm_apply_apply]

/-- **On every affine étale chart of `Z'` the restricted thickening has a retraction over `Y`**,
when `Z` is formally smooth over `Y`: the left inverse of
`AlgebraicGeometry.Space.exists_retraction_of_formallySmooth`, read through the identification of
the preimage of `Z` in the chart with the square-zero chart of
`AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`. -/
theorem exists_chartRetraction_of_formallySmooth
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (hsm : FormallySmooth (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom)
    (A : SmallEtale B S hS Z'.1) (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left)) :
    ∃ r : yonedaSpace B S hS A.1.left ⟶
        (⟨(preimageSubspace B S hS (etaleChartHom B S hS A)
            (thickeningClosedSubspace B S hS hZ)).1.toFunctor,
          (preimageSubspace B S hS (etaleChartHom B S hS A)
            (thickeningClosedSubspace B S hS hZ)).2.1⟩ : AlgebraicSpaces B S hS),
      subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
          (preimageSubspace B S hS (etaleChartHom B S hS A) (thickeningClosedSubspace B S hS hZ)) ≫
          r = 𝟙 _ ∧
        r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
            (preimageSubspace B S hS (etaleChartHom B S hS A)
              (thickeningClosedSubspace B S hS hZ)) ≫
          etaleChartHom B S hS A ≫ h' ≫ p = etaleChartHom B S hS A ≫ h' ≫ p := by
  have hv : IsEtale B S hS A.1.hom := (isEtale_iff_presheaf_of_yoneda B S hS A.1.hom).2 A.2
  obtain ⟨Us, t, u, hpb, -, hu, ht⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening B S hS hZ.firstOrder A.1.left A.1.hom hv hA
  obtain ⟨g, hg₁, hg₂⟩ := exists_retraction_of_formallySmooth B S hS hZ p hsm t A.1.hom u
    hpb.w ht hu hA
  have hrange : Subfunctor.range (yoneda.map t) ≤ Z.preimage A.1.hom := by
    rintro T _ ⟨y, rfl⟩
    change A.1.hom.app T ((yoneda.map t).app T y) ∈ Z.obj T
    rw [← NatTrans.comp_app_apply, hpb.w]
    exact (u.app T y).2
  let lt := Subfunctor.lift (yoneda.map t) hrange
  have hlt : lt ≫ (Z.preimage A.1.hom).ι = yoneda.map t := Subfunctor.lift_ι _ _
  let ℓ := hpb.lift (Z.preimage A.1.hom).ι (Z.fromPreimage A.1.hom)
    (Subfunctor.fromPreimage_ι Z A.1.hom).symm
  have hℓ : ℓ ≫ yoneda.map t = (Z.preimage A.1.hom).ι := hpb.lift_fst _ _ _
  have hι : (Z.preimage A.1.hom).ι ≫ g ≫ lt = 𝟙 _ := by
    refine (cancel_mono (Z.preimage A.1.hom).ι).1 ?_
    rw [Category.assoc, Category.assoc, hlt, Category.id_comp, ← hℓ, Category.assoc,
      ← Category.assoc (yoneda.map t) g, hg₁, Category.id_comp]
  refine ⟨ObjectProperty.homMk (g ≫ lt), ObjectProperty.hom_ext _ hι,
    ObjectProperty.hom_ext _ ?_⟩
  change (g ≫ lt) ≫ (Z.preimage A.1.hom).ι ≫ A.1.hom ≫ (h' ≫ p).hom = A.1.hom ≫ (h' ≫ p).hom
  rw [Category.assoc, ← Category.assoc lt, hlt]
  exact hg₂

/-- **The first arrow of the sequence of Stacks 05ZA at the universal first order thickening is
injective when the source is formally smooth.**  For the universal first order thickening
`Z ⊂ Z'` of a formally unramified `h = ι ≫ h' : Z ⟶ X` over `Y`, with `Z` formally smooth over
`Y`, the first arrow `𝒞_{Z/Z'} ⟶ ι^*Ω_{Z'/Y}` of the sequence of Stacks 05ZA is a monomorphism.

This is `AlgebraicGeometry.Space.mono_conormalSequenceIdealPullbackMap_of_retractions` with the
retractions of `AlgebraicGeometry.Space.exists_chartRetraction_of_formallySmooth`. -/
theorem mono_conormalSequenceFirstMap_of_formallySmooth
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (hsm : FormallySmooth (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom) :
    Mono (conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p)) :=
  mono_conormalSequenceIdealPullbackMap_of_retractions B S hS
    (thickeningClosedSubspace B S hS hZ) hZ.firstOrder (h' ≫ p)
    (exists_chartRetraction_of_formallySmooth B S hS hZ p hsm)

namespace IsUniversalFirstOrderThickening

/-- **Stacks 06BJ.**  Let `h = ι ≫ h' : Z ⟶ X` be a formally unramified morphism of algebraic
spaces over `Y`, with universal first order thickening `Z ⊂ Z'` over `X` given by `hZ`, and
assume `Z` is formally smooth over `Y`.  Then the canonical exact sequence
```
  0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of Stacks 060F, `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.conormalSequence`, is
short exact.

Exactness at the middle and the epimorphism on the right are Stacks 060F.  The first arrow
followed by the isomorphism of Stacks 060E is the first arrow of Stacks 05ZA for `Z ⊂ Z'`, which
is a monomorphism by `AlgebraicGeometry.Space.mono_conormalSequenceFirstMap_of_formallySmooth`. -/
@[stacks 06BJ]
theorem conormalSequence_shortExact_of_formallySmooth
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (hsm : FormallySmooth (universalThickeningInclusion B S hS hZ ≫ h' ≫ p).hom) :
    ShortComplex.ShortExact (C := Modules.{u, u} B S hS (universalThickeningSubSpace B S hS hZ).obj
      (universalThickeningSubSpace B S hS hZ).property) (hZ.conormalSequence B S hS p) := by
  have hcomp : Mono (thickeningConormalFirstMap B S hS hZ p
      (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p) ≫
        thickeningSheafOfDifferentialsMap B S hS hZ p) := by
    rw [thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap B S hS hZ p _]
    exact mono_conormalSequenceFirstMap_of_formallySmooth B S hS hZ p hsm
  have hf : Mono (thickeningConormalFirstMap B S hS hZ p
      (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p)) :=
    mono_of_mono _ (thickeningSheafOfDifferentialsMap B S hS hZ p)
  exact ShortComplex.ShortExact.mk' (C := Modules.{u, u} B S hS
      (universalThickeningSubSpace B S hS hZ).obj (universalThickeningSubSpace B S hS hZ).property)
    (hZ.conormalSequence_exact B S hS p) hf (hZ.epi_conormalSequence_g B S hS p)

end IsUniversalFirstOrderThickening

end AlgebraicGeometry.Space

end

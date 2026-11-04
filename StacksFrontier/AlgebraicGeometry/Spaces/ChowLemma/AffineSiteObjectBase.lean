module

public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Chow's lemma over an affine object of the site (Stacks 089J)

`AlgebraicGeometry.Space.exists_chowSchemeCover_over_spec` is Stacks 089J for an algebraic space
`X` over an arbitrary base scheme `S` of the big fppf site, equipped with a separated morphism of
finite type to the representable presheaf of an object of the site presented as
`AlgebraicGeometry.siteObject` of a morphism `Spec A ⟶ S`. This file removes the presentation:
the base object may be *any* object `T` of the big fppf site of `S` whose underlying scheme is
affine. That is the form in which the base is reached by the reduction of Stacks 08AR to a
Noetherian affine base, `AlgebraicGeometry.Space.isCoherent_rightDerived_of_isProper_of_witness`.

## Main results

* `AlgebraicGeometry.Space.exists_chowSchemeCover_over_affine`: **Stacks 089J over an affine
  object of the site.** An algebraic space `X` over `S` with a separated morphism of finite type
  `g : X ⟶ h_T`, where `T` is an object of the big fppf site of `S` with affine underlying scheme,
  is the target of a proper surjective morphism `p : h_{X'} ⟶ X` from a scheme `X'` of the site
  over `T`, compatible with the two morphisms to `h_T`, with `X' ⟶ T` H-quasi-projective on
  underlying schemes.
* `AlgebraicGeometry.Space.exists_chowSchemeCover_of_isProper_over_affine`: the same for a
  *proper* `g`, where the cover `X' ⟶ T` is then proper and H-projective — the diagram the proof
  of Stacks 08AR draws: `X' ⟶ X` proper surjective and `X' ⟶ P^n_T` a closed immersion.
* `Stacks.HProjective.isHProjective_of_isHQuasiProjective_of_isProper`: a proper H-quasi-projective
  morphism of schemes is H-projective (Stacks 04NX and 01W0 for schemes: the immersion into `P^n`
  is proper, hence closed).

## Implementation notes

The underlying scheme `T₀` of `T` is isomorphic to `Spec Γ(T₀, ⊤)` by `Scheme.isoSpec`, and that
spectrum lies in the site because a monomorphism which is quasi-compact does not increase the size
of a scheme (`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact`). The resulting isomorphism
of objects of the site between `T` and `siteObject (T₀.isoSpec.inv ≫ T.hom)` moves the morphism
`g` and the cover back and forth; separatedness and finite type are invariant under that move by
`AlgebraicGeometry.Space.isSeparated_of_arrowIso` and
`AlgebraicGeometry.Space.isFiniteType_of_arrowIso`, and H-quasi-projectivity by
`Stacks.HProjective.isHQuasiProjective_of_iso`.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.HProjective

open _root_.AlgebraicGeometry

/-- **A proper H-quasi-projective morphism of schemes is H-projective.** The immersion
`i : X ⟶ P^n_S` through which `f` factors is proper, `f` being proper and `P^n_S ⟶ S` separated,
so its image is closed and it is a closed immersion. -/
theorem isHProjective_of_isHQuasiProjective_of_isProper {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsHQuasiProjective f) [IsProper f] : IsHProjective f := by
  obtain ⟨n, i, hi, -, hig⟩ := hf
  have := hi
  have : IsProper (i ≫ (projectiveSpaceOver n S ↘ S)) := by rw [hig]; infer_instance
  have : IsProper i := IsProper.of_comp i (projectiveSpaceOver n S ↘ S)
  exact ⟨n, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, hig⟩

end Stacks.HProjective

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of the big fppf site of `S` with affine underlying scheme `T₀` is isomorphic to the
spectrum of `Γ(T₀, ⊤)`, viewed as an object of the site over `S` along `T₀.isoSpec.inv ≫ T.hom`.
The spectrum lies in the site, its size being at most that of `T₀`. -/
theorem exists_siteObject_iso_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    ∃ (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S),
      Nonempty (siteObject B S hS hA a ≅ T) := by
  let T₀ := (BigFppfOver.toScheme B S hS).obj T
  have hA : B.Contains (Spec Γ(T₀, ⊤)) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact T₀.isoSpec.inv) T.left.property
  refine ⟨Γ(T₀, ⊤), hA, T₀.isoSpec.inv ≫ T.hom.hom, ⟨Over.isoMk
    (ObjectProperty.isoMk _ T₀.isoSpec.symm) ?_⟩⟩
  ext
  rfl

/-- **Chow's lemma for algebraic spaces over an affine object of the site, [Stacks, Tag 089J].**

Let `T` be an object of the big fppf site of `S` whose underlying scheme is affine, and let `X` be
an algebraic space over `S` with a separated morphism of finite type `g : X ⟶ h_T`. Then there are
an object `X'` of the big fppf site of `S`, a morphism `ψ : X' ⟶ T`, and a proper surjective
morphism `p : h_{X'} ⟶ X` with `p ≫ g = h_ψ`, such that `ψ` is H-quasi-projective on underlying
schemes.

This is `AlgebraicGeometry.Space.exists_chowSchemeCover_over_spec` transported along the
isomorphism `AlgebraicGeometry.Space.exists_siteObject_iso_of_isAffine` between `T` and the
spectrum of its global sections. -/
theorem exists_chowSchemeCover_over_affine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj T) (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g) :
    ∃ (X' : BigFppfOver B S hS) (ψ : X' ⟶ T) (p : yoneda.obj X' ⟶ X),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ g = yoneda.map ψ ∧
        IsHQuasiProjective ((BigFppfOver.toScheme B S hS).map ψ) := by
  obtain ⟨A, hA, a, ⟨e⟩⟩ := exists_siteObject_iso_of_isAffine B S hS T hT
  have hsep' : IsSeparated B S hS (g ≫ yoneda.map e.inv) :=
    isSeparated_of_arrowIso B S hS g _ (𝟙 _) (yoneda.map e.inv) (by simp) hsep
  have hft' : IsFiniteType B S hS (g ≫ yoneda.map e.inv) :=
    isFiniteType_of_arrowIso B S hS g _ (𝟙 _) (yoneda.map e.inv) (by simp) hft
  obtain ⟨X', ψ, p, hp, hps, hw, hqp⟩ :=
    exists_chowSchemeCover_over_spec B S hS A hA a hX (g ≫ yoneda.map e.inv) hsep' hft'
  refine ⟨X', ψ ≫ e.hom, p, hp, hps, ?_, ?_⟩
  · rw [yoneda.map_comp, ← hw, Category.assoc, Category.assoc, ← yoneda.map_comp, e.inv_hom_id,
      yoneda.map_id, Category.comp_id]
  · refine Stacks.HProjective.isHQuasiProjective_of_iso (Iso.refl _)
      ((BigFppfOver.toScheme B S hS).mapIso e) ?_ hqp
    simp

/-- **The Chow diagram of the proof of Stacks 08AR.** Let `T` be an object of the big fppf site
of `S` with affine underlying scheme and let `g : X ⟶ h_T` be a proper morphism from an algebraic
space. Then there are an object `X'` of the site, a morphism `ψ : X' ⟶ T` which is proper and
H-projective on underlying schemes, and a proper surjective `p : h_{X'} ⟶ X` with
`p ≫ g = h_ψ`.

This is `AlgebraicGeometry.Space.exists_chowSchemeCover_over_affine`; the composite `p ≫ g = h_ψ`
is proper, hence so is `ψ` (properness of a morphism of the site is read on its Yoneda image by
`AlgebraicGeometry.Space.presheaf_isProper_iff`), and a proper H-quasi-projective morphism is
H-projective. -/
theorem exists_chowSchemeCover_of_isProper_over_affine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj T) (hg : IsProper B S hS g) :
    ∃ (X' : BigFppfOver B S hS) (ψ : X' ⟶ T) (p : yoneda.obj X' ⟶ X),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ g = yoneda.map ψ ∧
        _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map ψ) ∧
        Stacks.HProjective.IsHProjective ((BigFppfOver.toScheme B S hS).map ψ) := by
  obtain ⟨X', ψ, p, hp, hps, hw, hqp⟩ :=
    exists_chowSchemeCover_over_affine B S hS T hT hX g hg.1 hg.2.1
  have hyψ : IsProper B S hS (yoneda.map ψ) := by
    rw [← hw]
    exact isProper_comp' B S hS p g hX (isAlgebraicSpace_yoneda B S hS T) hp hg
  have hψ : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map ψ) :=
    (presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsProper.{u}) inferInstance ψ).1
      ((presheaf_isProper_iff B S hS (yoneda.map ψ) (isAlgebraicSpace_yoneda B S hS X')
        (isAlgebraicSpace_yoneda B S hS T) (Functor.relativelyRepresentable.map _ ψ)).1 hyψ)
  have := hψ
  exact ⟨X', ψ, p, hp, hps, hw, hψ,
    Stacks.HProjective.isHProjective_of_isHQuasiProjective_of_isProper hqp⟩

end AlgebraicGeometry.Space

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatSurjectiveMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# Flat monomorphisms to an affine scheme every point of which is a generalization

Let `S` be a scheme contained in a big fppf site `B`, let `T` be an object of that site with
affine underlying scheme, and let `f : X ⟶ h_T` be a quasi-compact flat morphism from an
algebraic space over `S`. If some point `t` of `T` is a specialization of every point of `T` —
the situation of `T = Spec(A)` for a local ring `A` and `t` its closed point — and `X` has a
point above `t`, then `f` is surjective; if `f` is in addition a monomorphism, it is an
isomorphism, so `X` is a scheme.

This is the local case of **Stacks 0B8A**, that a flat monomorphism of algebraic spaces is
representable by schemes: it is the whole of the source's argument for that lemma after its
reduction, by Limits of Spaces **Stacks 0B80**, to a base which is the spectrum of a local ring.
The lemma itself is `AlgebraicGeometry.Space.relativelyRepresentable_of_isFlat_of_mono`, proved
by a different route that does not pass through local rings.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_isFlat_of_isQuasiCompact_of_forall_specializes`:
  such a morphism is surjective.
* `AlgebraicGeometry.Space.isIso_of_mono_of_isFlat_of_isQuasiCompact_of_forall_specializes`:
  such a morphism which is a monomorphism is an isomorphism.

## Implementation notes

Surjectivity is read on an affine étale chart rather than through Decent Spaces
**Stacks 0B7W**, the lifting of specializations along a flat morphism of algebraic spaces
(`AlgebraicGeometry.Space.exists_specializes_pointsMap_eq_of_isFlat`). Quasi-compactness of
`f` and of the affine target make `X` quasi-compact, hence covered by a single affine étale
chart `a : h_U ⟶ X` (**Stacks 03H6**); the chart's structure morphism `h : U ⟶ T`, which
exists because both source and target are represented, is then a *flat morphism of schemes*,
being one of the squares flatness of `f` tests (**Stacks 03ML**, part (1)). So Mathlib's
`AlgebraicGeometry.Flat.generalizingMap` lifts the specialization `t' ⤳ t` inside `U`, and
the identification of the points of a represented presheaf with the points of the
representing scheme (**Stacks 03BX**, clause (1)) carries the lifted point back to a point of
`X` above `t'`. This avoids having to verify, for the representable target, the finite-fibre
hypothesis that `exists_specializes_pointsMap_eq_of_isFlat` carries.

The step from surjectivity to invertibility is **Stacks 0B8C**,
`AlgebraicGeometry.Space.isIso_of_mono_of_isQuasiCompact_of_isFlat_of_isSurjective`, which is
already in the library; the hypotheses here are exactly its hypotheses with surjectivity
replaced by the data producing it.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 0B8A](https://stacks.math.columbia.edu/tag/0B8A)
* [Stacks Project, Tag 0B8C](https://stacks.math.columbia.edu/tag/0B8C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-compact flat morphism `f : X ⟶ h_T` from an algebraic space over `S` to a
represented presheaf with affine representing scheme is surjective as soon as `X` has a point
above a point `t` of `T` which is a specialization of every point of `T`.

The hypothesis on `t` is the one the spectrum of a local ring satisfies at its closed point. -/
theorem isSurjective_of_isFlat_of_isQuasiCompact_of_forall_specializes
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ yoneda.obj T) (hqc : IsQuasiCompact B S hS f) (hf : IsFlat B S hS f)
    (t : (BigFppfOver.toScheme B S hS).obj T)
    (ht : ∀ t' : (BigFppfOver.toScheme B S hS).obj T, t' ⤳ t)
    (x : points B S hS X)
    (hx : pointsMap B S hS X f x = (schemePointsHomeomorph B S hS T).symm t) :
    IsSurjective B S hS f := by
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  -- `X` is quasi-compact, being the base change of `f` along the identity of the affine `h_T`.
  have hbase : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ yoneda.obj T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsQuasiCompactSpace B S hS (pullback g f) :=
    ((isQuasiCompact_tfae B S hS hX hTalg f).out 1 3).mp hqc
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 (yoneda.obj T)) f))
      (hbase T (𝟙 _) hT)
  obtain ⟨U, a, hUaff, haSurj, haEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).mp hXqc
  -- The chart's structure morphism to `T`, a flat morphism of schemes.
  have heq : yoneda.map (yoneda.preimage (a ≫ f)) = a ≫ f := yoneda.map_preimage _
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))) :=
    hf U T a (𝟙 _) (yoneda.preimage (a ≫ f))
      ((isEtale_iff_presheaf_of_yoneda B S hS a).1 haEt)
      ((isEtale_iff_presheaf_of_yoneda B S hS (𝟙 (yoneda.obj T))).1
        (isEtale_of_isIso B S hS _)) (by simp [heq])
  have := hflat
  -- A point of the chart above `x`, read on the representing scheme.
  obtain ⟨u, hu⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).1 haSurj x
  have husymm : (schemePointsHomeomorph B S hS U).symm
      (schemePointsHomeomorph B S hS U u) = u :=
    (schemePointsHomeomorph B S hS U).symm_apply_apply u
  have hut : (BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))
      (schemePointsHomeomorph B S hS U u) = t := by
    refine (schemePointsHomeomorph B S hS T).symm.injective ?_
    rw [← schemePointsHomeomorph_symm_naturality, husymm, heq, pointsMap_comp_apply, hu, hx]
  intro y
  obtain ⟨v, -, hv⟩ :=
    Flat.generalizingMap ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f)))
      (a := schemePointsHomeomorph B S hS U u) (b := schemePointsHomeomorph B S hS T y)
      (by rw [hut]; exact ht _)
  refine ⟨pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm v), ?_⟩
  rw [← pointsMap_comp_apply, ← heq, schemePointsHomeomorph_symm_naturality, hv]
  exact (schemePointsHomeomorph B S hS T).symm_apply_apply y

/-- **The local case of Stacks 0B8A.** A quasi-compact flat monomorphism `f : X ⟶ h_T` from an
algebraic space over `S` to a represented presheaf with affine representing scheme is an
isomorphism as soon as `X` has a point above a point `t` of `T` which is a specialization of
every point of `T`.

The morphism is surjective by
`AlgebraicGeometry.Space.isSurjective_of_isFlat_of_isQuasiCompact_of_forall_specializes`, and
a quasi-compact flat surjective monomorphism is an isomorphism by **Stacks 0B8C**. -/
theorem isIso_of_mono_of_isFlat_of_isQuasiCompact_of_forall_specializes
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ yoneda.obj T) (hmono : Mono f)
    (hqc : IsQuasiCompact B S hS f) (hf : IsFlat B S hS f)
    (t : (BigFppfOver.toScheme B S hS).obj T)
    (ht : ∀ t' : (BigFppfOver.toScheme B S hS).obj T, t' ⤳ t)
    (x : points B S hS X)
    (hx : pointsMap B S hS X f x = (schemePointsHomeomorph B S hS T).symm t) :
    IsIso f := by
  have hsurj : IsSurjective B S hS f :=
    isSurjective_of_isFlat_of_isQuasiCompact_of_forall_specializes B S hS hX T hT f hqc hf t ht
      x hx
  let f' : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ := ObjectProperty.homMk f
  have : Mono f' := (mono_hom_iff_mono B S hS f').mp hmono
  exact (ObjectProperty.isIso_hom_iff f').mpr
    (isIso_of_mono_of_isQuasiCompact_of_isFlat_of_isSurjective B S hS f' hqc hf hsurj)

end AlgebraicGeometry.Space

end

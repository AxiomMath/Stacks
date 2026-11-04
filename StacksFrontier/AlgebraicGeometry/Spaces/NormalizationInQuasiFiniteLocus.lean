module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization

/-!
# The normalization of the target in the source along the quasi-finite locus

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `ν : Y' ⟶ Y`,
`f' : X ⟶ Y'` be the normalization of `Y` in `X`, so that `f = f' ≫ ν`. Zariski's Main Theorem
for algebraic spaces, Tag 082I, asserts for `f` of finite type and separated the existence of an
open subspace `U' ⊆ Y'` such that `(f')⁻¹(U') ⟶ U'` is an isomorphism and `(f')⁻¹(U')` is the
set of points of `X` at which `f` is quasi-finite.

This file proves the case in which `f` is itself integral, and the case in which `f` is finite.
In both cases the open subspace may be taken to be all of `Y'`: an integral morphism is its own
normalization, so `f'` is an isomorphism, and a finite morphism is in addition quasi-finite at
every point of its source.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isRelativeNormalization_id_of_isIntegralHom` is Tag 0825 in the form
  of the characterization: an integral morphism is the normalization of its target in its
  source.
* `AlgebraicGeometry.Space.IsRelativeNormalization.isIso_of_isIntegralHom`: if `f` is integral
  then the canonical morphism `f' : X ⟶ Y'` from `X` to the normalization of `Y` in `X` is an
  isomorphism.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isIso_fromPreimage_of_isFinite`: if `f` is
  finite then both conclusions of Tag 082I hold with `U' = Y'`.

## Implementation notes

**The normalization is taken as data satisfying the characterization of Tag 0823.** The source
of Tag 082I writes "let `Y'` be the normalization of `Y` in `X`"; the relative spectrum that
constructs it is not available unconditionally in this library, so the object is presented here,
as in `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization`, by the predicate
`AlgebraicGeometry.Space.IsRelativeNormalization` on a factorization `f = f' ≫ ν` with `ν`
integral: that `ν` is integral and that every factorization of `f` through an integral morphism
of algebraic spaces receives a unique compatible morphism from `Y'`. Stating the results for
every such factorization rather than for a chosen one is both the available form and the
stronger statement.

**Why an integral morphism is its own normalization.** The identity of `X` is a factorization of
`f` through the integral morphism `f` itself, so the universal property produces a
`k : Y' ⟶ X` with `f' ≫ k = 𝟙` and `k ≫ f = ν`. Then `k ≫ f'` and `𝟙` both solve the
universal property for the factorization `f = f' ≫ ν`, whose uniqueness clause forces
`k ≫ f' = 𝟙`; so `k` is a two-sided inverse of `f'`. This is the content of Tag 0825, read
through the characterization.

**The hypotheses of the two results against those of Tag 082I.** The tag assumes `f` of finite
type and separated. The first result below assumes instead that `f` is integral, which neither
implies nor is implied by those, and it proves only the isomorphism conclusion; the quasi-finite
locus is not mentioned, because an integral morphism need not be quasi-finite anywhere. The
second assumes that `f` is finite, which is strictly stronger than the tag's hypotheses — a
finite morphism is of finite type and separated by Tag 0A4X — and proves both numbered
conclusions of the tag. Neither result is the tag in its stated generality: the reduction of the
source to an affine base rests on the compatibility of the normalization with smooth base change
and on "being an isomorphism" being fpqc local on the base, and those are not used here.

**Both conclusions carry content at `U' = Y'`.** The first says that `f'` is an isomorphism, not
merely that some open subspace of `Y'` is isomorphic to its inverse image; the second says that
`f` is quasi-finite at every point of `X`, which for a finite morphism is local quasi-finiteness,
Tag 0A4X.

## References

* [Stacks Project, Tag 082I](https://stacks.math.columbia.edu/tag/082I)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0825](https://stacks.math.columbia.edu/tag/0825)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {ν : Y' ⟶ Y} {f' : X ⟶ Y'}

/-- **Stacks 0825, in the form of the characterization of Tag 0823.** An integral morphism
`f : X ⟶ Y` of algebraic spaces over `S` is the normalization of `Y` in `X`: the factorization
of `f` as the identity of `X` followed by `f` itself has the two characterizing properties.

Integrality of the second factor is the hypothesis, and a factorization `f = g ≫ π` through an
integral morphism `π : Z ⟶ Y` already has `g` as a morphism out of `X`, which is therefore the
unique morphism compatible with the two factorizations. -/
@[stacks 0825 "in the form of the characterization of Tag 0823: an integral morphism is the \
normalization of its target in its source"]
theorem isRelativeNormalization_id_of_isIntegralHom (hf : IsIntegralHom B S hS f) :
    IsRelativeNormalization B S hS f f (𝟙 X) :=
  ⟨Category.id_comp f, hf, fun _ _ _π _ g hg =>
    ⟨g, ⟨Category.id_comp g, hg⟩, fun y hy => (Category.id_comp y).symm.trans hy.1⟩⟩

namespace IsRelativeNormalization

/-- **Stacks 082I, the isomorphism conclusion for an integral morphism.** Let `f : X ⟶ Y` be an
integral morphism of algebraic spaces over `S` and let `ν : Y' ⟶ Y`, `f' : X ⟶ Y'` be the
normalization of `Y` in `X`. Then `f'` is an isomorphism, so the open subspace `U' ⊆ Y'` of the
tag may be taken to be all of `Y'`.

The identity of `X` factors `f` through the integral morphism `f`, so the universal property
yields `k : Y' ⟶ X` with `f' ≫ k = 𝟙` and `k ≫ f = ν`; uniqueness in the universal property
for the factorization `f = f' ≫ ν` identifies `k ≫ f'` with `𝟙`. -/
@[stacks 082I "the isomorphism conclusion when f is integral: the canonical morphism to the \
normalization is an isomorphism, so the open subspace may be taken to be the whole \
normalization"]
theorem isIso_of_isIntegralHom (h : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hf : IsIntegralHom B S hS f) : IsIso f' := by
  obtain ⟨k, ⟨hk, hkf⟩, -⟩ := h.existsUnique_lift hX f hf (𝟙 X) (Category.id_comp f)
  refine ⟨k, hk, ?_⟩
  refine (h.existsUnique_lift hY' ν h.isIntegralHom f' h.fac).unique ⟨?_, ?_⟩
    ⟨Category.comp_id f', Category.id_comp ν⟩
  · rw [← Category.assoc, hk, Category.id_comp]
  · rw [Category.assoc, h.fac, hkf]

end IsRelativeNormalization

/-- **Stacks 082I for a finite morphism.** Let `f : X ⟶ Y` be a finite morphism of algebraic
spaces over `S` and let `ν : Y' ⟶ Y`, `f' : X ⟶ Y'` be the normalization of `Y` in `X`. Then
there is an open subspace `U' ⊆ Y'` such that `(f')⁻¹(U') ⟶ U'` is an isomorphism and the point
set of `(f')⁻¹(U')` is the set of points of `X` at which `f` is quasi-finite; one may take
`U' = Y'`.

A finite morphism is integral by Tag 0414, so `f'` is an isomorphism and hence so is its base
change `(f')⁻¹(Y') ⟶ Y'`; and a finite morphism is locally quasi-finite by Tag 0A4X, hence
quasi-finite at every point of its source, which is the whole of `(f')⁻¹(Y')`. -/
@[stacks 082I "both numbered conclusions in the case of a finite morphism, with the open \
subspace the whole normalization"]
theorem exists_isOpenSubspace_isIso_fromPreimage_of_isFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (h : IsRelativeNormalization B S hS f ν f')
    (hf : IsFinite B S hS f) :
    ∃ U' : Subfunctor Y', IsOpenSubspace B S hS U' ∧ IsIso (U'.fromPreimage f') ∧
      ∀ x : points B S hS X,
        x ∈ Set.range (pointsMap B S hS (U'.preimage f').toFunctor (U'.preimage f').ι) ↔
          IsQuasiFiniteAt B S hS f x := by
  have hiso : IsIso f' :=
    h.isIso_of_isIntegralHom hX hY' (IsFinite.isIntegralHom B S hS hf)
  have hpre : IsIso ((⊤ : Subfunctor Y').preimage f').ι :=
    (Subfunctor.eq_top_iff_isIso _).1 ((Subfunctor.preimage_eq_top_iff _ _).2 le_top)
  refine ⟨⊤, isOpenSubspace_top hY', ?_, fun x => ?_⟩
  · have hfac : (⊤ : Subfunctor Y').fromPreimage f'
        = (((⊤ : Subfunctor Y').preimage f').ι ≫ f') ≫ inv (⊤ : Subfunctor Y').ι := by
      rw [← Subfunctor.fromPreimage_ι (⊤ : Subfunctor Y') f', Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    rw [hfac]
    infer_instance
  · refine ⟨fun _ => ?_, fun _ => pointsMap_surjective_of_isIso B S hS _ x⟩
    exact (isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS hX hY f).1
      (isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hX hY f hf).2 x

end AlgebraicGeometry.Space

end

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeReflectsIso

/-!
# Bounded charts survive relocalization to a larger base scheme

Let `k : S ⟶ S'` be a morphism of schemes contained in a big fppf site and let
`Λ = CategoryTheory.OverShriek.relocalizePresheafFunctor k` be the presheaf level lower shriek
of Stacks 03EH, which views a presheaf on the big fppf site of `S` as a presheaf on the big
fppf site of `S'`. The size condition `AlgebraicGeometry.Space.ChartsBounded` on an inverse
system of presheaves is unchanged by that view.

The reason is that `Λ` does not touch the underlying schemes of the site; it only composes
structure morphisms with `k`. An affine scheme-valued point `f₀ : h_{U₀} ⟶ Λ (D i₀)` of a
relocalized stage is `Λ` of an affine scheme-valued point `σ : h_{U₀'} ⟶ D i₀` over `S`, where
`U₀'` is `U₀` with its structure morphism factored through `k`, so with the same underlying
scheme (`CategoryTheory.OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`). Being a lower
shriek, `Λ` preserves connected limits, in particular the fibre product of a transition
morphism `D a` with `σ`, so an object `W` of the site over `S'` representing the base change of
`f₀` along `Λ (D a)` represents `Λ (D j ×_{D i₀} U₀')`. Reading that representation through the
same factorization presents it as `Λ` of a morphism `h_{W'} ⟶ D j ×_{D i₀} U₀'`, with `W'` the
object `W` viewed over `S`; and `Λ` reflects isomorphisms
(`CategoryTheory.OverShriek.isIso_of_isIso_map_relocalizePresheafFunctor`), so that morphism is
an isomorphism. Hence the cardinal bounding the base changes of `σ` bounds `W` as well, the
underlying schemes of `W` and `W'` being the same.

The two cardinality conditions of `AlgebraicGeometry.Space.ChartsBounded` are conditions on the
index category alone, which relocalization leaves alone.

## Main results

* `AlgebraicGeometry.Space.ChartsBounded.relocalize`: bounded charts relocalize.
* `AlgebraicGeometry.Space.ChartsBounded.viewOverIntegers`: the case of the structure morphism
  `S ⟶ Spec ℤ`, which is the relocalization that reduces a statement over `S` to the same
  statement over an affine base.

## Implementation notes

This is the size-bound counterpart of the relocalization transfer statements for affineness of
a morphism and quasi-compactness of an algebraic space, and its first two steps are theirs:
every morphism from a representable presheaf into a relocalization is a relocalized morphism
from a representable presheaf with the same underlying scheme, and relocalization carries the
fibre products involved to fibre products. The extra step is the one in the opposite direction,
which those statements do not need: the object of the site representing the relocalized base
change has to be recognized as an object representing the base change over `S`, and that is
where relocalization reflecting isomorphisms is used.

## References

* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 04IL](https://stacks.math.columbia.edu/tag/04IL)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Bounded charts are unchanged by relocalization to a larger base scheme.** The presheaf
level lower shriek along `k : S ⟶ S'` leaves the underlying schemes of the site alone — it only
composes structure morphisms with `k` — so the cardinals bounding the base changes of an affine
scheme-valued point over `S` bound the base changes of the corresponding point over `S'`.

Concretely, an affine scheme-valued point of a relocalized stage is the relocalization of an
affine scheme-valued point over `S` with the same underlying scheme, relocalization preserves
the fibre products defining the base changes, being a left adjoint, and relocalization reflects
isomorphisms, so an object of the site over `S'` representing a base change of the relocalized
point represents, after its structure morphism is factored through `k`, the corresponding base
change over `S`.

The two cardinality conditions are about the index category only, which is unchanged. -/
theorem ChartsBounded.relocalize {I : Type u} [Category.{u} I]
    {Dsys : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : ChartsBounded B S hS Dsys)
    {S' : Scheme.{u}} (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS') :
    ChartsBounded B S' hS' (Dsys ⋙ OverShriek.relocalizePresheafFunctor k) where
  mk_lt := h.mk_lt
  mk_over_lt := h.mk_over_lt
  bound := by
    intro i₀ U₀ f₀
    obtain ⟨ψ, hψ, σ, hf₀⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp k f₀
    have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk ψ)) := U₀.property
    obtain ⟨mu, hmu, hb⟩ := h.bound i₀ ⟨Over.mk ψ, haff⟩ σ
    refine ⟨mu, hmu, fun j a W e => ?_⟩
    have hsq : IsPullback
        ((OverShriek.relocalizePresheafFunctor k).map (pullback.fst (Dsys.map a) σ))
        ((OverShriek.relocalizePresheafFunctor k).map (pullback.snd (Dsys.map a) σ) ≫
          (OverShriek.relocalizeYonedaFactorIso k hψ).inv)
        ((OverShriek.relocalizePresheafFunctor k).map (Dsys.map a)) f₀ :=
      ((IsPullback.of_hasPullback (Dsys.map a) σ).map
          (OverShriek.relocalizePresheafFunctor k)).of_iso (Iso.refl _) (Iso.refl _)
        (OverShriek.relocalizeYonedaFactorIso k hψ).symm (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp [hf₀])
    obtain ⟨χ, hχ, τ, hτ⟩ :=
      OverShriek.exists_eq_relocalizeYonedaFactorIso_comp k (e ≪≫ hsq.isoPullback.symm).hom
    have hmap : (OverShriek.relocalizeYonedaFactorIso k hχ).inv ≫
        (e ≪≫ hsq.isoPullback.symm).hom =
          (OverShriek.relocalizePresheafFunctor k).map τ := by
      rw [hτ, Iso.inv_hom_id_assoc]
    have : IsIso ((OverShriek.relocalizePresheafFunctor k).map τ) := by
      rw [← hmap]; infer_instance
    have : IsIso τ := OverShriek.isIso_of_isIso_map_relocalizePresheafFunctor k τ
    exact hb j a (Over.mk χ) (asIso τ)

/-- **Bounded charts are unchanged by viewing the system over the terminal scheme.** This is
`AlgebraicGeometry.Space.ChartsBounded.relocalize` along the structure morphism
`S ⟶ Spec ℤ`, which is the relocalization through which a statement about a system over `S` is
reduced to the same statement over an affine base. -/
theorem ChartsBounded.viewOverIntegers {I : Type u} [Category.{u} I]
    {Dsys : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : ChartsBounded B S hS Dsys)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    ChartsBounded B (⊤_ Scheme.{u}) hZ (Dsys ⋙ OverShriek.relocalizePresheafFunctor
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)) :=
  h.relocalize hZ _

end AlgebraicGeometry.Space

end

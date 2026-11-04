module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructure

/-!
# The étale local chart of Tag 0CBY base-changes

`Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_etale` transfers the chart
form of Tag 0CBY along *étale* morphisms of source and target. The absolute Noetherian
approximation step of the first proof of Tag 0CBY needs the transfer along a morphism of bases
which is not étale at all: the morphism `S = Spec R ⟶ S_i = Spec R_i` from the limit to a stage
of a presentation of `R` as a filtered colimit of finite type `ℤ`-algebras. This file supplies
that transfer, for a morphism of *affine* bases, which is the situation of that step.

The chart over the stage is `Spec R_i ← Spec B`, `U_i → Spec B[x, y]/(xy - t)`; base changing the
whole chart along `Spec R ⟶ Spec R_i` replaces `Spec B` by `Spec (B ⊗_{R_i} R)`, which is again
affine, and the nodal chart by the nodal chart over `B ⊗_{R_i} R` with the image parameter, by
`Stacks.NodalEtaleLocalStructure.isPullback_specMap_nodalChartMap`. Étaleness of the three legs
is preserved because étale morphisms are stable under base change, and the chosen point of the
base-changed neighbourhood exists because the image of a projection of a cartesian square of
schemes is the preimage of the image of the opposite morphism
(`AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback`).

## Main results

* `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_isPullback` — **the chart
  form base-changes along a morphism of affine bases.**

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks

universe u

namespace Stacks.NodalEtaleLocalStructure

/-- **The chart form of Tag 0CBY base-changes along a morphism of affine bases.** Let
`f₀ : X₀ ⟶ Spec A₀`, let `γ : A₀ → A` be a ring map and let `p : X ⟶ X₀`, `f : X ⟶ Spec A`
exhibit `f` as the base change of `f₀` along `Spec A ⟶ Spec A₀`. An étale local chart for `f₀`
at a point `x₀` is an étale local chart for `f` at any point of `X` lying over `x₀`.

The base of the new chart is `B ⊗_{A₀} A`, where `Spec B` is the base of the old one. -/
public theorem nonempty_nodalChartNeighbourhood_of_isPullback
    {A₀ A : Type u} [CommRing A₀] [CommRing A]
    (γ : CommRingCat.of A₀ ⟶ CommRingCat.of A)
    {X₀ X : Scheme.{u}} {p : X ⟶ X₀} {f : X ⟶ Spec (.of A)} {f₀ : X₀ ⟶ Spec (.of A₀)}
    (hsq : IsPullback p f f₀ (Spec.map γ))
    {x : X} {x₀ : X₀} (hx : p.base x = x₀)
    (d : NodalChartNeighbourhood f₀ x₀) :
    Nonempty (NodalChartNeighbourhood f x) := by
  classical
  obtain ⟨β, hβ⟩ := Spec.map_surjective d.toBase
  let : Algebra A₀ d.base := β.hom.toAlgebra
  let : Algebra A₀ A := γ.hom.toAlgebra
  have hβ' : CommRingCat.ofHom (algebraMap A₀ d.base) = β := rfl
  have hγ' : CommRingCat.ofHom (algebraMap A₀ A) = γ := rfl
  set B := TensorProduct A₀ d.base A
  set ψ : d.base →+* B := Algebra.TensorProduct.includeLeftRingHom
  set ρ : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
  -- the base of the new chart is `Spec B`, cartesian over `Spec A₀`
  have hV : IsPullback (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom ρ))
      d.toBase (Spec.map γ) := by
    have h0 := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct A₀ d.base A)
    rwa [hβ', hγ', hβ] at h0
  -- the local model of the new chart is the nodal chart over `B`, cartesian over the old one
  have hWS : IsPullback (Spec.map (CommRingCat.ofHom (nodalChartMap ψ d.param)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (nodalChartRing B (ψ d.param)))) ≫
        Spec.map (CommRingCat.ofHom ρ))
      (Spec.map (CommRingCat.ofHom (algebraMap d.base (nodalChartRing d.base d.param))) ≫
        d.toBase)
      (Spec.map γ) :=
    (isPullback_specMap_nodalChartMap ψ d.param).paste_vert hV
  -- the new étale neighbourhood of the source
  have hU : IsPullback (pullback.fst d.toSource p) (pullback.snd d.toSource p) d.toSource p :=
    IsPullback.of_hasPullback d.toSource p
  -- the map to the new local model
  have hcommChart : d.toChart ≫
      (Spec.map (CommRingCat.ofHom (algebraMap d.base (nodalChartRing d.base d.param))) ≫
        d.toBase) = d.toSource ≫ f₀ := d.comm.symm
  have hcomm : (pullback.fst d.toSource p ≫ d.toChart) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap d.base (nodalChartRing d.base d.param))) ≫
        d.toBase) =
      (pullback.snd d.toSource p ≫ f) ≫ Spec.map γ := by
    rw [Category.assoc, hcommChart, pullback.condition_assoc, hsq.w, Category.assoc]
  set c : (pullback d.toSource p : Scheme.{u}) ⟶ Spec (.of (nodalChartRing B (ψ d.param))) :=
    hWS.lift (pullback.fst d.toSource p ≫ d.toChart) (pullback.snd d.toSource p ≫ f) hcomm
  have hcfst : c ≫ Spec.map (CommRingCat.ofHom (nodalChartMap ψ d.param)) =
      pullback.fst d.toSource p ≫ d.toChart := hWS.lift_fst _ _ _
  have hcsnd : c ≫ (Spec.map (CommRingCat.ofHom
        (algebraMap B (nodalChartRing B (ψ d.param)))) ≫
      Spec.map (CommRingCat.ofHom ρ)) = pullback.snd d.toSource p ≫ f := hWS.lift_snd _ _ _
  -- the map to the new local model is étale, being a base change of the old one
  have hchartsq : IsPullback (pullback.fst d.toSource p) c d.toChart
      (Spec.map (CommRingCat.ofHom (nodalChartMap ψ d.param))) := by
    refine IsPullback.of_bot ?_ hcfst.symm hWS
    rw [hcsnd, hcommChart]
    exact hU.paste_vert hsq
  have hetSource : Etale (pullback.snd d.toSource p) :=
    MorphismProperty.of_isPullback hU d.etale_toSource
  have hetBase : Etale (Spec.map (CommRingCat.ofHom ρ)) :=
    MorphismProperty.of_isPullback hV d.etale_toBase
  have hetChart : Etale c := MorphismProperty.of_isPullback hchartsq d.etale_toChart
  -- the chosen point of the new neighbourhood
  have hrange : Set.range (pullback.snd d.toSource p).base =
      p.base ⁻¹' Set.range d.toSource.base := by
    simpa using Scheme.image_preimage_eq_of_isPullback hU Set.univ
  obtain ⟨pt, hpt⟩ : x ∈ Set.range (pullback.snd d.toSource p).base := by
    rw [hrange]
    exact ⟨d.pt, by rw [d.pt_mem, hx]⟩
  exact ⟨{ base := B
           param := ψ d.param
           U := pullback d.toSource p
           toSource := pullback.snd d.toSource p
           toBase := Spec.map (CommRingCat.ofHom ρ)
           toChart := c
           pt := pt
           etale_toSource := hetSource
           etale_toBase := hetBase
           etale_toChart := hetChart
           pt_mem := hpt
           comm := hcsnd.symm }⟩

end Stacks.NodalEtaleLocalStructure

end

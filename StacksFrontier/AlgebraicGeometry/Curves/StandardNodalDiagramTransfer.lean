module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructure

/-!
# Transferring the diagram of Tag 0CBY

`Stacks.NodalEtaleLocalStructure.StandardNodalDiagram f x` is the conclusion of
[Stacks, Tag 0CBY] for a morphism `f` and a point `x` of its source: étale morphisms `U ⟶ X`,
`V ⟶ S` and `U ⟶ W`, a cartesian square exhibiting `W` as the base change of the standard family
`Spec ℤ[u, v, a]/(uv - a) ⟶ Spec ℤ[a]` along a parameter `V ⟶ Spec ℤ[a]`, and a point of `U`
over `x`.

This file transfers that datum along the three operations the first proof of the tag performs on
the pair `(f, x)` before it reaches a base of finite type over the integers: composition with
étale morphisms of source and target, restriction to open subschemes of source and target, and an
**arbitrary** base change of the target. The last is the step that passes from a stage of a
Noetherian approximation of the base to the base itself, along a morphism which is not étale.

## Main results

* `Stacks.NodalEtaleLocalStructure.standardNodalDiagramOfEtale` — the diagram transfers along
  étale morphisms of source and target.
* `Stacks.NodalEtaleLocalStructure.standardNodalDiagramOfResLE` — the diagram is local on source
  and target.
* `Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isPullback` — **the diagram
  base-changes along an arbitrary morphism of bases.**

## Implementation notes

The base change is cheaper for `StandardNodalDiagram` than for the chart form
`Stacks.NodalEtaleLocalStructure.NodalChartNeighbourhood`, where it is
`nonempty_nodalChartNeighbourhood_of_isPullback`: the chart form names an affine neighbourhood
`Spec B` of the image point and a parameter `h : B`, so its base change must compute the new
chart as the nodal chart over `B ⊗ A` and is stated only for affine bases, whereas here the local
model `W` is given by a cartesian square and the base change of that square is again one. Nothing
is affine and nothing is a spectrum: `V`, `W` and `U` are replaced by `V ×_S' S`,
`W ×_V (V ×_S' S)` and `U ×_{X'} X`, the parameter `V ⟶ Spec ℤ[a]` by its composite with the
projection, and the cartesian square by the horizontal paste of the base-change square with the old
one.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks

universe u

namespace Stacks.NodalEtaleLocalStructure

/-- **The diagram of Tag 0CBY transfers along étale morphisms of source and target.** If
`p : X' ⟶ X` and `eV : V ⟶ S` are étale, `f' : X' ⟶ V` is compatible with `f : X ⟶ S` along
them, and `x'` is a point of `X'` over `x`, then the diagram for `f'` at `x'` is a diagram for
`f` at `x`: the two étale legs of the diagram are composed with `p` and with `eV`, and
everything else is unchanged. -/
public def standardNodalDiagramOfEtale {X X' S V : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ V}
    (p : X' ⟶ X) [Etale p] (eV : V ⟶ S) [Etale eV] (hcomm : p ≫ f = f' ≫ eV)
    {x' : X'} {x : X} (hx : p.base x' = x) (d : StandardNodalDiagram f' x') :
    StandardNodalDiagram f x :=
  haveI := d.etale_toSource
  haveI := d.etale_toBase
  { U := d.U
    V := d.V
    W := d.W
    toSource := d.toSource ≫ p
    toBase := d.toBase ≫ eV
    familyU := d.familyU
    familyW := d.familyW
    toModel := d.toModel
    classifyW := d.classifyW
    classifyV := d.classifyV
    pt := d.pt
    etale_toSource := inferInstance
    etale_toBase := inferInstance
    etale_toModel := d.etale_toModel
    pt_mem := (congrArg p.base d.pt_mem).trans hx
    comm_left := by rw [Category.assoc, hcomm, reassoc_of% d.comm_left]
    comm_model := d.comm_model
    isPullback_model := d.isPullback_model }

/-- **The diagram of Tag 0CBY is local on source and target.** A diagram for the restriction of
`f` to an open `U` of the source mapping into an open `V` of the target, at a point of `U`, is a
diagram for `f` at that point: the two inclusions are open immersions, hence étale.

This is the step "the question is local on `X` and `S`, hence we may assume `X` and `S` affine"
of the first proof of Tag 0CBY. -/
public def standardNodalDiagramOfResLE {X S : Scheme.{u}} {f : X ⟶ S} (V : S.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U)
    (d : StandardNodalDiagram (f.resLE V U e) ⟨x, hx⟩) :
    StandardNodalDiagram f x :=
  standardNodalDiagramOfEtale (f := f) (x' := ⟨x, hx⟩) (x := x) U.ι V.ι
    (Scheme.Hom.resLE_comp_ι f e).symm rfl d

/-- **The diagram of Tag 0CBY base-changes along an arbitrary morphism of bases.** Let
`f₀ : X₀ ⟶ S₀` and let `p : X ⟶ X₀`, `f : X ⟶ S` exhibit `f` as the base change of `f₀` along a
morphism `g : S ⟶ S₀`. Then the diagram of Tag 0CBY for `f₀` at a point `x₀` gives the diagram
for `f` at any point of `X` over `x₀`.

No hypothesis is placed on `g`: this is the step of the first proof of Tag 0CBY which passes
from a stage of a Noetherian approximation of the base back to the base, along a morphism which
is not étale. -/
public theorem nonempty_standardNodalDiagram_of_isPullback {X₀ X S₀ S : Scheme.{u}}
    {p : X ⟶ X₀} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : S ⟶ S₀} (hsq : IsPullback p f f₀ g)
    {x : X} {x₀ : X₀} (hx : p.base x = x₀) (d : StandardNodalDiagram f₀ x₀) :
    Nonempty (StandardNodalDiagram f x) := by
  -- the new étale neighbourhood of the base, and the new local model over it
  have hV : IsPullback (pullback.fst d.toBase g) (pullback.snd d.toBase g) d.toBase g :=
    IsPullback.of_hasPullback d.toBase g
  have hW : IsPullback (pullback.fst d.familyW (pullback.fst d.toBase g))
      (pullback.snd d.familyW (pullback.fst d.toBase g)) d.familyW
      (pullback.fst d.toBase g) :=
    IsPullback.of_hasPullback _ _
  -- the new étale neighbourhood of the source
  have hU : IsPullback (pullback.fst d.toSource p) (pullback.snd d.toSource p) d.toSource p :=
    IsPullback.of_hasPullback d.toSource p
  -- the new family over the new neighbourhood of the base
  have hfam : (pullback.fst d.toSource p ≫ d.familyU) ≫ d.toBase =
      (pullback.snd d.toSource p ≫ f) ≫ g := by
    rw [Category.assoc, ← d.comm_left, pullback.condition_assoc, hsq.w, Category.assoc]
  set familyU' := hV.lift (pullback.fst d.toSource p ≫ d.familyU)
    (pullback.snd d.toSource p ≫ f) hfam
  have hfamfst : familyU' ≫ pullback.fst d.toBase g =
      pullback.fst d.toSource p ≫ d.familyU := hV.lift_fst _ _ _
  have hfamsnd : familyU' ≫ pullback.snd d.toBase g =
      pullback.snd d.toSource p ≫ f := hV.lift_snd _ _ _
  -- the whole neighbourhood of the source is cartesian over the old one along the new base
  have hbig : IsPullback (pullback.fst d.toSource p) familyU' d.familyU
      (pullback.fst d.toBase g) :=
    IsPullback.of_bot' (d.comm_left ▸ hU.paste_vert hsq) hV
  -- the new morphism to the new local model
  have hmod : (pullback.fst d.toSource p ≫ d.toModel) ≫ d.familyW =
      familyU' ≫ pullback.fst d.toBase g := by
    rw [Category.assoc, d.comm_model, hfamfst]
  set toModel' := hW.lift (pullback.fst d.toSource p ≫ d.toModel) familyU' hmod
  have hmodsnd : toModel' ≫ pullback.snd d.familyW (pullback.fst d.toBase g) =
      familyU' := hW.lift_snd _ _ _
  have hmodsq : IsPullback (pullback.fst d.toSource p) toModel' d.toModel
      (pullback.fst d.familyW (pullback.fst d.toBase g)) :=
    IsPullback.of_bot' (by rw [d.comm_model]; exact hbig) hW
  -- the chosen point of the new neighbourhood of the source
  have hrange : Set.range (pullback.snd d.toSource p).base =
      p.base ⁻¹' Set.range d.toSource.base := by
    simpa using Scheme.image_preimage_eq_of_isPullback hU Set.univ
  obtain ⟨pt, hpt⟩ : x ∈ Set.range (pullback.snd d.toSource p).base := by
    rw [hrange]
    exact ⟨d.pt, by rw [d.pt_mem, hx]⟩
  exact ⟨{ U := pullback d.toSource p
           V := pullback d.toBase g
           W := pullback d.familyW (pullback.fst d.toBase g)
           toSource := pullback.snd d.toSource p
           toBase := pullback.snd d.toBase g
           familyU := familyU'
           familyW := pullback.snd d.familyW (pullback.fst d.toBase g)
           toModel := toModel'
           classifyW := pullback.fst d.familyW (pullback.fst d.toBase g) ≫ d.classifyW
           classifyV := pullback.fst d.toBase g ≫ d.classifyV
           pt := pt
           -- the three legs stay étale, being base changes of the old ones
           etale_toSource := MorphismProperty.of_isPullback hU d.etale_toSource
           etale_toBase := MorphismProperty.of_isPullback hV d.etale_toBase
           etale_toModel := MorphismProperty.of_isPullback hmodsq d.etale_toModel
           pt_mem := hpt
           comm_left := hfamsnd.symm
           comm_model := hmodsnd
           isPullback_model := hW.paste_horiz d.isPullback_model }⟩

end Stacks.NodalEtaleLocalStructure

end

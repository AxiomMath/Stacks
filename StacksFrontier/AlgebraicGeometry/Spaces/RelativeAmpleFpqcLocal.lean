module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleFpqcRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleTestSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative ampleness is fpqc local on the base (Stacks 0D3C)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓛` be an invertible
`𝒪_X`-module and let `{gᵢ : Yᵢ ⟶ Y}` be an fpqc covering. Let `fᵢ : Xᵢ ⟶ Yᵢ` be the base change
of `f` and `𝓛ᵢ` the pullback of `𝓛` to `Xᵢ`. Then `𝓛` is ample on `X/Y` if and only if each
`𝓛ᵢ` is ample on `Xᵢ/Yᵢ`.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_isRelativelyAmple_of_isFpqcCovering`:
  **Stacks 0D3C**.

## Proof

The forward implication is the base change stability of Stacks 0D33. For the converse, the
morphism `f` is quasi-compact and separated, because each `fᵢ` is (Stacks 0D34) and both
properties are fpqc local on the base (Stacks 041L, 0421). Relative ampleness may be tested on
the affine schemes `T` of the site over `Y` (Stacks 0D36,
`AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_affine_isAmpleOnBaseChange`), and for such a
`T` the fpqc condition supplies a finite covering of `T` by affine schemes `Tⱼ` at which the clause
of Stacks 0D36 holds
(`AlgebraicGeometry.Space.exists_affineFpqcRefinement_isAmpleOnBaseChange`). The base change
`X ×_Y T` is then a scheme (`AlgebraicGeometry.Space.exists_isPullback_of_affineFpqcFamily`), and
the pullback of `𝓛` to it is ample over `T` by the scheme case, Stacks 0D2P
(`AlgebraicGeometry.Space.exists_isRelativelyAmple_of_fpqcFamily`).

## References

* [Stacks Project, Tag 0D3C](https://stacks.math.columbia.edu/tag/0D3C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0D3C.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, `𝓛` an invertible
`𝒪_X`-module and `{gᵢ : Yᵢ ⟶ Y}` an fpqc covering, with base changes `fᵢ : Xᵢ ⟶ Yᵢ` of `f` and
pullbacks `𝓛ᵢ` of `𝓛` to `Xᵢ`. Then `𝓛` is ample on `X/Y` if and only if `𝓛ᵢ` is ample on
`Xᵢ/Yᵢ` for every `i`. -/
@[stacks 0D3C]
theorem isRelativelyAmple_iff_forall_isRelativelyAmple_of_isFpqcCovering
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {I : Type v}
    {Yᵢ Xᵢ : I → AlgebraicSpaces B S hS} {gᵢ : ∀ i, Yᵢ i ⟶ Y} {fᵢ : ∀ i, Xᵢ i ⟶ Yᵢ i}
    {pᵢ : ∀ i, Xᵢ i ⟶ X} (hsq : ∀ i, IsPullback (pᵢ i) (fᵢ i) f (gᵢ i))
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (hfpqc : IsFpqcCovering B S hS fun i => (gᵢ i).hom) :
    IsRelativelyAmple B S hS f L ↔
      ∀ i, IsRelativelyAmple B S hS (fᵢ i) ((modulePullback B S hS (pᵢ i)).obj L) := by
  refine ⟨fun hamp i => forall_isRelativelyAmple_baseChange_of_isRelativelyAmple hsq L hamp i,
    fun h => ?_⟩
  -- `f` is quasi-compact and separated, these being fpqc local on the base (041L, 0421)
  have := quasiCompact_isLocalAtTarget_fpqc.{u, v} B S hS
  have := separated_isLocalAtTarget_fpqc.{u, v} B S hS
  have key (P : MorphismProperty (AlgebraicSpaces B S hS))
      [P.IsLocalAtTarget (Topology.precoverage.{u, v} .fpqc B S hS)]
      (hP : ∀ i, P (fᵢ i)) : P f := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (K := Topology.precoverage.{u, v} .fpqc B S hS)
      (R := Presieve.ofArrows Yᵢ gᵢ) ⟨I, Yᵢ, gᵢ, rfl, Y.2, fun i => (Yᵢ i).2, hfpqc⟩
      fun {U g} _ hg => ?_
    obtain ⟨i⟩ := hg
    refine (MorphismProperty.cancel_left_of_respectsIso P (hsq i).isoPullback.hom _).mp ?_
    rw [(hsq i).isoPullback_hom_snd]
    exact hP i
  have hqc : IsQuasiCompact B S hS f.hom :=
    key (quasiCompactProperty B S hS) fun i => (h i).isQuasiCompact
  have hsep : IsSeparated B S hS f.hom := key (separatedProperty B S hS) fun i => (h i).isSeparated
  -- the clause of Stacks 0D36 at every affine scheme over `Y`
  refine (isRelativelyAmple_iff_forall_affine_isAmpleOnBaseChange f L hL).mpr
    fun T hT g => ?_
  obtain ⟨𝒰, hfin, hmem, hclause⟩ :=
    exists_affineFpqcRefinement_isAmpleOnBaseChange hsq L hfpqc h ⟨T, hT⟩ g
  have hmap : Presieve.map (BigAffineFppf.toScheme B S hS) 𝒰.presieve₀ =
      Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj (𝒰.X j)))
        (fun j => (BigFppfOver.toScheme B S hS).map
          ((BigAffineFppf.inclusion B S hS).map (𝒰.f j))) := by
    simp [PreZeroHypercover.presieve₀]
  refine ⟨exists_isPullback_of_affineFpqcFamily f L hL hqc hsep ⟨T, hT⟩ g 𝒰 hfin hmem hclause,
    fun U p q hsq' => ?_⟩
  exact exists_isRelativelyAmple_of_fpqcFamily f L hL g
    (fun j => (BigAffineFppf.inclusion B S hS).map (𝒰.f j)) (hmap ▸ hmem) hclause U p q hsq'

end AlgebraicGeometry.Space

end

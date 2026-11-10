module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of integral morphisms are closed in their fibres

Let `f : X ⟶ S` be an integral morphism of schemes. Every point of `X`, viewed as a point of the
scheme-theoretic fibre over its image in `S`, is closed in that fibre.

## Main results

* `AlgebraicGeometry.isClosed_singleton_asFiber_of_isIntegral` says that a point of the source
  of an integral morphism is closed in its fibre.

## Implementation notes

The point of the fibre is represented by `Scheme.Hom.asFiber`. Via `Scheme.Hom.fiberHomeo`,
this is the point in the topological fibre over its image. The fibre is affine over the residue
field, and the corresponding prime is maximal because an integral extension of a field reflects
maximality.

## References

* [Stacks Project, Tag 02NT](https://stacks.math.columbia.edu/tag/02NT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 02NT.** Every point of the source of an integral morphism is
closed in the fibre over its image. -/
@[stacks 02NT]
lemma isClosed_singleton_asFiber_of_isIntegral (f : X ⟶ S) [IsIntegralHom f] (x : X) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  let F := f.fiber (f x)
  let g := f.fiberToSpecResidueField (f x)
  have : IsIntegralHom g := by
    dsimp [g, Scheme.Hom.fiberToSpecResidueField]
    exact IsIntegralHom.instIsStableUnderBaseChangeScheme.of_isPullback
      (IsPullback.of_hasPullback _ _) inferInstance
  let p : PrimeSpectrum Γ(F, ⊤) := F.isoSpec.hom (f.asFiber x)
  rw [← show F.isoSpec.hom ⁻¹' {p} = {f.asFiber x} by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, p]
    exact F.isoSpec.hom.homeomorph.injective.eq_iff]
  refine ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 ?_).preimage
    F.isoSpec.hom.continuous
  let := ((Scheme.ΓSpecIso (S.residueField (f x))).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField (S.residueField (f x)))).toField
  apply @Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ _ _ _
    g.appTop.hom (isIntegral_appTop_of_universallyClosed g) p.asIdeal p.2
  rw [(Ideal.eq_bot_or_top _).resolve_right (p.2.comap g.appTop.hom).ne_top]
  exact Ideal.bot_isMaximal

end AlgebraicGeometry

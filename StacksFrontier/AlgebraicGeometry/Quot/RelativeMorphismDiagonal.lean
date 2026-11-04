module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace

/-!
# The diagonal of the relative morphism functor (Stacks 0DPM)

Let `B` be an algebraic space and `Y, X` algebraic spaces over `B` with `Y ⟶ B` flat, proper and of
finite presentation and `X ⟶ B` separated and of finite presentation. Stacks 0DPM asserts that the
diagonal of `Mor_B(Y, X) ⟶ B` is a closed immersion of finite presentation. The source deduces it
from the open immersion `Mor_B(Y, X) ⟶ Hilb_{Y ×_B X / B}` of Stacks 0D1B and Stacks 0DM6.

All that is used of the graph transformation is that it is a monomorphism over `B`: two relative
morphisms over a scheme `T` agree after a base change exactly when their graphs do
(`AlgebraicGeometry.Space.graphTransformation_injective`), so the equalizer locus of two relative
morphisms is that of their graphs, which is a closed subscheme of finite presentation by
`AlgebraicGeometry.Space.exists_equalizerLocus_hilbertPresheaf`, the ambient space `Y ×_B X` being
of finite presentation over `B`.

In this development `Y ⟶ B` is `z : Z ⟶ Q` and `X ⟶ B` is `x : X ⟶ Q`.

## Main results

* `AlgebraicGeometry.Space.exists_equalizerLocus_relativeHom`.
* `AlgebraicGeometry.Space.diagonal_relativeHomProjection`: **Stacks 0DPM.**

## References

* [Stacks Project, Tag 0DPM](https://stacks.math.columbia.edu/tag/0DPM)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0DM6](https://stacks.math.columbia.edu/tag/0DM6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- **The equalizer locus of two points of `Mor_B(Y, X)`.** Two `a`-valued relative morphisms over
the same point of `B` agree after restriction along `t : c ⟶ a` exactly when `t` factors through a
fixed closed immersion locally of finite presentation. -/
theorem exists_equalizerLocus_relativeHom (hsep : IsSeparated B S hS x)
    (hxfp : IsFinitePresentation B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (a : BigFppfOver B S hS) (p q : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op a))
    (hpq : (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (Opposite.op a) p =
      (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (Opposite.op a) q) :
    ∃ (b : BigFppfOver B S hS) (s : b ⟶ a), Mono s ∧
      closedImmersionFinitePresentation (B := B) (S := S) (hS := hS) s ∧
      ∀ (c : BigFppfOver B S hS) (t : c ⟶ a),
        (relativeHom B S hS Z X Q z x hZ hX hQ).map t.op p =
            (relativeHom B S hS Z X Q z x hZ hX hQ).map t.op q ↔
          ∃ r : c ⟶ b, r ≫ s = t := by
  let g := graphTransformation hZ hX hQ hsep hfp hflat hproper
  have hg : ∀ w : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op a),
      (hilbertPresheafToBase (graphAmbientMap B S hS z x hZ hX hQ)).app (Opposite.op a)
          (g.app (Opposite.op a) (ULift.up w)) =
        ULift.up ((relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (Opposite.op a) w) :=
    fun _ => rfl
  obtain ⟨b, s, hm, hs, hloc⟩ := exists_equalizerLocus_hilbertPresheaf
    (graphAmbientMap B S hS z x hZ hX hQ)
    (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp) a
    (g.app (Opposite.op a) (ULift.up p)) (g.app (Opposite.op a) (ULift.up q))
    (by rw [hg, hg, hpq])
  refine ⟨b, s, hm, hs, fun c t => ?_⟩
  have hn : ∀ w : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op a),
      g.app (Opposite.op c) (ULift.up ((relativeHom B S hS Z X Q z x hZ hX hQ).map t.op w)) =
        (hilbertPresheaf (graphAmbientMap B S hS z x hZ hX hQ)).map t.op
          (g.app (Opposite.op a) (ULift.up w)) :=
    fun w => types_congr_hom (g.naturality t.op) (ULift.up w)
  rw [← hloc c t, ← hn p, ← hn q]
  constructor
  · intro h
    rw [h]
  · intro h
    exact congrArg ULift.down
      (graphTransformation_injective hZ hX hQ hsep hfp hflat hproper c h)

/-- **Stacks 0DPM.** The diagonal of `Mor_B(Y, X) ⟶ B` is a closed immersion of finite
presentation, for `Y ⟶ B` flat, proper and of finite presentation and `X ⟶ B` separated and of
finite presentation: it is representable by closed immersions of schemes locally of finite
presentation. -/
@[stacks 0DPM]
theorem diagonal_relativeHomProjection (hsep : IsSeparated B S hS x)
    (hxfp : IsFinitePresentation B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z) :
    (closedImmersionFinitePresentation (B := B) (S := S) (hS := hS)).presheaf
      (pullback.diagonal (relativeHomProjection B S hS Z X Q z x hZ hX hQ)) :=
  MorphismProperty.presheaf_pullbackDiagonal_of_equalizerLoci _ _
    fun a p q hpq =>
      exists_equalizerLocus_relativeHom hZ hX hQ hsep hxfp hfp hflat hproper a p q hpq

/-- **Stacks 0DPN, the separation clause.** The morphism `Mor_B(Y, X) ⟶ B` is separated: its
diagonal is a closed immersion, by Stacks 0DPM. -/
theorem isSeparated_relativeHomProjection (hsep : IsSeparated B S hS x)
    (hxfp : IsFinitePresentation B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z) :
    IsSeparated B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) :=
  have h := diagonal_relativeHomProjection hZ hX hQ hsep hxfp hfp hflat hproper
  ⟨h.1, fun _ _ g fst snd hpb => (h.2 g fst snd hpb).1⟩

end AlgebraicGeometry.Space

end

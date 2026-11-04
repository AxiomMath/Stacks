module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Jacobson algebraic spaces

An algebraic space over `S` is *Jacobson* when it admits a surjective étale atlas by a
Jacobson scheme. The main result is that this property is inherited by any algebraic space
locally of finite type over a Jacobson algebraic space.

## Main results

* `AlgebraicGeometry.Space.exists_jacobson_atlas_of_isLocallyOfFiniteType`: an algebraic
  space locally of finite type over a Jacobson algebraic space is Jacobson.

## Implementation notes

The Jacobson condition is written out as the existence of a surjective étale atlas whose
scheme is a Jacobson topological space, which is the source's definition. It is not written
as the étale-local property of Stacks 03E6 attached to `JacobsonSpace`, because that
abbreviation takes the locality of its property as an instance argument, and locality of the
Jacobson property — Stacks 0368 — is not available in this development. Nothing below needs
it: the atlas of the source produced here is a fibre product with the atlas of the target,
so only *ascent* of the Jacobson property along a morphism locally of finite type is used,
which is Mathlib's `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`.

Neither space is assumed decent or locally Noetherian and no finiteness is asked of the
base: the atlas is obtained by base changing the atlas of the target along an atlas of the
source, and the resulting scheme is locally of finite type over the Jacobson scheme because
the composite of the atlas of the source with the given morphism is.

## References

* [Stacks Project, Tag 0BA3](https://stacks.math.columbia.edu/tag/0BA3)
* [Stacks Project, Tag 02J6](https://stacks.math.columbia.edu/tag/02J6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0BA3.** An algebraic space locally of finite type over a Jacobson algebraic
space is Jacobson: if the algebraic space `X` over `S` has a surjective étale atlas by a
Jacobson scheme and `f : Y ⟶ X` is locally of finite type, then so does `Y`. -/
@[stacks 0BA3, ega "IV 10.4.7" "Y Jacobson"]
theorem exists_jacobson_atlas_of_isLocallyOfFiniteType (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hJac : ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj V) := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, a, haS, haE, haJac⟩ := hJac
  obtain ⟨V, b, hbS, hbE⟩ := hY.exists_atlas
  let gf : yoneda.obj V ⟶ X := b ≫ f
  have hrep : yoneda.relativelyRepresentable gf :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).mp
      hX.diagonal_representable gf
  let W := hrep.pullback a
  let p := hrep.fst a
  let q := hrep.snd a
  have hpull := hrep.isPullback a
  let r : W ⟶ V := yoneda.preimage p
  have hr : yoneda.map r = p := yoneda.map_preimage p
  have key : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
      [P.IsStableUnderBaseChange], (MorphismProperty.inverseImage P T).presheaf a →
      (MorphismProperty.inverseImage P T).presheaf b →
      (MorphismProperty.inverseImage P T).presheaf (yoneda.map r ≫ b) := by
    intro P _ _ ha hb
    let : (MorphismProperty.inverseImage P T).IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    let : (MorphismProperty.inverseImage P T).IsStableUnderBaseChange := ⟨by
      intro A C C' D h k k' h' hsq hk
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (hsq.map T) hk⟩
    have hrP : P (T.map r) :=
      ha.property gf (yoneda.map q) r (by simpa [hr] using hpull.flip)
    exact MorphismProperty.comp_mem _ _ _
      ((MorphismProperty.relative_map_iff (F := yoneda)).2 hrP) hb
  let : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) := ⟨by
    intro A C D k l hk hl
    let : Surjective k := hk
    let : Surjective l := hl
    infer_instance⟩
  have hWS := key _ haS hbS
  have hWE := key _ haE hbE
  have hqLft : LocallyOfFiniteType (T.map q) := by
    apply hf W U (yoneda.map r ≫ b) a q hWE haE
    simpa [gf, Category.assoc, hr] using hpull.w.symm
  have hWJac : JacobsonSpace (T.obj W) := by
    let : JacobsonSpace (T.obj U) := haJac
    let : LocallyOfFiniteType (T.map q) := hqLft
    exact LocallyOfFiniteType.jacobsonSpace (T.map q)
  exact ⟨W, yoneda.map r ≫ b, hWS, hWE, hWJac⟩

end AlgebraicGeometry.Space

end

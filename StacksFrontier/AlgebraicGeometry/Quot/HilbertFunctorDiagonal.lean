module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealFiniteTypeOfQuotient

/-!
# The diagonal of the Hilbert functor (Stacks 0DM6)

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation. Stacks 0DM6 asserts that
the diagonal of `Hilb_{X/Y} ⟶ Y` is a closed immersion of finite presentation. The source's proof
is one line: `Hilb_{X/Y} = Quot_{𝒪_X/X/Y}` by Stacks 0D00, and Stacks 0DM2 applies, the structure
sheaf being of finite type.

Here the identification of Stacks 0D00 is
`AlgebraicGeometry.Space.exists_hilbertPresheafIso_quotSitePresheaf`, an isomorphism of presheaves
over `Y`, and the diagonal is transported through it at the level of equalizer loci: two families
over a scheme `T` agree after a base change `T' ⟶ T` exactly when their images in the Quot presheaf
do, the isomorphism being natural and bijective.

## Main results

* `AlgebraicGeometry.Space.exists_equalizerLocus_hilbertPresheaf`: the locus where two families
  agree is a closed subscheme of finite presentation.
* `AlgebraicGeometry.Space.diagonal_hilbertPresheafToBase`: **Stacks 0DM6.**

## References

* [Stacks Project, Tag 0DM6](https://stacks.math.columbia.edu/tag/0DM6)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0DM2](https://stacks.math.columbia.edu/tag/0DM2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The equalizer locus of two points of `Hilb_{X/Y}`.** For `f : X ⟶ Y` of finite presentation,
two `a`-valued points of the Hilbert presheaf over the same point of `Y` agree after restriction
along `t : c ⟶ a` exactly when `t` factors through a fixed closed immersion locally of finite
presentation. -/
theorem exists_equalizerLocus_hilbertPresheaf (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (a : BigFppfOver B S hS) (x y : (hilbertPresheaf f).obj (Opposite.op a))
    (hxy : (hilbertPresheafToBase f).app (Opposite.op a) x =
      (hilbertPresheafToBase f).app (Opposite.op a) y) :
    ∃ (b : BigFppfOver B S hS) (s : b ⟶ a), Mono s ∧
      closedImmersionFinitePresentation (B := B) (S := S) (hS := hS) s ∧
      ∀ (c : BigFppfOver B S hS) (t : c ⟶ a),
        (hilbertPresheaf f).map t.op x = (hilbertPresheaf f).map t.op y ↔
          ∃ r : c ⟶ b, r ≫ s = t := by
  obtain ⟨e, he⟩ := exists_hilbertPresheafIso_quotSitePresheaf f hf
  have hq : ∀ z : (hilbertPresheaf f).obj (Opposite.op a),
      (structureSheafQuotSituation f hf).quotSitePresheafToBase.app (Opposite.op a)
          (e.hom.app (Opposite.op a) z) = (hilbertPresheafToBase f).app (Opposite.op a) z := by
    intro z
    rw [← he]
    rfl
  obtain ⟨b, s, hm, hs, hloc⟩ :=
    (structureSheafQuotSituation f hf).exists_equalizerLocus_quotSitePresheaf
      closedImmersionFinitePresentation
      (fun s hs => mono_of_isClosedImmersion_toScheme_map s hs.1)
      (fun _ Z hZ hfp => presheaf_closedImmersionFinitePresentation_of_isClosedSubspace Z hZ
        (hfp (isFiniteTypeOnSite_unit_structureRingSheaf B S hS X)))
      a _ _ ((hq x).trans (hxy.trans (hq y).symm))
  refine ⟨b, s, hm, hs, fun c t => ?_⟩
  rw [← hloc c t, ← NatTrans.naturality_apply e.hom, ← NatTrans.naturality_apply e.hom]
  exact ⟨fun h => by rw [h], fun h => by simpa using congrArg (e.inv.app (Opposite.op c)) h⟩

/-- **Stacks 0DM6.** The diagonal of `Hilb_{X/Y} ⟶ Y` is a closed immersion of finite
presentation, for `f : X ⟶ Y` of finite presentation.

The Hilbert presheaf takes values in `Type (u + 1)`, closed subspaces being recorded as
subfunctors, so its diagonal is read through `CategoryTheory.uliftYoneda`: it is representable by
closed immersions of schemes locally of finite presentation. -/
@[stacks 0DM6]
theorem diagonal_hilbertPresheafToBase (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom) :
    (closedImmersionFinitePresentation (B := B) (S := S) (hS := hS)).relative uliftYoneda.{u + 1}
      (pullback.diagonal (hilbertPresheafToBase f)) :=
  MorphismProperty.relative_pullbackDiagonal_of_equalizerLoci _ _
    fun a x y hxy => exists_equalizerLocus_hilbertPresheaf f hf a x y hxy

end AlgebraicGeometry.Space

end

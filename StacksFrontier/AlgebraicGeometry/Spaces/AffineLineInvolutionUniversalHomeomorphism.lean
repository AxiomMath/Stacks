module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# The involution quotient of the affine line is a universal homeomorphism over the line

The example of Stacks 05Z6 exhibits, over a field in which `2` is invertible, two morphisms
`𝐀¹_k ⟶ X ⟶ 𝐀¹_k` with `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}`: the first is étale surjective, the
second is universally injective, and their composite is `x ↦ x²`, hence universally closed.
**This file supplies the concluding claim of the example: the second morphism `X ⟶ 𝐀¹_k` is a
universal homeomorphism.**

The three earlier assertions of the example are already in the library — the étale
presentation in `AlgebraicGeometry.AffineLineInvolution.presheafEtale_quotientChart` and
`AlgebraicGeometry.AffineLineInvolution.presheafSurjective_quotientChart`, universal
injectivity in `AlgebraicGeometry.AffineLineInvolution.universallyInjective_squaringMap`,
universal closedness of the composite in
`AlgebraicGeometry.Space.universallyClosed_toQuotientSheaf_comp_squaringMap`, and the closing
nonseparatedness assertion in
`AlgebraicGeometry.AffineLineInvolution.not_isSeparated_squaringMap`. What was missing is the
step the Stacks project takes in the proof of Stacks 05Z4: a morphism which is universally
injective, universally closed and surjective is a universal homeomorphism. That criterion is
proved here, together with the passage from universal closedness of the composite to universal
closedness of `X ⟶ 𝐀¹_k`.

## Main results

* `AlgebraicGeometry.Space.universalHomeomorphism_of_universallyInjective_of_universallyClosed`:
  a universally injective, universally closed and surjective morphism of algebraic spaces over
  `S` is a universal homeomorphism. This is the criterion used in the proof of Stacks 05Z4.
* `AlgebraicGeometry.Space.universallyClosed_of_comp_of_isSurjective`: if `c ≫ f` is
  universally closed and `c` is surjective, then `f` is universally closed.
* `AlgebraicGeometry.AffineLineInvolution.universalHomeomorphism_squaringMap`: the concluding
  claim of **Stacks 05Z6**, that `X ⟶ 𝐀¹_k` is a universal homeomorphism.

## Implementation notes

The criterion is read off the definitions: `AlgebraicGeometry.Space.UniversalHomeomorphism`,
`AlgebraicGeometry.Space.UniversallyClosed` and
`AlgebraicGeometry.Space.UniversallyInjective` all quantify over the same base changes, and a
map on points is automatically continuous (Stacks 03BX, clause (2),
`AlgebraicGeometry.Space.continuous_pointsMap`), so
`isHomeomorph_iff_continuous_isClosedMap_bijective` needs only injectivity, closedness and
surjectivity of each base change. Surjectivity of the
base changes is *not* an extra hypothesis: surjectivity of algebraic spaces is stable under
base change by Stacks 03MF, `AlgebraicGeometry.Space.isSurjective_pullback_fst`.

The descent of universal closedness along a surjection is the usual point-set argument: for a
continuous surjection `v` and a map `h` with `h ∘ v` closed, `h '' C` equals
`(h ∘ v) '' (v ⁻¹' C)`, which is closed. The base change of the composite `c ≫ f` is
identified with the composite of base changes by the pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, exactly as in
`AlgebraicGeometry.Space.universalHomeomorphism_comp`.

Surjectivity of the two morphisms out of the affine line is verified through local
surjectivity for the fppf topology, which suffices by
`AlgebraicGeometry.Space.surjective_pointsMap_of_isLocallySurjective`: the quotient projection
is locally surjective by construction of the quotient sheaf, and squaring the coordinate is
locally surjective by
`AlgebraicGeometry.AffineLineInvolution.affineLineSquare_points_locallySurjective`, which
adjoins a square root of the coordinate over an affine piece of a test object. The hypothesis
`(2 : k) ≠ 0` is the one under which the quotient `X` is constructed in Stacks 02Z1; it is not
an extra assumption on the conclusion.

## References

* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
* [Stacks Project, Tag 05Z4](https://stacks.math.columbia.edu/tag/05Z4)
* [Stacks Project, Tag 03MF](https://stacks.math.columbia.edu/tag/03MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Closed maps and continuous surjections -/

/-- A map whose composite after a continuous surjection is closed is itself closed: the image
of a closed set under it is the image of the preimage of that set under the composite. -/
private theorem isClosedMap_of_comp_of_surjective {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {v : α → β} {h : β → γ} (hv : Continuous v)
    (hvs : Function.Surjective v) (hc : IsClosedMap (h ∘ v)) : IsClosedMap h := by
  intro C hC
  rw [show h '' C = (h ∘ v) '' (v ⁻¹' C) by
    rw [Set.image_comp, Set.image_preimage_eq _ hvs]]
  exact hc _ (hC.preimage hv)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Universal closedness along a surjection -/

section Descent

variable {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If the composite `c ≫ f` of morphisms of algebraic spaces over `S` is universally closed
and `c` is surjective, then `f` is universally closed.

A base change of `c ≫ f` along `g : Z ⟶ Y` is, by the pasting isomorphism, the base change of
`c` along `Z ×_Y X ⟶ X` followed by the base change of `f` along `g`. The first of these is
surjective on points because surjectivity is stable under base change (Stacks 03MF), so the
second is closed as soon as the composite is. -/
theorem universallyClosed_of_comp_of_isSurjective (hW : IsAlgebraicSpace B S hS W)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (c : W ⟶ X) (f : X ⟶ Y)
    (hc : IsSurjective B S hS c) (hcf : UniversallyClosed B S hS (c ≫ f)) :
    UniversallyClosed B S hS f := by
  intro Z hZ g
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hX hY
  have hq : IsSurjective B S hS (pullback.fst (pullback.snd g f) c) :=
    isSurjective_pullback_fst B S hS hP hX hW (pullback.snd g f) c hc
  have hcl : IsClosedMap (pointsMap B S hS (pullback (pullback.snd g f) c)
      (pullback.fst (pullback.snd g f) c ≫ pullback.fst g f)) :=
    isClosedMap_pointsMap_of_comp_isIso B S hS (pullbackLeftPullbackSndIso g f c).hom
      (pullbackLeftPullbackSndIso_hom_fst g f c) (hcf Z hZ g)
  rw [pointsMap_comp] at hcl
  exact isClosedMap_of_comp_of_surjective
    (continuous_pointsMap B S hS (pullback.fst (pullback.snd g f) c)) hq hcl

end Descent

/-! ### The criterion for a universal homeomorphism -/

section Criterion

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A universally injective, universally closed and surjective morphism of algebraic spaces
over `S` is a universal homeomorphism.

This is the criterion the Stacks project uses in the proof of Stacks 05Z4. Each base change of
`f` is injective on points by universal injectivity, closed by universal closedness, surjective
because surjectivity is stable under base change (Stacks 03MF) and continuous by Stacks 03BX,
clause (2); a continuous closed bijection is a homeomorphism. -/
theorem universalHomeomorphism_of_universallyInjective_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hinj : UniversallyInjective B S hS f) (hcl : UniversallyClosed B S hS f)
    (hsurj : IsSurjective B S hS f) : UniversalHomeomorphism B S hS f := fun Z hZ g ↦
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨continuous_pointsMap B S hS (pullback.fst g f), hcl Z hZ g, hinj Z hZ g,
      isSurjective_pullback_fst B S hS hZ hY hX g f hsurj⟩

end Criterion

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-! ### Surjectivity of the two morphisms of the example -/

/-- The projection of the affine line onto the involution quotient is surjective on points: it
is locally surjective for the fppf topology, by construction of the quotient sheaf. -/
theorem isSurjective_toQuotientSheaf :
    Space.IsSurjective B (Spec (.of k)) hk
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)) :=
  Space.surjective_pointsMap_of_isLocallySurjective B (Spec (.of k)) hk _
    (Stacks.Groupoids.toQuotientSheaf_isLocallySurjective
      (BigFppfOver.topology B (Spec (.of k)) hk)
      (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k))

/-- The squaring map out of the involution quotient is surjective.

Its composite with the quotient projection is squaring the coordinate of the affine line, which
is locally surjective for the fppf topology, hence surjective on points; a composite can only
be surjective if its second factor is. -/
theorem isSurjective_squaringMap :
    Space.IsSurjective B (Spec (.of k)) hk (squaringMap k B hk) := by
  have hcomp : Function.Surjective (Space.pointsMap B (Spec (.of k)) hk _
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
        squaringMap k B hk)) := by
    rw [toQuotientSheaf_comp_squaringMap]
    exact Space.surjective_pointsMap_of_isLocallySurjective B (Spec (.of k)) hk _
      (affineLineSquare_points_locallySurjective k B hk)
  rw [Space.pointsMap_comp] at hcomp
  exact hcomp.of_comp

/-! ### The concluding claim of the example -/

/-- The squaring map out of the involution quotient of the affine line is universally closed.

Its composite with the quotient projection is universally closed
(`AlgebraicGeometry.Space.universallyClosed_toQuotientSheaf_comp_squaringMap`) and the quotient
projection is surjective, so this follows from
`AlgebraicGeometry.Space.universallyClosed_of_comp_of_isSurjective`. -/
theorem universallyClosed_squaringMap (hchar : (2 : k) ≠ 0) :
    Space.UniversallyClosed B (Spec (.of k)) hk (squaringMap k B hk) :=
  Space.universallyClosed_of_comp_of_isSurjective B (Spec (.of k)) hk
    (Space.isAlgebraicSpace_points_affineLine B k hk)
    (isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar)
    (Space.isAlgebraicSpace_points_affineLine B k hk) _ (squaringMap k B hk)
    (isSurjective_toQuotientSheaf k B hk)
    (Space.universallyClosed_toQuotientSheaf_comp_squaringMap B k hk)

/-- **Stacks 05Z6, the concluding claim.** Over a field in which `2` is invertible the squaring
map `X ⟶ 𝐀¹_k` out of the quotient `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` is a universal homeomorphism.

The morphism is universally injective (Stacks 05VS, part (4)), universally closed — because its
composite with the étale surjective chart `𝐀¹_k ⟶ X` is squaring the coordinate, which is
integral — and surjective, so the criterion
`AlgebraicGeometry.Space.universalHomeomorphism_of_universallyInjective_of_universallyClosed`
applies. Together with
`AlgebraicGeometry.AffineLineInvolution.not_isSeparated_squaringMap` this exhibits a universal
homeomorphism of algebraic spaces which is not separated, which is the point of the example. -/
theorem universalHomeomorphism_squaringMap (hchar : (2 : k) ≠ 0) :
    Space.UniversalHomeomorphism B (Spec (.of k)) hk (squaringMap k B hk) :=
  Space.universalHomeomorphism_of_universallyInjective_of_universallyClosed B (Spec (.of k)) hk
    (isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar)
    (Space.isAlgebraicSpace_points_affineLine B k hk)
    (universallyInjective_squaringMap k hchar B hk)
    (universallyClosed_squaringMap k B hk hchar)
    (isSurjective_squaringMap k B hk)

end AlgebraicGeometry.AffineLineInvolution

end

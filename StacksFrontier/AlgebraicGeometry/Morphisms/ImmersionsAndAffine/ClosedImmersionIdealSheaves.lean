module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Scheme theoretic unions and intersections of closed subschemes

Closed subschemes of a scheme `X` are the subschemes `I.subscheme` cut out by the quasi-coherent
sheaves of ideals `I : X.IdealSheafData`, ordered so that a larger ideal sheaf cuts out a smaller
subscheme. The scheme theoretic *union* of the subschemes cut out by `I` and `J` is the subscheme
cut out by `I ⊓ J`, and their scheme theoretic *intersection* is the one cut out by `I ⊔ J`.

Any inclusion `I ≤ J` of ideal sheaves induces a closed immersion `J.subscheme ⟶ I.subscheme`,
which is what makes both of those constructions subschemes of the subschemes they are built from:
applying it to `I ⊓ J ≤ I` and `I ⊓ J ≤ J` exhibits each of two closed subschemes as a closed
subscheme of their union, and applying it to `I ≤ I ⊔ J` and `J ≤ I ⊔ J` exhibits their
intersection as a closed subscheme of each. The intersection is moreover the fibre product of the
two subschemes over `X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_inclusion`: the morphism of
  subschemes induced by an inclusion of ideal sheaves is a closed immersion.
* `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subscheme_sup`: the subscheme cut out by
  `I ⊔ J` is the fibre product of the subschemes cut out by `I` and by `J` over the ambient
  scheme.

## Implementation notes

Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.inclusion` is defined by gluing, with no
closed-immersion instance attached; the instance is obtained here from
`AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion` and
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι`, which factors it through the
closed immersion `I.subschemeι`.

The cartesian square is stated with the two inclusions themselves rather than with an abstract
isomorphism onto a chosen pullback, so no choice of limit cone is involved. Its universal
property comes from `AlgebraicGeometry.IsClosedImmersion.lift`: a cone over the two subschemes
kills both `I` and `J`, hence kills `I ⊔ J`.

## References

* [Stacks Project, Tag 0C4I](https://stacks.math.columbia.edu/tag/0C4I)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **Stacks Project, Tag 0C4I** and **Tag 0C4J.** An inclusion `I ≤ J` of quasi-coherent
sheaves of ideals induces a closed immersion of the associated closed subschemes.

Applied to `I ≤ I ⊔ J` and `J ≤ I ⊔ J` this gives the closed immersions of the scheme theoretic
intersection into either of the two subschemes, and applied to `I ⊓ J ≤ I` and `I ⊓ J ≤ J` it
gives the closed immersions of either subscheme into their scheme theoretic union. -/
@[stacks 0C4I "closed immersions into the two factors",
  stacks 0C4J "union_closed_immersions"]
instance isClosedImmersion_inclusion {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J) :
    IsClosedImmersion (inclusion h) := by
  have : IsClosedImmersion (inclusion h ≫ I.subschemeι) := by
    rw [inclusion_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ I.subschemeι

/-- The subscheme cut out by the sum of two ideal sheaves is the fibre product of the
corresponding closed subschemes over the ambient scheme. -/
@[stacks 0C4I "cartesian intersection square"]
theorem isPullback_subscheme_sup (X : Scheme.{u}) (I J : X.IdealSheafData) :
    IsPullback (I.inclusion le_sup_left : (I ⊔ J).subscheme ⟶ I.subscheme)
      (J.inclusion le_sup_right : (I ⊔ J).subscheme ⟶ J.subscheme)
      I.subschemeι J.subschemeι := by
  let iI := inclusion (I := I) (J := I ⊔ J) le_sup_left
  let iJ := inclusion (I := J) (J := I ⊔ J) le_sup_right
  have hiI : iI ≫ I.subschemeι = (I ⊔ J).subschemeι := inclusion_subschemeι le_sup_left
  have hiJ : iJ ≫ J.subschemeι = (I ⊔ J).subschemeι := inclusion_subschemeι le_sup_right
  have hker (s : PullbackCone I.subschemeι J.subschemeι) :
      ((I ⊔ J).subschemeι).ker ≤ (s.fst ≫ I.subschemeι).ker := by
    rw [ker_subschemeι]
    refine sup_le ?_ ?_
    · simpa only [ker_subschemeι] using Scheme.Hom.le_ker_comp s.fst I.subschemeι
    · rw [s.condition]
      simpa only [ker_subschemeι] using Scheme.Hom.le_ker_comp s.snd J.subschemeι
  let lift (s : PullbackCone I.subschemeι J.subschemeι) : s.pt ⟶ (I ⊔ J).subscheme :=
    IsClosedImmersion.lift (I ⊔ J).subschemeι (s.fst ≫ I.subschemeι) (hker s)
  have hfacI (s : PullbackCone I.subschemeι J.subschemeι) : lift s ≫ iI = s.fst := by
    apply (cancel_mono I.subschemeι).1
    rw [Category.assoc, hiI, IsClosedImmersion.lift_fac]
  have hfacJ (s : PullbackCone I.subschemeι J.subschemeι) : lift s ≫ iJ = s.snd := by
    apply (cancel_mono J.subschemeι).1
    rw [Category.assoc, hiJ, IsClosedImmersion.lift_fac, s.condition]
  have huniq (s : PullbackCone I.subschemeι J.subschemeι) (m : s.pt ⟶ (I ⊔ J).subscheme)
      (hmI : m ≫ iI = s.fst) (hmJ : m ≫ iJ = s.snd) : m = lift s := by
    apply (cancel_mono (I ⊔ J).subschemeι).1
    simp only [← hiI, ← Category.assoc, hmI, hfacI]
  exact IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk (hiI.trans hiJ.symm) lift hfacI hfacJ huniq)

end AlgebraicGeometry.Scheme.IdealSheafData

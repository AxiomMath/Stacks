module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixSubstitution
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The `m`-th power of `GL₂` as an object of the big fppf site over a ring

The contraction step of [Stacks, Tag 0AEM] runs the action of `(GL_{2,k})^m` on `(ℙ¹_k)^m`
through [Stacks, Tag 0AEJ], which is a statement about algebraic spaces over a base contained in
a big fppf site. For that the group has to be an object of the site, and this file puts it there:
its coordinate ring is a localization of a polynomial ring on finitely many indeterminates over
`k`, so the two size bounds of [Stacks, Tag 000R] apply to it exactly as they do to the general
linear group scheme over the integers in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/Examples/GeneralLinear.lean`.

## Main definitions

* `AlgebraicGeometry.Space.generalLinearTwoPowerSiteObject`: `(GL₂)^m` over `Spec k`, as an
  object of the big fppf site over `Spec k`.

## Main results

* `AlgebraicGeometry.Space.contains_generalLinearTwoPowerCoordinateRing`: the spectrum of the
  coordinate ring of `(GL₂)^m` is small enough to belong to any big fppf site containing
  `Spec k`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [CommRing k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)

include hk in
/-- **The coordinate ring of `(GL₂)^m` has a small spectrum.** It is a localization of the
polynomial ring on the `4m` entries of the `m` generic matrices, which is of finite type over
`k`, so the spectrum belongs to every big fppf site that contains `Spec k`. -/
theorem contains_generalLinearTwoPowerCoordinateRing :
    B.Contains (Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m))) := by
  have hpoly :
      (Spec (CommRingCat.of (MvPolynomial (Fin m × Fin 2 × Fin 2) k))).size < B.cutoff :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      k (MvPolynomial (Fin m × Fin 2 × Fin 2) k) hk
  exact Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (Submonoid.powers (∏ i : Fin m, genericTwoPowerDeterminant k m i))
    (generalLinearTwoPowerCoordinateRing k m) hpoly

/-- **`(GL₂)^m` over `Spec k`, as an object of the big fppf site over `Spec k`**: the spectrum of
its coordinate ring, with the structure morphism of that ring as the morphism to the base. -/
def generalLinearTwoPowerSiteObject : BigFppfOver B (Spec (CommRingCat.of k)) hk :=
  siteObject B (Spec (CommRingCat.of k)) hk
    (contains_generalLinearTwoPowerCoordinateRing k B hk m)
    (Spec.map (generalLinearTwoPowerStructureMap k m))

/-- The underlying scheme of the site object of `(GL₂)^m` is the spectrum of its coordinate
ring. -/
theorem generalLinearTwoPowerSiteObject_left :
    (BigFppfOver.toScheme B (Spec (CommRingCat.of k)) hk).obj
        (generalLinearTwoPowerSiteObject k B hk m) =
      Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m)) :=
  rfl

/-- The structure morphism of the site object of `(GL₂)^m` is the one of its coordinate ring. -/
theorem generalLinearTwoPowerSiteObject_hom :
    B.inclusion.map (generalLinearTwoPowerSiteObject k B hk m).hom =
      Spec.map (generalLinearTwoPowerStructureMap k m) :=
  rfl

end AlgebraicGeometry.Space

end

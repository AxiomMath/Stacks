module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding
public import StacksFrontier.RingTheory.Branches.Completion

/-!
# The henselian local ring of a space and an abstract henselization of a chart stalk agree

Let `X` be a decent algebraic space over `S`, let `x` be a point of `|X|` and let `U` be an
elementary étale neighbourhood of `x`.  The henselian local ring `𝒪^h_{X, x}` of Stacks 0BGW is
a `CommRingCat.{u + 1}`, one universe above the Zariski local ring `𝒪_{U, u}` of the chart.  Any
henselization `R : Type u` of `𝒪_{U, u}` with residue field `κ(u)` is isomorphic to
`𝒪^h_{X, x}` as an `𝒪_{U, u}`-algebra.

## Main results

* `AlgebraicGeometry.Space.exists_algEquiv_henselianLocalRing`: an abstract henselization of the
  Zariski local ring of an elementary étale neighbourhood at its distinguished point is
  isomorphic, as an algebra over that local ring, to the henselian local ring of the space at
  the point.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_algEquiv_genericHenselianLocalRing` and
  `AlgebraicGeometry.Space.PrimeDivisor.exists_ringEquiv_genericHenselianLocalRing`: the same at
  the generic point of a prime divisor, read at its generic chart.

## References

* [Stacks Project, Tag 08HT](https://stacks.math.columbia.edu/tag/08HT)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) (hdec : IsDecentSpace B S hS X)

/-- The henselian local ring `𝒪^h_{X, x}` of a decent algebraic space is isomorphic, as an algebra
over the Zariski local ring `𝒪_{U, u}` of an elementary étale neighbourhood, to any henselization
`R : Type u` of `𝒪_{U, u}` with residue field `κ(u)`. -/
theorem exists_algEquiv_henselianLocalRing (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (R : Type u) [CommRing R] [IsLocalRing R]
    [Algebra (U.scheme.left.1.presheaf.stalk U.point) R]
    [IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
      (ResidueField (U.scheme.left.1.presheaf.stalk U.point)) R] :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hdec
    letI := stalkAlgebra B S hS X hX x hdec U
    Nonempty (R ≃ₐ[U.scheme.left.1.presheaf.stalk U.point]
      (henselianLocalRing B S hS X hX x hdec : Type (u + 1))) := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hdec
  let := stalkAlgebra B S hS X hX x hdec U
  let := henselianLocalRing_isHenselization B S hS X hX x hdec U
  exact exists_algEquiv_of_isHenselization_independentUniverses
    (U.scheme.left.1.presheaf.stalk U.point) R
    (henselianLocalRing B S hS X hX x hdec : Type (u + 1))
    (ResidueField (U.scheme.left.1.presheaf.stalk U.point))
    (ResidueField (U.scheme.left.1.presheaf.stalk U.point)) AlgEquiv.refl

variable {X}

/-- A henselization `R : Type u` of the Zariski local ring of the generic chart of a prime divisor
`Z` is isomorphic, as an algebra over that local ring, to
`𝒪^h_{X, ξ} = AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing`. -/
theorem PrimeDivisor.exists_algEquiv_genericHenselianLocalRing (Z : PrimeDivisor B S hS X)
    (R : Type u) [CommRing R] [IsLocalRing R]
    [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) R]
    [IsHenselization ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
      (ResidueField ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R] :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := stalkAlgebra B S hS X hX (Z.genericPoint B S hS X) hdec
      (Z.genericChart B S hS hX hdec)
    Nonempty (R ≃ₐ[(Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point]
      ↥(Z.genericHenselianLocalRing B S hS hX hdec)) :=
  exists_algEquiv_henselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    (Z.genericChart B S hS hX hdec) R

/-- A henselization `R : Type u` of the Zariski local ring of the generic chart of a prime divisor
`Z` is isomorphic as a ring to
`𝒪^h_{X, ξ} = AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing`. -/
theorem PrimeDivisor.exists_ringEquiv_genericHenselianLocalRing (Z : PrimeDivisor B S hS X)
    (R : Type u) [CommRing R] [IsLocalRing R]
    [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) R]
    [IsHenselization ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
      (ResidueField ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R] :
    Nonempty (R ≃+* ↥(Z.genericHenselianLocalRing B S hS hX hdec)) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := stalkAlgebra B S hS X hX (Z.genericPoint B S hS X) hdec
    (Z.genericChart B S hS hX hdec)
  exact (Z.exists_algEquiv_genericHenselianLocalRing B S hS hX hdec R).map AlgEquiv.toRingEquiv

end AlgebraicGeometry.Space

end

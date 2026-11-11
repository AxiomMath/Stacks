module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing
public import StacksFrontier.RingTheory.OrderOfVanishing.Henselization

/-!
# The order of vanishing along a prime divisor, compared with the order on a scheme chart

Let `X` be a decent algebraic space, let `Z ⊆ X` be a prime divisor with generic point `ξ`, and
let `(U, u) → (X, ξ)` be an elementary étale neighbourhood whose scheme is integral and locally
Noetherian and whose marked point has codimension one. The henselian local ring `𝒪^h_{X, ξ}` is
a henselization of `𝒪_{U, u}`, so the structure map carries nonzerodivisors to nonzerodivisors
and leaves the length of the quotient by a principal ideal unchanged. Hence it induces a map
`R(U) = Q(𝒪_{U, u}) → Q(𝒪^h_{X, ξ})`, and the order of vanishing along `Z` of the image of a
nonzero rational function of `U` is its order of vanishing at `u` in the sense of a scheme.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.functionFieldToTotalFractionRing` is the induced map
  from the function field of an étale scheme chart to the total ring of fractions of the
  henselian local ring at the generic point of a prime divisor.

## Main results

* `AlgebraicGeometry.Scheme.ord_mk'`: the order of vanishing of a fraction `a / b` of
  nonzerodivisors of a stalk of a locally Noetherian integral scheme at a point of codimension
  one is the difference of the lengths of the quotients by `(a)` and by `(b)`.
* `AlgebraicGeometry.Space.stalkToHenselianLocalRing_mem_nonZeroDivisors` and
  `AlgebraicGeometry.Space.ord_stalkToHenselianLocalRing`: the canonical map from the stalk of
  an elementary étale neighbourhood into the henselian local ring preserves nonzerodivisors and
  the order of vanishing.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing`: the two orders of
  vanishing agree on a chart.

## Implementation notes

The source hypothesis is that `Z` meets the schematic locus of `X`; its proof then shrinks `X`
to an integral Noetherian scheme and works there. The shrinking step is carried here as the
hypothesis of an elementary étale neighbourhood `U` of `ξ` which is integral, locally Noetherian
and of codimension one at its marked point: an open subspace of `X` which is a scheme and which
meets `Z` contains `ξ` and provides such a `U`, but the passage from a representable open
subspace to an elementary étale neighbourhood is not available in this development. Stated this
way the result applies to any étale scheme chart, not only to an open one.

The codimension hypothesis `coheight U.point = 1` is *not* a strengthening of the source's: it is
equivalent to the codimension-one condition on `ξ` in `|X|` that makes `Z` a prime divisor, since
the dimension of the local ring of `|X|` at a point is the Krull dimension of the local ring of
any étale chart above it (`AlgebraicGeometry.Space.localRingDimension_eq_of_chartPoint`) and that
dimension is the coheight by Stacks 02IZ. The direction a client needs is packaged as
`AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one`; the
purely topological equality of coheights along an étale morphism is
`AlgebraicGeometry.Space.coheight_pointsMap_eq`.

Cofilteredness of the category of elementary étale neighbourhoods of a point of an algebraic
space, which is Stacks 0BGV, is *not* a hypothesis of the comparison: it is
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isCofiltered_of_nonempty`, and the
neighbourhood `U` the comparison is stated at is itself the witness of the nonemptiness that
lemma asks for. The two lemmas about the map on stalks below do not need it at all.
Locality, Noetherianness and the dimension bound for `𝒪^h_{X, ξ}` are carried as
instance arguments, as they are for `AlgebraicGeometry.Space.PrimeDivisor.ord` itself; locality
is `AlgebraicGeometry.Space.henselianLocalRing_isLocalRing`, and at the generic point of a prime
divisor of a decent, locally Noetherian, integral algebraic space the other two are available
too, as `AlgebraicGeometry.Space.PrimeDivisor.isNoetherianRing_genericHenselianLocalRing` and
`AlgebraicGeometry.Space.PrimeDivisor.krullDimLE_genericHenselianLocalRing`.

The rational function is presented through the comparison map rather than through the embedding
`R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK, which is
`AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing`. The two are
identified in `StacksFrontier/AlgebraicGeometry/Spaces/OrderOfVanishingSchematicLocus.lean`, on the way
to the full statement of Stacks 0ENM,
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_schematicLocus`; what that needs is the
independence of the embedding of the affine elementary étale neighbourhood it is computed on, which
is `AlgebraicGeometry.Space.PrimeDivisor.neighborhoodTotalFractionRingToGeneric_pullback_eq`.

The scheme-level order of vanishing is `AlgebraicGeometry.Scheme.ord` of the ambient library,
which is Divisors, Definition 02RJ; no declaration in this repository carries `@[stacks 02RJ]`.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public section

open CategoryTheory Order
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-! ### The scheme-level order of vanishing as a difference of lengths -/

/-- The order of vanishing at a point `z` of codimension one of a fraction `a / b` of
nonzerodivisors of `𝒪_{X, z}` is `length(𝒪_{X, z}/a) - length(𝒪_{X, z}/b)`. -/
theorem Scheme.ord_mk' {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hz : coheight z = 1) (a b : (X.presheaf.stalk z)⁰) :
    X.ord (IsLocalization.mk' X.functionField (a : X.presheaf.stalk z) b) z =
      ((Ring.ord (X.presheaf.stalk z) (a : X.presheaf.stalk z)).toNat : ℤ) -
        ((Ring.ord (X.presheaf.stalk z) (b : X.presheaf.stalk z)).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz,
    show Scheme.ordHom z hz = Ring.ordFrac (X.presheaf.stalk z) from rfl, Ring.ordFrac_eq_div,
    Ring.ordMonoidWithZeroHom_eq_coe _ a.2 (ENat.natCast_toNat (Ring.ord_ne_top a.2)).symm,
    Ring.ordMonoidWithZeroHom_eq_coe _ b.2 (ENat.natCast_toNat (Ring.ord_ne_top b.2)).symm]
  simp [← WithZero.coe_div, ← ofAdd_sub]

namespace Space

/-! ### The henselization comparison at the generic point of a prime divisor -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))

/-- The canonical map from the stalk of an elementary étale neighbourhood of the generic point of
a prime divisor into the henselian local ring there carries nonzerodivisors to nonzerodivisors,
being the structure map of a henselization. -/
theorem stalkToHenselianLocalRing_mem_nonZeroDivisors
    {r : ↥(U.scheme.left.1.presheaf.stalk U.point)}
    (hr : r ∈ (↥(U.scheme.left.1.presheaf.stalk U.point))⁰) :
    stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U r ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ := by
  let := stalkAlgebra B S hS X hX (Z.genericPoint B S hS X) hdec U
  let := henselianLocalRing_isHenselization B S hS X hX (Z.genericPoint B S hS X) hdec U
  exact IsLocalRing.IsHenselization.algebraMap_mem_nonZeroDivisors
    (IsLocalRing.ResidueField ↥(U.scheme.left.1.presheaf.stalk U.point)) hr

/-- The length of the quotient by a principal ideal is unchanged by the canonical map from the
stalk of an elementary étale neighbourhood into the henselian local ring: that map is the
structure map of a henselization, which is flat and local with the maximal ideal extended. -/
theorem ord_stalkToHenselianLocalRing (r : U.scheme.left.1.presheaf.stalk U.point) :
    Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U r) =
      Ring.ord ↥(U.scheme.left.1.presheaf.stalk U.point) r := by
  let := stalkAlgebra B S hS X hX (Z.genericPoint B S hS X) hdec U
  let := henselianLocalRing_isHenselization B S hS X hX (Z.genericPoint B S hS X) hdec U
  exact IsLocalRing.IsHenselization.ord_algebraMap
    (IsLocalRing.ResidueField ↥(U.scheme.left.1.presheaf.stalk U.point)) r

/-! ### The comparison of the two orders of vanishing -/

variable [AlgebraicGeometry.IsIntegral U.scheme.left.1]

/-- The map from the function field of an integral elementary étale neighbourhood of the generic
point of a prime divisor to the total ring of fractions of the henselian local ring there,
induced by the canonical map on stalks. -/
noncomputable def PrimeDivisor.functionFieldToTotalFractionRing :
    ↥U.scheme.left.1.functionField →+* Z.genericTotalFractionRing B S hS hX hdec :=
  IsLocalization.map (T := (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰) _
    (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U)
    fun _ hr =>
      stalkToHenselianLocalRing_mem_nonZeroDivisors B S hS hX hdec Z U hr

/-- The induced map on fractions sends `a / b` to the fraction of the images of `a` and `b`. -/
theorem PrimeDivisor.functionFieldToTotalFractionRing_mk'
    (a : U.scheme.left.1.presheaf.stalk U.point)
    (b : (↥(U.scheme.left.1.presheaf.stalk U.point))⁰) :
    Z.functionFieldToTotalFractionRing B S hS hX hdec U (IsLocalization.mk' _ a b) =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U a)
        ⟨stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U b,
          stalkToHenselianLocalRing_mem_nonZeroDivisors B S hS hX hdec Z U b.2⟩ :=
  IsLocalization.map_mk' ..

variable [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsLocallyNoetherian U.scheme.left.1]

/-- **The comparison step of the proof of Stacks 0ENM, on a given neighbourhood.** The order
of vanishing along a prime divisor `Z` of the image of a nonzero
rational function `f` of an elementary étale neighbourhood `U` of the generic point of `Z` is
the order of vanishing of `f` at the marked point of `U` in the sense of Divisors, Definition
02RJ.

Both sides are a difference of lengths, and the canonical map from the stalk of `U` into the
henselian local ring is the structure map of a henselization, so it leaves those lengths
unchanged.

Stacks 0ENM itself, on the scheme representing the schematic locus, is
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_schematicLocus`. -/
theorem PrimeDivisor.ord_functionFieldToTotalFractionRing
    (hcoh : coheight U.point = 1) (f : ↥U.scheme.left.1.functionField) (hf : f ≠ 0) :
    Z.ord B S hS hX hdec (Z.functionFieldToTotalFractionRing B S hS hX hdec U f)
        ((isUnit_iff_ne_zero.mpr hf).map
          (Z.functionFieldToTotalFractionRing B S hS hX hdec U)) =
      U.scheme.left.1.ord f U.point := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective
    (nonZeroDivisors ↥(U.scheme.left.1.presheaf.stalk U.point)) f
  have ha : a ∈ (↥(U.scheme.left.1.presheaf.stalk U.point))⁰ :=
    mem_nonZeroDivisors_of_ne_zero fun h => hf (by simp [h])
  have hmem {r} := stalkToHenselianLocalRing_mem_nonZeroDivisors B S hS hX hdec Z U (r := r)
  have key := Z.functionFieldToTotalFractionRing_mk' B S hS hX hdec U a b
  rw [Z.ord_congr B S hS hX hdec _ (key ▸ (isUnit_iff_ne_zero.mpr hf).map
    (Z.functionFieldToTotalFractionRing B S hS hX hdec U)) key]
  refine ((Z.ord_mk' B S hS hX hdec ⟨_, hmem ha⟩ ⟨_, hmem b.2⟩ _).trans ?_).trans
    (Scheme.ord_mk' hcoh ⟨a, ha⟩ b).symm
  simp only [ord_stalkToHenselianLocalRing B S hS hX hdec Z U]

end Space

end AlgebraicGeometry

end

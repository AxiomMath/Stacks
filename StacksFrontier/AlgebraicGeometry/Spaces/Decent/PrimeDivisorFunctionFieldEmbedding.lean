module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisorClassGroup

/-!
# The function field of an integral algebraic space in the total ring of fractions at a prime
divisor

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`, let
`Z ⊂ X` be a prime divisor and let `ξ ∈ |Z|` be its generic point. We construct the canonical
injection `R(X) → Q(𝒪^h_{X, ξ})` of [Stacks, Tag 0ENK] from the function field of `X` into the
total ring of fractions of the henselian local ring at `ξ`, and package it, together with the
ring-theoretic conclusions of the same lemma, as
`AlgebraicGeometry.Space.GenericFractionEmbedding`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericChart`: the chosen affine elementary étale
  neighbourhood `(U, u)` of the generic point of a prime divisor.
* `AlgebraicGeometry.Space.PrimeDivisor.chartTotalFractionRingToGeneric`: the induced map
  `Q(Γ(U, 𝒪_U)) → Q(𝒪^h_{X, ξ})`.
* `AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing`: the
  canonical map `R(X) → Q(𝒪^h_{X, ξ})`.
* `AlgebraicGeometry.Space.genericFractionEmbedding`: the resulting
  `AlgebraicGeometry.Space.GenericFractionEmbedding`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.injective_rationalFunctionsToGenericTotalFractionRing`:
  the canonical map is injective.

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)

/-! ### The chart at the generic point of a prime divisor -/

/-- The chosen affine elementary étale neighbourhood of the generic point of a prime divisor. -/
def PrimeDivisor.genericChart :
    ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X) :=
  (exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec (Z.genericPoint B S hS X)).choose

/-- The chart at the generic point of a prime divisor is affine. -/
instance PrimeDivisor.isAffine_genericChart :
    IsAffine (Z.genericChart B S hS hX hdec).scheme.left.1 :=
  (exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec
    (Z.genericPoint B S hS X)).choose_spec.1

include hN in
/-- The scheme of an elementary étale neighbourhood of the generic point of a prime divisor is
locally Noetherian. -/
theorem PrimeDivisor.isLocallyNoetherian_chart
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)) :
    IsLocallyNoetherian U.scheme.left.1 :=
  (exists_atlas_iff_forall_etale B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T) hX).mp hN
    U.scheme U.toSpace
    ((isEtale_iff_presheaf_of_yoneda B S hS U.toSpace).1 U.etale_toSpace)

include hN in
/-- The chart at the generic point of a prime divisor is locally Noetherian. -/
theorem PrimeDivisor.isLocallyNoetherian_genericChart :
    IsLocallyNoetherian (Z.genericChart B S hS hX hdec).scheme.left.1 :=
  Z.isLocallyNoetherian_chart B S hS hX hN (Z.genericChart B S hS hX hdec)

include hInt in
/-- The scheme of an elementary étale neighbourhood of the generic point of a prime divisor is
reduced. -/
theorem PrimeDivisor.isReduced_chart
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)) :
    IsReduced U.scheme.left.1 :=
  (exists_atlas_iff_forall_etale B S hS X (fun T : Scheme.{u} => IsReduced T) hX).mp
    hInt.hasEtaleLocalProperty_isReduced U.scheme U.toSpace
    ((isEtale_iff_presheaf_of_yoneda B S hS U.toSpace).1 U.etale_toSpace)

include hInt in
/-- The chart at the generic point of a prime divisor is reduced. -/
theorem PrimeDivisor.isReduced_genericChart :
    IsReduced (Z.genericChart B S hS hX hdec).scheme.left.1 :=
  Z.isReduced_chart B S hS hX hInt (Z.genericChart B S hS hX hdec)

/-! ### From the chart to the henselian local ring -/

/-- The composite of the germ at the marked point of an elementary étale neighbourhood with the
canonical map of Stacks 0EMY into the henselian local ring at the generic point of a prime
divisor. -/
def PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)) :
    Γ(U.scheme.left.1, ⊤) →+* ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U).comp
    (U.scheme.left.1.presheaf.germ ⊤ U.point trivial).hom

/-- The composite of the germ at the marked point of the chart with the canonical map of Stacks
0EMY into the henselian local ring at the generic point of a prime divisor. -/
def PrimeDivisor.chartSectionsToGenericHenselianLocalRing :
    Γ((Z.genericChart B S hS hX hdec).scheme.left.1, ⊤) →+*
      ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec
    (Z.genericChart B S hS hX hdec)

/-- The composite map from the global sections of an elementary étale neighbourhood into the
henselian local ring at the generic point of a prime divisor carries nonzerodivisors to
nonzerodivisors. -/
theorem PrimeDivisor.nonZeroDivisors_le_comap_neighborhoodSectionsToGenericHenselianLocalRing
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1]
    (hCofiltered :
      IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))) :
    (Γ(U.scheme.left.1, ⊤))⁰ ≤
      ((↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰).comap
        (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U) :=
  fun _ ha => stalkToHenselianLocalRing_mem_nonZeroDivisors B S hS hX hdec Z hCofiltered U
    (U.scheme.left.1.nonZeroDivisors_le_comap_germ_top U.point ha)

/-- The composite map from the global sections of the chart into the henselian local ring at
the generic point of a prime divisor carries nonzerodivisors to nonzerodivisors. -/
theorem PrimeDivisor.nonZeroDivisors_le_comap_chartSectionsToGenericHenselianLocalRing
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (hCofiltered :
      IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))) :
    (Γ((Z.genericChart B S hS hX hdec).scheme.left.1, ⊤))⁰ ≤
      ((↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰).comap
        (Z.chartSectionsToGenericHenselianLocalRing B S hS hX hdec) :=
  Z.nonZeroDivisors_le_comap_neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec
    (Z.genericChart B S hS hX hdec) hCofiltered

/-- The map on total rings of fractions induced by the composite from the global sections of an
elementary étale neighbourhood into the henselian local ring at the generic point of a prime
divisor. -/
def PrimeDivisor.neighborhoodTotalFractionRingToGeneric
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1]
    (hCofiltered :
      IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))) :
    FractionRing Γ(U.scheme.left.1, ⊤) →+* Z.genericTotalFractionRing B S hS hX hdec :=
  IsLocalization.map (T := (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰) _
    (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U)
    (Z.nonZeroDivisors_le_comap_neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
      hCofiltered)

/-- The map on total rings of fractions induced by the composite from the global sections of
the chart into the henselian local ring at the generic point of a prime divisor. -/
def PrimeDivisor.chartTotalFractionRingToGeneric
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (hCofiltered :
      IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))) :
    FractionRing Γ((Z.genericChart B S hS hX hdec).scheme.left.1, ⊤) →+*
      Z.genericTotalFractionRing B S hS hX hdec :=
  Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec (Z.genericChart B S hS hX hdec)
    hCofiltered

/-! ### The canonical map of Stacks 0ENK -/

/-- The canonical map from the function field of a decent, locally Noetherian, integral algebraic
space into the total ring of fractions of the henselian local ring at the generic point of a
prime divisor: a rational function is pulled back to the spectrum of the total ring of fractions
of the global sections `A` of the chosen affine elementary étale neighbourhood `(U, u)` of the
generic point, and then pushed along `A → 𝒪_{U, u} → 𝒪^h_{X, ξ}`. -/
@[stacks 0ENK "the canonical map R(X) → Q(𝒪^h_{X, ξ}) from the function field into the total \
  ring of fractions of the henselian local ring at the generic point of a prime divisor"]
def PrimeDivisor.rationalFunctionsToGenericTotalFractionRing :
    rationalFunctions B S hS hX →+* Z.genericTotalFractionRing B S hS hX hdec := by
  have hCof := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX
    (Z.genericPoint B S hS X) ⟨Z.genericChart B S hS hX hdec⟩
  have _ : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have _ := Z.isLocallyNoetherian_genericChart B S hS hX hdec hN
  have _ := Z.isReduced_genericChart B S hS hX hdec hInt
  exact (Z.chartTotalFractionRingToGeneric B S hS hX hdec hCof).comp
    (rationalFunctionsToTotalFractionRing B S hS hX (Z.genericChart B S hS hX hdec).scheme
      (Z.genericChart B S hS hX hdec).toSpace (Z.genericChart B S hS hX hdec).etale_toSpace)

/-- The canonical map from the function field of a decent, locally Noetherian, integral algebraic
space into the total ring of fractions of the henselian local ring at the generic point of a
prime divisor is injective. -/
@[stacks 0ENK "injectivity of the canonical map R(X) → Q(𝒪^h_{X, ξ}), the function field being \
  a field and the total ring of fractions nontrivial"]
theorem PrimeDivisor.injective_rationalFunctionsToGenericTotalFractionRing :
    Function.Injective
      (Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN) := by
  have _ : Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Z.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  let _ := (isField_rationalFunctions B S hS hX hInt).toField
  exact RingHom.injective _

/-! ### The data of Stacks 0ENK at every prime divisor -/

/-- At every prime divisor of a decent, locally Noetherian, integral algebraic space: the
henselian local ring at the generic point of the prime divisor is a nontrivial Noetherian local
ring of dimension at most one, and the function field embeds in its total ring of fractions. -/
@[stacks 0ENK "the conclusions of the lemma assembled at every prime divisor, as the data the \
  order of vanishing along a prime divisor is defined from"]
def genericFractionEmbedding : GenericFractionEmbedding B S hS hX hdec where
  nontrivial Z := Z.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  isNoetherianRing Z := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  krullDimLE Z := Z.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  emb Z := Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN
  injective_emb Z := Z.injective_rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN

end AlgebraicGeometry.Space

end

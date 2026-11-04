module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentSectionOrderAdditivity

/-!
# The order of vanishing of a flat pullback, summed over the irreducible components

Let `Y` be an algebraic space, good over the base of Situation 0EDT, let `f : Y ⟶ T` be a
flat morphism to a good integral algebraic space `T`, let `g ∈ R(T)^*` and let `Z` be a prime
divisor of `Y` with generic point `ξ`.  Write `A = 𝒪^h_{Y, ξ}` for the henselian local ring of
Stacks 0ENK there and `V` for the generic chart of `Z`.  Then the order of vanishing at `ξ` of
the reading of `g` on `V` is

  `ord_A(reading of g at ξ) = ∑_i m_{Y_i, Y} · ord_{Z_i}(g ∘ f|_{Y_i})`,

the sum running over the irreducible components `Y_i` of `|Y|` through `ξ` with `m_{Y_i, Y}` the
multiplicity of Stacks 0EE9 and `Z_i` a prime divisor of `Y_i` whose generic point lies over `ξ`.
This is the coefficient at one prime divisor of the cycle identity of Stacks 0EQA and Stacks
0EQQ.

## Main definitions

* `PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat`: the reading of a rational
  function of `T`, pulled back along a flat `f : Y ⟶ T`, at the generic point of a prime
  divisor of `Y`.

## Main results

* `pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace_of_isFlat`: the
  restriction of a flat morphism to an irreducible component of the source is dominant.
* `PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_eq_mk'_neighborhoodSections`: the
  embedding of Stacks 0ENK as a fraction of the images of two global sections of an affine chart
  of the prime divisor's generic point under the canonical map of Stacks 0EMY.
* `PrimeDivisor.ord_eq_sub_natCast_ord_neighborhoodSections`: the order of vanishing of a
  rational function as a difference of two orders of vanishing in the henselian local ring.
* `exists_natCast_ord_sub_eq_finsum_components_mul_ordRationalFunction`: the identity displayed
  above.

## Implementation notes

No tag is claimed.  The identity proved here is the coefficient at one prime divisor of the
cycle identity of Stacks 0EQA and Stacks 0EQQ; the cycle identity itself needs in addition the
left-hand coefficient read as a flat-pullback coefficient and the right-hand sum read as a
pushforward of cycles, neither of which is done here.

## References

* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Dominance of the restriction of a flat morphism to an irreducible component -/

/-- **The restriction of a flat morphism to an irreducible component of its source is
dominant.**  In Situation 0EDT let `f : X ⟶ T` be a flat morphism of good algebraic spaces over
`B`, let `T` be integral and let `W ⊆ X` be an integral closed subspace whose set of points is
an irreducible component of `|X|`.  Then `f|_W : W ⟶ T` carries the generic point of `W` to the
generic point of `T`; this is what makes the pullback `g ∘ f|_W` of a rational function defined
(Morphisms of Spaces, Section 0EML).

The image of the generic point of `W` is a generic point of `|T|`, hence *the* generic point,
`|T|` being Kolmogorov by Stacks 03K3.

**No `@[stacks]` attribute is registered**: this is the dominance clause of Stacks 0EP5, not
the full tag. -/
theorem pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace_of_isFlat
    (D : BaseSpaceDimensionSituation.{u})
    {X T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sT : T ⟶ D.space) (hT : D.IsGood sT)
    {f : X ⟶ T} (hflat : IsFlat D.site D.base D.base_mem f)
    (hintT : IsIntegralSpace D.site D.base D.base_mem T)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWcomp : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    pointsMap D.site D.base D.base_mem W.subspace.toFunctor (W.subspace.ι ≫ f)
        (genericPoint D.site D.base D.base_mem W.isClosedSubspace.1 W.isIntegralSpace) =
      genericPoint D.site D.base D.base_mem hT.1 hintT := by
  have hQS : QuasiSober (points D.site D.base D.base_mem T) := quasiSober_points_of_isGood D sT hT
  have hT0 : T0Space (points D.site D.base D.base_mem T) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hT.1
      (D.isDecentSpace_of_isGood sT hT)
  have hirrT : IrreducibleSpace (points D.site D.base D.base_mem T) := hintT.2.2
  have hcomp := GeneralizingMap.mem_irreducibleComponents_closure_singleton
    (FlatPreimage.generalizingMap_pointsMap_of_isFlat D.site D.base D.base_mem hX.1 hT.1
      (D.isDecentSpace_of_isGood sT hT) hflat)
    (continuous_pointsMap D.site D.base D.base_mem f) hWcomp
    (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1)
  have huniv : IsGenericPoint (pointsMap D.site D.base D.base_mem X f
        (W.ambientGenericPoint D.site D.base D.base_mem))
      (Set.univ : Set (points D.site D.base D.base_mem T)) :=
    Set.eq_univ_of_univ_subset
      (hcomp.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
  rw [show pointsMap D.site D.base D.base_mem W.subspace.toFunctor (W.subspace.ι ≫ f)
        (genericPoint D.site D.base D.base_mem W.isClosedSubspace.1 W.isIntegralSpace) =
      pointsMap D.site D.base D.base_mem X f
        (W.ambientGenericPoint D.site D.base D.base_mem) from
    congrFun (pointsMap_comp D.site D.base D.base_mem W.subspace.toFunctor
      W.subspace.ι f) _]
  exact huniv.eq (isGenericPoint_genericPoint D.site D.base D.base_mem hT.1 hintT)

/-! ### The embedding of Stacks 0ENK as a fraction -/

/-- The numerator of a unit of a total ring of fractions is a nonzerodivisor. -/
private theorem mem_nonZeroDivisors_of_isUnit_mk' {A : Type*} [CommRing A] {K : Type*}
    [CommRing K] [Algebra A K] [IsFractionRing A K] (a : A) (b : A⁰)
    (hu : IsUnit (IsLocalization.mk' K a b)) : a ∈ A⁰ :=
  Stacks.Chow.mem_nonZeroDivisors_of_isUnit_algebraMap (Q := K)
    (by rw [← IsLocalization.mk'_spec K a b]; exact hu.mul (IsLocalization.map_units K b))

section Reading

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (Z : PrimeDivisor B S hS X)

/-- **The embedding of Stacks 0ENK as a fraction of the images of two global sections of a
chart, at the canonical map of Stacks 0EMY.** Let `X` be a decent, locally Noetherian, integral
algebraic space with a prime divisor `Z` of generic point `ξ`, let `U` be an affine elementary
étale neighborhood of `ξ` and let `a`, `b` be global sections of `𝒪_U` with `b` a
nonzerodivisor.  If the reading of a rational function `r` of `X` on `U` is the fraction `a / b`,
then

  `emb_X(r) = σ_U a / σ_U b`   in `Q(𝒪^h_{X, ξ})`,

`σ_U : Γ(U, 𝒪_U) → 𝒪^h_{X, ξ}` being the canonical map of Stacks 0EMY on global sections. -/
theorem PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_eq_mk'_neighborhoodSections
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] [IsReduced U.scheme.left.1] [IsLocallyNoetherian U.scheme.left.1]
    (hCof : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)))
    (a : Γ(U.scheme.left.1, ⊤)) (b : (Γ(U.scheme.left.1, ⊤))⁰)
    (r : rationalFunctions B S hS hX)
    (hr : rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace U.etale_toSpace r =
      IsLocalization.mk' (FractionRing Γ(U.scheme.left.1, ⊤)) a b)
    (hb : Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
        (b : Γ(U.scheme.left.1, ⊤)) ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰) :
    Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN r =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a) ⟨_, hb⟩ := by
  rw [← Z.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX hdec hInt hN U hCof r, hr,
    PrimeDivisor.neighborhoodTotalFractionRingToGeneric, IsLocalization.map_mk']

/-- **The order of vanishing of a rational function along a prime divisor, as a difference of
two orders of vanishing in the henselian local ring.** Let `X` be a decent, locally Noetherian,
integral algebraic space with a prime divisor `Z` of generic point `ξ`, let `U` be an affine
elementary étale neighborhood of `ξ`, and let the reading of a rational function `r` of `X` on
`U` be the fraction `a / b` of global sections of `𝒪_U`, with `b` a nonzerodivisor.  If `r` is a
unit of the total ring of fractions, then

  `ord_Z(r) = ord_{𝒪^h_{X, ξ}}(σ_U a) - ord_{𝒪^h_{X, ξ}}(σ_U b)`,

`σ_U` being the canonical map of Stacks 0EMY on global sections and `ord_Z` the order of
vanishing of Stacks 0ENL. -/
theorem PrimeDivisor.ord_eq_sub_natCast_ord_neighborhoodSections
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] [IsReduced U.scheme.left.1] [IsLocallyNoetherian U.scheme.left.1]
    (hCof : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)))
    (a : Γ(U.scheme.left.1, ⊤)) (b : (Γ(U.scheme.left.1, ⊤))⁰)
    (r : rationalFunctions B S hS hX)
    (hr : rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace U.etale_toSpace r =
      IsLocalization.mk' (FractionRing Γ(U.scheme.left.1, ⊤)) a b) :
    letI := Z.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
    letI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    letI := Z.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
    ∀ hu : IsUnit (Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN r),
      Z.ord B S hS hX hdec
          (Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN r) hu =
        ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
            (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a)).toNat : ℤ) -
          ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
            (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
              (b : Γ(U.scheme.left.1, ⊤)))).toNat : ℤ) := by
  let := Z.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  let := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  let := Z.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  intro hu
  have hbnz : Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
      (b : Γ(U.scheme.left.1, ⊤)) ∈ (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ :=
    Z.nonZeroDivisors_le_comap_neighborhoodSectionsToGenericHenselianLocalRing B S hS
      hX hdec U hCof b.2
  have heq := Z.rationalFunctionsToGenericTotalFractionRing_eq_mk'_neighborhoodSections B S hS hX
    hdec hInt hN U hCof a b r hr hbnz
  have hanz : Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ :=
    mem_nonZeroDivisors_of_isUnit_mk' (K := Z.genericTotalFractionRing B S hS hX hdec) _
      ⟨_, hbnz⟩ (heq ▸ hu)
  rw [Z.ord_congr B S hS hX hdec hu (heq ▸ hu) heq]
  exact Z.ord_mk' B S hS hX hdec ⟨_, hanz⟩ ⟨_, hbnz⟩ _

end Reading

/-! ### The reading at a prime divisor of a rational function pulled back along a flat morphism -/

section FlatReading

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y)
    (hYN : HasEtaleLocalProperty B S hS Y (fun W : Scheme.{u} => IsLocallyNoetherian W))
    (hT : IsAlgebraicSpace B S hS T) (hintT : IsIntegralSpace B S hS T)
    (Z : PrimeDivisor B S hS Y)

/-- **The reading at the generic point of a prime divisor of a rational function pulled back
along a flat morphism.** Let `f : Y ⟶ T` be a flat morphism of algebraic spaces with `T`
integral, and let `Z` be a prime divisor of a decent, locally Noetherian `Y` with generic point
`ξ`; `Y` is not assumed integral.  A rational function of `T` is read on the generic chart `V`
of `Z`, which is flat over `T` by composition, and the resulting fraction of global sections of
`𝒪_V` is pushed into `Q(𝒪^h_{Y, ξ})` along the map on total rings of fractions induced by the
canonical map of Stacks 0EMY.  The cofilteredness that map needs is Stacks 0BGV in the form
`ElementaryEtaleNeighborhood.isCofiltered_of_nonempty`, the generic chart itself witnessing
nonemptiness. -/
def PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat (f : Y ⟶ T)
    (hf : IsFlat B S hS f) :
    rationalFunctions B S hS hT →+* Z.genericTotalFractionRing B S hS hY hYdec :=
  letI := Z.isLocallyNoetherian_genericChart B S hS hY hYdec hYN
  letI : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hY hYdec) :=
    henselianLocalRing_isLocalRing B S hS Y hY (Z.genericPoint B S hS Y) hYdec
  (Z.chartTotalFractionRingToGeneric B S hS hY hYdec
      (ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS Y hY
        (Z.genericPoint B S hS Y) ⟨Z.genericChart B S hS hY hYdec⟩)).comp
    (rationalFunctionsToTotalFractionRingOfFlat B S hS hT hintT
      (Z.genericChart B S hS hY hYdec).scheme
      ((Z.genericChart B S hS hY hYdec).toSpace ≫ f)
      (isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS
          (Z.genericChart B S hS hY hYdec).scheme) hY hT
        (Z.genericChart B S hS hY hYdec).toSpace f
        (isFlat_of_isEtale B S hS (Z.genericChart B S hS hY hYdec).etale_toSpace) hf))

/-- **The reading of a rational function at the generic point of a prime divisor, as a fraction
of the images of two global sections of the generic chart.** If `s / t` presents the reading of
`g` on the generic chart `V` of `Z`, flat over `T`, then the reading of `g` at `ξ` is
`σ_V s / σ_V t`, `σ_V` being the canonical map of Stacks 0EMY on global sections of `V`. -/
theorem PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat_eq_mk' (f : Y ⟶ T)
    (hf : IsFlat B S hS f) (g : rationalFunctions B S hS hT)
    (s : Γ((Z.genericChart B S hS hY hYdec).scheme.left.1, ⊤))
    (t : (Γ((Z.genericChart B S hS hY hYdec).scheme.left.1, ⊤))⁰)
    (hst : letI := Z.isLocallyNoetherian_genericChart B S hS hY hYdec hYN
      IsLocalization.mk' (FractionRing Γ((Z.genericChart B S hS hY hYdec).scheme.left.1, ⊤)) s t =
        rationalFunctionsToTotalFractionRingOfFlat B S hS hT hintT
          (Z.genericChart B S hS hY hYdec).scheme
          ((Z.genericChart B S hS hY hYdec).toSpace ≫ f)
          (isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS
              (Z.genericChart B S hS hY hYdec).scheme) hY hT
            (Z.genericChart B S hS hY hYdec).toSpace f
            (isFlat_of_isEtale B S hS (Z.genericChart B S hS hY hYdec).etale_toSpace) hf) g)
    (ht : Z.chartSectionsToGenericHenselianLocalRing B S hS hY hYdec
        (t : Γ((Z.genericChart B S hS hY hYdec).scheme.left.1, ⊤)) ∈
      (↥(Z.genericHenselianLocalRing B S hS hY hYdec))⁰) :
    Z.rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hY hYdec hYN hT hintT f hf g =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hY hYdec)
        (Z.chartSectionsToGenericHenselianLocalRing B S hS hY hYdec s) ⟨_, ht⟩ := by
  let := Z.isLocallyNoetherian_genericChart B S hS hY hYdec hYN
  let : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hY hYdec) :=
    henselianLocalRing_isLocalRing B S hS Y hY (Z.genericPoint B S hS Y) hYdec
  rw [PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat, RingHom.comp_apply, ← hst,
    PrimeDivisor.chartTotalFractionRingToGeneric,
    PrimeDivisor.neighborhoodTotalFractionRingToGeneric, IsLocalization.map_mk']
  rfl

end FlatReading

/-! ### The same numerator and denominator read on every irreducible component -/

section ComponentReading

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) {y : points B S hS Y}
    (V : ElementaryEtaleNeighborhood B S hS Y hY y) [IsAffine V.scheme.left.1]
    [IsLocallyNoetherian V.scheme.left.1]
    (hT : IsAlgebraicSpace B S hS T) (hintT : IsIntegralSpace B S hS T)

include hY hYdec in
/-- **The reading on an irreducible component of a rational function pulled back along a flat
morphism, at the canonical map of Stacks 0EMY.** Let `V` be an affine, locally Noetherian
elementary étale neighborhood of a point of a decent algebraic space `Y`, let `f : Y ⟶ T` be a
morphism to an integral `T` with `V ⟶ Y ⟶ T` flat, and let `s / t` present the reading of a
rational function `g` of `T` on `V`. Let `W ⊆ Y` be an integral closed subspace whose set of
points is an irreducible component of `|Y|`, let `Z'` be a prime divisor of `W` and let
`j : U ⟶ V` be a morphism of charts over the inclusion `W ⟶ Y`, with `U` an affine elementary
étale neighborhood of the generic point of `Z'`. Then

  `emb_W(g ∘ f|_W) = σ_U (j^♯ s) / σ_U (j^♯ t)`   in `Q(𝒪^h_{W, ξ'})`,

`σ_U` being the canonical map of Stacks 0EMY on global sections of `U`.

The numerator and the denominator do not depend on the component: `s` and `t` present the
reading of `g` on `V` alone.  That is what
`exists_natCast_ord_sub_eq_finsum_components_mul_sections` needs of them — it takes two global
sections of one chart and reads them on every component — and it is why this statement takes
them as arguments rather than producing them. -/
theorem rationalFunctionsToGenericTotalFractionRing_rationalFunctionMap_eq_mk'_neighborhoodSections_of_isFlat
    (f : Y ⟶ T) (hcVf : IsFlat B S hS (V.toSpace ≫ f)) (g : rationalFunctions B S hS hT)
    (s : Γ(V.scheme.left.1, ⊤)) (t : (Γ(V.scheme.left.1, ⊤))⁰)
    (hst : IsLocalization.mk' (FractionRing Γ(V.scheme.left.1, ⊤)) s t =
      rationalFunctionsToTotalFractionRingOfFlat B S hS hT hintT V.scheme (V.toSpace ≫ f) hcVf g)
    (W : IntegralClosedSubspace B S hS Y)
    (hWcomp : subspacePointSet B S hS Y W.subspace ∈ irreducibleComponents (points B S hS Y))
    (hWN : HasEtaleLocalProperty B S hS W.subspace.toFunctor
      (fun P : Scheme.{u} => IsLocallyNoetherian P))
    (Z' : PrimeDivisor B S hS W.subspace.toFunctor)
    (hgen : pointsMap B S hS W.subspace.toFunctor (W.subspace.ι ≫ f)
        (_root_.AlgebraicGeometry.Space.genericPoint B S hS W.isClosedSubspace.1
          W.isIntegralSpace) =
      _root_.AlgebraicGeometry.Space.genericPoint B S hS hT hintT)
    (U : ElementaryEtaleNeighborhood B S hS W.subspace.toFunctor W.isClosedSubspace.1
      (Z'.genericPoint B S hS W.subspace.toFunctor))
    (hUaff : IsAffine U.scheme.left.1) (j : U.scheme ⟶ V.scheme)
    (hsq : yoneda.map j ≫ V.toSpace = U.toSpace ≫ W.subspace.ι)
    (ht : Z'.neighborhoodSectionsToGenericHenselianLocalRing B S hS W.isClosedSubspace.1
        W.isIntegralSpace.isDecentSpace U
        ((j.left.1.appTop).hom (t : Γ(V.scheme.left.1, ⊤))) ∈
      (↥(Z'.genericHenselianLocalRing B S hS W.isClosedSubspace.1
        W.isIntegralSpace.isDecentSpace))⁰) :
    Z'.rationalFunctionsToGenericTotalFractionRing B S hS W.isClosedSubspace.1
        W.isIntegralSpace.isDecentSpace W.isIntegralSpace hWN
        (rationalFunctionMap B S hS W.isClosedSubspace.1 hT W.isIntegralSpace hintT
          (W.subspace.ι ≫ f) hgen g) =
      IsLocalization.mk' (Z'.genericTotalFractionRing B S hS W.isClosedSubspace.1
          W.isIntegralSpace.isDecentSpace)
        (Z'.neighborhoodSectionsToGenericHenselianLocalRing B S hS W.isClosedSubspace.1
          W.isIntegralSpace.isDecentSpace U ((j.left.1.appTop).hom s)) ⟨_, ht⟩ := by
  let := hUaff
  let := Z'.isReduced_chart B S hS W.isClosedSubspace.1 W.isIntegralSpace U
  let := Z'.isLocallyNoetherian_chart B S hS W.isClosedSubspace.1 hWN U
  let : IsLocalRing ↥(Z'.genericHenselianLocalRing B S hS W.isClosedSubspace.1
      W.isIntegralSpace.isDecentSpace) :=
    henselianLocalRing_isLocalRing B S hS W.subspace.toFunctor W.isClosedSubspace.1
      (Z'.genericPoint B S hS W.subspace.toFunctor) W.isIntegralSpace.isDecentSpace
  have hnzd := nonZeroDivisors_le_comap_chartGlobalSectionsRestrict_of_irreducibleComponent
    B S hS hY hYdec W hWcomp U.toSpace U.etale_toSpace V.toSpace V.etale_toSpace j hsq
  have hr := rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_of_eq
    B S hS W.isClosedSubspace.1 hT W.isIntegralSpace hintT (W.subspace.ι ≫ f) hgen U.toSpace
    U.etale_toSpace (V.toSpace ≫ f) hcVf j (by rw [← Category.assoc, hsq, Category.assoc]) hnzd
    g s t (hnzd t.2) hst
  exact Z'.rationalFunctionsToGenericTotalFractionRing_eq_mk'_neighborhoodSections B S hS
    W.isClosedSubspace.1 W.isIntegralSpace.isDecentSpace W.isIntegralSpace hWN U
    (ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS W.subspace.toFunctor
      W.isClosedSubspace.1 (Z'.genericPoint B S hS W.subspace.toFunctor) ⟨U⟩)
    ((j.left.1.appTop).hom s)
    ⟨(j.left.1.appTop).hom (t : Γ(V.scheme.left.1, ⊤)), hnzd t.2⟩ _ hr ht

end ComponentReading

/-! ### The identity of Stacks 0EQA and Stacks 0EQQ at one prime divisor -/

section Components

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (sY : Y ⟶ D.space) (hYg : D.IsGood sY)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    (Z : PrimeDivisor D.site D.base D.base_mem Y)
    {T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sT : T ⟶ D.space) (hTg : D.IsGood sT)
    (hintT : IsIntegralSpace D.site D.base D.base_mem T)

/-- The set of points of the subspace cutting out an irreducible component of `|Y|` through the
generic point of a prime divisor is an irreducible component of `|Y|`. -/
theorem PrimeDivisor.subspacePointSet_genericComponentSubspace_mem_irreducibleComponents
    (i : Z.genericComponentIndex D Y hY hYdec) :
    subspacePointSet D.site D.base D.base_mem Y
        (Z.genericComponentSubspace D Y hY hYdec i).subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem Y) :=
  (subspacePointSet_integralClosedSubspaceOfComponent D.site D.base D.base_mem hY hYdec
    i.1) ▸ i.1.2

include hY hYg hYdec in
/-- **The component clause of Stacks 0EQA and Stacks 0EQQ, at one prime divisor.** In
Situation 0EDT let `Y` be an algebraic space which is good over the base, let `f : Y ⟶ T` be
a flat morphism to a good *integral* algebraic space `T`, let `g ∈ R(T)^*` and let `Z` be a
prime divisor of `Y` with generic point `ξ`.  Assume every irreducible component of `|Y|`
through `ξ` has δ-dimension `dim_δ(Z) + 1`.  Write `A = 𝒪^h_{Y, ξ}` for the henselian local ring
of Stacks 0ENK there.  Then there are nonzerodivisors `a`, `b` of `A` presenting the reading of
`g` at `ξ`, and, for each irreducible component `Y_i` of `|Y|` through `ξ`, a prime divisor `Z_i`
of `Y_i` whose generic point lies over `ξ`, such that

  `ord_A(a) - ord_A(b) = ∑_i m_{Y_i, Y} · ord_{Z_i}(g ∘ f|_{Y_i})`,

`m_{Y_i, Y}` being the multiplicity of Stacks 0EE9 of the `i`-th component.  The left-hand side
is the difference-of-lengths formula of Stacks 0ENL evaluated at the reading of `g` at `ξ`, so it
does not depend on the presentation; `Y` is not assumed integral.

This is the coefficient at `Z` of the cycle identity

  `f^* div_T(g) = ∑_i m_{Y_i, Y} (Y_i → Y)_* div_{Y_i}(g ∘ f|_{Y_i})`

of Stacks 0EQA and Stacks 0EQQ.  **No tag is claimed**: reading the left-hand side as the
coefficient of a flat pullback of cycles and the right-hand side as the coefficient of a
pushforward of cycles is not done here.

Each component's difference of orders of vanishing is converted by
`ordRationalFunction_eq_length_sub_length`, the defining formula of Stacks 0ENL.  Going through
`ordRationalFunction` rather than through `PrimeDivisor.ord` is what avoids having to supply
`Nontrivial`, `IsNoetherianRing` and `Ring.KrullDimLE 1` for each component's henselian local
ring inside the existential that produces that component's prime divisor.

The δ-dimension hypothesis is the one input not discharged.  It is what produces the prime
divisors `Z_i`: `ξ` has codimension one in `|Y|`, but its codimension inside a single component
is a δ-dimension count, and is `0` rather than `1` for a component of which `ξ` is itself the
generic point.  In the application it follows from Stacks 0EP5, which is not assumed here. -/
theorem exists_natCast_ord_sub_eq_finsum_components_mul_ordRationalFunction
    (f : Y ⟶ T) (hf : IsFlat D.site D.base D.base_mem f)
    (hdim : ∀ W : irreducibleComponents (points D.site D.base D.base_mem Y),
      Z.genericPoint D.site D.base D.base_mem Y ∈
          (W : Set (points D.site D.base D.base_mem Y)) →
        deltaDimension D sY
            (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY hYdec W) =
          deltaDimension D sY (Z.toIntegralClosedSubspace D.site D.base D.base_mem) + 1)
    (g : (rationalFunctions D.site D.base D.base_mem hTg.1)ˣ) :
    ∃ (a b : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))⁰)
        (Zc : ∀ i : Z.genericComponentIndex D Y hY hYdec,
          PrimeDivisor D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor)
        (_ : ∀ i, pointsMap D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.ι
            ((Zc i).genericPoint D.site D.base D.base_mem
              (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor) =
          Z.genericPoint D.site D.base D.base_mem Y),
      IsLocalization.mk' (Z.genericTotalFractionRing D.site D.base D.base_mem hY hYdec)
            (a : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)) b =
          Z.rationalFunctionsToGenericTotalFractionRingOfFlat D.site D.base D.base_mem hY hYdec
            (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hYg) hTg.1 hintT f hf
            (g : rationalFunctions D.site D.base D.base_mem hTg.1) ∧
        ((Ring.ord ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
              (a : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY
                hYdec))).toNat : ℤ) -
            ((Ring.ord ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
              (b : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY
                hYdec))).toNat : ℤ) =
          ∑ᶠ i : Z.genericComponentIndex D Y hY hYdec,
            irreducibleComponentMultiplicity D Y hY hYdec i.1 *
              ordRationalFunction D.site D.base D.base_mem
                (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
                (Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace
                (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D
                  ((Z.genericComponentSubspace D Y hY hYdec i).subspace.ι ≫ sY)
                  (isGood_integralClosedSubspace D sY hYg
                    (Z.genericComponentSubspace D Y hY hYdec i)))
                (Units.map (rationalFunctionMap D.site D.base D.base_mem
                    (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1 hTg.1
                    (Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace hintT
                    ((Z.genericComponentSubspace D Y hY hYdec i).subspace.ι ≫ f)
                    (pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace_of_isFlat
                      D sY hYg sT hTg hf hintT (Z.genericComponentSubspace D Y hY hYdec i)
                      (Z.subspacePointSet_genericComponentSubspace_mem_irreducibleComponents D Y
                        hY hYdec i))).toMonoidHom g)
                (Zc i) := by
  classical
  have hYN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hYg
  let : IsLocalRing ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) :=
    henselianLocalRing_isLocalRing D.site D.base D.base_mem Y hY
      (Z.genericPoint D.site D.base D.base_mem Y) hYdec
  let := Z.isLocallyNoetherian_genericChart D.site D.base D.base_mem hY hYdec hYN
  have hCof := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty D.site D.base D.base_mem
    Y hY (Z.genericPoint D.site D.base D.base_mem Y)
    ⟨Z.genericChart D.site D.base D.base_mem hY hYdec⟩
  have hcVf : IsFlat D.site D.base D.base_mem
      ((Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace ≫ f) :=
    isFlat_comp D.site D.base D.base_mem (isAlgebraicSpace_yoneda D.site D.base D.base_mem
        (Z.genericChart D.site D.base D.base_mem hY hYdec).scheme) hY hTg.1
      (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace f
      (isFlat_of_isEtale D.site D.base D.base_mem
        (Z.genericChart D.site D.base D.base_mem hY hYdec).etale_toSpace) hf
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective
    (Γ((Z.genericChart D.site D.base D.base_mem hY hYdec).scheme.left.1, ⊤))⁰
    (rationalFunctionsToTotalFractionRingOfFlat D.site D.base D.base_mem hTg.1 hintT
      (Z.genericChart D.site D.base D.base_mem hY hYdec).scheme
      ((Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace ≫ f) hcVf
      (g : rationalFunctions D.site D.base D.base_mem hTg.1))
  have ht : Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY hYdec
      (t : Γ((Z.genericChart D.site D.base D.base_mem hY hYdec).scheme.left.1, ⊤)) ∈
      (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))⁰ :=
    Z.nonZeroDivisors_le_comap_chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem
      hY hYdec hCof t.2
  have heqA := Z.rationalFunctionsToGenericTotalFractionRingOfFlat_eq_mk' D.site D.base
    D.base_mem hY hYdec hYN hTg.1 hintT f hf (g : rationalFunctions D.site D.base D.base_mem
      hTg.1) s t hst ht
  have hs : Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY hYdec s ∈
      (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))⁰ :=
    mem_nonZeroDivisors_of_isUnit_mk'
      (K := Z.genericTotalFractionRing D.site D.base D.base_mem hY hYdec) _ ⟨_, ht⟩
      (heqA ▸ g.isUnit.map (Z.rationalFunctionsToGenericTotalFractionRingOfFlat D.site D.base
        D.base_mem hY hYdec hYN hTg.1 hintT f hf))
  obtain ⟨Zc, hZc, U, j, hj, hsurj, hsq, haff, hnzs, hnzt, hadd⟩ :=
    exists_natCast_ord_sub_eq_finsum_components_mul_sections D Y hY sY hYg hYdec Z hdim s
      (t : Γ((Z.genericChart D.site D.base D.base_mem hY hYdec).scheme.left.1, ⊤)) hs ht
  have hmem := Z.subspacePointSet_genericComponentSubspace_mem_irreducibleComponents D Y hY hYdec
  have hWN := fun i => hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D
    ((Z.genericComponentSubspace D Y hY hYdec i).subspace.ι ≫ sY)
    (isGood_integralClosedSubspace D sY hYg (Z.genericComponentSubspace D Y hY hYdec i))
  have hgen := fun i =>
    pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace_of_isFlat D sY hYg sT
      hTg hf hintT (Z.genericComponentSubspace D Y hY hYdec i) (hmem i)
  refine ⟨⟨_, hs⟩, ⟨_, ht⟩, Zc, hZc, heqA.symm, hadd.trans (finsum_congr fun i => ?_)⟩
  refine congrArg (fun k : ℤ => irreducibleComponentMultiplicity D Y hY hYdec i.1 * k) ?_
  refine (ordRationalFunction_eq_length_sub_length D.site D.base D.base_mem
    (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
    (Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace (hWN i) _
    (Zc i) ⟨_, hnzs i⟩ ⟨_, hnzt i⟩ ?_).symm
  exact rationalFunctionsToGenericTotalFractionRing_rationalFunctionMap_eq_mk'_neighborhoodSections_of_isFlat
    D.site D.base D.base_mem hY hYdec (Z.genericChart D.site D.base D.base_mem hY hYdec)
    hTg.1 hintT f hcVf (g : rationalFunctions D.site D.base D.base_mem hTg.1) s t hst
    (Z.genericComponentSubspace D Y hY hYdec i) (hmem i) (hWN i) (Zc i) (hgen i)
    (U i) (haff i) (j i) (hsq i) (hnzt i)

end Components

end AlgebraicGeometry.Space

end

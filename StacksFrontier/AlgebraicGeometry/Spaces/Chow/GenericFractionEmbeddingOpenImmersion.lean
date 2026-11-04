module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.HubComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.DominantGenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# The embedding of Stacks 0ENK along an open immersion

Let `A` and `C` be decent, locally Noetherian, integral algebraic spaces over a scheme `S`, let
`Z ⊂ A` and `Z' ⊂ C` be prime divisors and let `ξ`, `ξ'` be their generic points. Stacks 0ENK
gives the two canonical embeddings
`R(A) → Q(𝒪^h_{A, ξ})` and `R(C) → Q(𝒪^h_{C, ξ'})`
of the function fields into the total rings of fractions of the henselian local rings at the
generic points. The source uses, without saying so, that these embeddings are compatible with
open immersions: if `m : A ⟶ C` is an open immersion carrying `ξ` to `ξ'`, the two embeddings
agree once the function fields and the henselian local rings are identified. Consequently the
order of vanishing along `Z` of the restriction of a rational function of `C` is its order of
vanishing along `Z'`. This file proves both. An isomorphism is an open immersion, so the
isomorphism case is included.

The proof rests on one observation. Both embeddings can be computed on *any* affine elementary
étale neighbourhood of the generic point, by the chart independence of Stacks 0ENK
(`AlgebraicGeometry.Space.PrimeDivisor.neighborhoodTotalFractionRingToGeneric_pullback_eq`). An
elementary étale neighbourhood `(U, u)` of `ξ` in `A` becomes one of `ξ'` in `C` by composing its
chart with `m`, keeping the *same* pointed scheme. So both embeddings may be computed on the one
ring `Q(Γ(U, 𝒪_U))`, and the comparison reduces to two facts about that ring:

* *the henselian local rings are identified as `𝒪_{U, u}`-algebras.* Both are henselizations
  of the stalk `𝒪_{U, u}` (Stacks 0EMY), and two henselizations of one local ring are
  isomorphic as algebras over it;
* *the identification of the function fields reads the same in the chart.* The extension
  `AlgebraicGeometry.Space.rationalFunctionMap` of function fields, induced by a morphism that
  carries the generic point to the generic point, is the composition of a partial map with the
  morphism. So its reading on a chart of the source is the reading of the original on the chart
  composed with the morphism.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.ofPointEq`: an elementary étale
  neighbourhood of a point, read as one of an equal point.
* `AlgebraicGeometry.Space.PartialMap.preimageOfMapGenericPoint`: the pullback of a partial
  map along a morphism of integral algebraic spaces that carries the generic point to the
  generic point.
* `AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIsOpenImmersion`: the identification
  `R(A) ≃ R(C)` of function fields along an open immersion `A ⟶ C` of integral algebraic
  spaces, inverse to the restriction of rational functions.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_eq_of_chart`:
  the comparison of the two embeddings of Stacks 0ENK on a common chart.
* `AlgebraicGeometry.Space.toRationalMap_preimageOfMapGenericPoint` and
  `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_comp`: the
  extension of function fields is the pullback of partial maps, and is read on a chart through
  composition with the morphism.
* `AlgebraicGeometry.Space.pointsMap_genericPoint_of_isOpenImmersion`: an open immersion of
  integral algebraic spaces carries the generic point to the generic point.
* `Space.PrimeDivisor.exists_rationalFunctionsToGenericTotalFractionRing_of_isOpenImmersion`:
  **the naturality of Stacks 0ENK along an open immersion.**
* `AlgebraicGeometry.Space.genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion`:
  **the order of vanishing is unchanged by an open immersion.**

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
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

/-! ### Elementary étale neighbourhoods of equal points -/

/-- An elementary étale neighbourhood of a point `x`, read as an elementary étale neighbourhood
of a point `y` equal to `x`: the same pointed scheme and the same chart. -/
def ElementaryEtaleNeighborhood.ofPointEq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {x y : points B S hS F}
    (N : ElementaryEtaleNeighborhood B S hS F hF x) (h : x = y) :
    ElementaryEtaleNeighborhood B S hS F hF y where
  scheme := N.scheme
  point := N.point
  residueField_contained := N.residueField_contained
  toSpace := N.toSpace
  etale_toSpace := N.etale_toSpace
  map_point := N.map_point.trans h
  mono_residueField := N.mono_residueField

/-! ### The two embeddings of Stacks 0ENK on a common chart -/

section CommonChart

variable {A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hC : IsAlgebraicSpace B S hS C)
    (hAdec : IsDecentSpace B S hS A) (hCdec : IsDecentSpace B S hS C)

/-- Two ring homomorphisms out of a fraction ring that agree on the base ring agree everywhere. -/
private theorem eq_of_comp_algebraMap_eq {R K L G : Type*} [CommRing R] [CommRing K] [CommRing L]
    [Algebra R K] [IsFractionRing R K] [FunLike G K L] [RingHomClass G K L] (j : K →+* L) (k : G)
    (h : ∀ a : R, j (algebraMap R K a) = k (algebraMap R K a)) (x : K) : j x = k x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext R⁰ (j := j) (k := (k : K →+* L))
    (RingHom.ext h)) x

/-- The maps on total rings of fractions from two affine elementary étale neighbourhoods into the
total rings of fractions of the henselian local rings agree, once the global sections of the two
neighbourhoods and the two henselian local rings are identified compatibly. -/
theorem PrimeDivisor.ringEquivOfRingEquiv_neighborhoodTotalFractionRingToGeneric
    (Z : PrimeDivisor B S hS A) (Z' : PrimeDivisor B S hS C)
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hA hAdec)]
    [IsLocalRing ↥(Z'.genericHenselianLocalRing B S hS hC hCdec)]
    (U : ElementaryEtaleNeighborhood B S hS A hA (Z.genericPoint B S hS A))
    (V : ElementaryEtaleNeighborhood B S hS C hC (Z'.genericPoint B S hS C))
    [IsAffine U.scheme.left.1] [IsAffine V.scheme.left.1]
    (hCofA : IsCofiltered (ElementaryEtaleNeighborhood B S hS A hA (Z.genericPoint B S hS A)))
    (hCofC : IsCofiltered (ElementaryEtaleNeighborhood B S hS C hC (Z'.genericPoint B S hS C)))
    (σ : Γ(U.scheme.left.1, ⊤) ≃+* Γ(V.scheme.left.1, ⊤))
    (ψ : ↥(Z.genericHenselianLocalRing B S hS hA hAdec) ≃+*
      ↥(Z'.genericHenselianLocalRing B S hS hC hCdec))
    (hψ : ∀ a : Γ(U.scheme.left.1, ⊤),
      ψ (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hA hAdec U a) =
        Z'.neighborhoodSectionsToGenericHenselianLocalRing B S hS hC hCdec V (σ a))
    (x : FractionRing Γ(U.scheme.left.1, ⊤)) :
    (IsFractionRing.ringEquivOfRingEquiv ψ :
        Z.genericTotalFractionRing B S hS hA hAdec ≃+*
          Z'.genericTotalFractionRing B S hS hC hCdec)
        (Z.neighborhoodTotalFractionRingToGeneric B S hS hA hAdec U hCofA x) =
      Z'.neighborhoodTotalFractionRingToGeneric B S hS hC hCdec V hCofC
        ((IsFractionRing.ringEquivOfRingEquiv σ :
          FractionRing Γ(U.scheme.left.1, ⊤) ≃+* FractionRing Γ(V.scheme.left.1, ⊤)) x) := by
  refine eq_of_comp_algebraMap_eq (R := Γ(U.scheme.left.1, ⊤))
    (((IsFractionRing.ringEquivOfRingEquiv ψ :
      Z.genericTotalFractionRing B S hS hA hAdec ≃+* Z'.genericTotalFractionRing B S hS hC hCdec) :
        _ →+* _).comp (Z.neighborhoodTotalFractionRingToGeneric B S hS hA hAdec U hCofA))
    ((Z'.neighborhoodTotalFractionRingToGeneric B S hS hC hCdec V hCofC).comp
      ((IsFractionRing.ringEquivOfRingEquiv σ :
        FractionRing Γ(U.scheme.left.1, ⊤) ≃+* FractionRing Γ(V.scheme.left.1, ⊤)) : _ →+* _))
    (fun a => ?_) x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    PrimeDivisor.neighborhoodTotalFractionRingToGeneric, IsLocalization.map_eq,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, hψ]

variable (hAint : IsIntegralSpace B S hS A) (hCint : IsIntegralSpace B S hS C)
    (hAN : HasEtaleLocalProperty B S hS A (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hCN : HasEtaleLocalProperty B S hS C (fun T : Scheme.{u} => IsLocallyNoetherian T))

/-- **The two embeddings of Stacks 0ENK agree on a common chart.** Let `(U, u)` and `(V, v)` be
affine elementary étale neighbourhoods of the generic points of prime divisors `Z ⊂ A` and
`Z' ⊂ C`, let `σ` identify their global sections and `ψ` the two henselian local rings,
compatibly with the maps from global sections, and let `e : R(A) → R(C)` be read in the two
charts compatibly with `σ`. Then the canonical embedding of `e g` is the image under `ψ` of the
canonical embedding of `g`: both are computed on the given charts, by the chart independence of
Stacks 0ENK. -/
theorem PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_eq_of_chart
    (Z : PrimeDivisor B S hS A) (Z' : PrimeDivisor B S hS C)
    (U : ElementaryEtaleNeighborhood B S hS A hA (Z.genericPoint B S hS A))
    (V : ElementaryEtaleNeighborhood B S hS C hC (Z'.genericPoint B S hS C))
    [IsAffine U.scheme.left.1] [IsReduced U.scheme.left.1] [IsLocallyNoetherian U.scheme.left.1]
    [IsAffine V.scheme.left.1] [IsReduced V.scheme.left.1] [IsLocallyNoetherian V.scheme.left.1]
    (σ : Γ(U.scheme.left.1, ⊤) ≃+* Γ(V.scheme.left.1, ⊤))
    (ψ : ↥(Z.genericHenselianLocalRing B S hS hA hAdec) ≃+*
      ↥(Z'.genericHenselianLocalRing B S hS hC hCdec))
    (hψ : ∀ a : Γ(U.scheme.left.1, ⊤),
      ψ (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hA hAdec U a) =
        Z'.neighborhoodSectionsToGenericHenselianLocalRing B S hS hC hCdec V (σ a))
    (e : rationalFunctions B S hS hA →+* rationalFunctions B S hS hC)
    (he : ∀ g : rationalFunctions B S hS hA,
      rationalFunctionsToTotalFractionRing B S hS hC V.scheme V.toSpace V.etale_toSpace (e g) =
        (IsFractionRing.ringEquivOfRingEquiv σ :
          FractionRing Γ(U.scheme.left.1, ⊤) ≃+* FractionRing Γ(V.scheme.left.1, ⊤))
          (rationalFunctionsToTotalFractionRing B S hS hA U.scheme U.toSpace U.etale_toSpace g))
    (g : rationalFunctions B S hS hA) :
    Z'.rationalFunctionsToGenericTotalFractionRing B S hS hC hCdec hCint hCN (e g) =
      (IsFractionRing.ringEquivOfRingEquiv ψ :
        Z.genericTotalFractionRing B S hS hA hAdec ≃+*
          Z'.genericTotalFractionRing B S hS hC hCdec)
        (Z.rationalFunctionsToGenericTotalFractionRing B S hS hA hAdec hAint hAN g) := by
  have := henselianLocalRing_isLocalRing B S hS A hA (Z.genericPoint B S hS A) hAdec
  have := henselianLocalRing_isLocalRing B S hS C hC (Z'.genericPoint B S hS C) hCdec
  have hCofA := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS A hA
    (Z.genericPoint B S hS A) ⟨U⟩
  have hCofC := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS C hC
    (Z'.genericPoint B S hS C) ⟨V⟩
  rw [← Z.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hA hAdec hAint hAN U hCofA g,
    ← Z'.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hC hCdec hCint hCN V hCofC
      (e g), he]
  exact (Z.ringEquivOfRingEquiv_neighborhoodTotalFractionRingToGeneric B S hS hA hC hAdec hCdec
    Z' U V hCofA hCofC σ ψ hψ _).symm

end CommonChart

/-! ### The extension of function fields, read on a chart -/

section Pullback

variable {A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hC : IsAlgebraicSpace B S hS C)
    (hAint : IsIntegralSpace B S hS A) (hCint : IsIntegralSpace B S hS C) (f : A ⟶ C)
    (hgen : pointsMap B S hS A f (genericPoint B S hS hA hAint) = genericPoint B S hS hC hCint)

include hAint hCint hgen in
/-- The preimage of a dense open subspace along a morphism of integral algebraic spaces carrying
the generic point to the generic point is a dense open subspace: it is open, and its point set
contains the generic point of the source. -/
theorem isDenseOpenSubspace_preimage_of_map_genericPoint {V : Subfunctor C}
    (hV : IsDenseOpenSubspace B S hS hC V) :
    IsDenseOpenSubspace B S hS hA (V.preimage f) := by
  refine ⟨isOpenSubspace_preimage B S hS f V hC hA hV.1,
    dense_of_genericPoint_mem B S hS hA hAint ?_⟩
  rw [range_pointsMap_preimage_ι B S hS f V, Set.mem_preimage, hgen]
  exact genericPoint_mem_range_pointsMap_ι B S hS hC hCint hV

include hAint hCint hgen in
/-- A morphism of the site into `A` factoring through the dense open subspaces of `A` still does
so, into `C`, after composition with a morphism carrying the generic point to the generic
point. -/
theorem FactorsThroughDenseOpens.comp_of_map_genericPoint {W : BigFppfOver B S hS}
    {c : yoneda.obj W ⟶ A} (hc : FactorsThroughDenseOpens B S hS hA W c) :
    FactorsThroughDenseOpens B S hS hC W (c ≫ f) := by
  intro V hV
  obtain ⟨j, hj⟩ := hc (V.preimage f)
    (isDenseOpenSubspace_preimage_of_map_genericPoint B S hS hA hC hAint hCint f hgen hV)
  exact ⟨j ≫ V.fromPreimage f, by rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
    hj]⟩

/-- The pullback of a partial map of `C` along a morphism `f : A ⟶ C` of integral algebraic
spaces carrying the generic point to the generic point: it is defined on the preimage of the
domain. -/
def PartialMap.preimageOfMapGenericPoint
    (q : PartialMap B S hS hC (affineLineFunctor B S hS)) :
    PartialMap B S hS hA (affineLineFunctor B S hS) where
  domain := q.domain.preimage f
  dense_open_domain := isDenseOpenSubspace_preimage_of_map_genericPoint B S hS hA hC hAint hCint
    f hgen q.dense_open_domain
  hom := q.domain.fromPreimage f ≫ q.hom

/-- The value on a chart of the pullback of a partial map is the value of the partial map on the
chart composed with the morphism. -/
theorem evalSitePartial_preimageOfMapGenericPoint {W : BigFppfOver B S hS}
    {c : yoneda.obj W ⟶ A} (hc : FactorsThroughDenseOpens B S hS hA W c)
    (q : PartialMap B S hS hC (affineLineFunctor B S hS)) :
    evalSitePartial B S hS hA hc
        (PartialMap.preimageOfMapGenericPoint B S hS hA hC hAint hCint f hgen q) =
      evalSitePartial B S hS hC
        (FactorsThroughDenseOpens.comp_of_map_genericPoint B S hS hA hC hAint hCint f hgen hc)
        q := by
  obtain ⟨j, hj⟩ := hc (q.domain.preimage f)
    (isDenseOpenSubspace_preimage_of_map_genericPoint B S hS hA hC hAint hCint f hgen
      q.dense_open_domain)
  rw [evalSitePartial_eq B S hS hA hc _ j hj,
    evalSitePartial_eq B S hS hC _ q (j ≫ q.domain.fromPreimage f)
      (by rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hj]),
    Category.assoc]
  rfl

include hCint in
/-- Evaluation at the representative of the residue field at a point is unchanged by passing
to an equal point, through the identification of the two residue fields. -/
theorem residueFieldCongr_evalRingHom_residueFieldRepresentative {x y : points B S hS C}
    (h : x = y)
    (hx : ((residueFieldRepresentative B S hS C hCint.2.1 x).1).class B S hS C =
      genericPoint B S hS hC hCint)
    (hy : ((residueFieldRepresentative B S hS C hCint.2.1 y).1).class B S hS C =
      genericPoint B S hS hC hCint) (g : rationalFunctions B S hS hC) :
    residueFieldCongr B S hS hCint.2.1 h
        (evalRingHom B S hS hC hCint (residueFieldRepresentative B S hS C hCint.2.1 x).1 hx g) =
      evalRingHom B S hS hC hCint (residueFieldRepresentative B S hS C hCint.2.1 y).1 hy g := by
  subst h
  rfl

/-- **The extension of function fields is the pullback of partial maps.** The class of the
pullback of a partial map `q` of `C` is the image of the class of `q` under the extension
`R(C) → R(A)` of function fields: both have the same value at the generic point of `A`, because
the homomorphism of residue fields there is the one `f` induces, characterized by its square
(Stacks 0EMW). -/
theorem toRationalMap_preimageOfMapGenericPoint
    (q : PartialMap B S hS hC (affineLineFunctor B S hS)) :
    (PartialMap.preimageOfMapGenericPoint B S hS hA hC hAint hCint f hgen q).toRationalMap
        B S hS =
      rationalFunctionMap B S hS hA hC hAint hCint f hgen (q.toRationalMap B S hS) := by
  obtain ⟨gsq, hspec, hsquare⟩ := residueFieldHom_spec B S hS A C hC hAint.2.1 hCint.2.1 f
    (genericPoint B S hS hA hAint)
  have hpy : ((residueFieldRepresentative B S hS C hCint.2.1
      (pointsMap B S hS A f (genericPoint B S hS hA hAint))).1).class B S hS C =
      genericPoint B S hS hC hCint := by
    rw [(residueFieldRepresentative B S hS C hCint.2.1
      (pointsMap B S hS A f (genericPoint B S hS hA hAint))).2.1]
    exact hgen
  have hmC := factorsThroughDenseOpens_fieldMorphism B S hS hC hCint
    (residueFieldRepresentative B S hS C hCint.2.1
      (pointsMap B S hS A f (genericPoint B S hS hA hAint))).1 hpy
  have hmA := factorsThroughDenseOpens_fieldMorphism B S hS hA hAint
    (genericRep B S hS hA hAint) (genericRep_class B S hS hA hAint)
  have hmAf := FactorsThroughDenseOpens.comp_of_map_genericPoint B S hS hA hC hAint hCint f hgen
    hmA
  have hts : (BigFppfOver.toScheme B S hS).map gsq =
      Spec.map (CommRingCat.ofHom
        (residueFieldHom B S hS A C hC hAint.2.1 hCint.2.1 f
          (genericPoint B S hS hA hAint))) := hspec
  have key : evalSiteRingHom B S hS hC hmAf (q.toRationalMap B S hS) =
      ((BigFppfOver.toScheme B S hS).map gsq).appTop
        (evalSiteRingHom B S hS hC hmC (q.toRationalMap B S hS)) := by
    rw [← evalSiteRingHom_naturality B S hS hC gsq hmC (hmC.comp B S hS hC gsq)]
    exact evalSiteRingHom_congr_mor B S hS hC hsquare.symm hmAf _ _
  refine (rationalFunctionsRingEquiv B S hS hA hAint).injective ?_
  have hLHS : rationalFunctionsRingEquiv B S hS hA hAint
        ((PartialMap.preimageOfMapGenericPoint B S hS hA hC hAint hCint f hgen q).toRationalMap
          B S hS) =
      (Scheme.ΓSpecIso (CommRingCat.of
          (residueField B S hS A hAint.2.1 (genericPoint B S hS hA hAint)))).hom
        (evalSitePartial B S hS hA hmA
          (PartialMap.preimageOfMapGenericPoint B S hS hA hC hAint hCint f hgen q)) := rfl
  have hRHS : rationalFunctionsRingEquiv B S hS hA hAint
        (rationalFunctionMap B S hS hA hC hAint hCint f hgen (q.toRationalMap B S hS)) =
      residueFieldHom B S hS A C hC hAint.2.1 hCint.2.1 f (genericPoint B S hS hA hAint)
        ((residueFieldCongr B S hS hCint.2.1 hgen).symm
          (rationalFunctionsRingEquiv B S hS hC hCint (q.toRationalMap B S hS))) := by
    simp only [rationalFunctionMap, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [hLHS, hRHS, evalSitePartial_preimageOfMapGenericPoint B S hS hA hC hAint hCint f hgen hmA q,
    show evalSitePartial B S hS hC hmAf q =
      evalSiteRingHom B S hS hC hmAf (q.toRationalMap B S hS) from rfl, key, hts,
    Scheme.ΓSpecIso_hom_appTop_ofHom_apply]
  refine congrArg _ ?_
  rw [rationalFunctionsRingEquiv_apply, ← residueFieldCongr_evalRingHom_residueFieldRepresentative
    B S hS hC hCint hgen hpy (genericRep_class B S hS hC hCint) (q.toRationalMap B S hS),
    RingEquiv.symm_apply_apply]
  rfl

/-- **The extension of function fields, evaluated on a chart.** For a morphism of the site into
`A` factoring through the dense open subspaces of `A`, the value of the image of `g ∈ R(C)` in
`R(A)` is the value of `g` on the chart composed with `f`. -/
theorem evalSiteRingHom_rationalFunctionMap_eq {W : BigFppfOver B S hS}
    {c : yoneda.obj W ⟶ A} (hc : FactorsThroughDenseOpens B S hS hA W c)
    (g : rationalFunctions B S hS hC) :
    evalSiteRingHom B S hS hA hc (rationalFunctionMap B S hS hA hC hAint hCint f hgen g) =
      evalSiteRingHom B S hS hC
        (FactorsThroughDenseOpens.comp_of_map_genericPoint B S hS hA hC hAint hCint f hgen hc)
        g := by
  obtain ⟨q, rfl⟩ := RationalMap.exists_rep B S hS g
  rw [← toRationalMap_preimageOfMapGenericPoint B S hS hA hC hAint hCint f hgen q]
  exact evalSitePartial_preimageOfMapGenericPoint B S hS hA hC hAint hCint f hgen hc q

/-- **The extension of function fields, read in the total ring of fractions of an affine
chart.** For an étale chart `c : W ⟶ A` whose scheme is affine, reduced and locally Noetherian,
and with `c ≫ f` étale, the reading in `Q(Γ(W, 𝒪_W))` of the image of `g ∈ R(C)` in `R(A)` is
the reading of `g` along `c ≫ f`. -/
theorem rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_comp (W : BigFppfOver B S hS)
    [IsAffine W.left.1] [IsReduced W.left.1] [IsLocallyNoetherian W.left.1]
    (c : yoneda.obj W ⟶ A) (hc : IsEtale B S hS c) (hcf : IsEtale B S hS (c ≫ f))
    (g : rationalFunctions B S hS hC) :
    rationalFunctionsToTotalFractionRing B S hS hA W c hc
        (rationalFunctionMap B S hS hA hC hAint hCint f hgen g) =
      rationalFunctionsToTotalFractionRing B S hS hC W (c ≫ f) hcf g := by
  have hmA := factorsThroughDenseOpens_totalFractionObject B S hS hA W c hc
  have hmC := factorsThroughDenseOpens_totalFractionObject B S hS hC W (c ≫ f) hcf
  rw [rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hA W c hc hmA,
    rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hC W (c ≫ f) hcf hmC,
    evalSiteRingHom_rationalFunctionMap_eq B S hS hA hC hAint hCint f hgen hmA g,
    evalSiteRingHom_congr_mor B S hS hC (Category.assoc _ _ _) _ hmC g]

end Pullback

/-! ### Along an open immersion -/

section OpenImmersion

variable {A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hC : IsAlgebraicSpace B S hS C)
    (hAint : IsIntegralSpace B S hS A) (hCint : IsIntegralSpace B S hS C)
    {m : A ⟶ C} (hm : IsOpenImmersion B S hS m)

include hm in
/-- An open immersion of integral algebraic spaces carries the generic point to the generic
point: its image is a nonempty open subset of an irreducible point space, hence dense, and the
point space of a decent algebraic space is Kolmogorov. -/
theorem pointsMap_genericPoint_of_isOpenImmersion :
    pointsMap B S hS A m (genericPoint B S hS hA hAint) = genericPoint B S hS hC hCint := by
  have hopen : IsOpen (Set.range (pointsMap B S hS A m)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS m hm
  have hmem : genericPoint B S hS hC hCint ∈ Set.range (pointsMap B S hS A m) :=
    ((isGenericPoint_genericPoint B S hS hC hCint).mem_open_set_iff hopen).2
      ⟨_, Set.mem_univ _, genericPoint B S hS hA hAint, rfl⟩
  exact pointsMap_eq_of_isGenericPoint B S hS hC hCint.2.1 m
    (dense_of_genericPoint_mem B S hS hC hCint hmem) (isGenericPoint_genericPoint B S hS hA hAint)
    (isGenericPoint_genericPoint B S hS hC hCint)

/-- **Stacks 0END along a monomorphism.** A monomorphism `p : A ⟶ C` of integral algebraic spaces
carrying the generic point to the generic point induces a bijective homomorphism of function
fields `R(C) → R(A)`: under the identifications of Stacks 0END it is the homomorphism of residue
fields at the generic points, which is bijective by Stacks 0EMX because the residue field
morphism of `A` followed by a monomorphism is a monomorphism. -/
theorem rationalFunctionMap_bijective_of_mono (p : A ⟶ C) [Mono p]
    (hgen : pointsMap B S hS A p (genericPoint B S hS hA hAint) = genericPoint B S hS hC hCint) :
    Function.Bijective (rationalFunctionMap B S hS hA hC hAint hCint p hgen) := by
  have hmono : Mono (residueFieldMorphism B S hS A hAint.2.1 (genericPoint B S hS hA hAint) ≫
      p) := by
    have := (residueFieldRepresentative B S hS A hAint.2.1 (genericPoint B S hS hA hAint)).2.2
    infer_instance
  have hiso := (isIso_residueFieldHom_iff_mono B S hS A C hC hAint.2.1 hCint.2.1 p
    (genericPoint B S hS hA hAint)).2 hmono
  have hb : Function.Bijective (residueFieldHom B S hS A C hC hAint.2.1 hCint.2.1 p
      (genericPoint B S hS hA hAint)) :=
    ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom _)
  exact (rationalFunctionsRingEquiv B S hS hA hAint).symm.bijective.comp
    ((hb.comp (residueFieldCongr B S hS hCint.2.1 hgen).symm.bijective).comp
      (rationalFunctionsRingEquiv B S hS hC hCint).bijective)

/-- **The function fields along an open immersion.** An open immersion `m : A ⟶ C` of integral
algebraic spaces identifies the function fields: this is the inverse of the restriction
`R(C) → R(A)` of rational functions along `m`, which is bijective by Stacks 0EMX. -/
def rationalFunctionsRingEquivOfIsOpenImmersion :
    rationalFunctions B S hS hA ≃+* rationalFunctions B S hS hC :=
  haveI := mono_of_isOpenImmersion B S hS m hm
  (RingEquiv.ofBijective _ (rationalFunctionMap_bijective_of_mono B S hS hA hC hAint hCint m
    (pointsMap_genericPoint_of_isOpenImmersion B S hS hA hC hAint hCint hm))).symm

/-- Restricting along the open immersion the rational function that
`AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIsOpenImmersion` attaches to `g` gives
back `g`. -/
theorem rationalFunctionMap_rationalFunctionsRingEquivOfIsOpenImmersion
    (hgen : pointsMap B S hS A m (genericPoint B S hS hA hAint) = genericPoint B S hS hC hCint)
    (g : rationalFunctions B S hS hA) :
    rationalFunctionMap B S hS hA hC hAint hCint m hgen
        (rationalFunctionsRingEquivOfIsOpenImmersion B S hS hA hC hAint hCint hm g) = g :=
  have := mono_of_isOpenImmersion B S hS m hm
  (RingEquiv.ofBijective _ (rationalFunctionMap_bijective_of_mono B S hS hA hC hAint hCint m
    (pointsMap_genericPoint_of_isOpenImmersion B S hS hA hC hAint hCint hm))).apply_symm_apply g

/-- A rational function of `C` whose restriction along the open immersion is `g` is the one
`AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIsOpenImmersion` attaches to `g`. -/
theorem rationalFunctionsRingEquivOfIsOpenImmersion_eq_of_rationalFunctionMap
    (hgen : pointsMap B S hS A m (genericPoint B S hS hA hAint) = genericPoint B S hS hC hCint)
    (g : rationalFunctions B S hS hA) (r : rationalFunctions B S hS hC)
    (hr : rationalFunctionMap B S hS hA hC hAint hCint m hgen r = g) :
    rationalFunctionsRingEquivOfIsOpenImmersion B S hS hA hC hAint hCint hm g = r := by
  have := mono_of_isOpenImmersion B S hS m hm
  refine (rationalFunctionMap_bijective_of_mono B S hS hA hC hAint hCint m hgen).1 ?_
  rw [hr, rationalFunctionMap_rationalFunctionsRingEquivOfIsOpenImmersion B S hS hA hC hAint hCint
    hm hgen]

variable (hAdec : IsDecentSpace B S hS A) (hCdec : IsDecentSpace B S hS C)
    (hAN : HasEtaleLocalProperty B S hS A (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hCN : HasEtaleLocalProperty B S hS C (fun T : Scheme.{u} => IsLocallyNoetherian T))

/-- **The naturality of Stacks 0ENK along an open immersion.** Let `m : A ⟶ C` be an open
immersion of decent, locally Noetherian, integral algebraic spaces and let `Z ⊂ A` and `Z' ⊂ C`
be prime divisors with `m` carrying the generic point of `Z` to that of `Z'`. Then the henselian
local rings at the two generic points are identified by some `ψ` for which, for every
`g ∈ R(A)`, the canonical embedding of Stacks 0ENK of the rational function `g` defines on `C`
is the image under `ψ` of the canonical embedding of `g`.

An affine elementary étale neighbourhood `(U, u)` of the generic point of `Z` (Stacks 0BBP) is,
composed with `m`, one of the generic point of `Z'` with the same pointed scheme; both henselian
local rings are henselizations of its stalk (Stacks 0EMY), and `ψ` is the identification of the
two as algebras over that stalk. Both embeddings are then computed on `Q(Γ(U, 𝒪_U))`. -/
theorem PrimeDivisor.exists_rationalFunctionsToGenericTotalFractionRing_of_isOpenImmersion
    (Z : PrimeDivisor B S hS A) (Z' : PrimeDivisor B S hS C)
    (h : pointsMap B S hS A m (Z.genericPoint B S hS A) = Z'.genericPoint B S hS C) :
    ∃ ψ : ↥(Z.genericHenselianLocalRing B S hS hA hAdec) ≃+*
        ↥(Z'.genericHenselianLocalRing B S hS hC hCdec),
      ∀ g : rationalFunctions B S hS hA,
        Z'.rationalFunctionsToGenericTotalFractionRing B S hS hC hCdec hCint hCN
            (rationalFunctionsRingEquivOfIsOpenImmersion B S hS hA hC hAint hCint hm g) =
          (IsFractionRing.ringEquivOfRingEquiv ψ :
            Z.genericTotalFractionRing B S hS hA hAdec ≃+*
              Z'.genericTotalFractionRing B S hS hC hCdec)
            (Z.rationalFunctionsToGenericTotalFractionRing B S hS hA hAdec hAint hAN g) := by
  obtain ⟨N, hNaff, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hA hAdec
    (Z.genericPoint B S hS A)
  have := Z.isReduced_chart B S hS hA hAint N
  have := Z.isLocallyNoetherian_chart B S hS hA hAN N
  let V : ElementaryEtaleNeighborhood B S hS C hC (Z'.genericPoint B S hS C) :=
    ElementaryEtaleNeighborhood.ofPointEq B S hS
      (ElementaryEtaleNeighborhood.ofOpenImmersion B S hS hA hC hm N) h
  have : IsAffine V.scheme.left.1 := inferInstanceAs (IsAffine N.scheme.left.1)
  have : IsReduced V.scheme.left.1 := inferInstanceAs (IsReduced N.scheme.left.1)
  have : IsLocallyNoetherian V.scheme.left.1 :=
    inferInstanceAs (IsLocallyNoetherian N.scheme.left.1)
  -- the two henselian local rings, as henselizations of the stalk of the common chart
  let := henselianLocalRing_isLocalRing B S hS A hA (Z.genericPoint B S hS A) hAdec
  let := henselianLocalRing_isLocalRing B S hS C hC (Z'.genericPoint B S hS C) hCdec
  let := stalkAlgebra B S hS A hA (Z.genericPoint B S hS A) hAdec N
  let : Algebra (N.scheme.left.1.presheaf.stalk N.point)
      ↥(Z'.genericHenselianLocalRing B S hS hC hCdec) :=
    stalkAlgebra B S hS C hC (Z'.genericPoint B S hS C) hCdec V
  have := henselianLocalRing_isHenselization B S hS A hA (Z.genericPoint B S hS A) hAdec N
  have : IsLocalRing.IsHenselization (N.scheme.left.1.presheaf.stalk N.point)
      (IsLocalRing.ResidueField (N.scheme.left.1.presheaf.stalk N.point))
      ↥(Z'.genericHenselianLocalRing B S hS hC hCdec) :=
    henselianLocalRing_isHenselization B S hS C hC (Z'.genericPoint B S hS C) hCdec V
  obtain ⟨ψ, hψ⟩ := StacksDraft.exists_ringEquiv_of_isHenselization
    (R := N.scheme.left.1.presheaf.stalk N.point)
    (H := ↥(Z.genericHenselianLocalRing B S hS hA hAdec))
    (H' := ↥(Z'.genericHenselianLocalRing B S hS hC hCdec))
  have hgen := pointsMap_genericPoint_of_isOpenImmersion B S hS hA hC hAint hCint hm
  have hrefl : ∀ y : FractionRing Γ(N.scheme.left.1, ⊤),
      (IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl Γ(N.scheme.left.1, ⊤)) :
        FractionRing Γ(N.scheme.left.1, ⊤) ≃+* FractionRing Γ(N.scheme.left.1, ⊤)) y = y :=
    fun y => by rw [IsFractionRing.ringEquivOfRingEquiv_refl, RingEquiv.refl_apply]
  refine ⟨ψ, fun g => Z.rationalFunctionsToGenericTotalFractionRing_eq_of_chart B S hS hA hC
    hAdec hCdec hAint hCint hAN hCN Z' N V (RingEquiv.refl _) ψ
    (fun a => hψ (N.scheme.left.1.presheaf.germ ⊤ N.point trivial a))
    (rationalFunctionsRingEquivOfIsOpenImmersion B S hS hA hC hAint hCint hm).toRingHom
    (fun g' => ?_) g⟩
  refine Eq.trans ?_ (hrefl _).symm
  conv_rhs => rw [← rationalFunctionMap_rationalFunctionsRingEquivOfIsOpenImmersion B S hS hA hC
    hAint hCint hm hgen g']
  exact (rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_comp B S hS hA hC hAint hCint m
    hgen N.scheme N.toSpace N.etale_toSpace V.etale_toSpace _).symm

end OpenImmersion

/-! ### The order of vanishing along an open immersion -/

/-- **The order of vanishing is unchanged by an open immersion.** Let `p : Y ⟶ X` be an open
immersion of locally Noetherian integral algebraic spaces over `S` carrying the generic point to
the generic point, let `P' ⊂ Y` and `P ⊂ X` be prime divisors with `p` carrying the generic
point of `P'` to that of `P`, and let `g ∈ R(X)^*`. The order of vanishing along `P'` of the
restriction of `g` to `Y` is the order of vanishing of `g` along `P`, both taken through the
canonical embeddings of Stacks 0ENK.

The canonical embeddings are carried into each other by an identification `ψ` of the henselian
local rings at the two generic points
(`PrimeDivisor.exists_rationalFunctionsToGenericTotalFractionRing_of_isOpenImmersion`),
and the order of vanishing on the total ring of fractions of a Noetherian local ring of
dimension at most one is invariant under a ring isomorphism, which is a flat local homomorphism
carrying the maximal ideal onto the maximal ideal
(`Stacks.Chow.ordTotalFracInt_map_of_flat`). -/
theorem genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (p : Y ⟶ X) (hp : IsOpenImmersion B S hS p)
    (hgen : pointsMap B S hS Y p (genericPoint B S hS hY hintY) = genericPoint B S hS hX hintX)
    (P' : PrimeDivisor B S hS Y) (P : PrimeDivisor B S hS X)
    (hP : pointsMap B S hS Y p (P'.genericPoint B S hS Y) = P.genericPoint B S hS X)
    (g : (rationalFunctions B S hS hX)ˣ) :
    (genericFractionEmbedding B S hS hY hintY.isDecentSpace hintY hNY).ord
        (Units.map (rationalFunctionMap B S hS hY hX hintY hintX p hgen :
          rationalFunctions B S hS hX →* rationalFunctions B S hS hY) g) P' =
      (genericFractionEmbedding B S hS hX hintX.isDecentSpace hintX hNX).ord g P := by
  obtain ⟨ψ, hψ⟩ :=
    P'.exists_rationalFunctionsToGenericTotalFractionRing_of_isOpenImmersion B S hS hY hX hintY
      hintX hp hintY.isDecentSpace hintX.isDecentSpace hNY hNX P hP
  have hR : rationalFunctionsRingEquivOfIsOpenImmersion B S hS hY hX hintY hintX hp
      (rationalFunctionMap B S hS hY hX hintY hintX p hgen (g : rationalFunctions B S hS hX)) =
      (g : rationalFunctions B S hS hX) :=
    rationalFunctionsRingEquivOfIsOpenImmersion_eq_of_rationalFunctionMap B S hS hY hX hintY
      hintX hp hgen _ _ rfl
  have key := hψ (rationalFunctionMap B S hS hY hX hintY hintX p hgen
    (g : rationalFunctions B S hS hX))
  rw [hR] at key
  -- the two henselian local rings and their total rings of fractions
  set A := ↥(P'.genericHenselianLocalRing B S hS hY hintY.isDecentSpace)
  set A' := ↥(P.genericHenselianLocalRing B S hS hX hintX.isDecentSpace)
  set EY := genericFractionEmbedding B S hS hY hintY.isDecentSpace hintY hNY
  set EX := genericFractionEmbedding B S hS hX hintX.isDecentSpace hintX hNX
  let := EY.isNoetherianRing P'
  let := EY.krullDimLE P'
  let := EX.isNoetherianRing P
  let := EX.krullDimLE P
  let : IsLocalRing A :=
    henselianLocalRing_isLocalRing B S hS Y hY (P'.genericPoint B S hS Y) hintY.isDecentSpace
  let : IsLocalRing A' :=
    henselianLocalRing_isLocalRing B S hS X hX (P.genericPoint B S hS X) hintX.isDecentSpace
  set x : FractionRing A := EY.emb P'
    (rationalFunctionMap B S hS hY hX hintY hintX p hgen (g : rationalFunctions B S hS hX))
    with hx
  have hxu : IsUnit x :=
    (g.isUnit.map (rationalFunctionMap B S hS hY hX hintY hintX p hgen)).map (EY.emb P')
  -- the order of vanishing is invariant under `ψ`
  let : Algebra A A' := ψ.toRingHom.toAlgebra
  have : Module.Flat A A' := RingHom.Flat.of_bijective ψ.bijective
  have : IsLocalHom (algebraMap A A') :=
    ⟨fun a ha => (MulEquiv.isUnit_map ψ).1 ha⟩
  have hmax : Ideal.map (algebraMap A A') (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal A' :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A A') ψ.surjective
  have hmap : IsLocalization.map (FractionRing A') (algebraMap A A')
      (Stacks.Chow.nonZeroDivisors_le_comap_of_flat (A := A) (A' := A')) x =
      (IsFractionRing.ringEquivOfRingEquiv ψ : FractionRing A ≃+* FractionRing A') x := by
    refine eq_of_comp_algebraMap_eq (R := A) _ _ (fun a => ?_) x
    simp only [IsLocalization.map_eq, RingHom.algebraMap_toAlgebra]
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap ψ a).symm
  have hord := Stacks.Chow.ordTotalFracInt_map_of_flat (A := A) (A' := A') (FractionRing A)
    (FractionRing A') hmax hxu.unit
  simp only [IsUnit.unit_spec] at hord
  unfold GenericFractionEmbedding.ord PrimeDivisor.ord
  refine Eq.trans ?_ (hord.symm.trans (Ring.ordTotalFracInt_congr A' _ _ (hmap.trans key.symm)))
  exact Ring.ordTotalFracInt_congr A _ _ (by simp [hx])

end AlgebraicGeometry.Space

end

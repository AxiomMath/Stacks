module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineRefinementOfNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingMapAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# Naturality of the embedding of Stacks 0ENK along a flat dominant morphism

Let `f : X ⟶ Y` be a morphism of decent, locally Noetherian, integral algebraic spaces over a
scheme `S` which carries the generic point of `X` to the generic point of `Y`, let `Z ⊆ X` and
`Z' ⊆ Y` be prime divisors and suppose the generic point `ξ` of `Z` lies over the generic point
`ξ'` of `Z'`. Stacks 0ENK gives the two canonical embeddings
`R(Y) → Q(𝒪^h_{Y, ξ'})` and `R(X) → Q(𝒪^h_{X, ξ})`
of the function fields into the total rings of fractions of the henselian local rings there, and
`f` gives both the extension `R(Y) → R(X)` of function fields and a homomorphism
`φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` of the henselian local rings. This file proves that the square
they form commutes, for `f` flat: the embedding of the pullback `g ∘ f` of a rational function
`g` of `Y` is the image of the embedding of `g` under the induced map `Q(φ)` of total rings of
fractions.

As a consequence, the coefficientwise form of Stacks 0EQA,
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_multiplicity_mul_ord`, holds with its hypotheses
discharged: the order of vanishing of a rational function pulls back with multiplicities.

## Main results

* `AlgebraicGeometry.Space.dominantPullback_toRationalMap`: the extension of function fields is
  the pullback of partial maps.
* `AlgebraicGeometry.Space.evalSiteRingHom_rationalFunctionMap`: the chart reading of `g ∘ f` is
  the reading of `g` on the chart composed with `f`.
* `AlgebraicGeometry.Space.toGenericTotalFractionRing_rationalFunctionMap_of_chartSquare`:
  the naturality square of Stacks 0ENK, on a square of affine charts.
* `AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_naturality`: the naturality of
  the embedding of Stacks 0ENK along a flat dominant morphism — there is a flat local
  homomorphism of the henselian local rings at the two generic points for which the square
  commutes.
* `AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_ord_eq_multiplicity_mul_ord`:
  Stacks 0EQA, coefficientwise, for the flat local homomorphism `f` induces.
* `AlgebraicGeometry.Space.totalFractionObjectMapOfHom` and
  `AlgebraicGeometry.Space.totalFractionObjectMapOfHom_comp`: the morphism of the site which
  restriction of global sections along `j` induces on the spectra of the total rings of
  fractions, and the square it fits in.

## Implementation notes

Flatness of `f` makes restriction of global sections along a morphism of charts over `f` carry
nonzerodivisors to nonzerodivisors, and makes `φ` flat, so that `Q(φ)` exists. Dominance — that
`f` carries the generic point of `X` to the generic point of `Y` — makes the pullback of a
rational function defined (Morphisms of Spaces, Section 0EML).

`φ` is existentially quantified, as in `AlgebraicGeometry.Space.exists_henselianLocalRingHom`:
the naturality square is a property of the homomorphism induced by a square of charts, not of an
arbitrary flat local homomorphism of the two henselian local rings — composing one with a
nontrivial automorphism leaves locality and flatness intact and destroys the square. For the same
reason the form of Stacks 0EQA here quantifies `φ` existentially.

## References

* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0EML](https://stacks.math.columbia.edu/tag/0EML)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPL](https://stacks.math.columbia.edu/tag/0EPL)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hgen : pointsMap B S hS X f (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY)

/-! ### Dense open subspaces pull back along a dominant morphism -/

include hX hintX hintY hgen in
/-- The preimage of a dense open subspace along a morphism of integral algebraic spaces
carrying the generic point to the generic point is a dense open subspace. -/
theorem isDenseOpenSubspace_preimage {V : Subfunctor Y}
    (hV : IsDenseOpenSubspace B S hS hY V) :
    IsDenseOpenSubspace B S hS hX (V.preimage f) := by
  refine ⟨isOpenSubspace_preimage B S hS f V hY hX hV.1, ?_⟩
  refine dense_of_genericPoint_mem B S hS hX hintX ?_
  rw [range_pointsMap_preimage_ι B S hS f V, Set.mem_preimage, hgen]
  exact genericPoint_mem_range_pointsMap_ι B S hS hY hintY hV

include hX hintX hintY hgen in
/-- A morphism of the site into the source which factors through every dense open subspace
there also factors, after composition with a dominant morphism, through every dense open
subspace of the target. -/
theorem factorsThroughDenseOpens_comp_of_genericPoint_eq {W : BigFppfOver B S hS}
    {m : yoneda.obj W ⟶ X} (hm : FactorsThroughDenseOpens B S hS hX W m) :
    FactorsThroughDenseOpens B S hS hY W (m ≫ f) := by
  intro V hV
  obtain ⟨j, hj⟩ := hm (V.preimage f)
    (isDenseOpenSubspace_preimage B S hS hX hY hintX hintY f hgen hV)
  refine ⟨j ≫ V.fromPreimage f, ?_⟩
  rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hj]

/-! ### The pullback of a rational function along a dominant morphism -/

/-- The pullback of a partial map along a morphism of integral algebraic spaces carrying the
generic point to the generic point, with domain the preimage of the domain. -/
def PartialMap.dominantPullback (q : PartialMap B S hS hY (affineLineFunctor B S hS)) :
    PartialMap B S hS hX (affineLineFunctor B S hS) where
  domain := q.domain.preimage f
  dense_open_domain :=
    isDenseOpenSubspace_preimage B S hS hX hY hintX hintY f hgen q.dense_open_domain
  hom := q.domain.fromPreimage f ≫ q.hom

include hX hintX hintY hgen in
/-- Evaluating the pullback of a partial map on a chart of the source is evaluating the
partial map itself on that chart composed with the morphism. -/
theorem evalSitePartial_dominantPullback {W : BigFppfOver B S hS} {m : yoneda.obj W ⟶ X}
    (hm : FactorsThroughDenseOpens B S hS hX W m)
    (q : PartialMap B S hS hY (affineLineFunctor B S hS)) :
    evalSitePartial B S hS hX hm
        (PartialMap.dominantPullback B S hS hX hY hintX hintY f hgen q) =
      evalSitePartial B S hS hY
        (factorsThroughDenseOpens_comp_of_genericPoint_eq B S hS hX hY hintX hintY f hgen hm)
        q := by
  obtain ⟨j, hj⟩ := hm (q.domain.preimage f)
    (isDenseOpenSubspace_preimage B S hS hX hY hintX hintY f hgen q.dense_open_domain)
  rw [evalSitePartial_eq B S hS hX hm _ j hj,
    evalSitePartial_eq B S hS hY _ q (j ≫ q.domain.fromPreimage f)
      (by rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hj]),
    Category.assoc]
  rfl

include hintY in
/-- Evaluation at the generic point of an integral algebraic space is unchanged by replacing
the chosen residue-field representative at a point by the one at an equal point, through the
identification of the two residue fields. -/
theorem residueFieldCongr_evalRingHom {x y : points B S hS Y} (h : x = y)
    (hx : ((residueFieldRepresentative B S hS Y hintY.2.1 x).1).class B S hS Y =
      genericPoint B S hS hY hintY)
    (hy : ((residueFieldRepresentative B S hS Y hintY.2.1 y).1).class B S hS Y =
      genericPoint B S hS hY hintY) (g : rationalFunctions B S hS hY) :
    residueFieldCongr B S hS hintY.2.1 h
        (evalRingHom B S hS hY hintY
          (residueFieldRepresentative B S hS Y hintY.2.1 x).1 hx g) =
      evalRingHom B S hS hY hintY
        (residueFieldRepresentative B S hS Y hintY.2.1 y).1 hy g := by
  subst h
  rfl

include hX hintX hintY hgen in
/-- The extension of function fields is the pullback of partial maps: the image under
`AlgebraicGeometry.Space.rationalFunctionMap` of the class of a partial map `q` of the target
is the class of the pullback of `q`. -/
theorem dominantPullback_toRationalMap
    (q : PartialMap B S hS hY (affineLineFunctor B S hS)) :
    (PartialMap.dominantPullback B S hS hX hY hintX hintY f hgen q).toRationalMap B S hS =
      rationalFunctionMap B S hS hX hY hintX hintY f hgen (q.toRationalMap B S hS) := by
  obtain ⟨gsq, hspec, hsquare⟩ := residueFieldHom_spec B S hS X Y hY hintX.2.1 hintY.2.1 f
    (genericPoint B S hS hX hintX)
  have hpy : ((residueFieldRepresentative B S hS Y hintY.2.1
      (pointsMap B S hS X f (genericPoint B S hS hX hintX))).1).class B S hS Y =
      genericPoint B S hS hY hintY := by
    rw [(residueFieldRepresentative B S hS Y hintY.2.1
      (pointsMap B S hS X f (genericPoint B S hS hX hintX))).2.1]
    exact hgen
  have hmY := factorsThroughDenseOpens_fieldMorphism B S hS hY hintY
    (residueFieldRepresentative B S hS Y hintY.2.1
      (pointsMap B S hS X f (genericPoint B S hS hX hintX))).1 hpy
  have hmX := factorsThroughDenseOpens_fieldMorphism B S hS hX hintX
    (genericRep B S hS hX hintX) (genericRep_class B S hS hX hintX)
  have hmXf := factorsThroughDenseOpens_comp_of_genericPoint_eq B S hS hX hY hintX hintY f hgen
    hmX
  have hts : (BigFppfOver.toScheme B S hS).map gsq =
      Spec.map (CommRingCat.ofHom
        (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 f
          (genericPoint B S hS hX hintX))) := hspec
  have key : evalSiteRingHom B S hS hY hmXf (q.toRationalMap B S hS) =
      ((BigFppfOver.toScheme B S hS).map gsq).appTop
        (evalSiteRingHom B S hS hY hmY (q.toRationalMap B S hS)) := by
    have hmsq := hmY.comp B S hS hY gsq
    rw [← evalSiteRingHom_naturality B S hS hY gsq hmY hmsq]
    exact evalSiteRingHom_congr_mor B S hS hY hsquare.symm hmXf hmsq _
  refine (rationalFunctionsRingEquiv B S hS hX hintX).injective ?_
  have hLHS : rationalFunctionsRingEquiv B S hS hX hintX
        ((PartialMap.dominantPullback B S hS hX hY hintX hintY f hgen q).toRationalMap B S hS) =
      (Scheme.ΓSpecIso (CommRingCat.of
          (residueField B S hS X hintX.2.1 (genericPoint B S hS hX hintX)))).hom
        (evalSitePartial B S hS hX hmX
          (PartialMap.dominantPullback B S hS hX hY hintX hintY f hgen q)) := rfl
  have hRHS : rationalFunctionsRingEquiv B S hS hX hintX
        (rationalFunctionMap B S hS hX hY hintX hintY f hgen (q.toRationalMap B S hS)) =
      residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 f (genericPoint B S hS hX hintX)
        ((residueFieldCongr B S hS hintY.2.1 hgen).symm
          (rationalFunctionsRingEquiv B S hS hY hintY (q.toRationalMap B S hS))) := by
    simp only [rationalFunctionMap, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [hLHS, hRHS,
    evalSitePartial_dominantPullback B S hS hX hY hintX hintY f hgen hmX q,
    show evalSitePartial B S hS hY hmXf q =
      evalSiteRingHom B S hS hY hmXf (q.toRationalMap B S hS) from rfl, key, hts,
    Scheme.ΓSpecIso_hom_appTop_ofHom_apply]
  refine congrArg _ ?_
  rw [rationalFunctionsRingEquiv_apply, ← residueFieldCongr_evalRingHom B S hS hY hintY hgen hpy
    (genericRep_class B S hS hY hintY) (q.toRationalMap B S hS), RingEquiv.symm_apply_apply]
  rfl

include hX hintX hintY hgen in
/-- The extension of function fields is read on a chart as composition with the morphism.
For a morphism of the site into the source which factors through every dense open subspace
there, the value of `g ∘ f` on that chart is the value of `g` on the chart composed with
`f`. -/
theorem evalSiteRingHom_rationalFunctionMap {W : BigFppfOver B S hS} {m : yoneda.obj W ⟶ X}
    (hm : FactorsThroughDenseOpens B S hS hX W m) (g : rationalFunctions B S hS hY) :
    evalSiteRingHom B S hS hX hm (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
      evalSiteRingHom B S hS hY
        (factorsThroughDenseOpens_comp_of_genericPoint_eq B S hS hX hY hintX hintY f hgen hm)
        g := by
  obtain ⟨q, rfl⟩ := RationalMap.exists_rep B S hS g
  rw [← dominantPullback_toRationalMap B S hS hX hY hintX hintY f hgen q]
  exact evalSitePartial_dominantPullback B S hS hX hY hintX hintY f hgen hm q

/-! ### The two chart readings of a rational function and of its pullback -/

section Charts

variable {U V : BigFppfOver B S hS}

/-- Restriction of global sections along a morphism of the site. -/
abbrev chartGlobalSectionsRestrict (j : U ⟶ V) : Γ(V.left.1, ⊤) →+* Γ(U.left.1, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map j).appTop.hom

/-- Restriction of global sections along a morphism of the site, on total rings of fractions:
it exists as soon as restriction carries nonzerodivisors to nonzerodivisors. -/
def chartFractionMap (j : U ⟶ V)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j)) :
    FractionRing Γ(V.left.1, ⊤) →+* FractionRing Γ(U.left.1, ⊤) :=
  IsLocalization.map (FractionRing Γ(U.left.1, ⊤)) (chartGlobalSectionsRestrict B S hS j) hj

/-- Restriction on total rings of fractions extends restriction of global sections. -/
theorem chartFractionMap_algebraMap (j : U ⟶ V)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (a : Γ(V.left.1, ⊤)) :
    chartFractionMap B S hS j hj
        (algebraMap Γ(V.left.1, ⊤) (FractionRing Γ(V.left.1, ⊤)) a) =
      algebraMap Γ(U.left.1, ⊤) (FractionRing Γ(U.left.1, ⊤))
        (chartGlobalSectionsRestrict B S hS j a) :=
  IsLocalization.map_eq hj a

variable [IsAffine U.left.1] [IsAffine V.left.1]

/-- The square formed by restriction along `j` on total rings of fractions, restriction along
`j` on schemes, and the two canonical morphisms from the spectra of the total rings of fractions
commutes. -/
private theorem specMap_chartFractionMap_comp (j : U ⟶ V)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j)) :
    Spec.map (CommRingCat.ofHom (chartFractionMap B S hS j hj)) ≫
        V.left.1.fromSpecTotalFractionRing =
      U.left.1.fromSpecTotalFractionRing ≫ (BigFppfOver.toScheme B S hS).map j := by
  rw [Scheme.specMap_comp_fromSpecTotalFractionRing (T := V.left.1) (T' := U.left.1)
    ((BigFppfOver.toScheme B S hS).map j) (chartFractionMap B S hS j hj)
    (RingHom.id (FractionRing Γ(U.left.1, ⊤))) (chartFractionMap_algebraMap B S hS j hj),
    CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- The spectrum of the total ring of fractions of `Γ(U, 𝒪_U)`, mapped to that of
`Γ(V, 𝒪_V)` by restriction along `j`. -/
def totalFractionObjectMapOfHom (j : U ⟶ V)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j)) :
    totalFractionObject B S hS U ⟶ totalFractionObject B S hS V :=
  Over.homMk (⟨Spec.map (CommRingCat.ofHom (chartFractionMap B S hS j hj))⟩ :
      B.obj (contains_specTotalFractionRing B S hS U) ⟶ (totalFractionObject B S hS V).left)
    (by
      apply ObjectProperty.hom_ext
      have hw : (BigFppfOver.toScheme B S hS).map j ≫ V.hom.1 = U.hom.1 :=
        congrArg (fun k : U.left ⟶ B.obj hS ↦ k.1) (Over.w j)
      change Spec.map (CommRingCat.ofHom (chartFractionMap B S hS j hj)) ≫
          (V.left.1.fromSpecTotalFractionRing ≫ V.hom.1) =
        U.left.1.fromSpecTotalFractionRing ≫ U.hom.1
      rw [← hw, ← Category.assoc, specMap_chartFractionMap_comp B S hS j hj, Category.assoc])

/-- The square of the restriction along `j` and the two canonical morphisms from the spectra
of the total rings of fractions commutes. -/
theorem totalFractionObjectMapOfHom_comp (j : U ⟶ V)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j)) :
    totalFractionObjectMapOfHom B S hS j hj ≫ totalFractionObjectMap B S hS V =
      totalFractionObjectMap B S hS U ≫ j :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (specMap_chartFractionMap_comp B S hS j hj))

variable [IsReduced U.left.1] [IsLocallyNoetherian U.left.1] [IsReduced V.left.1]
    [IsLocallyNoetherian V.left.1]

include hX hintX hintY hgen in
/-- The chart reading of the pullback of a rational function. Let `cU : U → X` and
`cV : V → Y` be étale charts whose schemes are affine, reduced and locally Noetherian, let
`j : U → V` be a morphism of the site over `f` and suppose restriction along `j` carries
nonzerodivisors to nonzerodivisors. Then the reading of `g ∘ f` in `Q(Γ(U, 𝒪_U))` is the
reading of `g` in `Q(Γ(V, 𝒪_V))`, restricted along `j`. -/
theorem rationalFunctionsToTotalFractionRing_rationalFunctionMap
    (cU : yoneda.obj U ⟶ X) (hcU : IsEtale B S hS cU)
    (cV : yoneda.obj V ⟶ Y) (hcV : IsEtale B S hS cV) (j : U ⟶ V)
    (hsq : yoneda.map j ≫ cV = cU ≫ f)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (g : rationalFunctions B S hS hY) :
    rationalFunctionsToTotalFractionRing B S hS hX U cU hcU
        (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
      chartFractionMap B S hS j hj
        (rationalFunctionsToTotalFractionRing B S hS hY V cV hcV g) := by
  have hmU := factorsThroughDenseOpens_totalFractionObject B S hS hX U cU hcU
  have hmV := factorsThroughDenseOpens_totalFractionObject B S hS hY V cV hcV
  have hmUf := factorsThroughDenseOpens_comp_of_genericPoint_eq B S hS hX hY hintX hintY f hgen
    hmU
  have hmV' := hmV.comp B S hS hY (totalFractionObjectMapOfHom B S hS j hj)
  have hmor : yoneda.map (totalFractionObjectMapOfHom B S hS j hj) ≫
        (yoneda.map (totalFractionObjectMap B S hS V) ≫ cV) =
      (yoneda.map (totalFractionObjectMap B S hS U) ≫ cU) ≫ f := by
    rw [← Category.assoc, ← Functor.map_comp, totalFractionObjectMapOfHom_comp B S hS j hj,
      Functor.map_comp, Category.assoc, hsq, Category.assoc]
  rw [rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hX U cU hcU hmU,
    rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hY V cV hcV hmV,
    evalSiteRingHom_rationalFunctionMap B S hS hX hY hintX hintY f hgen hmU g,
    ← evalSiteRingHom_congr_mor B S hS hY hmor hmV' hmUf g,
    evalSiteRingHom_naturality B S hS hY (totalFractionObjectMapOfHom B S hS j hj) hmV hmV' g]
  exact Scheme.ΓSpecIso_hom_appTop_ofHom_apply (chartFractionMap B S hS j hj) _

end Charts

/-! ### Naturality of the embedding of Stacks 0ENK -/

section Embedding

variable (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (ZX : PrimeDivisor B S hS X) (ZY : PrimeDivisor B S hS Y)

/-- The map on total rings of fractions induced by a homomorphism of henselian local rings
which extends restriction along a morphism of charts is compatible with the maps from the total
rings of fractions of the two charts' global sections. -/
theorem neighborhoodTotalFractionRingToGeneric_chartFractionMap
    [IsLocalRing ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)]
    [IsLocalRing ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)]
    (U : ElementaryEtaleNeighborhood B S hS X hX (ZX.genericPoint B S hS X))
    (V : ElementaryEtaleNeighborhood B S hS Y hY (ZY.genericPoint B S hS Y))
    [IsAffine U.scheme.left.1] [IsAffine V.scheme.left.1]
    (j : U.scheme ⟶ V.scheme)
    (hj : (Γ(V.scheme.left.1, ⊤))⁰ ≤
      ((Γ(U.scheme.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
      ↥(ZX.genericHenselianLocalRing B S hS hX hdecX))
    (hφ : (↥(ZY.genericHenselianLocalRing B S hS hY hdecY))⁰ ≤
      ((↥(ZX.genericHenselianLocalRing B S hS hX hdecX))⁰).comap φ)
    (hcompat : ∀ a : Γ(V.scheme.left.1, ⊤),
      φ (ZY.neighborhoodSectionsToGenericHenselianLocalRing B S hS hY hdecY V a) =
        ZX.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdecX U
          (chartGlobalSectionsRestrict B S hS j a))
    (x : FractionRing Γ(V.scheme.left.1, ⊤)) :
    ZX.neighborhoodTotalFractionRingToGeneric B S hS hX hdecX U
        (chartFractionMap B S hS j hj x) =
      IsLocalization.map (ZX.genericTotalFractionRing B S hS hX hdecX) φ hφ
        (ZY.neighborhoodTotalFractionRingToGeneric B S hS hY hdecY V x) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (Γ(V.scheme.left.1, ⊤))⁰ x
  simp only [PrimeDivisor.neighborhoodTotalFractionRingToGeneric, chartFractionMap,
    IsLocalization.map_mk']
  rw [hcompat a]
  exact congrArg _ (Subtype.ext (hcompat (b : Γ(V.scheme.left.1, ⊤))).symm)

include hX hintX hintY hgen in
/-- Naturality of the embedding of Stacks 0ENK, on a square of charts. Let `f : X ⟶ Y` be
a morphism of decent, locally Noetherian, integral algebraic spaces carrying the generic point
of `X` to the generic point of `Y`, let `Z ⊆ X` and `Z' ⊆ Y` be prime divisors, let `U` and `V`
be affine elementary étale neighbourhoods of the two generic points and let `j : U ⟶ V` be a
morphism of the site over `f` carrying nonzerodivisors to nonzerodivisors. A homomorphism
`φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` of the henselian local rings which extends restriction along
`j`, and which carries nonzerodivisors to nonzerodivisors, makes the square

  `R(Y) → R(X)`, `R(Y) → Q(𝒪^h_{Y, ξ'})`, `R(X) → Q(𝒪^h_{X, ξ})`, `Q(φ)`

commute: the embedding of Stacks 0ENK of the pullback `g ∘ f` of a rational function `g` of `Y`
is the image under `Q(φ)` of the embedding of `g`. -/
theorem toGenericTotalFractionRing_rationalFunctionMap_of_chartSquare
    (U : ElementaryEtaleNeighborhood B S hS X hX (ZX.genericPoint B S hS X))
    (V : ElementaryEtaleNeighborhood B S hS Y hY (ZY.genericPoint B S hS Y))
    [IsAffine U.scheme.left.1] [IsAffine V.scheme.left.1]
    (j : U.scheme ⟶ V.scheme) (hsq : yoneda.map j ≫ V.toSpace = U.toSpace ≫ f)
    (hj : (Γ(V.scheme.left.1, ⊤))⁰ ≤
      ((Γ(U.scheme.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
      ↥(ZX.genericHenselianLocalRing B S hS hX hdecX))
    (hφ : (↥(ZY.genericHenselianLocalRing B S hS hY hdecY))⁰ ≤
      ((↥(ZX.genericHenselianLocalRing B S hS hX hdecX))⁰).comap φ)
    (hcompat : ∀ a : Γ(V.scheme.left.1, ⊤),
      φ (ZY.neighborhoodSectionsToGenericHenselianLocalRing B S hS hY hdecY V a) =
        ZX.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdecX U
          (chartGlobalSectionsRestrict B S hS j a))
    (g : rationalFunctions B S hS hY) :
    ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX hintX hNX
        (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
      IsLocalization.map (ZX.genericTotalFractionRing B S hS hX hdecX) φ hφ
        (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY g) := by
  have : IsLocalRing ↥(ZX.genericHenselianLocalRing B S hS hX hdecX) :=
    henselianLocalRing_isLocalRing B S hS X hX (ZX.genericPoint B S hS X) hdecX
  have : IsLocalRing ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) :=
    henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
  have := ZX.isReduced_chart B S hS hX hintX U
  have := ZX.isLocallyNoetherian_chart B S hS hX hNX U
  have := ZY.isReduced_chart B S hS hY hintY V
  have := ZY.isLocallyNoetherian_chart B S hS hY hNY V
  rw [← ZX.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX hdecX hintX hNX U,
    ← ZY.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hY hdecY hintY hNY V,
    rationalFunctionsToTotalFractionRing_rationalFunctionMap B S hS hX hY hintX hintY f hgen
      U.toSpace U.etale_toSpace V.toSpace V.etale_toSpace j hsq hj g,
    neighborhoodTotalFractionRingToGeneric_chartFractionMap B S hS hX hY hdecX hdecY ZX ZY U V
      j hj φ hφ hcompat]

/-- The germ at a point of a global section moves along a morphism of schemes by restriction of
global sections, read through the identification of the stalks at the point and at its
image. -/
theorem germ_top_stalkCongr_stalkMap {T T' : Scheme.{u}} (h : T' ⟶ T) {t' : T'} {t : T}
    (ht : h.base t' = t) (a : Γ(T, ⊤)) :
    ((T.presheaf.stalkCongr (Inseparable.of_eq ht.symm)).hom ≫ h.stalkMap t').hom
        (T.presheaf.germ ⊤ t trivial a) =
      T'.presheaf.germ ⊤ t' trivial (h.appTop a) := by
  subst ht
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact Scheme.Hom.germ_stalkMap_apply h ⊤ t' trivial a

include hX hintX hintY hgen in
/-- Naturality of the embedding of Stacks 0ENK along a flat dominant morphism. Let
`f : X ⟶ Y` be a flat morphism of decent, locally Noetherian, integral algebraic spaces over
`S` carrying the generic point of `X` to the generic point of `Y`, let `Z ⊆ X` and `Z' ⊆ Y` be
prime divisors and suppose the generic point `ξ` of `Z` lies over the generic point `ξ'` of
`Z'`. There is a flat local homomorphism `φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` of the henselian local
rings there for which the square

  `R(Y) → R(X)`, `R(Y) → Q(𝒪^h_{Y, ξ'})`, `R(X) → Q(𝒪^h_{X, ξ})`, `Q(φ)`

commutes: for every rational function `g` of `Y`, the embedding of Stacks 0ENK of its pullback
`g ∘ f` is the image under `Q(φ)` of the embedding of `g`. -/
theorem exists_genericHenselianLocalRingHom_naturality
    (hf : IsFlat B S hS f)
    (hZ : pointsMap B S hS X f (ZX.genericPoint B S hS X) = ZY.genericPoint B S hS Y) :
    ∃ (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
        ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) (_ : IsLocalHom φ) (hφflat : φ.Flat),
      ∀ g : rationalFunctions B S hS hY,
        ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX hintX hNX
            (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
          IsLocalization.map (T := (↥(ZX.genericHenselianLocalRing B S hS hX hdecX))⁰)
            (ZX.genericTotalFractionRing B S hS hX hdecX) φ
            (fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom hφflat hc)
            (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY g) := by
  obtain ⟨V, U₀, j₀, hj₀, φ, hsq₀, hVaff, hφloc, hcompat₀, hφflat⟩ := hZ ▸
    exists_henselianLocalRingHom_affineChartSquare B S hS hX hdecX hY hdecY f
      (ZX.genericPoint B S hS X)
  obtain ⟨U, r, hUaff⟩ := ElementaryEtaleNeighborhood.exists_affine_refinement B S hS X hX
    (ZX.genericPoint B S hS X) U₀
  have : IsAffine V.scheme.left.1 := hVaff
  have : IsAffine U.scheme.left.1 := hUaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.scheme) := hUaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.scheme) := hVaff
  have hsq : yoneda.map (r.hom ≫ j₀) ≫ V.toSpace = U.toSpace ≫ f := by
    rw [Functor.map_comp, Category.assoc, hsq₀, ← Category.assoc, r.over]
  have het : ∀ {P} {hP : IsAlgebraicSpace B S hS P} {x}
      (T : ElementaryEtaleNeighborhood B S hS P hP x),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf T.toSpace := fun T => by
    simpa using T.etale_toSpace T.scheme (𝟙 _) (presheaf_etale_id B S hS T.scheme)
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (r.hom ≫ j₀)) :=
    hf U.scheme V.scheme U.toSpace V.toSpace (r.hom ≫ j₀) (het U) (het V) hsq
  have hj : (Γ(V.scheme.left.1, ⊤))⁰ ≤ ((Γ(U.scheme.left.1, ⊤))⁰).comap
      (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀)) := fun _ hc =>
    Ring.map_mem_nonZeroDivisors_of_flatHom
      (Scheme.Hom.flat_appTop ((BigFppfOver.toScheme B S hS).map (r.hom ≫ j₀))) hc
  have hcompat : ∀ a : Γ(V.scheme.left.1, ⊤),
      φ (ZY.neighborhoodSectionsToGenericHenselianLocalRing B S hS hY hdecY V a) =
        ZX.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdecX U
          (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) a) := by
    intro a
    have h₁ := hcompat₀ (V.scheme.left.1.presheaf.germ ⊤ V.point trivial a)
    rw [germ_top_stalkCongr_stalkMap j₀.left.1 hj₀ a] at h₁
    have h₂ := ZX.neighborhoodSectionsToGenericHenselianLocalRing_naturality B S hS hX hdecX r
      (j₀.left.1.appTop a)
    rw [show chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) a =
        r.hom.left.1.appTop (j₀.left.1.appTop a) by
      rw [chartGlobalSectionsRestrict, Functor.map_comp, Scheme.Hom.comp_appTop]; rfl, h₂]
    exact h₁
  exact ⟨φ, hφloc, hφflat hf, fun g =>
    toGenericTotalFractionRing_rationalFunctionMap_of_chartSquare
      B S hS hX hY hintX hintY f hgen hdecX hdecY hNX hNY ZX ZY U V (r.hom ≫ j₀) hsq hj φ
      (fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom (hφflat hf) hc) hcompat g⟩

/-! ### Stacks 0EQA with its hypotheses discharged -/

/-- A unit of the total ring of fractions is a fraction of two nonzerodivisors. -/
theorem _root_.Ring.exists_mk'_of_isUnit {A : Type*} [CommRing A] (K : Type*) [CommRing K]
    [Algebra A K] [IsFractionRing A K] {x : K} (hx : IsUnit x) :
    ∃ a b : A⁰, x = IsLocalization.mk' K (a : A) b := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective A⁰ x
  refine ⟨⟨a, ?_⟩, b, rfl⟩
  have hunit : IsUnit (algebraMap A K a) := by
    simpa [IsLocalization.mk'_spec] using hx.mul (IsLocalization.map_units K b)
  exact mem_nonZeroDivisors_of_injective (IsLocalization.injective K le_rfl)
    hunit.mem_nonZeroDivisors

include hX hintX hintY hgen in
/-- Stacks 0EQA, coefficientwise: the order of vanishing of a rational function pulls back with
multiplicities. Let `f : X ⟶ Y` be a flat morphism of decent, locally
Noetherian, integral algebraic spaces over `S` carrying the generic point of `X` to the generic
point of `Y`, let `Z ⊆ X` and `Z' ⊆ Y` be prime divisors and suppose the generic point `ξ` of
`Z` lies over the generic point `ξ'` of `Z'`. There is a flat local homomorphism
`φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` induced by `f` such that, `m` being the multiplicity of `Z` over
`Z'` along `φ`, every `g ∈ R(Y)` with `g` and its pullback `g ∘ f` units of the two total rings
of fractions satisfies

  `ord_Z(g ∘ f) = m · ord_{Z'}(g)`,

the orders of vanishing being taken at the canonical embeddings of Stacks 0ENK. -/
theorem exists_genericHenselianLocalRingHom_ord_eq_multiplicity_mul_ord
    (hf : IsFlat B S hS f)
    (hZ : pointsMap B S hS X f (ZX.genericPoint B S hS X) = ZY.genericPoint B S hS Y) :
    letI := ZX.nontrivial_genericHenselianLocalRing B S hS hX hdecX hintX hNX
    letI := ZX.isNoetherianRing_genericHenselianLocalRing B S hS hX hdecX hintX hNX
    letI := ZX.krullDimLE_genericHenselianLocalRing B S hS hX hdecX hintX hNX
    letI := ZY.nontrivial_genericHenselianLocalRing B S hS hY hdecY hintY hNY
    letI := ZY.isNoetherianRing_genericHenselianLocalRing B S hS hY hdecY hintY hNY
    letI := ZY.krullDimLE_genericHenselianLocalRing B S hS hY hdecY hintY hNY
    letI := henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
    ∃ (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
        ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) (_ : IsLocalHom φ) (_ : φ.Flat),
      ∀ m : ℕ, primeDivisorFlatMultiplicity B S hS hX hdecX ZX hY hdecY ZY φ = (m : ℕ∞) →
        ∀ (g : rationalFunctions B S hS hY)
          (hgu : IsUnit (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY
            hNY g))
          (hgfu : IsUnit (ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX hintX
            hNX (rationalFunctionMap B S hS hX hY hintX hintY f hgen g))),
          ZX.ord B S hS hX hdecX (ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX
              hintX hNX (rationalFunctionMap B S hS hX hY hintX hintY f hgen g)) hgfu =
            (m : ℤ) * ZY.ord B S hS hY hdecY
              (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY g)
              hgu := by
  have : ∀ W : PrimeDivisor B S hS X,
      IsLocalRing ↥(W.genericHenselianLocalRing B S hS hX hdecX) :=
    fun W => henselianLocalRing_isLocalRing B S hS X hX (W.genericPoint B S hS X) hdecX
  have : ∀ W : PrimeDivisor B S hS Y,
      IsLocalRing ↥(W.genericHenselianLocalRing B S hS hY hdecY) :=
    fun W => henselianLocalRing_isLocalRing B S hS Y hY (W.genericPoint B S hS Y) hdecY
  have : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdecX) :=
    (genericFractionEmbedding B S hS hX hdecX hintX hNX).isNoetherianRing
  have : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdecX) :=
    (genericFractionEmbedding B S hS hX hdecX hintX hNX).krullDimLE
  have : ∀ W : PrimeDivisor B S hS Y,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hY hdecY) :=
    (genericFractionEmbedding B S hS hY hdecY hintY hNY).isNoetherianRing
  have : ∀ W : PrimeDivisor B S hS Y,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hY hdecY) :=
    (genericFractionEmbedding B S hS hY hdecY hintY hNY).krullDimLE
  obtain ⟨φ, hφloc, hφflat, hnat⟩ :=
    exists_genericHenselianLocalRingHom_naturality B S hS hX hY
      hintX hintY f hgen hdecX hdecY hNX hNY ZX ZY hf hZ
  refine ⟨φ, hφloc, hφflat, fun m hm g hgu hgfu => ?_⟩
  obtain ⟨a, b, hab⟩ := Ring.exists_mk'_of_isUnit
    (A := ↥(ZY.genericHenselianLocalRing B S hS hY hdecY))
    (ZY.genericTotalFractionRing B S hS hY hdecY) hgu
  refine PrimeDivisor.ord_eq_multiplicity_mul_ord B S hS hX hdecX ZX hY hdecY ZY hφloc hφflat hm
    (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY)
    (ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX hintX hNX) g
    (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) a b hab ?_ hgu hgfu
  rw [hnat g, hab]
  exact IsLocalization.map_mk' _ (a : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)) b

end Embedding

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPreimageDominance
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatWeaklyAssociatedGenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition

/-!
# The reading of a rational function on a flat affine chart

Let `Y` be an integral algebraic space over a scheme `S` and let `c : V → Y` be a **flat**
chart whose scheme is affine and locally Noetherian, not necessarily reduced. Write
`A = Γ(V, 𝒪_V)`. This file constructs the ring homomorphism

  `R(Y) ⟶ Q(A)`

reading a rational function of `Y` on `V`, generalizing
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing`, which is defined only when `c`
is *étale* and only for a reduced chart.

A rational function is a section over a dense open subspace of `Y`, so to read it on `V` it is
enough that the morphism `Spec Q(A) → V → Y` factor through every dense open subspace of `Y`.
It does, because every point of `Spec Q(A)` is carried to the generic point of `Y`.

For a morphism `f` of integral algebraic spaces, the reading of the pullback `g ∘ f` of a
rational function on an étale chart of the source is the restriction of the reading of `g` on a
flat chart of the target, and hence a fraction `s / t` of global sections of that chart.

## Main definitions

* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRingOfFlat`: the ring homomorphism
  `R(Y) ⟶ Q(Γ(V, 𝒪_V))` for a flat affine chart.

## Main results

* `AlgebraicGeometry.Space.pointsMap_totalFractionObjectMap_eq_genericPoint_of_isFlat`: every
  point of `Spec Q(Γ(V, 𝒪_V))` is carried to the generic point of `Y`.
* `AlgebraicGeometry.Space.factorsThroughDenseOpens_totalFractionObject_of_isFlat`: the
  morphism `Spec Q(Γ(V, 𝒪_V)) → Y` factors through every dense open subspace.
* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRingOfFlat_of_isEtale`: for an étale
  chart the homomorphism is the one of
  `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing`.
* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionMap_of_isFlat`:
  the reading of `g ∘ f` on an étale chart of the source is the reading of `g` on a flat chart
  of the target, restricted along a morphism of the two charts.
* `exists_rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat` and
  `exists_rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_comp`: the
  same, in the form of the existence of a numerator and a denominator among the global sections
  of the chart of the target.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The spectrum of the total ring of fractions lies over the generic point -/

/-- **Every point of `Spec Q(Γ(V, 𝒪_V))` lies over the generic point of `Y`**, for `c : V → Y`
a flat chart of an integral algebraic space whose scheme is affine and locally Noetherian, not
necessarily reduced. -/
theorem pointsMap_totalFractionObjectMap_eq_genericPoint_of_isFlat
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    (V : BigFppfOver B S hS) [IsAffine V.left.1]
    [IsLocallyNoetherian V.left.1] (c : yoneda.obj V ⟶ Y) (hc : IsFlat B S hS c)
    (z : points B S hS (yoneda.obj (totalFractionObject B S hS V))) :
    pointsMap B S hS (yoneda.obj (totalFractionObject B S hS V))
        (yoneda.map (totalFractionObjectMap B S hS V) ≫ c) z =
      genericPoint B S hS hY hintY := by
  rw [pointsMap_comp_apply]
  refine pointsMap_eq_genericPoint_of_isFlat_of_mem_range_fromSpecTotalFractionRing B S hS hY
    hintY V c hc _ (schemePointsHomeomorph B S hS (totalFractionObject B S hS V) z) ?_
  exact pointsToScheme_pointsMap B S hS (totalFractionObjectMap B S hS V) z

/-- **The pullback of rational functions to a flat affine chart exists.** For a flat chart
`c : V → Y` of an integral algebraic space whose scheme is affine and locally Noetherian, the
morphism `Spec Q(Γ(V, 𝒪_V)) → Y` factors through every dense open subspace of `Y`. -/
theorem factorsThroughDenseOpens_totalFractionObject_of_isFlat
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    (V : BigFppfOver B S hS) [IsAffine V.left.1]
    [IsLocallyNoetherian V.left.1] (c : yoneda.obj V ⟶ Y) (hc : IsFlat B S hS c) :
    FactorsThroughDenseOpens B S hS hY (totalFractionObject B S hS V)
      (yoneda.map (totalFractionObjectMap B S hS V) ≫ c) := by
  intro W hW
  refine (factorsThrough_openSubspace_iff_points B S hS hY
    (isAlgebraicSpace_yoneda B S hS _) W hW.1 _).2 ?_
  rintro y ⟨z, rfl⟩
  rw [pointsMap_totalFractionObjectMap_eq_genericPoint_of_isFlat B S hS hY hintY V c hc z]
  exact genericPoint_mem_range_pointsMap_ι B S hS hY hintY hW

/-- The ring homomorphism from the rational functions of an integral algebraic space to the
total ring of fractions of the global sections of a **flat** affine chart, obtained by pulling
rational functions back along the morphism `Spec Q(Γ(V, 𝒪_V)) → Y`. For an étale chart this is
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing`. -/
def rationalFunctionsToTotalFractionRingOfFlat (hY : IsAlgebraicSpace B S hS Y)
    (hintY : IsIntegralSpace B S hS Y) (V : BigFppfOver B S hS) [IsAffine V.left.1]
    [IsLocallyNoetherian V.left.1] (c : yoneda.obj V ⟶ Y)
    (hc : IsFlat B S hS c) :
    rationalFunctions B S hS hY →+* FractionRing Γ(V.left.1, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(V.left.1, ⊤)))).hom.hom).comp
    (evalSiteRingHom B S hS hY
      (factorsThroughDenseOpens_totalFractionObject_of_isFlat B S hS hY hintY V c hc))

/-- The reading of a rational function on a flat affine chart is the evaluation on the spectrum
of the total ring of fractions, read in that ring — the statement
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_eq_ΓSpecIso` for a flat chart. -/
theorem rationalFunctionsToTotalFractionRingOfFlat_eq_ΓSpecIso
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    (V : BigFppfOver B S hS) [IsAffine V.left.1]
    [IsLocallyNoetherian V.left.1] (c : yoneda.obj V ⟶ Y) (hc : IsFlat B S hS c)
    (hm : FactorsThroughDenseOpens B S hS hY (totalFractionObject B S hS V)
      (yoneda.map (totalFractionObjectMap B S hS V) ≫ c))
    (g : rationalFunctions B S hS hY) :
    rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V c hc g =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(V.left.1, ⊤)))).hom
        (evalSiteRingHom B S hS hY hm g) := rfl

/-- **For an étale chart the reading on a flat chart is the reading of
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing`.** -/
theorem rationalFunctionsToTotalFractionRingOfFlat_of_isEtale
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    (V : BigFppfOver B S hS) [IsAffine V.left.1] [IsReduced V.left.1]
    [IsLocallyNoetherian V.left.1] (c : yoneda.obj V ⟶ Y) (hc : IsEtale B S hS c) :
    rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V c
        (isFlat_of_isEtale B S hS hc) =
      rationalFunctionsToTotalFractionRing B S hS hY V c hc := rfl

/-! ### The chart reading of the pullback of a rational function along a flat morphism -/

section Naturality

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hgen : pointsMap B S hS X f (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY)
    {U V : BigFppfOver B S hS} [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] [IsAffine V.left.1]
    [IsLocallyNoetherian V.left.1]

include hX hintX hintY hgen in
/-- **The chart reading of the pullback of a rational function, on a flat chart of the target.**
Let `f : X ⟶ Y` be a morphism of integral algebraic spaces carrying the generic point of `X` to
the generic point of `Y`, let `cU : U → X` be an étale chart and `cV : V → Y` a **flat** chart,
both with affine, locally Noetherian scheme, `U` reduced, let `j : U → V` be a morphism of the
site over `f` and suppose restriction of global sections along `j` carries nonzerodivisors to
nonzerodivisors. Then the reading of `g ∘ f` in `Q(Γ(U, 𝒪_U))` is the reading of `g` in
`Q(Γ(V, 𝒪_V))`, restricted along `j`. -/
theorem rationalFunctionsToTotalFractionRing_rationalFunctionMap_of_isFlat
    (cU : yoneda.obj U ⟶ X) (hcU : IsEtale B S hS cU)
    (cV : yoneda.obj V ⟶ Y) (hcV : IsFlat B S hS cV) (j : U ⟶ V)
    (hsq : yoneda.map j ≫ cV = cU ≫ f)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (g : rationalFunctions B S hS hY) :
    rationalFunctionsToTotalFractionRing B S hS hX U cU hcU
        (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
      chartFractionMap B S hS j hj
        (rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V cV hcV g) := by
  have hmU := factorsThroughDenseOpens_totalFractionObject B S hS hX U cU hcU
  have hmV := factorsThroughDenseOpens_totalFractionObject_of_isFlat B S hS hY hintY V cV hcV
  have hmUf := factorsThroughDenseOpens_comp_of_genericPoint_eq B S hS hX hY hintX hintY f hgen
    hmU
  have hmV' := hmV.comp B S hS hY (totalFractionObjectMapOfHom B S hS j hj)
  have hmor : yoneda.map (totalFractionObjectMapOfHom B S hS j hj) ≫
        (yoneda.map (totalFractionObjectMap B S hS V) ≫ cV) =
      (yoneda.map (totalFractionObjectMap B S hS U) ≫ cU) ≫ f := by
    rw [← Category.assoc, ← Functor.map_comp, totalFractionObjectMapOfHom_comp B S hS j hj,
      Functor.map_comp, Category.assoc, hsq, Category.assoc]
  rw [rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hX U cU hcU hmU,
    rationalFunctionsToTotalFractionRingOfFlat_eq_ΓSpecIso B S hS hY hintY V cV hcV hmV,
    evalSiteRingHom_rationalFunctionMap B S hS hX hY hintX hintY f hgen hmU g,
    ← evalSiteRingHom_congr_mor B S hS hY hmor hmV' hmUf g,
    evalSiteRingHom_naturality B S hS hY (totalFractionObjectMapOfHom B S hS j hj) hmV hmV' g]
  exact Scheme.ΓSpecIso_hom_appTop_ofHom_apply (chartFractionMap B S hS j hj) _

include hX hintX hintY hgen in
/-- **The reading of `g ∘ f` on an étale chart of the source is a fraction of global sections of
a flat chart of the target.** In the situation of
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionMap_of_isFlat`
there are global sections `s`, `t` of `𝒪_V` with `j^♯ t` a nonzerodivisor such that the reading
of `g ∘ f` in `Q(Γ(U, 𝒪_U))` is `j^♯ s / j^♯ t`. -/
theorem exists_rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat
    (cU : yoneda.obj U ⟶ X) (hcU : IsEtale B S hS cU)
    (cV : yoneda.obj V ⟶ Y) (hcV : IsFlat B S hS cV) (j : U ⟶ V)
    (hsq : yoneda.map j ≫ cV = cU ≫ f)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (g : rationalFunctions B S hS hY) :
    ∃ (s t : Γ(V.left.1, ⊤)) (ht : (j.left.1.appTop).hom t ∈ (Γ(U.left.1, ⊤))⁰),
      rationalFunctionsToTotalFractionRing B S hS hX U cU hcU
          (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
        IsLocalization.mk' (FractionRing Γ(U.left.1, ⊤)) ((j.left.1.appTop).hom s)
          ⟨(j.left.1.appTop).hom t, ht⟩ := by
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective (Γ(V.left.1, ⊤))⁰
    (rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V cV hcV g)
  refine ⟨s, t, hj t.2, ?_⟩
  rw [rationalFunctionsToTotalFractionRing_rationalFunctionMap_of_isFlat B S hS hX hY hintX
    hintY f hgen cU hcU cV hcV j hsq hj g, ← hst]
  simp only [chartFractionMap, IsLocalization.map_mk']
  rfl

end Naturality

/-! ### The reading on a chart of an irreducible component of a flat source -/

/-- **The reading of `g ∘ (i ≫ f)` on an étale chart of `X` is a fraction of global sections of
an étale chart of `XA`**, for `f : XA ⟶ Y` flat and `i : X ⟶ XA`. Let `Y` be integral, let
`f : XA ⟶ Y` be flat, let `i : X ⟶ XA` be a morphism with `X` integral and suppose the
composite carries the generic point of `X` to the generic point of `Y`. Let `cV : V → XA` be an
étale chart and `cU : U → X` an étale chart, both with affine, locally Noetherian scheme, `U`
reduced, let `j : U → V` be a morphism of the site over `i`, and suppose restriction of global
sections along `j` carries nonzerodivisors to nonzerodivisors. Then there are global sections
`s`, `t` of `𝒪_V` with `j^♯ t` a nonzerodivisor such that the reading of the pullback of a
rational function `g` of `Y` along `i ≫ f` in `Q(Γ(U, 𝒪_U))` is `j^♯ s / j^♯ t`. -/
theorem exists_rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_comp
    {XA : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXA : IsAlgebraicSpace B S hS XA) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y)
    (i : X ⟶ XA) (f : XA ⟶ Y) (hf : IsFlat B S hS f)
    (hgen : pointsMap B S hS X (i ≫ f) (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY)
    {U V : BigFppfOver B S hS} [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] [IsAffine V.left.1]
    [IsLocallyNoetherian V.left.1]
    (cU : yoneda.obj U ⟶ X) (hcU : IsEtale B S hS cU)
    (cV : yoneda.obj V ⟶ XA) (hcV : IsEtale B S hS cV) (j : U ⟶ V)
    (hsq : yoneda.map j ≫ cV = cU ≫ i)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (g : rationalFunctions B S hS hY) :
    ∃ (s t : Γ(V.left.1, ⊤)) (ht : (j.left.1.appTop).hom t ∈ (Γ(U.left.1, ⊤))⁰),
      rationalFunctionsToTotalFractionRing B S hS hX U cU hcU
          (rationalFunctionMap B S hS hX hY hintX hintY (i ≫ f) hgen g) =
        IsLocalization.mk' (FractionRing Γ(U.left.1, ⊤)) ((j.left.1.appTop).hom s)
          ⟨(j.left.1.appTop).hom t, ht⟩ :=
  exists_rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat B S hS hX hY
    hintX hintY (i ≫ f) hgen cU hcU (cV ≫ f)
    (isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS V) hXA hY cV f
      (isFlat_of_isEtale B S hS hcV) hf) j
    (by rw [← Category.assoc, hsq, Category.assoc]) hj g

end AlgebraicGeometry.Space

end

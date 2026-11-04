module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.SpecTotalFractionRing
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The rational functions of an algebraic space on an étale affine chart

Let `X` be an algebraic space over a scheme `S` and let `c : U → X` be an étale chart whose
scheme is affine, reduced and locally Noetherian — for instance an elementary étale
neighbourhood of a point of a locally Noetherian integral algebraic space. Write
`A = Γ(U, 𝒪_U)`, a reduced Noetherian ring.

The morphism `Spec Q(A) → U → X` factors through *every* dense open subspace of `X`. Indeed
`|c|` is open, because `c` is étale, so the preimage in `|U|` of the point set of a dense open
subspace of `|X|` is a dense open subset of `|U|`; and the image of `Spec Q(A) → U` consists
of generic points of irreducible components of `U`, which lie in every dense open subset.
Pulling rational functions back along that morphism therefore gives a ring homomorphism
`R(X) → Q(A)`.

This is the first half of the construction of Stacks 0ENK: the source's `R(X) → R(U)`,
composed with the identification of `R(U)` with the total ring of fractions of a local ring of
`U`. Here the target is the total ring of fractions of `A` itself, from which the local ring of
`U` at any point is reached by a localization, which preserves nonzerodivisors; no shrinking of
`U` is needed, and `U` is not assumed irreducible.

## Main definitions

* `AlgebraicGeometry.Space.totalFractionObject` is `Spec Q(Γ(U, 𝒪_U))` as an object of the big
  fppf site over `S`, and `AlgebraicGeometry.Space.totalFractionObjectMap` its morphism to `U`.
* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing` is the ring homomorphism
  `R(X) → Q(Γ(U, 𝒪_U))`.

## Main results

* `AlgebraicGeometry.Space.contains_specTotalFractionRing`: the spectrum of the total ring of
  fractions of the global sections of an affine object of the site is again in the site, being
  the spectrum of a localization.
* `AlgebraicGeometry.Space.factorsThroughDenseOpens_totalFractionObject`: the morphism
  `Spec Q(A) → X` factors through every dense open subspace.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The spectrum of the total ring of fractions of the global sections of an affine object of
the big fppf site is again an object of that site: it is the spectrum of a localization of the
global sections, which does not increase size beyond the site's cutoff. -/
theorem contains_specTotalFractionRing (U : BigFppfOver B S hS) [IsAffine U.left.1] :
    B.Contains (Spec (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))) := by
  have hU : (Spec (CommRingCat.of Γ(U.left.1, ⊤))).size < B.cutoff := by
    rw [Scheme.size_Spec]
    exact (Scheme.size_of_isAffine U.left.1) ▸ U.left.2
  exact Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (Γ(U.left.1, ⊤))⁰ (FractionRing Γ(U.left.1, ⊤)) hU

/-- The spectrum of the total ring of fractions of the global sections of an affine object of
the big fppf site, as an object of that site over `S`. -/
noncomputable def totalFractionObject (U : BigFppfOver B S hS) [IsAffine U.left.1] :
    BigFppfOver B S hS :=
  Over.mk (⟨U.left.1.fromSpecTotalFractionRing ≫ U.hom.1⟩ :
    B.obj (contains_specTotalFractionRing B S hS U) ⟶ B.obj hS)

/-- The canonical morphism from the spectrum of the total ring of fractions of the global
sections of an affine object of the big fppf site to that object. -/
noncomputable def totalFractionObjectMap (U : BigFppfOver B S hS) [IsAffine U.left.1] :
    totalFractionObject B S hS U ⟶ U :=
  Over.homMk (⟨U.left.1.fromSpecTotalFractionRing⟩ :
    B.obj (contains_specTotalFractionRing B S hS U) ⟶ U.left)

/-- The underlying morphism of schemes of `totalFractionObjectMap` is the canonical morphism
`Spec Q(Γ(U, 𝒪_U)) → U`. -/
@[simp]
theorem toScheme_map_totalFractionObjectMap (U : BigFppfOver B S hS) [IsAffine U.left.1] :
    (BigFppfOver.toScheme B S hS).map (totalFractionObjectMap B S hS U) =
      U.left.1.fromSpecTotalFractionRing := rfl

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The pullback of rational functions to an étale affine chart exists.** For an étale chart
`c : U → X` of an algebraic space whose scheme is affine, reduced and locally
Noetherian, the morphism `Spec Q(Γ(U, 𝒪_U)) → X` factors through every dense open subspace
of `X`.

The point set of a dense open subspace of `X` pulls back to a dense open subset of `|U|`,
because `|c|` is open by Stacks 03IR, and the image of `Spec Q(Γ(U, 𝒪_U))` in `|U|` consists
of generic points of irreducible components, which lie in every dense open subset. -/
theorem factorsThroughDenseOpens_totalFractionObject (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] (c : yoneda.obj U ⟶ X) (hc : IsEtale B S hS c) :
    FactorsThroughDenseOpens B S hS hX (totalFractionObject B S hS U)
      (yoneda.map (totalFractionObjectMap B S hS U) ≫ c) := by
  intro V hV
  refine (factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS _) V hV.1 _).2 ?_
  -- the point set of `V`, pulled back to the chart
  set R : Set (points B S hS X) := Set.range (pointsMap B S hS V.toFunctor V.ι) with hRdef
  have hRopen : IsOpen R := isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.1.2
  have hcopen : IsOpenMap (pointsMap B S hS (yoneda.obj U) c) :=
    isOpenMap_pointsMap_of_isEtale B S hS c (isAlgebraicSpace_yoneda B S hS U) hX hc
  set D : Set (points B S hS (yoneda.obj U)) := pointsMap B S hS (yoneda.obj U) c ⁻¹' R with hDdef
  have hDopen : IsOpen D := hRopen.preimage (continuous_pointsMap B S hS c)
  have hDdense : Dense D := hV.2.preimage hcopen
  -- transported to the scheme underlying the chart
  set e := schemePointsHomeomorph B S hS U with hedef
  have hD'open : IsOpen (e.symm ⁻¹' D) := hDopen.preimage e.symm.continuous
  have hD'dense : Dense (e.symm ⁻¹' D) :=
    hDdense.preimage e.symm.isOpenMap
  rintro y ⟨z, rfl⟩
  have hmem : U.left.1.fromSpecTotalFractionRing.base
      (schemePointsHomeomorph B S hS (totalFractionObject B S hS U) z) ∈ e.symm ⁻¹' D :=
    U.left.1.fromSpecTotalFractionRing_mem_of_dense hD'open hD'dense _
  have hnat : e (pointsMap B S hS (yoneda.obj (totalFractionObject B S hS U))
      (yoneda.map (totalFractionObjectMap B S hS U)) z) =
      U.left.1.fromSpecTotalFractionRing.base
        (schemePointsHomeomorph B S hS (totalFractionObject B S hS U) z) :=
    pointsToScheme_pointsMap B S hS (totalFractionObjectMap B S hS U) z
  rw [← hnat, Set.mem_preimage, e.symm_apply_apply] at hmem
  rw [pointsMap_comp_apply]
  exact hmem

/-- The ring homomorphism from the rational functions of an algebraic space to the
total ring of fractions of the global sections of an étale affine chart, obtained by pulling
rational functions back along the morphism `Spec Q(Γ(U, 𝒪_U)) → X`. -/
noncomputable def rationalFunctionsToTotalFractionRing (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] (c : yoneda.obj U ⟶ X) (hc : IsEtale B S hS c) :
    rationalFunctions B S hS hX →+* FractionRing Γ(U.left.1, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).hom.hom).comp
    (evalSiteRingHom B S hS hX
      (factorsThroughDenseOpens_totalFractionObject B S hS hX U c hc))

end AlgebraicGeometry.Space

end

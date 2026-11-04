module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ConormalNonvanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree

/-!
# The conormal comparison map of two curves is nonzero

In step 3 of [Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) the source asserts that
the comparison map of [Stacks, Tag 01R4]

`φ : γ^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}`

attached to the square of the two exceptional curves "is nonzero (as `f'` is an isomorphism in the
generic point of `E`)". This file proves that nonvanishing for a commutative square of two integral
closed subschemes `D ⊆ X'` and `D' ⊆ Y'`, with `D'` an effective Cartier divisor, under the
hypothesis that `g' : X' ⟶ Y'` is an isomorphism on the local ring at the generic point `η` of `D`
and that this local ring is not a field. In the situation of the source the first hypothesis is
item (2) of [Stacks, Tag 0BFP], and the second holds because the local ring at a codimension-one
point of a regular surface is a discrete valuation ring.

At `η` the ideal of `D` is the maximal ideal, and `g'` matches the local rings at the generic
points, so a local equation of `D'` pulls back to a generator of the maximal ideal at `η`; a
generator of a nonzero maximal ideal is not in its square, which is the chart condition of
`Stacks.Conormal.ne_zero_immersionConormalSheafMap_of_notMem_sq`.

## Main results

* `Stacks.Conormal.ker_stalkMap_subschemeι_genericPoint` — the ideal of an integral closed
  subscheme at its generic point is the maximal ideal of the ambient local ring, the quotient
  being the function field of the subscheme.
* `Stacks.Conormal.map_germ_eq_maximalIdeal_of_affineModel` — the same read on an affine chart:
  the ideal cutting the subscheme out on the chart generates that maximal ideal.
* `Stacks.Conormal.span_germ_eq_maximalIdeal_of_ideal_eq_span` — a local equation of an effective
  Cartier divisor generates the maximal ideal at the generic point of the divisor.
* `Stacks.Conormal.ne_zero_immersionConormalSheafMap_of_isIso_stalkMap` — the conormal comparison
  map of a square of two integral closed subschemes is nonzero when `g'` is an isomorphism on
  the local ring at the generic point and that local ring is not a field.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal

/-! ### The ideal of a closed subscheme at its generic point -/

/-- The kernel of the stalk map of the closed immersion of an integral closed subscheme at its
generic point is the maximal ideal of the local ring of the ambient scheme there. -/
public theorem ker_stalkMap_subschemeι_genericPoint {X : Scheme.{u}} (D : X.IdealSheafData)
    [AlgebraicGeometry.IsIntegral D.subscheme] :
    RingHom.ker (D.subschemeι.stalkMap (genericPoint D.subscheme)).hom =
      IsLocalRing.maximalIdeal
        (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) := by
  let _ : Field (ToType (D.subscheme.presheaf.stalk (genericPoint D.subscheme))) :=
    (isField_stalk_genericPoint D.subscheme).toField
  exact IsLocalRing.ker_eq_maximalIdeal _
    (D.subschemeι.stalkMap_surjective (genericPoint D.subscheme))

/-- On an affine open `U` of `X` on which `D ∩ U` is cut out by `I`, the ideal `I` generates the
maximal ideal of the local ring of `X` at the generic point of `D`. -/
public theorem map_germ_eq_maximalIdeal_of_affineModel {X : Scheme.{u}} (D : X.IdealSheafData)
    [AlgebraicGeometry.IsIntegral D.subscheme] (U : X.Opens) (hU : IsAffineOpen U)
    (I : Ideal Γ(X, U)) (e : pullback D.subschemeι U.ι ≅ Spec (.of (Γ(X, U) ⧸ I)))
    (he : pullback.snd D.subschemeι U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hmem : D.subschemeι.base (genericPoint D.subscheme) ∈ U) :
    I.map (X.presheaf.germ U (D.subschemeι.base (genericPoint D.subscheme)) hmem).hom =
      IsLocalRing.maximalIdeal
        (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) := by
  have hpre : IsAffineOpen (D.subschemeι ⁻¹ᵁ U) :=
    isAffineOpen_preimage_of_affineModel D.subschemeι U I e
  have hsurj := surjective_appLE_of_affineModel D.subschemeι U hU I e he
  have hker := Stacks.Flatness.ker_stalkMap_eq_map_germ D.subschemeι hU hpre le_rfl
    (show genericPoint D.subscheme ∈ D.subschemeι ⁻¹ᵁ U from hmem) hmem hsurj
  rw [ker_stalkMap_subschemeι_genericPoint D, ker_appLE_eq_of_affineModel
    D.subschemeι U hU I e he] at hker
  exact hker.symm

/-- A local equation `f` of an integral closed subscheme `D` on an affine open `V` generates the
maximal ideal of the local ring at the generic point of `D`. -/
public theorem span_germ_eq_maximalIdeal_of_ideal_eq_span {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsIntegral D.subscheme] (V : Y.Opens) (hV : IsAffineOpen V)
    (f : Γ(Y, V)) (hfspan : D.ideal ⟨V, hV⟩ = Ideal.span {f})
    (y : Y) (hy : y ∈ V) (hyeq : y = D.subschemeι.base (genericPoint D.subscheme)) :
    Ideal.span {(Y.presheaf.germ V y hy).hom f} =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  subst hyeq
  obtain ⟨J, eJ, heJ⟩ := exists_affineModel D.subschemeι V hV
  have hJ : J = Ideal.span {f} := by
    rw [← hfspan, ← AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app D ⟨V, hV⟩,
      ← ker_appLE_eq_of_affineModel D.subschemeι V hV J eJ heJ,
      Scheme.Hom.appLE_preimage_self]
  have hmap := map_germ_eq_maximalIdeal_of_affineModel D V hV J eJ heJ hy
  rw [hJ, Ideal.map_span, Set.image_singleton] at hmap
  exact hmap

/-! ### The comparison map of two curves in a square is nonzero -/

/-- Let `D ⊆ X'` and `D' ⊆ Y'` be integral closed subschemes with `D'` an effective Cartier
divisor, let `γ : D ⟶ D'` and `g' : X' ⟶ Y'` make the square commute, suppose `γ` carries the
generic point of `D` to that of `D'`, and suppose `g'` is an isomorphism on the local ring of `X'`
at the generic point `η` of `D`. If the local ring of `X'` at `η` is not a field, the comparison
map of [Stacks, Tag 01R4] attached to the square is nonzero. -/
public theorem ne_zero_immersionConormalSheafMap_of_isIso_stalkMap {X' Y' : Scheme.{u}}
    {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    [AlgebraicGeometry.IsIntegral D.subscheme] [AlgebraicGeometry.IsIntegral D'.subscheme]
    (hD' : Stacks.Divisors.IsEffectiveCartierDivisor D')
    (γ : D.subscheme ⟶ D'.subscheme) (g' : X' ⟶ Y')
    (hsq : D.subschemeι ≫ g' = γ ≫ D'.subschemeι)
    (hgen : γ.base (genericPoint D.subscheme) = genericPoint D'.subscheme)
    (hstalk : IsIso (g'.stalkMap (D.subschemeι.base (genericPoint D.subscheme))))
    (hmax : IsLocalRing.maximalIdeal
      (X'.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) ≠ ⊥) :
    Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι γ g'
      (Stacks.Immersion.toShHom_square hsq) ≠ 0 := by
  have hw : g'.base (D.subschemeι.base (genericPoint D.subscheme)) =
      D'.subschemeι.base (genericPoint D'.subscheme) := by
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hgen]
  obtain ⟨V, hV, hwV, f, -, hfspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D' hD'
      (D'.subschemeι.base (genericPoint D'.subscheme))
  have hgV : D.subschemeι.base (genericPoint D.subscheme) ∈ g' ⁻¹ᵁ V := by
    show g'.base (D.subschemeι.base (genericPoint D.subscheme)) ∈ V
    rwa [hw]
  obtain ⟨-, ⟨U, hU, rfl⟩, hηU, hUV'⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hgV (g' ⁻¹ᵁ V).isOpen
  have hUV : U ≤ g' ⁻¹ᵁ V := hUV'
  obtain ⟨I, e, he⟩ := exists_affineModel D.subschemeι U hU
  have hf0 : (D'.subschemeι.app V).hom f = 0 := by
    show f ∈ RingHom.ker (D'.subschemeι.app V).hom
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app D' ⟨V, hV⟩, hfspan]
    exact Ideal.mem_span_singleton_self f
  have ha' : (D.subschemeι.app U).hom
      ((X'.presheaf.map (homOfLE hUV).op).hom ((g'.app V).hom f)) = 0 := by
    have hn := congrArg
      (fun q : Γ(X', g' ⁻¹ᵁ V) ⟶ Γ(D.subscheme, D.subschemeι ⁻¹ᵁ U) =>
        q.hom ((g'.app V).hom f))
      (Scheme.Hom.naturality D.subschemeι (homOfLE hUV).op)
    simp only [CommRingCat.comp_apply] at hn
    rw [hn, app_app_eq_zero_of_square hsq V f hf0, map_zero]
  have haI : (X'.presheaf.map (homOfLE hUV).op).hom ((g'.app V).hom f) ∈ I := by
    rw [← ker_appLE_eq_of_affineModel D.subschemeι U hU I e he, Scheme.Hom.appLE_preimage_self]
    exact ha'
  have hYspan := span_germ_eq_maximalIdeal_of_ideal_eq_span D' V hV f hfspan
    (g'.base (D.subschemeι.base (genericPoint D.subscheme))) hgV hw
  have hmap : (IsLocalRing.maximalIdeal
        (Y'.presheaf.stalk (g'.base (D.subschemeι.base (genericPoint D.subscheme))))).map
      (g'.stalkMap (D.subschemeι.base (genericPoint D.subscheme))).hom =
      IsLocalRing.maximalIdeal
        (X'.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (g'.stalkMap (D.subschemeι.base (genericPoint D.subscheme)))).2
  have hXspan : Ideal.span
        {(X'.presheaf.germ U (D.subschemeι.base (genericPoint D.subscheme)) hηU).hom
          ((X'.presheaf.map (homOfLE hUV).op).hom ((g'.app V).hom f))} =
      IsLocalRing.maximalIdeal
        (X'.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) := by
    rw [X'.presheaf.germ_res_apply (homOfLE hUV) _ hηU,
      ← Scheme.Hom.germ_stalkMap_apply g' V _ hgV f, ← Set.image_singleton, ← Ideal.map_span,
      hYspan, hmap]
  have hne0 : (X'.presheaf.germ U (D.subschemeι.base (genericPoint D.subscheme)) hηU).hom
      ((X'.presheaf.map (homOfLE hUV).op).hom ((g'.app V).hom f)) ≠ 0 := by
    intro h0
    rw [h0] at hXspan
    exact hmax ((Ideal.span_singleton_eq_bot.mpr rfl).symm.trans hXspan).symm
  refine ne_zero_immersionConormalSheafMap_of_notMem_sq D.subschemeι D'.subschemeι γ g' hsq
    V f hf0 U hUV hU I e he ⟨_, haI⟩ rfl ?_
  exact notMem_sq_of_notMem_sq_of_map_le
    (X'.presheaf.germ U (D.subschemeι.base (genericPoint D.subscheme)) hηU).hom I _
    (le_of_eq (map_germ_eq_maximalIdeal_of_affineModel D U hU I e he hηU)) _
    (notMem_sq_maximalIdeal_of_span_eq _ hXspan hne0)

end Stacks.Conormal

end

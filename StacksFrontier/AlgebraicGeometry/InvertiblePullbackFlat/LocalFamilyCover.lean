module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkTransport
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.LocalFamilyMember
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MonoImageOpen
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing

/-!
# The penultimate paragraph of Tag 0BD7 at every point of `X`

`Stacks.InvertiblePullback.exists_mem_generatingLocus_restrictₛₗ_pullbackMeromorphicMul_eq`
produces the member of the family owed at one point of `X` from three inputs: an affine chart
with a generator at that point, the relation `r c = g u`, and the generic generator written as
the multiple `c` of the chart generator's germ. This file supplies all three at every point and
collects the members into a family.

The generator `m` of the generic stalk is chosen **once**, before the point is quantified: it is
`AlgebraicGeometry.genericStalkGenerator`, built from the trivialization of the generic fibre and
from no chart. That order is forced — the statement with `m` universally quantified is false, as
`LocalFamilyAssembly.lean` records.

## Main results

* `Stacks.InvertiblePullback`'s
  `exists_mem_generatingLocus_pullbackMeromorphicMul_genericStalkGenerator`: the member owed at a
  point `x`, for the chosen `m`, with no chart in the hypotheses.
* `Stacks.InvertiblePullback.exists_span_eq_top_isPullMeromorphicFamilyOn`: the family, indexed
  by the points of `X`, together with the generation property, the maximality of its opens, and
  the fact that `m` generates. This is the penultimate paragraph of [Stacks, Tag 0BD7].

## Implementation notes

The chart comes from `AlgebraicGeometry.exists_affine_chart_generator_mem`, which is exactly the
shape `AlgebraicGeometry.exists_isUnit_mul_eq_germ_generatorRatio` and
`AlgebraicGeometry.eq_smul_germ_genericStalkGenerator` need, and both are applied at the *same*
`hx : x ∈ U`, since the chart of the generic fibre is a function of that proof.

The relation `r c = g u` arrives with its two `algebraMap`s spelled through the composite algebra
`𝒪_{Y, φ(x)} → K(X)` that
`AlgebraicGeometry.exists_isUnit_mul_eq_germ_generatorRatio` introduces by `letI`, while the
local member asks for them spelled through `φ`'s stalk map. The two are the same ring
homomorphism by definition of that algebra structure, so the conversion is a `have`.

Each member is moved onto the *largest* open of `φ^{-1}(A)` carrying it, by
`Stacks.SheafOfModules.exists_le_forall_le_map_eq_app` applied to the monomorphism `ℒ ⟶ 𝒦_X(ℒ)`;
the two members have the same generating locus inside the smaller open, so the moved one still
generates at the point. That maximality is `hVmax` below and is what makes the agreement
hypothesis of
`Stacks.InvertiblePullback.exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn`
derivable: for a family on arbitrary opens it is false, as `LocalFamilyUnit.lean` records.

The tag is **withheld**: the family is indexed by the points of `X` and lives on arbitrary opens
of the preimages, neither of which [Stacks, Tag 0BD7] states; the assembly onto preimages is
`Stacks.InvertiblePullback.exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn`.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.InvertiblePullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
  [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (L : X.Modules) [L.IsQuasicoherent]
  (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
  (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
    (f.fiber (genericPoint Y)).presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
      (f.fiber (genericPoint Y)).IsSheaf)
    ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
  (hfib : ∀ y : Y, AlgebraicGeometry.IsIntegral (f.fiber y))

include hL hfib in
/-- **The member of the family owed at a point of `X`, for the chosen generic generator.** The
chart and the relation `r c = g u` of the penultimate paragraph of [Stacks, Tag 0BD7] are
produced here, so nothing but invertibility of `ℒ` and triviality on the generic fibre is
assumed. -/
theorem exists_mem_generatingLocus_pullbackMeromorphicMul_genericStalkGenerator
    (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) (x : X) :
    ∃ (A : Y.Opens) (V : X.Opens) (hVA : (V : Opens X.toRingedSpace.carrier) ≤
        ((f ⁻¹ᵁ A : X.Opens) : Opens X.toRingedSpace.carrier))
      (q : (totalQuotientSheafAsModule Y).val.obj (op A)) (t : L.val.obj (op V)),
      x ∈ V ∧ x ∈ generatingLocus L t ∧
        (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hVA).op
            ((pullbackMeromorphicMul f L (meromorphicSectionOfGenericStalk X L
              (genericStalkGenerator f L hgen x₀ hx₀))).val.app (op A) q)
          = (toMeromorphicSectionSheafAsModule X L).val.app (op V) t := by
  classical
  obtain ⟨V, U, hV, hU, e, hxU, ⟨genU⟩⟩ := exists_affine_chart_generator_mem f L hL x
  have hξU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hxU⟩
  have hgenU : x ∈ generatingLocus L genU.val :=
    mem_generatingLocus L hxU (notMem_maximalIdeal_smul_top_of_generator L genU x hxU)
  have hm := eq_smul_germ_genericStalkGenerator f hV hU e hxU L hgen hL genU x₀ hx₀ hξU
  obtain ⟨g, r, u, hg, _, hu, heq⟩ :=
    exists_isUnit_mul_eq_germ_generatorRatio f hV hU e hxU L hgen hL genU hfib x₀ hx₀
  have hgru : algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r)
        * (genericFiberStalkIsoFunctionField f x₀ hx₀).inv
            ((f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hxU) x₀
              (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hxU x₀ hx₀)
              (generatorRatio _ (genericFiberChartOpens f hV hU e hxU)
                (genericFiberChartGenerator f hV hU e hxU L hL genU)
                (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hxU))))
      = algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom g) *
        algebraMap (X.presheaf.stalk x) X.functionField u := heq
  exact exists_mem_generatingLocus_restrictₛₗ_pullbackMeromorphicMul_eq f L hxU hξU genU.val
    hgenU _ _ hm hg hu hgru

include hL hgen hfib in
/-- **The penultimate paragraph of [Stacks, Tag 0BD7].** There is a generator `m` of the stalk of
`ℒ` at the generic point of `X` and, for the meromorphic section it determines, a family of
meromorphic functions on the base whose products with that section are regular sections, indexed
by the points of `X`, with the member at `z` generating `ℒ` at `z`.

The generator is chosen before the point is quantified, which is what the statement demands and
what makes it true. -/
theorem exists_span_eq_top_isPullMeromorphicFamilyOn (hsurj : Function.Surjective f.base) :
    letI : Module (ringStalk X.toRingedSpace (genericPoint X))
        (grpStalk X.toRingedSpace L.val (genericPoint X)) :=
      stalkModule X.toRingedSpace L.val (genericPoint X)
    ∃ (m : grpStalk X.toRingedSpace L.val (genericPoint X)) (A : X → Y.Opens)
      (V : X → Opens X.toRingedSpace.carrier)
      (hVA : ∀ z : X, (V z : X.Opens) ≤ (f ⁻¹ᵁ A z : X.Opens))
      (q : ∀ z, (totalQuotientSheafAsModule Y).val.obj (op (A z)))
      (t : ∀ z, L.val.obj (op (V z))),
      Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤ ∧
        IsPullMeromorphicFamilyOn f L (meromorphicSectionOfGenericStalk X L m) hVA q t ∧
          IsMaximalPullMeromorphicFamilyOn f L (meromorphicSectionOfGenericStalk X L m) q t ∧
            ∀ z : X.toRingedSpace.carrier, z ∈ generatingLocus L (t z) := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_fiberι_base_eq_genericPoint f hsurj
  choose A V₀ hV₀A q t₀ _ hgL₀ hfam₀ using
    exists_mem_generatingLocus_pullbackMeromorphicMul_genericStalkGenerator f L hL hgen hfib x₀ hx₀
  choose V hVA t hfam hmax using fun z : X =>
    Stacks.SheafOfModules.exists_le_forall_le_map_eq_app
      (toMeromorphicSectionSheafAsModule X L) (mono_toMeromorphicSectionSheafAsModule X L hL)
      ((f ⁻¹ᵁ A z : X.Opens) : Opens X.toRingedSpace.carrier)
      ((pullbackMeromorphicMul f L (meromorphicSectionOfGenericStalk X L
        (genericStalkGenerator f L hgen x₀ hx₀))).val.app (op (A z)) (q z))
  have hgL : ∀ z : X, z ∈ generatingLocus L (t z) := by
    intro z
    obtain ⟨hV₀V, hres⟩ := hmax z (V₀ z) (hV₀A z) (t₀ z) (hfam₀ z)
    have hgl : generatingLocus L (t₀ z)
        = generatingLocus L (t z) ∩ ((V₀ z : Opens X.toRingedSpace.carrier) :
            Set X.toRingedSpace.carrier) := by
      rw [← hres]
      exact generatingLocus_restrictₛₗ L hV₀V (t z)
    exact (hgl.subset (hgL₀ z)).1
  exact ⟨genericStalkGenerator f L hgen x₀ hx₀, A, V, hVA, q, t,
    span_eq_top_genericStalkGenerator f L hgen x₀ hx₀, hfam, hmax, hgL⟩

end Stacks.InvertiblePullback

end

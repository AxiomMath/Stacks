module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassIntegral

/-!
# The order of vanishing is zero where the section generates the module

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`, let `ℒ` be an
invertible `𝒪_X`-module and let `s` be the chosen regular meromorphic section of `ℒ`.  At a prime
divisor `Z` with generic point `ξ` the canonical ratio `s / s_ξ` of Stacks 0EPR is the image of
the coefficient of `s` against the generator over `Spec(𝒪_{U, u})`, and where that coefficient is
a unit the order of vanishing `ord_{Z, ℒ}(s)` is zero.

This is the arithmetic half of the input of Stacks 0EPS: the geometric half,
`AlgebraicGeometry.Space.exists_isOpen_nonempty_generatesOnChart_of_isIntegralSpace`, produces a
nonempty open `U ⊆ |X|` each of whose points lies in the image of an étale chart over which `s`
generates `ℒ`, and this file turns a unit ratio at the generic point of a prime divisor into the
vanishing of its coefficient in `div_ℒ(s)`.

## Main results

* `AlgebraicGeometry.Space.generatesOnChart_of_hom`: generation of an invertible module by a
  meromorphic section is inherited by every chart over a chart over which it holds.
* `AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit` and
  `AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_coefficient`:
  the order of vanishing at the canonical ratio is zero where the ratio, respectively the
  coefficient of the section against the generator, is a unit.
* `AlgebraicGeometry.Space.exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit`: the
  nonempty open subspace whose complement carries the generic point of every prime divisor with a
  nonzero coefficient in `div_ℒ(s)`, given that the canonical ratio is a unit of `𝒪^h_{X, ξ}` at
  the generic point of every prime divisor lying in a chart over which `s` generates `ℒ`.

## Implementation notes

The hypothesis `hunit` of
`AlgebraicGeometry.Space.exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit` asks for
generation of `ℒ` by `s` over a chart `V` whose image contains the generic point `ξ` of a prime
divisor to be carried to `Spec(𝒪_{U, u})`, where `(U, u)` is the chosen affine elementary étale
neighbourhood of `ξ` and where the coefficient of Stacks 0EPR is formed.  `U` need not map into
`V`, so the transport is not along a morphism of charts and
`AlgebraicGeometry.Space.generatesOnChart_of_hom` does not apply.

The image of `Spec(𝒪_{U, u})` in `|X|` consists of generalizations of `ξ`, and an open set
containing a point contains its generalizations, so that image lies in the open image of `V`;
the fibre product `Spec(𝒪_{U, u}) ×_X V` is therefore an étale *covering* of
`Spec(𝒪_{U, u})`, and `AlgebraicGeometry.Space.smallBaseChange` turns `V` into a chart of
`Spec(𝒪_{U, u})` over it, exactly as
`AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointChartDiagram` does for the
morphism `Spec(𝒪_{X, η}) ⟶ X`.  Over the charts of a covering sieve the inverse image of a free
generator of `ℒ` is again a free generator, which is
`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`; and the
discrepancy between the generator so obtained and the one
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkGenerator` chooses is a unit, which is
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul`, so it does
not disturb unit-ness of the coefficient.  It then remains to descend: the coefficient over
`Spec(𝒪_{U, u})` itself is a unit as soon as it is one over a member of the covering sieve
meeting the closed point, `𝒪_{U, u}` and `𝒪^h_{X, ξ}` being local rings and the maps between
them local.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X)

/-! ### Generation is inherited by charts over the chart -/

include hX in
/-- **Generation is inherited by a chart over the chart.**  If a meromorphic section generates an
`𝒪_X`-module over an étale chart `V`, it generates it over every chart over `V`: the generator is
the restricted family and the presentation restricts by
`AlgebraicGeometry.Space.eval_eq_toMeromorphicSectionSheaf_tmul_restrict`. -/
theorem generatesOnChart_of_hom (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L) {V V' : SmallEtale B S hS X} (j : V' ⟶ V)
    (h : GeneratesOnChart B S hS hX L s V) :
    GeneratesOnChart B S hS hX L s V' := by
  obtain ⟨e, hcompat, hbij, hpres⟩ := h
  refine ⟨fun W k ↦ e W (k ≫ j), fun W W' k g ↦ ?_, fun W k ↦ hbij W (k ≫ j), ?_⟩
  · exact (hcompat W W' (k ≫ j) g).trans (congrArg (e W') (Category.assoc g k j).symm)
  · have hres := eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS X hX L s V e hcompat
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj.obj
        (op V)) hpres V' j
    refine hres.trans (congrArg (toMeromorphicSectionSheaf B S hS X hX L V') ?_)
    rw [map_one]
    exact congrArg (fun z : L.val.obj (op V') ↦ (1 ⊗ₜ[chartRing B S hS X hX V'] z :
        (meromorphicSectionModule B S hS X hX L).obj (op V')))
      (congrArg (e V') (Category.id_comp j).symm)

variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-! ### The order of vanishing at the canonical ratio -/

variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

/-- **The order of vanishing is zero where the canonical ratio is a unit of `𝒪^h_{X, ξ}`.**  This
is `AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit` at the canonical ratio
`s / s_ξ` of Stacks 0EPR, which on a regular meromorphic section is
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`. -/
theorem orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit
    (Z : PrimeDivisor B S hS X) (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t)
    {v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)} (hv : IsUnit v)
    (hvr : Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec) v) :
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L t
        (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) = 0 :=
  orderOfVanishingSection_eq_zero_of_isUnit.{u, u} B S hS hX hdec Z L t
    (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) hv
    ((Z.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hN t ht).trans hvr)

/-- **The order of vanishing is zero where the coefficient of the section against the generator
is a unit.**  The canonical ratio is then the image in `Q(𝒪^h_{X, ξ})` of a unit of
`𝒪^h_{X, ξ}`. -/
theorem orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_coefficient
    (Z : PrimeDivisor B S hS X) (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t)
    {w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec))}
    (hw : IsUnit w)
    (hwc : Z.genericStalkCoefficient B S hS hX hdec L hL t =
      algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
          (op (Z.genericStalkChart B S hS hX hdec)))
        ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec))) w) :
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L t
        (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) = 0 :=
  orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit B S hS hX hdec hInt hN Z L hL t ht
    (hw.map (Z.genericStalkSectionsToHenselian B S hS hX hdec))
    (by
      rw [PrimeDivisor.canonicalGenericRatio, hwc,
        Z.genericStalkMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hN w])

/-! ### The open subspace of Stacks 0EPS -/

include hX hInt hN in
/-- **The input of Stacks 0EPS for the chosen regular meromorphic section.**  A nonempty open
`U ⊆ |X|` whose complement contains the generic point of every prime divisor whose coefficient in
`div_ℒ(s)` is nonzero, given that at the generic point of a prime divisor lying in a chart over
which `s` generates `ℒ` the canonical ratio `s / s_ξ` is the image of a unit of `𝒪^h_{X, ξ}`.

The open subspace is the generating locus of
`AlgebraicGeometry.Space.exists_isOpen_nonempty_generatesOnChart_of_isIntegralSpace`. -/
theorem exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hunit : ∀ (W : PrimeDivisor B S hS X) (V : SmallEtale B S hS X),
      W.genericPoint B S hS X ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom) →
      GeneratesOnChart B S hS hX L (regularMeromorphicSection B S hS hX hInt hN L hL) V →
      ∃ v : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit v ∧
        W.canonicalGenericRatio B S hS hX hdec L hL hInt hN
            (regularMeromorphicSection B S hS hX hInt hN L hL) =
          algebraMap ↥(W.genericHenselianLocalRing B S hS hX hdec)
            (W.genericTotalFractionRing B S hS hX hdec) v) :
    ∃ U : Set (points B S hS X), IsOpen U ∧ U.Nonempty ∧
      ∀ W : PrimeDivisor B S hS X,
        divisorCoefficients.{u, u} B S hS hX hdec L
            (regularMeromorphicSection B S hS hX hInt hN L hL)
            (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN) W ≠ 0 →
          W.genericPoint B S hS X ∈ Uᶜ := by
  refine ⟨generatingLocus B S hS hX L (regularMeromorphicSection B S hS hX hInt hN L hL),
    isOpen_generatingLocus B S hS hX L _,
    nonempty_generatingLocus_of_isRegularMeromorphicSection B S hS hX L
      hInt.hasEtaleLocalProperty_isReduced hInt.irreducibleSpace.toNonempty hL _
      (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hN L hL),
    fun W hW ↦ ?_⟩
  by_contra hmem
  obtain ⟨V, hrange, hgen⟩ := not_not.1 hmem
  obtain ⟨v, hv, hvr⟩ := hunit W V hrange hgen
  exact hW (orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit B S hS hX hdec hInt hN
    W L hL _ (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hN L hL) hv
    hvr)

end AlgebraicGeometry.Space

end

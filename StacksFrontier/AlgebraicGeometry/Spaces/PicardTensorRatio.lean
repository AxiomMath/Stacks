module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassIntegral

/-!
# The canonical ratio of a product section at the generic point of a prime divisor

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`, let `ℒ` and `𝒩` be
invertible `𝒪_X`-modules and let `Z ⊂ X` be a prime divisor with generic point `ξ`. The
hypothesis `hst` of Stacks 0EPV asks that the ratio `s_{ℒ⊗𝒩} / s_{ξ,ℒ⊗𝒩}` of the chosen
section of `ℒ ⊗ 𝒩` be the product of the ratios of the chosen sections of `ℒ` and of `𝒩`.

This file reduces that hypothesis, at the *constructed* ratio
`AlgebraicGeometry.Space.canonicalLocalRatioFamily` of Stacks 0EPR, to a single identity
between the coefficients of Stacks 0EPR over the spectrum of the local ring of the chosen
affine elementary étale neighbourhood of `ξ`:

`a_{ℒ⊗𝒩}(s_{ℒ⊗𝒩}) = a_ℒ(s_ℒ) · a_𝒩(s_𝒩)`.

The ratio is the image of the coefficient under a ring homomorphism, so the reduction is
immediate; what the reduction buys is that the remaining identity no longer mentions
`Q(𝒪^h_{X, ξ})` and is a statement about free generators of the pullbacks to
`Spec(𝒪_{U, u})` only.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_of_eval_eq`: the coefficient
  of Stacks 0EPR is the unique meromorphic function with its defining property over *any* chart
  of `Spec(𝒪_{U, u})`, so any presentation of the pullback of a section over a chart as a
  multiple of the chosen generator there computes the restriction of the coefficient to that
  chart.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_smul_genericStalkGenerator` and
  `AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul`: two
  free generators of the pullback at `ξ` over any chart of `Spec(𝒪_{U, u})` differ by a unit of
  the regular functions there, and the coefficient changes by that unit.
* `AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq`: the
  *order of vanishing* read through the canonical ratio does not depend on the generator chosen
  at `ξ`, that unit having order of vanishing zero.
* `Space.PrimeDivisor.canonicalGenericRatio_mul_of_genericStalkCoefficient_mul` and
  `Space.PrimeDivisor.coe_canonicalLocalRatio_mul_of_genericStalkCoefficient_mul`:
  multiplicativity of the coefficient at `ξ` gives multiplicativity of the ratio there.
* `AlgebraicGeometry.Space.PrimeDivisor.coe_canonicalLocalRatio_mul_iff_canonicalGenericRatio_mul`:
  the hypothesis `hst` at one prime divisor is *equivalent* to multiplicativity of the
  constructed ratio there.
* `AlgebraicGeometry.Space.ratio_tensorModule_canonicalLocalRatioFamily` and
  `AlgebraicGeometry.Space.ratio_tensorModule_regularMeromorphicSection`: the hypothesis `hst`
  of Stacks 0EPV at the constructed ratio family, with the coefficient identity as its only
  remaining hypothesis.

## Implementation notes

The coefficient identity is *not* a consequence of the construction as it stands: the chosen
section of `ℒ ⊗ 𝒩` is an arbitrary regular meromorphic section, and the chosen free generator
of the pullback of `ℒ ⊗ 𝒩` to `Spec(𝒪_{U, u})` is an arbitrary one, so the two sides differ by
the unit of `𝒪_{U, u}` relating that generator to the product of the chosen generators of the
pullbacks of `ℒ` and of `𝒩`. Both choices must be made compatibly; see
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul` for the
measurement of the discrepancy.

Of the two choices only the choice of *section* matters for the Weil divisor: the generator's
discrepancy is a unit of `𝒪_{U, u}`, whose order of vanishing is zero, which is
`AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq`. So a
form of `hst` stated on orders of vanishing — or on the Weil divisor class, where the ratio of
two regular meromorphic sections of one module is absorbed — is insensitive to the
trivialisation, while the identity of ratios above is not.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (L N M : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hNinv : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (hM : IsInvertibleModule (B := B) ⟨X, hX⟩ M)
    (hInt : IsIntegralSpace B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-! ### The coefficient against the generator is determined by the pullback of the section -/

/-- **The coefficient `s / s_ξ` is the unique meromorphic function with its defining property,
over any chart of `Spec(𝒪_{U, u})`.** A presentation of the pullback of a meromorphic section
over a chart `W` as a multiple of the chosen generator there therefore computes the
*restriction* of the coefficient to `W`.

The chart is arbitrary, not the identity chart of `Spec(𝒪_{U, u})`, for the reason recorded on
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_spec_restrict`: a presentation
transported from an étale chart `V` of `X` is available only over a chart lying over both
`Spec(𝒪_{U, u})` and `V`, since `Spec(𝒪_{U, u})` need not map into `V`. -/
theorem PrimeDivisor.genericStalkCoefficient_eq_of_eval_eq
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec)
    (a : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op W))
    (ha : (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval (op W) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) W
        (a ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 W]
          Z.genericStalkGenerator B S hS hX hdec L hL W k :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
              (op W))) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map k.op).hom
        (Z.genericStalkCoefficient B S hS hX hdec L hL t) = a :=
  (Z.bijective_genericStalkTmul B S hS hX hdec L hL W k).1
    ((Z.genericStalkCoefficient_spec_restrict B S hS hX hdec L hL t W k).symm.trans ha)

/-- **Two free generators of the pullback of `ℒ` to `Spec(𝒪_{U, u})` over a chart `W` differ by
a unit of `𝒪_W`.** Each generates the sections over `W` freely, so each is a multiple of the
other and the two factors multiply to `1`.

The chart is arbitrary, not the identity chart of `Spec(𝒪_{U, u})`: the generator
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkGenerator` is chosen over every chart over the
identity one at once, and generates freely over each
(`AlgebraicGeometry.Space.PrimeDivisor.bijective_smul_genericStalkGenerator`), which is all this
uses. Comparing generators over a chart that is *not* the identity one is what reading a
presentation of the section transported from an étale chart of `X` needs.

The comparison of two free generators over one chart is
`AlgebraicGeometry.Space.exists_isUnit_smul_of_bijective_smul`, stated for any `𝒪_F`-module over
any chart of any algebraic space; this is it at the pullback of `ℒ` to `Spec(𝒪_{U, u})` and the
generator chosen there. -/
theorem PrimeDivisor.exists_isUnit_smul_genericStalkGenerator
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec)
    (g : ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L).val.obj
      (op W))
    (hg : Function.Bijective fun r : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 W ↦ r • g) :
    ∃ v : (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 W)ˣ,
      g = (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 W) •
        Z.genericStalkGenerator B S hS hX hdec L hL W k :=
  exists_isUnit_smul_of_bijective_smul B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) W
    (Z.genericStalkGenerator B S hS hX hdec L hL W k) g
    (Z.bijective_smul_genericStalkGenerator B S hS hX hdec L hL W k) hg

/-- **A presentation of the pullback of a section against any free generator computes the
coefficient up to a unit.** If the pullback of `t` to `Spec(𝒪_{U, u})` is, over a chart `W`, `a`
times a free generator `g` there, then the *restriction* to `W` of the coefficient of `t`
against the chosen generator `s_ξ` is `v · a` for the unit `v` of `𝒪_W` with `g = v · s_ξ|_W`.

The chart is arbitrary, not the identity chart of `Spec(𝒪_{U, u})`. That is what lets the
presentation come from an étale chart `V` of `X` rather than from `Spec(𝒪_{U, u})` itself: the
section generating `ℒ` over `V` is read on a chart lying over both, which is where the field
`generating` of `AlgebraicGeometry.Space.PicardDivisorData` has to read it.

This is the obstruction to the coefficient identity of
`AlgebraicGeometry.Space.ratio_tensorModule_canonicalLocalRatioFamily`: the generator chosen at
`ξ` for one module and the generator built from the generators chosen for two others agree only
up to such a `v`, and `AlgebraicGeometry.Space.PrimeDivisor.genericStalkTrivialisation`, which
makes the choice, makes it for each module separately. -/
theorem PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec)
    (g : ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L).val.obj
      (op W))
    (hg : Function.Bijective fun r : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 W ↦ r • g)
    (a : (meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op W))
    (ha : (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval (op W) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) W
        (a ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 W] g :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
              (op W))) :
    ∃ v : (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 W)ˣ,
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map k.op).hom
          (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
        algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 W)
          ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op W))
          (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 W) * a := by
  obtain ⟨v, hv⟩ := Z.exists_isUnit_smul_genericStalkGenerator B S hS hX hdec L hL W k g hg
  refine ⟨v, Z.genericStalkCoefficient_eq_of_eval_eq B S hS hX hdec L hL t W k _ (ha.trans ?_)⟩
  refine congrArg (toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 _ W) ?_
  rw [hv]
  exact meromorphicSectionModule_tmul_smul B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 _ W (v : _) a _

/-! ### The order of vanishing does not see the choice of generator -/

include hInt hNoeth in
/-- **The order of vanishing read through the canonical ratio does not depend on the generator
chosen at `ξ`.** If the pullback of a regular meromorphic section `t` to `Spec(𝒪_{U, u})` is `a`
times *some* free generator `g`, then the order of vanishing taken through any ratio sending `t`
to the image of `a` agrees with the one taken through the canonical ratio: the two coefficients
differ by a unit of `𝒪_{U, u}`, whose order of vanishing is zero.

This is what makes the choice made by
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkTrivialisation` harmless for divisors, even
though it is not harmless for ratios: in the identity `hst` of Stacks 0EPV only the choice of
*section* survives. -/
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t)
    (g : ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L).val.obj
      (op (Z.genericStalkChart B S hS hX hdec)))
    (hg : Function.Bijective fun r : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec) ↦ r • g)
    (a : (meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec)))
    (ha : (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval
        (op (Z.genericStalkChart B S hS hX hdec)) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
        (Z.genericStalkChart B S hS hX hdec)
        (a ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec)] g :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
              (op (Z.genericStalkChart B S hS hX hdec))))
    (ratio : LocalRatio.{u, u} B S hS hX hdec Z L)
    (hratio : (ratio t : Z.genericTotalFractionRing B S hS hX hdec) =
      Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hNoeth a) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L t
        (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec Z L t ratio := by
  have : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
  have : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
  have : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
  obtain ⟨v, hvW⟩ := Z.genericStalkCoefficient_eq_mul_of_eval_eq_smul B S hS hX hdec L hL t
    (Z.genericStalkChart B S hS hX hdec) (𝟙 (Z.genericStalkChart B S hS hX hdec)) g hg a ha
  have hv : Z.genericStalkCoefficient B S hS hX hdec L hL t =
      algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec))
        ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec)))
        (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
            (Z.genericStalkChart B S hS hX hdec)) * a := by
    have h := hvW
    simp only [op_id, CategoryTheory.Functor.map_id, RingCat.hom_id] at h
    exact h
  have hw : IsUnit (Z.genericStalkSectionsToHenselian B S hS hX hdec v.val) :=
    IsUnit.map _ v.isUnit
  have hstep : Z.canonicalGenericRatio B S hS hX hdec L hL hInt hNoeth t =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (Z.genericStalkSectionsToHenselian B S hS hX hdec v.val) *
        Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hNoeth a := by
    refine Eq.trans (congrArg (Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hNoeth)
      hv) ?_
    refine Eq.trans (map_mul (Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hNoeth)
      _ _) ?_
    exact congrArg (fun z ↦ z * Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hNoeth a)
      (Z.genericStalkMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hNoeth v.val)
  refine orderOfVanishingSection_unit_smul.{u, u} B S hS hX hdec Z L t ratio
    (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) hw ?_
  rw [Z.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth t ht, hstep, hratio]

/-! ### From the coefficients to the ratios -/

/-- **Multiplicativity of the coefficient at `ξ` gives multiplicativity of the ratio `s / s_ξ`
there.** The ratio is the image of the coefficient under the ring homomorphism
`Q(𝒪_{U, u}) → Q(𝒪^h_{X, ξ})`. The three modules are unrelated: only their coefficients at `ξ`
are compared. -/
theorem PrimeDivisor.canonicalGenericRatio_mul_of_genericStalkCoefficient_mul
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (st : MeromorphicSection.{u, u} B S hS X hX M)
    (h : Z.genericStalkCoefficient B S hS hX hdec M hM st =
      Z.genericStalkCoefficient B S hS hX hdec L hL s *
        Z.genericStalkCoefficient B S hS hX hdec N hNinv t) :
    Z.canonicalGenericRatio B S hS hX hdec M hM hInt hNoeth st =
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hNoeth s *
        Z.canonicalGenericRatio B S hS hX hdec N hNinv hInt hNoeth t := by
  rw [PrimeDivisor.canonicalGenericRatio, PrimeDivisor.canonicalGenericRatio,
    PrimeDivisor.canonicalGenericRatio, h, map_mul]

/-- **Stacks 0EPV, the hypothesis `hst` at one prime divisor and at the constructed ratio.**
If the coefficients at `ξ` of three regular meromorphic sections are multiplicative, then so
are the ratios `s / s_ξ` read as choices of generator in the sense of
`AlgebraicGeometry.Space.LocalRatio`. -/
theorem PrimeDivisor.coe_canonicalLocalRatio_mul_of_genericStalkCoefficient_mul
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (st : MeromorphicSection.{u, u} B S hS X hX M)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX N t)
    (hst : IsRegularMeromorphicSection.{u, u} B S hS X hX M st)
    (h : Z.genericStalkCoefficient B S hS hX hdec M hM st =
      Z.genericStalkCoefficient B S hS hX hdec L hL s *
        Z.genericStalkCoefficient B S hS hX hdec N hNinv t) :
    (Z.canonicalLocalRatio B S hS hX hdec M hM hInt hNoeth st :
        Z.genericTotalFractionRing B S hS hX hdec) =
      (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s :
          Z.genericTotalFractionRing B S hS hX hdec) *
        (Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t :
          Z.genericTotalFractionRing B S hS hX hdec) := by
  rw [Z.coe_canonicalLocalRatio B S hS hX hdec M hM hInt hNoeth st hst,
    Z.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s hs,
    Z.coe_canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t ht]
  exact Z.canonicalGenericRatio_mul_of_genericStalkCoefficient_mul B S hS hX hdec L N M hL hNinv
    hM hInt hNoeth s t st h

/-- **The hypothesis `hst` of Stacks 0EPV at one prime divisor is exactly multiplicativity of
the constructed ratio there.** For regular meromorphic sections the ratio read as a choice of
generator is the ratio `s / s_ξ` itself, so nothing is lost or gained by passing between the
two; what remains to be proved is therefore an identity between the images in `Q(𝒪^h_{X, ξ})`
of the coefficients of Stacks 0EPR, and nothing weaker. -/
theorem PrimeDivisor.coe_canonicalLocalRatio_mul_iff_canonicalGenericRatio_mul
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (st : MeromorphicSection.{u, u} B S hS X hX M)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX N t)
    (hst : IsRegularMeromorphicSection.{u, u} B S hS X hX M st) :
    (Z.canonicalLocalRatio B S hS hX hdec M hM hInt hNoeth st :
          Z.genericTotalFractionRing B S hS hX hdec) =
        (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s :
            Z.genericTotalFractionRing B S hS hX hdec) *
          (Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t :
            Z.genericTotalFractionRing B S hS hX hdec) ↔
      Z.canonicalGenericRatio B S hS hX hdec M hM hInt hNoeth st =
        Z.canonicalGenericRatio B S hS hX hdec L hL hInt hNoeth s *
          Z.canonicalGenericRatio B S hS hX hdec N hNinv hInt hNoeth t := by
  rw [Z.coe_canonicalLocalRatio B S hS hX hdec M hM hInt hNoeth st hst,
    Z.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s hs,
    Z.coe_canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t ht]

/-! ### The hypothesis `hst` of Stacks 0EPV at the constructed ratio family -/

/-- **Stacks 0EPV, the hypothesis `hst` at the constructed ratio family.** For any choice of a
regular meromorphic section of every invertible `𝒪_X`-module, the ratio of the chosen section of
`ℒ ⊗ 𝒩` at the generic point of every prime divisor is the product of the ratios of the chosen
sections of `ℒ` and of `𝒩`, provided the coefficients of Stacks 0EPR over `Spec(𝒪_{U, u})` are
multiplicative at every prime divisor.

The conclusion is the hypothesis of
`AlgebraicGeometry.Space.exists_ord_sub_eq_of_ratio_mul`, which turns it into the field
`exists_ord_sub_eq_tensorModule` of `AlgebraicGeometry.Space.PicardDivisorData` with `f = 1`,
the `ratio` there being the constructed family
`AlgebraicGeometry.Space.canonicalLocalRatioFamily` of Stacks 0EPR. -/
theorem ratio_tensorModule_canonicalLocalRatioFamily
    (sect : (P : Modules.{u, u} B S hS X hX) → IsInvertibleModule (B := B) ⟨X, hX⟩ P →
      MeromorphicSection.{u, u} B S hS X hX P)
    (hsect : ∀ (P : Modules.{u, u} B S hS X hX) (hP : IsInvertibleModule (B := B) ⟨X, hX⟩ P),
      IsRegularMeromorphicSection.{u, u} B S hS X hX P (sect P hP))
    (hcoeff : ∀ W : PrimeDivisor B S hS X,
      W.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
          (sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)) =
        W.genericStalkCoefficient B S hS hX hdec L hL (sect L hL) *
          W.genericStalkCoefficient B S hS hX hdec N hNinv (sect N hNinv)) :
    ∀ W : PrimeDivisor B S hS X,
      (canonicalLocalRatioFamily B S hS hX hdec (picardTensorModule B S hS hX L N)
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth W
            (sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)) :
          W.genericTotalFractionRing B S hS hX hdec) =
        (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hNoeth W (sect L hL) :
            W.genericTotalFractionRing B S hS hX hdec) *
          (canonicalLocalRatioFamily B S hS hX hdec N hNinv hInt hNoeth W (sect N hNinv) :
            W.genericTotalFractionRing B S hS hX hdec) :=
  fun W =>
    W.coe_canonicalLocalRatio_mul_of_genericStalkCoefficient_mul B S hS hX hdec L N
      (picardTensorModule B S hS hX L N) hL hNinv
      (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth (sect L hL)
      (sect N hNinv) (sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv))
      (hsect L hL) (hsect N hNinv)
      (hsect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)) (hcoeff W)

/-- **Stacks 0EPV, the hypothesis `hst` at the constructed section and the constructed ratio
family.** This is `AlgebraicGeometry.Space.ratio_tensorModule_canonicalLocalRatioFamily` at the
regular meromorphic section of Stacks 0EPQ, whose regularity discharges the hypothesis `hsect`:
the coefficient identity at the generic point of every prime divisor is all that is left of the
identity of ratios that `AlgebraicGeometry.Space.exists_ord_sub_eq_of_ratio_mul` turns into the
field `exists_ord_sub_eq_tensorModule` of `AlgebraicGeometry.Space.PicardDivisorData`. -/
theorem ratio_tensorModule_regularMeromorphicSection
    (hcoeff : ∀ W : PrimeDivisor B S hS X,
      W.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
          (regularMeromorphicSection B S hS hX hInt hNoeth _
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)) =
        W.genericStalkCoefficient B S hS hX hdec L hL
            (regularMeromorphicSection B S hS hX hInt hNoeth L hL) *
          W.genericStalkCoefficient B S hS hX hdec N hNinv
            (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)) :
    ∀ W : PrimeDivisor B S hS X,
      (canonicalLocalRatioFamily B S hS hX hdec (picardTensorModule B S hS hX L N)
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth W
            (regularMeromorphicSection B S hS hX hInt hNoeth _
              (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)) :
          W.genericTotalFractionRing B S hS hX hdec) =
        (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hNoeth W
            (regularMeromorphicSection B S hS hX hInt hNoeth L hL) :
            W.genericTotalFractionRing B S hS hX hdec) *
          (canonicalLocalRatioFamily B S hS hX hdec N hNinv hInt hNoeth W
            (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv) :
            W.genericTotalFractionRing B S hS hX hdec) :=
  ratio_tensorModule_canonicalLocalRatioFamily B S hS hX hdec L N hL hNinv hInt hNoeth
    (regularMeromorphicSection B S hS hX hInt hNoeth)
    (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth) hcoeff

end AlgebraicGeometry.Space

end

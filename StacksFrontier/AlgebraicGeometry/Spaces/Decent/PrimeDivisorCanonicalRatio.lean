module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGeneratorRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear

/-!
# The canonical ratio `s / s_ξ` of Stacks 0EPR

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`, let `ℒ` be an
invertible `𝒪_X`-module and let `Z ⊂ X` be a prime divisor with generic point `ξ`. This file
constructs the ratio `s / s_ξ` of Stacks 0EPR as a unit of the total ring of fractions
`Q(𝒪^h_{X, ξ})` and restates the conclusions of Stacks 0EPR at it.

The generator `s_ξ` is read on `Spec(𝒪_{U, u})` for the chosen affine elementary étale
neighbourhood `(U, u)` of `ξ`: the pullback of `ℒ` there is the structure sheaf, the local ring
`𝒪_{U, u}` having trivial Picard group, so a meromorphic section pulled back to
`Spec(𝒪_{U, u})` — which is defined, the morphism being flat — is `a · s_ξ` for exactly one
meromorphic function `a`, by the module analogue of Stacks 0EN6, part (2). That `a` lies in the
total ring of fractions of `𝒪_{U, u}`, again by Stacks 0EN6, part (2), and
`𝒪_{U, u} → 𝒪^h_{X, ξ}` carries nonzerodivisors to nonzerodivisors, so `a` has an image in
`Q(𝒪^h_{X, ξ})`; regularity of the section makes `a` a nonzerodivisor, hence a unit of a total
ring of fractions, hence its image a unit.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio` is the ratio `s / s_ξ` in
  `Q(𝒪^h_{X, ξ})`, `AlgebraicGeometry.Space.PrimeDivisor.canonicalLocalRatio` it read as a
  choice of generator in the sense of `AlgebraicGeometry.Space.LocalRatio`, and
  `AlgebraicGeometry.Space.canonicalLocalRatioFamily` the family of those over all prime
  divisors.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.coe_canonicalLocalRatio` and
  `AlgebraicGeometry.Space.PrimeDivisor.exists_eval_eq_tmul_canonicalGenericRatio` tie the ratio
  to the section it is taken of: it is the image of the coefficient of that section against the
  generator.
* `AlgebraicGeometry.Space.PrimeDivisor.isUnit_canonicalGenericRatio`: the ratio of a regular
  meromorphic section is a unit.
* `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_smul` and
  `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_smul_of_eval`: multiplying the
  section by a meromorphic function multiplies the ratio.
* `PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_length_sub_length`: the length
  formula of Stacks 0EPR for `ord_{Z,ℒ}(s)` at the canonical ratio.
* `PrimeDivisor.exists_orderOfVanishingSection_canonicalLocalRatio_eq_length_sub_length`: the
  canonical ratio is a fraction of nonzerodivisors, and the length formula holds for it.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
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
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- The ratio `s / s_ξ` of a meromorphic section of an invertible `𝒪_X`-module against the
generator of `ℒ` at the generic point of a prime divisor, as an element of `Q(𝒪^h_{X, ξ})`: the
coefficient of the section against the generator over `Spec(𝒪_{U, u})`, pushed along
`Q(𝒪_{U, u}) → Q(𝒪^h_{X, ξ})`. -/
@[stacks 0EPR "the ratio s/s_ξ in Q(O^h_{X, ξ}) of a meromorphic section of an invertible \
module against the generator at the generic point of a prime divisor, read on the spectrum of \
the local ring of an affine elementary étale neighbourhood"]
def PrimeDivisor.canonicalGenericRatio (t : MeromorphicSection.{u, u} B S hS X hX L) :
    Z.genericTotalFractionRing B S hS hX hdec :=
  Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
    (Z.genericStalkCoefficient B S hS hX hdec L hL t)

/-- The ratio `s / s_ξ` of a regular meromorphic section is a unit of `Q(𝒪^h_{X, ξ})`. -/
@[stacks 0EPR "the ratio s/s_ξ of a regular meromorphic section is a unit of Q(O^h_{X, ξ})"]
theorem PrimeDivisor.isUnit_canonicalGenericRatio
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t) :
    IsUnit (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) :=
  (Z.isUnit_genericStalkCoefficient B S hS hX hdec L hL hInt hN t ht).map _

/-- The choice of the generator `s_ξ`: the generator of `ℒ` at the generic
point of a prime divisor, read as the ratio `t ↦ t / s_ξ` in the units of `Q(𝒪^h_{X, ξ})` that
it assigns to a meromorphic section of `ℒ`. On a regular meromorphic section the value is the
ratio `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`. -/
@[stacks 0EPR "the generator s_ξ of an invertible module at the generic point of a prime \
divisor, read as the ratio family it assigns to meromorphic sections"]
def PrimeDivisor.canonicalLocalRatio : LocalRatio.{u, u} B S hS hX hdec Z L := fun t =>
  letI : Decidable (IsUnit (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t)) :=
    Classical.propDecidable _
  if h : IsUnit (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t) then h.unit else 1

/-- On a regular meromorphic section, the value of
`AlgebraicGeometry.Space.PrimeDivisor.canonicalLocalRatio` is the ratio
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`. -/
theorem PrimeDivisor.coe_canonicalLocalRatio (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t) :
    (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN t :
        Z.genericTotalFractionRing B S hS hX hdec) =
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t := by
  have h := Z.isUnit_canonicalGenericRatio B S hS hX hdec L hL hInt hN t ht
  have hval : Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN t = h.unit := dif_pos h
  rw [hval, IsUnit.unit_spec]

/-- The ratio is the image of the coefficient of the section against the generator: the
pullback of the section to `Spec(𝒪_{U, u})` is `a · s_ξ`, and the ratio is the image of `a` in
`Q(𝒪^h_{X, ξ})`. -/
theorem PrimeDivisor.exists_eval_eq_tmul_canonicalGenericRatio
    (t : MeromorphicSection.{u, u} B S hS X hX L) :
    ∃ a : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec)),
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t =
          Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN a ∧
        (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
              (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval
            (op (Z.genericStalkChart B S hS hX hdec)) =
          toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
            (Z.genericStalkChart B S hS hX hdec)
            (a ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec)]
              Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
                (𝟙 (Z.genericStalkChart B S hS hX hdec)) :
              (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
                (Z.genericStalkSpace B S hS hX hdec).2
                ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
                  (op (Z.genericStalkChart B S hS hX hdec))) :=
  ⟨Z.genericStalkCoefficient B S hS hX hdec L hL t, rfl,
    Z.genericStalkCoefficient_spec B S hS hX hdec L hL t⟩

/-- If the pullback of `t` to `Spec(𝒪_{U, u})` is `c` times the pullback of `t'` there, then the
ratio of `t` is the image of `c` times the ratio of `t'`. -/
@[stacks 0EPR "the ratio s/s_ξ is multiplied by c when the section is, which is the step by \
which Stacks 0EPT and Stacks 0EPV compare two sections through one generator"]
theorem PrimeDivisor.canonicalGenericRatio_smul
    (t t' : MeromorphicSection.{u, u} B S hS X hX L)
    (c : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec)))
    (hc : (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval
          (op (Z.genericStalkChart B S hS hX hdec)) =
      (meromorphicChartRingEquiv B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
          (Z.genericStalkChart B S hS hX hdec)).symm c •
        (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
              (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t').eval
          (op (Z.genericStalkChart B S hS hX hdec))) :
    Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t =
      Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN c *
        Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t' := by
  set E := meromorphicChartRingEquiv B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec) with hE
  have hstep : E.symm (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
      E.symm c * E.symm (Z.genericStalkCoefficient B S hS hX hdec L hL t') := by
    refine (Z.bijective_genericStalkTmul B S hS hX hdec L hL
      (Z.genericStalkChart B S hS hX hdec) (𝟙 (Z.genericStalkChart B S hS hX hdec))).1 ?_
    refine Eq.trans (Z.genericStalkCoefficient_spec B S hS hX hdec L hL t).symm ?_
    refine Eq.trans hc ?_
    refine Eq.trans (congrArg (fun z ↦ E.symm c • z)
      (Z.genericStalkCoefficient_spec B S hS hX hdec L hL t')) ?_
    refine Eq.trans (toMeromorphicSectionSheaf_smul B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2 _
      (Z.genericStalkChart B S hS hX hdec) (E.symm c) _).symm ?_
    exact congrArg (toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 _ (Z.genericStalkChart B S hS hX hdec))
      (meromorphicSectionModule_smul_tmul B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 _ (Z.genericStalkChart B S hS hX hdec) _
        (E.symm c) (E.symm (Z.genericStalkCoefficient B S hS hX hdec L hL t')) _ rfl)
  have hcoeff : Z.genericStalkCoefficient B S hS hX hdec L hL t =
      c * Z.genericStalkCoefficient B S hS hX hdec L hL t' := by
    have h := congrArg E hstep
    rwa [E.apply_symm_apply, map_mul E, E.apply_symm_apply, E.apply_symm_apply] at h
  rw [PrimeDivisor.canonicalGenericRatio, PrimeDivisor.canonicalGenericRatio, hcoeff, map_mul]

/-- The generic chart of a prime divisor as an object of the small étale site of `X`: the chosen
affine elementary étale neighbourhood `AlgebraicGeometry.Space.PrimeDivisor.genericChart` of `ξ`,
of which `𝒪^h_{X, ξ}` is the henselization, with its étale structure morphism. -/
def PrimeDivisor.genericEtaleChart : SmallEtale B S hS X :=
  ⟨CostructuredArrow.mk (Z.genericChart B S hS hX hdec).toSpace,
    (isEtale_iff_presheaf_of_yoneda B S hS (Z.genericChart B S hS hX hdec).toSpace).1
      (Z.genericChart B S hS hX hdec).etale_toSpace⟩

/-- The commuting square of étale scheme charts over `j : Spec(𝒪_{U, u}) ⟶ X` in which the chart
`Spec(𝒪_{U, u})` of `Spec(𝒪_{U, u})` lies over the chart `U` of `X`. -/
def PrimeDivisor.genericStalkChartDiagram :
    ChartDiagram B S hS (Z.genericStalkSpace B S hS hX hdec).1 X
      (Z.genericStalkMorphism B S hS hX hdec).hom where
  U := Z.genericStalkChart B S hS hX hdec
  V := Z.genericEtaleChart B S hS hX hdec
  g := Z.genericStalkSpecToChart B S hS hX hdec
  comm := Category.id_comp _

/-- If `t` is `c` times `t'` over the chosen affine elementary étale neighbourhood `U` of the
generic point, for `c` a meromorphic function on `U`, then the ratio of `t` is the image of the
pullback of `c` to `Spec(𝒪_{U, u})` times the ratio of `t'`. -/
@[stacks 0EPR "the ratio s/s_ξ is multiplied by c when the section is, with the scaling read \
over the chart of X rather than over the spectrum of the local ring -- the step by which \
Stacks 0EPT and Stacks 0EPV compare two sections through one generator"]
theorem PrimeDivisor.canonicalGenericRatio_smul_of_eval
    (t t' : MeromorphicSection.{u, u} B S hS X hX L)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj.obj
      (op (Z.genericEtaleChart B S hS hX hdec)))
    (hc : t.eval (op (Z.genericEtaleChart B S hS hX hdec)) =
      c • t'.eval (op (Z.genericEtaleChart B S hS hX hdec))) :
    Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t =
      Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
          (chartMeromorphicRingedSitePullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
            (Z.genericStalkChartDiagram B S hS hX hdec) c) *
        Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t' :=
  Z.canonicalGenericRatio_smul B S hS hX hdec L hL hInt hN t t' _
    (pullbackMeromorphicSection_eval_smul_chartDiagram B S hS
      (Z.genericStalkMorphism B S hS hX hdec) L
      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t t'
      (Z.genericStalkChartDiagram B S hS hX hdec)
      (Z.isAffine_genericStalkChart B S hS hX hdec)
      (Z.isAffine_genericChart B S hS hX hdec) c hc)

/-! ### The conclusions of Stacks 0EPR at the canonical ratio -/

/-- The family of canonical ratios over all prime divisors of `X`: the choice of a generator of
`ℒ` at the generic point of every prime divisor. -/
@[stacks 0EPR "the generators s_ξ at every prime divisor, read as the ratio family"]
def canonicalLocalRatioFamily : LocalRatioFamily.{u, u} B S hS hX hdec L := fun W =>
  W.canonicalLocalRatio B S hS hX hdec L hL hInt hN

include hInt hN in
/-- If the canonical ratio `s / s_ξ` of a meromorphic section is `a / b` with
`a` and `b` nonzerodivisors of `𝒪^h_{X,ξ}`, then `ord_{Z,ℒ}(s)` is the difference of the lengths
of the quotients of `𝒪^h_{X,ξ}` by `a` and by `b`. -/
@[stacks 0EPR "the length formula for ord_{Z,ℒ}(s) at the canonical ratio s/s_ξ on a locally \
Noetherian integral algebraic space"]
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_length_sub_length
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (a b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (hab : (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN t :
        Z.genericTotalFractionRing B S hS hX hdec) =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L t
        (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) =
      ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) -
        ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) :=
  have : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  orderOfVanishingSection_eq_length_sub_length.{u, u} B S hS hX hdec Z L t
    (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) a b hab

include hInt hN in
/-- The canonical ratio `s / s_ξ` is a fraction `a / b` of nonzerodivisors of `𝒪^h_{X,ξ}`, and for
one — hence for every — such presentation `ord_{Z,ℒ}(s)` is the difference of the lengths of the
quotients. -/
@[stacks 0EPR "existence of the presentation s/s_ξ = a/b by nonzerodivisors at the canonical \
ratio, with the length formula, on a locally Noetherian integral algebraic space"]
theorem PrimeDivisor.exists_orderOfVanishingSection_canonicalLocalRatio_eq_length_sub_length
    (t : MeromorphicSection.{u, u} B S hS X hX L) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
    ∃ a b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hdec),
      (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN t :
            Z.genericTotalFractionRing B S hS hX hdec) =
          IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
            (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b ∧
        orderOfVanishingSection.{u, u} B S hS hX hdec Z L t
            (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) =
          ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
              (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) -
            ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
              (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) :=
  have : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  exists_orderOfVanishingSection_eq_length_sub_length.{u, u} B S hS hX hdec Z L t
    (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN)

end AlgebraicGeometry.Space

end

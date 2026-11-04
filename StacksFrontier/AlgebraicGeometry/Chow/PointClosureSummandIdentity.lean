module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureFractionFieldOrder
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureRelativeClosure
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Transport

/-!
# The summand identity of Stacks 0GU9

Let `(S, δ)` be the base situation of chapter 42, let `p : X ⟶ S` be locally of finite type, let
`x` be a point of `X` of relative dimension `k + 2` and let `y` be a point of `X` of relative
dimension `k` with `x ⇝ y`. Write `W = closure {x}` for the integral closed subscheme spanned by
`x` and `A = 𝒪_{W, y}` for its local ring at `y`, a two-dimensional Noetherian local domain.

The proof of Stacks 0GU9 computes the coefficient at `y` of the composite of its two
differentials as a sum over the intermediate points `x'` of `W`, and recognizes that sum as the
one the local algebraic reciprocity of Stacks 0EAX sets to zero. Both sides of that recognition
are already in the library:

* the geometric summand is
  `Stacks.Chow.pointClosureOrdBoundaryTerm`, the coefficient at `y` of the pushed-forward
  principal divisor on `closure {x'}` of the tame-symbol boundary of the chain at `x`;
* the algebraic summand is
  `AlgebraicGeometry.localMilnorBoundaryOrder`, the order along `A ⧸ 𝔮` of the Milnor `K₂`
  boundary at the height-one prime `𝔮` of `A` corresponding to `x'`.

**This file proves that the two agree**, which is the one step the path to Stacks 0GUA was
missing. The main result is
`Stacks.Chow.pointClosureOrdBoundaryTerm_eq_localMilnorBoundaryOrder`.

## The two halves of the identification

Running the identification requires moving a Milnor K-class and an order of vanishing across four
identifications, two of rings and two of fields.

The Milnor K-class moves by `Stacks.Chow.milnorKTwoTameSymbol_ringEquiv`: the localization `A_𝔮`
is the local ring `𝒪_{W, x'}` by `Stacks.Chow.stalkLocalizationAtPrimeEquiv`, the canonical
fraction field of `A` is `κ(x)` by `Stacks.Chow.pointClosureFractionRingEquiv`, and the two
identifications are compatible over `A`, which is
`Stacks.Chow.pointClosureFractionRingEquiv_stalkLocalizationAtPrimeEquiv` and comes from the
uniqueness of a localization together with the fact that a germ reaches the function field by
specializing to the generic point.

The order of vanishing moves by `Stacks.Chow.ordFrac_ringEquiv`, whose input is again a
compatible pair: the ring `A ⧸ 𝔮` is the local ring of `closure {x'}` at `y` -- taken inside `W`
by `Stacks.Chow.quotStalkEquivIntermediatePointStalk` and then inside `X` by
`Stacks.Chow.integralComponentStalkEquiv` -- while the field `κ(𝔮)` is the function field of
`closure {x'}`, through `κ(x')`. That the resulting square commutes is
`Stacks.Chow.pointClosure_compat_square`. It is proved by taking a germ at `y` on `X`, which is
possible because the stalk map of a closed immersion is surjective, and then chasing the
naturality of stalk maps, of specialization maps and of residue fields; the heart of the chase is
`Stacks.Chow.pointClosureFunctionFieldEquiv_algebraMap_stalkMap`, which says that the
identification of Stacks 01RV sends the restriction to `closure {x'}` of a germ to the value of
that germ at `x'`.

## What is carried

No further input is assumed. The statements about one closure carry local Noetherianness of that
closure, which is what makes an order of vanishing defined; on the schemes of Stacks 0GUA it is
automatic, since a scheme locally of finite type over a locally Noetherian base is locally
Noetherian.

Nothing here asserts Stacks 0GU9 or Stacks 0GUA: no chain group of the tag is summed over, no
differential is composed with another, and the complex of Stacks 0GU9 does not appear. What is
proved is the identification of one summand with another.

## Main results

* `Stacks.Chow.ord_eq_toAdd_unzero_ordFrac` -- the order of vanishing of Stacks 02MD, read as the
  integer logarithm of a value of `Ring.ordFrac`.
* `Stacks.Chow.pointClosureFunctionFieldEquiv_eq_residue` -- the identification of Stacks 01RV of
  the function field of `closure {x}` with `κ(x)`, computed.
* `Stacks.Chow.pointClosureFunctionFieldEquiv_algebraMap_stalkMap` -- that identification on the
  restriction of a germ.
* `Stacks.Chow.pointClosureOrd_eq_ord` -- the coefficient at `y` of the divisor differential of
  Stacks 0GU3 is an order of vanishing on `closure {x'}`.
* `Stacks.Chow.pointClosure_compat_square` -- **the compatibility square** of the two
  identifications of `A ⧸ 𝔮` with the local ring of `closure {x'}` at `y`.
* `Stacks.Chow.ord_eq_residueUnitOrder` -- the order of vanishing of the transported symbol is
  the order of the symbol along `A ⧸ 𝔮`.
* `Stacks.Chow.pointClosureFractionRingEquiv_stalkLocalizationAtPrimeEquiv`,
  `Stacks.Chow.localMilnorBoundary_transport` -- the transport of the Milnor `K₂` boundary.
* `Stacks.Chow.pointClosureOrdBoundaryTerm_eq_localMilnorBoundaryOrder` -- **the summand
  identity**.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The order of vanishing as an integer logarithm -/

attribute [local instance] isIntegral_integralComponentAt

variable {Z : Scheme.{u}} {X : Scheme.{u}}

/-- **The order of vanishing of Stacks 02MD, read as an integer logarithm.** On a locally
Noetherian integral scheme, at a point of coheight one, `AlgebraicGeometry.Scheme.ord` of a
rational function with nonzero `Ring.ordFrac` is the integer logarithm of that value. This is the
shape in which the scheme-level order of vanishing meets the ring-level `Ring.ordFrac` of the
development. -/
theorem ord_eq_toAdd_unzero_ordFrac [IsIntegral Z] [IsLocallyNoetherian Z]
    {t : Z} (ht : Order.coheight t = 1) [Ring.KrullDimLE 1 ↥(Z.presheaf.stalk t)]
    {f : ↥Z.functionField} (h : Ring.ordFrac ↥(Z.presheaf.stalk t) f ≠ 0) :
    Z.ord f t = Multiplicative.toAdd (WithZero.unzero h) := by
  have hf : f ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at h
    exact h rfl
  rw [Scheme.ord_eq_unzero_ordHom ht hf]
  rfl

/-- Equal nonzero values have equal integer logarithms. -/
private theorem toAdd_unzero_eq {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a = b) :
    Multiplicative.toAdd (WithZero.unzero ha) = Multiplicative.toAdd (WithZero.unzero hb) := by
  subst h
  rfl

/-- On an integral scheme the identification of the rational functions with the residue field at
the generic point is the identification with the function field followed by the residue map. -/
theorem rationalFunctionsEquivResidueField_eq (W : Scheme.{u}) [IsIntegral W]
    (g : rationalFunctions W) :
    (rationalFunctionsEquivResidueField W).1 g =
      W.residue (genericPoint W) ((rationalFunctionsEquivFunctionField W).1 g) := rfl

/-- **Stacks 01RV, computed.** The identification of the function field of `closure {x}` with
`κ(x)` takes the residue at the generic point of `closure {x}`, undoes the isomorphism of residue
fields induced by the closed immersion, and transports along the equality of the generic point of
`closure {x}` with `x`. -/
theorem pointClosureFunctionFieldEquiv_eq_residue (x : X)
    (f : ↥((integralComponentAt x).subscheme.functionField)) :
    pointClosureFunctionFieldEquiv x f =
      (X.residueFieldCongr (genericPointOf_integralComponentAt x)).commRingCatIsoToRingEquiv
        ((RingEquiv.ofBijective
            ((integralComponentAt x).subschemeι.residueFieldMap
              (genericPoint (integralComponentAt x).subscheme)).hom
            (bijective_residueFieldMap_of_isClosedImmersion _ _)).symm
          ((integralComponentAt x).subscheme.residue
            (genericPoint (integralComponentAt x).subscheme) f)) := by
  have h1 : pointClosureFunctionFieldEquiv x f =
      (X.residueFieldCongr (genericPointOf_integralComponentAt x)).commRingCatIsoToRingEquiv
        ((RingEquiv.ofBijective
            ((integralComponentAt x).subschemeι.residueFieldMap
              (genericPoint (integralComponentAt x).subscheme)).hom
            (bijective_residueFieldMap_of_isClosedImmersion _ _)).symm
          ((rationalFunctionsEquivResidueField (integralComponentAt x).subscheme).1
            ((rationalFunctionsEquivFunctionField
              (integralComponentAt x).subscheme).1.symm f))) := rfl
  rw [h1, rationalFunctionsEquivResidueField_eq, RingEquiv.apply_symm_apply]


/-! ### The residue field of a height-one prime -/

/-- **A germ, read in the residue field of a height-one prime.** Let `x''` be a point of a scheme
`Z` and let `𝔮` be a height-one prime of `A = 𝒪_{Z, x''}`, cutting out the point `x'`. The image
of a germ `r` at `x''` in the residue field `κ(𝔮)`, transported along the identification of `A_𝔮`
with `𝒪_{Z, x'}`, is the residue at `x'` of the germ `r` specialized to `x'`.

This is one of the two compatibilities that
`Stacks.Chow.pointClosure_compat_square` is assembled from. -/
theorem residueField_mapEquiv_stalkLocalizationAtPrimeEquiv (x'' : Z)
    (q : {q : Ideal ↥(Z.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1})
    (r : ↥(Z.presheaf.stalk x'')) :
    letI : q.1.IsPrime := q.2.1
    IsLocalRing.ResidueField.mapEquiv (stalkLocalizationAtPrimeEquiv x'' q)
        (algebraMap (↥(Z.presheaf.stalk x'') ⧸ q.1) q.1.ResidueField
          (Ideal.Quotient.mk q.1 r)) =
      IsLocalRing.residue ↥(Z.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q))
        ((Z.presheaf.stalkSpecializes
          (specializes_intermediatePointOfHeightOnePrime x'' q)).hom r) := by
  let _ : q.1.IsPrime := q.2.1
  rw [Ideal.algebraMap_quotient_residueField_mk,
    IsScalarTower.algebraMap_apply ↥(Z.presheaf.stalk x'') (Localization.AtPrime q.1)
      q.1.ResidueField r, IsLocalRing.ResidueField.algebraMap_eq]
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue _) (stalkLocalizationAtPrimeEquiv_algebraMap x'' q r)


/-! ### The value of a germ at the generic point -/

/-- The inverse of the residue-field isomorphism of a closed immersion sends the residue of the
image of a germ to the residue of that germ. -/
private theorem symm_ofBijective_residue_stalkMap (x : X) (t : (integralComponentAt x).subscheme)
    (s : ↥(X.presheaf.stalk ((integralComponentAt x).subschemeι t))) :
    (RingEquiv.ofBijective ((integralComponentAt x).subschemeι.residueFieldMap t).hom
        (bijective_residueFieldMap_of_isClosedImmersion _ _)).symm
      ((integralComponentAt x).subscheme.residue t
        (((integralComponentAt x).subschemeι.stalkMap t).hom s)) =
      X.residue ((integralComponentAt x).subschemeι t) s := by
  rw [RingEquiv.symm_apply_eq]
  conv_lhs => rw [← CommRingCat.comp_apply, ← Scheme.residue_residueFieldMap,
    CommRingCat.comp_apply]
  rfl

/-- **The identification of Stacks 01RV sends the restriction of a germ to its value.** Let `w`
be a point of `X`, let `t` be a point of `closure {w}` and let `s` be a germ at the image of `t`
in `X`. Restricting `s` to `closure {w}`, reading the result in the function field of
`closure {w}` and identifying that with `κ(w)` gives the residue at `w` of the germ `s`
specialized to `w`.

The proof chases the naturality of the stalk map of the closed immersion against specialization,
then against the residue map, and finally composes the two specializations. -/
theorem pointClosureFunctionFieldEquiv_algebraMap_stalkMap (w : X)
    (t : (integralComponentAt w).subscheme)
    (hspec : w ⤳ (integralComponentAt w).subschemeι t)
    (s : ↥(X.presheaf.stalk ((integralComponentAt w).subschemeι t))) :
    pointClosureFunctionFieldEquiv w
        (algebraMap ↥((integralComponentAt w).subscheme.presheaf.stalk t)
          ↥((integralComponentAt w).subscheme.functionField)
          (((integralComponentAt w).subschemeι.stalkMap t).hom s)) =
      X.residue w ((X.presheaf.stalkSpecializes hspec).hom s) := by
  have hηt : genericPoint (integralComponentAt w).subscheme ⤳ t :=
    (genericPoint_spec (integralComponentAt w).subscheme).specializes trivial
  have h1 : algebraMap ↥((integralComponentAt w).subscheme.presheaf.stalk t)
      ↥((integralComponentAt w).subscheme.functionField)
      (((integralComponentAt w).subschemeι.stalkMap t).hom s) =
      ((integralComponentAt w).subscheme.presheaf.stalkSpecializes hηt).hom
        (((integralComponentAt w).subschemeι.stalkMap t).hom s) := rfl
  rw [pointClosureFunctionFieldEquiv_eq_residue, h1,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply (integralComponentAt w).subschemeι
      (genericPoint (integralComponentAt w).subscheme) t hηt s]
  have h4 : ∀ c : ↥(X.presheaf.stalk ((integralComponentAt w).subschemeι
        (genericPoint (integralComponentAt w).subscheme))),
      (X.residueFieldCongr (genericPointOf_integralComponentAt w)).commRingCatIsoToRingEquiv
          ((X.residue ((integralComponentAt w).subschemeι
            (genericPoint (integralComponentAt w).subscheme))) c) =
        (X.residue w) ((X.presheaf.stalkCongr
          (Inseparable.of_eq (genericPointOf_integralComponentAt w))).hom c) := fun c =>
    DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (X.residue_residueFieldCongr (genericPointOf_integralComponentAt w))) c
  rw [symm_ofBijective_residue_stalkMap, h4]
  have h5 : ((X.presheaf.stalkCongr
        (Inseparable.of_eq (genericPointOf_integralComponentAt w))).hom
        ((X.presheaf.stalkSpecializes
          (((integralComponentAt w).subschemeι.base.hom.map_specializes hηt))) s)) =
      (X.presheaf.stalkSpecializes hspec) s :=
    TopCat.Presheaf.stalkSpecializes_comp_apply X.presheaf
      (Inseparable.of_eq (genericPointOf_integralComponentAt w)).ge
      ((integralComponentAt w).subschemeι.base.hom.map_specializes hηt) s
  rw [h5]


/-! ### The coefficient as an order of vanishing -/

/-- **The coefficient of the divisor differential of Stacks 0GU3 is an order of vanishing.** The
coefficient at a point `y` of the pushed-forward principal divisor on `closure {x'}` of the
rational function attached to a degree-one Milnor K-class at `x'` is the order of vanishing of
Stacks 02MD of that rational function on `closure {x'}`, at the point `y` of that closure. -/
theorem pointClosureOrd_eq_ord (C : ChowSituation.{u}) (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (x' : X) [IsLocallyNoetherian (integralComponentAt x').subscheme]
    (u : MilnorKTheory ↥(X.residueField x') 1) {y : X}
    (hy : y ∈ closure ({x'} : Set X)) :
    pointClosureOrd C p x' u y =
      (integralComponentAt x').subscheme.ord
        ((pointClosureFunctionFieldEquiv x').symm
          ((Additive.toMul (milnorKTheoryOneAddEquiv ↥(X.residueField x') u) :
            (↥(X.residueField x'))ˣ) : ↥(X.residueField x')))
        (pointClosurePoint x' hy) := by
  have himg := principalDivisorPushforward_apply_image C p (integralComponentAt x')
    (integralComponentFunction x'
      (Additive.toMul (milnorKTheoryOneAddEquiv ↥(X.residueField x') u)))
    (pointClosurePoint x' hy)
  rw [subschemeι_pointClosurePoint] at himg
  rw [pointClosureOrd, himg, principalCycle_apply]
  rfl


/-! ### The residue-field identification on a residue -/

/-- **The identification of residue fields across a closed immersion, on a residue.** The
residue at a point `t` of `closure {x}` of the restriction of a germ `s` on `X`, read in `κ` of
the image of `t`, is the residue of `s` itself. -/
theorem pointClosureResidueFieldEquiv_residue (x : X)
    (t : (integralComponentAt x).subscheme)
    (h : (integralComponentAt x).subschemeι t ∈ closure ({x} : Set X))
    (s : ↥(X.presheaf.stalk ((integralComponentAt x).subschemeι t))) :
    pointClosureResidueFieldEquiv x h
        ((integralComponentAt x).subscheme.residue t
          (((integralComponentAt x).subschemeι.stalkMap t).hom s)) =
      X.residue ((integralComponentAt x).subschemeι t) s := by
  exact symm_ofBijective_residue_stalkMap x t s


/-! ### The compatibility of the two presentations of `A ⧸ 𝔮` -/

/-- **The compatibility square.** Let `x` be a point of `X`, let `x''` be a point of
`W = closure {x}` and let `𝔮` be a height-one prime of `A = 𝒪_{W, x''}`, cutting out the
intermediate point `x'` of `W`. There are two ways to send a germ at `x''` into the function field
of the closure of the image of `x'` in `X`: through the residue field `κ(𝔮)` of the prime and the
identifications of residue fields, or through the local ring of that closure and the canonical map
into its function field. They agree.

This is the compatibility that `Stacks.Chow.ordFrac_ringEquiv` consumes, and the reason the two
orders of vanishing of Stacks 0GU9 may be compared. The germ is written as the restriction of a
germ on `X`, which is possible because the stalk map of a closed immersion is surjective; the
left-hand side is then `Stacks.Chow.residueField_mapEquiv_stalkLocalizationAtPrimeEquiv` followed
by `Stacks.Chow.pointClosureResidueFieldEquiv_residue`, and the right-hand side collapses to
`Stacks.Chow.pointClosureFunctionFieldEquiv_algebraMap_stalkMap`. -/
theorem pointClosure_compat_square (x : X) (x'' : (integralComponentAt x).subscheme)
    (q : {q : Ideal ↥((integralComponentAt x).subscheme.presheaf.stalk x'') //
      q.IsPrime ∧ q.height = 1}) [q.1.IsPrime]
    (hmem : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ∈
      closure ({x} : Set X))
    (hsp : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ⤳
      (integralComponentAt x).subschemeι x'')
    (r₀ : ↥(X.presheaf.stalk ((integralComponentAt x).subschemeι x''))) :
    (pointClosureFunctionFieldEquiv ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))).symm
        (pointClosureResidueFieldEquiv x hmem
          (IsLocalRing.ResidueField.mapEquiv (stalkLocalizationAtPrimeEquiv x'' q)
            (algebraMap _ q.1.ResidueField (Ideal.Quotient.mk q.1
              (((integralComponentAt x).subschemeι.stalkMap x'').hom r₀))))) =
      algebraMap
        ↥((integralComponentAt ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))).subscheme.presheaf.stalk
            ((pointClosureInnerIso x
              (intermediatePointOfHeightOnePrime x'' q)).hom.base
                (intermediatePointClosurePoint x'' q)))
        ↥((integralComponentAt ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))).subscheme.functionField)
        (integralComponentStalkEquiv (integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q) (intermediatePointClosurePoint x'' q)
          (quotStalkEquivIntermediatePointStalk x'' q (Ideal.Quotient.mk q.1
            (((integralComponentAt x).subschemeι.stalkMap x'').hom r₀)))) := by
  rw [RingEquiv.symm_apply_eq]
  have hA := residueField_mapEquiv_stalkLocalizationAtPrimeEquiv x'' q
    (((integralComponentAt x).subschemeι.stalkMap x'').hom r₀)
  have hB := (Scheme.Hom.stalkSpecializes_stalkMap_apply (integralComponentAt x).subschemeι
    (intermediatePointOfHeightOnePrime x'' q) x''
    (specializes_intermediatePointOfHeightOnePrime x'' q) r₀).symm
  have hC := pointClosureResidueFieldEquiv_residue x
    (intermediatePointOfHeightOnePrime x'' q) hmem
    ((X.presheaf.stalkSpecializes ((integralComponentAt x).subschemeι.base.hom.map_specializes
      (specializes_intermediatePointOfHeightOnePrime x'' q))).hom r₀)
  have hLHS : pointClosureResidueFieldEquiv x hmem
      (IsLocalRing.ResidueField.mapEquiv (stalkLocalizationAtPrimeEquiv x'' q)
        (algebraMap _ q.1.ResidueField (Ideal.Quotient.mk q.1
          (((integralComponentAt x).subschemeι.stalkMap x'').hom r₀)))) =
      X.residue ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))
        ((X.presheaf.stalkSpecializes
          ((integralComponentAt x).subschemeι.base.hom.map_specializes
            (specializes_intermediatePointOfHeightOnePrime x'' q))).hom r₀) :=
    (congrArg (pointClosureResidueFieldEquiv x hmem)
      (hA.trans (congrArg (IsLocalRing.residue
        ↥((integralComponentAt x).subscheme.presheaf.stalk
          (intermediatePointOfHeightOnePrime x'' q))) hB))).trans hC
  have hD : quotStalkEquivIntermediatePointStalk x'' q (Ideal.Quotient.mk q.1
        (((integralComponentAt x).subschemeι.stalkMap x'').hom r₀)) =
      ((integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subschemeι.stalkMap
        (intermediatePointClosurePoint x'' q)).hom
        (((integralComponentAt x).subschemeι.stalkMap x'').hom r₀) :=
    quotStalkEquivClosureStalk_mk x'' ⟨q.1, q.2.1⟩ _
  have hE : ((integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subschemeι.stalkMap
        (intermediatePointClosurePoint x'' q)).hom
        (((integralComponentAt x).subschemeι.stalkMap x'').hom r₀) =
      (((integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subschemeι ≫
        (integralComponentAt x).subschemeι).stalkMap
          (intermediatePointClosurePoint x'' q)).hom r₀ := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hfg : (integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subschemeι ≫
        (integralComponentAt x).subschemeι =
      (pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom ≫
        (integralComponentAt ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))).subschemeι :=
    (integralComponentMap_subschemeι (integralComponentAt x).subschemeι
      (intermediatePointOfHeightOnePrime x'' q)).symm
  have hG : ∀ b, integralComponentStalkEquiv (integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q) (intermediatePointClosurePoint x'' q)
        (((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.stalkMap
          (intermediatePointClosurePoint x'' q)).hom b) = b := fun b =>
    stalkIsoOfIso_hom_stalkMap_apply (pointClosureInnerIso x
      (intermediatePointOfHeightOnePrime x'' q)) (intermediatePointClosurePoint x'' q) b
  have hpt : (integralComponentAt x).subschemeι x'' =
      (integralComponentAt ((integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q))).subschemeι
        ((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
          (intermediatePointClosurePoint x'' q)) :=
    (subschemeι_pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)
      (intermediatePointClosurePoint x'' q)).symm
  have hF : (((integralComponentAt (intermediatePointOfHeightOnePrime x'' q)).subschemeι ≫
        (integralComponentAt x).subschemeι).stalkMap
          (intermediatePointClosurePoint x'' q)).hom r₀ =
      ((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.stalkMap
        (intermediatePointClosurePoint x'' q)).hom
        (((integralComponentAt ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))).subschemeι.stalkMap
            ((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
              (intermediatePointClosurePoint x'' q))).hom
          ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom r₀)) := by
    rw [Scheme.Hom.stalkMap_congr_hom _ _ hfg, Scheme.Hom.stalkMap_comp]
    rfl
  have hspec2 : (integralComponentAt x).subschemeι
      (intermediatePointOfHeightOnePrime x'' q) ⤳
      (integralComponentAt ((integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q))).subschemeι
        ((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
          (intermediatePointClosurePoint x'' q)) := by
    rw [← hpt]
    exact hsp
  have hsq := pointClosureFunctionFieldEquiv_algebraMap_stalkMap
    ((integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q))
    ((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
      (intermediatePointClosurePoint x'' q)) hspec2
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom r₀)
  have hlast : (X.presheaf.stalkSpecializes hspec2).hom
        ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom r₀) =
      (X.presheaf.stalkSpecializes
        ((integralComponentAt x).subschemeι.base.hom.map_specializes
          (specializes_intermediatePointOfHeightOnePrime x'' q))).hom r₀ :=
    TopCat.Presheaf.stalkSpecializes_comp_apply X.presheaf hspec2
      (Inseparable.of_eq hpt).ge r₀
  refine hLHS.trans (Eq.symm ?_)
  rw [hD, hE, hF, hG]
  exact hsq.trans (congrArg (X.residue ((integralComponentAt x).subschemeι
    (intermediatePointOfHeightOnePrime x'' q))) hlast)


/-! ### The order of the transported symbol -/

/-- **The order of the transported symbol.** Let `d` be a unit of the residue field `κ(𝔮)` of a
height-one prime `𝔮` of `A = 𝒪_{W, x''}` and let `dB` be its image in `κ(x')` under the
identification of residue fields. Then the order of vanishing on the closure of the image of `x'`
in `X`, at the point of it below, of the rational function attached to `dB` equals the order of
`d` along `A ⧸ 𝔮`.

The two values are transported into one another by `Stacks.Chow.ordFrac_ringEquiv`, whose
compatibility hypothesis is `Stacks.Chow.pointClosure_compat_square`, and the scheme-level order
is read as an integer logarithm by `Stacks.Chow.ord_eq_toAdd_unzero_ordFrac`. -/
theorem ord_eq_residueUnitOrder (x : X)
    [IsLocallyNoetherian (integralComponentAt x).subscheme]
    (x'' : (integralComponentAt x).subscheme)
    (q : {q : Ideal ↥((integralComponentAt x).subscheme.presheaf.stalk x'') //
      q.IsPrime ∧ q.height = 1}) [q.1.IsPrime]
    (hmem : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ∈
      closure ({x} : Set X))
    (hsp : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ⤳
      (integralComponentAt x).subschemeι x'')
    [IsLocallyNoetherian (integralComponentAt ((integralComponentAt x).subschemeι
      (intermediatePointOfHeightOnePrime x'' q))).subscheme]
    (hdimV : Order.coheight ((pointClosureInnerIso x
      (intermediatePointOfHeightOnePrime x'' q)).hom.base
        (intermediatePointClosurePoint x'' q)) = 1)
    (hquot : Ring.KrullDimLE 1
      (↥((integralComponentAt x).subscheme.presheaf.stalk x'') ⧸ q.1))
    {d : q.1.ResidueFieldˣ}
    {dB : (IsLocalRing.ResidueField ↥((integralComponentAt x).subscheme.presheaf.stalk
      (intermediatePointOfHeightOnePrime x'' q)))ˣ}
    (hdB : Units.map (IsLocalRing.ResidueField.mapEquiv
        (stalkLocalizationAtPrimeEquiv x'' q) :
          q.1.ResidueField →+* IsLocalRing.ResidueField
            ↥((integralComponentAt x).subscheme.presheaf.stalk
              (intermediatePointOfHeightOnePrime x'' q))).toMonoidHom d = dB) :
    (integralComponentAt ((integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q))).subscheme.ord
      ((pointClosureFunctionFieldEquiv ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))).symm
        (pointClosureResidueFieldEquiv x hmem (dB : IsLocalRing.ResidueField
          ↥((integralComponentAt x).subscheme.presheaf.stalk
            (intermediatePointOfHeightOnePrime x'' q)))))
      ((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
        (intermediatePointClosurePoint x'' q)) =
      residueUnitOrder hquot d := by
  subst hdB
  let _ := hquot
  let _ : Ring.KrullDimLE 1 ↥((integralComponentAt ((integralComponentAt x).subschemeι
      (intermediatePointOfHeightOnePrime x'' q))).subscheme.presheaf.stalk
        ((pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
          (intermediatePointClosurePoint x'' q))) := krullDimLE_of_coheight_le hdimV.le
  let _ : Ring.KrullDimLE 1 ↥((integralComponentAt ((integralComponentAt x).subschemeι
      (intermediatePointOfHeightOnePrime x'' q))).subscheme.presheaf.stalk
        ((integralComponentIso (integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q)).hom.base
            (intermediatePointClosurePoint x'' q))) := krullDimLE_of_coheight_le hdimV.le
  have hE : ∀ r : ↥((integralComponentAt x).subscheme.presheaf.stalk x'') ⧸ q.1,
      ((IsLocalRing.ResidueField.mapEquiv (stalkLocalizationAtPrimeEquiv x'' q)).trans
          ((pointClosureResidueFieldEquiv x hmem).trans
            (pointClosureFunctionFieldEquiv ((integralComponentAt x).subschemeι
              (intermediatePointOfHeightOnePrime x'' q))).symm))
          (algebraMap _ q.1.ResidueField r) =
        algebraMap _ _ (((quotStalkEquivIntermediatePointStalk x'' q).trans
          (integralComponentStalkEquiv (integralComponentAt x).subschemeι
            (intermediatePointOfHeightOnePrime x'' q)
            (intermediatePointClosurePoint x'' q))) r) := by
    intro r
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨r₀, rfl⟩ := (integralComponentAt x).subschemeι.stalkMap_surjective x'' r'
    exact pointClosure_compat_square x x'' q hmem hsp r₀
  have hord := ordFrac_ringEquiv
    ((quotStalkEquivIntermediatePointStalk x'' q).trans
      (integralComponentStalkEquiv (integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q) (intermediatePointClosurePoint x'' q)))
    ((IsLocalRing.ResidueField.mapEquiv (stalkLocalizationAtPrimeEquiv x'' q)).trans
      ((pointClosureResidueFieldEquiv x hmem).trans
        (pointClosureFunctionFieldEquiv ((integralComponentAt x).subschemeι
          (intermediatePointOfHeightOnePrime x'' q))).symm)) hE (d : q.1.ResidueField)
  have hne : Ring.ordFrac (↥((integralComponentAt x).subscheme.presheaf.stalk x'') ⧸ q.1)
      (d : q.1.ResidueField) ≠ 0 :=
    ((Units.isUnit d).map (Ring.ordFrac
      (↥((integralComponentAt x).subscheme.presheaf.stalk x'') ⧸ q.1))).ne_zero
  have hne' : Ring.ordFrac ↥((integralComponentAt ((integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q))).subscheme.presheaf.stalk
          ((integralComponentIso (integralComponentAt x).subschemeι
            (intermediatePointOfHeightOnePrime x'' q)).hom.base
              (intermediatePointClosurePoint x'' q)))
        (((IsLocalRing.ResidueField.mapEquiv (stalkLocalizationAtPrimeEquiv x'' q)).trans
          ((pointClosureResidueFieldEquiv x hmem).trans
            (pointClosureFunctionFieldEquiv ((integralComponentAt x).subschemeι
              (intermediatePointOfHeightOnePrime x'' q))).symm)) (d : q.1.ResidueField)) ≠ 0 := by
    rw [hord]
    exact hne
  exact (ord_eq_toAdd_unzero_ordFrac hdimV hne').trans (toAdd_unzero_eq hne' hne hord)


/-! ### Compatibility of the fraction-field identifications -/

/-- **The two identifications of fraction fields are compatible.** The canonical fraction field
of `A = 𝒪_{W, x''}` is `κ(x)` by `Stacks.Chow.pointClosureFractionRingEquiv`, and the localization
`A_𝔮` is the local ring at the intermediate point by
`Stacks.Chow.stalkLocalizationAtPrimeEquiv`; the square they form with the maps from `A_𝔮`
commutes.

Two maps out of a localization agreeing on the ring are equal, so it is enough to check this on a
germ at `x''`, where both sides send it to the image in `κ(x)` of its germ at the generic point;
that is the composition of two specialization maps. This is the compatibility that
`Stacks.Chow.milnorKTwoTameSymbol_ringEquiv` consumes. -/
theorem pointClosureFractionRingEquiv_stalkLocalizationAtPrimeEquiv (x : X)
    [IsLocallyNoetherian (integralComponentAt x).subscheme]
    (x'' : (integralComponentAt x).subscheme)
    (q : {q : Ideal ↥((integralComponentAt x).subscheme.presheaf.stalk x'') //
      q.IsPrime ∧ q.height = 1}) [q.1.IsPrime]
    (a : Localization.AtPrime q.1) :
    pointClosureFractionRingEquiv x x''
        (algebraMap (Localization.AtPrime q.1)
          (FractionRing ↥((integralComponentAt x).subscheme.presheaf.stalk x'')) a) =
      pointClosureFunctionFieldEquiv x (algebraMap
        ↥((integralComponentAt x).subscheme.presheaf.stalk
          (intermediatePointOfHeightOnePrime x'' q))
        ↥((integralComponentAt x).subscheme.functionField)
        (stalkLocalizationAtPrimeEquiv x'' q a)) := by
  have key : ∀ a₀ : ↥((integralComponentAt x).subscheme.presheaf.stalk x''),
      pointClosureFractionRingEquiv x x''
          (algebraMap (Localization.AtPrime q.1)
            (FractionRing ↥((integralComponentAt x).subscheme.presheaf.stalk x''))
            (algebraMap _ (Localization.AtPrime q.1) a₀)) =
        pointClosureFunctionFieldEquiv x (algebraMap
          ↥((integralComponentAt x).subscheme.presheaf.stalk
            (intermediatePointOfHeightOnePrime x'' q))
          ↥((integralComponentAt x).subscheme.functionField)
          (stalkLocalizationAtPrimeEquiv x'' q (algebraMap _ (Localization.AtPrime q.1) a₀))) := by
    intro a₀
    rw [← IsScalarTower.algebraMap_apply, pointClosureFractionRingEquiv_algebraMap,
      stalkLocalizationAtPrimeEquiv_algebraMap]
    refine congrArg (pointClosureFunctionFieldEquiv x) ?_
    rw [algebraMap_stalk_functionField, algebraMap_stalk_functionField]
    exact (TopCat.Presheaf.stalkSpecializes_comp_apply (integralComponentAt x).subscheme.presheaf
      ((genericPoint_spec (integralComponentAt x).subscheme).specializes trivial)
      (specializes_intermediatePointOfHeightOnePrime x'' q) a₀).symm
  have hhom : ((pointClosureFractionRingEquiv x x'').toRingHom.comp
        (algebraMap (Localization.AtPrime q.1)
          (FractionRing ↥((integralComponentAt x).subscheme.presheaf.stalk x'')))) =
      ((pointClosureFunctionFieldEquiv x).toRingHom.comp (algebraMap
          ↥((integralComponentAt x).subscheme.presheaf.stalk
            (intermediatePointOfHeightOnePrime x'' q))
          ↥((integralComponentAt x).subscheme.functionField))).comp
        (stalkLocalizationAtPrimeEquiv x'' q).toRingHom :=
    IsLocalization.ringHom_ext q.1.primeCompl (RingHom.ext key)
  exact DFunLike.congr_fun hhom a


/-! ### Transport of the boundary -/

/-- **The Milnor `K₂` boundary of Stacks 0GU9, transported to the height-one prime.** Let `α` be
a degree-two Milnor K-class of `κ(x)`. Transporting `α` to the canonical fraction field of
`A = 𝒪_{W, x''}`, taking its boundary at a height-one prime `𝔮`, and reading the value in `κ(x')`
gives the tame-symbol boundary of `α` at the intermediate point `x'` itself.

This is `Stacks.Chow.milnorKTwoTameSymbol_ringEquiv` read at the two identifications of this
situation. -/
theorem localMilnorBoundary_transport (x : X)
    [IsLocallyNoetherian (integralComponentAt x).subscheme]
    (x'' : (integralComponentAt x).subscheme)
    (q : {q : Ideal ↥((integralComponentAt x).subscheme.presheaf.stalk x'') //
      q.IsPrime ∧ q.height = 1}) [q.1.IsPrime]
    (hB : ringKrullDim ↥((integralComponentAt x).subscheme.presheaf.stalk
      (intermediatePointOfHeightOnePrime x'' q)) = 1)
    (α : MilnorKTheory ↥(X.residueField x) 2) :
    milnorKOneRingEquiv (IsLocalRing.ResidueField.mapEquiv (stalkLocalizationAtPrimeEquiv x'' q))
        (localMilnorBoundary q
          ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv x x'')).symm α)) =
      stalkMilnorBoundary (pointClosureFunctionFieldEquiv x)
        (intermediatePointOfHeightOnePrime x'' q) hB α := by
  let _ := stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (intermediatePointOfHeightOnePrime x'' q)
  have _ := isFractionRing_stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (intermediatePointOfHeightOnePrime x'' q)
  have h := milnorKTwoTameSymbol_ringEquiv (stalkLocalizationAtPrimeEquiv x'' q)
    (pointClosureFractionRingEquiv x x'')
    (pointClosureFractionRingEquiv_stalkLocalizationAtPrimeEquiv x x'' q)
    (ringKrullDim_localizationAtPrime_heightOne q) hB
    ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv x x'')).symm α)
  rwa [AddEquiv.apply_symm_apply] at h


/-! ### K-theory bookkeeping -/

/-- The transport of a degree-one Milnor K-group along an isomorphism of fields is the map of
unit groups, read through the identification of the degree-one Milnor K-group with the unit
group. -/
theorem toMul_milnorKOneRingEquiv {k₁ k₂ : Type u} [Field k₁] [Field k₂] (φ : k₁ ≃+* k₂)
    (u : MilnorKTheory k₁ 1) :
    Additive.toMul (milnorKTheoryOneAddEquiv k₂ (milnorKOneRingEquiv φ u)) =
      Units.map (φ : k₁ →+* k₂).toMonoidHom
        (Additive.toMul (milnorKTheoryOneAddEquiv k₁ u)) := by
  have h : milnorKOneRingEquiv φ u = (milnorKTheoryOneAddEquiv k₂).symm
      (MulEquiv.toAdditive (Units.mapEquiv φ.toMulEquiv)
        (milnorKTheoryOneAddEquiv k₁ u)) := rfl
  rw [h, AddEquiv.apply_symm_apply]
  rfl

/-- The transport of a degree-one Milnor K-class used by the first differential of Stacks 0GU9
is likewise the map of unit groups. -/
theorem toMul_milnorKOneTransport {k₁ k₂ : Type u} [Field k₁] [Field k₂] (φ : k₁ ≃+* k₂)
    (u : MilnorKTheory k₁ 1) :
    Additive.toMul (milnorKTheoryOneAddEquiv k₂ (milnorKOneTransport φ u)) =
      Units.map (φ : k₁ →+* k₂).toMonoidHom
        (Additive.toMul (milnorKTheoryOneAddEquiv k₁ u)) := by
  have h : milnorKOneTransport φ u = (milnorKTheoryOneAddEquiv k₂).symm
      (MonoidHom.toAdditive (Units.map (φ : k₁ →+* k₂).toMonoidHom)
        (milnorKTheoryOneAddEquiv k₁ u)) := rfl
  rw [h, AddEquiv.apply_symm_apply]
  rfl

/-- The image in `X` of a point of `closure {x}` lies in `closure {x}`: the range of the closed
immersion is that closure. -/
theorem subschemeι_mem_closure (x : X) (t : (integralComponentAt x).subscheme) :
    (integralComponentAt x).subschemeι t ∈ closure ({x} : Set X) := by
  have h : (integralComponentAt x).subschemeι t ∈
      Set.range (integralComponentAt x).subschemeι.base := ⟨t, rfl⟩
  rwa [(integralComponentAt x).range_subschemeι, coe_support_integralComponentAt x] at h


/-! ### The summand identity -/

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- **The summand identity, at a height-one prime.** Let `x` be a point of `X`, let `x''` be a
point of `W = closure {x}` and let `𝔮` be a height-one prime of `𝒪_{W, x''}`, cutting out the
intermediate point `x'`. The coefficient, at the image of `x''`, of the pushed-forward principal
divisor on the closure of the image of `x'` of the local tame-symbol boundary of a degree-two
Milnor K-class `α` of `κ(x)` equals the order along the quotient by `𝔮` of the Milnor `K₂`
boundary at `𝔮` of the transport of `α`.

The class is transported by `Stacks.Chow.localMilnorBoundary_transport` and the order by
`Stacks.Chow.ord_eq_residueUnitOrder`. -/
theorem pointClosureOrd_pointClosureMilnorBoundary_eq (x : X)
    [IsLocallyNoetherian (integralComponentAt x).subscheme]
    (x'' : (integralComponentAt x).subscheme)
    (q : {q : Ideal ↥((integralComponentAt x).subscheme.presheaf.stalk x'') //
      q.IsPrime ∧ q.height = 1}) [q.1.IsPrime]
    (hmem : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ∈
      closure ({x} : Set X))
    (hsp : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ⤳
      (integralComponentAt x).subschemeι x'')
    [IsLocallyNoetherian (integralComponentAt ((integralComponentAt x).subschemeι
      (intermediatePointOfHeightOnePrime x'' q))).subscheme]
    (hdimV : Order.coheight ((pointClosureInnerIso x
      (intermediatePointOfHeightOnePrime x'' q)).hom.base
        (intermediatePointClosurePoint x'' q)) = 1)
    (hw : (pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
        (intermediatePointClosurePoint x'' q) =
      pointClosurePoint ((integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q)) (specializes_iff_mem_closure.mp hsp))
    (hdim2 : ringKrullDim ↥((integralComponentAt x).subscheme.presheaf.stalk x'') = 2)
    (hB : ringKrullDim ↥((integralComponentAt x).subscheme.presheaf.stalk
      (intermediatePointOfHeightOnePrime x'' q)) = 1)
    (α : MilnorKTheory ↥(X.residueField x) 2) :
    pointClosureOrd C p ((integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q))
        (pointClosureMilnorBoundary C p x hmem hB α)
        ((integralComponentAt x).subschemeι x'') =
      localMilnorBoundaryOrder hdim2 q
        ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv x x'')).symm α) := by
  have h1 := toMul_milnorKOneRingEquiv (IsLocalRing.ResidueField.mapEquiv
    (stalkLocalizationAtPrimeEquiv x'' q))
    (localMilnorBoundary q ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv x x'')).symm α))
  rw [localMilnorBoundary_transport x x'' q hB α] at h1
  have hord := ord_eq_residueUnitOrder x x'' q hmem hsp hdimV
    (krullDimLE_one_quotient_heightOne hdim2 q) h1.symm
  rw [hw] at hord
  have h2 := toMul_milnorKOneTransport (pointClosureResidueFieldEquiv x hmem)
    (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x)
      (intermediatePointOfHeightOnePrime x'' q) hB α)
  have hpcmb : pointClosureMilnorBoundary C p x hmem hB α =
      milnorKOneTransport (pointClosureResidueFieldEquiv x hmem)
        (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x)
          (intermediatePointOfHeightOnePrime x'' q) hB α) := rfl
  rw [pointClosureOrd_eq_ord C p _ _ (specializes_iff_mem_closure.mp hsp), hpcmb, h2]
  exact hord


/-- **The summand identity of Stacks 0GU9.** Let `x` be a point of relative dimension `k + 2`
specializing to a point `y` of relative dimension `k`, so that the local ring `A` of
`W = closure {x}` at `y` is two-dimensional, and let `𝔮` be a height-one prime of `A`. The
contribution to the composite of the two differentials of the pair consisting of `x` and the
intermediate point cut out by `𝔮` equals the contribution of `𝔮` to the local algebraic
reciprocity of Stacks 0EAX, for the transport of the chain's class at `x` to the canonical
fraction field of `A`.

This is the identification that the proof of Stacks 0GU9 performs when it reads its displayed sum
as the sum of that reciprocity. -/
theorem pointClosureOrdBoundaryTerm_eq_localMilnorBoundaryOrder (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k) (x : pointsOfDimension C p (k + 2))
    (y : pointsOfDimension C p k) (hxy : (x.1 : X) ⤳ (y.1 : X))
    [IsLocallyNoetherian (integralComponentAt (x.1 : X)).subscheme]
    (hdim2 : ringKrullDim ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy))) = 2)
    (q : {q : Ideal ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy))) //
        q.IsPrime ∧ q.height = 1}) :
    pointClosureOrdBoundaryTerm C p k ξ y.1 x
        (intermediatePointOfDimension C p ((mem_pointsOfDimension C p).mp x.2)
          (specializes_iff_mem_closure.mp hxy)
          (heightOnePrimeEquivIntermediatePoint hdim2 q)) =
      localMilnorBoundaryOrder hdim2 q
        ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv (x.1 : X)
          (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)))).symm (ξ.1 x)) := by
  let _ : q.1.IsPrime := q.2.1
  have hmem := subschemeι_mem_closure (x.1 : X)
    (intermediatePointOfHeightOnePrime
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)
  have hsp : (integralComponentAt (x.1 : X)).subschemeι
      (intermediatePointOfHeightOnePrime
        (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q) ⤳ (y.1 : X) :=
    (specializes_intermediatePointOfHeightOnePrime _ q).map
      (integralComponentAt (x.1 : X)).subschemeι.continuous
  have hB : ringKrullDim ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (intermediatePointOfHeightOnePrime
        (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)) = 1 :=
    ringKrullDim_stalk_intermediatePoint_eq_one
      (isImmediateSpecialization_genericPoint_intermediatePointOfHeightOnePrime _ q)
  let _ : IsLocallyNoetherian (integralComponentAt ((integralComponentAt (x.1 : X)).subschemeι
      (intermediatePointOfHeightOnePrime
        (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q))).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((integralComponentAt ((integralComponentAt (x.1 : X)).subschemeι
        (intermediatePointOfHeightOnePrime
          (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q))).subschemeι ≫ p)
  have hw := pointClosureInnerIso_pointClosurePoint (x.1 : X)
    (intermediatePointOfHeightOnePrime
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)
    (specializes_intermediatePointOfHeightOnePrime _ q).mem_closure
    (specializes_iff_mem_closure.mp hsp)
  have hrel := relativeDimension_intermediatePoint C p ((mem_pointsOfDimension C p).mp x.2)
    (specializes_iff_mem_closure.mp hxy) (heightOnePrimeEquivIntermediatePoint hdim2 q)
  have hdimV : Order.coheight ((pointClosureInnerIso (x.1 : X)
      (intermediatePointOfHeightOnePrime
        (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)).hom.base
          (pointClosurePoint (intermediatePointOfHeightOnePrime
            (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)
              (specializes_intermediatePointOfHeightOnePrime _ q).mem_closure)) = 1 := by
    rw [hw]
    refine coheight_pointClosurePoint_eq_one_of_relativeDimension_sub_eq_one C p hsp ?_
    have hrel' : relativeDimension C.dimensionFunction p
        ((integralComponentAt (x.1 : X)).subschemeι (intermediatePointOfHeightOnePrime
          (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)) = k + 1 := hrel
    rw [hrel', (mem_pointsOfDimension C p).mp y.2]
    ring
  have hxx' : (x.1 : X) ⤳ (integralComponentAt (x.1 : X)).subschemeι
      (intermediatePointOfHeightOnePrime
        (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q) :=
    specializes_iff_mem_closure.mpr hmem
  rw [pointClosureOrdBoundaryTerm, pointClosureOrdHom_apply,
    pointwiseMilnorBoundaryTerm_of_specializes C p k ξ x
      (intermediatePointOfDimension C p ((mem_pointsOfDimension C p).mp x.2)
        (specializes_iff_mem_closure.mp hxy) (heightOnePrimeEquivIntermediatePoint hdim2 q))
      hxx' hB]
  exact pointClosureOrd_pointClosureMilnorBoundary_eq C p (x.1 : X)
    (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q hmem hsp hdimV hw
    hdim2 hB (ξ.1 x)

end Stacks.Chow

end

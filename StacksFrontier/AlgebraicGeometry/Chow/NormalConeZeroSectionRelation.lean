module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeFunctorial
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNestedZeroSection
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSection
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom

/-!
# The relation between the normal cones of two nested effective Cartier divisors

Let `(S, δ)` be the base situation of chapter 42, let `X` be an integral scheme locally of finite
type over `S` of δ-dimension `n`, and let `Z ⊆ Y ⊆ X` be closed subschemes which are both
effective Cartier divisors in `X`. The normal cone `C_YX` is a line bundle over `Y`, with zero
section `o : Y ⟶ C_YX`, and [Stacks, Tag 0FEB] states

    `o^*[C_ZX]_n = [C_ZY]_{n-1}` in `CH_{n-1}(Y ×_{o, C_YX} C_ZX)`.

This file sets up the two sides of that identity; the identity itself is
`Stacks.Chow.gysinBivariantCap_fundamentalChowClass_normalCone`.

## Main definitions

* `Stacks.Chow.zeroSectionDivisorSheaf` and `Stacks.Chow.zeroSectionDivisorSection`: the
  invertible module `𝒪(o(Y))` on `C_YX` and its canonical section, which present `o(Y)` as the
  zero scheme of a section of an invertible module — the shape the Gysin cap operation of
  [Stacks, Tag 0B79] is written at.
* `Stacks.Chow.zeroSectionToZeroScheme`: the identification of `Y` with that zero scheme.
* `Stacks.Chow.normalConeOfNestedToAmbient`: the canonical morphism `C_ZY ⟶ C_ZX`.
* `Stacks.Chow.normalConeToZeroFibre`: the morphism `C_ZY ⟶ Y ×_{o, C_YX} C_ZX` that the source
  leaves implicit, built from the factorization of `C_ZY ⟶ C_ZX ⟶ C_YX` through `o`.

## Main results

* `Stacks.Chow.zeroSectionToZeroScheme_comp_gysinTripleInclusion`: the identification of `Y` with
  the zero scheme carries the inclusion of the zero scheme back to `o`.
* `Stacks.Chow.isClosedImmersion_normalConeOfNestedToAmbient`: the canonical morphism
  `C_ZY ⟶ C_ZX` is a closed immersion.
* `Stacks.Chow.normalConeToZeroFibre_fst`, `Stacks.Chow.normalConeToZeroFibre_snd` and
  `Stacks.Chow.isClosedImmersion_normalConeToZeroFibre`: the components of
  `C_ZY ⟶ Y ×_{o, C_YX} C_ZX` are the canonical morphisms, and it is a closed immersion.
* `Stacks.Chow.normalConeZeroSectionGysinRelation_hom_ext`: a morphism with those two components
  is unique.

## How the two sides of the identity are written

**The left-hand side.** The identity is stated through the cap operation of the bivariant class
`o^* ∈ A^1(Y ⟶ C_YX)` of [Stacks, Tag 0B79] rather than through the class itself. The cap
operation, `Stacks.Chow.gysinBivariantCap`, is unconditional, and
`Stacks.Chow.IsGysinBivariantClass` says that a bivariant class is *the* Gysin class exactly when
its cap operation is that one; by `Stacks.Chow.BivariantClass.ext` at most one class satisfies
that. So `o^* ∩ -` is `Stacks.Chow.gysinBivariantCap` at the divisor `o(Y) ⊆ C_YX` and at the
test morphism `C_ZX ⟶ C_YX`, and the identity is stated against it, with no hypothesis
asserting that the class exists.

That cap operation is written at a divisor presented as the zero scheme of a section of an
invertible module (the triple of Definition 02T8), while `o(Y)` arrives as an ideal sheaf — the
kernel of the closed immersion `o`, shown to be an effective Cartier divisor by
`Stacks.Conormal.isEffectiveCartierDivisor_ker_normalConeZeroSection`. The presentation is the
canonical one: `𝒪(o(Y))` with its canonical section, whose zero scheme is `o(Y)` by
`Stacks.Divisors.zeroScheme_canonicalSection`. Nothing about the divisor is assumed.

**The right-hand side.** `[C_ZY]_{n-1}` is the cycle of [Stacks, Tag 02QU] associated to `C_ZY`
as a closed subscheme of `Y ×_{o, C_YX} C_ZX`, read modulo rational equivalence. The closed
immersion that makes `C_ZY` such a subscheme is the one the source leaves implicit, and it is
constructed here rather than assumed: `C_ZY` maps to `C_ZX` by
`Stacks.Conormal.normalConeMapOfSquare` for the square `Z = Z`, `Y ⊆ X`, and the composite
`C_ZY ⟶ C_ZX ⟶ C_YX` lands in the zero section, so the two of them lift to
`ι : C_ZY ⟶ Y ×_{o, C_YX} C_ZX`. That lift is `Stacks.Chow.normalConeToZeroFibre`; it is pinned
to the canonical maps by its two components and is therefore the only such morphism
(`Stacks.Chow.normalConeZeroSectionGysinRelation_hom_ext`). Both sides of the identity live in
`CH_{n-1}(Y ×_{o, C_YX} C_ZX)` exactly as in the source, and nothing about `ι` is assumed.

**The two facts `ι` rests on.** They are the scheme-level readings of the conormal sequence of
[Stacks, Tag 06AE].

* **`C_ZY ⟶ C_ZX` is a closed immersion**
  (`Stacks.Chow.isClosedImmersion_normalConeOfNestedToAmbient`). What this needs is the graded
  form of the degree-one surjectivity of [Stacks, Tag 06AE] together with the statement that the
  morphism of relative spectra attached to a surjection of algebras is a closed immersion. The
  graded form is `Stacks.Conormal.surjective_nestedConormalHom_map` — on a conormal chart the map
  `𝒞_{Z/X,n} ⟶ 𝒞_{Z/Y,n}` is surjective on sections in every degree, because on an affine chart of
  `X` the `n`-th power of the ideal of `Z` surjects onto the `n`-th power of the ideal of `Z` in
  `Y` (`Stacks.Conormal.exists_mem_chartIdealPow`) and
  `Stacks.Conormal.ConormalAlgebraHom.IsCanonical` computes the map on those classes. The second
  is `Stacks.RelativeSpec.isClosedImmersion_pairToHom`, applied in
  `Stacks.Conormal.isClosedImmersion_normalConeMap`.
* **The composite `C_ZY ⟶ C_ZX ⟶ C_YX` factors through the zero section**
  (`Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection`). Both sides are morphisms
  into the relative spectrum `C_YX` of `𝒞_{Y/X,*}`, so by [Stacks, Tag 01LV] each is
  `Stacks.RelativeSpec.pairToHom` of a relative-spectrum pair and the identity is an identity of
  pairs. It follows from this chain:

  - the factorization is equivalent to the vanishing of the *module component* of the pair that
    the functor of points of the total space of the conormal line bundle attaches to the composite
    (`Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection_iff`, with the morphism to
    the base pinned by `Stacks.Conormal.normalConeNested_comp_normalConeToBase`), so no comparison
    of two `Σ`-types with propositionally equal first components is needed and nothing above
    degree one is;
  - that vanishing is equivalent to a vanishing on the sections over the **affine** opens of `Y`
    in degree one
    (`Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection_iff_affineOpens`), which is
    the granularity at which the pair of a morphism of relative spectra can be computed. The
    reduction is the basis-of-opens extensionality principle
    `Stacks.BasisRestriction.moduleSheafHom_ext_onBasis`, the hom-level reading of
    [Stacks, Tag 009U], at the basis of affine opens;
  - the pair of the composite is computed by peeling one factor at a time: a composite of
    morphisms of relative spectra over *different* bases is itself one
    `Stacks.RelativeSpec.pairToHom`, of the pulled-back pair
    (`Stacks.RelativeSpec.comp_pairToHom`), and pulling an algebra-comparison pair back along such
    a morphism composes the two algebra maps
    (`Stacks.RelativeSpec.pullback_comp_pairToHom_algebraHomPair`). The three factors are
    presented by `Stacks.Conormal.normalConeMap_eq_pairToHom` and
    `Stacks.Conormal.normalConeToNormalBundle_eq_pairToHom`;
  - the values of the algebra maps on a degree-one homogeneous section are
    `Stacks.Conormal.conormalSymmetricAlgebraSheafHom_ungradedIncl`,
    `Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl` and
    `Stacks.Conormal.conormalAlgebraSheafPushforwardHom_ungradedIncl`; composing the last two of
    them gives the canonical map `𝒞_{Y/X,1} ⟶ 𝒞_{Z/X,1} ⟶ 𝒞_{Z/Y,1}`; and
  - that canonical composite is zero, in every nonzero degree and not only in degree one:
    `AlgebraicGeometry.conormalAlgebraHom_comp_map_eq_zero`. On a conormal chart
    `AlgebraicGeometry.ConormalAlgebraHom.IsCanonical` computes the composite as reduction of a
    representative — the class of `a ∈ ℐ_Y^n` goes to the class of the image of `a` in
    `𝒪_X/ℐ_Y`, which is `0` for `n ≥ 1` because `ℐ_Y^n ⊆ ℐ_Y` — and the chart cover of
    `AlgebraicGeometry.conormalChart_cover` descends it. No statement that the conormal algebra
    is generated in degree one is used.

**The conormal sequence.** For the chain of immersions `Z ⟶ Y ⟶ X` the
sequence of [Stacks, Tag 062S] — the same sequence as part (2) of [Stacks, Tag 06AE] — is
`Stacks.Immersion.conormalSequence_comp_zero` (the composite `𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` is
zero), `Stacks.Immersion.epi_conormalSequenceRightMap` (`𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` is surjective) and
`Stacks.Immersion.conormalSequence_exact` (exactness at `𝒞_{Z/X}`); the universal-thickening form
of [Stacks, Tag 06AE] itself is `Stacks.Thickenings.transitivityConormalLeftMap_comp_rightMap`,
`Stacks.Thickenings.epi_transitivityConormalRightMap` and
`Stacks.Thickenings.transitivityConormalShortComplex_exact`.

## Why the Gysin system is the canonical one

The identity fails for an arbitrary `Stacks.Chow.GysinSystem`. A Gysin system's
contained-component rule enters `o^* ∩ [C_ZX]_n` on every component of
`C_ZX` that `C_ZX ⟶ C_YX` carries into `o(Y)`, and on a test scheme `T` of δ-dimension `k + 1` the
`factors` field of the system says nothing about the rule in degree `k`: `CH_{k+1}(T)` has no
rational equivalences, as `T` has no integral closed subscheme of δ-dimension `k + 2`. So the
rule may be changed by any class at the single datum `(C_ZX, 𝒪(o(Y))|_{C_ZX}, n - 1)` without
leaving the Gysin systems. Take `S = Spec k`, `X = P^1_k × A^1_k` (`n = 2`), `Z = P^1 × {0}` cut
out by `t` and `Y = P^1 × Spec k[t]/(t^2)` cut out by `t^2`. Then `𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X}` sends
`t^2` to `0`, so `C_ZX ≅ P^1 × A^1` maps into `o(Y)` and `Y ×_{o, C_YX} C_ZX ≅ C_ZX`; the right
hand side is `[C_ZY]_1 = 2[P^1 × 0] = [div(v^2)] = 0` for the fibre coordinate `v` of `C_ZX`,
while the left hand side is the value of the rule on `C_ZX`, which may be taken to be the class
of `{pt} × A^1`, nonzero in `CH_1(P^1 × A^1) ≅ CH_0(P^1) ≅ ℤ`. At the canonical system the left
hand side is `c_1(𝒪(Y)|_{C_ZX}) ∩ [C_ZX] = 0`, as `𝒪(Y)` is trivial, and the identity holds.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 06AE](https://stacks.math.columbia.edu/tag/06AE)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The zero section's image as the zero scheme of a section of an invertible module -/

attribute [local instance] Stacks.Conormal.isEffectiveCartierDivisor_ker_normalConeZeroSection

section Presentation

variable {X : Scheme.{u}} (DY : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor DY]

/-- **The invertible module `𝒪(o(Y))` on the normal cone `C_YX`**, where `o : Y ⟶ C_YX` is the
zero section of [Stacks, Tag 0FEB]: it is `Stacks.Divisors.divisorSheaf` of the effective Cartier
divisor `o(Y)`. Together with `Stacks.Chow.zeroSectionDivisorSection` it presents `o(Y)` as the
zero scheme of a section of an invertible module. -/
abbrev zeroSectionDivisorSheaf : (Stacks.Conormal.normalCone DY.subschemeι).Modules :=
  Stacks.Divisors.divisorSheaf (Stacks.Conormal.normalConeZeroSection DY).ker

/-- **The canonical section of `𝒪(o(Y))`**, whose zero scheme is `o(Y)` by
`Stacks.Divisors.zeroScheme_canonicalSection`. -/
abbrev zeroSectionDivisorSection : Γ(zeroSectionDivisorSheaf DY, ⊤) :=
  Stacks.Divisors.divisorSheafGlobalSection (Stacks.Conormal.normalConeZeroSection DY).ker

/-- **The identification of `Y` with the zero scheme of the canonical section of `𝒪(o(Y))`.** It
is the isomorphism of `Y` onto the scheme-theoretic image of the closed immersion `o`, followed by
the transport along `Stacks.Divisors.zeroScheme_canonicalSection`. -/
def zeroSectionToZeroScheme : DY.subscheme ⟶
    (Stacks.Divisors.zeroScheme (Stacks.Conormal.normalCone DY.subschemeι)
      (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)).subscheme :=
  (Stacks.Conormal.normalConeZeroSection DY).toImage ≫
    eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (Stacks.Divisors.zeroScheme_canonicalSection
        (Stacks.Conormal.normalConeZeroSection DY).ker).symm)

/-- **The identification of `Y` with the zero scheme carries the inclusion of the zero scheme back
to the zero section `o`.** -/
theorem zeroSectionToZeroScheme_comp_gysinTripleInclusion :
    zeroSectionToZeroScheme DY ≫
        gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY) =
      Stacks.Conormal.normalConeZeroSection DY :=
  (Category.assoc _ _ _).trans
    ((congrArg ((Stacks.Conormal.normalConeZeroSection DY).toImage ≫ ·)
        (eqToHom_subscheme_comp_subschemeι _ _
          (Stacks.Divisors.zeroScheme_canonicalSection
            (Stacks.Conormal.normalConeZeroSection DY).ker).symm)).trans
      (Stacks.Conormal.normalConeZeroSection DY).toImage_imageι)

/-- The identification of `Y` with the zero scheme is an isomorphism: both factors are. -/
instance isIso_zeroSectionToZeroScheme : IsIso (zeroSectionToZeroScheme DY) :=
  inferInstanceAs
    (IsIso ((Stacks.Conormal.normalConeZeroSection DY).toImage ≫ eqToHom _))

end Presentation

/-! ### The statement of Stacks 0FEB -/

section Statement

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]
  (DY : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  {Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  (f : Z ⟶ DY.subscheme) [IsClosedImmersion f]
  (hf : f ≫ DY.subschemeι = iZ)

/-- **The canonical morphism `C_ZY ⟶ C_ZX`** of the nested pair `Z ⊆ Y ⊆ X`, read for one `Z` and
the two ambients `Y ⊆ X`: it is `Stacks.Conormal.normalConeMapOfSquare` for the square with
`𝟙 Z` on the left and the inclusion `Y ⟶ X` on the right. -/
abbrev normalConeOfNestedToAmbient : Stacks.Conormal.normalCone f ⟶ Stacks.Conormal.normalCone iZ :=
  Stacks.Conormal.normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι
    ((Category.id_comp iZ).trans hf.symm)

/-- **The closed immersion `C_ZY ⟶ Y ×_{o, C_YX} C_ZX` that [Stacks, Tag 0FEB] leaves implicit.**
It is the lift of the canonical morphism `C_ZY ⟶ C_ZX` and the projection `C_ZY ⟶ Z ⟶ Y` across
the fibre product, which exists because the composite `C_ZY ⟶ C_ZX ⟶ C_YX` factors through the
zero section `o`, by `Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection`.

Its components are `Stacks.Chow.normalConeToZeroFibre_fst` and
`Stacks.Chow.normalConeToZeroFibre_snd`, and they determine it
(`Stacks.Chow.normalConeZeroSectionGysinRelation_hom_ext`). -/
def normalConeToZeroFibre :
    Stacks.Conormal.normalCone f ⟶
      pullback (gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY))
        (Stacks.Conormal.normalConeMapOfFactorization iZ DY.subschemeι f hf) :=
  pullback.lift (Stacks.Conormal.normalConeToBase f ≫ f ≫ zeroSectionToZeroScheme DY)
    (normalConeOfNestedToAmbient DY iZ f hf)
    ((Category.assoc _ _ _).trans
      (((congrArg (Stacks.Conormal.normalConeToBase f ≫ ·) ((Category.assoc _ _ _).trans
            (congrArg (f ≫ ·) (zeroSectionToZeroScheme_comp_gysinTripleInclusion DY)))).trans
          (Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection
            DY iZ f hf).symm)))

/-- The first component of `Stacks.Chow.normalConeToZeroFibre` is the projection
`C_ZY ⟶ Z ⟶ Y`, read on the zero scheme. -/
theorem normalConeToZeroFibre_fst :
    normalConeToZeroFibre DY iZ f hf ≫ pullback.fst _ _ =
      Stacks.Conormal.normalConeToBase f ≫ f ≫ zeroSectionToZeroScheme DY :=
  pullback.lift_fst _ _ _

/-- The second component of `Stacks.Chow.normalConeToZeroFibre` is the canonical morphism
`C_ZY ⟶ C_ZX`. -/
theorem normalConeToZeroFibre_snd :
    normalConeToZeroFibre DY iZ f hf ≫ pullback.snd _ _ =
      normalConeOfNestedToAmbient DY iZ f hf :=
  pullback.lift_snd _ _ _

omit [Stacks.Divisors.IsEffectiveCartierDivisor DY] in
/-- **The canonical morphism `C_ZY ⟶ C_ZX` is a closed immersion.** -/
theorem isClosedImmersion_normalConeOfNestedToAmbient :
    IsClosedImmersion (normalConeOfNestedToAmbient DY iZ f hf) :=
  Stacks.Conormal.isClosedImmersion_normalConeMapOfSquare_of_factorization f DY.subschemeι iZ
    ((Category.id_comp iZ).trans hf.symm)

/-- **`Stacks.Chow.normalConeToZeroFibre` is a closed immersion.** -/
theorem isClosedImmersion_normalConeToZeroFibre :
    IsClosedImmersion (normalConeToZeroFibre DY iZ f hf) :=
  have : IsClosedImmersion (normalConeOfNestedToAmbient DY iZ f hf) :=
    isClosedImmersion_normalConeOfNestedToAmbient DY iZ f hf
  have : IsClosedImmersion (normalConeToZeroFibre DY iZ f hf ≫ pullback.snd _ _) :=
    (normalConeToZeroFibre_snd DY iZ f hf) ▸ ‹_›
  IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.snd _ _)

/-- **A morphism `C_ZY ⟶ Y ×_{o, C_YX} C_ZX` is determined by having the two components of
`Stacks.Chow.normalConeToZeroFibre`**: any two such morphisms are equal. -/
theorem normalConeZeroSectionGysinRelation_hom_ext
    (ι ι' : Stacks.Conormal.normalCone f ⟶
      pullback (gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY))
        (Stacks.Conormal.normalConeMapOfFactorization iZ DY.subschemeι f hf))
    (hsnd : ι ≫ pullback.snd _ _ =
      Stacks.Conormal.normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι
        ((Category.id_comp iZ).trans hf.symm))
    (hfst : ι ≫ pullback.fst _ _ =
      Stacks.Conormal.normalConeToBase f ≫ f ≫ zeroSectionToZeroScheme DY)
    (hsnd' : ι' ≫ pullback.snd _ _ =
      Stacks.Conormal.normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι
        ((Category.id_comp iZ).trans hf.symm))
    (hfst' : ι' ≫ pullback.fst _ _ =
      Stacks.Conormal.normalConeToBase f ≫ f ≫ zeroSectionToZeroScheme DY) : ι = ι' :=
  pullback.hom_ext (hfst.trans hfst'.symm) (hsnd.trans hsnd'.symm)

end Statement

/-! ### The statement at two effective Cartier divisors -/

section StatementAtDivisors

open Scheme.IdealSheafData

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (DY : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  (DZ : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DZ] (hZY : DY ≤ DZ)
  (n : ℤ)

/-- The canonical morphism `C_ZX ⟶ C_YX` of two nested effective Cartier divisors `Z ⊆ Y` is
locally of finite type. -/
instance locallyOfFiniteType_normalConeMapOfFactorization_inclusion :
    LocallyOfFiniteType (Stacks.Conormal.normalConeMapOfFactorization DZ.subschemeι DY.subschemeι
      (inclusion hZY) (inclusion_subschemeι hZY)) := by
  have : LocallyOfFiniteType (Stacks.Conormal.normalConeMapOfFactorization DZ.subschemeι
      DY.subschemeι (inclusion hZY) (inclusion_subschemeι hZY) ≫
        Stacks.Conormal.normalConeToBase DY.subschemeι) := by
    rw [Stacks.Conormal.normalConeMapOfFactorization_toBase]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (Stacks.Conormal.normalConeToBase DY.subschemeι)

end StatementAtDivisors

end Stacks.Chow

end

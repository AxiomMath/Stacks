module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage

/-!
# The normalization of an algebraic space in another

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and
let `𝒪'` be the integral closure of `𝒪_X` in `f_* 𝒪_Y`.  The *normalization of `X` in `Y`* is
the relative spectrum

`ν : X' = \underline{Spec}_X(𝒪') ⟶ X`,

and it comes with a canonical factorization `Y ⟶ X' ⟶ X` of `f`: the factorization
`Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X` of Stacks 081X, composed with the morphism of relative
spectra that the inclusion `𝒪' ⊂ f_* 𝒪_Y` induces in the other direction.  This file
constructs both, and records that the factorization is one.

## Main definitions

* `AlgebraicGeometry.Space.normalizationInAlgebra` is `𝒪'`, the integral closure of `𝒪_X` in
  `f_* 𝒪_Y`, as a quasi-coherent `𝒪_X`-algebra.
* `AlgebraicGeometry.Space.normalizationIn` is the normalization `ν : X' ⟶ X` of `X` in `Y`,
  as an algebraic space affine over `X`.
* `AlgebraicGeometry.Space.relativeSpecDirectImageToNormalizationIn` is the morphism
  `\underline{Spec}_X(f_* 𝒪_Y) ⟶ X'` over `X` induced by the inclusion `𝒪' ⊂ f_* 𝒪_Y`, and
  `AlgebraicGeometry.Space.toNormalizationIn` is the resulting canonical morphism `f' : Y ⟶ X'`
  over `X`.

## Main results

* `AlgebraicGeometry.Space.toNormalizationIn_factorization`: the canonical morphism composed
  with `ν` is `f`.  This is the factorization `Y ⟶ X' ⟶ X` of the definition.
* `AlgebraicGeometry.Space.normalizationInPushforwardIso`: the direct image of the structure
  sheaf of `X'` is `𝒪'`, so the construction recovers the algebra it was formed from.

## Implementation notes

**The hypotheses carried, and why none of them is the content of this definition.**  Four
hypotheses appear, each an isolated clause of a tag other than 0822, and each in the shape the
library already states it:

* `E : AffineAlgebraAntiEquivalence B S hS` and `C : BaseChangeCompatibility B S hS E` are the
  two clauses of Stacks 081V, the existence of the relative spectrum.  They are what the
  definition means by `\underline{Spec}_X`, they are the inputs
  `StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage` carries for the same reason,
  and neither is inhabited in this library; see the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence`.
* `hqc` is Stacks 03M9 for the structure sheaf: quasi-coherence of `f_* 𝒪_Y`.  It is where the
  quasi-compactness and quasi-separatedness of `f` enter — the source assumes them exactly so
  that `f_* 𝒪_Y` is quasi-coherent and the relative spectrum of its integral closure is
  defined — so no separate quasi-compactness or quasi-separatedness hypothesis is carried, and
  the definitions below are correspondingly more general than the source's.
* `hqc'` is quasi-coherence of the integral closure, which is the first assertion of Stacks
  0820.  `AlgebraicGeometry.Space.AlgebraSheaf.integralClosureSheaf` constructs the subalgebra
  but proves neither of the two assertions the source makes about it; the implementation notes
  of `StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf` record what the missing proof
  needs.  Stacks 0821 names that subalgebra, and the definition here is stated for it.
* `hid` is the identity clause of Stacks 03G8, carried by
  `AlgebraicGeometry.Space.relativeSpecDirectImageMap` and needed here only because that
  morphism is what is being composed with.

**The direction of the induced morphism.**  The relative spectrum is contravariant in the
algebra, so the inclusion `𝒪' ⊂ f_* 𝒪_Y` induces a morphism
`\underline{Spec}_X(f_* 𝒪_Y) ⟶ \underline{Spec}_X(𝒪')` and not the other way round.  There is
no named functoriality of `AlgebraicGeometry.Space.relativeSpec` in the library, so the
morphism is taken from the inverse of the anti-equivalence, whose values lie in the opposite
of the category of algebraic spaces affine over `X`; `AlgebraicGeometry.Space.relativeSpec` is
by definition the `unop` of such a value, which is what makes the two types agree.

**Why the factorization needs no proof of its own.**  Both morphisms composed are morphisms of
`CategoryTheory.Over X`, so their composite is one, and the factorization equation is its
structure map.  Stating it separately is worthwhile because the source states it, and because
`CategoryTheory.Over.w` of a composite is not in the simp normal form a consumer would reach
for.

## References

* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : AffineAlgebraAntiEquivalence B S hS) (C : BaseChangeCompatibility B S hS E)
    {X Y : AlgebraicSpaces B S hS}

/-- The integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`, as a quasi-coherent `𝒪_X`-algebra.

This is the subalgebra named by Stacks 0821, together with its quasi-coherence, which is the
first assertion of Stacks 0820 and is carried as the hypothesis `hqc'`. -/
def normalizationInAlgebra (f : Y ⟶ X)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent) :
    QuasicoherentAlgebra B S hS X :=
  ⟨AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)), hqc'⟩

/-- **The normalization of `X` in `Y`.**  For a morphism `f : Y ⟶ X` of algebraic spaces whose
direct image `f_* 𝒪_Y` is quasi-coherent, it is the relative spectrum
`ν : X' = \underline{Spec}_X(𝒪') ⟶ X` of the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`,
regarded as an algebraic space affine over `X`. -/
@[stacks 0822 "the normalization of X in Y"]
def normalizationIn (f : Y ⟶ X)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent) :
    AffineOver B S hS X :=
  relativeSpec B S hS E (normalizationInAlgebra B S hS f hqc')

/-- The inclusion `𝒪' ⊂ f_* 𝒪_Y` of the integral closure, as a morphism of quasi-coherent
`𝒪_X`-algebras. -/
def normalizationInAlgebraInclusion (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent) :
    normalizationInAlgebra B S hS f hqc' ⟶ directImageAlgebra B S hS f hqc :=
  ObjectProperty.homMk
    (AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f)))

/-- The morphism `\underline{Spec}_X(f_* 𝒪_Y) ⟶ X'` over `X` induced by the inclusion
`𝒪' ⊂ f_* 𝒪_Y`.  The relative spectrum is contravariant in the algebra, which is why this
morphism runs towards the normalization. -/
def relativeSpecDirectImageToNormalizationIn (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent) :
    relativeSpecDirectImage B S hS E f hqc ⟶ normalizationIn B S hS E f hqc' :=
  ((E.equivalence X).inverse.map
    (normalizationInAlgebraInclusion B S hS f hqc hqc')).unop

/-- **The canonical morphism `f' : Y ⟶ X'` to the normalization of `X` in `Y`**, as a morphism
over `X`.  It is the factorization `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` of Stacks 081X followed by
the morphism of relative spectra induced by the inclusion `𝒪' ⊂ f_* 𝒪_Y`. -/
@[stacks 0822 "the canonical factorization of f through the normalization"]
def toNormalizationIn (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    Over.mk f ⟶ (normalizationIn B S hS E f hqc').obj :=
  relativeSpecDirectImageMap B S hS E C f hqc hid ≫
    (relativeSpecDirectImageToNormalizationIn B S hS E f hqc hqc').hom

/-- The canonical morphism to the normalization of `X` in `Y`, composed with the normalization
`ν : X' ⟶ X`, is `f`.  This is the factorization `Y ⟶ X' ⟶ X` of Stacks 0822. -/
theorem toNormalizationIn_factorization (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    (toNormalizationIn B S hS E C f hqc hqc' hid).left ≫
        (normalizationIn B S hS E f hqc').obj.hom = f :=
  Over.w _

/-- The direct image of the structure sheaf of the normalization of `X` in `Y` is the integral
closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`: the relative spectrum recovers the algebra it is formed
from. -/
def normalizationInPushforwardIso (f : Y ⟶ X)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent) :
    pushforwardAlgebra B S hS (normalizationIn B S hS E f hqc').obj ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)) :=
  relativeSpecPushforwardIso B S hS E (normalizationInAlgebra B S hS f hqc')

end AlgebraicGeometry.Space

end

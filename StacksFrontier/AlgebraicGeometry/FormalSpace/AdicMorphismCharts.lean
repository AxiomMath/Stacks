module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut

/-!
# Adic morphisms and their chart maps

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Formal Spaces, **Section 0AQ2** matches representability of
`f` by algebraic spaces (condition (1)) with the condition that every commutative square

```
U ⟶ V
↓     ↓
X ⟶ Y
```

with `U`, `V` affine formal algebraic spaces and representable étale vertical maps has its upper
horizontal map given by an adic map of `WAdm^{adic*}` (condition (2)).

## Main results

* `AlgebraicGeometry.FormalSpace.IsAdicMorphism.of_comp_eq`: the upper horizontal map of such a
  square over an adic morphism is again adic.
* `AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism'`: **Section
  0AQ2**, condition (1) implies condition (2), with no hypothesis on `X` or `Y`.

## Implementation notes

The upper horizontal map `t : U ⟶ V` of a chart square over a morphism `f` representable by
algebraic spaces is representable by algebraic spaces, by Stacks 0APY and Stacks 0AQ0 for a
second morphism whose source is a formal algebraic space. Composing with the identifications
`U ≅ Spf R`, `V ≅ Spf A` of a presentation, the formal spectrum map `Spf A ⟶ Spf R` of the chart
homomorphism `A ⟶ R` is representable by algebraic spaces, hence the homomorphism is taut by the
implication (1) ⟹ (3) of Stacks 0AN5, in the form in which the formal spectra are known to be
affine formal algebraic spaces — they are isomorphic to `U` and `V`. On `WAdm^{adic*}` taut
is adic by Stacks 0GBS.

## References

* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Definition 0AQ3 on the upper horizontal map of a chart square.** Let `f : X ⟶ Y` be an
adic morphism of formal algebraic spaces over `S` and let `a : U ⟶ X`, `b : V ⟶ Y`,
`t : U ⟶ V` form a commutative square with `a` representable étale and `V` a formal algebraic
space. Then `t` is again an adic morphism: `a ≫ f = t ≫ b` is adic, and Stacks 0AQ0 for a
second morphism whose source is a formal algebraic space cancels `b`. -/
theorem IsAdicMorphism.of_comp_eq {X Y U V : FppfSheaf B S hS}
    {f : X ⟶ Y} {a : U ⟶ X} {b : V ⟶ Y} {t : U ⟶ V}
    (hV : IsFormalAlgebraicSpace B S hS V) (ha : IsRepresentableEtale B S hS a)
    (hf : IsAdicMorphism B S hS f) (hcomm : a ≫ f = t ≫ b) :
    IsAdicMorphism B S hS t := by
  have h : IsAdicMorphism B S hS (t ≫ b) := hcomm ▸ IsAdicMorphism.comp B S hS a f ha.1 hf
  exact isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace B S hS t b hV h

/-- The upper horizontal map of a chart square over a representable étale morphism of fppf
sheaves is an adic morphism, a representable étale morphism being representable by algebraic
spaces. -/
theorem isAdicMorphism_of_comp_eq_of_isRepresentableEtale
    {X Y U V : FppfSheaf B S hS} {w : X ⟶ Y} {a : U ⟶ X} {b : V ⟶ Y} {t : U ⟶ V}
    (hV : IsFormalAlgebraicSpace B S hS V) (ha : IsRepresentableEtale B S hS a)
    (hw : IsRepresentableEtale B S hS w) (hcomm : a ≫ w = t ≫ b) :
    IsAdicMorphism B S hS t :=
  IsAdicMorphism.of_comp_eq B S hS hV ha hw.1 hcomm

/-- **Section 0AQ2, condition (1) implies condition (2).** A morphism `f : X ⟶ Y` of fppf
sheaves over `S` which is representable by algebraic spaces — an adic morphism in the sense of
Definition 0AQ3 — has every one of its chart maps in `WAdm^{adic*}` adic: for every commutative
square with `U`, `V` affine formal algebraic spaces and representable étale vertical maps, and
every presentation of `U` and `V` as formal spectra of rings of `WAdm^{adic*}`, the continuous
homomorphism realizing `U ⟶ V` is adic.

No hypothesis on `X` or `Y` is needed; in particular this holds for `X` and `Y` locally adic\*,
which is the situation of the section. -/
theorem isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism' {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsAdicMorphism B S hS f) :
    IsAdicOnEveryAffineEtaleDiagram B S hS f := by
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  have ht : IsAdicMorphism B S hS t :=
    IsAdicMorphism.of_comp_eq B S hS
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha hf hsq
  have hmap : formalSpectrumMap hA g = eU.inv ≫ t ≫ eV.hom := by
    rw [hg]
    simp
  have hrep : IsAdicMorphism B S hS (formalSpectrumMap hA g) := by
    rw [hmap]
    exact IsAdicMorphism.comp B S hS _ _ (isAdicMorphism_of_isIso B S hS eU.inv)
      (IsAdicMorphism.comp B S hS _ _ ht (isAdicMorphism_of_isIso B S hS eV.hom))
  have htaut : RingHom.IsTaut g.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS hA
      hCR.1.1 D E (isAffineFormalAlgebraicSpace_of_iso B S hS eV hV)
      (isAffineFormalAlgebraicSpace_of_iso B S hS eU hU) g hrep
  exact (@RingHom.isAdic_iff_isTaut A R _ _ _ _ _ _ _ _ g.toRingHom hCA.2
    hCR.1.1.2.1 hCR.1.1.2.2).mpr htaut

end AlgebraicGeometry.FormalSpace

end

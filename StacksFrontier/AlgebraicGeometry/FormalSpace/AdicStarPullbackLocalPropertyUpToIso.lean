module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarBaseChangeVariant
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyUpToIsoInvariance

/-!
# Stacks 0GBE: the variant of Lemma 0GBD for locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Remark 87.21.8 (Stacks 0GBE)** calls a
local property `P` of morphisms of `WAdm^{adic*}` (Remark 0ANH) *stable under base change* when
`P (B → A)` implies `P (C → A ⊗̂_B C)` for all morphisms `B → A`, `B → C` of `WAdm^{adic*}`, and
asserts that in exactly the same way as Lemma 87.21.7 (Stacks 0GBD) one obtains its variant for
morphisms between locally adic\* formal algebraic spaces over `S`: if `f : X ⟶ Y` satisfies the
equivalent conditions of the variant of Stacks 0ANG of Remark 0ANH for `P`, then so does
`pr₂ : X ×_Y Z ⟶ Z` for every `g : Z ⟶ Y`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasProperty_pullback_snd_of_isLocalUpToIso_of_isLocallyAdicStar`:
  the second half of **Stacks 0GBE**, for a local property of morphisms of `WAdm^{adic*}` which is
  stable under base change, with no further hypothesis on `P`.

## Implementation notes

`P` being local in the sense of Remark 0ANH is `TopologicalRing.PropertyIsLocalAdicStarUpToIso P`:
the three axioms of Situation 0CBA for morphisms of `WAdm^{adic*}`, with the completed corners
`(A')^∧ = lim A'/IA'` and `(B')^∧ = lim B'/JB'` of the diagram (87.21.2.1) taken, as limits are,
up to isomorphism. `P` being stable under base change is
`TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar P`, the first half of Stacks 0GBE, whose
locality field is implied by the former through
`TopologicalRing.PropertyIsLocalUpToIso.toPropertyIsLocal`; the two hypotheses together say
exactly that `P` is a local property of morphisms of `WAdm^{adic*}` stable under base change. This
is the same reading as for Stacks 0GBD,
`FormalSpace.hasProperty_pullback_snd_of_isLocalUpToIso_of_isLocallyCountablyIndexed`.

The proof is the chart argument of the source,
`FormalSpace.pullback_snd_hasProperty_of_isLocallyAdicStar` in
`StacksFrontier/AlgebraicGeometry/FormalSpace/AdicStarBaseChangeVariant.lean`. Its one further input,
the invariance of `P` under isomorphism of source and target in `WAdm^{adic*}`, is derived here
from axiom (1) of Situation 0CBA, an isomorphism being étale and a complete ring being its own
completion, by `FormalSpace.propertyIsInvariantUnderSourceIso_of_propertyIsLocalAdicStarUpToIso`
and `FormalSpace.propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalAdicStarUpToIso`.

## References

* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GBE, second half: the variant of Lemma 0GBD for locally adic\* formal algebraic
spaces.** Let `P` be a local property of morphisms of `WAdm^{adic*}` (Remark 0ANH) which is
stable under base change in the sense of the first half of Remark 0GBE. Let `f : X ⟶ Y` and
`g : Z ⟶ Y` be morphisms of locally adic\* formal algebraic spaces over `S`. If `f` satisfies the
equivalent conditions of the variant of Stacks 0ANG of Remark 0ANH for `P`, then so does
`pr₂ : X ×_Y Z ⟶ Z`.

`P` being local in the sense of Remark 0ANH is `hloc`, and `P` being stable under base change is
`hP`. The conditions for `f` are equivalent by
`AlgebraicGeometry.FormalSpace.hasProperty_tfae_isAdicStar`, and `hf` is condition (1). The
conclusion is that `X ×_Y Z` is again locally adic\*, so that those conditions are equivalent for
`pr₂`, and that `pr₂` satisfies all three of them. -/
@[stacks 0GBE "the second half, the variant of Lemma 0GBD for morphisms between locally adic* \
formal algebraic spaces: for a local property P of morphisms of WAdm^{adic*} in the sense of \
Remark 0ANH (hloc, TopologicalRing.PropertyIsLocalAdicStarUpToIso) which is stable under base \
change in the sense of the first half (hP, TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar), \
and morphisms f : X -> Y, g : Z -> Y of locally adic* formal algebraic spaces, if f satisfies the \
equivalent conditions of the variant of Stacks 0ANG then X x_Y Z is locally adic* and \
pr2 : X x_Y Z -> Z satisfies all three"]
theorem hasProperty_pullback_snd_of_isLocalUpToIso_of_isLocallyAdicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hloc : TopologicalRing.PropertyIsLocalAdicStarUpToIso.{u} P)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    IsLocallyAdicStar B S hS (pullback f g) ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) :=
  pullback_snd_hasProperty_of_isLocallyAdicStar B S hS P hP
    (propertyIsInvariantUnderSourceIso_of_propertyIsLocalAdicStarUpToIso P hloc)
    (propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalAdicStarUpToIso P hloc)
    f g hX hY hZ hf

end AlgebraicGeometry.FormalSpace

end

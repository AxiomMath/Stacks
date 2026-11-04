module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability

/-!
# Characterising finite type morphisms of formal algebraic spaces on affine charts

Let `S` be a scheme contained in a big fppf site `B`.

**Stacks 0ANV** says that for a morphism `f : X ⟶ Y` of affine formal algebraic spaces over
`S` with `Y` countably indexed, being locally of finite type, being of finite type, and
corresponding to a morphism of `WAdm^{count}` satisfying the equivalent conditions of Stacks
0ANU are equivalent.

**Stacks 0ANW** says that for a morphism `f : X ⟶ Y` of locally countably indexed formal
algebraic spaces over `S` the following are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has its upper horizontal map `U ⟶ V` given by a taut,
   topologically of finite type morphism of `WAdm^{count}`;
2. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with each `Xⱼᵢ ⟶ Yⱼ` given by such a morphism;
3. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Xᵢ ⟶ Yᵢ` given by such a morphism;
4. `f` is locally of finite type.

## Main definitions

* `TopologicalRing.IsTautTopologicallyOfFiniteTypeHom`: being taut and topologically of finite
  type, in the shape in which the local-property machinery of Stacks 0ANG takes a property of
  arrows. This is the property Stacks 0ANU supplies the equivalent conditions for.
* `AlgebraicGeometry.FormalSpace.IsFiniteTypeOfIsLocallyOfFiniteTypeOnAffine`,
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeFormalSpectrumMapOfFiniteTypeModulo`,
  `AlgebraicGeometry.FormalSpace.ChartPropertyIsLocallyOfFiniteType`,
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnEveryEtaleSquare` and
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOfTargetCover`: the five inputs of the
  two lemmas that this library does not carry, each named once with the Stacks tag it is.

## Main results

* **Stacks 0ANV** is
  `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae_of_isAffineFormalAlgebraicSpace`, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationAffine`.
* **Stacks 0ANW** is `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae'`, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationRefined`.

## Implementation notes

### Stacks 0ANV

The lemma itself, at the source's hypotheses, is
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae_of_isAffineFormalAlgebraicSpace`.
Two of the four conditions of Stacks 0ANU appear in its list, condition (a) and condition (c),
and they are identified by Stacks 0ANU — `TopologicalRing.finiteType_tfae` — which is where
the countable generation of the two neighbourhood filters of zero is used. This module names
two inputs of a conditional form of the lemma read on formal spectrum maps:
`AlgebraicGeometry.FormalSpace.IsFiniteTypeOfIsLocallyOfFiniteTypeOnAffine`, the
identification of being locally of finite type with being of finite type on affine formal
algebraic spaces (Definition 0AJC and Lemma 0AJB), and
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeFormalSpectrumMapOfFiniteTypeModulo`, the
implication (2) ⟹ (1) of Stacks 0ANT, of which the library carries only the stage half
`AlgebraicGeometry.FormalSpace.exists_isPullback_isFiniteTypeULift_formalSpectrumMap_stage`.

### Stacks 0ANW

The equivalence of conditions (1), (2) and (3) is Stacks 0ANG for the class of countably
indexed weakly admissible topological rings and the property of being taut and topologically
of finite type, which is a local property of such arrows by Stacks 0ANU. The lemma itself is
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae'`; this module names inputs of a
conditional comparison with condition (4).

* `AlgebraicGeometry.FormalSpace.ChartPropertyIsLocallyOfFiniteType` is **Stacks 0ANV** read
  on countably indexed affine charts rather than on formal spectra: a map of such charts is
  locally of finite type exactly when the morphism of `WAdm^{count}` presenting it is taut and
  topologically of finite type. Transporting Lemma
  0ANV to charts uses that a countably indexed affine formal algebraic space is a formal
  spectrum (Stacks 0AIK) and that a map of formal spectra comes from a continuous
  homomorphism (Stacks 0AN0); restricting to countably indexed charts is what keeps it
  faithful, since an affine formal algebraic space which is not a formal spectrum has no
  presentation and the condition on its chart maps is then vacuous. This is the same shape as
  the hypothesis `h0AN5` of
  `AlgebraicGeometry.FormalSpace.isTaut_tfae_isRepresentableByAlgebraicSpaces`.
* The implication (2) ⟹ (1) of Stacks 0AKX says that an affine formal algebraic space
  representable étale over a locally countably indexed formal algebraic space is countably
  indexed. The library takes condition (2) as the definition of "locally countably indexed"
  precisely because that equivalence is missing, so the charts appearing in (1), (2) and (3)
  are not known to be countably indexed without it, and
  `AlgebraicGeometry.FormalSpace.ChartPropertyIsLocallyOfFiniteType` does not apply to them.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnEveryEtaleSquare` and
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOfTargetCover` are the implications
  (1) ⟹ (3) and (4) ⟹ (1) of **Stacks 0ANL**, which are the two the source's proof of Stacks
  0ANW uses and which this library does not carry.

## References

* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0ANV](https://stacks.math.columbia.edu/tag/0ANV)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- Being taut and topologically of finite type, read as a property of arrows of
`WAdm^{count}`. This is the shape in which the local-property machinery of Stacks 0ANG takes a
property of arrows, and it is condition (c) of the equivalent conditions of Stacks 0ANU. -/
abbrev IsTautTopologicallyOfFiniteTypeHom {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁]
    [IsTopologicalRing R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    (φ : R₁ →+* R₂) : Prop :=
  RingHom.IsTaut φ ∧ IsTopologicallyOfFiniteType φ

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inputs this library does not carry -/

/-- The quasi-compactness input of **Stacks 0AJC**: a morphism of affine formal algebraic
spaces over `S` which is locally of finite type is of finite type. The source reads "of finite
type" as "locally of finite type and quasi-compact in the sense of Definition 0AJC", whose
equivalent conditions are Lemma 0AJB; neither the definition nor the lemma is part of this
library. -/
abbrev IsFiniteTypeOfIsLocallyOfFiniteTypeOnAffine : Prop :=
  ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V), IsAffineFormalAlgebraicSpace B S hS U →
    IsAffineFormalAlgebraicSpace B S hS V →
    IsLocallyOfFiniteType B S hS t → IsFiniteType B S hS t

/-- The implication (2) ⟹ (1) of **Stacks 0ANT**: a continuous homomorphism of weakly
admissible topological rings over `S` which is taut and of finite type modulo every weak ideal
of definition has formal spectrum map locally of finite type. The library carries only the
stage half of this implication,
`AlgebraicGeometry.FormalSpace.exists_isPullback_isFiniteTypeULift_formalSpectrumMap_stage`,
because condition (1) of Stacks 0ANT quantifies over every scheme-valued point of the target
and not only over those factoring through a thickening stage. -/
abbrev IsLocallyOfFiniteTypeFormalSpectrumMapOfFiniteTypeModulo : Prop :=
  ∀ {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (g : ContinuousHom D E),
    TopologicalRing.FiniteTypeModuloEveryWeakIdeal g.toRingHom →
    IsLocallyOfFiniteType B S hS (formalSpectrumMap hA g)

/-- **Stacks 0ANV** read on countably indexed affine charts rather than on formal spectra: a
map of countably indexed affine formal algebraic spaces over `S` is locally of finite type
exactly when every morphism of `WAdm^{count}` presenting it is taut and topologically of
finite type. Transporting Lemma 0ANV from formal spectra to charts uses Stacks 0AIK, that a
countably indexed affine formal algebraic space is a formal spectrum, and Stacks 0AN0, that a
map of formal spectra comes from a continuous homomorphism; neither is carried here in the
form needed. The restriction to countably indexed charts is what keeps the statement
faithful: an affine formal algebraic space which is not a formal spectrum has no presentation
at all, and the condition on its chart maps is then vacuous. -/
abbrev ChartPropertyIsLocallyOfFiniteType : Prop :=
  ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V), IsAffineFormalAlgebraicSpace B S hS U →
    IsAffineFormalAlgebraicSpace B S hS V → IsCountablyIndexed B S hS U →
    IsCountablyIndexed B S hS V →
    (IsLocallyOfFiniteType B S hS t ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom t)

/-- The implication (1) ⟹ (3) of **Stacks 0ANL**: if a morphism of formal algebraic spaces
over `S` is locally of finite type, then so is the induced map of any pair of representable
étale charts of its source and target. The library does not carry Stacks 0ANL; the source's
proof of this implication goes through Stacks 046G and the locally-of-finite-type diagonal of
Stacks 0AN2. -/
abbrev IsLocallyOfFiniteTypeOnEveryEtaleSquare : Prop :=
  ∀ {X Y U V : FppfSheaf B S hS} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V),
    IsFormalAlgebraicSpace B S hS U → IsFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b → a ≫ f = t ≫ b →
    IsLocallyOfFiniteType B S hS f → IsLocallyOfFiniteType B S hS t

/-- The implication (4) ⟹ (1) of **Stacks 0ANL**: a morphism of formal algebraic spaces over
`S` admitting an affine étale covering of its target together with affine étale coverings of
the fibre products of the members with its source, all of whose maps to the members of the
outer covering are locally of finite type, is itself locally of finite type. The library does
not carry Stacks 0ANL; the source's proof of this implication assembles the coverings into a
single square and descends along it by Stacks 040Y. -/
abbrev IsLocallyOfFiniteTypeOfTargetCover : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
    (∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
      IsAffineEtaleCover B S hS V v ∧
        ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS)
          (w : ∀ i, U i ⟶ pullback (v j) f),
          IsAffineEtaleCover B S hS U w ∧
            ∀ i, IsLocallyOfFiniteType B S hS (w i ≫ pullback.fst (v j) f)) →
    IsLocallyOfFiniteType B S hS f

/-! ### Stacks 0ANV -/

variable {B S hS}

/-! ### Stacks 0ANW -/

end AlgebraicGeometry.FormalSpace

end

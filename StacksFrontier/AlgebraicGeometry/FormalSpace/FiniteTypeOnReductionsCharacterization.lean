module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal

/-!
# Characterising finite type on reductions on affine charts

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GC7** says that for a morphism
`f : X ⟶ Y` of locally countably indexed formal algebraic spaces over `S` the following four
conditions are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has its upper horizontal map `U ⟶ V` given by an arrow of
   `WAdm^{count}` satisfying the property of Stacks 0GC2, namely that the induced map of the
   quotients by the ideals of topologically nilpotent elements be of finite type;
2. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with each `Xⱼᵢ ⟶ Yⱼ` given by such an arrow;
3. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Xᵢ ⟶ Yᵢ` given by such an arrow;
4. the induced morphism of reductions `f_red : X_red ⟶ Y_red` is locally of finite type.

Conditions (1), (2) and (3) are the three conditions of Stacks 0ANG for the class of countably
indexed weakly admissible topological rings and the property of Stacks 0GC2, which is a local
property of such arrows by `TopologicalRing.isFiniteTypeOnReductions_propertyIsLocal`.
Condition (4) is compared with them chart by chart: for `Spf A` the reduction is
`Spec (A ⧸ 𝔞)` by Stacks 0GB6, so an arrow `B ⟶ A` of `WAdm^{count}` has the property of
Stacks 0GC2 exactly when the induced map `Spec (A ⧸ 𝔞) ⟶ Spec (B ⧸ 𝔟)` of reductions is
locally of finite type, and being locally of finite type is étale local on source and target.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnReductions`: condition (4), that every
  morphism between reductions of the source and of the target compatible with `f` be a
  morphism of algebraic spaces locally of finite type.
* `AlgebraicGeometry.FormalSpace.ChartPropertyIsFiniteTypeOnReductions`,
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare` and
  `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnReductionsOfTargetCover`: the three
  inputs comparing condition (4) with the other three which this library does not carry, each
  named once with the Stacks tag it is.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnReductions_tfae`: the four conditions of
  **Stacks 0GC7**, on the eight results this library does not carry taken as named hypotheses.
  The tag itself is proved outright, with none of them, as
  `isLocallyOfFiniteTypeOnReductions_tfae_of_isLocallyCountablyIndexed` in the module
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsTfae`.

## Implementation notes

Stacks 0AIN, the existence of the reduction, is not available in this library, so condition (4)
quantifies over reductions of the source and of the target and over morphisms between them
compatible with `f`, exactly as `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions` does
for condition (1) of Stacks 0AJB. Being locally of finite type for the resulting morphism of
algebraic spaces is `AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift`, part (1) of Stacks
03XF in the value universe `u + 1` in which a formal algebraic space lives.

The equivalence of conditions (1), (2) and (3) is run through the three legs of Stacks 0ANG the
library carries, with `hpb`, `hasc`, `hdesc` and `href` the same hypotheses as for
`AlgebraicGeometry.FormalSpace.isFlat_tfae`: Stacks 0AJ3, that the fibre product of a chart of
`Y` with `f` is a formal algebraic space, is `hpb`; the refinement of a covering as in condition
(3) against a square as in condition (1), which uses Stacks 0AJ2 and quasi-compactness of an
affine formal algebraic space, is `href`; and the locality axioms of Situation 0CBA for the
property of Stacks 0GC2, which hold by that tag but have to be transported to morphisms of
affine formal algebraic spaces through Stacks 0AN8 and Stacks 0AN9, are `hasc` and `hdesc` —
the library carries that transport only for a morphism already presented by an étale ring map.

Comparison with condition (4) uses three further inputs.

* `hbridge` is the affine computation of the source's proof: for a map of countably indexed
  affine formal algebraic spaces, the morphism of reductions is locally of finite type exactly
  when the arrow of `WAdm^{count}` presenting it has the property of Stacks 0GC2. It rests on
  Stacks 0GB6, that the reduction of `Spf A` is `Spec (A ⧸ 𝔞)` — which the library carries as
  `AlgebraicGeometry.FormalSpace.isReduction_formalSpectrum`, but only for a chosen presentation
  and a large enough site — together with Stacks 0AIK, that a countably indexed affine formal
  algebraic space is a formal spectrum, Stacks 0AN0, that a map of formal spectra comes from a
  continuous homomorphism, and the identification of being locally of finite type for a morphism
  of affine schemes with `RingHom.FiniteType`. Restricting to countably indexed charts is what
  keeps it faithful, since an affine formal algebraic space which is not a formal spectrum has
  no presentation and the condition on its chart maps is then vacuous.
* `h0AKX` is the implication (2) ⟹ (1) of Stacks 0AKX: an affine formal algebraic space
  representable étale over a locally countably indexed formal algebraic space is countably
  indexed. The library takes condition (2) as the definition of "locally countably indexed"
  precisely because that equivalence is missing, so the charts appearing in (1), (2) and (3) are
  not known to be countably indexed without it and `hbridge` does not apply to them.
* `hredsquare` and `hredcover` are the two forms in which the source uses that being locally of
  finite type is étale local on source and target (Stacks 040Y), read on reductions: condition
  (4) passes from `f` to the upper horizontal map of an affine representable étale square over
  it, and conversely holds for `f` as soon as it holds after a covering of the target together
  with coverings of the fibre products of its members with the source. These are the two
  implications (1) ⟹ (3) and (4) ⟹ (1) of Stacks 0ANL read on reductions; the library carries
  Stacks 0ANL only in the legs (1) ⟹ (2), (3) ⟹ (1), (3) ⟹ (2), (3) ⟹ (4) and (4) ⟹ (5), and
  carries no transport of them to reductions, which would need that the reductions of the
  members of a covering as in Definition 0AIM form an étale covering of the reduction.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GB6](https://stacks.math.columbia.edu/tag/0GB6)
* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
* [Stacks Project, Tag 0GC7](https://stacks.math.columbia.edu/tag/0GC7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

universe u

/-- On linearly topologized rings the property that the local-property machinery of Stacks 0ANG
consumes is the property of Stacks 0GC2: the homomorphism is continuous and the induced map of
the quotients by the topological nilradicals is of finite type. -/
theorem finiteTypeOnReductionsProperty_iff {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁]
    [IsTopologicalRing R₁] [IsLinearTopology R₁ R₁] [CommRing R₂] [TopologicalSpace R₂]
    [IsTopologicalRing R₂] [IsLinearTopology R₂ R₂] (φ : R₁ →+* R₂) :
    FiniteTypeOnReductionsProperty φ ↔
      ∃ hφ : Continuous φ, Rig.IsFiniteTypeOnReductions φ hφ :=
  ⟨fun h ↦ h, fun h _ _ ↦ h⟩

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GC7, condition (4).** A morphism of fppf sheaves on the big fppf site of `S` is
*locally of finite type on reductions* when every morphism between a reduction of its source and
a reduction of its target compatible with it is a morphism of algebraic spaces locally of finite
type. The reductions are quantified over rather than constructed, Stacks 0AIN not being
available in this library. -/
abbrev IsLocallyOfFiniteTypeOnReductions {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (Xred Yred : FppfSheaf B S hS) (iX : Xred ⟶ X) (iY : Yred ⟶ Y),
    IsReduction B S hS X Xred iX → IsReduction B S hS Y Yred iY →
      ∀ fred : Xred ⟶ Yred, fred ≫ iY = iX ≫ f →
        Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS fred.hom

/-! ### The inputs comparing condition (4) with the other three -/

/-- The affine computation of the proof of **Stacks 0GC7**: a map of countably indexed affine
formal algebraic spaces over `S` is locally of finite type on reductions exactly when every
arrow of `WAdm^{count}` presenting it has the property of Stacks 0GC2. For `Spf A` the reduction
is `Spec (A ⧸ 𝔞)` by Stacks 0GB6, so the morphism of reductions is the map of spectra of the
quotients by the ideals of topologically nilpotent elements; identifying it with that map uses
Stacks 0AIK, that a countably indexed affine formal algebraic space is a formal spectrum, and
Stacks 0AN0, that a map of formal spectra comes from a continuous homomorphism. The restriction
to countably indexed charts is what keeps the statement faithful: an affine formal algebraic
space which is not a formal spectrum has no presentation at all, and the condition on its chart
maps is then vacuous. -/
abbrev ChartPropertyIsFiniteTypeOnReductions : Prop :=
  ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V), IsAffineFormalAlgebraicSpace B S hS U →
    IsAffineFormalAlgebraicSpace B S hS V → IsCountablyIndexed B S hS U →
    IsCountablyIndexed B S hS V →
    (IsLocallyOfFiniteTypeOnReductions B S hS t ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.FiniteTypeOnReductionsProperty t)

/-- The implication (1) ⟹ (3) of **Stacks 0ANL** read on reductions, in the affine case the
proof of Stacks 0GC7 uses: if a morphism of formal algebraic spaces over `S` is locally of
finite type on reductions, then so is the induced map of any pair of affine representable étale
charts of its source and target. The library carries no transport of Stacks 0ANL to reductions;
on reductions the statement is that being locally of finite type for a morphism of algebraic
spaces is étale local on the source and the target (Stacks 040Y), applied to the reductions of
the charts, which form étale coverings of the reductions by affine schemes. -/
abbrev IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare : Prop :=
  ∀ {X Y U V : FppfSheaf B S hS} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b → a ≫ f = t ≫ b →
    IsLocallyOfFiniteTypeOnReductions B S hS f → IsLocallyOfFiniteTypeOnReductions B S hS t

/-- The implication (4) ⟹ (1) of **Stacks 0ANL** read on reductions: a morphism of formal
algebraic spaces over `S` admitting an affine étale covering of its target together with affine
étale coverings of the fibre products of the members with its source, all of whose maps to the
members of the outer covering are locally of finite type on reductions, is itself locally of
finite type on reductions. The library carries no transport of Stacks 0ANL to reductions; on
reductions the statement is that being locally of finite type for a morphism of algebraic spaces
is étale local on the source and the target (Stacks 040Y), applied to the reductions of the two
coverings, which form étale coverings of the reductions by affine schemes. -/
abbrev IsLocallyOfFiniteTypeOnReductionsOfTargetCover : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
    (∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
      IsAffineEtaleCover B S hS V v ∧
        ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS)
          (w : ∀ i, U i ⟶ pullback (v j) f),
          IsAffineEtaleCover B S hS U w ∧
            ∀ i, IsLocallyOfFiniteTypeOnReductions B S hS (w i ≫ pullback.fst (v j) f)) →
    IsLocallyOfFiniteTypeOnReductions B S hS f

/-! ### Stacks 0GC7 -/

variable {B S hS}

/-- **Stacks 0GC7.** For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic
spaces over `S`, the condition that every affine representable étale square over `f` carry an
arrow of `WAdm^{count}` with the property of Stacks 0GC2, the existence of an affine étale
covering of `Y` together with affine étale coverings of the fibre products of its members with
`X` on which that condition holds, the existence of an affine étale covering of `X` whose
members factor through affine representable étale charts of `Y` by such arrows, and the morphism
of reductions `f_red` being locally of finite type, are all equivalent.

The first three are the three conditions of Stacks 0ANG for the class of countably indexed
weakly admissible topological rings and the property of Stacks 0GC2, which that tag makes a
local property of such arrows; the comparison with the fourth is the affine computation of
Stacks 0GB6 together with the étale locality of being locally of finite type.

This is the special case of the tag that takes the eight results the equivalence rests on as
named hypotheses. It is no longer the registration of Stacks 0GC7: the tag is proved outright,
on the same four conditions and with none of those hypotheses, as
`isLocallyOfFiniteTypeOnReductions_tfae_of_isLocallyCountablyIndexed` in the module
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsTfae`. That module imports this
one, so the derivation cannot be made here. -/
theorem isLocallyOfFiniteTypeOnReductions_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hpb : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty)
    (href : HasEtaleRefinementOfSourceCover B S hS f)
    (hbridge : ChartPropertyIsFiniteTypeOnReductions B S hS)
    (h0AKX : ∀ (Z : FppfSheaf B S hS), IsLocallyCountablyIndexed B S hS Z →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U)
    (hredsquare : IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare B S hS)
    (hredcover : IsLocallyOfFiniteTypeOnReductionsOfTargetCover B S hS) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        IsLocallyOfFiniteTypeOnReductions B S hS f] := by
  tfae_have 1 → 2 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hY.1 hpb h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f h
  tfae_have 3 → 1 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hasc hdesc href h
  tfae_have 2 → 4 := by
    rintro ⟨J, V, v, hVcover, hinner⟩
    refine hredcover f ⟨J, V, v, hVcover, fun j ↦ ?_⟩
    obtain ⟨I, U, w, hUcover, hUproperty⟩ := hinner j
    refine ⟨I, U, w, hUcover, fun i ↦ ?_⟩
    have hsnd : IsRepresentableEtale B S hS (w i ≫ pullback.snd (v j) f) :=
      IsRepresentableEtale.comp B S hS (hUcover.2.1 i)
        (isRepresentableEtale_pullback_snd B S hS (v j) f (hVcover.2.1 j))
    exact (hbridge (w i ≫ pullback.fst (v j) f) (hUcover.1 i) (hVcover.1 j)
      (h0AKX X hX (U i) (w i ≫ pullback.snd (v j) f) (hUcover.1 i) hsnd)
      (h0AKX Y hY (V j) (v j) (hVcover.1 j) (hVcover.2.1 j))).2 (hUproperty i)
  tfae_have 4 → 1 := by
    intro hf U V a b t hU hV ha hb hsq
    exact (hbridge t hU hV (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1
      (hredsquare f a b t hU hV ha hb hsq hf)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The relation of an étale chart in the second step of the proof of Stacks 03M9

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`.  The second step of the proof of Stacks 03M9 — the
case of an affine base, which
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardReduction.lean` reduces the lemma
to — begins by choosing a surjective étale `τ : U ⟶ X` with `U` affine and forming the relation

`R = U ×_X U`.

The source then says: *"since `X ⟶ Y` is quasi-separated the morphism `R ⟶ U ×_Y U` is a
quasi-compact monomorphism, hence `R` is a quasi-compact separated scheme, and both
`a = τ ≫ f : U ⟶ Y` and `b : R ⟶ Y` are quasi-compact quasi-separated morphisms of schemes."*
This file proves the part of that sentence which concerns `R` and `b`.

The comparison `R ⟶ U ×_Y U` is Mathlib's `CategoryTheory.Limits.pullback.mapDesc`, and that it
is a quasi-compact monomorphism is *already* in the tree: it is parts (1) and (4) of
Stacks 03KN, formalized as `AlgebraicGeometry.Space.relativelyRepresentable_mapDesc`,
`AlgebraicGeometry.Space.isSeparated_mapDesc` and
`AlgebraicGeometry.Space.isQuasiCompact_mapDesc` in
`StacksFrontier/AlgebraicGeometry/Spaces/MapDescent.lean`.  What is supplied
here is quasi-compactness of `R` itself and the two separation properties of `b`.

## Main definitions

There are no new definitions.  The comparison morphism is Mathlib's
`CategoryTheory.Limits.pullback.mapDesc` and the morphism `b : R ⟶ Y` is written out as the
composite `pullback.fst τ τ ≫ τ ≫ f`.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_mapDesc`: the comparison of fibre products is
  quasi-separated, unconditionally.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_selfPullback`: the relation `R = U ×_X U` of a
  chart of a quasi-separated morphism is a quasi-compact algebraic space as soon as `U` is
  quasi-compact and `a = τ ≫ f` is a quasi-compact morphism.
* `AlgebraicGeometry.Space.isQuasiCompact_selfPullback_comp` and
  `AlgebraicGeometry.Space.isQuasiSeparated_selfPullback_comp`: the morphism `b : R ⟶ Y` is
  quasi-compact, respectively quasi-separated, as soon as `a` is.

## Implementation notes

**Why the quasi-separated clause of Stacks 03KQ carries algebraicity hypotheses.**  That clause
is `AlgebraicGeometry.Space.isQuasiSeparated_comp`, and it is used below rather than reproved.
The other two clauses of the same lemma, `AlgebraicGeometry.Space.isSeparated_comp` and
`AlgebraicGeometry.Space.isLocallySeparated_comp`, are one-liners, because
`AlgebraicGeometry.Space.IsSeparated` and `AlgebraicGeometry.Space.IsLocallySeparated` are *by
definition* a represented property of the relative diagonal, so Mathlib's multiplicativity of
`CategoryTheory.MorphismProperty.diagonal` applies directly.  Quasi-separatedness is not of that
shape: `AlgebraicGeometry.Space.IsQuasiCompact` is Stacks 03HE, which quantifies over morphisms
from quasi-compact *algebraic spaces* rather than over represented base changes.  The proof
therefore passes through the two readings of quasi-compactness of a relative diagonal,
`AlgebraicGeometry.Space.isQuasiSeparated_iff_diagonalProp_quasiCompact`, whose two halves need
the relative diagonal to be representable — which it is, for a morphism with algebraic source,
and that is where the hypothesis of algebraicity of the source and of the intermediate object
comes from.  It is the same argument the source gives (factoring `Δ_{X/Z}` through `X ×_Y X`),
since multiplicativity of `CategoryTheory.MorphismProperty.diagonal` is proved by exactly that
factorization.  The two applications below supply the witnesses from
`AlgebraicGeometry.isAlgebraicSpace_pullback`.

**Where the geometry of the relation stops.**  The source concludes that `R` is a quasi-compact
*separated scheme*.  Representability of `R` is not restated here: it is
`AlgebraicGeometry.Space.relativelyRepresentable_mapDesc` together with representability of
`U ×_Y U`, which for affine `U` and affine `Y` is an object of the site.  Separatedness of `R`
over `Y` is likewise not restated, because what the proof of Stacks 03M9 goes on to use is not
separatedness of `R` but quasi-separatedness of `b`, which is what
`AlgebraicGeometry.Space.isQuasiSeparated_selfPullback_comp` gives.

**The hypotheses on `a = τ ≫ f`.**  Quasi-compactness and quasi-separatedness of `a` are
carried rather than derived.  That is the honest factoring of the source argument: in the
situation the second step has arranged, `U` and `Y` are affine, so `a` is a morphism of affine
schemes and both properties are automatic, whereas the corresponding properties of `b` are
exactly what needs `R`.  Nothing about `τ` beyond the two properties of `a` is used — in
particular neither étaleness nor surjectivity of `τ` enters any statement below.

**No quasi-coherence appears in this file.**  The module-theoretic half of the second step of
Stacks 03M9 — the exact sequence of Stacks 03M8 and the identification of the restrictions of
`F` along `τ` with modules on the small étale sites of `U` and `R` — is not treated here; see
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardReduction.lean`.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03KQ](https://stacks.math.columbia.edu/tag/03KQ)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quasi-separated reading of Stacks 03KN, part (1).**  The comparison
`X ×_Z Y ⟶ X ×_T Y` of fibre products is a quasi-separated morphism of algebraic spaces
over `S`.

It is separated by `AlgebraicGeometry.Space.isSeparated_mapDesc`, and a separated morphism is
quasi-separated by Stacks 03KK.  No hypothesis on `h : Z ⟶ T` is needed: parts (2), (3)
and (4) of Stacks 03KN strengthen the conclusion under separation hypotheses on `h`, but
part (1) is unconditional. -/
theorem isQuasiSeparated_mapDesc {X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z)
    (g : Y ⟶ Z) (h : Z ⟶ T) :
    IsQuasiSeparated B S hS (pullback.mapDesc f g h) :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_mapDesc B S hS f g h)

/-! ### The relation `R = U ×_X U` of a chart -/

variable {X Y U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The comparison `U ×_X U ⟶ U ×_Y U` followed by the first projection is the first
projection of `U ×_X U`.

This is `CategoryTheory.Limits.pullback.lift_fst` for the defining cone of
`CategoryTheory.Limits.pullback.mapDesc`, whose first component is the identity of `U`. -/
private theorem mapDesc_comp_fst (τ : U ⟶ X) (f : X ⟶ Y) :
    pullback.mapDesc τ τ f ≫ pullback.fst (τ ≫ f) (τ ≫ f) = pullback.fst τ τ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The morphism `b : U ×_X U ⟶ Y` of the second step of the proof of Stacks 03M9, which is the
common composite `U ×_X U ⟶ X` followed by `f`, factors through `U ×_Y U` as the comparison of
fibre products followed by `U ×_Y U ⟶ U ⟶ Y`. -/
private theorem selfPullback_comp_eq (τ : U ⟶ X) (f : X ⟶ Y) :
    pullback.fst τ τ ≫ τ ≫ f =
      pullback.mapDesc τ τ f ≫ pullback.fst (τ ≫ f) (τ ≫ f) ≫ (τ ≫ f) := by
  rw [← Category.assoc (pullback.mapDesc τ τ f), mapDesc_comp_fst B S hS τ f]

/-- **`R = U ×_X U` is a quasi-compact algebraic space.**  Let `f : X ⟶ Y` be a quasi-separated
morphism of algebraic spaces over `S`, let `τ : U ⟶ X` be a morphism with `U` a quasi-compact
algebraic space, and suppose the composite `a = τ ≫ f : U ⟶ Y` is quasi-compact.  Then the
fibre product of `τ` with itself is quasi-compact.

This is the step *"hence `R` is a quasi-compact … scheme"* of the proof of Stacks 03M9.  The
comparison `R ⟶ U ×_Y U` is quasi-compact by part (4) of Stacks 03KN,
`AlgebraicGeometry.Space.isQuasiCompact_mapDesc`, which is where quasi-separatedness of `f` is
used; `U ×_Y U` is a quasi-compact algebraic space because it is the base change of the
quasi-compact `a` along `a` itself, and is algebraic by Stacks 02X2.  Testing
quasi-compactness of the comparison against the identity of `U ×_Y U` then gives the claim,
the fibre product of a morphism with an identity being its own source. -/
theorem isQuasiCompactSpace_selfPullback (τ : U ⟶ X) (f : X ⟶ Y)
    (hU : IsAlgebraicSpace B S hS U) (hY : IsAlgebraicSpace B S hS Y)
    (hUqc : IsQuasiCompactSpace B S hS U) (hfqs : IsQuasiSeparated B S hS f)
    (haqc : IsQuasiCompact B S hS (τ ≫ f)) :
    IsQuasiCompactSpace B S hS (pullback τ τ) :=
  (isQuasiCompact_mapDesc B S hS τ τ f hfqs _
    (isAlgebraicSpace_pullback B S hS (τ ≫ f) (τ ≫ f) hU hU hY)
    (haqc U hU hUqc (τ ≫ f)) (𝟙 _)).of_iso B S hS
      (IsPullback.of_id_snd (f := pullback.mapDesc τ τ f)).isoPullback.symm

/-- **The morphism `b : R ⟶ Y` is quasi-compact.**  Let `f : X ⟶ Y` be a quasi-separated
morphism of algebraic spaces over `S`, let `τ : U ⟶ X` be a morphism and suppose
`a = τ ≫ f : U ⟶ Y` is quasi-compact.  Then the composite `R = U ×_X U ⟶ X ⟶ Y` is
quasi-compact.

The composite factors as `R ⟶ U ×_Y U ⟶ U ⟶ Y`.  Its first factor is quasi-compact by
part (4) of Stacks 03KN, the second is the base change of `a` along `a`, and the third is `a`;
Stacks 03HG composes them. -/
theorem isQuasiCompact_selfPullback_comp (τ : U ⟶ X) (f : X ⟶ Y)
    (hU : IsAlgebraicSpace B S hS U) (hY : IsAlgebraicSpace B S hS Y)
    (hfqs : IsQuasiSeparated B S hS f) (haqc : IsQuasiCompact B S hS (τ ≫ f)) :
    IsQuasiCompact B S hS (pullback.fst τ τ ≫ τ ≫ f) := by
  have hP := isAlgebraicSpace_pullback B S hS (τ ≫ f) (τ ≫ f) hU hU hY
  rw [selfPullback_comp_eq B S hS τ f]
  refine IsQuasiCompact.comp B S hS hP hY
    (isQuasiCompact_mapDesc B S hS τ τ f hfqs) ?_
  exact IsQuasiCompact.comp B S hS hU hY
    (isQuasiCompact_of_isPullback B S hS
      (IsPullback.of_hasPullback (τ ≫ f) (τ ≫ f)).flip haqc) haqc

/-- **The morphism `b : R ⟶ Y` is quasi-separated.**  Let `τ : U ⟶ X` and `f : X ⟶ Y` be
morphisms of algebraic spaces over `S` and suppose `a = τ ≫ f : U ⟶ Y` is quasi-separated.
Then the composite `R = U ×_X U ⟶ X ⟶ Y` is quasi-separated.

The same factorization `R ⟶ U ×_Y U ⟶ U ⟶ Y` is used.  Its first factor is quasi-separated
unconditionally, by part (1) of Stacks 03KN; the second is the base change of `a` along `a`,
quasi-separated by part (3) of Stacks 03KL; and the third is `a`.  The quasi-separated clause
of Stacks 03KQ composes them, which is why the sources of the two outer factors have to be
known to be algebraic spaces.

Quasi-separatedness of `f` itself is *not* needed: the comparison of fibre products carries no
hypothesis in part (1) of Stacks 03KN. -/
theorem isQuasiSeparated_selfPullback_comp (τ : U ⟶ X) (f : X ⟶ Y)
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (haqs : IsQuasiSeparated B S hS (τ ≫ f)) :
    IsQuasiSeparated B S hS (pullback.fst τ τ ≫ τ ≫ f) := by
  have hP := isAlgebraicSpace_pullback B S hS (τ ≫ f) (τ ≫ f) hU hU hY
  rw [selfPullback_comp_eq B S hS τ f]
  refine isQuasiSeparated_comp B S hS
    (isAlgebraicSpace_pullback B S hS τ τ hU hU hX) hP _ _
    (isQuasiSeparated_mapDesc B S hS τ τ f) ?_
  exact isQuasiSeparated_comp B S hS hP hU _ _
    (isQuasiSeparated_of_isPullback B S hS
      (IsPullback.of_hasPullback (τ ≫ f) (τ ≫ f)).flip haqs) haqs

end AlgebraicGeometry.Space

end

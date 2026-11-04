module

public import StacksFrontier.AlgebraicGeometry.ProjF1Reduction.Basic
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.UniversalClass

/-!
# The representing bijections of Tag 01O4, and what the bundle still costs

`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` has six fields.
`StacksFrontier.AlgebraicGeometry.ProjF1Reduction.Basic` reduced it to four, two of them being
formal. This file supplies three of those four — the universal pair, the representing bijections,
and their normalisation at the identity — and reduces the remaining one to a single equation in
each nonnegative degree.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackPair`: **the pullback of a pair along a
  morphism of test schemes**, built as the pair of the pullback of the pair's quadruple.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.canonicalHomEquiv`: **the representing bijections of
  Tag 01O4**, the inverse of the classifying map `pairClassifyingEquiv` at relative `Proj`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.bundleOfIsPullbackPair`: the bundle of Tag 01O4 from
  the single clause that `pullbackPair` is a pullback pair.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingHom_pullbackPair`: **the morphism
  classified by the pullback of a pair is the composite** — the classifying map of Tag 01O4 is
  natural in the test scheme.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackClassOf_quot_mk`: **the pullback of the class
  of a pair is the class of the pullback pair**, which is the computation-by-a-representative
  clause of the bundle.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.canonicalHomEquiv_id`: the representing bijections
  send the identity of relative `Proj` to the class of the universal pair.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isPullbackPair_pullbackPair_of_degreewise`: **the
  generator clause, the unit clause and the negative degrees of the pullback property are free.**
  Both isomorphisms the property asks for can be taken to be the identity, because the invertible
  sheaf of `pullbackPair` is the pullback of the invertible sheaf on the nose; and in a negative
  degree the source is a zero object.

## Implementation notes

**The pullback of a pair is built on the quadruple side.** A pair has a multiplicativity and a
unitality clause and a degree-one surjectivity clause, and the pullback of a quadruple already
discharges all three: `Quadruple.pullback` is available, with
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullbackApp_mul` and `_one` and
`epi_pullbackApp`. So `pullbackPair` is `quadruplePair` of `Quadruple.pullback`, and no clause of
a pair is reproved.

**The naturality of the classifying map is the naturality of the relative universal property.**
`pairClassifyingHom` is `quadrupleClassEquiv` after `quadrupleClass`, and
`Stacks.AlgebraicGeometry.ProjRepresentsF1.classifyingHom_pullback` is naturality for the former.
What connects them is `strictlyEquivalent_quadruple_quadruplePair`: the quadruple of the pair of
the pulled-back quadruple is strictly equivalent to that pulled-back quadruple, so the two have
the same class and `Fd.pullback_mk` identifies the class with the pullback of the class.

**The identity of the two isomorphisms in the pullback property is not an accident of spelling.**
`Quadruple.pullback` takes the invertible sheaf to `(pullbackFunctor (ringedSpaceHom g)).obj L`
and `IsPullbackPair` asks about `Scheme.Modules.pullback g`; those are equal by `rfl`
(`pullback_eq_pullbackFunctor`), which is what lets `Iso.refl` be offered for both.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)

## Not done here

No `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` is assembled in this file. The one
equation `isPullbackPair_pullbackPair_of_degreewise` still asks for here says that the degreewise
comparison `tensorAlgebraPullbackIsos` agrees, after the identification of the pieces of a tensor
algebra with tensor powers, with the comparison that `Twisting.pullbackApp` uses on the Laurent
algebra.

`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.BundleBridge` strips that equation of everything
but those two comparisons: `...ProjRepresentsF1.isPullbackPair_pullbackPair_of_bridge` derives
this clause from `...ProjRepresentsF1.TensorLaurentBridge`, which mentions only
`tensorAlgebraPullbackIsos`, `tensorToLaurent` and `...RelativeProjQcohSheaf.laurentPullback` —
no pair, no adjunction and no degree bookkeeping — and `...ProjRepresentsF1.bundleOfBridge`
assembles the bundle from it. So what that clause costs is an identification of two of the
repository's families `g^*(L^{⊗n}) ≅ (g^*L)^{⊗n}`, of the kind
`...RelativeProjQcohSheaf.pieceIso_hom_eq_laurentPullback` and
`...RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull` already carry out for two other
pairs; it is proved for this pair in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeProof`, as
`...ProjRepresentsF1.tensorPowerBridge`, and the bundle is assembled there as
`...ProjRepresentsF1.f1Bundle`. The two families do not recurse on the same side —
`...ProjRepresentsF1.pullbackTensorPowerIso` recurses on the left and `laurentPullback` has its
successor law on the right — so they meet through the concatenation law of
`SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso`, which the library carries
sectionwise as the field `tensorPieceIso_mul_left` and which
`...ProjRepresentsF1.generatorMul_comp_eq_id` lifts to an equation of morphisms; the
multiplicativity of `laurentPullback` in bidegree `(1, n+1)` then suffices, and no braiding and
no right-handed law is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (X : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData A)
  (hgen : IsGeneratedInDegreeOne A)

/-- **The pullback of a pair of Tag 01O4 along a morphism of test schemes**: the pair determined
by the pullback of the pair's quadruple. Its invertible sheaf is the pullback of the pair's
invertible sheaf, on the nose. -/
public def pullbackPair {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f) :
    F1Pair A TA (g ≫ f) :=
  quadruplePair A TA (g ≫ f) ((P.quadruple A TA f).pullback g)

/-- **Tag 01O4.** The classifying map of Tag 01O4 is natural in the test scheme: the morphism
classified by the pullback of a pair along `g` is `g` followed by the morphism classified by the
pair.

This is `classifyingHom_pullback`, the naturality of the relative universal property, transported
across `strictlyEquivalent_quadruple_quadruplePair`. -/
public theorem pairClassifyingHom_pullbackPair {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T)
    (P : F1Pair A TA f) :
    (pairClassifyingHom A TA (g ≫ f) X hgen
        (Quot.mk _ (pullbackPair A TA g P))).1 =
      g ≫ (pairClassifyingHom A TA f X hgen (Quot.mk _ P)).1 :=
  Eq.trans
    (congrArg
      (fun q : Quotient (Quadruple.setoid (g ≫ f) (situationAlgebra A) (1 : ℤ)) =>
        classifyingHom A X ⟨g ≫ f, q⟩)
      (Quotient.sound
        (strictlyEquivalent_quadruple_quadruplePair A TA (g ≫ f)
          ((P.quadruple A TA f).pullback g))))
    (classifyingHom_pullback A X g ⟨f, Quotient.mk _ (P.quadruple A TA f)⟩)

/-- The representing bijections of Tag 01O4, at relative `Proj` itself: the inverse of the
classifying map, whose bijectivity is `pairClassifyingHom_bijective`. -/
public def canonicalHomEquiv {T : Scheme.{u}} (f : T ⟶ S) :
    {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f} ≃ F1 A TA f :=
  (pairClassifyingEquiv A TA f (relativeProj A) hgen).symm

/-- The representing bijections take the identity of relative `Proj` to the class of the
universal pair. This is `pairClassifyingEquiv_symm_id` at the chosen relative homogeneous
spectrum. -/
public theorem canonicalHomEquiv_id :
    canonicalHomEquiv A TA hgen (relativeProj A).toBase ⟨𝟙 _, Category.id_comp _⟩ =
      Quot.mk _ (universalPair A TA (relativeProj A) hgen) :=
  pairClassifyingEquiv_symm_id A TA (relativeProj A) hgen

/-- **Tag 01O4.** The pullback of a strict isomorphism class along a morphism of test schemes is
the class of the pullback of a representative: the pullback operation the representing bijections
induce is computed by `pullbackPair`. -/
public theorem pullbackClassOf_quot_mk {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T)
    (P : F1Pair A TA f) :
    pullbackClassOf A TA (canonicalHomEquiv A TA hgen) g (Quot.mk _ P) =
      Quot.mk _ (pullbackPair A TA g P) :=
  (Equiv.symm_apply_eq (pairClassifyingEquiv A TA (g ≫ f) (relativeProj A) hgen)).2
    (Subtype.ext
      (pairClassifyingHom_pullbackPair A TA (relativeProj A) hgen g P).symm)

/-- **The bundle of Tag 01O4 costs one clause, not four.** The universal pair, the representing
bijections and their normalisation at the identity are supplied here; what is left is that the
pullback of a pair really is a pullback pair in the sense of `IsPullbackPair`. -/
public def bundleOfIsPullbackPair {ι : TensorAlgebraPullbackIsos.{u} TA}
    (hpb : ∀ {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f),
      IsPullbackPair A TA ι g P (pullbackPair A TA g P)) :
    F1Bundle A TA ι :=
  bundleOfHomEquiv A TA hgen (universalPair A TA (relativeProj A) hgen)
    (canonicalHomEquiv A TA hgen) (canonicalHomEquiv_id A TA hgen)
    (fun g P => ⟨pullbackPair A TA g P, hpb g P, pullbackClassOf_quot_mk A TA hgen g P⟩)

/-- **The pullback property of `pullbackPair` reduces to one equation in each nonnegative
degree.** Both isomorphisms the property asks for are the identity: the invertible sheaf of
`pullbackPair` is the pullback of the pair's invertible sheaf on the nose, so the generator clause
is `Category.comp_id` after `Category.id_comp` and the unit clause is `rfl`. In a negative degree
the common source is a zero object. -/
public theorem isPullbackPair_pullbackPair_of_degreewise {T T' : Scheme.{u}} {f : T ⟶ S}
    (g : T' ⟶ T) (P : F1Pair A TA f)
    (h : ∀ n : ℤ, 0 ≤ n → (Scheme.Modules.pullbackComp g f).inv.app (A.piece n) ≫
        (Scheme.Modules.pullback g).map (P.pullbackMap A TA n) ≫
        (tensorAlgebraPullbackIsos TA g P.L n).hom =
      (pullbackPair A TA g P).pullbackMap A TA n) :
    IsPullbackPair A TA (tensorAlgebraPullbackIsos TA) g P (pullbackPair A TA g P) := by
  refine ⟨Iso.refl _, Iso.refl _, ?_, ?_, fun n => ?_⟩
  · exact Eq.trans (Category.comp_id _) (Category.id_comp _).symm
  · rfl
  · rcases lt_or_ge n 0 with hn | hn
    · exact (isZero_pullbackPiece_of_neg A (g ≫ f) hn).eq_of_src _ _
    · exact Eq.trans
        (congrArg (fun z => (Scheme.Modules.pullbackComp g f).inv.app (A.piece n) ≫
          (Scheme.Modules.pullback g).map (P.pullbackMap A TA n) ≫ z)
          (Category.comp_id ((tensorAlgebraPullbackIsos TA g P.L n).hom)))
        (h n hn)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end

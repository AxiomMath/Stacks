module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Representation

/-!
# The representation of Tag 01O4 is determined by its bijections alone

`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` has eight fields: generation in
degree one, the universal pair, its canonicality, the representing bijections, their
normalisation at the identity, the pullback operation on strict-equivalence classes, its
computation by a representative, and the naturality of the bijections in the test scheme. Two of
them carry no content.

Given the bijections, there is only one pullback operation that can make them natural — conjugate
"compose with `g`" by them — and with that operation naturality is an identity. This file supplies
that operation and the resulting constructor, so that building a representation requires exactly
five things: generation in degree one, the universal pair, its canonicality, the bijections, and
their normalisation, together with the statement that pullback of a class is computed by the
canonical pullback of a representative.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackClassOf`: the pullback operation on classes
  determined by a family of bijections.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation.ofHomEquiv`: the constructor with
  the naturality field discharged and the pullback operation supplied.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackClassOf_homEquiv`: **the point of the file.**
  The bijections are natural for `pullbackClassOf` with no hypothesis whatever.

## Implementation notes

`pullbackClassOf` sends a class `c` over `f : T ⟶ S` to the class of `g ≫ h`, where `h` is the
morphism to relative Proj that the bijection assigns to `c`; the side condition
`(g ≫ h) ≫ π = g ≫ f` is associativity applied to `h ≫ π = f`. Naturality then reduces to
`Equiv.symm_apply_apply`, and the two subtype elements involved differ only in their proofs of a
`Prop`, so `Subtype.ext` closes it. No `rw` on a morphism of sheaves of modules occurs.

The reduction is of the same kind as
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_iff`, which removes the
existential over graded-algebra homomorphisms from the canonicality clause: in both cases a field
of the source's data is forced by the rest and is therefore not an input to be constructed.

## What is not done here

**No `F1Representation` is constructed and no project tag is attached.** The existence assertion
of Tag 01O4 is the family of bijections
`{g : T ⟶ Proj A // g ≫ π = f} ≃ F1 A TA f`, whose inverse is the construction of a morphism into
relative Proj out of a degree-one invertible quotient; that is untouched here and is what the
label `01O4 "represents_f1"` still waits on. This file narrows the input, it does not supply it.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The pullback operation on strict-equivalence classes determined by a family of representing
bijections: transport a class to the morphism it classifies, compose that morphism with `g`, and
transport back. -/
public def pullbackClassOf
    (homEquiv : ∀ {T : Scheme.{u}} (f : T ⟶ S),
      {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f} ≃ F1 A TA f)
    {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) : F1 A TA f → F1 A TA (g ≫ f) :=
  fun c => homEquiv (g ≫ f)
    ⟨g ≫ ((homEquiv f).symm c).1, by
      simpa [Category.assoc] using
        congrArg (fun k => g ≫ k) ((homEquiv f).symm c).2⟩

/-- **Naturality of the representing bijections is free.** For the pullback operation
`pullbackClassOf` the naturality field of `F1Representation` holds for *any* family of
bijections, with no compatibility hypothesis: it is `Equiv.symm_apply_apply` followed by
proof irrelevance in the subtype. -/
public theorem pullbackClassOf_homEquiv
    (homEquiv : ∀ {T : Scheme.{u}} (f : T ⟶ S),
      {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f} ≃ F1 A TA f)
    {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T)
    (h : {k : T ⟶ (relativeProj A).scheme // k ≫ (relativeProj A).toBase = f}) :
    homEquiv (g ≫ f)
        ⟨g ≫ h.1, by simpa [Category.assoc] using congrArg (fun k => g ≫ k) h.2⟩ =
      pullbackClassOf A TA homEquiv g (homEquiv f h) :=
  congrArg (homEquiv (g ≫ f))
    (Subtype.ext (congrArg (fun k => g ≫ k)
      (congrArg Subtype.val ((homEquiv f).symm_apply_apply h).symm)))

variable {ι : TensorAlgebraPullbackIsos.{u} TA} {D : TwistData A}

/-- **A bundle costs five inputs, not seven.** The pullback operation on classes and the
naturality of the bijections are supplied by
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackClassOf` and `pullbackClassOf_homEquiv`. -/
public def bundleOfHomEquiv
    (generated : IsGeneratedInDegreeOne A)
    (universal : F1Pair A TA (relativeProj A).toBase)
    (homEquiv : ∀ {T : Scheme.{u}} (f : T ⟶ S),
      {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f} ≃ F1 A TA f)
    (homEquiv_id : homEquiv (relativeProj A).toBase ⟨𝟙 _, Category.id_comp _⟩ =
      Quot.mk _ universal)
    (pullbackClass_rep : ∀ {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f),
      ∃ Q : F1Pair A TA (g ≫ f),
        IsPullbackPair A TA ι g P Q ∧
          pullbackClassOf A TA homEquiv g (Quot.mk _ P) = Quot.mk _ Q) :
    F1Bundle A TA ι where
  generated := generated
  universal := universal
  homEquiv := homEquiv
  homEquiv_id := homEquiv_id
  pullbackClass g := pullbackClassOf A TA homEquiv g
  pullbackClass_rep g P := pullbackClass_rep g P
  homEquiv_natural g h := pullbackClassOf_homEquiv A TA homEquiv g h

/-- **The representation of Tag 01O4, reduced to five inputs.** A representation is determined by
generation in degree one, the universal pair, its canonicality, the representing bijections,
their normalisation at the identity of relative Proj, and the clause that pullback of a class is
computed by the canonical pullback of a representative. The pullback operation on classes and
the naturality of the bijections are supplied here. -/
public def F1Representation.ofHomEquiv
    (generated : IsGeneratedInDegreeOne A)
    (universal : F1Pair A TA (relativeProj A).toBase)
    (universal_isCanonical : IsCanonicalTwistPair A TA D universal)
    (homEquiv : ∀ {T : Scheme.{u}} (f : T ⟶ S),
      {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f} ≃ F1 A TA f)
    (homEquiv_id : homEquiv (relativeProj A).toBase ⟨𝟙 _, Category.id_comp _⟩ =
      Quot.mk _ universal)
    (pullbackClass_rep : ∀ {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f),
      ∃ Q : F1Pair A TA (g ≫ f),
        IsPullbackPair A TA ι g P Q ∧
          pullbackClassOf A TA homEquiv g (Quot.mk _ P) = Quot.mk _ Q) :
    F1Representation A TA ι D :=
  { bundleOfHomEquiv A TA generated universal homEquiv homEquiv_id pullbackClass_rep with
    universal_isCanonical := universal_isCanonical }

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end

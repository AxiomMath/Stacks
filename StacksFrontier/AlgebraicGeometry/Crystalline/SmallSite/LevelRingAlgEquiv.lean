module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRingDividedPowers

/-!
# The level identification as an isomorphism of `Γ(S, ⊤)`-algebras

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine.
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` of
`SmallSite/EnvelopeCosimplicialComparison.lean` identifies the section ring of the level `(n, e)`
of the system of [Stacks, Tag 07JN] with the finite level `D(n)/(p)^{N + e}`, as a ring
isomorphism.  `Crystalline.tensorFormsEquivOfAlgEquiv` of
`ModuleDifferentials/FormsAlgEquivTensor.lean` — the crossing of that identification which the
degreewise composite of the isomorphism `ε` of [Stacks, Tag 07LF] has to make — needs it as an
isomorphism of algebras over the base `Γ(S, ⊤)`.  This file is that upgrade.

There is nothing to prove: `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE` is
exactly the statement that the identification carries the structure map of the level object to
the reduction of the structure map `Γ(S, ⊤) → D(n)`, and those two maps are the two algebra
structures.  What the file supplies is the two `Algebra` instances in the spellings the consumer
has, so that `AlgEquiv.ofRingEquiv` can be applied at all.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.levelEnvelopeAlgebra` — the
  `Γ(S, ⊤)`-algebra structure on the degree `n` of `...SmallSite.wholeSpaceEnvelopeRing`, namely
  `...SmallSite.wholeSpaceEnvelopeFromBase` read as an algebra.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv` —
  **the level identification as an isomorphism of `Γ(S, ⊤)`-algebras.**

## Implementation notes

The `Γ(S, ⊤)`-algebra structure on the section ring of the level object is
`Crystalline.GlobalCrystallineSituation.crysBaseAppLE` read as an algebra, and that is also the
instance `...affineCrysDifferentialForms_eq` states its conclusion under: the `V = ⊤` case of
`...affineBaseAppLE` is `...crysBaseAppLE` up to the proof argument of `Scheme.Hom.appLE`, so the
two are the same term.  Both are supplied as `letI` in the statement rather than as global
instances, for the reason `...SmallSite.wholeSpaceEnvelopeFromBase` records: a global instance at
one of the two spellings of a ring of sections competes with the instances already declared at
the other.

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved.**  What is supplied is the
hypothesis `f : B ≃ₐ[A] C` of `Crystalline.tensorFormsEquivOfAlgEquiv` at the level objects of
`...SmallSite.wholeSpaceSystem`; the transport itself is not performed here and no isomorphism of
cosimplicial objects is constructed.

No hypothesis is carried beyond `hp` and the two affineness instances that
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` itself carries.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The degree `n` of `...SmallSite.wholeSpaceEnvelopeRing` as a `Γ(S, ⊤)`-algebra**: the
structure map `...SmallSite.wholeSpaceEnvelopeFromBase` read as an algebra structure. -/
@[instance_reducible]
def levelEnvelopeAlgebra (n : ℕ) :
    Algebra (Γ(S.S.scheme, ⊤) : Type u)
      ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) :=
  (wholeSpaceEnvelopeFromBase hp n).toAlgebra

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The structure map of `levelEnvelopeAlgebra` is `...SmallSite.wholeSpaceEnvelopeFromBase`. -/
theorem levelEnvelopeAlgebra_algebraMap (n : ℕ) (a : Γ(S.S.scheme, ⊤)) :
    letI := levelEnvelopeAlgebra hp n
    algebraMap (Γ(S.S.scheme, ⊤) : Type u)
        ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) a =
      wholeSpaceEnvelopeFromBase hp n a :=
  rfl

/-- **The section ring of an object of `CRIS(X/S)` as a `Γ(S, ⊤)`-algebra**, through
`Crystalline.GlobalCrystallineSituation.crysBaseAppLE`.  This is the instance
`...affineCrysDifferentialForms_eq` states its conclusion under, the `V = ⊤` case of
`...affineBaseAppLE` being `...crysBaseAppLE`. -/
@[instance_reducible]
def crysSectionsAlgebra (A : CrystallineThickening S) :
    Algebra (Γ(S.S.scheme, ⊤) : Type u)
      ((structureSheaf S).obj.obj (op A) : Type u) :=
  (crysBaseAppLE S A.obj).hom.toAlgebra

/-- **The level identification is an isomorphism of `Γ(S, ⊤)`-algebras.**

`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` identifies the section ring of the level `(n, e)`
of the system of [Stacks, Tag 07JN] with `D(n)/(p)^{N + e}`; this says that it does so over the
base, the two algebra structures being the structure map of the level object and the reduction of
the structure map `Γ(S, ⊤) → D(n)`.  It is
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE` and nothing else.

This is the hypothesis `f` of `Crystalline.tensorFormsEquivOfAlgEquiv`, whose other two
hypotheses at these objects are
`...SmallSite.isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv` and
`...SmallSite.levelSections_smul_eq`.  **No tag attribute is placed.** -/
def wholeSpaceEnvelopeRingLevelAlgEquiv (n e : ℕ) :
    letI := levelEnvelopeAlgebra hp n
    letI := crysSectionsAlgebra
      (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)
    ((structureSheaf S).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) : Type u) ≃ₐ[
        (Γ(S.S.scheme, ⊤) : Type u)]
      (((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u))
            (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) :=
  letI := levelEnvelopeAlgebra hp n
  letI := crysSectionsAlgebra
    (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)
  { wholeSpaceEnvelopeRingLevelEquiv hp n e with
    commutes' := wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE hp n e }

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

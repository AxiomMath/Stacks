module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Commutes
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafCoproductInt

/-!
# The ungraded realization of a sheaf of graded algebras, and pullback

Let `g : Z ⟶ X` be a morphism of schemes and let `A` be a sheaf of graded `𝒪_X`-algebras whose
homogeneous multiplication commutes. There are two sheaves of commutative `𝒪_Z`-algebras one can
form from `A` and `g`:

* pull `A` back degreewise, by `Stacks.Conormal.gradedPullback`, and realize the result:
  `Stacks.RelativeSpec.gradedAlgebraSheaf Z (g^*A)`;
* realize `A` on `X` and pull the resulting algebra sheaf back, by
  `Stacks.AffineAlgebraEquivalence.algebraPullback`:
  `(algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A)`.

This file identifies their **underlying `𝒪_Z`-modules**. The degreewise pullback is the easy half
of the comparison and is `rfl` (`Stacks.Conormal.gradedPullback_piece`); what is proved here is
that the two realizations agree after the realization has been taken, which is not formal: the
realization is a sheafified direct sum over all of `ℤ`, and the statement is that pullback moves
across that sheafified sum.

## Main definitions

* `Stacks.RelativeSpec.pullbackIntCoprodIso`: pullback of the `ℤ`-indexed coproduct of the
  homogeneous pieces is the `ℤ`-indexed coproduct of the pieces of the degreewise pullback.
* `Stacks.RelativeSpec.pullbackUnderlyingModuleIso`: **the `𝒪_Z`-module underlying the
  realization of `g^*A` is the pullback of the `𝒪_X`-module underlying the realization of `A`.**

## Implementation notes

**What this is and is not, and which tag owns the rest.** [Stacks, Tag 01LX] part (2) — the base
change `S' ×_S \underline{Spec}_S(𝒜) = \underline{Spec}_{S'}(g^*𝒜)` of a relative spectrum — is
proved, in full generality for a quasi-coherent algebra sheaf, as
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso` and
`relativeSpecPullbackIso`. There `g^*𝒜` means
`Stacks.AffineAlgebraEquivalence.algebraPullback`, the pushout
`g⁻¹𝒜 ⊗_{g⁻¹𝒪_S} 𝒪_{S'}` of sheaves of commutative rings, and nothing in the tag mentions a
grading. So the comparison this file is about carries **no tag**: it is the plumbing between
01LX part (2) and the graded input of [Stacks, Tag 0897], where the source sets `𝓑 = f^*B̃` and
then writes `\underline{Spec}_X(𝓑)` without further comment. 01LX part (2) is reused, not
mirrored; what it cannot supply is precisely the identification of the algebra pullback of a
realization with the realization of a degreewise pullback, because its statement never names a
realization.

**Why the `ℤ`-indexed coproduct and not the `ℕ`-indexed one.** `SheafOfModules.GradedAlgebra` is
graded by `ℤ`, following [Stacks, Tag 0FQW], and `Stacks.Conormal.gradedPullback` pulls back every
degree. Routing the comparison through the `ℕ`-indexed
`Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule` would need the hypothesis
`hzero : ∀ n < 0, IsZero (A.piece n)` on both sides, which is not part of 0897's statement; the
`ℤ`-indexed `Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule` needs no such hypothesis, and
the two `Stacks.Conormal.gradedPullback_piece` identities that match the index families up are
`rfl`.

**Which spelling of the commutativity hypothesis.** The `hc` the pulled-back realization needs is
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm` rather than its scheme-level restatement
`Stacks.Conormal.gradedPullback_mul_comm`
(`StacksFrontier/AlgebraicGeometry/Constructions/PullbackGradedAlgebraSheaf.lean:69`), which is the
same term. The two are interchangeable; the former is taken because its module costs 33 modules
against that one's 810, and nothing else here needs the rest.

**What remains for the algebra-level isomorphism.** The module identification below is one of the
two halves of
```
(algebraPullback g).obj (gradedAlgebraSheaf X A hc) ≅ gradedAlgebraSheaf Z (gradedPullback g A)
```
exactly as `AlgebraicGeometry.pushforwardTildeIso` ([Stacks, Tag 01I9]) is the module half of the
affine comparison `(Spec B → Spec A)_* 𝒪_{Spec B} ≅ gradedAlgebraSheaf (Spec A) B̃`. It does not
by itself give the algebra isomorphism, and **the obvious way of closing the gap is blocked while
a second way is not**, so which one a proof takes matters.

*Blocked.* Comparing the two underlying modules directly needs the module underlying
`(algebraPullback g).obj B` to be the pullback of the module underlying `B`. That is
`Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso`, which is stated conditionally on
invertibility of `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison` — the residual
input of [Stacks, Tag 01SA] and [Stacks, Tag 02KH], whose implementation notes spell out the three
steps it needs — and it needs in addition the identification of the module underlying `g⁻¹B` with
the inverse image of the module underlying `B`, which that file states it does not address. Those
two open inputs are owned by 01SA and 02KH; this file assumes neither.

*Not blocked.* Both sides carry a universal property, so the isomorphism can be assembled as a
pair of mutually inverse morphisms without ever describing the sections of the pushout.

* Out of the realization: `Stacks.GradedAlgebra.totalSheafLift` maps out of `R(g^*A)` given a
  morphism of presheaves of rings out of `totalPresheaf`, and
  `Stacks.GradedAlgebra.totalRingHomOfFamily` supplies that objectwise from a degreewise family
  of additive maps `(g^*A)_n ⟶ (algebraPullback g).obj (R A)`. Those come by adjointness from
  `A_n ⟶ R(A) ⟶ g_*((algebraPullback g).obj (R A))`, the second arrow being
  `Limits.pushout.inl` after the unit — no description of the pushout is needed, only a map
  into it. Multiplicativity holds on pullback-unit images by
  `Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit`
  (`StacksFrontier/AlgebraicGeometry/PullbackTensor/GradedAlgebra.lean:636`) and extends to all
  local sections by `Stacks.RingedSpace.pullbackBilinear_heq_ext`
  (`StacksFrontier/AlgebraicGeometry/SymmetricPullback/BilinearExt.lean:147`), the same device
  `Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm` uses; the unit is
  `pullbackGradedAlgebra_one_eval` (ibid.:644). `Stacks.CommRingSheaf.homMk'` is what reads
  the result as a morphism of sheaves of *commutative* rings out of the lift.
* Out of the pushout: `Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout` gives
  `IsPushout.desc`, whose two legs are the structure map of `R(g^*A)` and the adjoint transpose
  of a morphism `R(A) ⟶ g_* R(g^*A)` built the same way, from the degreewise adjunction units.
* The two composites are then identities by the two uniqueness statements —
  `Stacks.GradedAlgebra.totalSheaf_hom_ext` one way and the pushout the other — each of which
  reduces to the generators where both formulas are known.

Neither direction exists yet; `totalRingHomOfFamily` and `Stacks.CommRingSheaf.homMk'` are the
two devices either direction needs, and both are available.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

/-- Pullback of sheaves of modules along a morphism of schemes preserves coproducts of any
shape: it is the left adjoint of the pushforward. -/
instance preservesColimits_schemeModulesPullback :
    PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits

/-- **The pullback of the `ℤ`-indexed coproduct of the homogeneous pieces of a sheaf of graded
algebras is the `ℤ`-indexed coproduct of the pieces of its degreewise pullback.** The two index
families agree because `Stacks.Conormal.gradedPullback_piece` holds by `rfl`. -/
def pullbackIntCoprodIso :
    (Scheme.Modules.pullback g).obj (∐ fun n : ℤ => A.piece n) ≅
      ∐ fun n : ℤ => (Stacks.Conormal.gradedPullback g A).piece n :=
  PreservesCoproduct.iso (Scheme.Modules.pullback g) fun n : ℤ => A.piece n

variable (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
  (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- **The `𝒪_Z`-module underlying the ungraded realization of the degreewise pullback `g^*A` is
the pullback of the `𝒪_X`-module underlying the ungraded realization of `A`.**

Both realizations are the sheafification of the direct sum of their homogeneous pieces over all
of `ℤ`, by `Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule`, and pullback of sheaves of
modules preserves that coproduct. No vanishing in negative degrees is assumed, so this applies
to the `ℤ`-graded algebras of [Stacks, Tag 0FQW] as they stand. -/
def pullbackUnderlyingModuleIso :
    (Scheme.Modules.pullback g).obj
        (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf X A hc)) ≅
      AlgebraSheaf.underlyingModule (gradedAlgebraSheaf Z (Stacks.Conormal.gradedPullback g A)
        (Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc)) :=
  (Scheme.Modules.pullback g).mapIso
      (Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule X A hc).symm ≪≫
    pullbackIntCoprodIso g A ≪≫
      Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule Z (Stacks.Conormal.gradedPullback g A)
        (Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc)

end Stacks.RelativeSpec

end

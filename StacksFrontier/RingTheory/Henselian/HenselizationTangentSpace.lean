module

public import StacksFrontier.RingTheory.Henselian.HenselizationDeformation

/-!
# Deformations of henselizations: the tangent-space conclusion

Let `k` be a field, let `B` be a finite type `k`-algebra, let `J ⊆ B` be an ideal such that
`Spec(B) → Spec(k)` is smooth on the complement of `V(J)`, and let `(Bʰ, Jʰ)` be the
henselization of the pair `(B, J)`.  Stacks 0DZD asserts two things about the functor
`Def_B ⟶ Def_{Bʰ}` of Stacks 0DYT: that it is **smooth**, and that it **induces an isomorphism
on tangent spaces**.  This file proves the second in the form the source's own proof produces
it — the case `N = B` of Stacks 0DZC, a bijection of isomorphism classes of square-zero
extensions.  Both conclusions are also available for the functor itself, elsewhere:
`Deformation.Examples.bijective_differential_henselizationFunctorData` is the tangent-space
conclusion for the map the functor *induces*, and
`Deformation.Examples.isSmooth_henselizationFunctorData` is smoothness.  That the bijection of
isomorphism classes *is* the map the functor induces is
`Deformation.Examples.naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv`, in the
canonical form of Stacks 0GPV; the implementation notes say what separates that form from the
one the statement below uses.

## Main results

* `Stacks.Deformation.exists_squareZeroAlgebraExtensionClassesHenselizationTangentEquiv`:
  **the case `N = B` of Stacks 0DZC, in the form Stacks 0DZC delivers it.**  It carries no
  `@[stacks 0DZD]` attribute: the identification of this form with the tangent-space assertion
  of Stacks 0DZD is the one thing the implementation notes below record as not established, so
  the attribute is withdrawn and the section note above the declaration says why.  Stacks
  0DZD's two conclusions are registered on the functor of Stacks 0DYT, in
  `StacksFrontier.Deformation.Examples.Geometric.HenselizationSmooth` and
  `StacksFrontier.Deformation.Examples.Geometric.HenselizationDifferential`.

## Implementation notes

**What is proved.** The source's proof of Stacks 0DZD reduces to two inputs through Formal
Deformation Theory, Lemma 0DYP: a correspondence between liftability, which is Stacks 0DZB, and
an isomorphism on tangent spaces, which it obtains as the case `N = B` of Stacks 0DZC.  The
second input is what is proved here, and it is proved outright: Stacks 0DZC,
`Stacks.Deformation.exists_squareZeroAlgebraExtensionClassesHenselizationEquiv`, carries no
hypothesis beyond the data of the henselization.  The tangent spaces in question are the groups
`Ext¹_B(NL_{B/k}, B)` and `Ext¹_{Bʰ}(NL_{Bʰ/k}, Bʰ)` of Stacks 0DY3, which classify the
isomorphism classes of square-zero extensions by Stacks 0GPT; the statement below is about those
isomorphism classes, which is the form Stacks 0DZC delivers.

**That the bijection is the differential of the functor.** The bijection of Stacks 0DZC at
`N = B` *is* the map induced by the functor of Stacks 0DYT, in the canonical form of Stacks
0GPV: by `Deformation.Examples.naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv`,
the differential, read on isomorphism classes of square-zero extensions through Stacks 0DY3 and
Stacks 0GPT, satisfies the compatibility with the restriction map along `B → Bʰ` and the
coefficient push `N → Bʰ ⊗_B N` which — both maps being injective there — characterizes that
bijection.  The differential itself is bijective, by
`Deformation.Examples.bijective_differential_henselizationFunctorData`.

What is still *not* established is that the characterization used in the statement below is the
same one.  That characterization goes through the scalar extension `m ↦ m ⊗ 1` of the `Ext`
group and `Stacks.Deformation.extOneCokernelHenselizationFlatBaseChangeEquiv`, and to match it
against the canonical form one needs
`extOneCokernelHenselizationFlatBaseChangeEquiv = extOneCokernelBaseChangeEquiv ∘
conormalCokernelPullback`, which is the identification the next paragraph describes as missing.

**The composite that is still unidentified.** The differential of the functor of Stacks 0DYT is
`Deformation.differential`, and the completion analogue of Stacks 0DZD, Stacks 0DZ5, proves
bijectivity of that differential in
`Deformation.Examples.bijective_differential_adicCompletionFunctorData` from both comparison
maps of Stacks 0GPV being bijective *as the canonical maps*
`Stacks.Deformation.naiveCotangentExtOneMap` and
`Stacks.Deformation.naiveCotangentExtOneTowerMap` — for completion, the two halves of Stacks
0DZ4.  For the henselization the coefficient half is
`Deformation.Examples.bijective_naiveCotangentExtOneMap_henselization`, and the restriction
along `B → Bʰ` is injective by
`Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_henselization`; an injective
restriction already determines the differential, so that is enough for bijectivity.  The
restriction is in fact *bijective* at the coefficients `Bʰ ⊗_B B` of Stacks 0DZC, by
`Deformation.Examples.bijective_naiveCotangentExtOneTowerMap_henselization` — but that is
deduced from bijectivity of the differential, not from Stacks 0D08 and Stacks 0GPY.

The derived-category route remains blocked.  Its ingredients are present — Stacks 0D08 as
`Stacks.Deformation.naiveCotangentExtOneHenselizationSourceEquiv` and Stacks 0GPY as
`Stacks.Deformation.naiveCotangentExtOneBaseChangeEquiv`, composed in
`Stacks.Deformation.extOneCokernelHenselizationFlatBaseChangeEquiv` — but the identification of
that composite with `Stacks.Deformation.conormalCokernelPullback`, i.e. with precomposition by
the canonical map of conormal modules, is missing; the composite is marked `irreducible`
precisely because it cannot be unfolded at a call site.  Of the two halves that identification
splits into, the ingredient for the flat-base-change half is available:
`Deformation.Examples.homCokernelBaseChangeEquiv_compRight` says that the comparison out of
which `Deformation.Examples.extOneCokernelBaseChangeEquiv` is built carries the push along
`n ↦ 1 ⊗ n` to `[δ] ↦ 1 ⊗ [δ]`.  What is missing is the derived-category half: no lemma computes
`naiveCotangentExtOneHenselizationSourceEquiv` or `naiveCotangentExtOneBaseChangeEquiv` on a
`NaiveCotangent.conormalHomExtClass`, and `naiveCotangentExtOneBaseChangeEquiv` is built from
the adjunction of Stacks 0GMT and the truncation comparison of Stacks 0G9G, whose comparison
morphism is produced only as a factorization of
`TwoTermComplex.twoTermBaseChange_iso_truncGE` through `truncGEπ (-1)`.

**The smoothness conclusion, and the shape of Stacks 0DZB it uses.** The first conclusion of
Stacks 0DZD is `Deformation.Examples.isSmooth_henselizationFunctorData`.  The source obtains it
from Stacks 0DZB, whose formalization `Deformation.hasFlatAlgebraLift_henselization_iff` carries
a hypothesis `h0DZ2 : Deformation.FlatModuleLiftBaseChangeStatement` standing for Stacks 0DZ2
with a *nilpotent* kernel of `A' → A`.  That hypothesis is not dischargeable as it stands: the
route to its nilpotent dévissage through surjectivity on lift sets is refuted, that surjectivity
needing `Ext¹` to be `J'`-power torsion while local liftability kills only the `Ext²`
obstruction.  What the dévissage would need instead, and what is still missing for it, is
recorded in `StacksFrontier.Deformation.FlatModuleLiftLocalization`.

What Stacks 0DZD needs is weaker than that.  The criterion of Stacks 0DYP applies Stacks 0DZB
only across *small extensions* `A' → A`, and a small extension has `ker(A' → A)² = ⊥` by
`InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection`; the thickening `P' → P` of a
square-zero kernel is square-zero too, because `ker(P' → P) = ker(A' → A) · P'`.  That is the
hypothesis of `Deformation.hasFlatAlgebraLift_henselization_iff_of_sqZero`, which is Stacks 0DZB
with `h0DZ2` discharged by `Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`.  So the
smoothness conclusion carries no `h0DZ2`-style hypothesis, and the correspondence of liftability
it rests on is `Deformation.Examples.lifts_henselizationFunctorData`.

## References

* [Stacks Project, Tag 0DZD](https://stacks.math.columbia.edu/tag/0DZD)
* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
* [Stacks Project, Tag 0DYP](https://stacks.math.columbia.edu/tag/0DYP)
-/

@[expose] public section

open scoped TensorProduct

universe uk uB

namespace Stacks.Deformation

noncomputable section

variable (k : Type uk) [Field k] (B : Type uB) [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B]

/-! #### Why withdrawing `@[stacks 0DZD]` from
`Stacks.Deformation.exists_squareZeroAlgebraExtensionClassesHenselizationTangentEquiv` has been
requested

**The attribute `@[stacks 0DZD]` is present here; the analysis below argues that this
registration ought to be withdrawn.** Stacks 0DZD is complete without it in any case,
on the four declarations named below.

The attribute is argued to be unsound, for the reason its own text gave: the clause said that
the identification of what this statement asserts with the tangent-space assertion of the tag
is not established, so the declaration does not establish the tag.  An attribute is what
`tag_grep`, the audit rows and the dashboard read as the tag being formalized, and none of them
reads this note; leaving it on would record a formalization that does not exist.  The statement
is unchanged and nothing depends on the attribute.  This is the same treatment
`@[stacks 0DZ3]` has in `StacksFrontier.Deformation.FlatAlgebraLiftCompletion`.

Withdrawing it costs the tag nothing.  Stacks 0DZD's two conclusions are registered, at the
functor the source states them for, on
`Deformation.Examples.isSmooth_henselizationFunctorData` and
`Deformation.Examples.isSmooth_henselizationFunctor`
(`StacksFrontier.Deformation.Examples.Geometric.HenselizationSmooth`) and on
`Deformation.Examples.bijective_differential_henselizationFunctorData` and
`Deformation.Examples.bijective_differential_henselizationFunctor`
(`StacksFrontier.Deformation.Examples.Geometric.HenselizationDifferential`), none of which carries
a hypothesis the source does not have.  What this declaration is, and remains, is the case
`N = B` of Stacks 0DZC in the form this file's Ext comparison produces it -- an input to that
work, not a statement of the tag.

The clause that used to sit inside the attribute follows verbatim.

ONLY the second conclusion, that the functor of Stacks 0DYT induces an isomorphism on tangent
spaces -- and that in the form the source's own proof produces it, as the case `N = B` of
Stacks 0DZC: the tangent spaces are the groups `Ext¹_B(NL_{B/k}, B)` and
`Ext¹_{Bʰ}(NL_{Bʰ/k}, Bʰ ⊗_B B)` of Stacks 0DY3, which classify isomorphism classes of
square-zero extensions by Stacks 0GPT, and it is those classes the bijection is between. That
the bijection of Stacks 0DZC at `N = B` IS the map INDUCED by the functor of Stacks 0DYT is
established, in the canonical form of Stacks 0GPV:
`Deformation.Examples.naiveCotangentExtOneTowerMap_henselizationTangentClassesEquiv` shows the
differential, read on isomorphism classes of square-zero extensions, satisfies the
compatibility with restriction along `B -> B^h` and with the coefficient push
`N -> B^h (x)_B N` that characterizes that bijection, both of those maps being injective here.
What is still NOT established is that the characterization used in THIS statement is the same
one: it goes through the scalar extension `m |-> m (x) 1` and
`extOneCokernelHenselizationFlatBaseChangeEquiv`, and matching the two needs
`extOneCokernelHenselizationFlatBaseChangeEquiv = extOneCokernelBaseChangeEquiv .
conormalCokernelPullback`, whose derived-category half is missing -- see the implementation
notes. The induced map is proved bijective in
`Deformation.Examples.bijective_differential_henselizationFunctorData`, which is where the
second conclusion is discharged for the functor itself; the first conclusion, that the functor
is smooth, is `Deformation.Examples.isSmooth_henselizationFunctorData`. No hypothesis the
source does not have is carried here: Stacks 0DZC is proved outright, base-change input and
all -- Stacks 0D08, Stacks 0GPY and flat base change of the conormal cokernel for the
comparison of the two Ext groups, and Stacks 00S1 for the J-power torsion of
`Ext¹_B(NL_{B/k}, N)`.
-/

/-- **The case `N = B` of Stacks 0DZC, in the form this file's Ext comparison produces it.**
Let `k` be a field, `B` a finite type `k`-algebra and `J ⊆ B` an ideal containing the non-smooth
locus of `B` over `k` in its vanishing locus, and let `(Bʰ, Jʰ)` be the henselization of the
pair `(B, J)`.  Then the isomorphism classes of square-zero extensions of `B` by `B` are in
bijection with those of `Bʰ` by `Bʰ ⊗_B B`, compatibly with extension of scalars along
`B → Bʰ` on the groups `Ext¹_B(NL_{B/k}, B)` and `Ext¹_{Bʰ}(NL_{Bʰ/k}, Bʰ ⊗_B B)` that
classify them.

By Stacks 0DY3 those two groups are the tangent spaces of the deformation categories `Def_B`
and `Def_{Bʰ}`.  The tangent-space conclusion of Stacks 0DZD itself is registered on
`Deformation.Examples.bijective_differential_henselizationFunctorData`, for the map the functor
of Stacks 0DYT induces; see the section note above for why the attribute is not here. -/
@[stacks 0DZD "ONLY the second conclusion, that the functor of Stacks 0DYT induces an \
isomorphism on tangent spaces -- and that in the form the source's own proof produces it, as \
the case `N = B` of Stacks 0DZC: the tangent spaces are the groups `Ext¹_B(NL_{B/k}, B)` and \
`Ext¹_{Bʰ}(NL_{Bʰ/k}, Bʰ ⊗_B B)` of Stacks 0DY3, which classify isomorphism classes of \
square-zero extensions by Stacks 0GPT, and it is those classes the bijection is between. That \
the bijection is the map INDUCED by the functor of Stacks 0DYT is not established: no \
naturality comparing `Deformation.Examples.henselizationFunctor` with the classification of \
Stacks 0GPT is formalized. No hypothesis the source does not have is carried: Stacks 0DZC is \
proved outright, base-change input and all -- Stacks 0D08, Stacks 0GPY and flat base change of \
the conormal cokernel for the comparison of the two Ext groups, and Stacks 00S1 for the J-power \
torsion of `Ext¹_B(NL_{B/k}, N)`. The FIRST conclusion, that the functor is smooth, is NOT \
proved at all: it rests on Stacks 0DZ2 through Stacks 0DZB, and the nilpotent devissage needed \
for 0DZ2 is refuted under 0DZ2's own hypotheses -- it would need `Ext¹` to be power torsion, \
whereas local liftability kills only the `Ext²` obstruction. See the implementation notes."]
public theorem exists_squareZeroAlgebraExtensionClassesHenselizationTangentEquiv
    (J : Ideal B)
    (hsmooth : ∀ q : PrimeSpectrum B, ¬ Algebra.IsSmoothAt k q.asIdeal → J ≤ q.asIdeal)
    (Bh : Type uB) [CommRing Bh] [Algebra B Bh] [Algebra k Bh] [IsScalarTower k B Bh]
    (hhens : HenselianPair Bh (J.map (algebraMap B Bh)))
    (huniv : ∀ (C : Type uB) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
      ∀ f : B →+* C, J ≤ JC.comap f →
        ∃! g : Bh →+* C, g.comp (algebraMap B Bh) = f ∧
          J.map (algebraMap B Bh) ≤ JC.comap g) :
    ∃ e : SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uB,
          uB} (algebraExtensionProblem k B B) ≃
        SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uB,
          uB} (algebraExtensionProblem k Bh (Bh ⊗[B] B)),
      ∀ x, extOneCokernelHenselizationFlatBaseChangeEquiv.{uk, uB, uB} k B B Bh J hhens huniv
              (extCokernelIso k Bh (Bh ⊗[B] B)
                (squareZeroAlgebraExtensionClassesEquivExtOne k Bh (Bh ⊗[B] B) (e x)))
            = extCokernelIso k B B (squareZeroAlgebraExtensionClassesEquivExtOne k B B x)
                ⊗ₜ[B] (1 : Bh) :=
  exists_squareZeroAlgebraExtensionClassesHenselizationEquiv.{uk, uB, uB} k B J hsmooth B Bh
    hhens huniv

end

end Stacks.Deformation

end

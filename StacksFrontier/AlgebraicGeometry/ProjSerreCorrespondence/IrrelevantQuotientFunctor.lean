module

public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantVanishing
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.SerreClass

/-!
# `M ↦ M̃` descends to the quotient `Mod^fg_A / Mod^fg_{A, irrelevant}`

Let `A` be a graded ring which is Noetherian as a ring, let `X = Proj(A)` and let `d` be a
positive integer. The arrow of Stacks 0BXF has the quotient category
`Mod^fg_A / Mod^fg_{A, irrelevant}` for its source. This file produces the functor out of that
quotient which the proposition asserts is an equivalence: the restriction of `M ↦ M̃` to the
finitely generated graded modules inverts every morphism which is an isomorphism modulo the
irrelevant ones, so it factors through the localization.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.irrelevantQuotientFunctor`: **the functor
  `Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Mod(𝒪_X)` induced by `M ↦ M̃`.**

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.irrelevantModules_le_kernel`: `M ↦ M̃` kills
  the irrelevant finitely generated graded modules, in every generation degree.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isInvertedBy_isoModSerre_irrelevantModules`:
  a morphism of finitely generated graded modules whose kernel and cokernel are irrelevant
  becomes an isomorphism of associated sheaves.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.additive_irrelevantQuotientFunctor`: the
  induced functor is additive.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.irrelevantQuotientFunctorFac`: the induced
  functor composed with the quotient functor is `M ↦ M̃` again.

## Implementation notes

The restriction of `M ↦ M̃` to `Mod^fg_A`, and its exactness, are
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.finiteAssociatedSheafFunctor` and the two
preservation lemmas beside it in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/SerreClass.lean`; they are shared with
every other tag which quotients `Mod^fg_A` by a Serre class and are not restated here.

For an exact functor, inverting the isomorphisms modulo a Serre class is *equivalent* to killing
the class — Mathlib's `CategoryTheory.ObjectProperty.isoModSerre_isInvertedBy_iff`. So the only
mathematical input beyond exactness is that `M ↦ M̃` kills an irrelevant finitely generated
module, which is `isZero_associatedModuleSheafFunctor_obj_of_isIrrelevant`, valid for every
generation degree `d` — this is where the situation differs from the degree-one, torsion-class one
of Tag 0BXD. The factorization is then Mathlib's `Localization.lift` applied to the quotient
functor, which is a localization functor for `isoModSerre` by construction.

## What this is not

This is the *arrow* of Stacks 0BXF, not the proposition. The proposition asserts that the
induced functor is an equivalence onto `Coh(𝒪_X)`, and identifies its quasi-inverse with
`ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))`.

Of the three conditions for an equivalence, **faithfulness** is
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.faithful_irrelevantQuotientFunctor` in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/Faithful.lean`, by way of the kernel
identification `irrelevantModules_eq_kernel` and Tag 06XK. Essential surjectivity is
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.essSurj_coherentIrrelevantQuotientFunctor` in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/EssentiallySurjective.lean`, where the
quasi-inverse `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))` is corestricted to `Mod^fg_A` by clause (4) of Tag
0B5Q and its associated sheaf identified with `ℱ` by
`truncatedTwistedSectionsIsoOfNoetherian`. Fullness comes with the unit, and the whole
proposition is
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_coherentIrrelevantQuotientEquivalence` in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/Equivalence.lean`.

The target here is all sheaves of `𝒪_X`-modules; the corestriction to the proposition's own
target `Coh(𝒪_X)` is
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentIrrelevantQuotientFunctor` in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/CoherentTarget.lean`, isomorphic to this
functor followed by the inclusion of the coherent sheaves and faithful with it. It rests on the
coherence of `M̃` for `M` finitely generated over a Noetherian graded ring, the finiteness half
of Tag 0B5Q, which is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheaf`. The
inventory of how the equivalence is assembled is in the module docstring of
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/IrrelevantModules.lean`.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 02MQ](https://stacks.math.columbia.edu/tag/02MQ)
* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] [IsNoetherianRing S] {d : ℕ}

omit [IsNoetherianRing S] in
/-- **The kernel of `M ↦ M̃` on `Mod^fg_A` contains the irrelevant modules**, in every
generation degree. -/
public theorem irrelevantModules_le_kernel (hd : 0 < d) :
    irrelevantModules.{u, u, w} 𝒮 d ≤ (finiteAssociatedSheafFunctor.{u, w} 𝒮).kernel :=
  fun M hM =>
    have := M.property
    isZero_associatedModuleSheafFunctor_obj_of_isIrrelevant 𝒮 hd M.obj hM

/-- **A morphism of finitely generated graded modules whose kernel and cokernel are irrelevant
induces an isomorphism of associated sheaves.** This is what lets `M ↦ M̃` factor through the
quotient category of Stacks 0BXF. -/
public theorem isInvertedBy_isoModSerre_irrelevantModules (hd : 0 < d) :
    haveI := isSerreClass_irrelevantModules 𝒮 hd
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒮 d)).IsInvertedBy
      (finiteAssociatedSheafFunctor.{u, w} 𝒮) := by
  have := isSerreClass_irrelevantModules 𝒮 hd
  have := preservesFiniteLimits_finiteAssociatedSheafFunctor.{u, w} 𝒮
  have := preservesFiniteColimits_finiteAssociatedSheafFunctor.{u, w} 𝒮
  exact (ObjectProperty.isoModSerre_isInvertedBy_iff (irrelevantModules.{u, u, w} 𝒮 d)
    (finiteAssociatedSheafFunctor.{u, w} 𝒮)).2 (irrelevantModules_le_kernel 𝒮 hd)

/-- **The functor `Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Mod(𝒪_X)` induced by `M ↦ M̃`.** This is
the functor of which Stacks 0BXF asserts that it is an equivalence onto `Coh(𝒪_X)`. -/
@[stacks 0BXF "the arrow of the proposition: the functor out of the quotient category \
Mod^fg_A / Mod^fg_{A, irrelevant} induced by M ↦ M~, obtained by factoring that functor's \
restriction to the finitely generated graded modules through the localization at the \
isomorphisms modulo the irrelevant ones. Its target is written as all sheaves of O_X-modules; \
its corestriction to the proposition's own target Coh(O_X) is \
coherentIrrelevantQuotientFunctor. Of the proposition's assertion that this functor is an \
equivalence, faithfulness is proved (faithful_irrelevantQuotientFunctor), for the corestriction \
too (faithful_coherentIrrelevantQuotientFunctor); the whole proposition is now proved, as \
exists_coherentIrrelevantQuotientEquivalence of CoherentEquivalence.lean. \
The quasi-inverse F ↦ ⨁_{n ≥ 0} Γ(X, F(n)) is identified on objects, by \
truncatedTwistedSectionsIsoOfNoetherian, and assembled into a functor to all graded modules, \
truncatedTwistedSectionsFunctor"]
public def irrelevantQuotientFunctor (hd : 0 < d) :
    IrrelevantQuotient 𝒮 hd ⥤ SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  Localization.lift (finiteAssociatedSheafFunctor.{u, w} 𝒮)
    (isInvertedBy_isoModSerre_irrelevantModules 𝒮 hd) (toIrrelevantQuotient 𝒮 hd)

/-- The induced functor composed with the quotient functor is `M ↦ M̃` again. -/
public def irrelevantQuotientFunctorFac (hd : 0 < d) :
    toIrrelevantQuotient 𝒮 hd ⋙ irrelevantQuotientFunctor 𝒮 hd ≅
      finiteAssociatedSheafFunctor.{u, w} 𝒮 :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  Localization.fac (finiteAssociatedSheafFunctor.{u, w} 𝒮)
    (isInvertedBy_isoModSerre_irrelevantModules 𝒮 hd) (toIrrelevantQuotient 𝒮 hd)

/-- **The induced functor is additive**, as an equivalence of abelian categories has to be. The
quotient category is preadditive and its quotient functor additive because `isoModSerre` admits a
left calculus of fractions, and a functor out of a localization is additive exactly when its
composite with the quotient functor is. -/
public theorem additive_irrelevantQuotientFunctor (hd : 0 < d) :
    (irrelevantQuotientFunctor.{u, w} 𝒮 hd).Additive := by
  have := isSerreClass_irrelevantModules 𝒮 hd
  refine (Localization.functor_additive_iff (toIrrelevantQuotient.{u, u, w} 𝒮 hd)
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒮 d)) _).2 ?_
  exact Functor.additive_of_iso (irrelevantQuotientFunctorFac 𝒮 hd).symm

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end

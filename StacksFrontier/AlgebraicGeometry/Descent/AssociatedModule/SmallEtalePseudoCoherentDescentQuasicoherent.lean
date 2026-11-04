module

public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePseudoCoherentDescent
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentOpenSlice

/-!
# Clause (2) ⇒ (1) of Stacks 08HE on an arbitrary scheme, for quasi-coherent cohomology

Let `X` be a scheme contained in a big étale site, let `ε : (X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)` be the
comparison of Stacks 08H7 and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are
quasi-coherent.  **If `ε^*E` is `m`-pseudo-coherent on the small étale site of `X`, then `E` is
`m`-pseudo-coherent on the small Zariski site of `X`.**

This is the globalization of
`AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale_of_isAffine`
over the affine opens, through the locality capstone
`AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_of_locally_toScheme_smallEtale_quasicoherent`.
It is the form in which Stacks 0DII consumes clause (2) ⇒ (1) of Stacks 08HE: there `E` lies in
`D_QCoh(𝒪_X)`, so its cohomology sheaves are quasi-coherent.

## Why the covering is the affine one

The locality capstone leaves the covering to the caller, and that is where the quasi-compactness
the boundedness step of clause (2) ⇒ (1) costs is paid.  An open subscheme of a quasi-compact
scheme need not be quasi-compact, so the covering cannot be arbitrary; the affine opens below an
open cover it, by `AlgebraicGeometry.Scheme.isBasis_affineOpens`, and on an affine member both
things the induction needs — the finite refinement behind boundedness and the *global* surjection
onto the top cohomology sheaf — are available.  No quasi-compactness hypothesis is carried on
`X` itself: it is produced member by member.

## What is and is not proved

`AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent_of_isQuasicoherent` has the
unproved obligation `AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentObligation.lean`
as its conclusion, with one hypothesis added: that the cohomology sheaves of `E` are
quasi-coherent.  **The obligation in its unrestricted form is still open**, and the reason is
recorded in the module documentation of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePseudoCoherentDescent`:
the affine-chart lift of the induction step exists because an obstruction group vanishes on an
affine, which is a statement about quasi-coherent modules, whereas the source lifts only locally
and shrinks the scheme at every stage of the induction — and a recursion that shrinks its ambient
site is what item 2 of the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/TopDegreeInduction.lean` describes
and is not built.

Three further hypotheses are carried, all of them derived-category models and all of them
required by the locality theorem rather than by anything proved here: a model of
`D(𝒪|_W)` on each slice of the small étale site of `X`, and a model of `D(𝒪_étale)` on the small
étale site of each open subscheme of `X`, both at the universe of the model on `X` itself.  They
are hypotheses and not instances because the obligation leaves that universe free; at the
universe `CategoryTheory.HasDerivedCategory.standard` produces they are both supplied by it.

## Main results

* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale`: clause
  (2) ⇒ (1) of Stacks 08HE on an arbitrary scheme for quasi-coherent cohomology.
* `AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent_of_isQuasicoherent`: the same,
  read as the obligation `AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent`.
* `AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule_of_isQuasicoherent`: **both
  implications of Stacks 08HE for an object with quasi-coherent cohomology**, the forward one
  being the unconditional
  `AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`.

## Implementation notes

No `@[stacks]` attribute is attached.  Clause (2) ⇒ (1) of Stacks 08HE is not proved in the
generality the tag states, and the three registrations of Stacks 0DII in this library — at
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/RelativeAbsolute.lean` and at
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean` — stay
where they are.

The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off for
this file.  It states the abelian structure of `SheafOfModules.{max u v r w} O` at a module
universe which is a `max` of the site universes; the small étale site has its objects in
`Type (u + 1)` while the modules here have sections in `Type u`, so instance search against it
leaves the stuck universe constraint `u =?= max (u + 1) ?w` and the `HasDerivedCategory` binders
fail to elaborate.  The abelian structure actually used is Mathlib's, at the pinned universes.

## References

* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

attribute [local instance 100000] AlgebraicGeometry.Scheme.standardZariskiHasDerivedCategory
  AlgebraicGeometry.Scheme.standardZariskiOverHasDerivedCategory

namespace AlgebraicGeometry.SmallEtale

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B X hX))]
  [∀ W : SmallEtale B X hX,
    HasDerivedCategory.{d'} (SheafOfModules.{u} ((structureSheaf B X hX).over W))]
  [∀ W : X.Opens, HasDerivedCategory.{d'}
    (SheafOfModules.{u} (structureSheaf B W.toScheme (BigEtaleOver.contains_opens B hX W)))]

/-- **Clause (2) ⇒ (1) of Stacks 08HE on an arbitrary scheme, for an object with quasi-coherent
cohomology.**  If `ε^*E` is `m`-pseudo-coherent on the small étale site of `X` and every
cohomology sheaf of `E` is quasi-coherent, then `E` is `m`-pseudo-coherent on `X`.

The covering handed to the locality capstone is the affine opens below each open of `X`, which is
where the quasi-compactness the induction costs is paid; over an affine member the conclusion is
`AlgebraicGeometry.SmallEtale`
`.isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale_of_isAffine`, both of whose hypotheses
the capstone makes available there. -/
public theorem isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)))
    (m : ℤ)
    (hE : IsPseudoCoherentFromSmallEtale B X hX E m)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))
        j).obj E).IsQuasicoherent) :
    X.zariskiRingedSite.IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_locally_toScheme_smallEtale_quasicoherent B X hX E m hE hQ ?_
  intro U
  refine ⟨fun {V} _ => IsAffineOpen V, ?_, ?_⟩
  · rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ :=
      Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (U := U) (x := x) hx
    exact ⟨V, homOfLE hVU, ⟨V, 𝟙 V, homOfLE hVU, hV, by simp⟩, hxV⟩
  · intro V f hV hPV hQV
    have : _root_.AlgebraicGeometry.IsAffine V.toScheme := hV
    exact isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale_of_isAffine
      B V.toScheme (BigEtaleOver.contains_opens B hX V) m _ hPV hQV

/-- **The obligation `AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent`, for an
object with quasi-coherent cohomology.**  The conclusion is the obligation written out in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentObligation.lean`;
the hypothesis `hQ` is what separates this from the unrestricted statement of the tag, and the
module documentation says why it cannot be dropped with the induction as it stands. -/
public theorem associatedModuleToPseudoCoherent_of_isQuasicoherent
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)))
    (m : ℤ)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))
        j).obj E).IsQuasicoherent) :
    AssociatedModuleToPseudoCoherent B X hX E m :=
  fun hE => isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale B X hX E m hE hQ

/-- **Stacks 08HE for an object with quasi-coherent cohomology**: `E` is `m`-pseudo-coherent on
the small Zariski site of `X` if and only if `ε^*E` is `m`-pseudo-coherent on the small étale
site.

The forward implication is the unconditional
`AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`, which carries the
`@[stacks 08HE]` attribute for clause (1) ⇒ (2); the converse is
`AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent_of_isQuasicoherent` above.  They
are assembled by `AlgebraicGeometry.SmallEtale.pseudoCoherentIff_of_imp`, which is the whole of
what assembling them takes. -/
public theorem pseudoCoherentIffAssociatedModule_of_isQuasicoherent
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)))
    (m : ℤ)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))
        j).obj E).IsQuasicoherent) :
    PseudoCoherentIffAssociatedModule B X hX E m :=
  pseudoCoherentIff_of_imp B X hX E m
    (fun h => pseudoCoherentToAssociatedModule_of_slice_exact B X hX E m h)
    (associatedModuleToPseudoCoherent_of_isQuasicoherent B X hX E m hQ)

end AlgebraicGeometry.SmallEtale

end

module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Towards Stacks 09NY: lifting an invertible module across a closed immersion

Stacks Tag 09NY (Varieties, Lemma 33.38.11) asserts the following. Let `i : Z ⟶ X` be a closed
immersion of schemes, let the underlying space of `X` be Noetherian of dimension at most one.
Then every invertible `𝒪_Z`-module is the pullback along `i` of an invertible `𝒪_X`-module, that
is, `Pic X ⟶ Pic Z` is surjective.

This file isolates the statement as a predicate on the morphism, and proves the cases of it that
hold with no hypothesis on `X` at all, together with the one structural reduction the eventual
proof will want: the predicate is stable under composition, so a closed immersion may be factored.
No `stacks` attribute is attached, and the module docstring says exactly why.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag09NY.LiftsInvertibleModules`: the conclusion of Tag 09NY for a
  fixed morphism of schemes `i : Z ⟶ X` — every invertible `𝒪_Z`-module is isomorphic to the
  pullback of an invertible `𝒪_X`-module. The dimension and Noetherian hypotheses of the tag are
  deliberately *not* part of it: they are hypotheses under which the predicate is to be proved,
  and separating them is what makes the results below stateable.

## Main results

* `Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback`: Tag 0B8L at the spelling this
  file uses, namely `RingedSpaceModuleAdjunction.modulePullback` and the invertibility class
  `AlgebraicGeometry.SheafOfModules.IsInvertible`.
* `Stacks.AlgebraicGeometry.Tag09NY.exists_modulePullback_iso_of_isTrivial`: the conclusion of
  Tag 09NY for a *trivial* `L`, with `M = 𝒪_X`, for an arbitrary morphism of schemes. Since every
  invertible module is locally trivial this is the local model of the tag.
* `Stacks.AlgebraicGeometry.Tag09NY.liftsInvertibleModules_of_isIso`: the conclusion of Tag 09NY
  for an isomorphism, with no hypothesis on `X`.
* `Stacks.AlgebraicGeometry.Tag09NY.LiftsInvertibleModules.comp`: the conclusion of Tag 09NY is
  stable under composition of morphisms. A closed immersion `Z ⟶ X` which factors as a chain of
  closed immersions can therefore be handled one step at a time, which is how the cohomological
  proof proceeds (it filters by the powers of the kernel ideal).

## What is missing

The source proof is cohomological and uses three inputs, none of which is available here. From
the short exact sequence of sheaves of *abelian groups* on `X`

    0 ⟶ (1 + ℐ) ∩ 𝒪_X^* ⟶ 𝒪_X^* ⟶ i_* 𝒪_Z^* ⟶ 0,

with `ℐ` the ideal sheaf of `Z`, one takes the long exact sequence in cohomology; the dimension
bound gives `H²(X, ℱ) = 0` for every abelian sheaf `ℱ` (Cohomology, Proposition 20.20.7, Tag
02UZ), hence `H¹(X, 𝒪_X^*) ⟶ H¹(X, i_* 𝒪_Z^*)` is onto; then `H¹(X, i_* 𝒪_Z^*) = H¹(Z, 𝒪_Z^*)`
(Cohomology, Lemma 20.20.1, Tag 02UV) and `Pic = H¹` of the sheaf of units (Cohomology, Lemma
20.6.1, Tag 09NU) finish it.

What is present, and what is not:

* the sheaf of units of a ringed space as a sheaf of abelian groups **is** present, as
  `Stacks.Cohomology.Generators.unitsSheaf`, with its group law;
* cohomology of abelian sheaves on a space **is** present, as
  `Stacks.Cohomology.AbelianSheaf.cohomologyOver` and
  `Stacks.CohomologyVanishing.abelianSheafCohomology`, bridged to Mathlib's site-level
  `CategoryTheory.Sheaf.H` by `Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections`;
* the **long exact sequence** for a short exact sequence of abelian sheaves is present, as the
  δ-functor `Stacks.Cohomology.NativeAbelian.cohomologyDeltaFunctor`;
* Tag 02UZ, the vanishing of `Hⁿ` above the dimension of a Noetherian space, is **absent**: no
  declaration in either tree relates the cohomology of an abelian sheaf to
  `topologicalKrullDim`, and the only unconditional higher vanishing is for profinite spaces
  (`Stacks.CohomologyVanishing.isZero_abelianSheafCohomology_of_isProfiniteStacks`). This is the
  genuine wall, and it is a theorem of Grothendieck, not a bridge;
* Tag 02UV, `Hᵖ(X, i_* ℱ) ≅ Hᵖ(Z, ℱ)` for a closed immersion, is **absent**, but all of its
  inputs are present — exactness of `i_*` on abelian sheaves
  (`Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward`, Tag 01AX), preservation of
  injectives (`Stacks.Cohomology.Leray.preservesInjectiveObjects_sheafPushforward`) and the
  comparison map itself (`Stacks.Cohomology.LerayLowDegree.abelianEdgeMap`). Only the assertion
  that the comparison is an isomorphism is unwritten;
* Tag 09NU, `Pic = H¹(𝒪^*)`, is **absent as a bijection**, but both halves of the correspondence
  it rests on are present: `Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne`
  (Tag 02FQ) identifies torsor classes with `H¹`, and
  `Stacks.Cohomology.Generators.generatorTorsor` /
  `Stacks.Cohomology.Generators.torsorAssociatedSheafOfModules` pass between rank-one locally
  free modules and `𝒪^*`-torsors. See the implementation notes for a correction to what those
  files say about their own hypotheses;
* the short exact sequence of unit sheaves itself is **absent**: nothing constructs the subsheaf
  `(1 + ℐ) ∩ 𝒪_X^*`.

So Tag 09NY is two theorems away, not one, and the harder of the two (02UZ) is independent of
everything in this file.

## Implementation notes

**No sheaf is transported.** Moving a module sheaf along a
morphism is the step this neighbourhood is dangerous at. It is not performed here by hand: the
three facts about `RingedSpaceModuleAdjunction.modulePullback` that these proofs need are already
available at exactly this spelling, so nothing is transported and no `eqToHom` occurs in this file.
They are `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso` (`f^* 𝒪_Y ≅ 𝒪_X`),
`Stacks.PullbackPseudofunctor.modulePullbackIdIso` and
`Stacks.PullbackPseudofunctor.modulePullbackCompIso`. The one discipline that is observed is the
one the spelling forces: `AlgebraicGeometry.SheafOfModules.IsInvertible` is stated over
`X.presheaf` together with a *proof* that the composite with `forget₂ CommRingCat RingCat` is a
sheaf, and instance search does not see through `AlgebraicGeometry.Scheme.ringCatSheaf` to find
it — `inferInstance` fails on the invertibility of `SheafOfModules.unit` while the
explicitly-applied `AlgebraicGeometry.SheafOfModules.isInvertible_unit` succeeds. So every
invertibility hypothesis below is an **ordinary explicit argument**, never an instance binder,
and every use of an invertibility result passes its arguments explicitly.

**A correction to Tag 09NU's own files, which bears directly on the route.**
The formalization of Tag 09NU's generators records in its header that deducing
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1` from invertibility "is exactly
clause 2 of Tag 0B8M, which nothing in this development concludes", and that the converse
"`isInvertible_of_isFiniteLocallyFreeOfRank_one` … is not in the development either". Both
clauses are false on this revision: clause 2 is
`Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme` and clause 1 is
`Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`, whose own docstring reads
"**Clause 1 of Stacks Tag 0B8M.** … No descent hypothesis is needed". So the Tag 09NU files'
hypothesis `IsFiniteLocallyFreeOfRank L 1` and Tag 09NU's own hypothesis `IsInvertible` are
already interchangeable for a scheme, and the stated reason for withholding a Tag 09NU attribute
there no longer applies. That is a composition, not a theorem, and it is not performed in this
file — it edits two files this directory does not own.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.Tag09NY

/-! ### The conclusion of Tag 09NY, as a predicate on the morphism -/

/-- **The conclusion of Stacks Tag 09NY for a fixed morphism of schemes `i : Z ⟶ X`**: every
invertible `𝒪_Z`-module is isomorphic to the pullback along `i` of an invertible `𝒪_X`-module.

This is the tag's statement with its hypotheses on `X` removed, so that the cases and reductions
below can be stated. Tag 09NY asserts `LiftsInvertibleModules i` whenever `i` is a closed
immersion, the space of `X` is Noetherian and `topologicalKrullDim X ≤ 1`.

The invertibility predicate is `AlgebraicGeometry.SheafOfModules.IsInvertible`, one of the two
classes in this repository carrying Tag 01CS, and the pullback is
`RingedSpaceModuleAdjunction.modulePullback`; both are the spellings the Tag 09NY statement uses.
Invertibility appears as an ordinary argument rather than an instance binder, for the reason
given in the module docstring. -/
def LiftsInvertibleModules {X Z : Scheme.{u}} (i : Z ⟶ X) : Prop :=
  ∀ L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace),
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L →
      ∃ M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
        _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M ∧
          Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L)

/-! ### Tag 0B8L at this spelling -/

/-- **Stacks Tag 0B8L at the spelling Tag 09NY is stated in.** The pullback of an invertible
`𝒪_X`-module along a morphism of schemes is invertible, for
`RingedSpaceModuleAdjunction.modulePullback` and the class
`AlgebraicGeometry.SheafOfModules.IsInvertible`.

This is `Stacks.InvertiblePullback.isInvertible_pullback'` with its instance argument supplied
explicitly; the explicitness is what makes it usable here, since instance search does not cross
`AlgebraicGeometry.Scheme.ringCatSheaf`. -/
theorem isInvertible_modulePullback {X Z : Scheme.{u}} (i : Z ⟶ X)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((modulePullback i.toLRSHom.toShHom).obj M) :=
  @Stacks.InvertiblePullback.isInvertible_pullback' _ _ i.toLRSHom.toShHom M hM

/-- The structure sheaf of a scheme, as a module over itself, is invertible, at the spelling Tag
09NY is stated in. This is `AlgebraicGeometry.SheafOfModules.isInvertible_unit` with both
arguments explicit. -/
theorem isInvertible_unit (X : Scheme.{u}) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :=
  _root_.AlgebraicGeometry.SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2

/-! ### Tag 09NY for a trivial module -/

/-- **The conclusion of Stacks Tag 09NY for a trivial `L`**, with `M = 𝒪_X`. This holds for an
arbitrary morphism of schemes: no closed immersion, no Noetherian hypothesis and no bound on the
dimension. Every invertible module is locally trivial, so this is the local model of the tag;
what Tag 09NY adds is the globalisation, which is where the cohomology enters. -/
theorem exists_modulePullback_iso_of_isTrivial {X Z : Scheme.{u}} (i : Z ⟶ X)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (e : L ≅ SheafOfModules.unit (structureSheafRing Z.toRingedSpace)) :
    ∃ M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
      _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M ∧
        Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  ⟨SheafOfModules.unit (structureSheafRing X.toRingedSpace), isInvertible_unit X,
    ⟨RingedSpaceModuleAdjunction.modulePullbackObjUnitIso i.toLRSHom.toShHom ≪≫ e.symm⟩⟩

/-! ### Tag 09NY for an isomorphism -/

/-- **The conclusion of Stacks Tag 09NY when `i` is an isomorphism**: every invertible
`𝒪_Z`-module is the pullback of one on `X`, namely of its own pullback along `i⁻¹`.

Invertibility of the witness is Tag 0B8L, and the isomorphism `i^* (i⁻¹)^* L ≅ L` is
pseudofunctoriality of the module pullback: `Stacks.PullbackPseudofunctor.modulePullbackCompIso`
turns the composite of the two pullbacks into the pullback along `i ≫ i⁻¹`, which is the identity
morphism of ringed spaces, and `Stacks.PullbackPseudofunctor.modulePullbackIdIso` finishes.
Neither a closed immersion nor any hypothesis on `X` is used. -/
theorem liftsInvertibleModules_of_isIso {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIso i] :
    LiftsInvertibleModules i := by
  intro L hL
  have hpush : i.toLRSHom.toShHom ≫ (inv i).toLRSHom.toShHom =
      ((i ≫ inv i) : Z ⟶ Z).toLRSHom.toShHom := rfl
  have hid : ((𝟙 Z : Z ⟶ Z).toLRSHom) = 𝟙 Z.toLocallyRingedSpace := rfl
  have hcomp : i.toLRSHom.toShHom ≫ (inv i).toLRSHom.toShHom = 𝟙 Z.toRingedSpace := by
    rw [hpush, IsIso.hom_inv_id, hid, LocallyRingedSpace.id_toShHom']
  refine ⟨(modulePullback (inv i).toLRSHom.toShHom).obj L, ?_, ⟨?_⟩⟩
  · exact isInvertible_modulePullback (inv i) L hL
  · have e₁ : (modulePullback (i.toLRSHom.toShHom ≫ (inv i).toLRSHom.toShHom)).obj L ≅ L := by
      rw [hcomp]
      exact (Stacks.PullbackPseudofunctor.modulePullbackIdIso Z.toRingedSpace).app L
    exact ((Stacks.PullbackPseudofunctor.modulePullbackCompIso
      (inv i).toLRSHom.toShHom i.toLRSHom.toShHom).app L).symm ≪≫ e₁

/-! ### The conclusion of Tag 09NY is stable under composition -/

/-- **The conclusion of Stacks Tag 09NY is stable under composition.** If every invertible module
on `Z` is the pullback of an invertible module on `X`, and every invertible module on `W` is the
pullback of an invertible module on `Z`, then every invertible module on `W` is the pullback of an
invertible module on `X`.

This is the reduction step that lets a closed immersion be factored: the cohomological proof of
Tag 09NY runs through the powers of the kernel ideal, i.e. through a chain of closed immersions,
and this is the statement that composing the chain's conclusions gives the tag's conclusion. The
isomorphism is pseudofunctoriality of the module pullback,
`Stacks.PullbackPseudofunctor.modulePullbackCompIso`, and the invertibility of the intermediate
witness is Tag 0B8L. -/
theorem LiftsInvertibleModules.comp {X Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Z)
    (hi : LiftsInvertibleModules i) (hj : LiftsInvertibleModules j) :
    LiftsInvertibleModules (j ≫ i) := by
  intro L hL
  obtain ⟨N, hN, ⟨eN⟩⟩ := hj L hL
  obtain ⟨M, hM, ⟨eM⟩⟩ := hi N hN
  refine ⟨M, hM, ⟨?_⟩⟩
  have hcomp : (j ≫ i).toLRSHom.toShHom =
      j.toLRSHom.toShHom ≫ i.toLRSHom.toShHom := rfl
  rw [hcomp]
  exact (Stacks.PullbackPseudofunctor.modulePullbackCompIso
      i.toLRSHom.toShHom j.toLRSHom.toShHom).app M ≪≫
    (modulePullback j.toLRSHom.toShHom).mapIso eM ≪≫ eN

end Stacks.AlgebraicGeometry.Tag09NY

end

module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexCohomology
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.HomologyRankBound
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A perfect complex on an integral scheme after a blowup

Let `X` be an integral scheme and let `E` be a perfect object of `D(𝒪_X)`. [Stacks, Tag 0ESR]
produces a nonempty open `U ⊆ X` on which every cohomology module `Hⁱ(E|_U)` is finite locally
free of a constant rank `rᵢ`, together with a `U`-admissible blowup `b : X' ⟶ X` after which
every `Hⁱ(Lb^*E)` is a perfect `𝒪_{X'}`-module of Tor dimension at most one.

This file supplies the first half, the generic local freeness of the cohomology: on a locally
Noetherian scheme the cohomology modules of a perfect complex are coherent, a coherent module on
an integral locally Noetherian scheme is finite free on a neighbourhood of the generic point, and
on a Noetherian scheme only finitely many degrees carry a nonzero cohomology module, so finitely
many such neighbourhoods have to be intersected. It also supplies the scheme-theoretic density of
a nonempty open, which is what lets [Stacks, Tag 0ESQ] be applied over such a `U`. The tag itself
is `AlgebraicGeometry.exists_nonempty_open_admissibleBlowup_forall_isHomologyPerfectTorLEOne` of
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/IntegralPerfectComplexBlowup.lean`.

## Main results

* `AlgebraicGeometry.isSchemeTheoreticallyDense_of_nonempty`: a nonempty open of an integral
  scheme is scheme-theoretically dense.
* `AlgebraicGeometry.exists_nonempty_open_isFiniteLocallyFreeOfRank_homology`: the first half of
  [Stacks, Tag 0ESR], the nonempty open of constant ranks.

## Implementation notes

**The two vocabularies of derived restriction, and a stale note about them.** The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/PerfectComplexCohomology.lean` say that "nothing
in the development identifies the two derived restriction functors on a scheme". That is out of
date: `AlgebraicGeometry.Scheme.Modules.derivedRestrictModulesIsoDerivedPullback` identifies
`AlgebraicGeometry.RingedSpace.derivedRestrictModules` with
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` along `U.ι`, and
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor` identifies it with
`CategoryTheory.Functor.mapDerivedCategory` of `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.
Composing the two with
`AlgebraicGeometry.Scheme.Modules.homologyFunctor_mapDerivedCategory_restrictFunctor_iso` — the
exactness of restriction — gives `AlgebraicGeometry.homologyDerivedPullbackIsoRestrict` (in
`StacksFrontier/AlgebraicGeometry/Perfect/HomologyRankBound.lean`), which is what lets the
`derivedPullback` spelling of the source's `Hⁱ(E|_U)`, the one [Stacks, Tag 0ESQ] is stated at,
be computed from the cohomology modules of `E` themselves.

**The Noetherian hypothesis.** The nonempty open of constant ranks is produced below under more
of `X` than the source asks of it.

* `[IsNoetherian X]`, that is locally Noetherian and quasi-compact. Local Noetherianness is what
  `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology` ([Stacks, Tag 0FEP]) needs to
  make the cohomology modules coherent, and coherence is the hypothesis of
  `exists_isIso_restrictFunctor_free_near_genericPoint` of
  `Stacks.AlgebraicGeometry.IrreducibleDevissage`, the generic freeness that produces the open in
  one degree; finite type alone is not enough for it. Quasi-compactness is what
  `Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect` needs to bound the
  degrees carrying nonzero cohomology globally. The local form,
  `Stacks.AlgebraicGeometry.PerfectCohomology.locally_finite_homology`, holds on any scheme and
  would suffice if a vanishing of a cohomology module on an open could be read off from its
  support missing that open; the development has that implication only in the other direction.

## References

* [Stacks Project, Tag 0ESR](https://stacks.math.columbia.edu/tag/0ESR)
* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 056D](https://stacks.math.columbia.edu/tag/056D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect TopologicalSpace
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.FittingComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Finite local freeness of a restriction -/

/-- Finite local freeness of rank `r` of a restriction passes to smaller opens. This is the rank
clause of `AlgebraicGeometry.Scheme.Modules.IsSingleDegreeRank.mono`, stated for a module rather
than for the cohomology of a derived module in a fixed degree. -/
theorem isFiniteLocallyFreeOfRank_restrict_of_le {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V)
    (F : X.Modules) {r : ℕ}
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor V.ι).obj F) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor W.ι).obj F) r := by
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ r).1
    (Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_isIso
      (Scheme.Opens.isoOfLE h).hom ?_)
  exact (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ r).2 hF).restrict
    (V.ι ⁻¹ᵁ W).ι).of_iso (Scheme.Modules.restrictPreimageIso h F)

/-! ### A nonempty open of an integral scheme -/

/-- The generic point of an integral scheme lies in every nonempty open: it specializes to every
point. -/
theorem genericPoint_mem_of_setNonempty {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U := by
  obtain ⟨x, hx⟩ := hU
  exact (genericPoint_specializes x).mem_open U.2 hx

/-- A nonempty open of an integral scheme is topologically dense: its closure contains the
closure of the generic point, which is everything. -/
theorem dense_of_nonempty_of_isIntegral {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : Dense (U : Set X) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  have hmono : closure ({genericPoint X} : Set X) ⊆ closure (U : Set X) :=
    closure_mono (Set.singleton_subset_iff.mpr (genericPoint_mem_of_setNonempty hU))
  exact hmono (by rw [genericPoint_closure]; trivial)

/-- **A nonempty open of an integral scheme is scheme-theoretically dense.** An integral scheme is
reduced, and for an open of a reduced scheme topological density and scheme-theoretic density
agree by [Stacks, Tag 056D]. -/
@[ega "IV 11.10.4" "converse, special case", ega "IV 20.2.16" "special case"]
theorem isSchemeTheoreticallyDense_of_nonempty {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : Scheme.Opens.IsSchemeTheoreticallyDense U :=
  ((AlgebraicGeometry.dense_open_tfae U).out 1 3).mp
    (dense_of_nonempty_of_isIntegral hU)

/-- **A coherent module on an integral locally Noetherian scheme is finite free near the generic
point**, [Stacks, Tag 0B8J] at the generic point. This names
`exists_isIso_restrictFunctor_free_near_genericPoint` of
`Stacks.AlgebraicGeometry.IrreducibleDevissage` at the canonical generic point of an integral
scheme. -/
theorem exists_restrict_iso_free_genericPoint {Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] (G : Z.Modules) [G.IsCoherent] :
    ∃ (q : ℕ) (V : Z.Opens), genericPoint Z ∈ V ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin q))) ≅
        (Scheme.Modules.restrictFunctor V.ι).obj G) :=
  Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isIso_restrictFunctor_free_near_genericPoint
    G (genericPoint Z) (genericPoint_spec Z)

/-! ### Shrinking finitely many neighbourhoods of a point -/

/-- Finitely many opens through a point, each carrying a property that survives shrinking, are
refined by a single open through that point. -/
theorem exists_mem_forall_of_finset {X : Scheme.{u}} (x : X) (s : Finset ℤ)
    (P : X.Opens → ℤ → Prop)
    (hmono : ∀ (V W : X.Opens), W ≤ V → ∀ n : ℤ, P V n → P W n)
    (hex : ∀ n ∈ s, ∃ V : X.Opens, x ∈ V ∧ P V n) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ n ∈ s, P V n := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨⊤, trivial, by simp⟩
  | insert n s hn ih =>
    obtain ⟨V, hxV, hV⟩ := ih fun m hm => hex m (Finset.mem_insert_of_mem hm)
    obtain ⟨W, hxW, hW⟩ := hex n (Finset.mem_insert_self n s)
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, fun m hm => ?_⟩
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hmono W (V ⊓ W) inf_le_right m hW
    · exact hmono V (V ⊓ W) inf_le_left m (hV m hm)

/-! ### The first half of Stacks 0ESR -/

/-- **The nonempty open of constant ranks, the first half of [Stacks, Tag 0ESR].** On an integral
Noetherian scheme a perfect object of `D(𝒪_X)` has a nonempty open `U` on which every cohomology
module of `E|_U` is finite locally free of a constant rank `rᵢ`, with the ranks vanishing above
an explicit degree.

Only finitely many degrees carry a nonzero cohomology module
(`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect`); in each of those
the cohomology module is coherent ([Stacks, Tag 0FEP]) and therefore finite free on a
neighbourhood of the generic point ([Stacks, Tag 0B8J] at the generic point, where the local ring
is the function field); the neighbourhoods are intersected by
`AlgebraicGeometry.exists_mem_forall_of_finset`, and outside the finite set the cohomology module
vanishes, hence restricts to a module of rank `0`. -/
theorem exists_nonempty_open_isFiniteLocallyFreeOfRank_homology (X : Scheme.{u}) [IsIntegral X]
    [IsNoetherian X] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : IsPerfect.{u, u, u + 1} E) :
    ∃ (U : X.Opens) (r : ℤ → ℕ) (m : ℤ), (U : Set X).Nonempty ∧ (∀ i : ℤ, m < i → r i = 0) ∧
      ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).obj
          ((derivedPullback U.ι.toLRSHom.toShHom).obj E)) (r i) := by
  classical
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X E hE
  set s : Finset ℤ := Finset.Icc a b with hs
  -- In each degree the cohomology module is coherent, hence free near the generic point.
  have hgen : ∀ n ∈ s, ∃ V : X.Opens, genericPoint X ∈ V ∧
      ∃ q : ℕ, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.restrictFunctor V.ι).obj
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E)) q := by
    intro n _
    have hcoh := Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology X E hE n
    obtain ⟨q, V, hV, ⟨e⟩⟩ :=
      @exists_restrict_iso_free_genericPoint.{u} X _ _
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E) hcoh
    have hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin q))) q :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ q).2
        (SheafOfModules.isFiniteLocallyFreeOfRank_free.{u, u, u} (R := X.ringCatSheaf) q)
    refine ⟨V, hV, q, Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso e ?_⟩
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ q).1 (hfree.restrict V.ι)
  choose! VV hVV qq hqq using hgen
  -- Intersect the finitely many neighbourhoods.
  obtain ⟨U, hU, hUall⟩ := exists_mem_forall_of_finset (genericPoint X) s
    (fun V n => SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E)) (qq n))
    (fun V W hWV n hn => isFiniteLocallyFreeOfRank_restrict_of_le hWV _ hn)
    fun n hn => ⟨VV n, hVV n hn, hqq n hn⟩
  refine ⟨U, fun i => if i ∈ s then qq i else 0, b, ⟨genericPoint X, hU⟩, ?_, fun i => ?_⟩
  · intro i hi
    have : i ∉ s := fun hmem => absurd (Finset.mem_Icc.mp hmem).2 (by omega)
    simp [this]
  · refine Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso
      (homologyDerivedPullbackIsoRestrict X U i E).symm ?_
    by_cases hi : i ∈ s
    · simpa [hi] using hUall i hi
    · have hzero : IsZero
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E) := by
        rcases lt_or_ge i a with h | h
        · exact ha i h
        · exact hb i (by
            by_contra hcon
            exact hi (Finset.mem_Icc.mpr ⟨h, by omega⟩))
      simpa [hi] using isFiniteLocallyFreeOfRank_zero_of_isZero
        (Functor.map_isZero (Scheme.Modules.restrictFunctor U.ι) hzero)

end AlgebraicGeometry

end

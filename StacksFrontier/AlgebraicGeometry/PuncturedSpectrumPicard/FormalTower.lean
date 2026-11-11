module

public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriple
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# Lifting invertible modules along a tower of first-order thickenings

Let `(A, 𝔪)` be a Noetherian local ring, `f ∈ 𝔪`, and let `U`, resp. `U₀`, be the punctured
spectrum of `A`, resp. of `A/fA`. [Stacks, Tag 0F2D] asserts that
`colim_{U₀ ⊆ U' ⊆ U open} Pic(U') ⟶ Pic(U₀)` is surjective when `A` is `f`-adically complete,
`f` is a nonzerodivisor, `H¹_𝔪(A/fA)` and `H²_𝔪(A/fA)` are finite and `H³_𝔪(A/fA) = 0`.

The source's proof has two halves.  It writes `U_n` for the `n`th infinitesimal neighbourhood of
`U₀` in `U`, observes that the ideal sheaf of `U_n` in `U_{n+1}` is `𝒪_{U₀}` because `U₀ ⊆ U` is
cut out by the nonzerodivisor `f`, and reads off from [Stacks, Tag 0C6R] the exact sequence
`Pic(U_{n+1}) → Pic(U_n) → H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`.  **That is the first half**: every
invertible module on `U₀` is the restriction of an invertible object of `Coh(U, f𝒪_U)`, i.e. of a
compatible system of invertible classes along the whole tower.  The second half is
[Stacks, Tag 0EKZ], which descends such a formal invertible object to an invertible module on an
actual open `U'` with `U₀ ⊆ U' ⊆ U`.

**This file proves the first half, in the generality the argument has**, and states the target of
the tag so that the remaining input is visible.

## Main definitions

* `Stacks.PuncturedSpectrumPicard.Pic`: the Picard group of a scheme, in the spelling
  [Stacks, Tag 0C6R] is stated at in this library, namely
  `Stacks.SheafOfModules.Picard.PicardGroup` of the structure sheaf.
* `Stacks.PuncturedSpectrumPicard.ThickeningTower`: a tower
  `X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` of first-order thickenings of schemes.  The source's `U₀ ⊆ U₁ ⊆ U₂ ⊆ ⋯`
  is an instance of this once the ideal sheaf identification is available.
* `Stacks.PuncturedSpectrumPicard.IsCompatible`: a family of Picard classes, one on each stage of
  such a tower, each restricting to the previous one.  This is the Picard-group shadow of an
  invertible object of `Coh(U, f𝒪_U)`.
* `Stacks.PuncturedSpectrumPicard.PicardColimitSurjective`: **the conclusion of
  [Stacks, Tag 0F2D]**, written out for `(A, f)`.  The colimit is filtered and over the opens
  `U'` of `U` through which `U₀ ⟶ U` factors, so surjectivity of the map out of it is exactly the
  elementwise statement given here.  Nothing in this file proves it; it is stated so that the one
  missing input is legible.

## Main results

* `Stacks.PuncturedSpectrumPicard.surjective_picardRestriction_of_forall_eq_zero`: if the second
  cohomology of the ideal sheaf of a first-order thickening `i : X ⟶ X'` vanishes, then
  `Pic(X') → Pic(X)` is surjective.  This is [Stacks, Tag 0C6R] — exactness at `Pic(X)`, which
  this library already proves — together with the vanishing.
* `Stacks.PuncturedSpectrumPicard.exists_isCompatible`: **the first half of the proof of
  [Stacks, Tag 0F2D]**.  If every stage of a tower of first-order thickenings has vanishing
  second ideal-sheaf cohomology, then every Picard class on the bottom stage extends to a
  compatible family along the whole tower.

## Implementation notes

**Where the source's hypotheses go.**  Of the four hypotheses of [Stacks, Tag 0F2D], only (4) is
consumed here, and only through the consequence the source's proof draws from it: the vanishing
of `H²` of the ideal sheaf at each stage of the tower, which the source obtains from
`H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`.  Hypotheses (1), (2) and (3) are inputs of
[Stacks, Tag 0EKZ] and of the construction of the tower, neither of which is carried out here, so
they do not appear.  This is why the statement proved below is about an abstract tower and not
about `(A, f)`: it is the part of the argument that is independent of them.

**Two spellings of the Picard group.**  `Stacks.PuncturedSpectrumPicard.Pic` is the spelling the
[Stacks, Tag 0C6R] sequence uses, and `Stacks.Picard.ofScheme` is the spelling the
neighbouring tags of the same section — [Stacks, Tag 0F2G], [Stacks, Tag 0FIX] — are stated at.
The two are the same group, but this library has no identification of
`Stacks.Thickenings.picardRestriction` with `Stacks.Picard.schemePullbackClass`, so
`PicardColimitSurjective` below is stated at the second spelling, matching its neighbours, and is
deliberately not connected to `exists_isCompatible`.  Supplying that identification, the tower
and [Stacks, Tag 0EKZ] are the three inputs the tag still needs.

**The abelian group structure** on `Pic X` is
`Stacks.Cohomology.Generators.picardGroupAddCommGroup`,
stated at the underlying ringed space and re-activated here as a local instance; instance search
reaches `X.sheaf` through that instance's `RingedSpace` argument without any further restatement.

**The compatible family is built by recursion on `ℕ`** over the motive `fun n => Pic (T.obj n)`,
choosing at each step a preimage supplied by
`surjective_picardRestriction_of_forall_eq_zero`.  The choice is genuine: the surjection has no
natural section, and nothing in the statement pins down which lift is taken.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.PuncturedSpectrumPicard

attribute [local implicit_reducible] TopCat.Sheaf

/-- `Ext`-groups of abelian sheaves on a topological space are computed in the universe of the
sections, because the category of abelian sheaves has enough injectives.  This is the local
instance of `StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence`, repeated because it is
local there and `CategoryTheory.Sheaf.H` cannot be written without it. -/
local instance hasExtAbelianSheaf (Y : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
  hasExt_of_enoughInjectives _

/-! The abelian group structure on the Picard group of a scheme is
`Stacks.Cohomology.Generators.picardGroupAddCommGroup`, applied at the underlying ringed space:
instance search finds the goal at `X.sheaf` through that instance's `RingedSpace` argument
without any further restatement. -/

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- The Picard group of a scheme, in the spelling the [Stacks, Tag 0C6R] exact sequence of
`StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence` is stated at. -/
abbrev Pic (X : Scheme.{u}) : Type _ :=
  Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property

/-! ### Surjectivity on Picard groups of a single first-order thickening -/

/-- If the second cohomology of the ideal sheaf of a first-order thickening `i : X ⟶ X'`
vanishes, then restriction of Picard classes `Pic(X') → Pic(X)` is surjective.

This is the one step the proof of [Stacks, Tag 0F2D] takes from [Stacks, Tag 0C6R]: exactness of
`Pic(X') → Pic(X) → H²(X, ℐ)` at `Pic(X)`, which is
`Stacks.Thickenings.exact_picardRestriction`, says that a class on `X` lifts exactly when its
image in `H²(X, ℐ)` vanishes, and under the hypothesis that image always vanishes. -/
theorem surjective_picardRestriction_of_forall_eq_zero {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    (h2 : ∀ x : CategoryTheory.Sheaf.H.{u} (Stacks.Thickenings.idealAddSheafOnSub i) 2, x = 0) :
    Function.Surjective (Stacks.Thickenings.picardRestriction i hi) := by
  intro c
  have hmem : c ∈ Set.range (Stacks.Thickenings.picardRestriction i hi) :=
    (Stacks.Thickenings.exact_picardRestriction i hi c).mp (h2 _)
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

/-! ### Towers of first-order thickenings -/

/-- A tower `X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` of first-order thickenings of schemes.  In the proof of
[Stacks, Tag 0F2D] this is the system of infinitesimal neighbourhoods `U₀ ⊆ U₁ ⊆ U₂ ⊆ ⋯` of the
punctured closed fibre inside the punctured spectrum. -/
structure ThickeningTower where
  /-- The `n`th stage of the tower. -/
  obj : ℕ → Scheme.{u}
  /-- The closed immersion of the `n`th stage into the next one. -/
  hom : ∀ n, obj n ⟶ obj (n + 1)
  /-- Each stage is a first-order thickening of the previous one. -/
  isFirstOrderThickening : ∀ n, Stacks.Thickenings.IsFirstOrderThickening (hom n)

variable (T : ThickeningTower.{u})

/-- A family of Picard classes, one on each stage of a tower of first-order thickenings, each
restricting to the previous one.  This is the Picard-group shadow of an invertible object of the
category `Coh(U, f𝒪_U)` of the source. -/
def IsCompatible (c : (n : ℕ) → Pic (T.obj n)) : Prop :=
  ∀ n, Stacks.Thickenings.picardRestriction (T.hom n) (T.isFirstOrderThickening n) (c (n + 1))
    = c n

/-- **The first half of the proof of [Stacks, Tag 0F2D].**  Let `X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` be a tower of
first-order thickenings in which the ideal sheaf of every stage has vanishing second cohomology.
Then every Picard class on the bottom stage extends to a compatible family of Picard classes
along the whole tower.

This is the step the source writes as "this gives an exact sequence
`Pic(U_{n+1}) → Pic(U_n) → H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`.  Therefore each invertible
`𝒪_{U₀}`-module is restricted from an invertible object of `Coh(U, f𝒪_U)`."  Each single lift is
`surjective_picardRestriction_of_forall_eq_zero`, and the family is assembled by recursion on the
stage, choosing a lift at each step.

What remains of the tag after this is [Stacks, Tag 0EKZ], which descends the formal object so
obtained to an invertible module on an open `U'` with `U₀ ⊆ U' ⊆ U`; see
`Stacks.PuncturedSpectrumPicard.PicardColimitSurjective` for the conclusion that needs it. -/
@[stacks 0F2D "the first half of the source's proof, in the generality the argument has: for a \
tower of first-order thickenings whose ideal sheaves have vanishing H², every Picard class on \
the bottom stage extends to a compatible family along the whole tower. That is the source's \
step `Pic(U_{n+1}) → Pic(U_n) → H²(U₀,𝒪_{U₀}) = H³_𝔪(A/fA) = 0, therefore each invertible \
𝒪_{U₀}-module is restricted from an invertible object of Coh(U,f𝒪_U)`, and the single-stage \
lift is Stacks 0C6R, Stacks.Thickenings.exact_picardRestriction in \
StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence. The vanishing of H² is a condition on \
the tower, not every tower satisfying it; for the same half at the punctured spectrum, with \
that vanishing derived from the source's own hypotheses (2) f a nonzerodivisor and (4) \
H³_𝔪(A/fA) = 0, see \
Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback_puncturedSpectrum. NOT covered by \
this declaration: the tag's own conclusion, surjectivity of colim_{U₀ ⊆ U' ⊆ U} Pic(U') → \
Pic(U₀), written as Stacks.PuncturedSpectrumPicard.PicardColimitSurjective, which needs \
Stacks 0EKZ and through it Stacks 0EIR part (2)"]
theorem exists_isCompatible
    (h2 : ∀ n, ∀ x : CategoryTheory.Sheaf.H.{u}
      (Stacks.Thickenings.idealAddSheafOnSub (T.hom n)) 2, x = 0)
    (c₀ : Pic (T.obj 0)) :
    ∃ c : (n : ℕ) → Pic (T.obj n), c 0 = c₀ ∧ IsCompatible T c := by
  have hsurj : ∀ n, Function.Surjective
      (Stacks.Thickenings.picardRestriction (T.hom n) (T.isFirstOrderThickening n)) := fun n =>
    surjective_picardRestriction_of_forall_eq_zero (T.hom n) (T.isFirstOrderThickening n) (h2 n)
  refine ⟨fun n => Nat.rec (motive := fun n => Pic (T.obj n)) c₀
    (fun n x => (hsurj n x).choose) n, rfl, fun n => ?_⟩
  exact (hsurj n _).choose_spec

/-! ### The conclusion of the tag -/

/-- **The conclusion of [Stacks, Tag 0F2D]**, written out for a local ring `A` and `f ∈ A`:
the map `colim_{U₀ ⊆ U' ⊆ U open} Pic(U') ⟶ Pic(U₀)` is surjective, where `U` is the punctured
spectrum of `A` and `U₀` is the part of `Spec(A/fA)` lying over it.

The index category is the poset of opens `U'` of `U` through which the closed immersion
`U₀ ⟶ U` factors — equivalently those containing the image of `U₀` — which is filtered, being
closed under intersection and nonempty.  Surjectivity of the map out of a filtered colimit of
abelian groups is therefore the elementwise statement written here: every class on `U₀` is the
pullback of a class on some such `U'`.  The factorisation `j` is required to be compatible with
the inclusion `U' ⟶ U`, which is what makes `U'` an open *of `U` containing `U₀`* rather than an
arbitrary scheme over `U`.

`U`, `U₀` and the arrow `U₀ ⟶ U` are the spellings the neighbouring tags of the same section use:
`Stacks.Divisors.puncturedSpectrum`, `Stacks.Algebraization.puncturedClosedFibre`, and
`AlgebraicGeometry.morphismRestrict` of `Stacks.Algebraization.closedImmersion`.  The Picard
group is `Stacks.Picard.ofScheme` and the pullback is `Stacks.Picard.schemePullbackClass`, as in
[Stacks, Tag 0F2G] and [Stacks, Tag 0FIX].

It is proved, under the hypotheses of [Stacks, Tag 0F2D], as
`Stacks.PuncturedSpectrumPicard.picardColimitSurjective` (in `FormalPicardAlgebraization`); this
file supplies the formal tower it is built from, see
`Stacks.PuncturedSpectrumPicard.exists_isCompatible`. -/
def PicardColimitSurjective (A : Type u) [CommRing A] [IsLocalRing A] (f : A) : Prop :=
  ∀ c : Stacks.Picard.ofScheme (Stacks.Algebraization.puncturedClosedFibre A f).toScheme,
    ∃ (V : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens)
      (j : (Stacks.Algebraization.puncturedClosedFibre A f).toScheme ⟶ V.toScheme),
      j ≫ V.ι = morphismRestrict (Stacks.Algebraization.closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A) ∧
        ∃ cV : Stacks.Picard.ofScheme V.toScheme, Stacks.Picard.schemePullbackClass j cV = c

end Stacks.PuncturedSpectrumPicard

end

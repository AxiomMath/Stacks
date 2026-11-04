module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFreeDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Locally strictly perfect complexes on a ringed space

Let `(X, O_X)` be a ringed space. Stacks 0FP9 states its hypothesis on a complex `F^•` of
`O_X`-modules in two ways: that `F^•` is *locally bounded* and each term `F^n` is *locally a
direct summand of a finite free `O_X`-module*, or equivalently that there is an open covering
`X = ⋃ U_i` on which each restriction `F^•|_{U_i}` is a strictly perfect complex. This file
defines the second form and proves it equivalent to the first, and deduces that each term of
such a complex has the dual sheaf `Hom(F^n, O_X)` as a left dual.

The two forms differ in the order of the quantifiers: the first allows the neighbourhood
witnessing the summand condition to depend on the degree, while the second demands a single
neighbourhood serving all degrees at once. They agree because local boundedness confines the
degrees on which anything is asked to a finite set, and a finite intersection of
neighbourhoods of a point is again one.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.IsFiniteFreeSummandOn`: a module whose restriction to an open
  is a retract of `O_U^{⊕n}`.
* `Stacks.SheafOfModules.OnSpace.IsBoundedOn`: a complex whose restriction to an open has only
  finitely many nonzero terms.
* `Stacks.SheafOfModules.OnSpace.IsStrictlyPerfectOn`: a complex whose restriction to an open
  is strictly perfect, that is, bounded with each term a direct summand of a finite free module.
* `Stacks.SheafOfModules.OnSpace.IsLocallyStrictlyPerfect` and
  `Stacks.SheafOfModules.OnSpace.IsLocallyBounded`: the pointwise local versions.

## Main results

* `Stacks.SheafOfModules.OnSpace.isLocallyStrictlyPerfect_iff`: a complex is locally strictly
  perfect precisely when it is locally bounded and each of its terms is locally a direct
  summand of a finite free module. This is the equivalence of the two phrasings of the
  hypothesis of Stacks 0FP9.
* `Stacks.SheafOfModules.OnSpace.termExactPairing`: the dual sheaf of each term of a locally
  strictly perfect complex is a left dual of that term, by Stacks 0FNV.

## Implementation notes

Boundedness on `U` is the vanishing of `F^i|_U` outside a finite set of degrees rather than
the vanishing of `F^i` itself, since a complex may well be locally bounded without any term
vanishing globally; this is the reason Stacks 0FP9 says *locally* bounded where the affine
statement Stacks 0FNK says bounded.

Both conditions are stated for the restriction of a module to the slice site over an open,
which is `SheafOfModules.over`, matching `IsLocallyFiniteFreeSummand`. Transporting either
condition from an open to a smaller one therefore means restricting along `SheafOfModules.overMap`
and identifying the result using `SheafOfModules.overFunctorMap`, together with
`Stacks.SheafOfModules.freeOverMapIso` for the free module.

A module whose restriction to `U` vanishes is a retract of the free module of rank zero for a
degenerate reason: the identity of a zero object is its own zero endomorphism, so the retract
identity holds for the pair of zero morphisms. This is what lets the equivalence below ask for
the summand condition in every degree, including those where the complex vanishes.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace MonoidalCategory

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] monoidal

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- A sheaf of `O_X`-modules is a **direct summand of a finite free module on `U`** if its
restriction to the open `U` is a retract of `O_U^{⊕n}` for some natural number `n`.

This is the condition `IsLocallyFiniteFreeSummand` asks for on some neighbourhood of each
point. -/
def IsFiniteFreeSummandOn (F : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) : Prop :=
  ∃ n : ℕ, Nonempty (Retract (F.over U)
    (SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n))))

/-- A complex of `O_X`-modules is **bounded on `U`** if its restriction to the open `U` has
only finitely many nonzero terms. -/
def IsBoundedOn (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (U : Opens X.carrier) : Prop :=
  ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s → IsZero ((F.X i).over U)

/-- A complex of `O_X`-modules is **strictly perfect on `U`** if its restriction to the open
`U` is a strictly perfect complex: bounded, with every term a direct summand of a finite free
`O_U`-module. This is the condition Stacks 0FP9 imposes on the members of its covering. -/
structure IsStrictlyPerfectOn (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (U : Opens X.carrier) : Prop where
  /-- Only finitely many terms of the restriction to `U` are nonzero. -/
  boundedOn : IsBoundedOn X F U
  /-- Every term of the restriction to `U` is a direct summand of a finite free module. -/
  summandOn : ∀ i : ℤ, IsFiniteFreeSummandOn X (F.X i) U

/-- A complex of `O_X`-modules is **locally bounded** if every point of `X` has an open
neighbourhood on which the complex is bounded. -/
def IsLocallyBounded (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ IsBoundedOn X F U

/-- A complex of `O_X`-modules is **locally strictly perfect** if every point of `X` has an
open neighbourhood on which the complex is strictly perfect. Equivalently, there is an open
covering `X = ⋃ U_i` with each `F^•|_{U_i}` strictly perfect, which is the hypothesis of
Stacks 0FP9. -/
def IsLocallyStrictlyPerfect
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ IsStrictlyPerfectOn X F U

/-- Being locally a direct summand of a finite free module is being a direct summand of a
finite free module on some neighbourhood of each point. -/
theorem isLocallyFiniteFreeSummand_iff (F : SheafOfModules.{u} (structureSheafRing X)) :
    IsLocallyFiniteFreeSummand X F ↔
      ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ IsFiniteFreeSummandOn X F U :=
  Iff.rfl

/-- Vanishing of the restriction of a module passes to smaller opens. -/
theorem isZero_over_of_le {F : SheafOfModules.{u} (structureSheafRing X)}
    {U V : Opens X.carrier} (h : U ≤ V) (hF : IsZero (F.over V)) :
    IsZero (F.over U) := by
  have : (SheafOfModules.overMap (structureSheafRing X) (homOfLE h)).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  exact (Functor.map_isZero (SheafOfModules.overMap (structureSheafRing X) (homOfLE h)) hF).of_iso
    ((SheafOfModules.overFunctorMap (structureSheafRing X) (homOfLE h)).app F).symm

/-- A module that vanishes has vanishing restriction to every open: restriction is a functor
preserving zero morphisms, so it carries `𝟙 = 0` to `𝟙 = 0`. -/
theorem isZero_over_of_isZero {F : SheafOfModules.{u} (structureSheafRing X)}
    (hF : IsZero F) (U : Opens X.carrier) :
    IsZero (F.over U) := by
  rw [IsZero.iff_id_eq_zero, show (𝟙 (F.over U))
      = (_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map (𝟙 F) by simp,
    hF.eq_of_src (𝟙 F) 0, Functor.map_zero]

/-- **A globally bounded complex is locally bounded.**  Take the neighbourhood to be `X` itself
and the same finite set of degrees; the terms outside it vanish, hence so do their restrictions.

Nothing in the tree stated this, although the implication is what makes the covering phrasing of
[Stacks, Tag 0FP9] and its termwise phrasing interchangeable once a global `Finset` bound is
assumed — see `isLocallyStrictlyPerfect_iff_of_bound`. -/
theorem isLocallyBounded_of_bound
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {s : Finset ℤ}
    (hbd : ∀ i : ℤ, i ∉ s → IsZero (F.X i)) :
    IsLocallyBounded X F :=
  fun _ => ⟨⊤, trivial, s, fun i hi => isZero_over_of_isZero X (hbd i hi) ⊤⟩

/-- Being a direct summand of a finite free module on an open passes to smaller opens, with the
same rank: restriction along the inclusion carries the retract to a retract, and identifies
the free module of rank `n` on the larger open with the free module of rank `n` on the
smaller. -/
theorem isFiniteFreeSummandOn_of_le {F : SheafOfModules.{u} (structureSheafRing X)}
    {U V : Opens X.carrier} (h : U ≤ V) (hF : IsFiniteFreeSummandOn X F V) :
    IsFiniteFreeSummandOn X F U := by
  obtain ⟨n, ⟨ρ⟩⟩ := hF
  refine ⟨n, ⟨(Retract.ofIso
    ((SheafOfModules.overFunctorMap (structureSheafRing X) (homOfLE h)).app F).symm).trans
      ((ρ.map (SheafOfModules.overMap (structureSheafRing X) (homOfLE h))).trans
        (Retract.ofIso (Stacks.SheafOfModules.freeOverMapIso
          (R := structureSheafRing X) (homOfLE h) (ULift.{u} (Fin n))).symm))⟩⟩

/-- A module whose restriction to `U` vanishes is a direct summand of a finite free module on
`U`, of rank zero: the two zero morphisms compose to the identity of a zero object. -/
theorem isFiniteFreeSummandOn_of_isZero {F : SheafOfModules.{u} (structureSheafRing X)}
    {U : Opens X.carrier} (hF : IsZero (F.over U)) :
    IsFiniteFreeSummandOn X F U :=
  ⟨0, ⟨{ i := 0, r := 0, retract := hF.eq_of_src _ _ }⟩⟩

/-- Finitely many of a family of neighbourhoods of a point admit a common open refinement
which is again a neighbourhood of that point. -/
theorem exists_mem_le_of_finset (s : Finset ℤ) (U : ℤ → Opens X.carrier) (x : X.carrier)
    (h : ∀ i : ℤ, x ∈ U i) :
    ∃ V : Opens X.carrier, x ∈ V ∧ ∀ i ∈ s, V ≤ U i := by
  refine Finset.induction_on s ⟨⊤, by simp, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨V, hxV, hV⟩ := ih
  refine ⟨U a ⊓ V, ⟨h a, hxV⟩, fun i hi => ?_⟩
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact inf_le_left
  · exact le_trans inf_le_right (hV i hi)

/-- **The two phrasings of the hypothesis of Stacks 0FP9 agree.** A complex of `O_X`-modules
admits an open covering on which it is strictly perfect precisely when it is locally bounded
and each of its terms is locally a direct summand of a finite free `O_X`-module.

The substance is the implication from right to left, where the neighbourhood witnessing the
summand condition is allowed to vary with the degree: local boundedness supplies a
neighbourhood outside a finite set of degrees on which the complex already vanishes, and
intersecting it with the finitely many remaining neighbourhoods gives one neighbourhood on
which every degree is accounted for at once. -/
theorem isLocallyStrictlyPerfect_iff
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    IsLocallyStrictlyPerfect X F ↔
      IsLocallyBounded X F ∧ ∀ i : ℤ, IsLocallyFiniteFreeSummand X (F.X i) := by
  classical
  refine ⟨fun hF => ⟨fun x => (hF x).imp fun _ h => ⟨h.1, h.2.boundedOn⟩,
      fun i x => (hF x).imp fun _ h => ⟨h.1, h.2.summandOn i⟩⟩, ?_⟩
  rintro ⟨hb, hs⟩ x
  obtain ⟨U₀, hxU₀, s, hs₀⟩ := hb x
  choose W hxW hsum using fun i : ℤ => hs i x
  obtain ⟨V, hxV, hV⟩ := exists_mem_le_of_finset X s W x hxW
  refine ⟨U₀ ⊓ V, ⟨hxU₀, hxV⟩, ⟨⟨s, fun i hi => isZero_over_of_le X inf_le_left (hs₀ i hi)⟩,
    fun i => ?_⟩⟩
  by_cases hi : i ∈ s
  · exact isFiniteFreeSummandOn_of_le X (le_trans inf_le_right (hV i hi)) (hsum i)
  · exact isFiniteFreeSummandOn_of_isZero X (isZero_over_of_le X inf_le_left (hs₀ i hi))

/-- Each term of a locally strictly perfect complex is locally a direct summand of a finite
free `O_X`-module, hence falls under Stacks 0FNV. -/
theorem isLocallyFiniteFreeSummand_of_isLocallyStrictlyPerfect
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (hF : IsLocallyStrictlyPerfect X F) (i : ℤ) :
    IsLocallyFiniteFreeSummand X (F.X i) :=
  ((isLocallyStrictlyPerfect_iff X F).mp hF).2 i

/-- A locally strictly perfect complex is locally bounded. -/
theorem isLocallyBounded_of_isLocallyStrictlyPerfect
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (hF : IsLocallyStrictlyPerfect X F) :
    IsLocallyBounded X F :=
  ((isLocallyStrictlyPerfect_iff X F).mp hF).1

/-- **Under a global bound the two hypothesis phrasings of [Stacks, Tag 0FP9] are equivalent.**
The tag offers its hypothesis in two forms — that each term is locally a direct summand of a
finite free module, and that there is an open covering `X = ⋃ Uᵢ` with each `ℱ^•|_{Uᵢ}` strictly
perfect — and asserts they agree. Once a global `Finset` bound is assumed, they do: local
boundedness comes free from the bound by `isLocallyBounded_of_bound`, and
`isLocallyStrictlyPerfect_iff` supplies the rest.

So the covering phrasing is not a *stronger* hypothesis than the termwise one in the presence of
a global bound, which is the form in which the graded assembly of the tag is stated. -/
theorem isLocallyStrictlyPerfect_iff_of_bound
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {s : Finset ℤ}
    (hbd : ∀ i : ℤ, i ∉ s → IsZero (F.X i)) :
    IsLocallyStrictlyPerfect X F ↔ ∀ i : ℤ, IsLocallyFiniteFreeSummand X (F.X i) :=
  ⟨isLocallyFiniteFreeSummand_of_isLocallyStrictlyPerfect X,
    fun hs => (isLocallyStrictlyPerfect_iff X F).mpr ⟨isLocallyBounded_of_bound X hbd, hs⟩⟩

/-- **The degreewise left duals of a locally strictly perfect complex.** For each `n`, the dual
sheaf `Hom(F^n, O_X)` is a left dual of `F^n` in the monoidal category of `O_X`-modules, with
the coevaluation and evaluation of Stacks 0FNV. These are the maps `η_n` and `ε_n` whose sums
Stacks 0FP9 takes to build the coevaluation and evaluation of the dual complex. -/
@[instance_reducible]
noncomputable def termExactPairing
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hF : IsLocallyStrictlyPerfect X F) (i : ℤ) :
    ExactPairing (F.X i) (dualSheaf X (F.X i)) :=
  dualSheafExactPairing X (F.X i)
    (isLocallyFiniteFreeSummand_of_isLocallyStrictlyPerfect X hF i)

end Stacks.SheafOfModules.OnSpace

end

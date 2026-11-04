module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Truncating a strictly perfect approximation on a ringed site

Let `(C, O)` be a ringed site, let `G` be a complex of `O`-modules whose cohomology vanishes
in degrees `> r`, and let `α : P ⟶ G` be an approximation of `G` by a strictly perfect complex
`P` in degrees `≥ m`, meaning that `Hʲ(α)` is an isomorphism for `j > m` and an epimorphism for
`j = m`. When `m ≤ r`, this file replaces `P` by a complex with no terms above degree `r`
without losing the approximation property: the canonical truncation `τ^{≤r} P` does the job,
and the composite `τ^{≤r} P ⟶ P ⟶ G` is again an approximation in degrees `≥ m`.

The only input beyond Mathlib's canonical truncation is that the degree-`r` cycles of `P` are
again a direct summand of a finite free `O`-module. On a site that is a statement which only
becomes true after refining a covering, so it is taken here as a hypothesis rather than proved,
and the purely homological part of the argument is thereby available independently of it.

The analogue over a ringed space, stated for `StrictlyPerfect.IsStrictlyPerfect`, is
`StrictlyPerfect.exists_isStrictlyPerfect_boundedAbove_of_approximation`.

## Main results

* `IsDirectSummandOfFiniteFree.of_isZero`: a zero `O`-module is a direct summand of a finite
  free `O`-module.
* `IsDirectSummandOfFiniteFree.of_retract`: being a direct summand of a finite free `O`-module
  passes to retracts.
* `SheafOfModules.isZero_truncLE_X`: the canonical truncation in degrees `≤ r` has no terms
  above degree `r`.
* `SheafOfModules.isStrictlyPerfect_truncLE`: the canonical truncation `τ^{≤r} P` of a strictly
  perfect complex is strictly perfect provided its degree-`r` cycles are a direct summand of a
  finite free `O`-module.
* `SheafOfModules.isZero_truncGE_X` and `SheafOfModules.isStrictlyPerfect_truncGE`: the mirror
  statements for the canonical truncation in degrees `≥ r`, whose degree-`r` term is the
  opcycles object; this is the complex the perfectness criterion of Stacks 08G7 produces.
* `SheafOfModules.isLE_of_isIso_homologyMap`: an approximation in degrees `≥ m` of a complex
  with no cohomology above `r ≥ m` has itself no cohomology above `r`.
* `SheafOfModules.exists_isStrictlyPerfect_boundedAbove_of_approximation`: the truncated
  approximation `τ^{≤r} P ⟶ G` is an approximation in degrees `≥ m` by a strictly perfect complex
  with no terms above degree `r`.

## Implementation notes

The truncation used is Mathlib's canonical truncation `CochainComplex.truncLE`, not a stupid
truncation: for cochain complexes the canonical truncation in degrees `≤ r` is a *subcomplex*,
so it comes with a map `CochainComplex.ιTruncLE` *into* `P`, which is the direction an
approximation of `G` needs. Mathlib already supplies that this map is a quasi-isomorphism
exactly when `P` has no cohomology above `r` (`CochainComplex.quasiIso_ιTruncLE_iff`), which is
what makes the composite with `α` still an approximation.

Degreewise, `τ^{≤r} P` agrees with `P` below `r`, is the cycles object in degree `r`, and is
zero above `r`. Only the degree-`r` term is not visibly a direct summand of a finite free
module, so that single fact is isolated as the hypothesis `hcyc`.

`IsDirectSummandOfFiniteFree` and `IsStrictlyPerfect` carry four independent universes: the
objects and the morphisms of the site, the sections of the structure sheaf, and the sections
of the modules. This file instantiates the last two at `0`; at equal ring and module universes
the predicate is the plain retract condition, which is `isDirectSummandOfFiniteFree_iff_free`
and is how the two lemmas below are proved. Sheafification for abelian-group-valued presheaves
is assumed in its left exact form `HasSheafify`, which is what makes `SheafOfModules.{0} R`
abelian and hence gives the complexes homology; the weak form that `SheafOfModules.free` needs
follows from it.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{0})
  [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- A zero `O`-module is a direct summand of a finite free `O`-module, namely of `O^{⊕0}`:
both composites out of a zero object agree with the identity. -/
lemma IsDirectSummandOfFiniteFree.of_isZero {F : SheafOfModules.{0} R} (hF : IsZero F) :
    IsDirectSummandOfFiniteFree R F :=
  (isDirectSummandOfFiniteFree_iff_free R F).mpr ⟨0, 0, 0, hF.eq_of_src _ _⟩

/-- A retract of a direct summand of a finite free `O`-module is again a direct summand of a
finite free `O`-module: compose the two retractions. -/
lemma IsDirectSummandOfFiniteFree.of_retract {F G : SheafOfModules.{0} R} (ρ : Retract F G)
    (hG : IsDirectSummandOfFiniteFree R G) : IsDirectSummandOfFiniteFree R F := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R G).mp hG
  refine (isDirectSummandOfFiniteFree_iff_free R F).mpr ⟨n, ρ.i ≫ i, r ≫ ρ.r, ?_⟩
  rw [Category.assoc, ← Category.assoc i, hir, Category.id_comp, ρ.retract]

namespace SheafOfModules

variable {R}

/-- The canonical truncation in degrees `≤ r` has no terms above degree `r`. -/
theorem isZero_truncLE_X (P : CochainComplex (SheafOfModules.{0} R) ℤ) (r : ℤ) {i : ℤ}
    (hi : r < i) : IsZero ((P.truncLE r).X i) :=
  (P.truncLE r).isZero_of_isStrictlyLE r i hi

/-- The canonical truncation in degrees `≤ r` of a strictly perfect complex of `O`-modules is
strictly perfect, provided its degree-`r` cycles are a direct summand of a finite free
`O`-module.

Below degree `r` the truncation agrees with `P`, in degree `r` it is the cycles object, and
above `r` it vanishes; only the middle case needs the extra hypothesis. -/
theorem isStrictlyPerfect_truncLE {P : CochainComplex (SheafOfModules.{0} R) ℤ}
    (hP : IsStrictlyPerfect R P) (r : ℤ)
    (hcyc : IsDirectSummandOfFiniteFree R (P.cycles r)) :
    IsStrictlyPerfect R (P.truncLE r) where
  bounded := by
    refine Set.Finite.subset (hP.bounded.union (Set.finite_singleton r)) ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    rcases lt_trichotomy i r with h | h | h
    · exact Or.inl fun hz => hi (hz.of_iso (P.truncLEXIso r i h))
    · exact Or.inr (by simp [h])
    · exact absurd (isZero_truncLE_X P r h) hi
  termDirectSummand i := by
    rcases lt_trichotomy i r with h | h | h
    · exact IsDirectSummandOfFiniteFree.of_iso R (P.truncLEXIso r i h)
        (hP.termDirectSummand i)
    · subst h
      exact IsDirectSummandOfFiniteFree.of_iso R (P.truncLEXIsoCycles i) hcyc
    · exact IsDirectSummandOfFiniteFree.of_isZero R (isZero_truncLE_X P r h)

/-- The canonical truncation in degrees `≥ r` has no terms below degree `r`. -/
theorem isZero_truncGE_X (P : CochainComplex (SheafOfModules.{0} R) ℤ) (r : ℤ) {i : ℤ}
    (hi : i < r) : IsZero ((P.truncGE r).X i) :=
  (P.truncGE r).isZero_of_isStrictlyGE r i hi

/-- The canonical truncation in degrees `≥ r` of a strictly perfect complex of `O`-modules is
strictly perfect, provided its degree-`r` opcycles are a direct summand of a finite free
`O`-module.

Above degree `r` the truncation agrees with `P`, in degree `r` it is the opcycles object — the
cokernel of `P^{r-1} ⟶ P^r` — and below `r` it vanishes; only the middle case needs the extra
hypothesis. This is the complex `E' ⟶ E^{a+1} ⟶ … ⟶ E^b` of the proof of Stacks 08G7,
with `r = a` and `E' = Coker(E^{a-1} ⟶ E^a)`. -/
theorem isStrictlyPerfect_truncGE {P : CochainComplex (SheafOfModules.{0} R) ℤ}
    (hP : IsStrictlyPerfect R P) (r : ℤ)
    (hop : IsDirectSummandOfFiniteFree R (P.opcycles r)) :
    IsStrictlyPerfect R (P.truncGE r) where
  bounded := by
    refine Set.Finite.subset (hP.bounded.union (Set.finite_singleton r)) ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    rcases lt_trichotomy i r with h | h | h
    · exact absurd (isZero_truncGE_X P r h) hi
    · exact Or.inr (by simp [h])
    · exact Or.inl fun hz => hi (hz.of_iso (P.truncGEXIso r i h))
  termDirectSummand i := by
    rcases lt_trichotomy i r with h | h | h
    · exact IsDirectSummandOfFiniteFree.of_isZero R (isZero_truncGE_X P r h)
    · subst h
      exact IsDirectSummandOfFiniteFree.of_iso R (P.truncGEXIsoOpcycles i) hop
    · exact IsDirectSummandOfFiniteFree.of_iso R (P.truncGEXIso r i h)
        (hP.termDirectSummand i)

/-- An approximation in degrees `≥ m` of a complex of `O`-modules without cohomology above
`r ≥ m` has itself no cohomology above `r`: in that range the approximation is an isomorphism
on cohomology. -/
theorem isLE_of_isIso_homologyMap {P G : CochainComplex (SheafOfModules.{0} R) ℤ} (m r : ℤ)
    (hmr : m ≤ r) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) : P.IsLE r := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : IsIso (HomologicalComplex.homologyMap α i) := hiso i (hmr.trans_lt hi)
  exact (hG i hi).of_iso (asIso (HomologicalComplex.homologyMap α i))

/-- **Truncating an approximation on a ringed site.** If `α : P ⟶ G` is an approximation in
degrees `≥ m` of a complex `G` of `O`-modules with no cohomology above `r`, if `m ≤ r`, if `P`
is strictly perfect and if the degree-`r` cycles of `P` are a direct summand of a finite free
`O`-module, then `G` admits an approximation in degrees `≥ m` by a strictly perfect complex
with no terms above degree `r`. -/
theorem exists_isStrictlyPerfect_boundedAbove_of_approximation
    {P G : CochainComplex (SheafOfModules.{0} R) ℤ} (hP : IsStrictlyPerfect R P) (m r : ℤ)
    (hmr : m ≤ r) (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (hcyc : IsDirectSummandOfFiniteFree R (P.cycles r)) :
    ∃ Q : CochainComplex (SheafOfModules.{0} R) ℤ, IsStrictlyPerfect R Q ∧
      (∀ i : ℤ, r < i → IsZero (Q.X i)) ∧
      ∃ β : Q ⟶ G, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) := by
  have : P.IsLE r := isLE_of_isIso_homologyMap m r hmr α hiso hG
  have hι : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap (P.ιTruncLE r) j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap _ j).1 (QuasiIso.quasiIsoAt (f := P.ιTruncLE r) j)
  refine ⟨P.truncLE r, isStrictlyPerfect_truncLE hP r hcyc,
    fun i hi => isZero_truncLE_X P r hi, P.ιTruncLE r ≫ α, fun j hj => ?_, ?_⟩
  · rw [HomologicalComplex.homologyMap_comp]
    exact IsIso.comp_isIso' (hι j) (hiso j hj)
  · rw [HomologicalComplex.homologyMap_comp]
    have := hι m
    exact epi_comp _ _

end SheafOfModules

end

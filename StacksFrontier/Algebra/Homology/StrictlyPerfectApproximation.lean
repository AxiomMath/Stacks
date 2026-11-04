module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands

/-!
# Truncating a strictly perfect approximation

Let `(X, O_X)` be a ringed space, let `G` be a complex of `O_X`-modules whose cohomology
vanishes in degrees `> r`, and let `α : P ⟶ G` be an approximation of `G` by a strictly
perfect complex `P` in degrees `≥ m`, meaning that `Hʲ(α)` is an isomorphism for `j > m`
and an epimorphism for `j = m`. When `m ≤ r`, this file replaces `P` by a complex with no
terms above degree `r` without losing the approximation property: the canonical truncation
`τ^{≤r} P` does the job, and the composite `τ^{≤r} P ⟶ P ⟶ G` is again an approximation
in degrees `≥ m`.

The only input beyond Mathlib's canonical truncation is that the degree-`r` cycles of `P`
are again a direct summand of a finite free module. That is a *local* statement about a
ringed space — it is where an open neighbourhood has to be shrunk — and it is taken here
as a hypothesis rather than proved, so that the purely homological part of the argument is
available independently of it.

## Main results

* `StrictlyPerfect.isDirectSummandOfFiniteFree_of_retract`: being a direct summand of a
  finite free module passes to retracts.
* `StrictlyPerfect.isDirectSummandOfFiniteFree_of_isZero`: a zero module is a direct
  summand of a finite free module.
* `StrictlyPerfect.isStrictlyPerfect_truncLE`: the canonical truncation `τ^{≤r} P` of a
  strictly perfect complex is strictly perfect provided its degree-`r` cycles are a direct
  summand of a finite free module.
* `StrictlyPerfect.isLE_of_isIso_homologyMap`: an approximation in degrees `≥ m` of a
  complex with no cohomology above `r ≥ m` has itself no cohomology above `r`.
* `StrictlyPerfect.exists_isStrictlyPerfect_boundedAbove_of_approximation`: the truncated
  approximation, packaged as the existence statement that a local approximation argument
  consumes.
* `StrictlyPerfect.exists_section_of_surjective_sections`: a morphism onto a direct summand of
  a finite free `O_X`-module which is surjective on sections admits a section.
* `StrictlyPerfect.epi_toCycles_of_isZero_homology`: the map from a term of a complex to the
  cycles one degree up is an epimorphism exactly where the cohomology vanishes.
* `StrictlyPerfect.retractCyclesOfSection`: a section of `P^k ⟶ Z^{k+1}(P)` exhibits
  `Z^k(P)` as a retract of `P^k`.
* `StrictlyPerfect.isDirectSummandOfFiniteFree_cycles_of_surjective_sections`: if the maps
  `P^k ⟶ Z^{k+1}(P)` are surjective on sections for all `k ≥ r`, then the degree-`r` cycles of
  a strictly perfect complex are a direct summand of a finite free module. This discharges the
  hypothesis `hcyc` of `exists_isStrictlyPerfect_boundedAbove_of_approximation`.
* `StrictlyPerfect.exists_isStrictlyPerfect_boundedAbove_of_approximation'`: the two combined.

## Implementation notes

The truncation used is Mathlib's canonical truncation `CochainComplex.truncLE`, not a
stupid truncation: for cochain complexes the canonical truncation in degrees `≤ r` is a
*subcomplex*, so it comes with a map `CochainComplex.ιTruncLE` *into* `P`, which is the
direction an approximation of `G` needs. Mathlib already supplies that this map is a
quasi-isomorphism exactly when `P` has no cohomology above `r`
(`CochainComplex.quasiIso_ιTruncLE_iff`), which is what makes the composite with `α` still
an approximation.

Degreewise, `τ^{≤r} P` agrees with `P` below `r`, is the cycles object in degree `r`, and
is zero above `r`. Only the degree-`r` term is not visibly a direct summand of a finite
free module, so that single fact is isolated as the hypothesis `hcyc`.

That hypothesis is then discharged by `isDirectSummandOfFiniteFree_cycles_of_surjective_sections`
from one input: that for every `k ≥ r` the map `P^k ⟶ Z^{k+1}(P)` is surjective on sections.
The downward induction which reduces to that input is carried out here, on the whole space: the
map `P^k ⟶ Z^{k+1}(P)` is an epimorphism precisely because `H^{k+1}(P) = 0`
(`epi_toCycles_of_isZero_homology`), a section of it splits `P^k` as `Z^k(P) ⊕ Z^{k+1}(P)` and so
makes `Z^k(P)` a retract of `P^k` (`retractCyclesOfSection`), and a section exists as soon as
`Z^{k+1}(P)` is a direct summand of a finite free module and the map is surjective on sections
(`exists_section_of_surjective_sections`, which needs only the finitely many sections
`O_X^{⊕n} ⟶ Z^{k+1}(P)` of a chosen retraction to lift). The induction runs downwards from the
top nonzero degree of `P`, where the cycles vanish, to `r`, and there are only finitely many
steps because `P` is bounded.

What is therefore *not* in this file, and is the whole of the remaining local input, is that a
point has a neighbourhood on which those finitely many sections do lift — that is, on which the
epimorphisms `P^k ⟶ Z^{k+1}(P)`, which are locally surjective, are surjective on sections. That
step needs the restriction functors for module sheaves on open subspaces and is deliberately kept
out.

**Universes.** `StrictlyPerfect.OXMod.{u, w, v}` takes the ring universe first, then the
module universe and the carrier universe of the ringed space. The three statements that mention
neither cohomology nor a finite free module keep the ring universe `u` and the carrier universe `v`
independent, and the two closure properties of the direct-summand predicate are polymorphic
in the module universe as well. Everything that mentions the cohomology of a complex of
`O_X`-modules sets all three equal, because `Abelian (StrictlyPerfect.OXMod X)` — hence
`HomologicalComplex.HasHomology` — is found by instance search only then; that is an
instance-availability constraint, not a typing one, and it could be traded for explicit
`HasSheafify`/`WEqualsLocallyBijective` hypotheses, which is deliberately not done here
because no consumer of this file needs the generality.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace StrictlyPerfect

universe u v w

/-! ### Statements that do not mention cohomology

The two closure properties of the direct-summand predicate are pure category theory, and the
existence of a section out of a finite free summand needs only the biproduct and
`SheafOfModules.unitHomEquiv`. None of the three mentions homology or sheafification, so all
three hold for a ringed space with independent ring and space universes; the two closure
properties hold at an arbitrary module universe `w` as well, while a section out of
`O_X^{⊕ n}` only makes sense at the module universe `u` where `O_X^{⊕ n}` lives. -/

section PredicateClosure

variable {X : AlgebraicGeometry.RingedSpace.{u, v}}

/-- A retract of a direct summand of a finite free `O_X`-module is again a direct summand
of a finite free `O_X`-module.

`StrictlyPerfect.IsDirectSummandOfFiniteFree` is a retract statement in the common module
universe, so the given retract is first pushed through `StrictlyPerfect.moduleULift`; that
functor is where the two module universes are reconciled, and `Retract.map` is all that is
needed because a functor carries a retract to a retract. -/
theorem isDirectSummandOfFiniteFree_of_retract {E F : OXMod.{u, w} X} (ρ : Retract E F)
    (hF : IsDirectSummandOfFiniteFree F) : IsDirectSummandOfFiniteFree E := by
  obtain ⟨n, ⟨σ⟩⟩ := hF
  exact ⟨n, ⟨(ρ.map (moduleULift X)).trans σ⟩⟩

/-- A zero `O_X`-module is a direct summand of a finite free `O_X`-module, namely of
`O_X^{⊕ 0}`.

`StrictlyPerfect.moduleULift` is additive, so it carries the zero object to a zero object
and the retract identity `0 ≫ 0 = 𝟙` holds in the common module universe. -/
theorem isDirectSummandOfFiniteFree_of_isZero {E : OXMod.{u, w} X} (hE : IsZero E) :
    IsDirectSummandOfFiniteFree E := by
  refine ⟨0, ⟨⟨0, 0, ?_⟩⟩⟩
  rw [zero_comp, ← CategoryTheory.Functor.map_id, hE.eq_of_src (𝟙 E) 0,
    CategoryTheory.Functor.map_zero]

/-- A morphism `g : M ⟶ E` of `O_X`-modules onto a retract `E` of `O_X^{⊕n}` which is surjective
on sections admits a section.

Only the `n` sections `O_X ⟶ O_X^{⊕n} ⟶ E` obtained from the retraction have to be lifted: a
morphism out of `O_X^{⊕n}` is exactly an `n`-tuple of sections, so lifting those `n` sections
produces `t : O_X^{⊕n} ⟶ M` with `t ≫ g` the retraction, and the composite of the inclusion of
`E` with `t` is then a section of `g`. -/
theorem exists_section_of_surjective_sections {M E : OXMod.{u, u} X} (g : M ⟶ E) {n : ℕ}
    (ρ : Retract E (finiteFree X n))
    (hg : Function.Surjective (SheafOfModules.sectionsMap g)) :
    ∃ s : E ⟶ M, s ≫ g = 𝟙 E := by
  choose e he using fun k : Fin n =>
    hg (SheafOfModules.unitHomEquiv E (biproduct.ι (fun _ : Fin n => structureModule X) k ≫ ρ.r))
  let u : ∀ _ : Fin n, structureModule X ⟶ M := fun k =>
    (SheafOfModules.unitHomEquiv M).symm (e k)
  let t : finiteFree X n ⟶ M := biproduct.desc u
  have key : t ≫ g = ρ.r := by
    show biproduct.desc u ≫ g = ρ.r
    refine biproduct.hom_ext' _ _ fun k => ?_
    rw [biproduct.ι_desc_assoc]
    show (SheafOfModules.unitHomEquiv M).symm (e k) ≫ g = _
    rw [SheafOfModules.unitHomEquiv_symm_comp, he k, Equiv.symm_apply_apply]
    rfl
  exact ⟨ρ.i ≫ t, by rw [Category.assoc, key, ρ.retract]⟩

end PredicateClosure

/-! ### Truncating an approximation

From here on the ring and space universes of the ringed space agree and the module
universe agrees with them.  That is forced by instance availability rather than by typing:
every statement below mentions the cohomology of a complex of `O_X`-modules, and
`Abelian (StrictlyPerfect.OXMod X)` — hence `HomologicalComplex.HasHomology` — is found
only when all three coincide. -/

section Truncation

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
variable {P G : CochainComplex (OXMod.{u, u} X) ℤ}

/-- An approximation in degrees `≥ m` of a complex without cohomology above `r ≥ m` has
itself no cohomology above `r`: in that range the approximation is an isomorphism on
cohomology. -/
theorem isLE_of_isIso_homologyMap (m r : ℤ) (hmr : m ≤ r) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) : P.IsLE r := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : IsIso (HomologicalComplex.homologyMap α i) := hiso i (hmr.trans_lt hi)
  exact (hG i hi).of_iso (asIso (HomologicalComplex.homologyMap α i))

/-- The canonical truncation in degrees `≤ r` has no terms above degree `r`. -/
theorem isZero_truncLE_X (P : CochainComplex (OXMod.{u, u} X) ℤ) (r : ℤ) {i : ℤ} (hi : r < i) :
    IsZero ((P.truncLE r).X i) :=
  (P.truncLE r).isZero_of_isStrictlyLE r i hi

/-- The canonical truncation in degrees `≤ r` of a strictly perfect complex is strictly
perfect, provided its degree-`r` cycles are a direct summand of a finite free module.

Below degree `r` the truncation agrees with `P`, in degree `r` it is the cycles object, and
above `r` it vanishes; only the middle case needs the extra hypothesis. -/
theorem isStrictlyPerfect_truncLE (hP : IsStrictlyPerfect P) (r : ℤ)
    (hcyc : IsDirectSummandOfFiniteFree (P.cycles r)) :
    IsStrictlyPerfect (P.truncLE r) where
  bounded := by
    refine Set.Finite.subset (hP.bounded.union (Set.finite_singleton r)) ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    rcases lt_trichotomy i r with h | h | h
    · exact Or.inl fun hz => hi (hz.of_iso (P.truncLEXIso r i h))
    · exact Or.inr (by simp [h])
    · exact absurd (isZero_truncLE_X P r h) hi
  directSummand i := by
    rcases lt_trichotomy i r with h | h | h
    · exact isDirectSummandOfFiniteFree_of_iso (P.truncLEXIso r i h) (hP.directSummand i)
    · subst h
      exact isDirectSummandOfFiniteFree_of_iso (P.truncLEXIsoCycles i) hcyc
    · exact isDirectSummandOfFiniteFree_of_isZero (isZero_truncLE_X P r h)

/-- Truncating an approximation. If `α : P ⟶ G` is an approximation in degrees `≥ m` of a
complex `G` with no cohomology above `r`, if `m ≤ r`, if `P` is strictly perfect and if the
degree-`r` cycles of `P` are a direct summand of a finite free module, then `G` admits an
approximation in degrees `≥ m` by a strictly perfect complex with no terms above degree
`r`. -/
theorem exists_isStrictlyPerfect_boundedAbove_of_approximation
    (hP : IsStrictlyPerfect P) (m r : ℤ) (hmr : m ≤ r)
    (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (hcyc : IsDirectSummandOfFiniteFree (P.cycles r)) :
    ∃ Q : CochainComplex (OXMod.{u, u} X) ℤ, IsStrictlyPerfect Q ∧
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

/-! ### The degree-`r` cycles of a strictly perfect complex

The hypothesis `hcyc` above is now reduced to a statement about sections. -/

/-- The map `P^k ⟶ Z^{k+1}(P)` from a term of a complex to the cycles one degree up is an
epimorphism when the cohomology in degree `k + 1` vanishes: that cohomology is by definition its
cokernel. -/
theorem epi_toCycles_of_isZero_homology (P : CochainComplex (OXMod.{u, u} X) ℤ) (k : ℤ)
    (h : IsZero (P.homology (k + 1))) : Epi (P.toCycles k (k + 1)) :=
  Preadditive.epi_of_isZero_cokernel' _ (P.homologyIsCokernel k (k + 1) (by simp)) h

/-- A section of `P^k ⟶ Z^{k+1}(P)` splits the short exact sequence
`0 ⟶ Z^k(P) ⟶ P^k ⟶ Z^{k+1}(P) ⟶ 0` and so exhibits the degree-`k` cycles as a retract of
`P^k`.

The retraction is `1 - (P^k ⟶ Z^{k+1}(P)) ≫ s`, which kills the differential and therefore
factors through the kernel `Z^k(P)` of the differential; it restricts to the identity on `Z^k(P)`
because the cycles are annihilated by `P^k ⟶ Z^{k+1}(P)`. -/
noncomputable def retractCyclesOfSection (k : ℤ) (s : P.cycles (k + 1) ⟶ P.X k)
    (hs : s ≫ P.toCycles k (k + 1) = 𝟙 (P.cycles (k + 1))) :
    Retract (P.cycles k) (P.X k) := by
  have hiz : P.iCycles k ≫ P.toCycles k (k + 1) = 0 := by
    rw [← cancel_mono (P.iCycles (k + 1)), Category.assoc, P.toCycles_i, zero_comp,
      P.iCycles_d k (k + 1)]
  have hp : (𝟙 (P.X k) - P.toCycles k (k + 1) ≫ s) ≫ P.d k (k + 1) = 0 := by
    have hsd : s ≫ P.d k (k + 1) = P.iCycles (k + 1) := by
      rw [← P.toCycles_i k (k + 1), ← Category.assoc, hs, Category.id_comp]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hsd, P.toCycles_i, sub_self]
  refine ⟨P.iCycles k, P.liftCycles (𝟙 (P.X k) - P.toCycles k (k + 1) ≫ s) (k + 1) (by simp) hp,
    ?_⟩
  rw [← cancel_mono (P.iCycles k), Category.assoc, P.liftCycles_i, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, hiz, zero_comp, sub_zero, Category.id_comp]

/-- **The degree-`r` cycles of a strictly perfect complex are a direct summand of a finite free
module**, provided that for every `k ≥ r` the map `P^k ⟶ Z^{k+1}(P)` is surjective on sections.

The argument is a downward induction from the top nonzero degree of `P`, which exists because `P`
is bounded. Above that degree the cycles vanish, hence are a direct summand of `O_X^{⊕0}`. For
`r ≤ k` below it, a retraction of the already-known direct summand `Z^{k+1}(P)` onto a finite
free module gives, by `exists_section_of_surjective_sections`, a section of `P^k ⟶ Z^{k+1}(P)`,
and `retractCyclesOfSection` then makes `Z^k(P)` a retract of `P^k`, which is a direct summand of
a finite free module because `P` is strictly perfect.

The surjectivity hypothesis is what has to be arranged by shrinking an open neighbourhood: the
maps in question are epimorphisms as soon as `P` has no cohomology above `r`
(`epi_toCycles_of_isZero_homology`), hence locally surjective, and only finitely many sections of
finitely many degrees are involved. -/
theorem isDirectSummandOfFiniteFree_cycles_of_surjective_sections
    (hP : IsStrictlyPerfect P) (r : ℤ)
    (hsurj : ∀ k : ℤ, r ≤ k →
      Function.Surjective (SheafOfModules.sectionsMap (P.toCycles k (k + 1)))) :
    IsDirectSummandOfFiniteFree (P.cycles r) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) := by
    obtain ⟨n, hn⟩ := hP.bounded.bddAbove
    refine ⟨n, fun i hi => ?_⟩
    by_contra h
    exact absurd (hn h) (not_le.2 hi)
  have main : ∀ j : ℕ, ∀ k : ℤ, r ≤ k → n + 1 - k ≤ (j : ℤ) →
      IsDirectSummandOfFiniteFree (P.cycles k) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro k hrk hk
      rcases lt_or_ge n k with hnk | hnk
      · exact isDirectSummandOfFiniteFree_of_isZero
          (IsZero.of_mono (P.iCycles k) (hn k hnk))
      · obtain ⟨m, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract (P.cycles (k + 1))).mp
          (ih (j - 1) (by omega) (k + 1) (by omega) (by omega))
        obtain ⟨s, hs⟩ := exists_section_of_surjective_sections (P.toCycles k (k + 1)) ρ
          (hsurj k hrk)
        exact isDirectSummandOfFiniteFree_of_retract (retractCyclesOfSection k s hs)
          (hP.directSummand k)
  exact main (n + 1 - r).toNat r le_rfl (Int.self_le_toNat _)

/-- Truncating an approximation, with the direct-summand hypothesis on the degree-`r` cycles
replaced by the surjectivity-on-sections hypothesis it follows from. This is
`exists_isStrictlyPerfect_boundedAbove_of_approximation` composed with
`isDirectSummandOfFiniteFree_cycles_of_surjective_sections`, and isolates the one local input
that a local approximation argument still has to arrange by shrinking a neighbourhood. -/
theorem exists_isStrictlyPerfect_boundedAbove_of_approximation'
    (hP : IsStrictlyPerfect P) (m r : ℤ) (hmr : m ≤ r)
    (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (hsurj : ∀ k : ℤ, r ≤ k →
      Function.Surjective (SheafOfModules.sectionsMap (P.toCycles k (k + 1)))) :
    ∃ Q : CochainComplex (OXMod.{u, u} X) ℤ, IsStrictlyPerfect Q ∧
      (∀ i : ℤ, r < i → IsZero (Q.X i)) ∧
      ∃ β : Q ⟶ G, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) :=
  exists_isStrictlyPerfect_boundedAbove_of_approximation hP m r hmr hG α hiso hepi
    (isDirectSummandOfFiniteFree_cycles_of_surjective_sections hP r hsurj)

end Truncation

end StrictlyPerfect

end

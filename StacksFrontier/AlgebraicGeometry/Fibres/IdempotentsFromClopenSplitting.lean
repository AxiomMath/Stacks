module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting an idempotent off a fibre from a splitting of a neighbourhood

Let `f : X ⟶ S` be a proper morphism of schemes, let `s : S` and let `e ∈ Γ(X_s, 𝒪_{X_s})` be an
idempotent. [Stacks, Tag 0G7X] asserts that `e` lies in the image of `(f_*𝒪_X)_s`, which is to
say that `e` is the restriction of a section of `𝒪_X` over `f ⁻¹ᵁ U` for some open neighbourhood
`U` of `s`: the predicate `Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood` of
`StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre`.

The source's proof produces the lift *geometrically*. An idempotent of `Γ(X_s, 𝒪_{X_s})`
decomposes the fibre into two disjoint opens — its nonvanishing locus and the nonvanishing locus
of `1 - e` — and the theorem on formal functions is used to decompose an infinitesimal
neighbourhood of the fibre, and thence a Zariski neighbourhood, in a compatible way. This file
takes that geometric output as the hypothesis `hsplit` and supplies everything else: the
dictionary between idempotent sections and decompositions into two disjoint opens, in both
directions, together with its compatibility with restriction along the fibre inclusion.

## Main results

* `Stacks.AlgebraicGeometry.Fibres.eq_of_isIdempotentElem_of_basicOpen_eq`: **an idempotent
  section of the structure sheaf is determined by its nonvanishing locus.**
* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isIdempotentElem_of_isProper`:
  **Stacks 0G7X**, over the single hypothesis `hsplit` described below.

## Implementation notes

**The carried hypothesis.** `hsplit` says: for every proper `g : Y ⟶ T`, every `t : T` and every
idempotent `c ∈ Γ(Y_t, 𝒪_{Y_t})` there are an open neighbourhood `U` of `t` and two disjoint
opens `V₁, V₂` of `Y` covering `g ⁻¹ᵁ U` such that `V₁` meets the fibre exactly in the
nonvanishing locus of `c`. It is quantified over all proper morphisms, which is how [Stacks, Tag
0G7X] is itself quantified and which is what makes the conclusion below usable in the shape that
the consumers of that tag want — see `he` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/SteinFactorization/ConnectedFibres.lean`.

`hsplit` is **strictly stronger than the tag, and it is false**: it asks the lift to be an
*idempotent* section over `f ⁻¹ᵁ U`, which is to say a clopen decomposition of that
neighbourhood, whereas the tag asks only for a section.
`Stacks.SteinFactorization.eq_zero_or_one_of_clopenSplitting` derives from `hsplit` that every
fibre of every proper morphism with (pre)irreducible source has only the trivial idempotents in
its ring of global functions, and `Spec ℤ[i] ⟶ Spec ℤ` refutes that: it is finite, hence proper,
its source is irreducible, and its fibre over `(5)` is `Spec(𝔽₅ × 𝔽₅)`. So the theorem below is
vacuous, and nothing consumes it.  Tag 0G7X itself is
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`, proved unconditionally.
What this file contributes unconditionally is the dictionary: the whole passage from a
decomposition of a neighbourhood back to a *section*, and the proof that that section restricts
to `e` on the nose and not merely to something with the same support. Neither direction of that
dictionary is in this library: the only idempotent-versus-opens material present is the easy
direction over a preconnected open,
`Stacks.AlgebraicGeometry.ProperGeomConnected.isIdempotentElem_eq_zero_or_one`, and the indexed
gluing `Stacks.AlgebraicGeometry.ProperGeomConnected.bijective_piRestrict`, which is stated only
over the whole scheme and so does not apply to `f ⁻¹ᵁ U`.

**What `hsplit` stands for, and why it is not proved here.** In the source the decomposition comes
from the theorem on formal functions, [Stacks, Tag 02OD], at `p = 0`: for a Noetherian base it
identifies the completed stalk `(f_*𝒪_X)_s^∧` with `lim_n Γ(X_n, 𝒪_{X_n})` over the
infinitesimal neighbourhoods `X_n` of the fibre, each of which has the same underlying space as
`X_s` and therefore inherits the decomposition; the limit idempotent is pushed back down through
`(f_*𝒪_X)_s^∧ / 𝔪_s = (f_*𝒪_X)_s / 𝔪_s`, which needs `(f_*𝒪_X)_s` to be a finite module, i.e.
[Stacks, Tag 02O5]; and the general case follows by Noetherian approximation. Of this chain the
library has the geometric setup — the system `X_n` is
`Stacks.FormalFunctions.infinitesimalNeighbourhood`, with `X_1 = X_s` recorded as
`Stacks.FormalFunctions.fiberIsoInfinitesimalNeighbourhoodOne` — and the commutative-algebra
form of [Stacks, Tag 02OC], `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv`, itself
conditional on [Stacks, Tag 02OB]. It also has Tag 02O5 itself, proved unconditionally as
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`, together with
[Stacks, Tag 02O6], so the named hypothesis
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase` that several
modules carry is dischargeable and 02O5 is not the obstruction; and it has the Noetherian
approximation [Stacks, Tag 0A0P] as
`AlgebraicGeometry.exists_isLimit_isProper_finiteType_arrow`. What it does **not** have is
Tag 02OB, whose clauses are
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient` over
[Stacks, Tag 02OA], carried in turn over the Rees finiteness of [Stacks, Tag 02O8]
(`...isCohomologyReesFinite_of_isCoherent`, over part (1) of [Stacks, Tag 0897]); the
cohomological inputs of that part's base change `X' = Spec(B) ×_{Spec A} X` are all available
(Tags 01LX, 01SB, 01XZ, 089W, and the interchange of cohomology with direct sums), but two
constructions are absent — the total module `⨁ₙ Fₙ` of a `SheafOfModules.GradedModule` carrying
the action of the total algebra, which is what Tag 01SB's equivalence would be applied to and
which exists for algebras only (`SheafOfModules.GradedAlgebra.ungradedSheaf`), and any
identification of the ideal-sheaf Rees algebra
`Stacks.Cohomology.FormalFunctions.baseReesAlgebra` with the pullback `f^* B̃` of the ring Rees
algebra. Nor does the library have the stalk form Tag 02OD, only its geometric setup. Routing
Tag 0G7X instead through Zariski's connectedness
theorem, [Stacks, Tag 03H2], is not available either: in this library clause (1) of Tag 03H2 is
*derived from* Tag 0G7X, in
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_etaleNeighborhood`, and the
source's proof of Tag 03H2 quotes Tag 0G7X, so that route is circular.

**Properness is used only to invoke `hsplit`.** Nothing in the argument below needs it, which is
as it should be: in the source too, properness enters only through the theorem on formal
functions. The hypothesis is kept because the tag has it.

## References

* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X): the theorem, proved
  here over `hsplit`.
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD) and
  [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC): the theorem on formal
  functions, which is what produces `hsplit` in the source.
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5): coherence of the higher
  direct images of a proper morphism, the bottom of that chain, which is proved.
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB) and
  [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897): the uniform Artin–Rees
  bound and the graded finiteness it rests on, which are where the chain is blocked.
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2): the circular
  alternative route.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Fibres

variable {X S : Scheme.{u}}

/-! ### Idempotent sections versus decompositions into two disjoint opens -/

/-- The nonvanishing loci of an idempotent `e` and of `1 - e` are disjoint. -/
private theorem basicOpen_inf_basicOpen_one_sub {U : X.Opens} {e : Γ(X, U)}
    (he : IsIdempotentElem e) : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  rw [← Scheme.basicOpen_mul, hmul, Scheme.basicOpen_zero]

/-- **An idempotent section of the structure sheaf is determined by its nonvanishing locus.** If
`e₁` and `e₂` are idempotents of `Γ(X, U)` with `D(e₁) = D(e₂)` then `e₁ = e₂`.

For commuting idempotents `f` and `g` the product `f * (1 - g)` is again idempotent, and
`D(f * (1 - g)) = D(f) ⊓ D(1 - g)`, which is contained in `D(g) ⊓ D(1 - g) = ⊥` as soon as
`D(f) ≤ D(g)`; an idempotent with empty nonvanishing locus vanishes, by
`Stacks.AlgebraicGeometry.ProperGeomConnected.eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot`,
so `f = f * g`. Applying this both ways round gives `e₁ = e₁ * e₂ = e₂ * e₁ = e₂`.

This is the half of the dictionary between idempotent sections and decompositions into two
disjoint opens that makes the decomposition *determine* the section, and it is what turns a
geometric lift of the decomposition of a fibre into a lift of the idempotent itself. -/
theorem eq_of_isIdempotentElem_of_basicOpen_eq {U : X.Opens} {e₁ e₂ : Γ(X, U)}
    (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂)
    (h : X.basicOpen e₁ = X.basicOpen e₂) : e₁ = e₂ := by
  have key : ∀ a b : Γ(X, U), IsIdempotentElem a → IsIdempotentElem b →
      X.basicOpen a ≤ X.basicOpen b → a * b = a := by
    intro a b ha hb hab
    have hidem : IsIdempotentElem (a * (1 - b)) := ha.mul hb.one_sub
    have hbot : X.basicOpen (a * (1 - b)) = ⊥ := by
      rw [Scheme.basicOpen_mul]
      refine le_bot_iff.mp ?_
      rw [← basicOpen_inf_basicOpen_one_sub hb]
      exact inf_le_inf hab le_rfl
    linear_combination
      -(ProperGeomConnected.eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot hidem hbot)
  calc e₁ = e₁ * e₂ := (key e₁ e₂ h₁ h₂ h.le).symm
    _ = e₂ * e₁ := mul_comm _ _
    _ = e₂ := key e₂ e₁ h₂ h₁ h.ge

/-- The two-element family of sections of the structure sheaf which is `1` over the first open
and `0` over the second. It is the datum that the sheaf condition glues into a single idempotent
section over an open that the two cover disjointly. -/
private def boolSection (X : Scheme.{u}) (V₁ V₂ : X.Opens) :
    ∀ b : Bool, Γ(X, bif b then V₁ else V₂)
  | true => 1
  | false => 0

/-- **Two disjoint opens covering an open carry an idempotent section equal to `1` on the first
and `0` on the second.** This is the other half of the dictionary: the sheaf condition over the
two-element cover `{V₁, V₂}`, whose compatibility condition is vacuous because the sections over
`V₁ ⊓ V₂ = ⊥` form a subsingleton. Idempotency comes from the uniqueness clause, `a * a`
restricting to `1` and to `0` just as `a` does. -/
private theorem exists_isIdempotentElem_of_disjoint_cover {W V₁ V₂ : X.Opens} (h₁ : V₁ ≤ W)
    (h₂ : V₂ ≤ W) (hcover : W ≤ V₁ ⊔ V₂) (hdisj : V₁ ⊓ V₂ = ⊥) :
    ∃ a : Γ(X, W), IsIdempotentElem a ∧ X.presheaf.map (homOfLE h₁).op a = 1 ∧
      X.presheaf.map (homOfLE h₂).op a = 0 := by
  have hle : ∀ b : Bool, (bif b then V₁ else V₂) ≤ W := fun b ↦ by cases b <;> assumption
  have hiSup : W ≤ iSup (fun b : Bool ↦ bif b then V₁ else V₂) :=
    hcover.trans (sup_le (le_iSup (fun b : Bool ↦ bif b then V₁ else V₂) true)
      (le_iSup (fun b : Bool ↦ bif b then V₁ else V₂) false))
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj
      (fun b : Bool ↦ bif b then V₁ else V₂) (boolSection X V₁ V₂) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · have hbot : (bif i then V₁ else V₂) ⊓ (bif j then V₁ else V₂) = ⊥ := by
        cases i <;> cases j
        · exact absurd rfl hij
        · exact (inf_comm _ _).trans hdisj
        · exact hdisj
        · exact absurd rfl hij
      have hss : Subsingleton Γ(X, (bif i then V₁ else V₂) ⊓ (bif j then V₁ else V₂)) := by
        rw [hbot]
        infer_instance
      exact @Subsingleton.elim _ hss _ _
  obtain ⟨a, ha, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf
    (fun b : Bool ↦ bif b then V₁ else V₂) W (fun b ↦ homOfLE (hle b)) hiSup
    (boolSection X V₁ V₂) hcompat
  refine ⟨a, ?_, ha true, ha false⟩
  refine huniq (a * a) fun b ↦ ?_
  rw [map_mul, ha b]
  cases b
  · exact mul_zero _
  · exact mul_one _

/-- The nonvanishing locus of the section produced by
`Stacks.AlgebraicGeometry.Fibres.exists_isIdempotentElem_of_disjoint_cover` is the first of the
two opens: it contains `V₁` because the section restricts to a unit there, misses `V₂` because
the section restricts to zero there, and is contained in `V₁ ⊔ V₂`. -/
private theorem basicOpen_eq_of_disjoint_cover {W V₁ V₂ : X.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W)
    (hcover : W ≤ V₁ ⊔ V₂) {a : Γ(X, W)} (ha₁ : X.presheaf.map (homOfLE h₁).op a = 1)
    (ha₂ : X.presheaf.map (homOfLE h₂).op a = 0) : X.basicOpen a = V₁ := by
  have e₁ : V₁ ⊓ X.basicOpen a = V₁ := by
    simpa [ha₁] using (Scheme.basicOpen_res X a (homOfLE h₁).op).symm
  have e₂ : X.basicOpen a ⊓ V₂ = ⊥ := by
    simpa [ha₂, inf_comm] using (Scheme.basicOpen_res X a (homOfLE h₂).op).symm
  refine le_antisymm ?_ (inf_eq_left.mp e₁)
  calc X.basicOpen a = X.basicOpen a ⊓ V₁ ⊔ X.basicOpen a ⊓ V₂ := by
        rw [← inf_sup_left, inf_eq_left.mpr ((X.basicOpen_le a).trans hcover)]
    _ ≤ V₁ := by
        rw [e₂, sup_bot_eq]
        exact inf_le_right

/-- The nonvanishing locus of a section restricted along a morphism is the preimage of the
nonvanishing locus, cut down to the open it was restricted to. -/
private theorem basicOpen_appLE {Y Z : Scheme.{u}} (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (hle : V ≤ g ⁻¹ᵁ U) (r : Γ(Z, U)) :
    Y.basicOpen (g.appLE U V hle r) = V ⊓ g ⁻¹ᵁ Z.basicOpen r := by
  rw [Scheme.preimage_basicOpen]
  simp only [Scheme.Hom.appLE]
  rw [CommRingCat.comp_apply, Scheme.basicOpen_res]

/-! ### Stacks 0G7X -/

/-- **Stacks Project, Tag 0G7X.** Let `f : X ⟶ S` be a proper morphism of schemes, let `s : S`
and let `e ∈ Γ(X_s, 𝒪_{X_s})` be an idempotent. Then `e` is the restriction of a section of
`𝒪_X` over `f ⁻¹ᵁ U` for some open neighbourhood `U` of `s`, which is membership in the image of
`(f_*𝒪_X)_s → Γ(X_s, 𝒪_{X_s})`.

The hypothesis `hsplit` is the geometric half of the tag, quantified over all proper morphisms
exactly as the tag is: for each proper `g : Y ⟶ T`, each `t : T` and each idempotent `c` on the
fibre `Y_t`, an open neighbourhood `U` of `t` whose preimage `g ⁻¹ᵁ U` splits as two disjoint
opens `V₁ ⊔ V₂`, with `V₁` meeting the fibre exactly in the nonvanishing locus of `c`. In the
source that splitting comes from the theorem on formal functions, which this library does not
have; see the module documentation.

Everything else is proved: the two disjoint opens carry an idempotent section `a` of `𝒪_X` over
`f ⁻¹ᵁ U`, by the sheaf condition over the two-element cover
(`Stacks.AlgebraicGeometry.Fibres.exists_isIdempotentElem_of_disjoint_cover`); the nonvanishing
locus of `a` is `V₁` (`Stacks.AlgebraicGeometry.Fibres.basicOpen_eq_of_disjoint_cover`); hence
the restriction of `a` to the fibre is an idempotent whose nonvanishing locus is that of `e`; and
an idempotent is determined by its nonvanishing locus
(`Stacks.AlgebraicGeometry.Fibres.eq_of_isIdempotentElem_of_basicOpen_eq`), so the restriction of
`a` *is* `e`. -/
-- NO `@[stacks 0G7X]` ATTRIBUTE HERE. The theorem below is true but VACUOUS: its hypothesis
-- `hsplit` is refuted in this repository by
-- `Stacks.SteinFactorization.eq_zero_or_one_of_clopenSplitting`
-- (StacksFrontier/AlgebraicGeometry/MoreMorphisms/SteinFactorization/Noetherian.lean), with the
-- witness `Spec ℤ[i] ⟶ Spec ℤ` at `(5)`: `hsplit` demands that the lift be an IDEMPOTENT
-- section, whereas Tag 0G7X asks only that the idempotent be the restriction of SOME section.
-- `(1,0) ∈ 𝔽₅ × 𝔽₅` does lift to `ℤ[i]`; what fails is idempotency of the lift.
-- A tag counts only on a declaration proved under the source's own hypotheses, so a
-- registration standing on a refuted hypothesis is a false claim of coverage that can never
-- be discharged -- strictly worse than an ordinary conditional one, which at least waits on
-- something provable. Tag 0G7X therefore has NO site in this library, which is the honest
-- state: the theorem on formal functions it rests on is not available (see the module doc).
-- Do not re-attach the attribute here. The real route is the chain through Stacks 0897(1),
-- 02O8, 02OA, 02OB and the stalk form of 02OD.
theorem extendsOverNeighbourhood_of_isIdempotentElem_of_isProper
    (hsplit : ∀ {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] (t : T) (c : Γ(g.fiber t, ⊤)),
      IsIdempotentElem c → ∃ (U : T.Opens) (_ : t ∈ U) (V₁ V₂ : Y.Opens), V₁ ≤ g ⁻¹ᵁ U ∧
        V₂ ≤ g ⁻¹ᵁ U ∧ g ⁻¹ᵁ U ≤ V₁ ⊔ V₂ ∧ V₁ ⊓ V₂ = ⊥ ∧
          g.fiberι t ⁻¹ᵁ V₁ = (g.fiber t).basicOpen c)
    (f : X ⟶ S) [IsProper f] (s : S) (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ExtendsOverNeighbourhood f s e := by
  obtain ⟨U, hsU, V₁, V₂, hle₁, hle₂, hcover, hdisj, htrace⟩ := hsplit f s e he
  obtain ⟨a, haidem, ha₁, ha₂⟩ :=
    exists_isIdempotentElem_of_disjoint_cover hle₁ hle₂ hcover hdisj
  refine ⟨U, hsU, a, ?_⟩
  have htop : ⊤ ≤ f.fiberι s ⁻¹ᵁ (f ⁻¹ᵁ U) := (fiberι_preimage_preimage_eq_top f hsU).ge
  have hidem : IsIdempotentElem ((f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ htop a) := haidem.map _
  refine eq_of_isIdempotentElem_of_basicOpen_eq hidem he ?_
  rw [basicOpen_appLE, basicOpen_eq_of_disjoint_cover hle₁ hle₂ hcover ha₁ ha₂, htrace, top_inf_eq]

end Stacks.AlgebraicGeometry.Fibres

end

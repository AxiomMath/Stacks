module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.NowhereDense
public import StacksFrontier.AlgebraicGeometry.EulerCharDirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Exactness
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.NowhereDenseDrop
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact

/-!
# Removing embedded associated points from the inductive step of Tag 0BEM

The induction of [Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) is driven by the
first difference of the Euler characteristic in one twisting direction, and
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep` reduces the tag to exactly that
difference identity: for every coherent `𝒢` of positive-dimensional support and every direction
`i`, two coherent sheaves `𝒢₁`, `𝒢₂` of strictly smaller support dimension with

  `χ(𝒢 ⊗ 𝓛ᵢ ⊗ twist) - χ(𝒢 ⊗ twist) = χ(𝒢₁ ⊗ twist) - χ(𝒢₂ ⊗ twist)`.

The source produces that identity only after two reductions, and this file performs the first of
them: **the removal of embedded associated points.** Given the identity for every coherent sheaf
*without* embedded associated points, it is supplied for every coherent sheaf.

The reduction is the source's first paragraph. [Stacks, Tag 02OL] gives a coherent subsheaf
`𝒦 ⊆ 𝒢` whose support is nowhere dense in `Supp 𝒢` and whose quotient `𝒬 = 𝒢/𝒦` has the *same*
support and *no* embedded associated points. Additivity of the Euler characteristic along
`0 ⟶ 𝒦 ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` splits the first difference of `𝒢` into the first difference of `𝒦` and
that of `𝒬`; the one for `𝒦` is `χ(𝒦 ⊗ 𝓛ᵢ ⊗ twist) - χ(𝒦 ⊗ twist)` by definition, and the one
for `𝒬` is the hypothesis. The four terms are then merged into two by a biproduct, whose Euler
characteristic is additive by the same lemma applied to the split sequence
`0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0`.

**Why this works at the level of the difference identity and not at the level of the two short
exact sequences.** `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences`
asks for two short exact sequences with a *common first term*. Replacing `𝒢` by `𝒬` and pulling
the two sequences back along `𝒢 ⟶ 𝒬` restores the middle terms but makes the two first terms an
extension of `ℐ𝒬` by `𝒦` and an extension of `ℐ𝒬 ⊗ 𝓛ᵢ` by `𝒦 ⊗ 𝓛ᵢ`, which are not isomorphic,
so the common-first-term binder fails. The difference identity asks for no common first term,
and the source likewise discharges `𝒦` through Euler characteristics rather than through
sequences — by its induction hypothesis, which the identity's own strictly-smaller-support
binders make available to the driver.

## The descent measure is carried in its nowhere-dense form

`AlgebraicGeometry.IsTwistDifferenceStep` asks for the two output sheaves to have support
nowhere dense in `Supp 𝒢` rather than merely of strictly smaller `AlgebraicGeometry.natDimSupp`.
The strict inequality is recovered from it by
`AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense`, so this is a *stronger*
hypothesis; it is the right one for two independent reasons.

* It is what the geometry supplies. The two third terms of [Stacks, Tag 02P2] are supported on
  a nowhere dense closed subset (`AlgebraicGeometry.denominatorBadLocus_isNowhereDense`), and
  nowhere density is what `AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense`
  consumes; the `natDimSupp` inequality is a consequence that the supplier computes and discards.
* It is what the merge needs. A strict drop in `natDimSupp` is not stable under union: a closed
  subset of `Supp 𝒢` can contain a whole low-dimensional irreducible component of `Supp 𝒢` and
  still have strictly smaller dimension, so two sheaves of strictly smaller support dimension
  can have a biproduct whose support is not of strictly smaller dimension unless the dimension
  of a union of closed sets is known to be the maximum — a statement the library does not have.
  Nowhere density *is* stable under finite unions (`IsNowhereDense.union`), which is exactly what
  the biproduct step consumes.

## Main definitions

* `AlgebraicGeometry.biprodModules`: `𝒜 ⊞ ℬ` at the declared type `X.Modules`.
* `AlgebraicGeometry.IsTwistDifferenceStep`: the inductive step of [Stacks, Tag 0BEM] restricted
  to the sheaves satisfying a predicate, with the support-dimension drops in their nowhere-dense
  form.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `supp_subset_of_mono`: the support of a submodule lies in the support of the module.
* `supp_subset_union_of_shortExact`: the support of the middle term of a short exact sequence
  lies in the union of the supports of the outer terms.
* `supp_biprodModules_subset`: the support of a biproduct lies in the union of the supports.
* `eulerCharacteristic_twistedSheaf_biprodModules`: the Euler characteristic of the twists of a
  biproduct is additive, given [Stacks, Tag 02O6].
* `isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints`: **the removal of embedded associated
  points**, at the level of the inductive step, carrying any side condition on the sheaf that is
  determined by its support.
* `exists_eulerPolynomial_twistedSheaf_of_hasNoEmbeddedAssociatedPointsStep`: **[Stacks, Tag
  0BEM] from [Stacks, Tag 02O6] and the inductive step for sheaves with no embedded associated
  points.**

## What Tag 0BEM still owes after this file

`hfin`, which is [Stacks, Tag 02O6], and nothing else. Note that it is *not* a hypothesis of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep`: the Euler characteristic is a
junk-value definition, so finiteness is absent from the tag's statement, and Tag 02O6 enters only
through the additivity used to assemble the difference identity — here and in
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences`.

The other hypothesis of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hasNoEmbeddedAssociatedPointsStep` — the
inductive step for a coherent sheaf with no embedded associated points, which is the source's
second and third paragraphs — is supplied by
`AlgebraicGeometry.isTwistDifferenceStep_hasNoEmbeddedAssociatedPoints`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/StepAssembly.lean`), so that
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` there is
Tag 0BEM's full conclusion from `hfin` alone. That assembly replaces the scheme by the
scheme-theoretic support ([Stacks, Tag 02OM]) so that the sheaf acquires full support, applies
[Stacks, Tag 02OZ] and [Stacks, Tag 02P2] there — through
`AlgebraicGeometry.exists_differenceSequences_of_supp_eq_univ` — removes the embedded associated
points downstairs with **this file's reduction at the side condition *full support***, and carries
everything back along the closed immersion by [Stacks, Tag 089W] and the projection formula
[Stacks, Tag 01E8]: the twisted Euler characteristic by
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion` (the
projection formula folded over the twisting exponents, `pushforwardTwistedSheafIso`), and the three
measures `AlgebraicGeometry.IsTwistDifferenceStep` descends on by
`AlgebraicGeometry.supp_pushforward_of_isClosedImmersion`,
`AlgebraicGeometry.natDimSupp_pushforward_of_isClosedImmersion` and
`AlgebraicGeometry.isNowhereDense_preimage_val_supp_pushforward_iff`, all of
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/PushforwardTwist.lean`.

## Implementation notes

**Why `AlgebraicGeometry.biprodModules` exists.** `CategoryTheory.Limits.biprod` is used here
inside the argument of `SheafOfModules.supp`, whose own module argument has type
`SheafOfModules R` for an implicit `R`; elaborating `𝒜 ⊞ ℬ` against that expected type leaves
`R` a metavariable and `HasBinaryBiproduct` is then not synthesized, since instance search is
syntactic. A declared return type of `X.Modules` fixes `R` before the biproduct is elaborated.
This is the same device as `AlgebraicGeometry.tensorModules` in
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/ZeroDimensionalTensor.lean`.

**Why relative nowhere density is transported by a congruence lemma.** The quotient of
[Stacks, Tag 02OL] has `Supp 𝒬 = Supp 𝒢` as a propositional equality of subsets of `X`, and the
nowhere-density hypothesis mentions the subset in a *type* position, as the ambient space
`↥(Supp 𝒬)`. Rewriting there fails the motive check — the two spellings of the category of
sheaves of modules on a scheme are not definitionally equal at the `implicit` transparency level
that `rw` uses. `AlgebraicGeometry.isNowhereDense_preimage_val_congr` states the transport with
the two subsets as free variables, so it is discharged by `subst` once and applied by
unification, with no motive formed at the use site.

**No attribute for Tag 0BEM is attached**, and none for Tags 02OL, 02O6 or 02P2. Tag 0BEM's
statement is unconditional, while everything below is conditional on `hfin` and on the restricted
step; and the three support lemmas are not statements of a tag.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open scoped ZeroObject
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace AlgebraicGeometry

/-! ### Supports of monomorphisms, short exact sequences and biproducts -/

/-- **The support of a submodule lies in the support of the module.** A monomorphism of sheaves
of modules is detected stalkwise, so its stalk maps are injective and a nonzero element of a
stalk upstairs produces one downstairs. -/
theorem supp_subset_of_mono {X : Scheme.{u}} {A B : X.Modules} (g : A ⟶ B) [Mono g] :
    SheafOfModules.supp A ⊆ SheafOfModules.supp B := by
  intro x hx
  let T : ShortComplex X.Modules := ShortComplex.mk (0 : (0 : X.Modules) ⟶ A) g (by simp)
  have hT : T.Exact := (T.exact_iff_mono (by simp [T])).2 ‹Mono g›
  have hU := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    X.ringCatSheaf T).mp hT x
  have hUf : (AlgebraicGeometry.SheafOfModules.stalkShortComplex X.ringCatSheaf T x).f = 0 :=
    Functor.map_zero
      (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x) _ _
  have hinj : Function.Injective (ConcreteCategory.hom
      (AlgebraicGeometry.SheafOfModules.stalkShortComplex X.ringCatSheaf T x).g) :=
    (AddCommGrpCat.mono_iff_injective _).mp
      (((AlgebraicGeometry.SheafOfModules.stalkShortComplex X.ringCatSheaf T x).exact_iff_mono
        hUf).1 hU)
  obtain ⟨a, ha⟩ := hx
  exact ⟨_, fun h => ha (hinj (h.trans (map_zero _).symm))⟩

/-- **The support of the middle term of a short exact sequence lies in the union of the supports
of the outer terms.** The sequence of stalks at a point is exact, so a stalk of the middle term
killed in the third term comes from the first. -/
theorem supp_subset_union_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    SheafOfModules.supp S.X₂ ⊆ SheafOfModules.supp S.X₁ ∪ SheafOfModules.supp S.X₃ := by
  intro x hx
  by_contra hxU
  have hex := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    X.ringCatSheaf S).mp hS.exact x
  have h1 : ∀ a : (AlgebraicGeometry.SheafOfModules.stalkShortComplex X.ringCatSheaf S x).X₁,
      a = 0 := fun a => by by_contra ha; exact hxU (Or.inl ⟨a, ha⟩)
  have h3 : ∀ a : (AlgebraicGeometry.SheafOfModules.stalkShortComplex X.ringCatSheaf S x).X₃,
      a = 0 := fun a => by by_contra ha; exact hxU (Or.inr ⟨a, ha⟩)
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp hex a (h3 _)
  exact ha (hb.symm.trans (by rw [h1 b]; exact map_zero _))

/-- **Transport of relative nowhere density along an equality of ambient subsets.** The two
subsets are free variables, so the equality is discharged by `subst` here and the statement is
applied by unification, with no rewrite motive formed at the use site. -/
theorem isNowhereDense_preimage_val_congr {Y : Type*} [TopologicalSpace Y] {S S' : Set Y}
    (h : S = S') {T : Set Y}
    (hnd : IsNowhereDense ((Subtype.val : ↥S → Y) ⁻¹' T)) :
    IsNowhereDense ((Subtype.val : ↥S' → Y) ⁻¹' T) := by
  subst h; exact hnd

/-- `𝒜 ⊞ ℬ` at the declared type `X.Modules`. The unascribed biproduct cannot be elaborated
against the module argument of `SheafOfModules.supp`, whose sheaf of rings is implicit: instance
search is syntactic and `HasBinaryBiproduct` is not found while that implicit is a metavariable.
Compare `AlgebraicGeometry.tensorModules`. -/
noncomputable abbrev biprodModules {X : Scheme.{u}} (A B : X.Modules) : X.Modules := A ⊞ B

/-- **The support of a biproduct lies in the union of the supports**, by
`AlgebraicGeometry.supp_subset_union_of_shortExact` applied to the split short exact sequence
`0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0`. -/
theorem supp_biprodModules_subset {X : Scheme.{u}} (A B : X.Modules) :
    SheafOfModules.supp (biprodModules A B) ⊆
      SheafOfModules.supp A ∪ SheafOfModules.supp B :=
  supp_subset_union_of_shortExact (biprodShortComplex A B)
    (biprodShortComplexSplitting A B).shortExact

/-- Coherence of a biproduct, with the coherence of the summands taken as explicit arguments. -/
theorem isCoherent_biprodModules {X : Scheme.{u}} (A B : X.Modules)
    (hA : SheafOfModules.IsCoherent A) (hB : SheafOfModules.IsCoherent B) :
    SheafOfModules.IsCoherent (biprodModules A B) :=
  SheafOfModules.isCoherent_biprod A B hA hB

/-! ### The inductive step, and the removal of embedded associated points -/

/-- The biproduct of two sheaves supported on nowhere dense parts of `Supp G` is again so. -/
private theorem supp_biprodModules_subset_and_isNowhereDense {X : Scheme.{u}}
    {G A B : X.Modules} (hA : SheafOfModules.supp A ⊆ SheafOfModules.supp G)
    (hB : SheafOfModules.supp B ⊆ SheafOfModules.supp G)
    (hndA : IsNowhereDense ((Subtype.val : SheafOfModules.supp G → X) ⁻¹' SheafOfModules.supp A))
    (hndB : IsNowhereDense ((Subtype.val : SheafOfModules.supp G → X) ⁻¹' SheafOfModules.supp B)) :
    SheafOfModules.supp (biprodModules A B) ⊆ SheafOfModules.supp G ∧
      IsNowhereDense ((Subtype.val : SheafOfModules.supp G → X) ⁻¹'
        SheafOfModules.supp (biprodModules A B)) :=
  ⟨(supp_biprodModules_subset A B).trans (Set.union_subset hA hB),
    (hndA.union hndB).mono (by
      rw [← Set.preimage_union]; exact Set.preimage_mono (supp_biprodModules_subset A B))⟩

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {r : ℕ}
  (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **Additivity of the Euler characteristic of twists over a biproduct**, given
[Stacks, Tag 02O6]. This is
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_add_of_shortExact` at the split sequence
`0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0`; it is what merges a four-term combination of Euler characteristics
into a difference of two. -/
theorem eulerCharacteristic_twistedSheaf_biprodModules [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (A B : X.Modules) (hA : SheafOfModules.IsCoherent A) (hB : SheafOfModules.IsCoherent B)
    (n : Fin r → ℤ) :
    @eulerCharacteristic k _ X f _ (twistedSheaf (biprodModules A B) L n)
        (@twistedSheaf_isCoherent X r _ L _ (isCoherent_biprodModules A B hA hB) n)
      = @eulerCharacteristic k _ X f _ (twistedSheaf A L n)
          (@twistedSheaf_isCoherent X r A L _ hA n)
        + @eulerCharacteristic k _ X f _ (twistedSheaf B L n)
            (@twistedSheaf_isCoherent X r B L _ hB n) :=
  eulerCharacteristic_twistedSheaf_add_of_shortExact k f L hfin
    (biprodShortComplexSplitting A B).shortExact hA (isCoherent_biprodModules A B hA hB) hB n

/-- **The inductive step of [Stacks, Tag 0BEM], restricted to the coherent sheaves satisfying
`P`, with the support-dimension drops in their nowhere-dense form.** For a coherent `𝒢` with `P`
and positive-dimensional support, and each twisting direction `i`, two coherent sheaves
supported on a nowhere dense closed part of `Supp 𝒢` whose twisted Euler characteristics compute
the first difference of those of `𝒢` in the direction `i`.

Taking `P` to be `fun _ => True` this is the hypothesis `hstep` of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep` with its two strict
`AlgebraicGeometry.natDimSupp` inequalities strengthened to relative nowhere density; see the
module docstring for why the nowhere-dense form is the one carried. -/
def IsTwistDifferenceStep [IsProper f] (P : X.Modules → Prop) : Prop :=
  ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), P G → natDimSupp G ≠ 0 →
    ∀ i : Fin r,
    ∃ (G₁ G₂ : X.Modules) (hG₁ : SheafOfModules.IsCoherent G₁)
      (hG₂ : SheafOfModules.IsCoherent G₂),
      SheafOfModules.supp G₁ ⊆ SheafOfModules.supp G ∧
      IsNowhereDense ((Subtype.val : SheafOfModules.supp G → X) ⁻¹'
        SheafOfModules.supp G₁) ∧
      SheafOfModules.supp G₂ ⊆ SheafOfModules.supp G ∧
      IsNowhereDense ((Subtype.val : SheafOfModules.supp G → X) ⁻¹'
        SheafOfModules.supp G₂) ∧
      ∀ n : Fin r → ℤ,
        (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
            (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
          - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
              (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
          = (@eulerCharacteristic k _ X f _ (twistedSheaf G₁ L n)
              (@twistedSheaf_isCoherent X r G₁ L _ hG₁ n) : ℚ)
            - (@eulerCharacteristic k _ X f _ (twistedSheaf G₂ L n)
                (@twistedSheaf_isCoherent X r G₂ L _ hG₂ n) : ℚ)

open Stacks.AlgebraicGeometry.CoherentSubquotients in
/-- **The removal of embedded associated points, at the level of the inductive step of
[Stacks, Tag 0BEM].** Given the step for every coherent sheaf with no embedded associated
points, it holds for every coherent sheaf.

This is the source's first paragraph. [Stacks, Tag 02OL] supplies the greatest coherent subsheaf
`𝒦 ⊆ 𝒢` with support nowhere dense in `Supp 𝒢`, and the quotient `𝒬 = 𝒢/𝒦` has `Supp 𝒬 = Supp 𝒢`
and no embedded associated points. Additivity along `0 ⟶ 𝒦 ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` at the exponent vectors
`n` and `n + eᵢ`, together with
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_update_eq` for `𝒦`, writes the first
difference of `𝒢` as `χ(𝒦 ⊗ 𝓛ᵢ ⊗ twist) + χ(𝒬₁ ⊗ twist) - χ(𝒦 ⊗ twist) - χ(𝒬₂ ⊗ twist)`, and
the two biproducts `(𝒦 ⊗ 𝓛ᵢ) ⊞ 𝒬₁` and `𝒦 ⊞ 𝒬₂` turn that into a difference of two. Their
supports are nowhere dense in `Supp 𝒢` because nowhere density is stable under finite unions,
and `Supp (𝒦 ⊗ 𝓛ᵢ) ⊆ Supp 𝒦`.

**A side condition on the sheaf is carried through, provided it depends only on the support.**
The reduction replaces `𝒢` by `𝒬 = 𝒢/𝒦`, and the only thing it knows about `𝒬` besides its
coherence and its lack of embedded associated points is that `Supp 𝒬 = Supp 𝒢`. So any predicate
`Q` determined by the support — `hQ` is that hypothesis — survives the replacement, and the step
for `Q`-sheaves follows from the step for `Q`-sheaves without embedded associated points. Taking
`Q = fun _ => True` gives the unconditional reduction (the `hQ` argument is then `trivial`);
taking `Q` to be *full support* is what lets the step be run on the scheme-theoretic support of
[Stacks, Tag 02OM], where that is the only hypothesis [Stacks, Tag 02P2] can be fed, and clause
(b) of Tag 02OM — blocked on [Stacks, Tag 05EY] — is not available to supply the rest. -/
theorem isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    {Q : X.Modules → Prop}
    (hQ : ∀ A B : X.Modules, SheafOfModules.supp A = SheafOfModules.supp B → Q B → Q A)
    (hstep : IsTwistDifferenceStep k f L (fun G => Q G ∧ HasNoEmbeddedAssociatedPoints G)) :
    IsTwistDifferenceStep k f L Q := by
  intro G hG hQG hG0 i
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := IsNoetherian.mk
  have : G.IsCoherent := hG
  obtain ⟨K, hK, hmax⟩ := exists_greatest_isNowhereDenseCoherentSubobject G
  have hKcoh : (K : X.Modules).IsCoherent := hK.1
  have hKnd : IsNowhereDense
      ((Subtype.val : SheafOfModules.supp G → X) ⁻¹' SheafOfModules.supp (K : X.Modules)) :=
    hK.2
  have hKsub : SheafOfModules.supp (K : X.Modules) ⊆ SheafOfModules.supp G :=
    supp_subset_of_mono K.arrow
  have hGqc : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  have hKqc : (K : X.Modules).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (K : X.Modules)).1
  have hQqc : (cokernel K.arrow).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel K.arrow
  have hQcoh : (cokernel K.arrow).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi (cokernel.π K.arrow)
  have hQsupp : SheafOfModules.supp (R := X.ringCatSheaf) (cokernel K.arrow)
      = SheafOfModules.supp (R := X.ringCatSheaf) G := supp_cokernel_eq G K hK
  have hQemb : HasNoEmbeddedAssociatedPoints (cokernel K.arrow) :=
    cokernel_hasNoEmbeddedAssociatedPoints G K hK hmax
  have hQdim : natDimSupp (cokernel K.arrow) = natDimSupp G :=
    congrArg (fun S : Set X => ((topologicalKrullDim S).unbotD 0).toNat) hQsupp
  obtain ⟨Q₁, Q₂, hQ1c, hQ2c, hs1, hnd1, hs2, hnd2, hid⟩ :=
    hstep (cokernel K.arrow) hQcoh ⟨hQ _ _ hQsupp hQG, hQemb⟩ (hQdim ▸ hG0) i
  replace hs1 : SheafOfModules.supp Q₁ ⊆ SheafOfModules.supp G := hs1.trans hQsupp.subset
  replace hs2 : SheafOfModules.supp Q₂ ⊆ SheafOfModules.supp G := hs2.trans hQsupp.subset
  replace hnd1 : IsNowhereDense
      ((Subtype.val : SheafOfModules.supp G → X) ⁻¹' SheafOfModules.supp Q₁) :=
    isNowhereDense_preimage_val_congr hQsupp hnd1
  replace hnd2 : IsNowhereDense
      ((Subtype.val : SheafOfModules.supp G → X) ⁻¹' SheafOfModules.supp Q₂) :=
    isNowhereDense_preimage_val_congr hQsupp hnd2
  set KL : X.Modules := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.2)⟩).obj ((K : X.Modules))).obj ((L i))) with hKL
  have hKLc : KL.IsCoherent := isCoherent_tensorSheaf_invertible L (K : X.Modules) hKcoh i
  have hKLsub : SheafOfModules.supp KL ⊆ SheafOfModules.supp (K : X.Modules) := fun y hy => by
    by_contra hyK
    exact notMem_supp_tensorSheaf_of_notMem_supp (K : X.Modules) (L i) hyK hy
  obtain ⟨hsub1, hndb1⟩ := supp_biprodModules_subset_and_isNowhereDense
    (hKLsub.trans hKsub) hs1 (.mono (Set.preimage_mono hKLsub) hKnd) hnd1
  obtain ⟨hsub2, hndb2⟩ := supp_biprodModules_subset_and_isNowhereDense hKsub hs2 hKnd hnd2
  refine ⟨biprodModules KL Q₁, biprodModules (K : X.Modules) Q₂,
    isCoherent_biprodModules _ _ hKLc hQ1c, isCoherent_biprodModules _ _ hKcoh hQ2c,
    hsub1, hndb1, hsub2, hndb2, fun n => ?_⟩
  have hSES : (ShortComplex.mk K.arrow (cokernel.π K.arrow)
      (cokernel.condition _)).ShortExact := ShortComplex.shortExact_mk_cokernel_π _
  have addU := eulerCharacteristic_twistedSheaf_add_of_shortExact k f L hfin hSES
    hKcoh hG hQcoh (Function.update n i (n i + 1))
  have addN := eulerCharacteristic_twistedSheaf_add_of_shortExact k f L hfin hSES
    hKcoh hG hQcoh n
  have updK := eulerCharacteristic_twistedSheaf_update_eq k f L (K : X.Modules) hKcoh n i
  have b1 := eulerCharacteristic_twistedSheaf_biprodModules k f L hfin KL Q₁ hKLc hQ1c n
  have b2 := eulerCharacteristic_twistedSheaf_biprodModules k f L hfin
    (K : X.Modules) Q₂ hKcoh hQ2c n
  have hid' := hid n
  norm_cast at hid' ⊢
  linarith

/-- **[Stacks, Tag 0BEM] from the nowhere-dense form of its inductive step.** This is
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep` with each relative nowhere
density converted to a strict drop of `AlgebraicGeometry.natDimSupp` by
`AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense`. The Noetherian hypothesis that
conversion asks for is not asked of the caller: a scheme proper over a field is locally of
finite type over a Noetherian base and quasi-compact. -/
theorem exists_eulerPolynomial_twistedSheaf_of_isTwistDifferenceStep [IsProper f]
    (hstep : IsTwistDifferenceStep k f L (fun _ => True))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := IsNoetherian.mk
  refine exists_eulerPolynomial_twistedSheaf_of_hstep k f L ?_ F hF
  intro G hG hG0 i
  obtain ⟨G₁, G₂, h1, h2, hs1, hnd1, hs2, hnd2, hid⟩ := hstep G hG trivial hG0 i
  exact ⟨G₁, G₂, h1, h2,
    natDimSupp_lt_natDimSupp_of_isNowhereDense k f G G₁ h1 hs1 hnd1 hG0,
    natDimSupp_lt_natDimSupp_of_isNowhereDense k f G G₂ h2 hs2 hnd2 hG0, hid⟩

/-- **[Stacks, Tag 0BEM] from [Stacks, Tag 02O6] and the inductive step for coherent sheaves
with no embedded associated points.** The Euler characteristics of the twists
`ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a proper scheme over a field are the
values of a rational polynomial which is zero or of total degree at most `dim Supp ℱ`.

The sheaf `ℱ` itself is arbitrary: the restriction to sheaves without embedded associated points
is on the *hypothesis*, and is discharged by
`AlgebraicGeometry.isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints` at the trivial side
condition `Q = fun _ => True`, whose support-invariance is `trivial`. -/
theorem exists_eulerPolynomial_twistedSheaf_of_hasNoEmbeddedAssociatedPointsStep [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (hstep : IsTwistDifferenceStep k f L HasNoEmbeddedAssociatedPoints)
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) := by
  refine exists_eulerPolynomial_twistedSheaf_of_isTwistDifferenceStep k f L
    (isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints k f L hfin
      (Q := fun _ => True) (fun _ _ _ _ => trivial) ?_) F hF
  intro G hG h hG0 i
  exact hstep G hG h.2 hG0 i

end

end AlgebraicGeometry

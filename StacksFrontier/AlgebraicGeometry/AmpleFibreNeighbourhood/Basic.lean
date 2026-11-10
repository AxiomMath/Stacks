module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FiniteFibreVanishing
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative ampleness from a finite morphism to projective space, and finiteness near a fibre

The proof of [Stacks, Tag 0D2N] — an invertible module ample on one fibre of a proper morphism
onto a Noetherian base is relatively ample over a neighbourhood of that point — runs in two
halves. The first produces, after shrinking the base, a morphism `φ : X ⟶ ℙⁿ_V` over `V` with
`ℒ ^⊗ d ≅ φ^* 𝒪(1)`; the second turns that into relative ampleness. This file is the second
half, together with the step the source calls "a sleight of hand" that makes `φ` finite.

## Main results

* `Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom`: **the
  relative form of [Stacks, Tag 0B3E] for an affine morphism.** If `M` is ample relative to
  `p : P ⟶ V` and `g : X ⟶ P` is an affine morphism, then `g^* M` is ample relative to
  `g ≫ p`.
* `Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver`: the
  second half of [Stacks, Tag 0D2N]. If `f : X ⟶ V` factors as an **affine** morphism
  `φ : X ⟶ ℙⁿ_V` followed by the structure morphism, and some positive tensor power of `ℒ` is
  isomorphic to `φ^* 𝒪(1)`, then `ℒ` is ample relative to `f`.
* `Stacks.AmpleFibreNeighbourhood.exists_isFinite_morphismRestrict_preimage`: the sleight of
  hand. A proper `g : W ⟶ P` whose set-theoretic fibres are finite at every point of one fibre
  of a universally closed `p : P ⟶ V` is finite over the preimage of an open neighbourhood of
  that point of `V`.
* `Stacks.AmpleFibreNeighbourhood.exists_mem_and_preimage_subset`: the step the source performs
  with "since `X ⟶ Y` is closed we can find an open `V ⊆ Y`" — an open set containing a whole
  fibre of a universally closed morphism contains the preimage of an open neighbourhood of the
  point.
* `Stacks.AmpleFibreNeighbourhood.morphismRestrict_of_le`: a property local on the target,
  known for the restriction of a morphism over an open, holds for the restriction over a
  smaller open.

## The route

Relative ampleness of `𝒪(1)` on `ℙⁿ_V ⟶ V` over an arbitrary base is already in the repository,
as `Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf`. What is added here is
the pullback step for an **affine** morphism: [Stacks, Tag 0892] part (2) is available only
absolutely, as `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`, and the relative
statement is that applied over the preimage of each affine open `W ⊆ V`, where the restricted
morphism `g ∣_ (p⁻¹W)` is again affine because affine morphisms are stable under base change.
The module on `g⁻¹(p⁻¹W)` is the pullback of `M` along the two equal composites into `P`, which
is why `Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso` and `pullbackModuleCongr` appear.
Passing from the power `ℒ ^⊗ d` back to `ℒ` is [Stacks, Tag 02NN] in the form
`Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule`.

The sleight of hand is [Stacks, Tag 02OH]
(`Stacks.FormalFunctions.exists_isFinite_morphismRestrict_of_finite_fibre`) applied at every
point of the fibre `p⁻¹(v)` at once: the opens it produces cover `p⁻¹(v)`, their union `Ω` has
closed complement, `p` carries that complement to a closed set missing `v`, and the complement
of *that* is the open `V' ⊆ V` wanted. Finiteness over `p⁻¹V'` is then read off the covering of
`p⁻¹V'` by the pieces `p⁻¹V' ⊓ Ωᵢ`, finiteness being Zariski local on the target.

## Where [Stacks, Tag 0D2N] is proved, and what this file contributes

This file does not state [Stacks, Tag 0D2N] and carries no `@[stacks 0D2N]` attribute; the tag is
proved and registered as
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`
(`AmpleFibreNeighbourhood/RelativelyAmpleNeighbourhood.lean`).  What this file contributes to that
proof is the second half of the source's argument, in the two forms above: the shrinking of the
base around a whole fibre (`exists_mem_and_preimage_subset`), the finiteness of the morphism to
projective space over a neighbourhood of the fibre
(`exists_isFinite_morphismRestrict_preimage`), and the passage from there to relative ampleness
(`isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver`).

The first half — the production of the sections, where [Stacks, Tag 0D2M] enters — is
`Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_fiberι_eq`
(`AmpleFibreNeighbourhood/FibreSectionLift.lean`), and the assembly of the two halves is
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_exists_lift`
(`AmpleFibreNeighbourhood/NeighbourhoodAssembly.lean`).

Tag 0D2N appeals to [Stacks, Tag 0D2M] exactly once, and only for its surjectivity assertion:
`f_*(ℱ ⊗ ℒ ^⊗ d)_y ⟶ H⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` for `d` large, which is what lets the sections
defining the immersion `X_y ⟶ ℙⁿ_{κ(y)}` be lifted to a neighbourhood.  The vanishing assertion,
`R ᵖ f_* = 0` in positive degrees, is not used by Tag 0D2N at all.  Both assertions are
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist`, which
carries the project's `@[stacks 0D2M]`.

Over a local base the surjectivity reduces, by the dévissage along
`0 → 𝔪 ⁿ ℱ(d) / 𝔪 ⁿ⁺¹ ℱ(d) → ℱ(d) / 𝔪 ⁿ⁺¹ ℱ(d) → ℱ(d) / 𝔪 ⁿ ℱ(d) → 0`, to the vanishing of
`H¹` of the graded pieces **with one exponent `d₀` serving every `n` at once** — part (2) of
[Stacks, Tag 0897] applied on `X_y` to `⨁ₙ 𝔪 ⁿ ℱ / 𝔪 ⁿ⁺¹ ℱ` over the associated graded algebra of
`𝔪`.  That uniformity is the whole content, and it is now proved, as
`Stacks.GradedProperCohomology.exists_isZero_rightDerived_kernelIdealPowerQuotientDropTwist`
(`../GradedProperCohomology/FibreLayerVanishing.lean`).

**Serre vanishing does not substitute for it, and that is worth keeping on record.**
`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`, clause (4)
of [Stacks, Tag 0B5T], is unconditional and does apply on the fibre, `X_y` being proper over the
Noetherian ring `κ(y)` with `ℒ_y` ample.  But its exponent is quantified *after* the coherent
module — `∀ ℱ, ∃ d₀, ∀ d p` — so at the graded piece `𝔪 ⁿ ℱ / 𝔪 ⁿ⁺¹ ℱ` it yields `d₀(n)`, while
the dévissage consumes every `n` with one `d₀`.  Uniformity in `p`, which that statement does
have, is not the uniformity needed.  Taking only finitely many `n` does not escape either: the
route uses the tower up to `n = c + 1` where `c` is the Artin--Rees bound of [Stacks, Tag 02OB]
clause (1) for the twist `ℱ(d)`, so `c` depends on `d` and the choice of `d` would have to
precede itself.  This is why the proof goes through [Stacks, Tag 0897].

**Choosing the neighbourhood first would not have helped either.** The lifting is a statement
about the stalk `(f_* ℒ ^⊗ d)_y`, which is the colimit of `Γ(f⁻¹V, ℒ ^⊗ d)` over all `V ∋ y`;
shrinking `V` only shrinks the source of the map that has to be surjective.  The order of the two
choices is not a degree of freedom, and the proof instead reduces the base to `Spec 𝒪_{S, y}` by
flat base change, as the source does.

**Why the associated graded and not the Rees algebra.** The engine of [Stacks, Tag 0897] part (2)
needs ampleness upstairs on the relative spectrum of the graded algebra, and Tag 0D2N grants
ampleness only on the fibre.  Over the Rees algebra `⨁ₙ 𝔪 ⁿ` the structure morphism does not kill
`𝔪`, so its relative spectrum does not factor through `X_y` and the ampleness is unavailable;
assuming `ℒ` ample on `X` instead would make the tag vacuous.  Over the associated graded
`⨁ₙ 𝔪 ⁿ / 𝔪 ⁿ⁺¹` the structure morphism `𝒪_X ⟶ 𝓑` kills `𝔪 𝒪_X`, so the relative spectrum
factors through the fibre and [Stacks, Tag 0892] part (2) for an affine morphism supplies the
ampleness from `ℒ_y` alone.  The graded pieces are also the only members of the filtration that
live on the fibre, which is the only place ampleness is available — so the associated graded is
forced, not convenient.

## Implementation notes

`AlgebraicGeometry.IsZariskiLocalAtTarget @IsFinite` is not found by instance search at this
pin — the instance it would come from is declared under a relaxed `backward.isDefEq`
transparency — so the repository's named form
`Stacks.Morphisms.isFinite_isZariskiLocalAtTarget` is supplied by hand, as
`../Curves/GenusCurve/BirationalGenus.lean` does. No compiler option is relaxed here.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 02NN](https://stacks.math.columbia.edu/tag/02NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleProjectiveImmersion
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-! ### The relative form of Stacks Tag 0B3E for an affine morphism -/

/-- **The pullback of a relatively ample module along an affine morphism is relatively ample.**
If `M` is ample relative to `p : P ⟶ V` and `g : X ⟶ P` is affine, then `g^* M` is ample
relative to the composite `g ≫ p`.

Over an affine open `W ⊆ V` the restriction `g ∣_ (p⁻¹W)` is affine, being a base change of `g`,
so [Stacks, Tag 0892] part (2) in its absolute form
`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom` turns ampleness of `M|_{p⁻¹W}` into
ampleness of its pullback. That pullback and the restriction of `g^* M` to `(g ≫ p)⁻¹W` are
pullbacks of `M` along the two sides of `morphismRestrict_ι`, hence isomorphic. -/
@[ega "III 2.6.2.1" "more general"]
theorem isRelativelyAmple_pullbackModule_of_isAffineHom {X P V : Scheme.{u}} (g : X ⟶ P)
    [IsAffineHom g] (p : P ⟶ V) (M : P.Modules) [IsInvertibleModule P M]
    (h : Stacks.RelativeAmple.IsRelativelyAmple p M) :
    Stacks.RelativeAmple.IsRelativelyAmple (g ≫ p) (pullbackModule g M) := by
  have hp : QuasiCompact p := h.1
  have := hp
  refine ⟨inferInstance, fun W hW => ?_⟩
  have : IsAffineHom (g ∣_ (p ⁻¹ᵁ W)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (isPullback_morphismRestrict g (p ⁻¹ᵁ W)).flip inferInstance
  have key := Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom
    (g ∣_ (p ⁻¹ᵁ W)) (pullbackModule (p ⁻¹ᵁ W).ι M) (h.2 W hW)
  change Stacks.Ample.IsAmple (g ⁻¹ᵁ (p ⁻¹ᵁ W)).toScheme
    (pullbackModule (g ⁻¹ᵁ (p ⁻¹ᵁ W)).ι (pullbackModule g M))
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mp key
  exact (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (g ∣_ (p ⁻¹ᵁ W)) (p ⁻¹ᵁ W).ι M).symm
    ≪≫ Stacks.RelativeAmpleBaseChange.pullbackModuleCongr (morphismRestrict_ι g (p ⁻¹ᵁ W)) M
    ≪≫ Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (g ⁻¹ᵁ (p ⁻¹ᵁ W)).ι g M

/-! ### The second half of Stacks Tag 0D2N -/

/-- **An invertible module a positive power of which is the pullback of `𝒪(1)` along an affine
morphism to projective space over the base is relatively ample.** Let `f : X ⟶ V` factor as
`φ : X ⟶ ℙⁿ_V` followed by the structure morphism of `ℙⁿ_V`, with `φ` affine, and let
`ℒ ^⊗ d ≅ φ^* 𝒪(1)` for some `d ≥ 1`. Then `ℒ` is ample relative to `f`.

`𝒪(1)` is ample relative to `ℙⁿ_V ⟶ V` over any base by
`Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf`;
`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom` pulls that back
along `φ`; ampleness is an invariant of the isomorphism class
(`Stacks.RelativeVeryAmple.isRelativelyAmple_congr`); and [Stacks, Tag 02NN] descends from the
power to `ℒ`.

This is the second half of the proof of [Stacks, Tag 0D2N]: there `φ` is finite — in particular
affine — by the sleight of hand of
`Stacks.AmpleFibreNeighbourhood.exists_isFinite_morphismRestrict_preimage`. -/
theorem isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver {X V : Scheme.{u}} {f : X ⟶ V}
    (L : X.Modules) [IsInvertibleModule X L] {n d : ℕ} (hd : 1 ≤ d)
    (φ : X ⟶ projectiveSpaceOver n V) [IsAffineHom φ]
    (hφ : φ ≫ (projectiveSpaceOver n V ↘ V) = f)
    (e : tensorPowModule X L (d : ℤ) ≅ pullbackModule φ (projectiveSpaceTwistingSheaf n V)) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  have h1 := isRelativelyAmple_pullbackModule_of_isAffineHom φ (projectiveSpaceOver n V ↘ V)
    (projectiveSpaceTwistingSheaf n V)
    (Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf n V)
  rw [hφ] at h1
  exact Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule f L d hd
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr f _ _ e).mpr h1)

/-! ### Finiteness over a neighbourhood of a whole fibre -/

/-- **An open set containing a whole fibre contains the preimage of a neighbourhood of the
point.** Let `p : Z ⟶ V` be universally closed, `v : V`, and `Ω ⊆ Z` open with
`p⁻¹(v) ⊆ Ω`. Then `v` has an open neighbourhood `V' ⊆ V` with `p⁻¹(V') ⊆ Ω`.

`p` carries the closed set `Ωᶜ` to a closed subset of `V`, which misses `v` precisely because
`Ω` contains the whole fibre; `V'` is its complement. This is the sentence "because `X ⟶ Y` is
closed we can find an open neighbourhood `V` of `y` such that `f⁻¹(V) ⊆ U`" of the proof of
[Stacks, Tag 0D2N], and the same step shrinks the base in the proof of
`Stacks.AmpleFibreNeighbourhood.exists_isFinite_morphismRestrict_preimage` below. -/
theorem exists_mem_and_preimage_subset {Z V : Scheme.{u}} (p : Z ⟶ V) [UniversallyClosed p]
    (v : V) {Ω : Set Z} (hΩ : IsOpen Ω) (hsub : p.base ⁻¹' {v} ⊆ Ω) :
    ∃ V' : V.Opens, v ∈ V' ∧ ((p ⁻¹ᵁ V' : Z.Opens) : Set Z) ⊆ Ω := by
  refine ⟨⟨(p.base '' Ωᶜ)ᶜ, (p.isClosedMap _ hΩ.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz (hsub rfl)
  · intro z hz
    by_contra hzΩ
    exact hz ⟨z, hzΩ, rfl⟩

/-- Restricting `g ∣_ U` over `U.ι⁻¹U'` is, as an arrow, restricting `g` over `U ⊓ U'`. -/
private theorem morphismRestrict_restrict_iff {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {A B : Scheme.{u}} (g : A ⟶ B) (U U' : B.Opens) :
    P ((g ∣_ U) ∣_ (U.ι ⁻¹ᵁ U')) ↔ P (g ∣_ (U ⊓ U')) := by
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ U') = U ⊓ U' := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact MorphismProperty.arrow_mk_iso_iff P
    (morphismRestrictRestrict g U (U.ι ⁻¹ᵁ U') ≪≫ morphismRestrictEq g heq)

/-- **A property local on the target passes to the restriction over a smaller open.** If `P` is
Zariski local on the target and holds for `g ∣_ U`, then it holds for `g ∣_ U'` whenever
`U' ≤ U`: the restriction of `g ∣_ U` over `U.ι⁻¹U'` is, as an arrow, `g ∣_ U'`. -/
theorem morphismRestrict_of_le {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {A B : Scheme.{u}} (g : A ⟶ B) {U U' : B.Opens} (hle : U' ≤ U) (hU : P (g ∣_ U)) :
    P (g ∣_ U') := by
  have h1 := (morphismRestrict_restrict_iff (P := P) g U U').mp
    (IsZariskiLocalAtTarget.restrict hU _)
  rwa [inf_eq_right.mpr hle] at h1

/-- **[Stacks, Tag 02OH] along a whole fibre.** Let `g : W ⟶ P` be proper with `P` locally
Noetherian, let `p : P ⟶ V` be universally closed and let `v : V`. If the set-theoretic fibre of
`g` is finite over every point of `p⁻¹(v)`, then `v` has an open neighbourhood `V' ⊆ V` over
whose preimage `g` is finite.

This is the step the proof of [Stacks, Tag 0D2N] calls a sleight of hand. Tag 02OH
(`Stacks.FormalFunctions.exists_isFinite_morphismRestrict_of_finite_fibre`) gives, at each point
`z` of the fibre, an open `Ω_z ∋ z` with `g ∣_ Ω_z` finite. Their union `Ω` contains `p⁻¹(v)`,
so `p` carries the closed set `Ωᶜ` to a closed set of `V` missing `v`, and `V'` is its
complement. The preimage `p⁻¹V'` lies inside `Ω`, so it is covered by the opens
`p⁻¹V' ⊓ Ω_z`, over each of which `g` is finite by
`Stacks.AmpleFibreNeighbourhood.morphismRestrict_of_le`; finiteness is Zariski local on the
target. -/
@[ega "III 4.8.11" "ordinary schemes"]
theorem exists_isFinite_morphismRestrict_preimage {W P V : Scheme.{u}} (g : W ⟶ P) (p : P ⟶ V)
    [IsProper g] [IsLocallyNoetherian P] [UniversallyClosed p] (v : V)
    (hfin : ∀ z : P, p z = v → (g ⁻¹' {z}).Finite) :
    ∃ V' : V.Opens, v ∈ V' ∧ IsFinite (g ∣_ (p ⁻¹ᵁ V')) := by
  classical
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  choose! U hUmem hUfin using fun (z : P) (hz : p z = v) =>
    Stacks.FormalFunctions.exists_isFinite_morphismRestrict_of_finite_fibre g z (hfin z hz)
  set Ω : Set P := ⋃ z ∈ p.base ⁻¹' {v}, (U z : Set P) with hΩ
  have hΩopen : IsOpen Ω := isOpen_biUnion fun z _ => (U z).isOpen
  have hfibre : p.base ⁻¹' {v} ⊆ Ω := fun z hz =>
    Set.mem_biUnion hz (hUmem z (Set.mem_singleton_iff.mp hz))
  obtain ⟨V', hvV', hsub⟩ := exists_mem_and_preimage_subset p v hΩopen hfibre
  refine ⟨V', hvV', ?_⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  have hxmem : ((p ⁻¹ᵁ V').ι x : P) ∈ ((p ⁻¹ᵁ V' : P.Opens) : Set P) := by
    have hr : ((p ⁻¹ᵁ V').ι x : P) ∈ (((p ⁻¹ᵁ V').ι.opensRange : P.Opens) : Set P) := ⟨x, rfl⟩
    rwa [Scheme.Opens.opensRange_ι] at hr
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hsub hxmem)
  refine ⟨(p ⁻¹ᵁ V').ι ⁻¹ᵁ U z, hxz, ?_⟩
  have hfin' : IsFinite (g ∣_ ((p ⁻¹ᵁ V') ⊓ U z)) :=
    morphismRestrict_of_le g inf_le_right (hUfin z hz)
  exact (morphismRestrict_restrict_iff g (p ⁻¹ᵁ V') (U z)).mpr hfin'

end Stacks.AmpleFibreNeighbourhood

end

module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Route2Assembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageStep
public import StacksFrontier.AlgebraicGeometry.RestrictIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The condition `hc` of Stacks 088B is the source's own hypothesis

`CompletionProper/Route2Assembly.lean` reduces [Stacks, Tag 088C], the binder `hDev` of [Stacks,
Tag 088E] and [Stacks, Tag 088E] itself to the single hypothesis
`Stacks.Algebraization.HasAdicBaseChangeUnitCondition` — the condition the source calls `hc`,
quantified over the data of the glueing and over the affine opens of the base. The docstring of
that definition names the two things standing between it and the source's own hypothesis
`IsIso (π ∣_ 𝒦.support.compl)`, which is **already an antecedent of the condition itself**:

1. the transport of `IsIso (π ∣_ 𝒦.support.compl)` to the base change along
   `Stacks.Algebraization.adicCompletionSpecMap`, and
2. the identification of the support of an inverse-image ideal sheaf.

This file does both, and so **proves the condition outright**. Nothing is assumed: the
isomorphism hypothesis the condition carries in its own statement is exactly what the two steps
consume.

## The chain

Write `B = Γ(X, V)` for an affine open `V ⊆ X`, `e = V.2.isoSpec : V ≅ Spec B`,
`π₀ = (π ∣_ V) ≫ e.hom : π ⁻¹ V ⟶ Spec B` and `g = Spec (B ^∧) ⟶ Spec B`. The condition asks
that the unit of `π'^* ⊣ π'_*`, for `π' = π₀ ×_{Spec B} Spec (B ^∧)`, restrict to an isomorphism
over the complement of the support of `((𝒦|_V) ⁻¹ along e.inv) ⁻¹ along g`. By
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`, which is
unconditional, it is enough that `π'` be an isomorphism over that open. The four steps:

* **the support of an inverse image.** `(ℐ ⁻¹ along h).support.compl = h ⁻¹ (ℐ.support.compl)`,
  `Stacks.Algebraization.support_compl_comap_eq_preimage`: the support of the inverse image is the
  preimage of the support (`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`), and taking
  complements commutes with preimages. Applied three times — at `V.ι`, at `e.inv` and at `g` —
  it turns the whole tower of `comap`s in the condition into one preimage of
  `𝒦.support.compl`.
* **down to the affine open.** `IsIso (π ∣_ Ω)` gives `IsIso (π ∣_ V ∣_ (V.ι ⁻¹ Ω))`,
  `Stacks.Algebraization.isIso_morphismRestrict_restrict_preimage`: the double restriction is the
  single restriction to `V.ι ''ᵁ (V.ι ⁻¹ Ω) = V ⊓ Ω` (`AlgebraicGeometry.morphismRestrictRestrict`)
  and `IsIso (π ∣_ ·)` descends to smaller opens
  (`Stacks.RestrictIso.isIso_morphismRestrict_of_le`).
* **across `e`.** `π₀ ∣_ (e.inv ⁻¹ Ω) = (π ∣_ V ∣_ Ω) ≫ (e.hom ∣_ (e.inv ⁻¹ Ω))` by
  `AlgebraicGeometry.morphismRestrict_comp`, because `e.hom ⁻¹ (e.inv ⁻¹ Ω) = Ω`; the second
  factor is an isomorphism because `e.hom` is.
* **to the base change.** `IsIso (pullback.snd f g ∣_ (𝒦 ⁻¹ along g).support.compl)`,
  `Stacks.Algebraization.isIso_morphismRestrict_pullbackSnd_comap`: the base change of `f` over
  `g ⁻¹ Ω` is the base change of `f ∣_ Ω` along `g ∣_ Ω`, by pasting the cartesian square of
  `AlgebraicGeometry.isPullback_morphismRestrict` onto the defining square of the base change and
  splitting off the cartesian square of `f ∣_ Ω`; a base change of an isomorphism is an
  isomorphism. **No flatness, affineness or quasi-coherence enters**, and `g` is an arbitrary
  morphism — the completion map plays no part.

## Main results

* `Stacks.Algebraization.isIso_morphismRestrict_pullbackSnd_comap` — step 1 of the docstring of
  `Stacks.Algebraization.HasAdicBaseChangeUnitCondition`, at an arbitrary base change.
* `Stacks.Algebraization.support_compl_comap_eq_preimage` — step 2.
* `Stacks.Algebraization.isIso_morphismRestrict_isoSpec_hom_comp_comap` — the two steps combined
  at one affine open of the base: `π₀` is an isomorphism over the complement of the support of
  the inverse image of `𝒦` on `Spec Γ(X, V)`.
* `Stacks.Algebraization.hasAdicBaseChangeUnitCondition` —
  **`Stacks.Algebraization.HasAdicBaseChangeUnitCondition` holds, with no hypothesis.**
* `Stacks.Algebraization.isDirectImageComparison_holds` — [Stacks, Tag 088B] at a general base,
  in the form Stacks 088C consumes, with no hypothesis.
* `Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds` — [Stacks, Tag 088E],
  Grothendieck's existence theorem with proper support, with no hypothesis.

## Implementation notes

**Why the condition is not stronger than the source's hypothesis.**
`HasAdicBaseChangeUnitCondition` quantifies over all of `π`, `𝒥`, `𝒦`, `(𝒢_n)`, `𝓕`, `β`, `V` and
`𝒜`, but `IsIso (π ∣_ 𝒦.support.compl)` sits *inside* that quantifier, as an antecedent. So the
condition is the ∀-closure of an implication whose hypothesis is the source's own, and proving it
means proving the implication for arbitrary data — which is what happens below. Neither `(𝒢_n)`,
nor `𝓕`, nor `β`, nor the algebraization isomorphism asked of `𝒜` is used: the conclusion is a
statement about the morphism `π'` alone.

**No module ever enters the geometry.** Every declaration before the last four is a statement
about morphisms of schemes and opens; the single declaration that touches
`AlgebraicGeometry.Scheme.Modules` is the final assembly, and there it does so only by applying
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`, with the
module and the open both inferred from the goal. This keeps the kernel work on the base change
to the single pullback square of
`Stacks.Algebraization.isIso_morphismRestrict_pullbackSnd_comap`.

**The one registration here is Stacks 088E.**
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds` carries
`@[stacks 088E]` at the source's hypotheses with no further input, and it is the declaration that
delivers the tag. The other forms of 088E take an input as an argument and are superseded by it:
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver`
(`GrothendieckExistenceSeparated.lean`, with `hDev`) and
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_adicBaseChangeUnitCondition`
(`Route2Assembly.lean`, with the condition `hc`). The other
results of this file carry no tag: they discharge binders. Tag 088B is registered on
`Stacks.Coherent.directImageComparison`,
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`
and `Stacks.Coherent.exists_pos_idealPowerMultiple_kernel_cokernel_eq_bot`, and tag 088C on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage` and, unconditionally, on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper`.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.Cohomology.FormalFunctions

/-! ### The support of an inverse-image ideal sheaf -/

/-- **The complement of the support of an inverse-image ideal sheaf is the preimage of the
complement of the support.** For `h : X ⟶ Y` and `ℐ ⊆ 𝒪_Y` quasi-coherent,

`(ℐ ⁻¹ along h).support.compl = h ⁻¹ (ℐ.support.compl)`.

`AlgebraicGeometry.Scheme.IdealSheafData.support_comap` says the support of the inverse image is
the preimage of the support; complementation of a closed set and preimage along a continuous map
commute on the nose, so the two opens have the same underlying set. **Unconditional.** -/
public theorem support_compl_comap_eq_preimage {X Y : Scheme.{u}} (ℐ : Y.IdealSheafData)
    (h : X ⟶ Y) : (ℐ.comap h).support.compl = h ⁻¹ᵁ ℐ.support.compl := by
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-! ### Restricting an isomorphism locus to an open of the base -/

/-- **An inverse image of an open under an isomorphism is undone by the inverse.** For an
isomorphism `e : X ≅ Y` of schemes and `Ω ⊆ X` open, `e.hom ⁻¹ (e.inv ⁻¹ Ω) = Ω`. -/
public theorem preimage_hom_preimage_inv {X Y : Scheme.{u}} (e : X ≅ Y) (Ω : X.Opens) :
    e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ Ω) = Ω := by
  rw [← Scheme.Hom.comp_preimage, e.hom_inv_id]
  simp

/-- **The isomorphism locus of a morphism restricts to the isomorphism locus of its restriction
to an open of the base.** If `f ∣_ Ω` is an isomorphism then so is `f ∣_ U ∣_ (U.ι ⁻¹ Ω)`, for
every open `U` of the target.

`AlgebraicGeometry.morphismRestrictRestrict` identifies the double restriction with the single
restriction to `U.ι ''ᵁ (U.ι ⁻¹ Ω)`, which is `U ⊓ Ω`
(`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`), and
`Stacks.RestrictIso.isIso_morphismRestrict_of_le` carries `IsIso (f ∣_ Ω)` down to the smaller
open `U ⊓ Ω`. **No hypothesis beyond `IsIso (f ∣_ Ω)`.** -/
public theorem isIso_morphismRestrict_restrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) {Ω : Y.Opens} (h : IsIso (f ∣_ Ω)) : IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ Ω)) := by
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ Ω) = U ⊓ Ω := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf]
  rw [← MorphismProperty.isomorphisms.iff,
    (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ Ω)), MorphismProperty.isomorphisms.iff, himg]
  exact Stacks.RestrictIso.isIso_morphismRestrict_of_le f inf_le_right h

/-- **`Stacks.Algebraization.isIso_morphismRestrict_restrict_preimage` with the open of `U` as a
binder.** The consumer meets the open of `U` already written as a tower of supports of
inverse-image ideal sheaves, which is `U.ι ⁻¹ (Ω)` only propositionally; rewriting that
identification into `f ∣_ U ∣_ ·` is not a legal motive, the open occurring in the *type* of the
restricted morphism. So the open and the identification are binders and the substitution happens
before anything else does. -/
public theorem isIso_morphismRestrict_restrict_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) {Ω : Y.Opens} {W : U.toScheme.Opens} (hW : U.ι ⁻¹ᵁ Ω = W)
    (h : IsIso (f ∣_ Ω)) : IsIso (f ∣_ U ∣_ W) := by
  subst hW
  exact isIso_morphismRestrict_restrict_preimage f U h

/-! ### Transporting the isomorphism locus to a base change -/

/-- **A base change is an isomorphism over the preimage of an open over which the original
morphism is one.** In a cartesian square

```
P --- p ---> X
|            |
q            f
v            v
Y' -- g ---> Y
```

if `f ∣_ Ω` is an isomorphism then so is `q ∣_ (g ⁻¹ Ω)`.

The square of `AlgebraicGeometry.isPullback_morphismRestrict` for `q` at `g ⁻¹ Ω` pasted below the
given square (`CategoryTheory.IsPullback.paste_vert`) is the cartesian square of `f` and
`(g ⁻¹ Ω).ι ≫ g = (g ∣_ Ω) ≫ Ω.ι` (`AlgebraicGeometry.morphismRestrict_ι`). Splitting off the
cartesian square of `f` at `Ω` from the bottom (`CategoryTheory.IsPullback.of_bot`) leaves
`q ∣_ (g ⁻¹ Ω)` as a base change of `f ∣_ Ω`, and a base change of an isomorphism is an
isomorphism (`CategoryTheory.IsPullback.isIso_snd_of_isIso`).

**Nothing is assumed of `g`**: no flatness, affineness or quasi-compactness, and the square is
only required to be cartesian. -/
public theorem isIso_morphismRestrict_of_isPullback {P X Y' Y : Scheme.{u}} {p : P ⟶ X}
    {q : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback p q f g) (Ω : Y.Opens)
    (hf : IsIso (f ∣_ Ω)) : IsIso (q ∣_ (g ⁻¹ᵁ Ω)) := by
  have hbase : ∀ z : P, f (p z) = g (q z) := fun z => by
    simpa using congrArg (fun m : P ⟶ Y => m.base z) sq.w
  -- the top edge of the restricted square, lifted through the open immersion `(f ⁻¹ᵁ Ω).ι`
  have hrange : Set.range ((q ⁻¹ᵁ g ⁻¹ᵁ Ω).ι ≫ p).base ⊆ Set.range (f ⁻¹ᵁ Ω).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (p ((q ⁻¹ᵁ g ⁻¹ᵁ Ω).ι x)) ∈ Ω
    rw [hbase]
    exact x.2
  let t : (q ⁻¹ᵁ g ⁻¹ᵁ Ω).toScheme ⟶ (f ⁻¹ᵁ Ω).toScheme :=
    IsOpenImmersion.lift (f ⁻¹ᵁ Ω).ι ((q ⁻¹ᵁ g ⁻¹ᵁ Ω).ι ≫ p) hrange
  have ht : t ≫ (f ⁻¹ᵁ Ω).ι = (q ⁻¹ᵁ g ⁻¹ᵁ Ω).ι ≫ p := IsOpenImmersion.lift_fac _ _ _
  -- the two squares pasted vertically, with the bottom edge split through `Ω`
  have big : IsPullback (q ∣_ g ⁻¹ᵁ Ω) ((q ⁻¹ᵁ g ⁻¹ᵁ Ω).ι ≫ p) ((g ∣_ Ω) ≫ Ω.ι) f := by
    rw [morphismRestrict_ι]
    exact (isPullback_morphismRestrict q (g ⁻¹ᵁ Ω)).paste_vert sq.flip
  have key : IsPullback (q ∣_ g ⁻¹ᵁ Ω) t (g ∣_ Ω) (f ∣_ Ω) := by
    refine IsPullback.of_bot (v₂₁ := (f ⁻¹ᵁ Ω).ι) (v₂₂ := Ω.ι) ?_ ?_
      (isPullback_morphismRestrict f Ω)
    · rwa [ht]
    · rw [← cancel_mono Ω.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
        morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, ← Category.assoc, ht,
        Category.assoc, Category.assoc, sq.w]
  exact key.flip.isIso_snd_of_isIso hf

/-- **Step 1: the isomorphism locus of a morphism transports to its base change.** For
`f : X ⟶ Y`, an arbitrary `g : Y' ⟶ Y` and `𝒦 ⊆ 𝒪_Y` quasi-coherent, if `f` is an isomorphism
over `Y ∖ V(𝒦)` then the base change `f ×_Y Y' : X ×_Y Y' ⟶ Y'` is an isomorphism over
`Y' ∖ V(𝒦 ⁻¹ along g)`.

`Stacks.Algebraization.support_compl_comap_eq_preimage` rewrites the target open as `g ⁻¹` of the
source open and `Stacks.Algebraization.isIso_morphismRestrict_of_isPullback` does the rest, read
at the standard cartesian square `CategoryTheory.IsPullback.of_hasPullback`.

This is the form the condition of Stacks 088B is asked at: there `g` is
`Stacks.Algebraization.adicCompletionSpecMap`, i.e. `Spec (B ^∧) ⟶ Spec B`, and the base change
is `Stacks.Algebraization.adicBaseChangeMap`, which is this `pullback.snd` by definition. -/
public theorem isIso_morphismRestrict_pullbackSnd_comap {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (𝒦 : Y.IdealSheafData) (hf : IsIso (f ∣_ 𝒦.support.compl)) :
    IsIso (pullback.snd f g ∣_ (𝒦.comap g).support.compl) := by
  rw [support_compl_comap_eq_preimage]
  exact isIso_morphismRestrict_of_isPullback (IsPullback.of_hasPullback f g) _ hf

/-! ### The two steps at one affine open of the base -/

/-- **The two steps at one affine open: `(π ∣_ V) ≫ e.hom` is an isomorphism over the complement
of the support of the inverse image of `𝒦` on `Spec Γ(X, V)`.** Let `π : X' ⟶ X` be a morphism of
schemes, `𝒦 ⊆ 𝒪_X` quasi-coherent, `V ⊆ X` an affine open and `e = isoSpec : V ≅ Spec Γ(X, V)`.
If `π` is an isomorphism over `X ∖ V(𝒦)`, then `(π ∣_ V) ≫ e.hom` is an isomorphism over the
complement of the support of `((𝒦|_V) ⁻¹ along e.inv)`.

`AlgebraicGeometry.morphismRestrict_comp` splits the restriction of the composite; the second
factor `e.hom ∣_ ·` is an isomorphism because `e.hom` is, and
`Stacks.Algebraization.isIso_morphismRestrict_restrict_of_eq` handles the first, its equation
binder discharged by the two supports read as preimages
(`Stacks.Algebraization.support_compl_comap_eq_preimage`, twice) followed by
`Stacks.Algebraization.preimage_hom_preimage_inv`.

**No hypothesis beyond `IsIso (π ∣_ 𝒦.support.compl)`**, which is the source's own; in
particular nothing is assumed of `V` beyond being affine, and `π` need not be proper. -/
public theorem isIso_morphismRestrict_isoSpec_hom_comp_comap {X' X : Scheme.{u}} (π : X' ⟶ X)
    (𝒦 : X.IdealSheafData) {V : X.Opens} (hV : IsAffineOpen V)
    (hiso : IsIso (π ∣_ 𝒦.support.compl)) :
    IsIso (((π ∣_ V) ≫ hV.isoSpec.hom) ∣_
      ((𝒦.comap V.ι).comap hV.isoSpec.inv).support.compl) := by
  have heq : V.ι ⁻¹ᵁ 𝒦.support.compl
      = hV.isoSpec.hom ⁻¹ᵁ ((𝒦.comap V.ι).comap hV.isoSpec.inv).support.compl := by
    rw [support_compl_comap_eq_preimage, support_compl_comap_eq_preimage,
      preimage_hom_preimage_inv]
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso' (isIso_morphismRestrict_restrict_of_eq π V heq hiso) inferInstance

/-! ### The condition `hc`, and Stacks 088B and 088E with no hypothesis -/

/-- **The condition `hc` of [Stacks, Tag 088B] holds, with no hypothesis.**
`Stacks.Algebraization.HasAdicBaseChangeUnitCondition` — the source's condition on the unit of
the adjunction of the base change away from the support, quantified over the data of
`Stacks.Algebraization.HasAffineLocalDirectImageSolution` and over the affine opens of the base —
is a theorem.

The condition carries `IsIso (π ∣_ 𝒦.support.compl)`, the source's own hypothesis on the
modification, as an antecedent inside its quantifier, and that is all the proof uses.
`Stacks.Algebraization.isIso_morphismRestrict_isoSpec_hom_comp_comap` carries it to
`(π ∣_ V) ≫ e.hom` over `Spec Γ(X, V)`,
`Stacks.Algebraization.isIso_morphismRestrict_pullbackSnd_comap` carries it to the base change
along `Spec (Γ(X, V) ^∧) ⟶ Spec Γ(X, V)` — which is
`Stacks.Algebraization.adicBaseChangeMap` by definition — and
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`, which is
unconditional, turns `IsIso (π' ∣_ U)` into the invertibility of the restricted unit at every
module. The system, the coherent module, the isomorphism `β` and the algebraization isomorphism
asked of `𝒜` are all unused: the statement is about `π'` alone.

No `stacks` attribute is attached: this is the discharge of a binder, not a statement of the
source. -/
public theorem hasAdicBaseChangeUnitCondition : HasAdicBaseChangeUnitCondition.{u} := by
  intro X' X _ _ π _ _ K _ _ _ hiso V _ _
  exact isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit _ _
    (isIso_morphismRestrict_pullbackSnd_comap _ _ _
      (isIso_morphismRestrict_isoSpec_hom_comp_comap π K V.2 hiso)) _

/-- **[Stacks, Tag 088B] at a general base, with no hypothesis.**
`Stacks.Algebraization.IsDirectImageComparison` — the form of Stacks 088B that Stacks 088C,
`hDev` and `hSupp` consume, at an arbitrary Noetherian base and an arbitrary quasi-coherent ideal
sheaf — holds outright.

`Stacks.Algebraization.isDirectImageComparison_of_adicBaseChangeUnitCondition` at
`Stacks.Algebraization.hasAdicBaseChangeUnitCondition`.

No `stacks` attribute is attached: the tag is registered on
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions`. -/
public theorem isDirectImageComparison_holds : IsDirectImageComparison.{u} :=
  isDirectImageComparison_of_adicBaseChangeUnitCondition hasAdicBaseChangeUnitCondition

/-- **[Stacks, Tag 088E], Grothendieck's existence theorem.** Let `A` be a Noetherian ring
complete with respect to an ideal `I` and let `f : Z ⟶ Spec A` be separated and of finite type
(`IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`). Then the functor of [Stacks, Tag 088D]

  `Coh_{support proper over A}(𝒪_Z) ⥤ Coh_{support proper over A}(Z, I 𝒪_Z)`

is an equivalence.

`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_adicBaseChangeUnitCondition`
at `Stacks.Algebraization.hasAdicBaseChangeUnitCondition`. Following the source, the proof reduces
to Stacks 088C on the closed subschemes of `Z` proper over `A`, after showing that every coherent
adic system with support proper over `A` is annihilated by the ideal sheaf of such a subscheme
(Chow's lemma, the projective case 0885, and Stacks 088B through
`Stacks.Algebraization.transport_of_isDirectImageComparison`).

This is the carrier of Stacks 088E: it takes no input beyond the source's hypotheses, and
supersedes the conditional forms
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver` and
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_adicBaseChangeUnitCondition`,
which take theirs as an argument. -/
@[stacks 088E "Grothendieck's existence theorem: A Noetherian and complete with respect to I, \
X separated and of finite type over A; the functor of 088D from coherent O_X-modules with support \
proper over A to coherent I-adic systems with support proper over A is an equivalence",
  ega "III 5.2.5" "more general",
  ega "III 5.2.6" "more general"]
public theorem isEquivalence_completionFunctorProperOver_holds
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (completionFunctorProperOver A I f).IsEquivalence :=
  isEquivalence_completionFunctorProperOver_of_adicBaseChangeUnitCondition A I f
    hasAdicBaseChangeUnitCondition

end Stacks.Algebraization

end

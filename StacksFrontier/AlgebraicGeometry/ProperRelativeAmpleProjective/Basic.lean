module

public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersUniformDegree.Basic
public import StacksFrontier.AlgebraicGeometry.ImmersionTwistGapUniform

/-!
# Stacks Tag 0B5N: properness plus a relatively ample sheaf gives local projectivity

Let `f : X ⟶ S` be a proper morphism of schemes. If there is an `f`-ample invertible
`𝒪_X`-module, then `f` is locally projective. This is [Stacks, Tag 0B5N].

## The source's proof, and where each step comes from

The source's proof is two sentences: the ample sheaf gives, locally over `S`, an immersion
`i : X ⟶ ℙⁿ_S` ([Stacks, Tag 01VT]), and properness makes `i` a closed immersion
([Stacks, Tag 01W6]). Both steps are available.

* **The immersion.** Relative ampleness is *defined* in this repository by ampleness of the
  restriction of `L` to `f⁻¹(V)` for every affine open `V ⊆ S`
  (`Stacks.RelativeAmple.IsRelativelyAmple`, Tag 01VH), so the local step of Tag 01VT is
  `Stacks.VeryAmplePowersUniformDegree.eventually_hasImmersionTwistOver_restrict`, which takes
  [Stacks, Tag 01VS] as the named hypothesis
  `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`. That hypothesis is discharged
  here as `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`, from the
  unconditional Tag 01VS of `Stacks.StalkwiseGeneration.immersionTwistGap_of_isAmple`. So **no
  named gap hypothesis survives into the statements below**; in particular neither the Tag 02NN
  hypothesis `Stacks.Tag01VT.TwistAmpleOverAffine` nor the Tag 0B3E hypothesis
  `Stacks.RelativeVeryAmple.AmplePullbackGap` is needed, because only the implication
  (2) ⟹ (6) of Tag 01VT is used and those two drive the converse implications.
* **The closed immersion.** Tag 01W6 is Mathlib's
  `AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated`: the composite
  `X ⟶ ℙⁿ_V ⟶ V` is `f ∣_ V`, which is proper, and `ℙⁿ_V ⟶ V` is separated — it is proper, by
  `AlgebraicGeometry.isProper_projectiveSpaceOver` — so `i` is universally closed, hence has
  closed image, hence is a closed immersion since it is already a preimmersion.

## The conclusion, and that it is the source's

"Locally projective" is clause (3) of Definition 01W8, `AlgebraicGeometry.IsLocallyProjective`:
the base is covered by opens over which the restriction of `f` is a closed immersion into the
projective bundle `𝐏(ℰ)` of a quasi-coherent module of finite type. What the argument above
produces is the a priori **stronger** H-projective form, clause (2) locally on the base, namely
`AlgebraicGeometry.IsLocallyProjectiveMorphism`; it is stronger because `ℙⁿ_S` is the projective
bundle of `𝒪_S^{n + 1}` and not conversely. Both are stated below, and the passage from the
stronger to the source's own is the implication (2) ⟹ (1) of [Stacks, Tag 01WB],
`AlgebraicGeometry.isLocallyProjective_of_isLocallyProjectiveMorphism`, unconditional in the
tree.

So the Tag 0B5N attribute sits on the clause-(3) conclusion, which is the source's, and the
H-projective strengthening is recorded beside it. Nothing is weakened.

## Main results

* `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`: [Stacks, Tag 01VS] at every
  situation, which is the single named input the local step of [Stacks, Tag 01VT] still carried.
* `Stacks.ProperRelativeAmpleProjective.isProjectiveMorphism_of_isProper_of_hasImmersionTwistOver`:
  [Stacks, Tag 01W6] applied to an immersion into projective space over the base — a proper
  morphism admitting one is H-projective.
* `isLocallyProjectiveMorphism_of_isProper_of_isRelativelyAmple`: the H-projective
  strengthening of [Stacks, Tag 0B5N].
* `isLocallyProjective_of_isProper_of_isRelativelyAmple` and
  `isLocallyProjective_of_isProper_of_exists_isRelativelyAmple`: **[Stacks, Tag 0B5N]**, with the
  ample sheaf supplied and with its existence assumed. The last three names are all in the
  `Stacks.ProperRelativeAmpleProjective` namespace.

## Implementation notes

**The two spellings of the structure morphism of `ℙⁿ_S` agree by `rfl`.**
`AlgebraicGeometry.IsProjectiveMorphism` is written with `projectiveSpaceOver n S ↘ S`, while
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` is written with the first pullback
projection that this `OverClass` instance is defined to be, so the clause "over `S`" of the
latter is accepted directly as the clause of the former with no transport.

**The covering used is the family of all affine opens of the base**, as
`AlgebraicGeometry.Scheme.Cover.mkOfCovers` of `S.affineOpens`; it covers because every point of
a scheme has an affine open neighbourhood
(`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`). Its members are the open subschemes
`V.toScheme` with their inclusions, which is what makes the base change `pullback.snd f V.ι`
isomorphic to the restriction `f ∣_ V` by `AlgebraicGeometry.pullbackRestrictIsoRestrict` — and
the restriction is the morphism the ampleness clause of relative ampleness and Tag 01VS's
finite-type instance are both stated for.

**Properness of the restriction costs nothing.** `IsProper (f ∣_ V)` and
`LocallyOfFiniteType f` are both found by instance search from `IsProper f`.

## References

* [Stacks Project, Tag 0B5N](https://stacks.math.columbia.edu/tag/0B5N)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.ProperRelativeAmpleProjective

/-! ### Stacks Tag 01VS at every situation -/

/-! ### Stacks Tag 01W6: properness upgrades the immersion to a closed immersion -/

/-- **A proper morphism admitting an immersion into projective space over its base is
H-projective.** This is [Stacks, Tag 01W6] at `Y = ℙⁿ_B`: the immersion `i` composed with the
separated structure morphism `ℙⁿ_B ⟶ B` is `g`, which is universally closed, so `i` is
universally closed; its range is therefore closed, and a preimmersion with closed range is a
closed immersion.

The separatedness of `ℙⁿ_B ⟶ B` is read off its properness,
`AlgebraicGeometry.isProper_projectiveSpaceOver`. The module `M` carried by
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` plays no part: only the immersion and
the clause that it lies over `B` are used. -/
theorem isProjectiveMorphism_of_isProper_of_hasImmersionTwistOver {A B : Scheme.{u}} (g : A ⟶ B)
    [IsProper g] {M : A.Modules} (h : HasImmersionTwistOver g M) : IsProjectiveMorphism g := by
  obtain ⟨n, i, hi, hover, -⟩ := h
  have := hi
  have hover' : i ≫ (projectiveSpaceOver n B ↘ B) = g := hover
  have : IsProper (projectiveSpaceOver n B ↘ B) := isProper_projectiveSpaceOver n B
  have : UniversallyClosed (i ≫ (projectiveSpaceOver n B ↘ B)) := by
    rw [hover']; infer_instance
  have : UniversallyClosed i :=
    UniversallyClosed.of_comp_of_isSeparated i (projectiveSpaceOver n B ↘ B)
  have : IsClosedImmersion i :=
    IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range
  exact ⟨n, i, inferInstance, hover'⟩

/-- **H-projectivity is invariant under replacing the source by an isomorphic one**: compose the
closed immersion into `ℙⁿ_B` with the isomorphism. -/
theorem isProjectiveMorphism_iso_hom_comp {A A' B : Scheme.{u}} (e : A' ≅ A) {g : A ⟶ B}
    (hg : IsProjectiveMorphism g) : IsProjectiveMorphism (e.hom ≫ g) := by
  obtain ⟨n, i, hi, hcomp⟩ := hg
  have := hi
  exact ⟨n, e.hom ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩

/-! ### Stacks Tag 0B5N -/

/-- **The H-projective strengthening of [Stacks, Tag 0B5N].** A proper morphism carrying a
relatively ample invertible module is H-projective over each member of an open covering of its
base — namely over each affine open, which is more than
`AlgebraicGeometry.IsLocallyProjectiveMorphism` asks for.

Over an affine open `V ⊆ S` the restriction `f ∣_ V` is proper and locally of finite type, and
relative ampleness gives ampleness of the restriction of `L` to `f⁻¹(V)`; so [Stacks, Tag 01VS]
produces an immersion `f⁻¹(V) ⟶ ℙⁿ_V` over `V` and
`Stacks.ProperRelativeAmpleProjective.isProjectiveMorphism_of_isProper_of_hasImmersionTwistOver`
makes it a closed immersion. -/
theorem isLocallyProjectiveMorphism_of_isProper_of_isRelativelyAmple {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (L : X.Modules) [IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : IsLocallyProjectiveMorphism f := by
  refine ⟨Scheme.Cover.mkOfCovers S.affineOpens (fun V : S.affineOpens => V.1.toScheme)
    (fun V => V.1.ι) (fun x => ?_), fun V => ?_⟩
  · obtain ⟨W, hW, hxW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (x := x) (U := ⊤) (by trivial)
    exact ⟨⟨W, hW⟩, ⟨x, hxW⟩, by simp⟩
  · change IsProjectiveMorphism (pullback.snd f (V : S.affineOpens).1.ι)
    obtain ⟨d₀, hd₀, hd⟩ :=
      Stacks.VeryAmplePowersUniformDegree.eventually_hasImmersionTwistOver_restrict
        Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform f L hL
          (V : S.affineOpens).1 (V : S.affineOpens).2
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f (V : S.affineOpens).1]
    exact isProjectiveMorphism_iso_hom_comp _
      (isProjectiveMorphism_of_isProper_of_hasImmersionTwistOver _ (hd d₀ le_rfl))

/-- **[Stacks, Tag 0B5N], with the relatively ample module supplied.** A proper morphism of
schemes carrying an invertible module ample relative to it is locally projective, in the sense of
clause (3) of Definition 01W8.

This is
`Stacks.ProperRelativeAmpleProjective.isLocallyProjectiveMorphism_of_isProper_of_isRelativelyAmple`
followed by the implication (2) ⟹ (1) of [Stacks, Tag 01WB]. -/
theorem isLocallyProjective_of_isProper_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (L : X.Modules) [IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : IsLocallyProjective f :=
  isLocallyProjective_of_isLocallyProjectiveMorphism
    (isLocallyProjectiveMorphism_of_isProper_of_isRelativelyAmple f L hL)

/-- **[Stacks, Tag 0B5N].** Let `f : X ⟶ S` be a proper morphism of schemes. If there exists an
`f`-ample invertible `𝒪_X`-module, then `f` is locally projective. -/
@[stacks 0B5N]
theorem isLocallyProjective_of_isProper_of_exists_isRelativelyAmple {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f]
    (hL : ∃ (L : X.Modules) (h : IsInvertibleModule X L),
      letI := h; Stacks.RelativeAmple.IsRelativelyAmple f L) :
    IsLocallyProjective f := by
  obtain ⟨L, h, hample⟩ := hL
  have := h
  exact isLocallyProjective_of_isProper_of_isRelativelyAmple f L hample

end Stacks.ProperRelativeAmpleProjective

end

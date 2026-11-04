module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.Serre
public import StacksFrontier.AlgebraicGeometry.ChevalleyAffine.Basic

/-!
# Chevalley's affineness criterion, reduced to two named inputs

[Stacks, Tag 01YQ] states that a Noetherian scheme `X` receiving a finite surjective morphism
`f : Y ⟶ X` from an affine scheme is affine. This file applies the Serre skeleton of
`StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.Serre` to that situation and records
exactly what is left.

Write `A = Γ(X, ⊤)`, `B = Γ(Y, ⊤)` and `φ = f.appTop : A ⟶ B`.

## Main results

* `Stacks.SerreAffinenessCriterion.span_image_appTop_eq_top`: **unconditional, and the only half of
  Serre's second input that the hypotheses of 01YQ supply.** If the basic opens of a family
  `s ⊆ A` cover `X` then `φ '' s` generates the unit ideal of `B`. Indeed the preimages
  `Y_{φ r} = f⁻¹(X_r)` cover `Y`, and `Y` is affine. Surjectivity and finiteness of `f` are not
  used.
* `Stacks.SerreAffinenessCriterion.isAffine_of_isFinite_surjective_of_isNoetherian_of_map_eq_top`:
  01YQ holds once (`H₁`) every closed point of `X` lies in an affine basic open of a global section
  and (`H₂`) `φ` reflects the unit ideal, i.e. `I·B = B` implies `I = A`.
* `isAffine_of_isFinite_surjective_of_isNoetherian_of_surjective_SpecMap_appTop`
  and `…_of_isIntegral_appTop`: the same with `H₂` replaced by surjectivity of
  `Spec B ⟶ Spec A`, respectively by integrality of `φ`. Each of these implies `H₂`.

## What this changes about the recorded status of 01YQ

`StacksFrontier/AlgebraicGeometry/ChevalleyAffine/Basic.lean` reduces 01YQ to **two** extra
hypotheses: quasi-affineness of `X`, and integrality of `φ`. The first of those is now
*derivable* from `H₁`, by
`Stacks.SerreAffinenessCriterion.isQuasiAffine_of_forall_isClosed_singleton`, so the pair
`(quasi-affine, integral)` is replaced by the pair `(H₁, integral)`, and integrality can be
weakened further to surjectivity of `Spec φ` or to the unit-ideal reflection `H₂`. Both
replacements are inputs that Serre's criterion genuinely produces, whereas quasi-affineness was
an assumption with no route to it.

## What is not done

**[Stacks, Tag 01YQ] is still not proved, and no `stacks` attribute is attached anywhere in this
directory.** The two inputs above are undischarged and both are cohomological. Writing
`H¹(X, ℱ)` for `Hgroup X.ringCatSheaf ⊤ 1 ℱ` (the repository's cohomology group, declared in
the `Hgroup` of [Stacks, Tag 01E3], which lives at the root namespace, *not* under
`Stacks.Cohomology`), the two missing declarations are the following, both of which elaborate at
this pin.

*Serre step one*, to be stated as
`Stacks.SerreAffinenessCriterion.exists_isAffineOpen_basicOpen_mem_of_isZero_hgroup`:

```
theorem (X : Scheme.{u}) [CompactSpace X]
    (hH1 : ∀ (I : X.Modules) (_ : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) I)
      (_ : I ⟶ SheafOfModules.unit X.ringCatSheaf),
        Limits.IsZero (Hgroup X.ringCatSheaf ⊤ 1 I))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧ ∃ U : X.Opens, IsAffineOpen U ∧ X.basicOpen r ≤ U
```

Its conclusion is exactly the hypothesis of
`Stacks.SerreAffinenessCriterion.exists_isAffineOpen_basicOpen_mem_of_le`. The proof is the first
paragraph of [Stacks, Tag 01XF]: for an affine open `U = Spec A ∋ x`, the quasi-coherent ideal
sheaves `𝓘`, `𝓘'` of the reduced closed subschemes `X ∖ U` and `(X ∖ U) ∪ {x}` sit in a short exact
sequence `0 → 𝓘' → 𝓘 → 𝓘/𝓘' → 0` with `Γ(X, 𝓘/𝓘') = A/𝔪`, so `H¹(X, 𝓘') = 0` lifts `1 ∈ A/𝔪` to a
global `r ∈ Γ(X, 𝓘)` with `x ∈ X_r ⊆ U`.

*Serre step two*, to be stated as
`Stacks.SerreAffinenessCriterion.span_eq_top_of_isZero_hgroup`:

```
theorem (X : Scheme.{u})
    (hH1 : ∀ (I : X.Modules) (_ : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) I)
      (_ : I ⟶ SheafOfModules.unit X.ringCatSheaf),
        Limits.IsZero (Hgroup X.ringCatSheaf ⊤ 1 I))
    (s : Finset Γ(X, ⊤)) (hcov : (⨆ r ∈ s, X.basicOpen r) = ⊤) :
    Ideal.span (s : Set Γ(X, ⊤)) = ⊤
```

Its conclusion is exactly the hypothesis `H₂` of
`Stacks.SerreAffinenessCriterion.isAffine_of_forall_isClosed_singleton_of_span_eq_top`. The proof
is the last paragraph of [Stacks, Tag 01XF]: the kernel `ℱ` of the map `𝒪_X^{⊕n} → 𝒪_X` defined by
`s` — epi because the basic opens cover — is filtered by `ℱ ∩ 𝒪_X^{⊕i}` with successive quotients
quasi-coherent sheaves of ideals, so `H¹(X, ℱ) = 0` by the long exact sequence, so
`Γ(X, 𝒪_X)^{⊕n} → Γ(X, 𝒪_X)` is surjective.

## State of the source's own route in the library

The vanishing `H¹(X, 𝓘) = 0` that feeds the two declarations above is, in the source, the whole
content of 01YQ: the dévissage [Stacks, Tag 01YM] applied to `𝒫(ℱ) ⇔ H¹(X, ℱ) = 0`. Of its
inputs:

* [Stacks, Tag 01XB] is **formalized** —
  `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, in
  `StacksFrontier/AlgebraicGeometry/AffineCohomologyGlue/AffineOpenVanishing.lean`, with the `U = ⊤`
  corollary `isZero_hgroup_of_isAffine` beside it.
* [Stacks, Tag 089W] is **formalized** —
  `Stacks.AlgebraicGeometry.AffineHigherDirectImage.cohomologyPushforwardIso`, in
  `StacksFrontier/AlgebraicGeometry/AffineHigherDirectImage/Natural.lean`, as a natural
  isomorphism of functors on quasi-coherent modules.
* [Stacks, Tag 01YP] is **formalized** —
  `AffineIdealPushforward.ideal_smul_pushforward_sections_eq`, in
  `StacksFrontier/AlgebraicGeometry/Cohomology/IdealPushforwardAffine.lean`.
* [Stacks, Tag 01YM] (dévissage) and [Stacks, Tag 01YO] carry no attribute anywhere in the
  repository, and neither do [Stacks, Tag 01XF] and [Stacks, Tag 01XG], the two forms of Serre's
  criterion. Those two are the blocker. [Stacks, Tag 0B6V], sometimes listed as a
  third form of Serre's criterion, is not one: it is Lemma 48.17.11, on invertibility of
  `f^!𝒪_Y` for a local complete intersection morphism, and is unrelated to affineness.

## References

* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SerreAffinenessCriterion

variable {X Y : Scheme.{u}}

/-- **A cover of `X` by basic opens of global sections becomes a unit ideal upstairs.** If the
basic opens of `s ⊆ Γ(X, ⊤)` cover `X` and `Y` is affine, then the images of `s` under
`f.appTop` generate the unit ideal of `Γ(Y, ⊤)`: the preimages `Y_{f.appTop r} = f⁻¹(X_r)` cover
`Y`, and on an affine scheme a covering family of basic opens spans.

Neither surjectivity nor finiteness of `f` is used. -/
theorem span_image_appTop_eq_top (f : Y ⟶ X) [IsAffine Y] {s : Set Γ(X, ⊤)}
    (hs : (⨆ r ∈ s, X.basicOpen r) = ⊤) :
    Ideal.span (f.appTop '' s) = ⊤ := by
  rw [← (isAffineOpen_top Y).iSup_basicOpen_eq_self_iff]
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨r, hr⟩ := Opens.mem_iSup.mp (hs.ge (show f y ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨hrs, hxr⟩ := Opens.mem_iSup.mp hr
  refine Opens.mem_iSup.mpr ⟨⟨f.appTop r, Set.mem_image_of_mem _ hrs⟩, ?_⟩
  have hy : y ∈ f ⁻¹ᵁ X.basicOpen r := hxr
  rwa [Scheme.preimage_basicOpen_top] at hy

/-- **[Stacks, Tag 01YQ] from two named inputs.** A Noetherian scheme receiving a finite
surjective morphism from an affine scheme is affine, *provided*

* `H₁`: every closed point of `X` lies in an affine basic open of a global section; and
* `H₂`: `f.appTop : Γ(X, ⊤) ⟶ Γ(Y, ⊤)` reflects the unit ideal.

Both are consequences of the vanishing of `H¹(X, 𝓘)` on quasi-coherent sheaves of ideals, which
is what the source proves; neither is proved here. See the module documentation for the precise
missing statements. -/
theorem isAffine_of_isFinite_surjective_of_isNoetherian_of_map_eq_top (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X]
    (H₁ : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r)
    (H₂ : ∀ I : Ideal Γ(X, ⊤), Ideal.map f.appTop.hom I = ⊤ → I = ⊤) :
    IsAffine X := by
  refine isAffine_of_forall_isClosed_singleton_of_span_eq_top X H₁ fun s _ hcov ↦ H₂ _ ?_
  rw [Ideal.map_span]
  exact span_image_appTop_eq_top f hcov

/-- **[Stacks, Tag 01YQ] from one cohomological input and surjectivity of `Spec φ`.** Compared to
`Stacks.AlgebraicGeometry.ChevalleyAffine.isAffine_of_isQuasiAffine_of_isIntegral_appTop`, the
quasi-affineness assumption is replaced by `H₁` — which Serre's criterion produces — and
integrality of `φ` is weakened to surjectivity of `Spec φ`. -/
theorem isAffine_of_isFinite_surjective_of_isNoetherian_of_surjective_SpecMap_appTop (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X] [Surjective (Spec.map f.appTop)]
    (H₁ : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) :
    IsAffine X := by
  have := isQuasiAffine_of_forall_isClosed_singleton X H₁
  have := AlgebraicGeometry.ChevalleyAffine.surjective_toSpecΓ_of_surjective_SpecMap_appTop f
  exact AlgebraicGeometry.ChevalleyAffine.isAffine_of_isQuasiAffine_of_surjective_toSpecΓ X

/-- **[Stacks, Tag 01YQ] from one cohomological input and integrality of `φ`.** The pair of extra
hypotheses recorded in `StacksFrontier/AlgebraicGeometry/ChevalleyAffine/Basic.lean`
(quasi-affineness of `X`, integrality of `φ`) becomes the single extra hypothesis of
integrality, together with the input `H₁` that Serre's criterion supplies. -/
theorem isAffine_of_isFinite_surjective_of_isNoetherian_of_isIntegral_appTop (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X]
    (H₁ : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r)
    (h : (Scheme.Hom.appTop f).hom.IsIntegral) :
    IsAffine X := by
  have := isQuasiAffine_of_forall_isClosed_singleton X H₁
  exact AlgebraicGeometry.ChevalleyAffine.isAffine_of_isIntegral_appTop f h

end Stacks.SerreAffinenessCriterion

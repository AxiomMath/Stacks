module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.GradedConsequence
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.AffineFiniteType
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFinitenessSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre product `X' = Spec(B) ×_{Spec(A)} X` of [Stacks, Tag 0897]'s proof

The proof of [Stacks, Tag 0897] begins with the fibre product square

```
X' = Spec(B) ×_{Spec(A)} X  --π-->  X
          |                          |
          f'                         f
          v                          v
      Spec(B)             -->    Spec(A)
```

and both parts of the tag are read off from it. `GradedProperCohomology/Basic.lean` takes `X'`,
`f'` and `π` as *binders*, on the ground that nothing built the square. This file builds it, and
restates both parts with the square supplied.

The square is Mathlib's pullback of `Spec(B) ⟶ Spec(A)` along `f`, and the two properties the
source cites for it are both available there:

* `f' = pullback.fst` is proper because `f` is, which is [Stacks, Tag 01W4]
  (`AlgebraicGeometry.IsProper.isStableUnderBaseChange`, and the instance
  `AlgebraicGeometry.IsProper (CategoryTheory.Limits.pullback.fst _ _)` it supports);
* `π = pullback.snd` is affine because `Spec(B) ⟶ Spec(A)` is, affineness of a morphism being
  stable under base change (`AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`). Affineness
  of `π` is what the source gets instead from `X'` being the relative spectrum of `ℬ` — it is the
  only consequence of that identification the proof uses, both for [Stacks, Tag 089W] in part (1)
  and for [Stacks, Tag 0892] part (2) in part (2).

`X'` is also Noetherian, as the source notes: `B` is a finitely generated algebra over the
Noetherian ring `A`, hence Noetherian by the Hilbert basis theorem, so `Spec(B)` is Noetherian,
and `f'` is proper hence locally of finite type.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraMap`: the morphism
  `Spec(B) ⟶ Spec(A)` of an algebra.
* `baseChange`: the scheme `X' = Spec(B) ×_{Spec(A)} X`.
* the morphism `f' : X' ⟶ Spec(B)` is the base's
  `Stacks.AlgebraicGeometry.GradedProperCohomology.baseChangeToSpec`.
* `baseChangeProj`: the projection `π : X' ⟶ X`.

## Main results

* `isProper_baseChangeToSpec`: **[Stacks, Tag 01W4] in the situation of [Stacks, Tag 0897]** —
  `f'` is proper.
* `isAffineHom_baseChangeProj`: `π` is affine.
* `isLocallyNoetherian_baseChange`: `X'` is locally Noetherian.
* `moduleFinite_gradedCohomologySum_baseChange`: **[Stacks, Tag 0897] part (1)** with the fibre
  product square supplied and with [Stacks, Tag 02O6] discharged.
* `exists_isZero_pieceTwistCohomology_baseChange`: **[Stacks, Tag 0897] part (2)** with the fibre
  product square supplied and with [Stacks, Tag 02O1]'s hypothesis discharged.

## Implementation notes

What is *not* done here, and is what still stands between these statements and an unconditional
[Stacks, Tag 0897]:

1. the identification of `X'` with the relative spectrum of `ℬ = f^* B̃` — the general base-change
   isomorphism is `Stacks.AffineAlgebraEquivalence.relativeSpecPullbackIso`, which identifies
   `Spec_S(A) ×_S T` with `Spec_T(g^* A)`; what it needs here is the identification of
   `Spec_{Spec A}(B̃)` with `Spec(B)`, and the passage from the *graded* `ℬ`-module `ℱ` to a module
   over the total algebra, which is what `relativeSpecQcohEquivalence` consumes;
2. the coherence of the resulting `ℱ'`, which the source states with *"details omitted"*: it
   needs `ℱ'` to be of finite type, and no lemma in this library reflects finite type or
   coherence downwards along an affine morphism;
3. the `B`-linearity of the comparison, the `B`-action on `⨁ₙ H^p(X, ℱₙ)` coming from the
   `ℬ`-action on `ℱ` through functoriality of cohomology.

So `F'` and the comparison remain hypotheses. They are hypotheses of a different kind from the
ones discharged: the square itself, which was a binder, is now a construction, and the two
cohomological inputs [Stacks, Tag 02O6] and [Stacks, Tag 02O1] are now theorems.

No `@[stacks]` attribute is attached. Tags 0897, 01W4, 02O6 and 02O1 all have their sites
already, and none is moved or duplicated; these statements are the same two implications with
fewer hypotheses.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The fibre product square -/

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- The morphism of affine schemes `Spec(B) ⟶ Spec(A)` attached to an `A`-algebra `B`: the
bottom edge of the fibre product square of [Stacks, Tag 0897]'s proof. -/
abbrev specAlgebraMap : Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

variable {X : Scheme.{u}}

/-- **The scheme `X' = Spec(B) ×_{Spec(A)} X`** of [Stacks, Tag 0897]'s proof. -/
abbrev baseChange (f : X ⟶ Spec (.of A)) : Scheme.{u} :=
  pullback (specAlgebraMap A B) f

/-- **The projection `π : X' ⟶ X`** of [Stacks, Tag 0897]'s proof. -/
abbrev baseChangeProj (f : X ⟶ Spec (.of A)) : baseChange A B f ⟶ X :=
  pullback.snd (specAlgebraMap A B) f

/-- **[Stacks, Tag 01W4] in the situation of [Stacks, Tag 0897]**: `f' : X' ⟶ Spec(B)` is proper,
being the base change of the proper morphism `f` along `Spec(B) ⟶ Spec(A)`. -/
instance isProper_baseChangeToSpec (f : X ⟶ Spec (.of A)) [IsProper f] :
    IsProper (baseChangeToSpec A B f) :=
  inferInstance

/-- **`π : X' ⟶ X` is affine**, being the base change of the morphism of affine schemes
`Spec(B) ⟶ Spec(A)`. This is the only property of the identification of `X'` with the relative
spectrum of `ℬ` that the proof of [Stacks, Tag 0897] uses. -/
@[sga "3 I 4.6.4.1" "special case"]
instance isAffineHom_baseChangeProj (f : X ⟶ Spec (.of A)) :
    _root_.AlgebraicGeometry.IsAffineHom (baseChangeProj A B f) :=
  -- `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange` is declared under
  -- `backward.isDefEq.respectTransparency.types false`, so instance search does not find
  -- `MorphismProperty.IsStableUnderBaseChangeAlong @IsAffineHom f` and
  -- `MorphismProperty.pullback_snd` does not fire; ascribing the property and applying
  -- `of_isPullback` by hand does resolve it.
  have hsbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u}) := inferInstance
  hsbc.of_isPullback (IsPullback.of_hasPullback (specAlgebraMap A B) f) inferInstance

/-- **`X'` is locally Noetherian**, as [Stacks, Tag 0897]'s proof notes: `B` is a finitely
generated algebra over the Noetherian ring `A`, hence Noetherian, so `Spec(B)` is locally
Noetherian, and `f'` is proper hence locally of finite type. -/
instance isLocallyNoetherian_baseChange [IsNoetherianRing A] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian (baseChange A B f) :=
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of B)) :=
    _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.mpr this
  _root_.AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (baseChangeToSpec A B f)

/-! ### The two parts of Tag 0897 over the constructed square -/

variable {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- **[Stacks, Tag 0897] part (1), over the fibre product square of the source's own proof.** Let
`A` be a Noetherian ring, `B` a finitely generated graded `A`-algebra, `f : X ⟶ Spec A` proper
and `F` a quasi-coherent graded `𝓑`-module of finite type. Granted a coherent `𝒪_{X'}`-module
`F'` on `X' = Spec(B) ×_{Spec(A)} X` and a `B`-linear comparison of `⨁ₙ H^p(X, Fₙ)` with
`H^p(X', F')`, the graded `B`-module `⨁ₙ H^p(X, Fₙ)` is a finite `B`-module.

Compared with `moduleFinite_gradedCohomologySum_of_tag02O6`, the scheme `X'` and the proper
morphism `f' : X' ⟶ Spec B` are no longer binders: they are the fibre product and its projection,
the properness of `f'` is [Stacks, Tag 01W4], and the hypothesis `h02O6` is gone. Finite type is
the affine `Stacks.Coherent.IsFiniteTypeOnAffine`, as in
`moduleFinite_gradedCohomologySum'`. -/
theorem moduleFinite_gradedCohomologySum_baseChange
    [IsNoetherianRing A] (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (p : ℕ)
    (F' : (baseChange A B f).Modules) [F'.IsCoherent]
    [Module B (gradedCohomologySum F p)]
    (cmp : gradedCohomologySum F p ≃ₗ[B]
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom B (baseChangeToSpec A B f))).obj
        (cohomologyOf (baseChange A B f) p F'))) :
    Module.Finite B (gradedCohomologySum F p) :=
  moduleFinite_gradedCohomologySum' A 𝒜 f F hqc hft p (baseChangeToSpec A B f) F' cmp

/-- **[Stacks, Tag 0897] part (2), over the fibre product square of the source's own proof.** Let
`A` be a Noetherian ring, `B` a finitely generated graded `A`-algebra, `f : X ⟶ Spec A` proper,
`F` a quasi-coherent graded `𝓑`-module of finite type and `L` an ample invertible `𝒪_X`-module.
Granted a coherent `𝒪_{X'}`-module `F'` on `X' = Spec(B) ×_{Spec(A)} X` and the comparison
`hcmp` of the vanishing upstairs with the vanishing of the graded pieces downstairs, there is a
`d₀` such that `H^p(X, Fₙ ⊗ L^{⊗d}) = 0` for every `p > 0`, every `d ≥ d₀` and every `n`.

Compared with `exists_isZero_pieceTwistCohomology'`, the scheme `X'`, the proper `f'` and the
affine projection `π` are no longer binders. -/
theorem exists_isZero_pieceTwistCohomology_baseChange
    [IsNoetherianRing A] (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (F' : (baseChange A B f).Modules) [F'.IsCoherent]
    (hcmp : ∀ p d : ℕ,
      IsZero ((ModuleCat.restrictScalars (baseChangeToSpec A B f).appTop.hom).obj
          (cohomologyOf (baseChange A B f) p
            (tensorModules (baseChange A B f) F'
              (tensorPowModule (baseChange A B f)
                (Stacks.AmpleLocallyClosed.pullbackModule (baseChangeProj A B f) L)
                (d : ℤ))))) →
        ∀ n : ℤ, IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ)))) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ))) :=
  exists_isZero_pieceTwistCohomology' A 𝒜 f F hqc hft L hL
    (baseChangeToSpec A B f) (baseChangeProj A B f) F' hcmp

end Stacks.AlgebraicGeometry.GradedProperCohomology

end

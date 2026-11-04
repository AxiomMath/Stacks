module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.PushforwardRestrictOpen

/-!
# The comparison of a restricted direct image on sections

For an open `U` of a scheme `Z`, an open immersion `g : X' ⟶ Z` and an `𝒪_Z`-module `M`, the
comparison `Stacks.Perfect.PushforwardRestrict.restrictPushforwardRestrictIso` identifies
`g^*((U → Z)_*(M|_U))` with `(X' ∩ U → X')_*((g^*M)|_{X' ∩ U})`.  Both of these have, over an
open
`V` of `X'`, the sections of `M` over `U ∩ g(V)`, in the two spellings
`U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V))` and `g ''ᵁ ((g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))`
compared by `comparisonOpen_eq`.  This file computes what the comparison does to a section: it
restricts it along that equality of opens, which is what the comparison of the extended
alternating Čech complexes of [Stacks, Tag 0G7U] along an open immersion needs.

## Main results

* `comparisonOpen_eq₁` to `comparisonOpen_eq₈`: the nine opens of `Z` the eight factors of
  `restrictPushforwardRestrictIso` successively restrict the coefficient module to, each
  identified with the previous one.  Composed, they are the equality `comparisonOpen_eq` of the
  two spellings of `U ∩ g(V)`; `comparisonOpen_eqUpTo₂` to `comparisonOpen_eqUpTo₇` are the
  partial composites.
* `comparisonFactor₁_app_apply` to `comparisonFactor₈_app_apply`: each factor of the comparison
  restricts a section along the corresponding one of those equalities.
* `comparisonChain₂_app_apply` to `comparisonChain₇_app_apply`: **the section formula for the
  first seven factors.**  On a section of `M` over `U ∩ g(V)`, the composite of the first `k`
  factors is the single restriction map along `comparisonOpen_eqUpTo₍k₎`, for `k ≤ 7`.
* `restrictPushforwardRestrictIso_app_apply_eq_factor₈` together with
  `comparisonFactor₈_app_apply`: **the section formula for the whole comparison**, in two
  steps — the comparison is factor 8 applied to the section restricted along
  `comparisonOpen_eqUpTo₇`, and factor 8 then restricts along `comparisonOpen_eq₈`.

## Implementation notes

Everything here is governed by one cost.  Reading the comparison as a restriction map of `M`
means identifying `Γ(Gᵢ.obj M, V)` — the sections of the `i`-th functor of the chain — with
`Γ(M, Oᵢ)`, and that identification, which is a definitional unfolding of a stack of
`Scheme.Modules.restrictFunctor`s and `Scheme.Modules.pushforward`s, costs a sizeable fraction
of the heartbeat budget each time.  On this chain, two of them in one declaration is
usually affordable, three is usually not, and the pair `(O₀, O₈)` — the two ends of the
comparison — is not affordable *twice* in one declaration, which is what an equation whose
statement crosses between the two spellings and whose proof crosses back needs.

Three things follow, and they are why the file is shaped as it is.  The comparison is grouped
from the left, so that each declaration here mentions `Γ(M, O₀)` and at most one other section
group.  Each step is spread over several declarations — the factor is pulled out
by `trans_hom_app_app`, the previous step is rewritten inside it by `congrArg`, the factor's own
`app` lemma is applied, and only then are the two accumulated restriction maps collapsed.  And
that collapse is done by rewriting the *right*-hand side with `collapseStep`, where both sides
are already `Γ(M, _)` and the rewrite is free, rather than by composing on the left.

## What is *not* here

The last step is not assembled: there is no single equation
`((restrictPushforwardRestrictIso U g).hom.app M).app V z = M.presheaf.map (eqToHom _).op z`.
Its *statement* elaborates, but no proof of it fits in 200000 heartbeats.
None of the following fits: the term `Eq.trans` of the two halves, the same with the two
halves split into four declarations, the collapse by `rw [← collapseStep …]` on the right-hand
side, the collapse by `rw` on the left-hand side, and the same with the equalities of opens
taken as hypotheses so that `whnf` cannot unfold the proved ones.  All of them time out at
`whnf` or `isDefEq` on the `(O₀, O₈)` pair, and raising the heartbeat limit is not available.
The content is nevertheless complete: `restrictPushforwardRestrictIso_app_apply_eq_factor₈`
and `comparisonFactor₈_app_apply` give it in two steps, and a consumer that is already working
in the `Γ(M, _)` spelling can finish with `collapseStep` without paying either crossing again.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech (comp_app_apply map_eq_apply map_map_apply)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.PushforwardRestrict

variable {Z X' : Scheme.{u}} (U : Z.Opens) (g : X' ⟶ Z) [IsOpenImmersion g]

/-- The image of an open along a composite of open immersions. -/
public theorem image_comp_opens {X₁ Y₁ Z₁ : Scheme.{u}} (a : X₁ ⟶ Y₁) (b : Y₁ ⟶ Z₁)
    [IsOpenImmersion a] [IsOpenImmersion b] (T : X₁.Opens) :
    (a ≫ b) ''ᵁ T = b ''ᵁ (a ''ᵁ T) := by
  apply TopologicalSpace.Opens.ext
  simp

/-- The image of an open along equal open immersions. -/
public theorem image_congr {X₁ Y₁ : Scheme.{u}} {a a' : X₁ ⟶ Y₁} [IsOpenImmersion a]
    [IsOpenImmersion a'] (h : a = a') (T : X₁.Opens) : a ''ᵁ T = a' ''ᵁ T := by
  subst h; rfl

/-- **One step of the collapse of a chain of restrictions.**  A restriction along `C = B` after
a restriction along `B = A` is the restriction along `C = A`.  All three equalities of opens are
arguments rather than inferred, which keeps the open the resulting equation lives at out of the
unifier's hands when the step is chained. -/
public theorem collapseStep (F : Z.Modules) {A B C : Z.Opens} (hBA : B = A) (hCB : C = B)
    (hCA : C = A) (y : Γ(F, A)) :
    F.presheaf.map (eqToHom hCB).op (F.presheaf.map (eqToHom hBA).op y)
      = F.presheaf.map (eqToHom hCA).op y := by
  rw [map_map_apply]
  exact map_eq_apply _ _ _ _

/-- Applying a composite of two natural isomorphisms of module functors to a section. -/
public theorem trans_hom_app_app {Y₁ : Scheme.{u}} {F G H : Z.Modules ⥤ Y₁.Modules}
    (α : F ≅ G) (β : G ≅ H) (M : Z.Modules) (V' : Y₁.Opens) (z : Γ(F.obj M, V')) :
    ((α ≪≫ β).hom.app M).app V' z = (β.hom.app M).app V' ((α.hom.app M).app V' z) := rfl

variable (V : X'.Opens)

/-- The open the unit factor of the comparison restricts to. -/
public alias comparisonOpen_eq₁ := image_inter_eq

/-- The image of `X' ∩ U ∩ V` along `X' ∩ U ⟶ X' ⟶ Z`, written with the composite. -/
public theorem comparisonOpen_eq₂ :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ (((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ ((g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))) :=
  congrArg (fun T : Z.Opens => U.ι ''ᵁ (U.ι ⁻¹ᵁ T))
    (image_comp_opens (g ⁻¹ᵁ U).ι g ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))

/-- The two factorisations of `X' ∩ U ⟶ Z`, inside the image. -/
public theorem comparisonOpen_eq₃ :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ ((interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) :=
  congrArg (fun T : Z.Opens => U.ι ''ᵁ (U.ι ⁻¹ᵁ T))
    (image_congr (interToFst_comp U g) ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))

/-- The image of `X' ∩ U ∩ V` along `X' ∩ U ⟶ U ⟶ Z`, written with the two images. -/
public theorem comparisonOpen_eq₄ :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ (U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ ((interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) :=
  congrArg (fun T : Z.Opens => U.ι ''ᵁ (U.ι ⁻¹ᵁ T))
    (image_comp_opens (interToFst U g) U.ι ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)).symm

/-- The counit factor cancels the preimage of an image. -/
public theorem comparisonOpen_eq₅ :
    U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))) :=
  (congrArg (fun T : U.toScheme.Opens => U.ι ''ᵁ T)
    (U.ι.preimage_image_eq (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))).symm

/-- The image along `X' ∩ U ⟶ U ⟶ Z`, written with the composite. -/
public theorem comparisonOpen_eq₆ :
    (interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V) =
      U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)) :=
  image_comp_opens (interToFst U g) U.ι ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)

/-- The two factorisations of `X' ∩ U ⟶ Z`. -/
public theorem comparisonOpen_eq₇ :
    ((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V) =
      (interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V) :=
  image_congr (interToFst_comp U g).symm ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)

/-- The image along `X' ∩ U ⟶ X' ⟶ Z`, written with the two images. -/
public theorem comparisonOpen_eq₈ :
    g ''ᵁ ((g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)) =
      ((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V) :=
  (image_comp_opens (g ⁻¹ᵁ U).ι g ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)).symm

/-- The open the first 2 factors of the comparison restrict the coefficient module
to. -/
public theorem comparisonOpen_eqUpTo₂ :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ (((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) :=
  (comparisonOpen_eq₂ U g V).trans (comparisonOpen_eq₁ U g V)

/-- The open the first 3 factors of the comparison restrict the coefficient module
to. -/
public theorem comparisonOpen_eqUpTo₃ :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ ((interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) :=
  (comparisonOpen_eq₃ U g V).trans (comparisonOpen_eqUpTo₂ U g V)

/-- The open the first 4 factors of the comparison restrict the coefficient module
to. -/
public theorem comparisonOpen_eqUpTo₄ :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ (U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) :=
  (comparisonOpen_eq₄ U g V).trans (comparisonOpen_eqUpTo₃ U g V)

/-- The open the first 5 factors of the comparison restrict the coefficient module
to. -/
public theorem comparisonOpen_eqUpTo₅ :
    U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) :=
  (comparisonOpen_eq₅ U g V).trans (comparisonOpen_eqUpTo₄ U g V)

/-- The open the first 6 factors of the comparison restrict the coefficient module
to. -/
public theorem comparisonOpen_eqUpTo₆ :
    (interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) :=
  (comparisonOpen_eq₆ U g V).trans (comparisonOpen_eqUpTo₅ U g V)

/-- The open the first 7 factors of the comparison restrict the coefficient module
to. -/
public theorem comparisonOpen_eqUpTo₇ :
    ((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) :=
  (comparisonOpen_eq₇ U g V).trans (comparisonOpen_eqUpTo₆ U g V)

/-! ### The eight factors on sections

Each of the eight factors of the comparison has, on an open `V` of `X'`, the effect of a single
restriction map of the coefficient module, along the corresponding equality of opens above.  The
statements below are *typed in the `Γ(M, Oᵢ)` spelling*: each costs exactly one identification
of `Γ(Gᵢ.obj M, V)` with `Γ(M, Oᵢ)`, so each is cheap, and chaining them by `rw` never leaves
that spelling. -/

variable (M : Z.Modules)

/-- Factor 1 of the comparison restricts a section along `comparisonOpen_eq₁`. -/
public theorem comparisonFactor₁_app_apply
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₁ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₁ U g V)).op z := rfl

/-- Factor 2 of the comparison restricts a section along `comparisonOpen_eq₂`. -/
public theorem comparisonFactor₂_app_apply
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ ((g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))))) :
    ((comparisonFactor₂ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₂ U g V)).op z := rfl

/-- Factor 3 of the comparison restricts a section along `comparisonOpen_eq₃`. -/
public theorem comparisonFactor₃_app_apply
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))))) :
    ((comparisonFactor₃ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₃ U g V)).op z := rfl

/-- Factor 4 of the comparison restricts a section along `comparisonOpen_eq₄`. -/
public theorem comparisonFactor₄_app_apply
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ ((interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))))) :
    ((comparisonFactor₄ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₄ U g V)).op z := rfl

/-- Factor 5 of the comparison restricts a section along `comparisonOpen_eq₅`. -/
public theorem comparisonFactor₅_app_apply
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))))) :
    ((comparisonFactor₅ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₅ U g V)).op z := rfl

/-- Factor 6 of the comparison restricts a section along `comparisonOpen_eq₆`. -/
public theorem comparisonFactor₆_app_apply
    (z : Γ(M, U.ι ''ᵁ (interToFst U g ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V)))) :
    ((comparisonFactor₆ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₆ U g V)).op z := rfl

/-- Factor 7 of the comparison restricts a section along `comparisonOpen_eq₇`. -/
public theorem comparisonFactor₇_app_apply
    (z : Γ(M, (interToFst U g ≫ U.ι) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) :
    ((comparisonFactor₇ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₇ U g V)).op z := rfl

/-- Factor 8 of the comparison restricts a section along `comparisonOpen_eq₈`. -/
public theorem comparisonFactor₈_app_apply
    (z : Γ(M, ((g ⁻¹ᵁ U).ι ≫ g) ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ V))) :
    ((comparisonFactor₈ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₈ U g V)).op z := rfl

/-! ### The comparison on sections

The eight factors are applied one at a time along the chain of partial composites in which
`restrictPushforwardRestrictIso` is written, and each step is spread over several declarations.
Keeping them apart is what makes the reduction go through.  An identification of
`Γ(Gᵢ.obj M, V)` with `Γ(M, Oᵢ)` — unavoidable, since the whole point is to read the comparison
as a restriction map of `M` — costs a sizeable fraction of the heartbeat budget, and for the two
intermediate opens with the most restriction functors stacked over them it costs more than half,
so no declaration may mention both of those.  The chain is grouped from the left so that every
declaration mentions `Γ(M, O₀)` and at most one other such group, and the collapse of two
accumulated restriction maps into one is done by rewriting the *right*-hand side, where both
sides are already `Γ(M, _)` and the rewrite is free. -/

/-- The first 2 factors of the comparison applied to a section is factor 2 applied to the
previous partial composite applied to it. -/
public theorem comparisonChain₂_app_apply_eq_factors (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₂ U g).hom.app M).app V z =
      ((comparisonFactor₂ U g).hom.app M).app V
        (((comparisonFactor₁ U g).hom.app M).app V z) :=
  trans_hom_app_app (comparisonFactor₁ U g) (comparisonFactor₂ U g) M V z

/-- The previous partial composite rewritten inside factor 2. -/
public theorem comparisonChain₂_app_apply_eq_factor (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₂ U g).hom.app M).app V
        (((comparisonFactor₁ U g).hom.app M).app V z) =
      ((comparisonFactor₂ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eq₁ U g V)).op z) :=
  congrArg (fun y => ((comparisonFactor₂ U g).hom.app M).app V y)
    (comparisonFactor₁_app_apply U g V M z)

/-- Factor 2 of the comparison applied to a section already restricted by the previous
factors. -/
public theorem comparisonFactor₂_app_apply_restricted (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₂ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eq₁ U g V)).op z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₂ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eq₁ U g V)).op z) :=
  comparisonFactor₂_app_apply U g V M _

/-- The first 2 factors of the comparison applied to a section, as the restriction map the
previous factors contribute followed by the one factor 2 contributes. -/
public theorem comparisonChain₂_app_apply_eq_maps (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₂ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₂ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eq₁ U g V)).op z) := by
  rw [comparisonChain₂_app_apply_eq_factors, comparisonChain₂_app_apply_eq_factor,
    comparisonFactor₂_app_apply_restricted]

/-- **The first 2 factors of the comparison, on sections.** -/
public theorem comparisonChain₂_app_apply (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₂ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₂ U g V)).op z :=
  (comparisonChain₂_app_apply_eq_maps U g V M z).trans
    (collapseStep M (comparisonOpen_eq₁ U g V) (comparisonOpen_eq₂ U g V)
      (comparisonOpen_eqUpTo₂ U g V) z)

/-- The first 3 factors of the comparison applied to a section is factor 3 applied to the
previous partial composite applied to it. -/
public theorem comparisonChain₃_app_apply_eq_factors (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₃ U g).hom.app M).app V z =
      ((comparisonFactor₃ U g).hom.app M).app V
        (((comparisonChain₂ U g).hom.app M).app V z) :=
  trans_hom_app_app (comparisonChain₂ U g) (comparisonFactor₃ U g) M V z

/-- The previous partial composite rewritten inside factor 3. -/
public theorem comparisonChain₃_app_apply_eq_factor (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₃ U g).hom.app M).app V
        (((comparisonChain₂ U g).hom.app M).app V z) =
      ((comparisonFactor₃ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₂ U g V)).op z) :=
  congrArg (fun y => ((comparisonFactor₃ U g).hom.app M).app V y)
    (comparisonChain₂_app_apply U g V M z)

/-- Factor 3 of the comparison applied to a section already restricted by the previous
factors. -/
public theorem comparisonFactor₃_app_apply_restricted (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₃ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₂ U g V)).op z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₃ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₂ U g V)).op z) :=
  comparisonFactor₃_app_apply U g V M _

/-- The first 3 factors of the comparison applied to a section, as the restriction map the
previous factors contribute followed by the one factor 3 contributes. -/
public theorem comparisonChain₃_app_apply_eq_maps (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₃ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₃ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₂ U g V)).op z) := by
  rw [comparisonChain₃_app_apply_eq_factors, comparisonChain₃_app_apply_eq_factor,
    comparisonFactor₃_app_apply_restricted]

/-- **The first 3 factors of the comparison, on sections.** -/
public theorem comparisonChain₃_app_apply (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₃ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₃ U g V)).op z :=
  (comparisonChain₃_app_apply_eq_maps U g V M z).trans
    (collapseStep M (comparisonOpen_eqUpTo₂ U g V) (comparisonOpen_eq₃ U g V)
      (comparisonOpen_eqUpTo₃ U g V) z)

/-- The first 4 factors of the comparison applied to a section is factor 4 applied to the
previous partial composite applied to it. -/
public theorem comparisonChain₄_app_apply_eq_factors (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₄ U g).hom.app M).app V z =
      ((comparisonFactor₄ U g).hom.app M).app V
        (((comparisonChain₃ U g).hom.app M).app V z) :=
  trans_hom_app_app (comparisonChain₃ U g) (comparisonFactor₄ U g) M V z

/-- The previous partial composite rewritten inside factor 4. -/
public theorem comparisonChain₄_app_apply_eq_factor (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₄ U g).hom.app M).app V
        (((comparisonChain₃ U g).hom.app M).app V z) =
      ((comparisonFactor₄ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₃ U g V)).op z) :=
  congrArg (fun y => ((comparisonFactor₄ U g).hom.app M).app V y)
    (comparisonChain₃_app_apply U g V M z)

/-- Factor 4 of the comparison applied to a section already restricted by the previous
factors. -/
public theorem comparisonFactor₄_app_apply_restricted (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₄ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₃ U g V)).op z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₄ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₃ U g V)).op z) :=
  comparisonFactor₄_app_apply U g V M _

/-- The first 4 factors of the comparison applied to a section, as the restriction map the
previous factors contribute followed by the one factor 4 contributes. -/
public theorem comparisonChain₄_app_apply_eq_maps (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₄ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₄ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₃ U g V)).op z) := by
  rw [comparisonChain₄_app_apply_eq_factors, comparisonChain₄_app_apply_eq_factor,
    comparisonFactor₄_app_apply_restricted]

/-- **The first 4 factors of the comparison, on sections.** -/
public theorem comparisonChain₄_app_apply (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₄ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₄ U g V)).op z :=
  (comparisonChain₄_app_apply_eq_maps U g V M z).trans
    (collapseStep M (comparisonOpen_eqUpTo₃ U g V) (comparisonOpen_eq₄ U g V)
      (comparisonOpen_eqUpTo₄ U g V) z)

/-- The first 5 factors of the comparison applied to a section is factor 5 applied to the
previous partial composite applied to it. -/
public theorem comparisonChain₅_app_apply_eq_factors (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₅ U g).hom.app M).app V z =
      ((comparisonFactor₅ U g).hom.app M).app V
        (((comparisonChain₄ U g).hom.app M).app V z) :=
  trans_hom_app_app (comparisonChain₄ U g) (comparisonFactor₅ U g) M V z

/-- The previous partial composite rewritten inside factor 5. -/
public theorem comparisonChain₅_app_apply_eq_factor (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₅ U g).hom.app M).app V
        (((comparisonChain₄ U g).hom.app M).app V z) =
      ((comparisonFactor₅ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₄ U g V)).op z) :=
  congrArg (fun y => ((comparisonFactor₅ U g).hom.app M).app V y)
    (comparisonChain₄_app_apply U g V M z)

/-- Factor 5 of the comparison applied to a section already restricted by the previous
factors. -/
public theorem comparisonFactor₅_app_apply_restricted (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₅ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₄ U g V)).op z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₅ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₄ U g V)).op z) :=
  comparisonFactor₅_app_apply U g V M _

/-- The first 5 factors of the comparison applied to a section, as the restriction map the
previous factors contribute followed by the one factor 5 contributes. -/
public theorem comparisonChain₅_app_apply_eq_maps (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₅ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₅ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₄ U g V)).op z) := by
  rw [comparisonChain₅_app_apply_eq_factors, comparisonChain₅_app_apply_eq_factor,
    comparisonFactor₅_app_apply_restricted]

/-- **The first 5 factors of the comparison, on sections.** -/
public theorem comparisonChain₅_app_apply (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₅ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₅ U g V)).op z :=
  (comparisonChain₅_app_apply_eq_maps U g V M z).trans
    (collapseStep M (comparisonOpen_eqUpTo₄ U g V) (comparisonOpen_eq₅ U g V)
      (comparisonOpen_eqUpTo₅ U g V) z)

/-- The first 6 factors of the comparison applied to a section is factor 6 applied to the
previous partial composite applied to it. -/
public theorem comparisonChain₆_app_apply_eq_factors (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₆ U g).hom.app M).app V z =
      ((comparisonFactor₆ U g).hom.app M).app V
        (((comparisonChain₅ U g).hom.app M).app V z) :=
  trans_hom_app_app (comparisonChain₅ U g) (comparisonFactor₆ U g) M V z

/-- The previous partial composite rewritten inside factor 6. -/
public theorem comparisonChain₆_app_apply_eq_factor (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₆ U g).hom.app M).app V
        (((comparisonChain₅ U g).hom.app M).app V z) =
      ((comparisonFactor₆ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₅ U g V)).op z) :=
  congrArg (fun y => ((comparisonFactor₆ U g).hom.app M).app V y)
    (comparisonChain₅_app_apply U g V M z)

/-- Factor 6 of the comparison applied to a section already restricted by the previous
factors. -/
public theorem comparisonFactor₆_app_apply_restricted (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₆ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₅ U g V)).op z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₆ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₅ U g V)).op z) :=
  comparisonFactor₆_app_apply U g V M _

/-- The first 6 factors of the comparison applied to a section, as the restriction map the
previous factors contribute followed by the one factor 6 contributes. -/
public theorem comparisonChain₆_app_apply_eq_maps (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₆ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₆ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₅ U g V)).op z) := by
  rw [comparisonChain₆_app_apply_eq_factors, comparisonChain₆_app_apply_eq_factor,
    comparisonFactor₆_app_apply_restricted]

/-- **The first 6 factors of the comparison, on sections.** -/
public theorem comparisonChain₆_app_apply (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₆ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₆ U g V)).op z :=
  (comparisonChain₆_app_apply_eq_maps U g V M z).trans
    (collapseStep M (comparisonOpen_eqUpTo₅ U g V) (comparisonOpen_eq₆ U g V)
      (comparisonOpen_eqUpTo₆ U g V) z)

/-- The first 7 factors of the comparison applied to a section is factor 7 applied to the
previous partial composite applied to it. -/
public theorem comparisonChain₇_app_apply_eq_factors (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₇ U g).hom.app M).app V z =
      ((comparisonFactor₇ U g).hom.app M).app V
        (((comparisonChain₆ U g).hom.app M).app V z) :=
  trans_hom_app_app (comparisonChain₆ U g) (comparisonFactor₇ U g) M V z

/-- The previous partial composite rewritten inside factor 7. -/
public theorem comparisonChain₇_app_apply_eq_factor (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₇ U g).hom.app M).app V
        (((comparisonChain₆ U g).hom.app M).app V z) =
      ((comparisonFactor₇ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₆ U g V)).op z) :=
  congrArg (fun y => ((comparisonFactor₇ U g).hom.app M).app V y)
    (comparisonChain₆_app_apply U g V M z)

/-- Factor 7 of the comparison applied to a section already restricted by the previous
factors. -/
public theorem comparisonFactor₇_app_apply_restricted (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₇ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₆ U g V)).op z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₇ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₆ U g V)).op z) :=
  comparisonFactor₇_app_apply U g V M _

/-- The first 7 factors of the comparison applied to a section, as the restriction map the
previous factors contribute followed by the one factor 7 contributes. -/
public theorem comparisonChain₇_app_apply_eq_maps (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₇ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eq₇ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₆ U g V)).op z) := by
  rw [comparisonChain₇_app_apply_eq_factors, comparisonChain₇_app_apply_eq_factor,
    comparisonFactor₇_app_apply_restricted]

/-- **The first 7 factors of the comparison, on sections.** -/
public theorem comparisonChain₇_app_apply (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonChain₇ U g).hom.app M).app V z =
      M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₇ U g V)).op z :=
  (comparisonChain₇_app_apply_eq_maps U g V M z).trans
    (collapseStep M (comparisonOpen_eqUpTo₆ U g V) (comparisonOpen_eq₇ U g V)
      (comparisonOpen_eqUpTo₇ U g V) z)

/-- The comparison applied to a section is factor 8 applied to the
previous partial composite applied to it. -/
public theorem restrictPushforwardRestrictIso_app_apply_eq_factors
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((restrictPushforwardRestrictIso U g).hom.app M).app V z =
      ((comparisonFactor₈ U g).hom.app M).app V
        (((comparisonChain₇ U g).hom.app M).app V z) :=
  trans_hom_app_app (comparisonChain₇ U g) (comparisonFactor₈ U g) M V z

/-- The previous partial composite rewritten inside factor 8. -/
public theorem restrictPushforwardRestrictIso_app_apply_eq_factor
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₈ U g).hom.app M).app V
        (((comparisonChain₇ U g).hom.app M).app V z) =
      ((comparisonFactor₈ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₇ U g V)).op z) :=
  congrArg (fun y => ((comparisonFactor₈ U g).hom.app M).app V y)
    (comparisonChain₇_app_apply U g V M z)

/-- Factor 8 of the comparison applied to a section already restricted by the previous
factors. -/
public theorem comparisonFactor₈_app_apply_restricted (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((comparisonFactor₈ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₇ U g V)).op z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₈ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₇ U g V)).op z) :=
  comparisonFactor₈_app_apply U g V M _

/-- The comparison applied to a section is factor 8 applied to the section restricted by the
first seven factors. -/
public theorem restrictPushforwardRestrictIso_app_apply_eq_factor₈
    (z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)))) :
    ((restrictPushforwardRestrictIso U g).hom.app M).app V z =
      ((comparisonFactor₈ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₇ U g V)).op z) :=
  (restrictPushforwardRestrictIso_app_apply_eq_factors U g V M z).trans
    (restrictPushforwardRestrictIso_app_apply_eq_factor U g V M z)

end Stacks.Perfect.PushforwardRestrict

end

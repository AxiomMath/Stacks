module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeCohomologyAndColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The long exact sequence of native sheaf cohomology over an open

The degree induction of Stacks 0A37 runs on a short exact sequence `0 → 𝒜 → 𝒢 → 𝒬 → 0` of
systems of abelian sheaves with `𝒢` stagewise injective
(`StacksDraft.Ch20.Sec16.Tag0A37InjectiveEmbedding`, whose embedding is short exact at every
stage by `SpectralDiagram.AbelianSystem.shortExact_map_ev`).  What the induction consumes from
such a sequence is the long exact cohomology sequence over a fixed open of a fixed stage, in
Mathlib's native `Sheaf.H'` spelling.  **This file supplies it.**

The content is already in Mathlib, and the only thing between the two is a definitional
unfolding that `StacksDraft.Ch20.Sec16.Tag0A37Colimits` records as
`Stacks.Cohomology.AbelianColimit.H'functor_eq_extFunctorObj`: native cohomology over `U`, read
as a functor in the sheaf variable, **is** the `Ext`-functor out of the free abelian sheaf
`freeOfOpen U` on `yoneda.obj U`.  Mathlib's covariant long exact sequence of `Ext`,
`CategoryTheory.Abelian.Ext.covariantSequence_exact`, is therefore the long exact sequence of
`Sheaf.H'` on the nose: the arrow `Ext.mk₀ S.f |>.postcomp (freeOfOpen U) (add_zero n)` out of
which Mathlib builds its sequence is *syntactically* reducible to `(H'functor U n).map S.f`, so
every statement below is proved by handing Mathlib's statement back with the maps renamed.

## Main definitions

* `H'δ` is the connecting map `Hⁿ⁰(U, 𝒬) ⟶ Hⁿ¹(U, 𝒜)`, namely postcomposition with the `Ext`-class
  of the short exact sequence.
* `H'longExactSequence` is the six-term sequence
  `Hⁿ⁰(U, 𝒜) → Hⁿ⁰(U, 𝒢) → Hⁿ⁰(U, 𝒬) → Hⁿ¹(U, 𝒜) → Hⁿ¹(U, 𝒢) → Hⁿ¹(U, 𝒬)`.

## Main results

* `H'longExactSequence_exact`: that sequence is exact.
* `shortComplex_H'_exact₂`, `shortComplex_H'_exact₃`, `shortComplex_H'_exact₁`: the three
  three-term pieces, which is the form a consumer that wants exactness at one spot applies.
* `mono_H'map_zero_of_mono`: in degree zero the sequence begins with a monomorphism, so the full
  sequence starts `0 → H⁰(U, 𝒜) → H⁰(U, 𝒢) → ⋯`.
* `epi_H'δ_of_isZero`, `mono_H'δ_of_isZero` and `isIso_H'δ_of_isZero`: **dimension shifting.**
  When the middle sheaf has vanishing cohomology in both degrees — the case the induction is run
  in, `𝒢` being injective — the connecting map is an isomorphism `Hⁿ⁰(U, 𝒬) ≅ Hⁿ¹(U, 𝒜)`.  This
  is the step that moves the 0A37 comparison from degree `n₀` to degree `n₁`.

## Implementation notes

Everything is stated in the `H'functor` spelling of `Tag0A37Colimits`, i.e. the arrows are
`(H'functor U n).map S.f` rather than the `Ext`-postcomposition they unfold to, and the objects
are `(H'functor U n).obj F`, which is `Sheaf.H' F n U` by `H'functor_obj`.  Keeping to one
spelling matters here: the two differ by unfolding a `def`, so a statement that mixes them
forces repeated instance unification across the two.

As in `Tag0A37Colimits`, the ambient space is a `Type u` with a topology rather than a `TopCat`,
because `TopCat.Sheaf` is a semireducible `def` over `Sheaf (Opens.grothendieckTopology X)` and
the `HasExt` instance that Mathlib's `Ext` long exact sequence needs is not found at the
`X.Sheaf` spelling.  A consumer holding `X : TopCat` applies these with `(X : Type u)`; the
sheaves and opens then need no translation, since `X.Sheaf AddCommGrpCat` and `Opens ↑X` are the
same types.

The element-level forms of exactness are Mathlib's `Ext.covariant_sequence_exact₁`,
`Ext.covariant_sequence_exact₂` and `Ext.covariant_sequence_exact₃`, applicable through
`H'functor_eq_extFunctorObj` without any statement of their own here.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 0156](https://stacks.math.columbia.edu/tag/0156)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Abelian

universe u

namespace Stacks.Cohomology.AbelianColimit

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

/-- Native cohomology over an open is an additive functor in the sheaf variable, being the
`Ext`-functor out of `freeOfOpen U`.  The instance is stated at the `H'functor` spelling because
that is the one the statements below are in, and instances do not cross the unfolding. -/
instance additive_H'functor (U : Opens X) (n : ℕ) : (H'functor U n).Additive :=
  inferInstanceAs (extFunctorObj (freeOfOpen U) n).Additive

/-! ### The connecting map -/

/-- **The connecting map of the long exact cohomology sequence over an open**,
`Hⁿ⁰(U, S.X₃) ⟶ Hⁿ¹(U, S.X₁)` for `n₀ + 1 = n₁`.  It is postcomposition with the `Ext`-class
`S.ShortExact.extClass : Ext S.X₃ S.X₁ 1` of the short exact sequence, under the identification
of cohomology over `U` with `Ext` out of `freeOfOpen U`. -/
def H'δ (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (H'functor U n₀).obj S.X₃ ⟶ (H'functor U n₁).obj S.X₁ :=
  AddCommGrpCat.ofHom (hS.extClass.postcomp (freeOfOpen U) h)

/-- The connecting map is the postcomposition with the `Ext`-class that Mathlib's long exact
sequence of `Ext` uses, so the two sequences have the same arrows. -/
theorem H'δ_eq_postcomp_extClass (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ}
    (h : n₀ + 1 = n₁) :
    H'δ hS U h = AddCommGrpCat.ofHom (hS.extClass.postcomp (freeOfOpen U) h) :=
  rfl

/-- The arrows of the long exact sequence that come from the sheaf maps are the functorial maps
on native cohomology, and are Mathlib's `Ext`-postcompositions by unfolding. -/
theorem H'map_eq_postcomp_mk₀ (U : Opens X) (n : ℕ)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (H'functor U n).map φ =
      AddCommGrpCat.ofHom ((Ext.mk₀ φ).postcomp (freeOfOpen U) (add_zero n)) :=
  rfl

/-! ### The two composites through the connecting map vanish

Both squares are stated purely in the `Ext`-postcomposition spelling that `H'functor` and `H'δ`
unfold to, and each is used as the `w` field of a `ShortComplex` whose arrows are the `H'functor`
spelling, where the definitional equality is checked once, in term position.  Stating them at the
`H'functor` spelling and unfolding `H'δ` inside the tactic block instead does not work: under a
composition the unfolded goal is not type-correct at `implicit` transparency.

The `change` is doing real work and is not decoration.  `postcomp` is an `abbrev` for the flip of
`Ext.bilinearComp`, so the goal after `ext` is a pair of nested `bilinearComp` applications, which
the `comp_assoc` lemmas — stated for `Ext.comp` — do not match; `dsimp` leaves it in that shape
and the rewrite then makes no progress. -/

/-- The sheaf map `S.g` followed by the connecting map is zero. -/
theorem postcomp_mk₀_g_comp_postcomp_extClass (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ}
    (h : n₀ + 1 = n₁) :
    AddCommGrpCat.ofHom ((Ext.mk₀ S.g).postcomp (freeOfOpen U) (add_zero n₀)) ≫
        AddCommGrpCat.ofHom (hS.extClass.postcomp (freeOfOpen U) h) = 0 := by
  ext x
  change (Ext.comp x (Ext.mk₀ S.g) (add_zero n₀)).comp hS.extClass h = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- The connecting map followed by the sheaf map `S.f` is zero. -/
theorem postcomp_extClass_comp_postcomp_mk₀_f (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ}
    (h : n₀ + 1 = n₁) :
    AddCommGrpCat.ofHom (hS.extClass.postcomp (freeOfOpen U) h) ≫
        AddCommGrpCat.ofHom ((Ext.mk₀ S.f).postcomp (freeOfOpen U) (add_zero n₁)) = 0 := by
  ext x
  change (Ext.comp x hS.extClass h).comp (Ext.mk₀ S.f) (add_zero n₁) = 0
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

/-! ### The three three-term exact pieces -/

/-- **Exactness of the cohomology sequence at the middle sheaf**, in every degree:
`Hⁿ(U, S.X₁) → Hⁿ(U, S.X₂) → Hⁿ(U, S.X₃)` is exact.  This is
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₂'` out of `freeOfOpen U`. -/
@[sga "4 V 2.1.1" "Exactness Ext^n(M", sga "7 VII 3.3.6" "Exactness at Extⁿ(L•"]
theorem shortComplex_H'_exact₂ (hS : S.ShortExact) (U : Opens X) (n : ℕ) :
    (ShortComplex.mk ((H'functor U n).map S.f) ((H'functor U n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  Ext.covariant_sequence_exact₂' (freeOfOpen U) hS n

/-- **Exactness of the cohomology sequence at the quotient sheaf**:
`Hⁿ⁰(U, S.X₂) → Hⁿ⁰(U, S.X₃) → Hⁿ¹(U, S.X₁)` is exact when `n₀ + 1 = n₁`.  This is
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'` out of `freeOfOpen U`. -/
@[ega "III 4.1.7.21" "Exactness at H_k", sga "4 V 2.1.1" "Exactness Ext^{n0}(M"]
theorem shortComplex_H'_exact₃ (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (ShortComplex.mk ((H'functor U n₀).map S.g) (H'δ hS U h)
      (postcomp_mk₀_g_comp_postcomp_extClass hS U h)).Exact :=
  Ext.covariant_sequence_exact₃' (freeOfOpen U) hS n₀ n₁ h

/-- **Exactness of the cohomology sequence at the sub-sheaf in the next degree**:
`Hⁿ⁰(U, S.X₃) → Hⁿ¹(U, S.X₁) → Hⁿ¹(U, S.X₂)` is exact when `n₀ + 1 = n₁`.  This is
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'` out of `freeOfOpen U`. -/
@[sga "4 V 2.1.1" "Exactness Ext^{n0}(M", sga "7 VII 3.3.6" "Exactness at Extⁿ⁰⁺¹(L•"]
theorem shortComplex_H'_exact₁ (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (H'δ hS U h) ((H'functor U n₁).map S.f)
      (postcomp_extClass_comp_postcomp_mk₀_f hS U h)).Exact :=
  Ext.covariant_sequence_exact₁' (freeOfOpen U) hS n₀ n₁ h

/-! ### The six-term sequence -/

/-- **The long exact sequence of native sheaf cohomology over an open.**  For a short exact
sequence `S` of abelian sheaves on the site of opens of `X`, an open `U` and `n₀ + 1 = n₁`, this
is the six-term sequence
`Hⁿ⁰(U, S.X₁) → Hⁿ⁰(U, S.X₂) → Hⁿ⁰(U, S.X₃) → Hⁿ¹(U, S.X₁) → Hⁿ¹(U, S.X₂) → Hⁿ¹(U, S.X₃)`,
the outer four arrows being the functorial maps on cohomology and the middle one the connecting
map `H'δ`. -/
def H'longExactSequence (hS : S.ShortExact) (U : Opens X) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅ ((H'functor U n₀).map S.f) ((H'functor U n₀).map S.g) (H'δ hS U h)
    ((H'functor U n₁).map S.f) ((H'functor U n₁).map S.g)

/-- **The long exact sequence of native sheaf cohomology over an open is exact.**  This is
`CategoryTheory.Abelian.Ext.covariantSequence_exact` out of `freeOfOpen U`. -/
@[sga "4½ Arcata 1.6.5" "partial"]
theorem H'longExactSequence_exact (hS : S.ShortExact) (U : Opens X) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) :
    (H'longExactSequence hS U n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact (freeOfOpen U) hS n₀ n₁ h

/-! ### The left end of the sequence -/

/-- **In degree zero the sequence starts with a monomorphism.**  Together with
`shortComplex_H'_exact₂` this says the long exact sequence begins
`0 → H⁰(U, S.X₁) → H⁰(U, S.X₂) → H⁰(U, S.X₃) → H¹(U, S.X₁) → ⋯`.  The input is that `S.f` is a
monomorphism, which is part of `S.ShortExact`. -/
theorem mono_H'map_zero_of_mono (hS : S.ShortExact) (U : Opens X) :
    Mono ((H'functor U 0).map S.f) :=
  have := hS.mono_f
  Ext.mono_postcomp_mk₀_of_mono (freeOfOpen U) S.f

/-! ### Dimension shifting -/

/-- **The connecting map is an epimorphism when the middle sheaf has no cohomology in the upper
degree.**  Exactness of `Hⁿ⁰(U, S.X₃) → Hⁿ¹(U, S.X₁) → Hⁿ¹(U, S.X₂)` makes the image of the
connecting map the kernel of the second arrow, and that arrow is zero because its target is. -/
theorem epi_H'δ_of_isZero (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (hz : IsZero ((H'functor U n₁).obj S.X₂)) : Epi (H'δ hS U h) :=
  (shortComplex_H'_exact₁ hS U h).epi_f (hz.eq_zero_of_tgt _)

/-- **The connecting map is a monomorphism when the middle sheaf has no cohomology in the lower
degree.**  Exactness of `Hⁿ⁰(U, S.X₂) → Hⁿ⁰(U, S.X₃) → Hⁿ¹(U, S.X₁)` makes the kernel of the
connecting map the image of the first arrow, and that arrow is zero because its source is. -/
theorem mono_H'δ_of_isZero (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (hz : IsZero ((H'functor U n₀).obj S.X₂)) : Mono (H'δ hS U h) :=
  (shortComplex_H'_exact₃ hS U h).mono_g (hz.eq_zero_of_src _)

/-- **Dimension shifting over an open.**  If the middle sheaf of a short exact sequence has
vanishing cohomology over `U` in both degrees `n₀` and `n₁ = n₀ + 1` — the situation the degree
induction of Stacks 0A37 is run in, the middle sheaf there being injective — then the connecting
map is an isomorphism `Hⁿ⁰(U, S.X₃) ≅ Hⁿ¹(U, S.X₁)`.

This is the step that carries a statement about cohomology of `S.X₃` in degree `n₀` to the same
statement about cohomology of `S.X₁` in degree `n₁`. -/
theorem isIso_H'δ_of_isZero (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (hz₀ : IsZero ((H'functor U n₀).obj S.X₂))
    (hz₁ : IsZero ((H'functor U n₁).obj S.X₂)) : IsIso (H'δ hS U h) :=
  have := mono_H'δ_of_isZero hS U h hz₀
  have := epi_H'δ_of_isZero hS U h hz₁
  isIso_of_mono_of_epi _

/-- **Dimension shifting over an open, as an isomorphism.** -/
def H'δIso (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (hz₀ : IsZero ((H'functor U n₀).obj S.X₂))
    (hz₁ : IsZero ((H'functor U n₁).obj S.X₂)) :
    (H'functor U n₀).obj S.X₃ ≅ (H'functor U n₁).obj S.X₁ :=
  have := isIso_H'δ_of_isZero hS U h hz₀ hz₁
  asIso (H'δ hS U h)

/-- The isomorphism of `H'δIso` is the connecting map. -/
@[simp]
theorem H'δIso_hom (hS : S.ShortExact) (U : Opens X) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (hz₀ : IsZero ((H'functor U n₀).obj S.X₂))
    (hz₁ : IsZero ((H'functor U n₁).obj S.X₂)) :
    (H'δIso hS U h hz₀ hz₁).hom = H'δ hS U h :=
  rfl

end Stacks.Cohomology.AbelianColimit

end

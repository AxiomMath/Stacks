module

import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.ENatToNat
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing
import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.Shift
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle
import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Triangulated.Functor
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Leray

/-!
# The higher right derived functors as a universal δ-functor

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, where `𝒜` has enough
injectives. The family `{R ⁱ F, δ}_{i ≥ 0}` is a cohomological `δ`-functor, universal as soon as
every object of `𝒜` embeds into a right acyclic object ([Stacks, Tag 05TE], via Grothendieck's
criterion [Stacks, Tag 010T]). The file also proves that right derived functors move cohomology
to the right ([Stacks, Tag 05TC]).

## Main results

* `CategoryTheory.Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal`
* `CategoryTheory.Functor.isGE_and_isIso_homologyFunctor_map_of_isRightDerivedValueAt`

## References

* [Stacks, Tag 05TE]
* [Stacks, Tag 010Q] and [Stacks, Tag 010T]
* [Stacks, Tag 05TC]
-/

@[expose] public section

universe v₁ v₂ v₃ w₁ w₂ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory.Functor

open _root_.DerivedCategory

-- As in `RightDerivedFunctorInjective.Exactness`, the instance deriving the conclusion of
-- `hasPointwiseRightDerivedFunctorAt_of_injective` from `EnoughInjectives 𝒜` takes precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Abelian

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- The short exact sequence `0 ⟶ X ⟶ Y ⟶ Y/X ⟶ 0` attached to a monomorphism `u : X ⟶ Y`. -/
private noncomputable abbrev cokerSC {X Y : 𝒜} (u : X ⟶ Y) : ShortComplex 𝒜 :=
  ShortComplex.mk u (cokernel.π u) (cokernel.condition u)

private lemma shortExact_cokerSC {X Y : 𝒜} (u : X ⟶ Y) (hu : Mono u) :
    (cokerSC u).ShortExact :=
  have := hu
  { exact := ShortComplex.exact_cokernel u }

/-- The morphism of short exact sequences `cokerSC u ⟶ cokerSC u'` induced by a commutative
square with vertical morphisms `u` and `u'`. -/
private noncomputable def cokerSCMap {X Y X' Y' : 𝒜} (u : X ⟶ Y) (u' : X' ⟶ Y') (a : X ⟶ X')
    (b : Y ⟶ Y') (w : u ≫ b = a ≫ u') : cokerSC u ⟶ cokerSC u' where
  τ₁ := a
  τ₂ := b
  τ₃ := cokernel.map u u' a b w
  comm₁₂ := w.symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- For a short exact sequence `S : 0 ⟶ A ⟶ B ⟶ C ⟶ 0` and a morphism `u : A ⟶ M`, the morphism
`A ⟶ B ⊞ M` with components `S.f` and `-u`; its cokernel is the pushout of `S.f` along `u`. -/
private noncomputable def toBiprod (S : ShortComplex 𝒜) {M : 𝒜} (u : S.X₁ ⟶ M) :
    S.X₁ ⟶ S.X₂ ⊞ M :=
  biprod.lift S.f (-u)

private lemma toBiprod_fst (S : ShortComplex 𝒜) {M : 𝒜} (u : S.X₁ ⟶ M) :
    toBiprod S u ≫ biprod.fst = S.f :=
  biprod.lift_fst _ _

private lemma toBiprod_snd (S : ShortComplex 𝒜) {M : 𝒜} (u : S.X₁ ⟶ M) :
    toBiprod S u ≫ biprod.snd = -u :=
  biprod.lift_snd _ _

private lemma toBiprod_eq (S : ShortComplex 𝒜) {M : 𝒜} (u : S.X₁ ⟶ M) :
    toBiprod S u = S.f ≫ biprod.inl - u ≫ biprod.inr := by
  rw [toBiprod, biprod.lift_eq, Preadditive.neg_comp, sub_eq_add_neg]

private lemma mono_toBiprod (S : ShortComplex 𝒜) (hS : S.ShortExact) {M : 𝒜} (u : S.X₁ ⟶ M) :
    Mono (toBiprod S u) :=
  have := hS.mono_f
  mono_of_mono_fac (toBiprod_fst S u)

/-- The short complex `0 ⟶ M ⟶ (B ⊞ M)/A ⟶ C ⟶ 0` attached to a short complex
`S : 0 ⟶ A ⟶ B ⟶ C ⟶ 0`, a morphism `u : A ⟶ M` and a morphism `q` out of the pushout
`(B ⊞ M)/A` of `S.f` along `u` with `π ≫ q = pr_B ≫ S.g`. -/
private noncomputable abbrev pushoutSC (S : ShortComplex 𝒜) {M : 𝒜} (u : S.X₁ ⟶ M)
    (q : cokernel (toBiprod S u) ⟶ S.X₃)
    (hq : cokernel.π (toBiprod S u) ≫ q = biprod.fst ≫ S.g) : ShortComplex 𝒜 :=
  ShortComplex.mk (biprod.inr ≫ cokernel.π (toBiprod S u)) q
    (by rw [Category.assoc, hq, ← Category.assoc, biprod.inr_fst, zero_comp])

/-- The morphism `S ⟶ pushoutSC S u q hq` whose first component is `u`, its third the
identity. -/
private noncomputable def toPushoutSC (S : ShortComplex 𝒜) {M : 𝒜} (u : S.X₁ ⟶ M)
    (q : cokernel (toBiprod S u) ⟶ S.X₃)
    (hq : cokernel.π (toBiprod S u) ≫ q = biprod.fst ≫ S.g) : S ⟶ pushoutSC S u q hq where
  τ₁ := u
  τ₂ := biprod.inl ≫ cokernel.π (toBiprod S u)
  τ₃ := 𝟙 S.X₃
  comm₁₂ := by
    have hz : (S.f ≫ biprod.inl - u ≫ biprod.inr) ≫ cokernel.π (toBiprod S u) = 0 := by
      rw [← toBiprod_eq]; exact cokernel.condition _
    rw [Preadditive.sub_comp, sub_eq_zero] at hz
    dsimp [pushoutSC]
    rw [← Category.assoc, ← Category.assoc, hz]
  comm₂₃ := by
    dsimp [pushoutSC]
    rw [Category.assoc, hq, ← Category.assoc, biprod.inl_fst, Category.id_comp,
      Category.comp_id]

/-- The morphism `cokerSC (toBiprod S u) ⟶ S` whose first component is the identity, its second
the projection `pr_B` and its third the morphism `q` out of the pushout. -/
private noncomputable def fromCokerSC (S : ShortComplex 𝒜) {M : 𝒜} (u : S.X₁ ⟶ M)
    (q : cokernel (toBiprod S u) ⟶ S.X₃)
    (hq : cokernel.π (toBiprod S u) ≫ q = biprod.fst ≫ S.g) : cokerSC (toBiprod S u) ⟶ S where
  τ₁ := 𝟙 S.X₁
  τ₂ := biprod.fst
  τ₃ := q
  comm₁₂ := by rw [Category.id_comp]; exact (toBiprod_fst S u).symm
  comm₂₃ := hq.symm

/-- **The pushout of a short exact sequence along a morphism out of its first term.** For
`S : 0 ⟶ A ⟶ B ⟶ C ⟶ 0` short exact and `u : A ⟶ M` arbitrary, the object `P = (B ⊞ M)/A` sits
in a short exact sequence `0 ⟶ M ⟶ P ⟶ C ⟶ 0` whose second morphism `q` satisfies
`π ≫ q = pr_B ≫ S.g`. -/
private lemma exists_shortExact_pushoutSC (S : ShortComplex 𝒜) (hS : S.ShortExact) {M : 𝒜}
    (u : S.X₁ ⟶ M) :
    ∃ (q : cokernel (toBiprod S u) ⟶ S.X₃)
      (hq : cokernel.π (toBiprod S u) ≫ q = biprod.fst ≫ S.g),
      (pushoutSC S u q hq).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hv : Mono (toBiprod S u) := mono_toBiprod S hS u
  have hzq : toBiprod S u ≫ (biprod.fst ≫ S.g) = 0 := by
    rw [← Category.assoc, toBiprod_fst, S.zero]
  refine ⟨cokernel.desc _ _ hzq, cokernel.π_desc _ _ _, ?_⟩
  have hm : Mono (biprod.inr ≫ cokernel.π (toBiprod S u)) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro X x hx
    obtain ⟨a, ha⟩ : ∃ a : X ⟶ S.X₁, a ≫ toBiprod S u = x ≫ biprod.inr :=
      ⟨(ShortComplex.exact_cokernel (toBiprod S u)).lift (x ≫ biprod.inr)
        (by dsimp; rw [Category.assoc]; exact hx),
      (ShortComplex.exact_cokernel (toBiprod S u)).lift_f _ _⟩
    have h2 : a ≫ S.f = 0 := by
      rw [← toBiprod_fst S u, ← Category.assoc, ha, Category.assoc, biprod.inr_fst, comp_zero]
    have h3 : a = 0 := (Preadditive.mono_iff_cancel_zero S.f).1 hS.mono_f _ _ h2
    have h4 : x ≫ (biprod.inr : M ⟶ S.X₂ ⊞ M) = 0 := by rw [← ha, h3, zero_comp]
    exact (Preadditive.mono_iff_cancel_zero (biprod.inr : M ⟶ S.X₂ ⊞ M)).1 inferInstance _ _ h4
  have he : Epi (cokernel.desc _ (biprod.fst ≫ S.g) hzq) := by
    have : Epi (cokernel.π (toBiprod S u) ≫ cokernel.desc _ (biprod.fst ≫ S.g) hzq) := by
      rw [cokernel.π_desc]
      infer_instance
    exact epi_of_epi (cokernel.π (toBiprod S u)) _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro X x hx
  dsimp [pushoutSC] at hx
  obtain ⟨X', p, hp, y, hy⟩ :=
    surjective_up_to_refinements_of_epi (cokernel.π (toBiprod S u)) x
  have h1 : (y ≫ biprod.fst) ≫ S.g = 0 := by
    have h0 : y ≫ cokernel.π (toBiprod S u) ≫ cokernel.desc _ (biprod.fst ≫ S.g) hzq = 0 := by
      rw [← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
    rw [cokernel.π_desc, ← Category.assoc] at h0
    exact h0
  obtain ⟨a, ha⟩ : ∃ a : X' ⟶ S.X₁, a ≫ S.f = y ≫ biprod.fst :=
    ⟨hS.exact.lift (y ≫ biprod.fst) h1, hS.exact.lift_f _ _⟩
  refine ⟨X', p, hp, (y - a ≫ toBiprod S u) ≫ biprod.snd, ?_⟩
  have hfst : (y - a ≫ toBiprod S u) ≫ biprod.fst = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, toBiprod_fst, ha, sub_self]
  have hsplit : ((y - a ≫ toBiprod S u) ≫ biprod.snd) ≫ biprod.inr
      = y - a ≫ toBiprod S u := by
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, biprod.inr_fst, comp_zero, hfst]
    · rw [Category.assoc, biprod.inr_snd, Category.comp_id]
  dsimp [pushoutSC]
  rw [← Category.assoc, hsplit, Preadditive.sub_comp, Category.assoc, cokernel.condition,
    comp_zero, sub_zero, hy]

end Abelian

section DeltaFunctor

variable {𝒜 ℬ : Type*} [Category 𝒜] [Abelian 𝒜] [Category ℬ] [Abelian ℬ]

/-- The data of a cohomological `δ`-functor from `𝒜` to `ℬ`, [Stacks, Tag 010Q], restricted to
what the universality argument of [Stacks, Tag 010T] uses: a family of additive functors
`E ⁿ : 𝒜 ⥤ ℬ`, connecting morphisms `δ : E ⁿ(C) ⟶ E ⁿ⁺¹(A)` for every short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`, exactness of the long sequence at the two spots adjacent to `δ`,
and naturality of `δ` in the short exact sequence. -/
private structure DeltaFunctor (𝒜 ℬ : Type*) [Category 𝒜] [Abelian 𝒜] [Category ℬ]
    [Abelian ℬ] where
  /-- The family of functors `E ⁿ`, `n ≥ 0`. -/
  obj : ℕ → 𝒜 ⥤ ℬ
  /-- Each `E ⁿ` is additive. -/
  additive : ∀ n, (obj n).Additive
  /-- The connecting morphism `δ : E ⁿ(C) ⟶ E ⁿ⁺¹(A)`. -/
  δ : ∀ {S : ShortComplex 𝒜}, S.ShortExact → ∀ n : ℕ, (obj n).obj S.X₃ ⟶ (obj (n + 1)).obj S.X₁
  /-- The long sequence is exact at `E ⁿ(C)`. -/
  exact_δ_left : ∀ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ),
    ∃ hz : (obj n).map S.g ≫ δ hS n = 0, (ShortComplex.mk _ _ hz).Exact
  /-- The long sequence is exact at `E ⁿ⁺¹(A)`. -/
  exact_δ_right : ∀ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ),
    ∃ hz : δ hS n ≫ (obj (n + 1)).map S.f = 0, (ShortComplex.mk _ _ hz).Exact
  /-- `δ` is natural in the short exact sequence. -/
  δ_naturality : ∀ {S S' : ShortComplex 𝒜} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S')
    (n : ℕ), (obj n).map φ.τ₃ ≫ δ hS' n = δ hS n ≫ (obj (n + 1)).map φ.τ₁

/-- An additive functor kills a morphism into a biproduct as soon as it kills both components. -/
private lemma map_biprod_lift_eq_zero {X Y Z : 𝒜} (P : 𝒜 ⥤ ℬ) [P.Additive] (f : X ⟶ Y)
    (g : X ⟶ Z) (hf : P.map f = 0) (hg : P.map g = 0) : P.map (biprod.lift f g) = 0 := by
  rw [biprod.lift_eq, P.map_add, P.map_comp, P.map_comp, hf, hg, zero_comp, zero_comp, add_zero]

/-- If `E ⁿ⁺¹` kills the first morphism of a short exact sequence, its connecting morphism in
degree `n` is an epimorphism. -/
private lemma epi_δ (E : DeltaFunctor 𝒜 ℬ) {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ)
    (hu : (E.obj (n + 1)).map S.f = 0) : Epi (E.δ hS n) := by
  obtain ⟨hz, hex⟩ := E.exact_δ_right hS n
  exact (ShortComplex.exact_iff_epi _ hu).1 hex

/-- If the connecting morphism of a short exact sequence vanishes in degree `n`, then
`E ⁿ(B) ⟶ E ⁿ(C)` is an epimorphism. -/
private lemma epi_map_g_of_δ_eq_zero (E : DeltaFunctor 𝒜 ℬ) {S : ShortComplex 𝒜}
    (hS : S.ShortExact) (n : ℕ) (hδ : E.δ hS n = 0) : Epi ((E.obj n).map S.g) := by
  obtain ⟨hz, hex⟩ := E.exact_δ_left hS n
  exact (ShortComplex.exact_iff_epi _ hδ).1 hex

/-- **The defining equation propagates along a morphism of short exact sequences.** If
`θ : E ⁿ⁺¹(A') ⟶ G ⁿ⁺¹(A')` satisfies `δ_E ≫ θ = t ≫ δ_G` for the short exact sequence `S'`, and
`φ : S ⟶ S'` is a morphism of short exact sequences, then `E ⁿ⁺¹(φ.τ₁) ≫ θ` satisfies the
corresponding equation for `S`. -/
private lemma key (E G : DeltaFunctor 𝒜 ℬ) {S S' : ShortComplex 𝒜} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (n : ℕ) (t : E.obj n ⟶ G.obj n) (φ : S ⟶ S')
    {θ : (E.obj (n + 1)).obj S'.X₁ ⟶ (G.obj (n + 1)).obj S'.X₁}
    (hθ : E.δ hS' n ≫ θ = t.app S'.X₃ ≫ G.δ hS' n) :
    E.δ hS n ≫ (E.obj (n + 1)).map φ.τ₁ ≫ θ
      = t.app S.X₃ ≫ G.δ hS n ≫ (G.obj (n + 1)).map φ.τ₁ := by
  calc E.δ hS n ≫ (E.obj (n + 1)).map φ.τ₁ ≫ θ
      = ((E.obj n).map φ.τ₃ ≫ E.δ hS' n) ≫ θ := by
        rw [E.δ_naturality hS hS' φ n, Category.assoc]
    _ = (E.obj n).map φ.τ₃ ≫ t.app S'.X₃ ≫ G.δ hS' n := by rw [Category.assoc, hθ]
    _ = (t.app S.X₃ ≫ (G.obj n).map φ.τ₃) ≫ G.δ hS' n := by
        rw [← Category.assoc, t.naturality φ.τ₃]
    _ = t.app S.X₃ ≫ G.δ hS n ≫ (G.obj (n + 1)).map φ.τ₁ := by
        rw [Category.assoc, G.δ_naturality hS hS' φ n]

section Step

/-- The defining equation propagates from `cokerSC u'` to `cokerSC u` along a factorisation
`u ≫ b = u'` of `u'` through `u`. -/
private lemma key_cokerSC_id (E G : DeltaFunctor 𝒜 ℬ) (n : ℕ) (t : E.obj n ⟶ G.obj n)
    {X Y Y' : 𝒜} (u : X ⟶ Y) (u' : X ⟶ Y') (hu : Mono u) (hu' : Mono u') (b : Y ⟶ Y')
    (w : u ≫ b = u') {θ : (E.obj (n + 1)).obj X ⟶ (G.obj (n + 1)).obj X}
    (hθ : E.δ (shortExact_cokerSC u' hu') n ≫ θ
      = t.app (cokernel u') ≫ G.δ (shortExact_cokerSC u' hu') n) :
    E.δ (shortExact_cokerSC u hu) n ≫ θ
      = t.app (cokernel u) ≫ G.δ (shortExact_cokerSC u hu) n := by
  have := key E G (shortExact_cokerSC u hu) (shortExact_cokerSC u' hu') n t
    (cokerSCMap u u' (𝟙 X) b (by rw [w, Category.id_comp])) hθ
  simpa [cokerSCMap] using this

/-- The connecting morphism of an effacing short exact sequence is an epimorphism. -/
private lemma epi_δ_cokerSC (E : DeltaFunctor 𝒜 ℬ) (n : ℕ) (Mo : 𝒜 → 𝒜)
    (uu : ∀ A : 𝒜, A ⟶ Mo A) (hmono : ∀ A, Mono (uu A))
    (hzero : ∀ A, (E.obj (n + 1)).map (uu A) = 0) (A : 𝒜) :
    Epi (E.δ (shortExact_cokerSC (uu A) (hmono A)) n) :=
  epi_δ E _ n (hzero A)

/-- The value at `A` of the extension of `t : E ⁿ ⟶ G ⁿ` to degree `n + 1`: the unique morphism
`E ⁿ⁺¹(A) ⟶ G ⁿ⁺¹(A)` compatible with `t` and the connecting morphisms of the effacing short
exact sequence `0 ⟶ A ⟶ M_A ⟶ M_A/A ⟶ 0`. -/
private noncomputable def stepApp (E G : DeltaFunctor 𝒜 ℬ) (n : ℕ) (Mo : 𝒜 → 𝒜)
    (uu : ∀ A : 𝒜, A ⟶ Mo A) (hmono : ∀ A, Mono (uu A))
    (hzero : ∀ A, (E.obj (n + 1)).map (uu A) = 0)
    (t : E.obj n ⟶ G.obj n) (A : 𝒜) :
    (E.obj (n + 1)).obj A ⟶ (G.obj (n + 1)).obj A :=
  have := epi_δ_cokerSC E n Mo uu hmono hzero A
  (E.exact_δ_left (shortExact_cokerSC (uu A) (hmono A)) n).choose_spec.desc
    (t.app (cokernel (uu A)) ≫ G.δ (shortExact_cokerSC (uu A) (hmono A)) n) (by
      obtain ⟨hz, -⟩ := G.exact_δ_left (shortExact_cokerSC (uu A) (hmono A)) n
      dsimp
      rw [← Category.assoc, t.naturality (cokernel.π (uu A)), Category.assoc]
      exact (by rw [hz, comp_zero] : t.app (Mo A) ≫ ((G.obj n).map (cokernel.π (uu A))
        ≫ G.δ (shortExact_cokerSC (uu A) (hmono A)) n) = 0))

private lemma stepApp_spec (E G : DeltaFunctor 𝒜 ℬ) (n : ℕ) (Mo : 𝒜 → 𝒜)
    (uu : ∀ A : 𝒜, A ⟶ Mo A) (hmono : ∀ A, Mono (uu A))
    (hzero : ∀ A, (E.obj (n + 1)).map (uu A) = 0)
    (t : E.obj n ⟶ G.obj n) (A : 𝒜) :
    E.δ (shortExact_cokerSC (uu A) (hmono A)) n ≫ stepApp E G n Mo uu hmono hzero t A
      = t.app (cokernel (uu A)) ≫ G.δ (shortExact_cokerSC (uu A) (hmono A)) n := by
  have := epi_δ_cokerSC E n Mo uu hmono hzero A
  exact (E.exact_δ_left (shortExact_cokerSC (uu A) (hmono A)) n).choose_spec.g_desc _ _

/-- `stepApp` is natural: it is a morphism of functors `E ⁿ⁺¹ ⟶ G ⁿ⁺¹`. -/
private lemma stepApp_naturality (E G : DeltaFunctor 𝒜 ℬ) (n : ℕ) (Mo : 𝒜 → 𝒜)
    (uu : ∀ A : 𝒜, A ⟶ Mo A) (hmono : ∀ A, Mono (uu A))
    (hzero : ∀ A, (E.obj (n + 1)).map (uu A) = 0)
    (t : E.obj n ⟶ G.obj n) {A A' : 𝒜} (f : A ⟶ A') :
    (E.obj (n + 1)).map f ≫ stepApp E G n Mo uu hmono hzero t A'
      = stepApp E G n Mo uu hmono hzero t A ≫ (G.obj (n + 1)).map f := by
  have := E.additive (n + 1)
  have hwfst : biprod.lift (uu A) (f ≫ uu A') ≫ biprod.fst = uu A := biprod.lift_fst _ _
  have hwsnd : biprod.lift (uu A) (f ≫ uu A') ≫ biprod.snd = f ≫ uu A' := biprod.lift_snd _ _
  have hwmono : Mono (biprod.lift (uu A) (f ≫ uu A')) :=
    have := hmono A
    mono_of_mono_fac hwfst
  have hw0 : (E.obj (n + 1)).map (biprod.lift (uu A) (f ≫ uu A')) = 0 :=
    map_biprod_lift_eq_zero _ _ _ (hzero A) (by rw [Functor.map_comp, hzero A', comp_zero])
  have hWSE : (cokerSC (biprod.lift (uu A) (f ≫ uu A'))).ShortExact :=
    shortExact_cokerSC _ hwmono
  have hepi : Epi (E.δ hWSE n) := epi_δ E hWSE n hw0
  have h1 : E.δ hWSE n ≫ (E.obj (n + 1)).map f ≫ stepApp E G n Mo uu hmono hzero t A'
      = t.app (cokernel (biprod.lift (uu A) (f ≫ uu A'))) ≫ G.δ hWSE n
          ≫ (G.obj (n + 1)).map f :=
    key E G hWSE (shortExact_cokerSC (uu A') (hmono A')) n t
      (cokerSCMap _ _ f biprod.snd (by rw [hwsnd]))
      (stepApp_spec E G n Mo uu hmono hzero t A')
  have h2 : E.δ hWSE n ≫ stepApp E G n Mo uu hmono hzero t A
      = t.app (cokernel (biprod.lift (uu A) (f ≫ uu A'))) ≫ G.δ hWSE n :=
    key_cokerSC_id E G n t _ _ hwmono (hmono A) biprod.fst hwfst
      (stepApp_spec E G n Mo uu hmono hzero t A)
  rw [← cancel_epi (E.δ hWSE n), h1, ← Category.assoc, ← Category.assoc, h2]

/-- The extension of `t : E ⁿ ⟶ G ⁿ` to degree `n + 1`. -/
private noncomputable def step (E G : DeltaFunctor 𝒜 ℬ) (n : ℕ) (Mo : 𝒜 → 𝒜)
    (uu : ∀ A : 𝒜, A ⟶ Mo A) (hmono : ∀ A, Mono (uu A))
    (hzero : ∀ A, (E.obj (n + 1)).map (uu A) = 0)
    (t : E.obj n ⟶ G.obj n) : E.obj (n + 1) ⟶ G.obj (n + 1) where
  app A := stepApp E G n Mo uu hmono hzero t A
  naturality _ _ f := stepApp_naturality E G n Mo uu hmono hzero t f

private lemma step_app (E G : DeltaFunctor 𝒜 ℬ) (n : ℕ) (Mo : 𝒜 → 𝒜)
    (uu : ∀ A : 𝒜, A ⟶ Mo A) (hmono : ∀ A, Mono (uu A))
    (hzero : ∀ A, (E.obj (n + 1)).map (uu A) = 0)
    (t : E.obj n ⟶ G.obj n) (A : 𝒜) :
    (step E G n Mo uu hmono hzero t).app A = stepApp E G n Mo uu hmono hzero t A := rfl

/-- **The extension is compatible with the connecting morphisms of every short exact sequence.** -/
private lemma step_δ (E G : DeltaFunctor 𝒜 ℬ) (n : ℕ) (Mo : 𝒜 → 𝒜)
    (uu : ∀ A : 𝒜, A ⟶ Mo A) (hmono : ∀ A, Mono (uu A))
    (hzero : ∀ A, (E.obj (n + 1)).map (uu A) = 0)
    (t : E.obj n ⟶ G.obj n) {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    t.app S.X₃ ≫ G.δ hS n = E.δ hS n ≫ (step E G n Mo uu hmono hzero t).app S.X₁ := by
  obtain ⟨q, hq, hTSE⟩ := exists_shortExact_pushoutSC S hS (uu S.X₁)
  have hWSE : (cokerSC (toBiprod S (uu S.X₁))).ShortExact :=
    shortExact_cokerSC _ (mono_toBiprod S hS (uu S.X₁))
  -- the connecting morphism of the pushout sequence vanishes, so `E ⁿ(P) ⟶ E ⁿ(C)` is epi
  have hδT : E.δ hTSE n = 0 := by
    have hnat : (E.obj n).map (𝟙 S.X₃) ≫ E.δ hTSE n
        = E.δ hS n ≫ (E.obj (n + 1)).map (uu S.X₁) :=
      E.δ_naturality hS hTSE (toPushoutSC S (uu S.X₁) q hq) n
    rw [CategoryTheory.Functor.map_id, Category.id_comp, hzero S.X₁, comp_zero] at hnat
    exact hnat
  have hepiq : Epi ((E.obj n).map q) := epi_map_g_of_δ_eq_zero E hTSE n hδT
  -- the two morphisms out of the mediating sequence, both with first component the identity
  have h1 : E.δ hWSE n ≫ (step E G n Mo uu hmono hzero t).app S.X₁
      = t.app (cokernel (toBiprod S (uu S.X₁))) ≫ G.δ hWSE n :=
    key_cokerSC_id E G n t _ _ (mono_toBiprod S hS _) (hmono S.X₁) (-biprod.snd)
      (by rw [Preadditive.comp_neg, toBiprod_snd, neg_neg])
      (stepApp_spec E G n Mo uu hmono hzero t S.X₁)
  have hδq : ∀ D : DeltaFunctor 𝒜 ℬ,
      (D.obj n).map q ≫ D.δ hS n = D.δ hWSE n := fun D ↦
    by simpa [fromCokerSC] using D.δ_naturality hWSE hS (fromCokerSC S (uu S.X₁) q hq) n
  rw [← cancel_epi ((E.obj n).map q)]
  calc (E.obj n).map q ≫ t.app S.X₃ ≫ G.δ hS n
      = t.app (cokernel (toBiprod S (uu S.X₁))) ≫ (G.obj n).map q ≫ G.δ hS n := by
        rw [← Category.assoc, ← Category.assoc, t.naturality q]
    _ = t.app (cokernel (toBiprod S (uu S.X₁))) ≫ G.δ hWSE n := by rw [hδq G]
    _ = E.δ hWSE n ≫ (step E G n Mo uu hmono hzero t).app S.X₁ := h1.symm
    _ = (E.obj n).map q ≫ E.δ hS n ≫ (step E G n Mo uu hmono hzero t).app S.X₁ := by
        rw [← hδq E, Category.assoc]

end Step

/-- **An effaceable `δ`-functor is universal**, [Stacks, Tag 010T]. Let `E` and `G` be
cohomological `δ`-functors from `𝒜` to `ℬ` and suppose that for every `n` and every object `A`
of `𝒜` there is a monomorphism `u : A ⟶ M_A` with `E ⁿ⁺¹(u) = 0`. Then every morphism of
functors `E ⁰ ⟶ G ⁰` extends uniquely to a morphism of `δ`-functors `E ⟶ G`. -/
@[sga "3 I 5.2.1" "partial"]
private theorem existsUnique_of_effaceable (E G : DeltaFunctor 𝒜 ℬ) (Mo : ℕ → 𝒜 → 𝒜)
    (uu : ∀ (n : ℕ) (A : 𝒜), A ⟶ Mo n A) (hmono : ∀ n A, Mono (uu n A))
    (hzero : ∀ n A, (E.obj (n + 1)).map (uu n A) = 0) (t₀ : E.obj 0 ⟶ G.obj 0) :
    ∃! t : ∀ n : ℕ, E.obj n ⟶ G.obj n, t 0 = t₀ ∧
      ∀ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ),
        (t n).app S.X₃ ≫ G.δ hS n = E.δ hS n ≫ (t (n + 1)).app S.X₁ := by
  refine ⟨fun n => Nat.rec (motive := fun n => E.obj n ⟶ G.obj n) t₀
    (fun n tn => step E G n (Mo n) (uu n) (hmono n) (hzero n) tn) n, ⟨rfl, ?_⟩, ?_⟩
  · intro S hS n
    exact step_δ E G n (Mo n) (uu n) (hmono n) (hzero n) _ hS
  · rintro t' ⟨h0, hcompat⟩
    funext m
    induction m with
    | zero => exact h0
    | succ n ih =>
      change t' (n + 1) = step E G n (Mo n) (uu n) (hmono n) (hzero n)
        (Nat.rec (motive := fun n => E.obj n ⟶ G.obj n) t₀
          (fun n tn => step E G n (Mo n) (uu n) (hmono n) (hzero n) tn) n)
      rw [← ih]
      ext A
      have := epi_δ_cokerSC E n (Mo n) (uu n) (hmono n) (hzero n) A
      rw [← cancel_epi (E.δ (shortExact_cokerSC (uu n A) (hmono n A)) n), step_app,
        stepApp_spec E G n (Mo n) (uu n) (hmono n) (hzero n) (t' n) A]
      exact (hcompat (shortExact_cokerSC (uu n A) (hmono n A)) n).symm

end DeltaFunctor

set_option maxHeartbeats 1600000 in
-- The two `δ`-functor structures compared here are stated with different, definitionally equal,
-- spellings of the functors `R ⁱ F`: `H ⁱ ∘ RF ∘ (·[0])` on this side and `G ⋙ H⁰.shift i` in
-- [Stacks, Tag 05SR], and the shift sequence of `H ⁰` has to be unfolded to identify them.
open ShortComplex Pretriangulated in
/-- **The higher right derived functors form a universal `δ`-functor**, [Stacks 05TE].
Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, where `𝒜` has enough
injectives, so that `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined and `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`.
Let `h` be a `δ`-functor structure on `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`, and let `δ` be the connecting
morphism `R ⁱ F(C) ⟶ R ⁱ⁺¹ F(A)` that the homology sequence of its distinguished triangles
attaches to a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`. Then
1. `{R ⁱ F, δ}_{i ≥ 0}` is a cohomological `δ`-functor from `𝒜` to `ℬ`: the `R ⁱ F` are additive,
   the long sequence `0 ⟶ R ⁰ F(A) ⟶ R ⁰ F(B) ⟶ R ⁰ F(C) ⟶ R ¹ F(A) ⟶ ⋯` is exact, and `δ` is
   natural in the short exact sequence; and
2. if every object of `𝒜` admits a monomorphism into an object right acyclic for `F`, then
   `{R ⁱ F, δ}_{i ≥ 0}` is a universal `δ`-functor: for every `δ`-functor `{G ⁱ, δ_G}_{i ≥ 0}`
   from `𝒜` to `ℬ` and every `t₀ : R ⁰ F ⟶ G ⁰` there is a unique family `t ⁱ : R ⁱ F ⟶ G ⁱ`
   commuting with `δ` and `δ_G` and with `t ⁰ = t₀`. -/
@[stacks 05TE]
public theorem rightDerivedPlus_isDeltaFunctor_and_isUniversal
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    (h : DeltaFunctorStructure C (DerivedCategory.Plus D)
      (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus))
    (δ : ∀ {S : ShortComplex C}, S.ShortExact → ∀ i : ℕ,
      (F.rightDerivedPlus i).obj S.X₃ ⟶ (F.rightDerivedPlus (i + 1)).obj S.X₁)
    (hδ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ), δ hS i =
      (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ
        (Triangle.mk
          ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).map S.f)
          ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).map S.g)
          (h.δ hS)) i (i + 1) rfl) :
    ((∀ i : ℕ, (F.rightDerivedPlus i).Additive) ∧
      (∀ {S : ShortComplex C}, S.ShortExact → Mono ((F.rightDerivedPlus 0).map S.f)) ∧
      (∀ {S : ShortComplex C} (_ : S.ShortExact) (i : ℕ),
        ∃ hz : (F.rightDerivedPlus i).map S.f ≫ (F.rightDerivedPlus i).map S.g = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : (F.rightDerivedPlus i).map S.g ≫ δ hS i = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : δ hS i ≫ (F.rightDerivedPlus (i + 1)).map S.f = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') (i : ℕ),
        (F.rightDerivedPlus i).map φ.τ₃ ≫ δ hS' i =
          δ hS i ≫ (F.rightDerivedPlus (i + 1)).map φ.τ₁)) ∧
    ((∀ A : C, ∃ (I : C) (u : A ⟶ I), Mono u ∧ F.rightAcyclic I) →
      ∀ (G : ℕ → C ⥤ D) (_ : ∀ i, (G i).Additive)
        (δG : ∀ {S : ShortComplex C}, S.ShortExact → ∀ i : ℕ,
          (G i).obj S.X₃ ⟶ (G (i + 1)).obj S.X₁),
        (∀ {S : ShortComplex C}, S.ShortExact → Mono ((G 0).map S.f)) →
        (∀ {S : ShortComplex C} (_ : S.ShortExact) (i : ℕ),
          ∃ hz : (G i).map S.f ≫ (G i).map S.g = 0, (ShortComplex.mk _ _ hz).Exact) →
        (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
          ∃ hz : (G i).map S.g ≫ δG hS i = 0, (ShortComplex.mk _ _ hz).Exact) →
        (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
          ∃ hz : δG hS i ≫ (G (i + 1)).map S.f = 0, (ShortComplex.mk _ _ hz).Exact) →
        (∀ {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S')
          (i : ℕ), (G i).map φ.τ₃ ≫ δG hS' i = δG hS i ≫ (G (i + 1)).map φ.τ₁) →
        ∀ t₀ : F.rightDerivedPlus 0 ⟶ G 0,
          ∃! t : ∀ i : ℕ, F.rightDerivedPlus i ⟶ G i,
            t 0 = t₀ ∧ ∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
              (t i).app S.X₃ ≫ δG hS i = δ hS i ≫ (t (i + 1)).app S.X₁) := by
  -- Part (1): the `δ`-functor structure, [Stacks, Tag 05SR] applied to `H ⁰`.
  have hH : ∀ A : C, IsZero (((DerivedCategory.Plus.homologyFunctor D 0).shift (-1 : ℤ)).obj
      ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).obj A)) := fun A ↦
    ((isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits F
      F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith).1 (-1) (by norm_num)).obj A
  have part1 := DeltaFunctorStructure.isCohomologicalDeltaFunctor_comp_shift h
    (DerivedCategory.Plus.homologyFunctor D 0) hH δ hδ
  obtain ⟨hadd, hmono0, hex₂, hexl, hexr, hnat⟩ := part1
  refine ⟨⟨hadd, hmono0, hex₂, hexl, hexr, hnat⟩, ?_⟩
  -- Part (2): universality, by Grothendieck's criterion.
  intro heff Gf Gadd δG _ _ Gexl Gexr Gnat t₀
  let E : DeltaFunctor C D :=
    { obj := fun i => F.rightDerivedPlus i
      additive := hadd
      δ := fun hS i => δ hS i
      exact_δ_left := fun hS i => hexl hS i
      exact_δ_right := fun hS i => hexr hS i
      δ_naturality := fun hS hS' φ i => hnat hS hS' φ i }
  let Gd : DeltaFunctor C D :=
    { obj := Gf
      additive := Gadd
      δ := fun hS i => δG hS i
      exact_δ_left := fun hS i => Gexl hS i
      exact_δ_right := fun hS i => Gexr hS i
      δ_naturality := fun hS hS' φ i => Gnat hS hS' φ i }
  choose Mo uu hmono hacyc using heff
  refine existsUnique_of_effaceable E Gd (fun _ A => Mo A) (fun _ A => uu A)
    (fun _ A => hmono A) (fun n A => ?_) t₀
  have h015C := (rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F (Mo A)).1.mp (hacyc A)
  exact (h015C.2 ((n : ℤ) + 1) (by positivity)).eq_zero_of_tgt _

end CategoryTheory.Functor

/-! ### Right derived functors move to the right -/

namespace StacksDraft.RightDerivedMovesRight

open CategoryTheory Limits CochainComplex

universe v u v' u'

section Retract

variable {C : Type u} [Category.{v} C] {H : Type u'} [Category.{v'} H]

/-- **Essential constancy makes the value a retract at every index receiving the pinned one.**
If the cocone `c` exhibits `c.pt` as a value of the ind-object of `G` at `X`, the retraction is
taken at one index `s₀`; but for every index `t` and every morphism `v : s₀ ⟶ t` the cocone law
turns the retraction at `s₀` into one at `t`. -/
private lemma exists_retraction_of_isRightDerivedValueAt (G : C ⥤ H) (W : MorphismProperty C)
    (X : C) (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ G))
    (hc : G.IsRightDerivedValueAt W X c) :
    ∃ (s₀ : W.Under ⊤ X) (r : c.pt ⟶ G.obj s₀.right),
      ∀ (t : W.Under ⊤ X) (v : s₀ ⟶ t), (r ≫ G.map v.right) ≫ c.ι.app t = 𝟙 c.pt := by
  obtain ⟨s₀, r, hr, -⟩ := hc
  exact ⟨s₀, r, fun t v ↦ (Category.assoc _ _ _).trans
    ((congrArg (fun g ↦ r ≫ g) (c.w v)).trans hr)⟩

end Retract

section IsGE

variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory B]

/-- **`IsGE` passes to retracts.** If `X` is a retract of `Y` and `Y` is `≥ n`, then `X` is `≥ n`:
in each degree `< n` the identity of `H ⁱ(X)` factors through `H ⁱ(Y) = 0`. -/
lemma isGE_of_retract {X Y : DerivedCategory B} (i : X ⟶ Y) (p : Y ⟶ X)
    (hip : i ≫ p = 𝟙 X) (n : ℤ) (hY : Y.IsGE n) : X.IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro j hj
  have hzero : IsZero ((DerivedCategory.homologyFunctor B j).obj Y) :=
    DerivedCategory.isZero_of_isGE Y n j hj
  rw [Limits.IsZero.iff_id_eq_zero]
  have hmap := congrArg (DerivedCategory.homologyFunctor B j).map hip
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hmap
  rw [← hmap, hzero.eq_of_tgt ((DerivedCategory.homologyFunctor B j).map i) 0, zero_comp]

end IsGE

section PartOne

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- The value of `Φ = Qh ∘ F` at the image of a cochain complex `L` in `K(A)` is the image under
`Q` of the complex obtained by applying `F` termwise to `L`. -/
private noncomputable def phiQuotientIso (L : CochainComplex A ℤ) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app L) ≪≫
    (DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)

/-- `Φ` carries a complex lying in degrees `≥ m` to an object of `D(B)` which is `≥ m`, because
`F` is additive and therefore sends the vanishing terms to zero objects. -/
private lemma isGE_phi_obj (L : CochainComplex A ℤ) (m : ℤ)
    (hm : CochainComplex.IsStrictlyGE L m) :
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)).IsGE m := by
  have := hm
  have hFm : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) m := inferInstance
  have := hFm
  exact DerivedCategory.TStructure.t.isGE_of_iso (phiQuotientIso F L).symm m

omit [HasDerivedCategory B] F in
/-- Cohomological boundedness below transfers along a quasi-isomorphism of `K(A)`: the homology of
`K` and of `L` are identified in every degree. -/
private lemma isGE_of_quasiIso {K L : CochainComplex A ℤ}
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)
    (hf : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) f) (a : ℤ) (hK : K.IsGE a) :
    L.IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hKi : IsZero (K.homology i) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact (CochainComplex.isGE_iff K a).1 hK i hi
  have := hf i
  exact hKi.of_iso
    ((((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app L).symm ≪≫
      (asIso ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i).map f)).symm ≪≫
        (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app K))

/-- **[StacksProject 05TC], part (1).** If `H ⁱ(K) = 0` for `i < a` and `RF` is defined at `K` with
value `c.pt`, then `H ⁱ(RF(K)) = 0` for `i < a`.

The value is a retract of the term `F(s₀.right)` of the ind-object at the index `s₀` supplied by
essential constancy, and that retraction moves along any morphism out of `s₀`. Since `K` is `≥ a`,
so is the complex `L₀ = s₀.right`, so `πTruncGE : L₀ ⟶ τ_{≥ a}L₀` is a quasi-isomorphism and
composing `s₀` with it gives another index `t` receiving `s₀`. Thus `c.pt` is a retract of
`Φ(τ_{≥ a}L₀)`, which is `≥ a` because `τ_{≥ a}L₀` is strictly `≥ a` and `F` is additive. -/
private lemma isGE_of_isRightDerivedValueAt (K : CochainComplex A ℤ) (a : ℤ)
    (c : Cocone (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
        ⊤ ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
      Under.forget ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) c)
    (hK : K.IsGE a) : c.pt.IsGE a := by
  obtain ⟨s₀, r, hret⟩ := exists_retraction_of_isRightDerivedValueAt _ _ _ c hc
  have hL₀ : CochainComplex.IsGE (s₀.right.as) a :=
    isGE_of_quasiIso (L := s₀.right.as) s₀.hom s₀.prop a hK
  have hqi : QuasiIso (CochainComplex.πTruncGE (s₀.right.as) a) :=
    (CochainComplex.quasiIso_πTruncGE_iff _ a).2 hL₀
  have hmem : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (CochainComplex.πTruncGE (s₀.right.as) a)) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
    exact hqi
  obtain ⟨t, v, hty⟩ : ∃ (t : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) (_ : s₀ ⟶ t),
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj t.right).IsGE a := by
    refine ⟨MorphismProperty.Under.mk ⊤ (s₀.hom ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (CochainComplex.πTruncGE (s₀.right.as) a))
        (MorphismProperty.comp_mem _ _ _ s₀.prop hmem),
      MorphismProperty.Under.homMk _ rfl trivial,
      isGE_phi_obj F (CochainComplex.truncGE (s₀.right.as) a) a inferInstance⟩
  exact isGE_of_retract _ (c.ι.app t) (hret t v) a hty

end PartOne

section Cone

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Cohomological boundedness below is a quasi-isomorphism invariant.** `IsGE n` says that a
complex is exact outside `[n, ∞)`, and a quasi-isomorphism identifies the homology of its two ends
in every degree. -/
private lemma isGE_of_quasiIso_of_isGE {K L : CochainComplex A ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (n : ℤ) (hL : L.IsGE n) : K.IsGE n :=
  (HomologicalComplex.isSupported_iff_of_quasiIso φ (ComplexShape.embeddingUpIntGE n)).2 hL

/-- **The cone on `τ_{≤ a}K ⟶ K` has no cohomology in degrees `≤ a`.** The canonical monomorphism
`K.ιTruncLE a` is the injection of a short exact sequence of complexes
(`CochainComplex.shortComplexTruncLE_shortExact`), so its cone is quasi-isomorphic to the quotient
term (`CochainComplex.mappingCone.quasiIso_descShortComplex`), which in turn is quasi-isomorphic to
`τ_{≥ a + 1}K` (`CochainComplex.shortComplexTruncLEX₃ToTruncGE`); and `τ_{≥ a + 1}K` vanishes in
degrees `< a + 1` even termwise. -/
private lemma isGE_mappingCone_ιTruncLE (K : CochainComplex A ℤ) (a : ℤ) :
    (CochainComplex.mappingCone (K.ιTruncLE a)).IsGE (a + 1) := by
  have hqi : QuasiIso (CochainComplex.mappingCone.descShortComplex (K.shortComplexTruncLE a)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (K.shortComplexTruncLE_shortExact a)
  have hX₃ : (K.shortComplexTruncLE a).X₃.IsGE (a + 1) :=
    isGE_of_quasiIso_of_isGE (K.shortComplexTruncLEX₃ToTruncGE a (a + 1) rfl) (a + 1) inferInstance
  exact isGE_of_quasiIso_of_isGE
    (CochainComplex.mappingCone.descShortComplex (K.shortComplexTruncLE a)) (a + 1) hX₃

end Cone

section Uniqueness

variable {C : Type u} [Category.{v} C] {H : Type u'} [Category.{v'} H]

/-- A morphism out of an object that is split off one of its own predecessors is determined by the
composite with the splitting: from `r ≫ p = 𝟙` and `p ≫ ψ = m` it follows that `ψ = r ≫ m`. Like
the corresponding lemmas of the file for Tag 05SC it is stated for abstract morphisms of `H`,
because the morphism `p` it is applied to is a coprojection of a cocone on the ind-object, whose
source is `G(X')` only after unfolding the diagram. -/
private lemma eq_comp_of_split {P Q R : H} {r : P ⟶ Q} {p : Q ⟶ P} (hr : r ≫ p = 𝟙 P)
    {ψ : P ⟶ R} {m : Q ⟶ R} (h : p ≫ ψ = m) : ψ = r ≫ m := by
  rw [← h, ← Category.assoc, hr, Category.id_comp]

/-- **The morphism of Tag 05SA is unique.** Let `RF` be defined at `X` with value `d`. A morphism
`ψ : d.pt ⟶ c.pt` compatible with the coprojections along the squares attached to `f : X ⟶ Y` is
determined by that compatibility: essential constancy splits the coprojection at one index `s₀` by
a morphism `r`, the Ore condition MS2 completes `f` and `s₀` to a square `(s₀, t, g)`, and the
compatibility at that single square already forces `ψ = r ≫ G(g) ≫ c.ι.app t`. -/
private lemma eq_of_comp_ι_app_eq (G : C ⥤ H) (W : MorphismProperty C)
    [W.HasLeftCalculusOfFractions] {X Y : C} (f : X ⟶ Y)
    {d : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ G)}
    (hd : G.IsRightDerivedValueAt W X d)
    {c : Cocone (MorphismProperty.Under.forget W ⊤ Y ⋙ Under.forget Y ⋙ G)}
    (ψ₁ ψ₂ : d.pt ⟶ c.pt)
    (h₁ : ∀ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (g : s.right ⟶ t.right),
      f ≫ t.hom = s.hom ≫ g → d.ι.app s ≫ ψ₁ = G.map g ≫ c.ι.app t)
    (h₂ : ∀ (s : W.Under ⊤ X) (t : W.Under ⊤ Y) (g : s.right ⟶ t.right),
      f ≫ t.hom = s.hom ≫ g → d.ι.app s ≫ ψ₂ = G.map g ≫ c.ι.app t) :
    ψ₁ = ψ₂ := by
  obtain ⟨s₀, r, hr, -⟩ := hd
  obtain ⟨t, g, hsq⟩ : ∃ (t : W.Under ⊤ Y) (g : s₀.right ⟶ t.right),
      f ≫ t.hom = s₀.hom ≫ g := by
    obtain ⟨χ, hχ⟩ := (MorphismProperty.RightFraction.mk s₀.hom s₀.prop f).exists_leftFraction
    exact ⟨MorphismProperty.Under.mk ⊤ χ.s χ.hs, χ.f, hχ⟩
  exact (eq_comp_of_split hr (h₁ s₀ t g hsq)).trans (eq_comp_of_split hr (h₂ s₀ t g hsq)).symm

end Uniqueness

section PartTwo

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- **[StacksProject 05TC], part (2).** If `RF` is defined at `K` with value `c.pt` and
at `τ_{≤ a}K` with value `d.pt`, then there is a unique morphism `φ : d.pt ⟶ c.pt` compatible with
the coprojections of the two values along `K.ιTruncLE a`, and `H ⁱ(φ)` is an isomorphism for
`i ≤ a`.

The whole assertion is read off the distinguished triangle
`Q(τ_{≤ a}K) ⟶ Q(K) ⟶ Q(C(ιTruncLE)) ⟶ Q(τ_{≤ a}K)⟦1⟧` of `K(A)` on the cone of `K.ιTruncLE a`
(`HomotopyCategory.mappingCone_triangleh_distinguished`), whose first two vertices and first
morphism are `Q(τ_{≤ a}K)`, `Q(K)` and `Q(ιTruncLE)` on the nose.

*The triangle of values.* `Qis(A)` is a saturated multiplicative system
([StacksProject 05RT]) compatible with the triangulation — the latter because it is
`Ac(A).trW` — so [StacksProject 05SC] applies to `Φ = Qh ∘ F` and that triangle: `RF` is defined at
the third vertex as well, and for the three values there are morphisms, each characterised by
compatibility with the coprojections as in [StacksProject 05SA], forming a distinguished triangle
`d.pt ⟶ c.pt ⟶ e.pt ⟶ d.pt⟦1⟧` of `D(B)`. Its first morphism is the required `φ`, and its
characterisation is the one asserted here.

*Uniqueness.* Essential constancy at `τ_{≤ a}K` splits one coprojection of `d`, so the
characterisation at a single square — one exists by the Ore condition MS2, available because
`Qis(A)` has a left calculus of fractions — already determines the morphism
(`eq_of_comp_ι_app_eq`).

*`H ⁱ(φ)` an isomorphism for `i ≤ a`.* The cone is `≥ a + 1` (`isGE_mappingCone_ιTruncLE`), so by
part (1) its value `e.pt` is `≥ a + 1`, i.e. `H ʲ(e.pt) = 0` for `j ≤ a`. Since `Hⁱ` on `D(B)` is
a homological functor with a shift sequence, the long exact sequence of the triangle of values
makes `H ⁱ(φ)` epi (`Functor.homologySequence_epi_shift_map_mor₁_iff`: the next map lands in
`H ⁱ(e.pt) = 0`) and mono (`Functor.homologySequence_mono_shift_map_mor₁_iff`: the incoming
connecting map leaves `H ⁱ⁻¹(e.pt) = 0`), hence an isomorphism because `B` is abelian. -/
private lemma exists_map_and_isIso_homologyFunctor_map (K : CochainComplex A ℤ) (a : ℤ)
    (c : Cocone (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
        ⊤ ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
      Under.forget ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) c)
    (d : Cocone (MorphismProperty.Under.forget
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)) ⋙
        Under.forget ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)) ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (hd : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)) d) :
    ∃ φ : d.pt ⟶ c.pt,
      (∀ ψ : d.pt ⟶ c.pt,
        (∀ (s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)))
           (t : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
           (g : s.right ⟶ t.right),
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (K.ιTruncLE a) ≫ t.hom =
              s.hom ≫ g →
            d.ι.app s ≫ ψ =
              (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map g ≫
                c.ι.app t) ↔ ψ = φ) ∧
      ∀ i ≤ a, IsIso ((DerivedCategory.homologyFunctor B i).map φ) := by
  have hW : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsSaturated :=
    (HomotopyCategory.isSaturated_subcategoryAcyclic_and_quasiIso_and_kernel_eq
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Q).2.1.1
  have hcompat :
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsCompatibleWithTriangulation := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  obtain ⟨hthird, -, -, htriangle⟩ :=
    (Functor.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) hW
      (CochainComplex.mappingCone.triangleh (K.ιTruncLE a))
      (HomotopyCategory.mappingCone_triangleh_distinguished (K.ιTruncLE a))).1
  obtain ⟨e, he⟩ := hthird ⟨d, hd⟩ ⟨c, hc⟩
  obtain ⟨φ, v, w, hdist, hφ, -, -⟩ := htriangle d hd c hc e he
  have hept : e.pt.IsGE (a + 1) :=
    isGE_of_isRightDerivedValueAt F (CochainComplex.mappingCone (K.ιTruncLE a)) (a + 1) e he
      (isGE_mappingCone_ιTruncLE K a)
  have hzero : ∀ j : ℤ, j ≤ a → IsZero ((DerivedCategory.homologyFunctor B j).obj e.pt) :=
    fun j hj ↦ DerivedCategory.isZero_of_isGE e.pt (a + 1) j (by lia)
  refine ⟨φ, fun ψ ↦ ⟨fun hψ ↦ eq_of_comp_ι_app_eq _ _ _ hd ψ φ hψ hφ, ?_⟩, ?_⟩
  · rintro rfl
    exact hφ
  · intro i hi
    have hepi : Epi ((DerivedCategory.homologyFunctor B i).map φ) :=
      ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₁_iff
        (Pretriangulated.Triangle.mk φ v w) hdist i).2 ((hzero i hi).eq_of_tgt _ 0)
    have hmono : Mono ((DerivedCategory.homologyFunctor B i).map φ) :=
      ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
        (Pretriangulated.Triangle.mk φ v w) hdist (i - 1) i (by lia)).2
        ((hzero (i - 1) (by lia)).eq_of_src _ 0)
    exact isIso_of_mono_of_epi _

end PartTwo

end StacksDraft.RightDerivedMovesRight

namespace CategoryTheory.Functor

open CochainComplex

/-- **Right derived functors move to the right**, [StackProject 05TC].
Let `F : A ⥤ B` be an additive functor between abelian categories, let `K` be a cochain complex
of objects of `A`, let `a : ℤ`, and let `RF` be the right derived functor of
`K(A) ⥤ K(B) ⥤ D(B)` with respect to the quasi-isomorphisms. Assume `RF` is defined at `K`,
with value `RF(K) = c.pt` (Stacks 05S9: the ind-object `(s : K ⟶ L) ↦ F(L)` of `D(B)` is
essentially constant with value `c.pt`).
1. If `H^i(K) = 0` for all `i < a`, then `H^i(RF(K)) = 0` for all `i < a`.
2. If moreover `RF` is defined at `τ_{≤ a}K`, with value `RF(τ_{≤ a}K) = d.pt`, then there is a
   unique morphism `φ : RF(τ_{≤ a}K) ⟶ RF(K)` compatible with the coprojections of the two
   values along the canonical monomorphism `K.ιTruncLE a : τ_{≤ a}K ⟶ K` — that is, with
   `d.ι.app s ≫ φ = F(g) ≫ c.ι.app t` for every pair of indices `s`, `t` and every
   `g : s.right ⟶ t.right` with `ιTruncLE ≫ t.hom = s.hom ≫ g`, the morphism `RF(ιTruncLE)`
   of Stacks 05SA — and `H^i(φ)` is an isomorphism for all `i ≤ a`. -/
@[stacks 05TC]
public theorem isGE_and_isIso_homologyFunctor_map_of_isRightDerivedValueAt
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (a : ℤ)
    (c : Cocone (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
        ⊤ ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
      Under.forget ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) c) :
    (K.IsGE a → c.pt.IsGE a) ∧
    ∀ (d : Cocone (MorphismProperty.Under.forget
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)) ⋙
        Under.forget ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)) ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)),
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)) d →
      ∃ φ : d.pt ⟶ c.pt,
        (∀ ψ : d.pt ⟶ c.pt,
          (∀ (s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K.truncLE a)))
             (t : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
             (g : s.right ⟶ t.right),
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (K.ιTruncLE a) ≫ t.hom =
                s.hom ≫ g →
              d.ι.app s ≫ ψ =
                (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map g ≫
                  c.ι.app t) ↔ ψ = φ) ∧
        ∀ i ≤ a, IsIso ((DerivedCategory.homologyFunctor B i).map φ) :=
  ⟨fun hK ↦ StacksDraft.RightDerivedMovesRight.isGE_of_isRightDerivedValueAt F K a c hc hK,
    fun d hd ↦ StacksDraft.RightDerivedMovesRight.exists_map_and_isIso_homologyFunctor_map
      F K a c hc d hd⟩

end CategoryTheory.Functor

end

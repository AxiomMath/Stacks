module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Refinements
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Resolutions of complexes by a class of objects

Let `A` be an abelian category, let `P` be a class of objects of `A` containing a zero object,
and fix `a : ℤ`. This file resolves a cochain complex bounded on one side by objects of `P`, in
the two dual situations.

If every object of `A` is a *subobject* of an object satisfying `P` — for `P` the injective
objects of a category with enough injectives, the standing assumptions of injective resolutions —
then every cochain complex `K` which is bounded below by `a` in cohomology, i.e. `H ^ n (K) = 0`
for `n < a`, admits a quasi-isomorphism `f : K ⟶ L` into a complex `L` with `L.X n = 0` for
`n < a` and all terms `L.X n` satisfying `P`; and if `K` is already strictly bounded below by `a`,
i.e. `K.X n = 0` for `n < a`, then `f` may moreover be taken degreewise monomorphic.

Dually, if every object of `A` is a *quotient* of an object satisfying `P` — for `P` the
projective objects of a category with enough projectives — then every cochain complex bounded
above by `a`, either strictly or only cohomologically, receives a quasi-isomorphism `f : L ⟶ K`
from a complex `L` with `L.X n = 0` for `n > a` and all terms satisfying `P`; in the strict case
`f` may moreover be taken degreewise epimorphic.

## Main results

* `CochainComplex.exists_quasiIso_prop_isStrictlyGE`: Stacks 05T6, parts (1) and (2).
* `CochainComplex.exists_quasiIso_prop`: Stacks 05T7, parts (1) and (2), in this order.

## Implementation notes

The class of objects of the source is a `CategoryTheory.ObjectProperty A`, i.e. a predicate on
objects. "Contains `0`" is `CategoryTheory.ObjectProperty.ContainsZero`, i.e. *some* zero object
satisfies `P`; this is what the constructions use (they fill the degrees outside the bound with
that object) and is weaker than `P 0` for a chosen zero object unless `P` is closed under
isomorphisms. For the same reason, terms of the complexes constructed that are merely isomorphic
to an object satisfying `P` are replaced by objects genuinely satisfying it, which is what
`transport` and `exists_iso_prop` are for; both resolutions use them. "Every object is a subobject
(quotient) of an element of `P`" is spelled as the existence, for each `X`, of a monomorphism into
(an epimorphism onto) `X` from an object satisfying `P`; Mathlib has no name for either hypothesis
— they are the shape of `CategoryTheory.EnoughInjectives.presentation`, resp.
`CategoryTheory.EnoughProjectives.presentation`, with `P` in place of injectivity, resp.
projectivity, and the second is strictly stronger than
`CategoryTheory.ObjectProperty.IsSeparating`, which allows coproducts.

The boundedness conditions are Mathlib's classes for cochain complexes indexed by `ℤ`:
`H ^ n (K) = 0` for `n < a` is `CochainComplex.IsGE K a` (see `CochainComplex.exactAt_of_isGE`)
and `K.X n = 0` for `n < a` is `CochainComplex.IsStrictlyGE K a` (see
`CochainComplex.isZero_of_isStrictlyGE`); the latter implies the former, and mirror-image for
`IsLE` and `IsStrictlyLE`. Both bounds obtained are sharp (`L.IsStrictlyGE a`, not `a - 1`), as in
the source; Mathlib's special case for `P` the injective objects,
`CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective`, loses one degree. The
source's `K^n → I^n` injective is stated degreewise, `∀ n, Mono (f.f n)`; it implies `Mono f` by
`HomologicalComplex.mono_of_mono_f`.

Parts (1) and (2) of 05T6 differ only in that (1) assumes the stronger, strict bound on `K` and
gets the stronger, degreewise monomorphic quasi-isomorphism, so they are stated as a single
assertion: one complex `K`, cohomologically bounded below, one resolution, and the monomorphy
clause conditional on `K` being strictly bounded below. For 05T7 the two parts share every
hypothesis on `A`, `P` and `a` and differ only in the complexes they quantify over — a strictly
bounded above one in part (1), a cohomologically bounded above one in part (2) — so they are
stated as the two conjuncts of a single result, with the complex and its bound inside each
conjunct; part (1) is what the source's own proof of part (2) applies to the truncation
`τ_{≤a}K`.

Each construction is an induction over `ℕ`, obtained by reindexing the source's induction on
degrees along `ComplexShape.embeddingUpIntGE a`, resp. `ComplexShape.embeddingUpIntLE a`, so that
it happens for a complex indexed by `ℕ` and the cochain complex bounded on one side is recovered
by `HomologicalComplex.extend`. The induction hypothesis is a `Rung`: the two terms of the
resolution in consecutive degrees with the differential between them, the monomorphism from
(epimorphism onto) the corresponding term, and the induced map on opcycles (cycles) — the data
the step consumes, rather than a complex-valued partial construction. Only the last of its fields
has content, and it is produced by the refinement calculus of `CategoryTheory.Abelian`
(`epi_iff_surjective_up_to_refinements`) rather than by elements. The step covers, resp. is
covered by, a fibre product of the terms constructed so far with the next term of the complex.

## References

* [StacksProject 05T6](https://stacks.math.columbia.edu/tag/05T6)
* [StacksProject 05T7](https://stacks.math.columbia.edu/tag/05T7)
-/

universe v u

open CategoryTheory Limits HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace CochainComplex

/-! ### The inductive construction -/

section Transport

variable {ι : Type*} {c : ComplexShape ι}

/-- The complex obtained from `L` by replacing each object `L.X n` by an isomorphic one. -/
private def transport (L : HomologicalComplex A c) (Y : ι → A)
    (ε : ∀ n, Y n ≅ L.X n) : HomologicalComplex A c where
  X := Y
  d i j := (ε i).hom ≫ L.d i j ≫ (ε j).inv
  shape i j h := by simp [L.shape i j h]
  d_comp_d' i j k _ _ := by simp

/-- The complex `transport L Y ε` is isomorphic to `L`. -/
private def transportIso (L : HomologicalComplex A c) (Y : ι → A)
    (ε : ∀ n, Y n ≅ L.X n) : transport L Y ε ≅ L :=
  Hom.isoOfComponents ε (fun i j _ => by simp [transport])

/-- A complex all of whose objects are isomorphic to objects satisfying `P` is isomorphic to a
complex all of whose objects satisfy `P`. -/
private lemma exists_iso_prop (P : ObjectProperty A) (L : HomologicalComplex A c)
    (h : ∀ n, ∃ Y, P Y ∧ Nonempty (Y ≅ L.X n)) :
    ∃ (L' : HomologicalComplex A c) (_ : L' ≅ L), ∀ n, P (L'.X n) := by
  choose Y hY hiso using h
  exact ⟨transport L Y (fun n => (hiso n).some), transportIso L Y _, hY⟩

/-- Extending along an embedding a complex all of whose terms satisfy `P` gives a complex
isomorphic to one all of whose terms satisfy `P`. -/
private lemma exists_iso_prop_extend {ι' : Type*} {c' : ComplexShape ι'} (P : ObjectProperty A)
    [P.ContainsZero] (e : c.Embedding c') (N : HomologicalComplex A c) (hN : ∀ n, P (N.X n)) :
    ∃ (L : HomologicalComplex A c') (_ : L ≅ N.extend e), ∀ n, P (L.X n) := by
  obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
  refine exists_iso_prop P _ (fun n => ?_)
  by_cases! hn : ∃ k, e.f k = n
  · obtain ⟨k, hk⟩ := hn
    exact ⟨N.X k, hN k, ⟨(extendXIso N e hk).symm⟩⟩
  · exact ⟨Z, hPZ, ⟨hZ.iso (isZero_extend_X _ _ _ hn)⟩⟩

/-- A morphism of complexes inducing a monomorphism and an epimorphism on homology in every
degree is a quasi-isomorphism. -/
private lemma quasiIso_of_mono_of_epi_homologyMap {K L : HomologicalComplex A c} (φ : K ⟶ L)
    (hm : ∀ j, Mono (homologyMap φ j)) (he : ∀ j, Epi (homologyMap φ j)) : QuasiIso φ where
  quasiIsoAt j := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have := hm j
    have := he j
    exact isIso_of_mono_of_epi _

end Transport

namespace propResolution

suppress_compilation

/-- A choice, for every object `X` of `A`, of a monomorphism from `X` into an object
satisfying `P`. -/
private structure Cover (P : ObjectProperty A) where
  /-- the chosen object containing `X` -/
  obj : A → A
  prop : ∀ X, P (obj X)
  /-- the chosen monomorphism `X ⟶ obj X` -/
  incl : ∀ X, X ⟶ obj X
  mono_incl : ∀ X, Mono (incl X)

/-- A morphism annihilated by the projection to a cokernel factors, up to refinements, through
the morphism that cokernel is taken of. -/
private lemma exists_factor_of_comp_cokernel_π_eq_zero {X Y W : A} (h : X ⟶ Y) (u : W ⟶ Y)
    (hu : u ≫ cokernel.π h = 0) :
    ∃ (W' : A) (π : W' ⟶ W) (_ : Epi π) (x : W' ⟶ X), π ≫ u = x ≫ h :=
  (Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
    (cokernelIsCokernel h) u).1 hu

/-- The universal property of a pushout square in an abelian category, read through
refinements: a pair of morphisms to the two other corners whose images in the pushout cancel
comes, up to refinements, from a morphism to the initial corner. -/
private lemma exists_lift_of_isPushout {X₁ X₂ X₃ X₄ : A} {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃}
    {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄} (sq : IsPushout f g inl inr) {W : A}
    (s : W ⟶ X₂) (t : W ⟶ X₃) (hst : s ≫ inl + t ≫ inr = 0) :
    ∃ (W' : A) (π : W' ⟶ W) (_ : Epi π) (w : W' ⟶ X₁),
      π ≫ s = w ≫ f ∧ π ≫ t = -(w ≫ g) := by
  obtain ⟨W', π, hπ, w, hw⟩ := sq.exact_shortComplex.exact_up_to_refinements (biprod.lift s t)
    (show biprod.lift s t ≫ biprod.desc inl inr = 0 by rwa [biprod.lift_desc])
  -- the map of the short complex of `sq` is `biprod.lift f (-g)` only definitionally, so the
  -- lift and its defining equation are repackaged with the types they are used at
  obtain ⟨w, hw'⟩ : ∃ w : W' ⟶ X₁, π ≫ biprod.lift s t = w ≫ biprod.lift f (-g) := ⟨w, hw⟩
  refine ⟨W', π, hπ, w, ?_, ?_⟩
  · have h := hw' =≫ biprod.fst
    rwa [Category.assoc, Category.assoc, biprod.lift_fst, biprod.lift_fst] at h
  · have h := hw' =≫ biprod.snd
    rwa [Category.assoc, Category.assoc, biprod.lift_snd, biprod.lift_snd,
      Preadditive.comp_neg] at h

/-- One rung of the inductive construction of a resolution of a cochain complex `M`: the terms
of the resolution in degrees `k - 1` and `k`, the differential between them and the map from
`M` in degree `k`, together with the induced monomorphism from the opcycles of `M` into the
cokernel of that differential. -/
private structure Rung (M : CochainComplex A ℕ) (P : ObjectProperty A) (k : ℕ) where
  /-- the term in degree `k - 1` of the resolution constructed so far -/
  Ym : A
  /-- the term in degree `k` of the resolution constructed so far -/
  Y : A
  hY : P Y
  /-- the differential into degree `k` -/
  δ : Ym ⟶ Y
  /-- the component in degree `k` of the map from `M` -/
  α : M.X k ⟶ Y
  hα : Mono α
  /-- the induced monomorphism from the opcycles of `M` into those of the resolution -/
  β : M.opcycles k ⟶ cokernel δ
  hβ : Mono β
  hβα : M.pOpcycles k ≫ β = α ≫ cokernel.π δ

variable {P : ObjectProperty A}

/-- Criterion for the morphism induced on the opcycles in degree `k + 1` by `γ` to be a
monomorphism: a morphism to `M.X (k + 1)` annihilated by `γ` is, up to refinements, a
boundary. -/
private lemma mono_descOpcycles {M : CochainComplex A ℕ} {k : ℕ} {Z : A}
    (γ : M.X (k + 1) ⟶ Z) (h : M.d k (k + 1) ≫ γ = 0)
    (H : ∀ ⦃W : A⦄ (x : W ⟶ M.X (k + 1)), x ≫ γ = 0 →
      ∃ (W' : A) (π : W' ⟶ W) (_ : Epi π) (t : W' ⟶ M.X k), π ≫ x = t ≫ M.d k (k + 1)) :
    Mono (M.descOpcycles γ k (prev_nat_succ k) h) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro W z hz
  obtain ⟨W₁, π₁, _, x, hx⟩ := surjective_up_to_refinements_of_epi (M.pOpcycles (k + 1)) z
  have hxγ : x ≫ γ = 0 := by
    simpa only [Category.assoc, hz, comp_zero, M.p_descOpcycles] using
      (hx =≫ M.descOpcycles γ k (prev_nat_succ k) h).symm
  obtain ⟨W₂, π₂, _, t, ht⟩ := H x hxγ
  rw [← cancel_epi (π₂ ≫ π₁), comp_zero, Category.assoc, hx, ← Category.assoc, ht,
    Category.assoc, M.d_pOpcycles, comp_zero]

namespace Rung

variable {M : CochainComplex A ℕ} {k : ℕ}

/-- The pushout of the opcycles of the resolution constructed so far and of `M.X (k + 1)`
over the opcycles of `M`. -/
private abbrev pushoutObj (r : Rung M P k) : A :=
  pushout r.β (M.fromOpcycles k (k + 1))

/-- The differential into degree `k + 1` of the resolution. -/
private abbrev stepδ (c : Cover P) (r : Rung M P k) :
    r.Y ⟶ c.obj r.pushoutObj :=
  cokernel.π r.δ ≫ pushout.inl r.β (M.fromOpcycles k (k + 1)) ≫ c.incl r.pushoutObj

/-- The component in degree `k + 1` of the map from `M` to the resolution. -/
private abbrev stepα (c : Cover P) (r : Rung M P k) :
    M.X (k + 1) ⟶ c.obj r.pushoutObj :=
  pushout.inr r.β (M.fromOpcycles k (k + 1)) ≫ c.incl r.pushoutObj

/-- The commutation rule of the inductive step. -/
private lemma d_comp_stepα (c : Cover P) (r : Rung M P k) :
    M.d k (k + 1) ≫ r.stepα c = r.α ≫ r.stepδ c := by
  rw [← M.p_fromOpcycles k (k + 1), stepα, stepδ]
  simp only [Category.assoc, ← reassoc_of% pushout.condition, ← reassoc_of% r.hβα]

/-- The differential into degree `k` is annihilated by the next differential. -/
private lemma δ_comp_stepδ (c : Cover P) (r : Rung M P k) : r.δ ≫ r.stepδ c = 0 := by
  simp [stepδ]

/-- The lifting property of the inductive step: a morphism to `M.X (k + 1)` whose image in the
cokernel of the differential into degree `k + 1` vanishes is, up to refinements, a boundary
of `M`. -/
private lemma step_lift (c : Cover P) (r : Rung M P k) {W : A} (x : W ⟶ M.X (k + 1))
    (hx : x ≫ r.stepα c ≫ cokernel.π (r.stepδ c) = 0) :
    ∃ (W' : A) (π : W' ⟶ W) (_ : Epi π) (t : W' ⟶ M.X k), π ≫ x = t ≫ M.d k (k + 1) := by
  have hm := c.mono_incl r.pushoutObj
  obtain ⟨W₁, π₁, _, v, hv⟩ := exists_factor_of_comp_cokernel_π_eq_zero (r.stepδ c)
    (x ≫ r.stepα c) (by rwa [Category.assoc])
  have key : (-(v ≫ cokernel.π r.δ)) ≫ pushout.inl r.β (M.fromOpcycles k (k + 1))
      + (π₁ ≫ x) ≫ pushout.inr r.β (M.fromOpcycles k (k + 1)) = 0 := by
    have h : ((π₁ ≫ x) ≫ pushout.inr r.β (M.fromOpcycles k (k + 1))) ≫ c.incl r.pushoutObj
        = ((v ≫ cokernel.π r.δ) ≫ pushout.inl r.β (M.fromOpcycles k (k + 1)))
          ≫ c.incl r.pushoutObj := by
      simpa only [Category.assoc] using hv
    rw [Preadditive.neg_comp, (cancel_mono (c.incl r.pushoutObj)).1 h, neg_add_cancel]
  obtain ⟨W₂, π₂, _, w, -, hw₂⟩ := exists_lift_of_isPushout
    (IsPushout.of_hasPushout r.β (M.fromOpcycles k (k + 1))) _ _ key
  obtain ⟨W₃, π₃, _, t, ht⟩ := surjective_up_to_refinements_of_epi (M.pOpcycles k) (-w)
  refine ⟨W₃, π₃ ≫ π₂ ≫ π₁, inferInstance, t, ?_⟩
  calc (π₃ ≫ π₂ ≫ π₁) ≫ x = π₃ ≫ π₂ ≫ π₁ ≫ x := by simp
    _ = π₃ ≫ (-(w ≫ M.fromOpcycles k (k + 1))) := by rw [← hw₂]
    _ = (π₃ ≫ (-w)) ≫ M.fromOpcycles k (k + 1) := by simp
    _ = t ≫ M.d k (k + 1) := by rw [ht, Category.assoc, M.p_fromOpcycles]

/-- The inductive step: the next term of the resolution is an object satisfying `P` which
contains the pushout `pushoutObj`. -/
private def step (c : Cover P) (r : Rung M P k) : Rung M P (k + 1) where
  Ym := r.Y
  Y := c.obj r.pushoutObj
  hY := c.prop _
  δ := r.stepδ c
  α := r.stepα c
  hα := by
    have := r.hβ
    have := c.mono_incl r.pushoutObj
    exact mono_comp _ _
  β := M.descOpcycles (r.stepα c ≫ cokernel.π (r.stepδ c)) k (prev_nat_succ k)
    (by rw [← Category.assoc, r.d_comp_stepα, Category.assoc, cokernel.condition, comp_zero])
  hβ := mono_descOpcycles _ _ (fun _ x hx => r.step_lift c x hx)
  hβα := M.p_descOpcycles _ _ _ _

/-- The rung in degree `0`: an object satisfying `P` containing `M.X 0`, with zero
differential. -/
private def base (c : Cover P) (M : CochainComplex A ℕ) : Rung M P 0 where
  Ym := c.obj (M.X 0)
  Y := c.obj (M.X 0)
  hY := c.prop _
  δ := 0
  α := c.incl (M.X 0)
  hα := c.mono_incl _
  β := M.descOpcycles (c.incl (M.X 0) ≫ cokernel.π (0 : c.obj (M.X 0) ⟶ c.obj (M.X 0))) 0
    prev_nat_zero (by rw [M.shape 0 0 (by simp), zero_comp])
  hβ := by
    have := c.mono_incl (M.X 0)
    refine (mono_comp_iff_of_isIso (M.pOpcycles 0) _).1 ?_
    rw [M.p_descOpcycles]
    exact mono_comp _ _
  hβα := M.p_descOpcycles _ _ _ _

end Rung

/-- The rungs of the resolution of `M` determined by the choice `c`. -/
private def rung (c : Cover P) (M : CochainComplex A ℕ) : ∀ k, Rung M P k :=
  Nat.rec (Rung.base c M) (fun _ r => r.step c)

private lemma rung_zero_δ (c : Cover P) (M : CochainComplex A ℕ) : (rung c M 0).δ = 0 := rfl

/-- The resolution of the cochain complex `M` determined by the choice `c`. -/
private abbrev resolution (c : Cover P) (M : CochainComplex A ℕ) :
    CochainComplex A ℕ :=
  CochainComplex.of (fun k => (rung c M k).Y) (fun k => (rung c M (k + 1)).δ)
    (fun k => (rung c M (k + 1)).δ_comp_stepδ c)

private lemma resolution_d (c : Cover P) (M : CochainComplex A ℕ) (k : ℕ) :
    (resolution c M).d k (k + 1) = (rung c M (k + 1)).δ :=
  CochainComplex.of_d (fun k => (rung c M k).Y) (fun k => (rung c M (k + 1)).δ) k

/-- The degreewise monomorphic map from `M` into its resolution. -/
private def resolutionMap (c : Cover P) (M : CochainComplex A ℕ) :
    M ⟶ resolution c M where
  f k := (rung c M k).α
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [resolution_d]
    exact ((rung c M i).d_comp_stepα c).symm

/-- The defining property of the monomorphism recorded by the rung in degree `k`, read on the
resolution. -/
private lemma pOpcycles_comp_rung_β (c : Cover P) (M : CochainComplex A ℕ) (k : ℕ) :
    M.pOpcycles k ≫ (rung c M k).β
      = (resolutionMap c M).f k ≫ cokernel.π (rung c M k).δ :=
  (rung c M k).hβα

/-- The differential into degree `j` of the resolution is annihilated by the projection to the
cokernel of the differential recorded by the rung in degree `j`. -/
private lemma resolution_d_comp_cokernel_π (c : Cover P) (M : CochainComplex A ℕ) (j : ℕ) :
    (resolution c M).d ((ComplexShape.up ℕ).prev j) j ≫ cokernel.π (rung c M j).δ = 0 := by
  cases j with
  | zero => rw [prev_nat_zero, (resolution c M).shape 0 0 (by simp), zero_comp]
  | succ k =>
    rw [prev_nat_succ, resolution_d]
    exact cokernel.condition _

/-- A morphism to the source of the differential recorded by the rung in degree `j` may be
replaced by a morphism to the term of degree `j - 1` of the resolution. -/
private lemma exists_factor_resolution_d (c : Cover P) (M : CochainComplex A ℕ) (j : ℕ)
    {W : A} (t : W ⟶ (rung c M j).Ym) :
    ∃ u : W ⟶ (resolution c M).X ((ComplexShape.up ℕ).prev j),
      u ≫ (resolution c M).d ((ComplexShape.up ℕ).prev j) j = t ≫ (rung c M j).δ := by
  cases j with
  | zero =>
    rw [prev_nat_zero]
    exact ⟨0, by rw [zero_comp, rung_zero_δ, comp_zero]⟩
  | succ k =>
    rw [prev_nat_succ]
    exact ⟨t, by rw [resolution_d]; rfl⟩

/-- Injectivity on cohomology: a cocycle of `M` whose image in the resolution is a boundary is,
up to refinements, a boundary. -/
private lemma mono_homologyMap_resolutionMap (c : Cover P) (M : CochainComplex A ℕ) (j : ℕ) :
    Mono (homologyMap (resolutionMap c M) j) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _
    ((ComplexShape.up ℕ).prev j) j (j + 1) rfl (CochainComplex.next ℕ j)]
  intro W x₂ hx₂ y₁ hy₁
  have := (rung c M j).hβ
  rw [← M.comp_pOpcycles_eq_zero_iff_up_to_refinements x₂ ((ComplexShape.up ℕ).prev j) rfl,
    ← cancel_mono (rung c M j).β, zero_comp, Category.assoc, pOpcycles_comp_rung_β,
    ← Category.assoc, hy₁, Category.assoc, resolution_d_comp_cokernel_π, comp_zero]

/-- Surjectivity on cohomology: a cocycle of the resolution is, up to refinements, the image of
a cocycle of `M` modulo a boundary. -/
private lemma epi_homologyMap_resolutionMap (c : Cover P) (M : CochainComplex A ℕ) (j : ℕ) :
    Epi (homologyMap (resolutionMap c M) j) := by
  rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _
    ((ComplexShape.up ℕ).prev j) j (j + 1) rfl (CochainComplex.next ℕ j)]
  intro W y₂ hy₂
  have hm := c.mono_incl (rung c M j).pushoutObj
  rw [resolution_d] at hy₂
  have h₀ : (y₂ ≫ cokernel.π (rung c M j).δ)
      ≫ pushout.inl (rung c M j).β (M.fromOpcycles j (j + 1)) = 0 :=
    zero_of_comp_mono (c.incl (rung c M j).pushoutObj) (by
      rwa [Category.assoc, Category.assoc])
  obtain ⟨W₁, π₁, _, w, hw₁, hw₂⟩ := exists_lift_of_isPushout
    (IsPushout.of_hasPushout (rung c M j).β (M.fromOpcycles j (j + 1)))
    (y₂ ≫ cokernel.π (rung c M j).δ) 0 (by rw [h₀, zero_comp, add_zero])
  have hwg : w ≫ M.fromOpcycles j (j + 1) = 0 := by simpa using hw₂.symm
  obtain ⟨W₂, π₂, _, x₂, hx₂⟩ := surjective_up_to_refinements_of_epi (M.pOpcycles j) w
  have hcyc : x₂ ≫ M.d j (j + 1) = 0 := by
    rw [← M.p_fromOpcycles j (j + 1), ← Category.assoc, ← hx₂, Category.assoc, hwg, comp_zero]
  have hstep : (π₂ ≫ π₁ ≫ y₂ - x₂ ≫ (resolutionMap c M).f j)
      ≫ cokernel.π (rung c M j).δ = 0 := by
    have h : x₂ ≫ (resolutionMap c M).f j ≫ cokernel.π (rung c M j).δ
        = π₂ ≫ π₁ ≫ y₂ ≫ cokernel.π (rung c M j).δ := by
      rw [← pOpcycles_comp_rung_β, ← Category.assoc, ← hx₂, Category.assoc, ← hw₁]
    simp only [Preadditive.sub_comp, Category.assoc, ← h, sub_self]
  obtain ⟨W₃, π₃, _, u, hu⟩ := exists_factor_of_comp_cokernel_π_eq_zero _ _ hstep
  obtain ⟨y₁, hy₁⟩ := exists_factor_resolution_d c M j u
  refine ⟨W₃, π₃ ≫ π₂ ≫ π₁, inferInstance, π₃ ≫ x₂,
    by rw [Category.assoc, hcyc, comp_zero], y₁, ?_⟩
  rw [Preadditive.comp_sub, ← hy₁, sub_eq_iff_eq_add] at hu
  simp only [Category.assoc] at hu ⊢
  rw [hu, add_comm]

private lemma quasiIso_resolutionMap (c : Cover P) (M : CochainComplex A ℕ) :
    QuasiIso (resolutionMap c M) :=
  quasiIso_of_mono_of_epi_homologyMap _ (mono_homologyMap_resolutionMap c M)
    (epi_homologyMap_resolutionMap c M)

/-- **Stacks 05T6(1)** for cochain complexes indexed by `ℕ`: if every object of `A` is a
subobject of an object satisfying `P`, then every cochain complex `M` indexed by `ℕ` admits a
degreewise monomorphic quasi-isomorphism into a cochain complex all of whose terms satisfy `P`.

This is the source's ascending induction: the resolution is built one degree at a time, the term
in degree `k + 1` being an object satisfying `P` which contains the pushout of
`M.opcycles k ⟶ M ^ {k + 1}` along `M.opcycles k ⟶ coker (N.d (k - 1) k)`. The invariant
carried along is that the latter morphism is a monomorphism; it alone gives injectivity and
surjectivity on cohomology in every degree. -/
private lemma exists_mono_quasiIso_of_prop_nat (P : ObjectProperty A)
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (i : X ⟶ Y), Mono i) (M : CochainComplex A ℕ) :
    ∃ (N : CochainComplex A ℕ) (f : M ⟶ N) (_ : ∀ k, Mono (f.f k)) (_ : QuasiIso f),
      ∀ k, P (N.X k) := by
  choose Y hY i hi using hP
  exact ⟨resolution ⟨Y, hY, i, hi⟩ M, resolutionMap _ M, fun k => (rung _ M k).hα,
    quasiIso_resolutionMap _ M, fun k => (rung _ M k).hY⟩

/-- **Stacks 05T6(1)**: a cochain complex `K` with `K.X n = 0` for `n < a` admits a degreewise
monomorphic quasi-isomorphism into a complex `L` with `L.X n = 0` for `n < a` and all `L.X n`
satisfying `P`. -/
private lemma exists_mono_quasiIso_of_prop_of_isStrictlyGE (P : ObjectProperty A)
    [P.ContainsZero] (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (i : X ⟶ Y), Mono i) (a : ℤ)
    (K : CochainComplex A ℤ) [K.IsStrictlyGE a] :
    ∃ (L : CochainComplex A ℤ) (f : K ⟶ L) (_ : ∀ n, Mono (f.f n)) (_ : QuasiIso f)
      (_ : ∀ n, P (L.X n)), L.IsStrictlyGE a := by
  let e := ComplexShape.embeddingUpIntGE a
  have hef : ∀ k : ℕ, e.f k = a + k := fun _ => rfl
  obtain ⟨N, f, hmono, hqis, hPN⟩ := exists_mono_quasiIso_of_prop_nat P hP (K.truncGE' e)
  obtain ⟨L, i, hPL⟩ := exists_iso_prop_extend P e N hPN
  have hex : ∀ n, Mono ((extendMap f e).f n) := fun n => by
    by_cases hn : n < a
    · exact (isZero_extend_X _ _ _ (fun k => by rw [hef]; omega)).mono _
    · have hn' : e.f (n - a).toNat = n := by rw [hef]; omega
      rw [extendMap_f f e hn']
      have := hmono (n - a).toNat
      infer_instance
  have : QuasiIso (extendMap f e) := (quasiIso_extendMap_iff f e).mpr hqis
  have : IsIso (K.πTruncGE a) := (K.isIso_πTruncGE_iff a).2 inferInstance
  -- `K.truncGE a` is the extension of `K.truncGE' e` only definitionally, and neither `rw` nor
  -- instance search unfolds it, so the projection is repackaged with the type it is composed at
  obtain ⟨φ, _⟩ : ∃ φ : K ⟶ (K.truncGE' e).extend e, IsIso φ := ⟨K.πTruncGE a, ‹_›⟩
  refine ⟨L, φ ≫ extendMap f e ≫ i.inv, fun n => ?_, inferInstance, hPL,
    isStrictlyGE_of_iso i.symm a⟩
  have := hex n
  rw [comp_f, comp_f]
  infer_instance

end propResolution

/-- **Stacks 05T6.** Let `A` be an abelian category, let `P` be a class of objects of `A`
containing a zero object and such that every object of `A` is a subobject of an object
satisfying `P`, and let `a : ℤ`. Let `K` be a cochain complex with `H ^ n (K) = 0` for `n < a`.
Then there is a quasi-isomorphism `f : K ⟶ L` with all `L.X n` satisfying `P` and `L.X n = 0`
for `n < a`; and if moreover `K.X n = 0` for `n < a`, then `f` can be chosen with all `f.f n`
monomorphisms. (Part (2) of the source is the statement with the last clause dropped, part (1)
is the statement for a strictly bounded below `K`.) -/
@[stacks 05T6]
public theorem exists_quasiIso_prop_isStrictlyGE (P : ObjectProperty A) [P.ContainsZero]
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (i : X ⟶ Y), Mono i) (a : ℤ)
    (K : CochainComplex A ℤ) [K.IsGE a] :
    ∃ (L : CochainComplex A ℤ) (f : K ⟶ L) (_ : QuasiIso f) (_ : ∀ n, P (L.X n))
      (_ : K.IsStrictlyGE a → ∀ n, Mono (f.f n)), L.IsStrictlyGE a := by
  obtain ⟨L, f, hmono, hqis, hPL, hGE⟩ :=
    propResolution.exists_mono_quasiIso_of_prop_of_isStrictlyGE P hP a (K.truncGE a)
  have : QuasiIso (K.πTruncGE a) := (K.quasiIso_πTruncGE_iff a).mpr inferInstance
  refine ⟨L, K.πTruncGE a ≫ f, inferInstance, hPL, fun hK n => ?_, hGE⟩
  have : IsIso (K.πTruncGE a) := (K.isIso_πTruncGE_iff a).2 hK
  have := hmono n
  rw [comp_f]
  infer_instance

/-! ### Resolutions by a class of objects every object is a quotient of -/

namespace propCoresolution

section General

variable {ι : Type*} {c : ComplexShape ι}

/-- The inclusion of the cycles in degree `i` is annihilated by the map to the cycles in
degree `j` induced by the differential. -/
private lemma iCycles_comp_toCycles (K : HomologicalComplex A c) (i j : ι)
    [K.HasHomology i] [K.HasHomology j] : K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), zero_comp, Category.assoc, K.toCycles_i, iCycles_d]

/-- Criterion for the map onto the cycles in degree `i` induced by a map `φ : Y ⟶ K.X i` which
lands in the cycles to be an epimorphism: every cycle in degree `i` factors through `φ`, up to
refinements. -/
private lemma epi_liftCycles {K : HomologicalComplex A c} {i j : ι} [K.HasHomology i]
    (hj : c.next i = j) {Y : A} (φ : Y ⟶ K.X i) (hφ : φ ≫ K.d i j = 0)
    (H : ∀ ⦃W : A⦄ (z : W ⟶ K.cycles i), ∃ (W' : A) (π : W' ⟶ W) (_ : Epi π) (t : W' ⟶ Y),
      t ≫ φ = π ≫ z ≫ K.iCycles i) :
    Epi (K.liftCycles φ j hj hφ) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro W z
  obtain ⟨W', π, hπ, t, ht⟩ := H z
  refine ⟨W', π, hπ, t, ?_⟩
  rw [← cancel_mono (K.iCycles i)]
  simpa only [Category.assoc, liftCycles_i] using ht.symm
end General

/-- A choice, for every object `X` of `A`, of an epimorphism onto `X` from an object
satisfying `P`. -/
private structure Cover (P : ObjectProperty A) where
  /-- the chosen object covering `X` -/
  obj : A → A
  prop : ∀ X, P (obj X)
  /-- the chosen epimorphism `obj X ⟶ X` -/
  proj : ∀ X, obj X ⟶ X
  epi_proj : ∀ X, Epi (proj X)

/-- One rung of the inductive construction of a resolution of a chain complex `M`: the terms
of the resolution in degrees `k - 1` and `k`, the differential and the map to `M` in degree
`k`, together with the induced epimorphism from the cycles onto the cycles of `M`. -/
private structure Rung (M : ChainComplex A ℕ) (P : ObjectProperty A) (k : ℕ) where
  /-- the term in degree `k - 1` of the resolution constructed so far -/
  Yp : A
  /-- the term in degree `k` of the resolution constructed so far -/
  Y : A
  hY : P Y
  /-- the differential out of degree `k` -/
  δ : Y ⟶ Yp
  /-- the component in degree `k` of the map to `M` -/
  α : Y ⟶ M.X k
  hα : Epi α
  /-- the induced map from the cycles of the resolution onto the cycles of `M` -/
  β : kernel δ ⟶ M.cycles k
  hβ : Epi β
  hβα : β ≫ M.iCycles k = kernel.ι δ ≫ α

section Resolution

variable {P : ObjectProperty A}

/-- A rung assembled from its differential `δ` and its epimorphism `α` onto `M.X k`: the map to
the cycles of `M` is the one induced by `kernel.ι δ ≫ α`, so the only thing to be checked is
that it is an epimorphism. -/
private noncomputable def Rung.ofLiftCycles {M : ChainComplex A ℕ} {k j : ℕ}
    (hj : (ComplexShape.down ℕ).next k = j) {Yp Y : A} (hY : P Y) (δ : Y ⟶ Yp)
    (α : Y ⟶ M.X k) (hα : Epi α) (h : (kernel.ι δ ≫ α) ≫ M.d k j = 0)
    (hβ : Epi (M.liftCycles (kernel.ι δ ≫ α) j hj h)) : Rung M P k where
  Yp := Yp
  Y := Y
  hY := hY
  δ := δ
  α := α
  hα := hα
  β := M.liftCycles (kernel.ι δ ≫ α) j hj h
  hβ := hβ
  hβα := M.liftCycles_i _ _ _ _

/-- The rung in degree `0`: a cover of `M.X 0`, with zero differential. Its map to the cycles
of `M` in degree `0` is an epimorphism because `M.iCycles 0` is an isomorphism. -/
private noncomputable def Rung.base (c : Cover P) (M : ChainComplex A ℕ) : Rung M P 0 :=
  .ofLiftCycles ChainComplex.next_nat_zero (c.prop _) (0 : c.obj (M.X 0) ⟶ c.obj (M.X 0))
    (c.proj _) (c.epi_proj _) (by rw [M.shape 0 0 (by simp)]; simp)
    (by
      have := c.epi_proj (M.X 0)
      rw [← epi_comp_iff_of_isIso _ (M.iCycles 0), liftCycles_i]
      infer_instance)

/-- The commutation rule underlying the inductive step: a map to the fibre product
`(ker δ) ×_{Z_k(M)} M_{k+1}`, followed by the differential of `M`, agrees with its first
projection followed by the previous component of the map to `M`. -/
private lemma Rung.pullback_snd_comp_d {M : ChainComplex A ℕ} {k : ℕ} (r : Rung M P k)
    {W : A} (u : W ⟶ pullback r.β (M.toCycles (k + 1) k)) :
    (u ≫ pullback.snd r.β (M.toCycles (k + 1) k)) ≫ M.d (k + 1) k
      = (u ≫ pullback.fst r.β (M.toCycles (k + 1) k) ≫ kernel.ι r.δ) ≫ r.α := by
  simp only [Category.assoc]
  rw [← r.hβα, pullback.condition_assoc, M.toCycles_i]

/-- The inductive step: cover the fibre product of the cycles constructed so far in degree
`k` with the terms of `M` in degree `k + 1`. Its map to the cycles of `M` in degree `k + 1` is
an epimorphism because a cycle `z` of `M` there, paired with `0`, is a map to the fibre
product, hence lifts to the cover up to refinements. -/
private noncomputable def Rung.step {M : ChainComplex A ℕ} {k : ℕ} (c : Cover P)
    (r : Rung M P k) : Rung M P (k + 1) :=
  .ofLiftCycles (ChainComplex.next_nat_succ k) (c.prop _)
    (c.proj (pullback r.β (M.toCycles (k + 1) k)) ≫
      pullback.fst r.β (M.toCycles (k + 1) k) ≫ kernel.ι r.δ)
    (c.proj (pullback r.β (M.toCycles (k + 1) k)) ≫ pullback.snd r.β (M.toCycles (k + 1) k))
    (by
      have := r.hβ
      have := c.epi_proj (pullback r.β (M.toCycles (k + 1) k))
      exact epi_comp _ _)
    (by rw [Category.assoc, r.pullback_snd_comp_d, ← Category.assoc, kernel.condition_assoc,
      zero_comp])
    (by
      have := c.epi_proj (pullback r.β (M.toCycles (k + 1) k))
      refine epi_liftCycles _ _ _ (fun W z => ?_)
      obtain ⟨W', π, hπ, t, ht⟩ := surjective_up_to_refinements_of_epi
        (c.proj (pullback r.β (M.toCycles (k + 1) k)))
        (pullback.lift (0 : W ⟶ kernel r.δ) (z ≫ M.iCycles (k + 1))
          (by rw [zero_comp, Category.assoc, iCycles_comp_toCycles, comp_zero]))
      refine ⟨W', π, hπ, kernel.lift _ t ?_, ?_⟩
      · simp only [← reassoc_of% ht, pullback.lift_fst_assoc, zero_comp, comp_zero]
      · simp only [kernel.lift_ι_assoc, ← reassoc_of% ht, pullback.lift_snd])

/-- The differentials of two consecutive rungs compose to zero: the differential produced by
the step factors through the kernel of the previous one. -/
private lemma Rung.step_δ_comp_δ {M : ChainComplex A ℕ} {k : ℕ} (c : Cover P) (r : Rung M P k) :
    (r.step c).δ ≫ r.δ = 0 := by
  change (c.proj _ ≫ pullback.fst r.β (M.toCycles (k + 1) k) ≫ kernel.ι r.δ) ≫ r.δ = 0
  simp

/-- The commutation rule of the inductive step. -/
private lemma Rung.step_comm {M : ChainComplex A ℕ} {k : ℕ} (c : Cover P) (r : Rung M P k) :
    (r.step c).α ≫ M.d (k + 1) k = (r.step c).δ ≫ r.α :=
  r.pullback_snd_comp_d _

/-- The lifting property of the inductive step: a cycle of the resolution in degree `k` whose
image in `M` is a boundary is itself, up to refinements, a boundary. -/
private lemma Rung.step_lift {M : ChainComplex A ℕ} {k : ℕ} (c : Cover P) (r : Rung M P k)
    {W : A} (v : W ⟶ kernel r.δ) (y : W ⟶ M.X (k + 1))
    (h : v ≫ r.β = y ≫ M.toCycles (k + 1) k) :
    ∃ (W' : A) (π : W' ⟶ W) (_ : Epi π) (x : W' ⟶ (r.step c).Y),
      x ≫ (r.step c).δ = π ≫ v ≫ kernel.ι r.δ := by
  have := c.epi_proj (pullback r.β (M.toCycles (k + 1) k))
  obtain ⟨W', π, hπ, x, hx⟩ := surjective_up_to_refinements_of_epi
    (c.proj (pullback r.β (M.toCycles (k + 1) k))) (pullback.lift v y h)
  refine ⟨W', π, hπ, x, ?_⟩
  change x ≫ c.proj _ ≫ pullback.fst r.β (M.toCycles (k + 1) k) ≫ kernel.ι r.δ
    = π ≫ v ≫ kernel.ι r.δ
  simp only [← reassoc_of% hx, pullback.lift_fst_assoc]

/-- The rungs of the resolution of `M` determined by the cover `c`. -/
private noncomputable def rung (c : Cover P) (M : ChainComplex A ℕ) : ∀ k, Rung M P k :=
  Nat.rec (Rung.base c M) (fun _ r => r.step c)

private lemma rung_zero_δ (c : Cover P) (M : ChainComplex A ℕ) : (rung c M 0).δ = 0 := rfl

/-- The resolution of the chain complex `M` determined by the cover `c`. -/
private noncomputable abbrev resolution (c : Cover P) (M : ChainComplex A ℕ) :
    ChainComplex A ℕ :=
  ChainComplex.of (fun k => (rung c M k).Y) (fun k => (rung c M (k + 1)).δ)
    (fun k => (rung c M (k + 1)).step_δ_comp_δ c)

private lemma resolution_d (c : Cover P) (M : ChainComplex A ℕ) (k : ℕ) :
    (resolution c M).d (k + 1) k = (rung c M (k + 1)).δ :=
  ChainComplex.of_d (fun k => (rung c M k).Y) (fun k => (rung c M (k + 1)).δ) k

/-- The degreewise epimorphic map from the resolution of `M` onto `M`. -/
private noncomputable def resolutionMap (c : Cover P) (M : ChainComplex A ℕ) :
    resolution c M ⟶ M where
  f k := (rung c M k).α
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    change (rung c M (j + 1)).α ≫ M.d (j + 1) j
      = (resolution c M).d (j + 1) j ≫ (rung c M j).α
    rw [resolution_d]
    exact Rung.step_comm c (rung c M j)

private lemma resolutionMap_f (c : Cover P) (M : ChainComplex A ℕ) (k : ℕ) :
    (resolutionMap c M).f k = (rung c M k).α := rfl

private lemma resolution_d_comp_eq_zero_iff (c : Cover P) (M : ChainComplex A ℕ) (j : ℕ)
    {W : A} (x : W ⟶ (resolution c M).X j) :
    x ≫ (resolution c M).d j ((ComplexShape.down ℕ).next j) = 0
      ↔ x ≫ (rung c M j).δ = 0 := by
  cases j with
  | zero =>
    rw [ChainComplex.next_nat_zero, (resolution c M).shape 0 0 (by simp), rung_zero_δ]
    rfl
  | succ k =>
    rw [ChainComplex.next_nat_succ, resolution_d]
    rfl

private lemma epi_homologyMap_resolutionMap (c : Cover P) (M : ChainComplex A ℕ) (j : ℕ) :
    Epi (homologyMap (resolutionMap c M) j) := by
  rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ (j + 1) j
    ((ComplexShape.down ℕ).next j) (ChainComplex.prev ℕ j) rfl]
  intro W y₂ hy₂
  have := (rung c M j).hβ
  obtain ⟨W', π, hπ, u, hu⟩ := surjective_up_to_refinements_of_epi (rung c M j).β
    (M.liftCycles y₂ _ rfl hy₂)
  refine ⟨W', π, hπ, u ≫ kernel.ι (rung c M j).δ, ?_, 0, ?_⟩
  · rw [resolution_d_comp_eq_zero_iff]
    simp
  · rw [zero_comp, add_zero, resolutionMap_f, Category.assoc, ← (rung c M j).hβα,
      ← Category.assoc, ← hu, Category.assoc, liftCycles_i]

private lemma mono_homologyMap_resolutionMap (c : Cover P) (M : ChainComplex A ℕ) (j : ℕ) :
    Mono (homologyMap (resolutionMap c M) j) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ (j + 1) j
    ((ComplexShape.down ℕ).next j) (ChainComplex.prev ℕ j) rfl]
  intro W x₂ hx₂ y₁ hy₁
  rw [resolution_d_comp_eq_zero_iff] at hx₂
  obtain ⟨W', π, hπ, x, hx⟩ := Rung.step_lift c (rung c M j) (kernel.lift _ x₂ hx₂) y₁ (by
    rw [← cancel_mono (M.iCycles j), Category.assoc, (rung c M j).hβα, ← Category.assoc,
      kernel.lift_ι, Category.assoc, M.toCycles_i]
    exact hy₁)
  refine ⟨W', π, hπ, x, ?_⟩
  rw [resolution_d]
  exact (hx.trans (by rw [kernel.lift_ι])).symm

private lemma quasiIso_resolutionMap (c : Cover P) (M : ChainComplex A ℕ) :
    QuasiIso (resolutionMap c M) :=
  quasiIso_of_mono_of_epi_homologyMap _ (mono_homologyMap_resolutionMap c M)
    (epi_homologyMap_resolutionMap c M)

end Resolution

/-- **Stacks 05T7(1)** for chain complexes indexed by `ℕ`: if every object of `A` is a quotient
of an object satisfying `P`, then every chain complex `M` indexed by `ℕ` receives a degreewise
epimorphic quasi-isomorphism from a chain complex all of whose terms satisfy `P`. -/
private lemma exists_quasiIso_chainComplex (P : ObjectProperty A)
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p) (M : ChainComplex A ℕ) :
    ∃ (L : ChainComplex A ℕ) (f : L ⟶ M) (_ : ∀ k, Epi (f.f k)) (_ : QuasiIso f),
      ∀ k, P (L.X k) := by
  choose Y hY p hp using hP
  exact ⟨resolution ⟨Y, hY, p, hp⟩ M, resolutionMap _ M, fun k => (rung _ M k).hα,
    quasiIso_resolutionMap _ M, fun k => (rung _ M k).hY⟩

/-- Part (1) of Stacks 05T7. -/
private lemma exists_quasiIso_prop_of_isStrictlyLE (P : ObjectProperty A) [P.ContainsZero]
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p) (a : ℤ)
    (K : CochainComplex A ℤ) [K.IsStrictlyLE a] :
    ∃ (L : CochainComplex A ℤ) (f : L ⟶ K) (_ : ∀ n, Epi (f.f n)) (_ : QuasiIso f)
      (_ : ∀ n, P (L.X n)), L.IsStrictlyLE a := by
  let e := ComplexShape.embeddingUpIntLE a
  have hef : ∀ k : ℕ, e.f k = a - k := fun k => rfl
  obtain ⟨Ln, fn, hepi, hqis, hPL⟩ := exists_quasiIso_chainComplex P hP (K.truncLE' e)
  obtain ⟨L, i, hPL'⟩ := exists_iso_prop_extend P e Ln hPL
  refine ⟨L, i.hom ≫ extendMap fn e ≫ (K.truncLEIso e).inv ≫ K.ιTruncLE a, fun n => ?_,
    inferInstance, hPL', isStrictlyLE_of_iso i.symm a⟩
  by_cases hn : a < n
  · exact ⟨fun g h _ => (K.isZero_of_isStrictlyLE a n hn).eq_of_src g h⟩
  · have : Epi ((extendMap fn e).f n) := by
      rw [extendMap_f fn e (show e.f (a - n).toNat = n by rw [hef]; omega)]
      have := hepi (a - n).toNat
      infer_instance
    rw [comp_f, comp_f, comp_f]
    infer_instance

end propCoresolution

/-- **Stacks 05T7.** Let `A` be an abelian category, let `P` be a class of
objects of `A` containing a zero object and such that every object of `A` is a
quotient of an object satisfying `P`, and let `a : ℤ`.
(1) If `K.X n = 0` for `n > a`, there is a quasi-isomorphism `f : L ⟶ K` with
all `f.f n` epimorphisms, all `L.X n` satisfying `P`, and `L.X n = 0` for
`n > a`.
(2) If `H ^ n (K) = 0` for `n > a`, there is a quasi-isomorphism `f : L ⟶ K`
with all `L.X n` satisfying `P` and `L.X n = 0` for `n > a`. -/
@[stacks 05T7]
public theorem exists_quasiIso_prop (P : ObjectProperty A)
    [P.ContainsZero] (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p) (a : ℤ) :
    (∀ (K : CochainComplex A ℤ) [K.IsStrictlyLE a],
        ∃ (L : CochainComplex A ℤ) (f : L ⟶ K) (_ : ∀ n, Epi (f.f n)) (_ : QuasiIso f)
          (_ : ∀ n, P (L.X n)), L.IsStrictlyLE a) ∧
      (∀ (K : CochainComplex A ℤ) [K.IsLE a],
        ∃ (L : CochainComplex A ℤ) (f : L ⟶ K) (_ : QuasiIso f) (_ : ∀ n, P (L.X n)),
          L.IsStrictlyLE a) := by
  refine ⟨fun K _ => propCoresolution.exists_quasiIso_prop_of_isStrictlyLE P hP a K,
    fun K _ => ?_⟩
  obtain ⟨L, f, -, hq, hPL, hLE⟩ :=
    propCoresolution.exists_quasiIso_prop_of_isStrictlyLE P hP a (K.truncLE a)
  exact ⟨L, f ≫ K.ιTruncLE a, inferInstance, hPL, hLE⟩

end CochainComplex

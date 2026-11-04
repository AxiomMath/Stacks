module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# A reassociated chain of two whiskerings is compatible with the shifts

A transformation of one-variable functors obtained from a transformation of bifunctors by fixing
one variable is, in this development, repeatedly of one shape: a transformation `θ` whiskered on
the right by a functor `h`, followed by a transformation `leg` whiskered on the left by a functor
`B`, with the two reassociations those whiskerings need written out as
`CategoryTheory.Functor.associator`s.  Its compatibility with the shifts is formal — Mathlib's
`CategoryTheory.NatTrans.CommShift.whiskerRight`, `whiskerLeft` and `associator`, plus
`CategoryTheory.NatTrans.CommShift.of_iso_inv` for the associator that is used backwards — but it
cannot be left to instance search at the point of use, for two reasons.

## Main results

* `CategoryTheory.NatTrans.commShift_assocChain`: **the chain
  `(associator q A h).inv ≫ Functor.whiskerRight θ h ≫ (associator B q' h).hom ≫
  Functor.whiskerLeft B leg` is compatible with the shifts**, given that `θ` and `leg` are.
* `CategoryTheory.NatTrans.commShift_assocChain₄` and `commShift_assocChain₄'`: **the same for a
  chain with two more whiskered factors and one more reassociation**, which is the shape the
  *second* comparison of [Stacks, Tag 079U] has in each variable: there the bifunctor acts on the
  fixed variable too and its value is transported as well.  The two differ only in the order of
  the first two whiskerings, which is opposite in the two variables.

## Implementation notes

**Why this is a lemma with every category, functor and transformation a variable.**  At a concrete
instantiation the `CategoryTheory.Functor.CommShift` datum that a chain's junction delivers and
the one its neighbour demands are the same structure reached along two routes — typically a field
of a `CategoryTheory.Functor.CommShift₂` closure instance on one side and a
`CategoryTheory.Functor.CommShift.comp` on the other.  The two are *equal*, by one of the `rfl`
lemmas of `StacksFrontier/CategoryTheory/Shift/CommShiftTwoDataTransport.lean`, but instance search
cannot see it: `CategoryTheory.Functor.CommShift₂.postcompInt` and Mathlib's `precomp₁`/`precomp₂`
are plain instances, so they are not unfolded at instance-reducible transparency.  Stating the
chain here, where every datum is a variable and each junction therefore matches on the nose, moves
the identification out of instance search and into the single `isDefEq` of the `exact` that applies
this lemma — and that one is performed at `default` transparency, where the closure instances *do*
unfold.

**Why `θ` and `leg` are hypotheses rather than instance arguments.**  For the same reason: a
consumer has their compatibility at the data its own `CommShift₂` structures provide, which
instance search would not match against `CommShift.comp q A` and `CommShift.comp B q'`.  Passed as
explicit arguments they are checked by `isDefEq` instead.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

/-- **A chain of two whiskerings, with the two reassociations they need written out, is
compatible with the shifts.**  The chain goes

`q ⋙ (A ⋙ h) ⟶ (q ⋙ A) ⋙ h ⟶ (B ⋙ q') ⋙ h ⟶ B ⋙ (q' ⋙ h) ⟶ B ⋙ p`,

whiskering `θ : q ⋙ A ⟶ B ⋙ q'` by `h` on the right and `leg : q' ⋙ h ⟶ p` by `B` on the left.
Each of the four factors is compatible with the shifts for a reason of Mathlib's — the two
associators by `CategoryTheory.NatTrans.CommShift.associator` and
`CategoryTheory.NatTrans.CommShift.of_iso_inv`, the two whiskerings by
`CategoryTheory.NatTrans.CommShift.whiskerRight` and `whiskerLeft` — and every junction joins two
syntactically identical commutation data, which is what the associators are written out for. -/
theorem commShift_assocChain {C D D' D'' E : Type*} [Category* C] [Category* D] [Category* D']
    [Category* D''] [Category* E] {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
    [HasShift D' M] [HasShift D'' M] [HasShift E M]
    (q : C ⥤ D) [q.CommShift M] (A : D ⥤ D') [A.CommShift M] (h : D' ⥤ E) [h.CommShift M]
    (B : C ⥤ D'') [B.CommShift M] (q' : D'' ⥤ D') [q'.CommShift M] (p : D'' ⥤ E) [p.CommShift M]
    (θ : q ⋙ A ⟶ B ⋙ q') (leg : q' ⋙ h ⟶ p)
    (hθ : NatTrans.CommShift θ M) (hleg : NatTrans.CommShift leg M) :
    NatTrans.CommShift ((Functor.associator q A h).inv ≫ Functor.whiskerRight θ h ≫
      (Functor.associator B q' h).hom ≫ Functor.whiskerLeft B leg) M := by
  have := hθ
  have := hleg
  infer_instance

/-- **A chain of four whiskered factors, with the three reassociations they need written out, is
compatible with the shifts.**  The chain goes

`q ⋙ (A ⋙ h₁) ⟶ (q ⋙ A) ⋙ h₁ ⟶ (q ⋙ A) ⋙ h₂ ⟶ (B ⋙ q') ⋙ h₂ ⟶ B ⋙ (q' ⋙ h₂) ⟶
  B ⋙ (u ⋙ q') ⟶ (B ⋙ u) ⋙ q' ⟶ (t ⋙ B) ⋙ q' ⟶ t ⋙ (B ⋙ q')`,

three of the steps being `CategoryTheory.Functor.associator`s and the four named ones the
whiskerings of `ν`, `θ`, `leg` and `rho`.  This is the shape each one-variable component of the
second comparison of [Stacks, Tag 079U] has: `ν` is the bifunctor's action on the *fixed*
variable, `θ` the comparison in the varying one, `leg` the transformation at the value and `rho`
the transport of the whole.

**Why `ν` and `θ` are hypotheses rather than their whiskerings being one abstract factor.**  Taking
the composite `Functor.whiskerLeft (q ⋙ A) ν ≫ Functor.whiskerRight θ h₂` as
a single abstract `head` would leave the consumer to produce its compatibility — and there it
cannot be had: the whiskerings need `CategoryTheory.Functor.CommShift` data on `(q ⋙ A) ⋙ h₁` and
`(q ⋙ A) ⋙ h₂`, at a concrete instantiation those are found by a search that competes with the
development's own one-variable instances for the same functors, and the two routes are not
identified.  Taking `ν` and `θ` apart keeps that search *inside this lemma*, where every datum is
a variable, the only instance available is the intended one and `infer_instance` is immediate. -/
theorem commShift_assocChain₄ {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁] {M : Type*} [AddMonoid M]
    [HasShift C₀ M] [HasShift C₁ M] [HasShift D₀ M] [HasShift D₁ M]
    (q : C₀ ⥤ D₀) [q.CommShift M] (A : D₀ ⥤ D₁) [A.CommShift M]
    (h₁ h₂ : D₁ ⥤ D₁) [h₁.CommShift M] [h₂.CommShift M]
    (B : C₀ ⥤ C₁) [B.CommShift M] (q' : C₁ ⥤ D₁) [q'.CommShift M]
    (u : C₁ ⥤ C₁) [u.CommShift M] (t : C₀ ⥤ C₀) [t.CommShift M]
    (ν : h₁ ⟶ h₂) (θ : q ⋙ A ⟶ B ⋙ q') (leg : q' ⋙ h₂ ⟶ u ⋙ q')
    (rho : B ⋙ u ⟶ t ⋙ B) (hν : NatTrans.CommShift ν M)
    (hθ : NatTrans.CommShift θ M) (hleg : NatTrans.CommShift leg M)
    (hrho : NatTrans.CommShift rho M) :
    NatTrans.CommShift ((Functor.associator q A h₁).inv ≫
      (Functor.whiskerLeft (q ⋙ A) ν ≫ Functor.whiskerRight θ h₂) ≫
      (Functor.associator B q' h₂).hom ≫ Functor.whiskerLeft B leg ≫
      (Functor.associator B u q').inv ≫ Functor.whiskerRight rho q' ≫
      (Functor.associator t B q').hom) M := by
  have := hν
  have := hθ
  have := hleg
  have := hrho
  infer_instance

/-- **`commShift_assocChain₄` with the first two whiskerings in the other order**, which is how the
same component reads in the *other* variable of the bifunctor: there the comparison `θ` acts first
and the action `ν` on the fixed variable follows it, whiskered by `B ⋙ q'` instead of by `q ⋙ A`.
Everything from `leg` on is unchanged. -/
theorem commShift_assocChain₄' {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁] {M : Type*} [AddMonoid M]
    [HasShift C₀ M] [HasShift C₁ M] [HasShift D₀ M] [HasShift D₁ M]
    (q : C₀ ⥤ D₀) [q.CommShift M] (A : D₀ ⥤ D₁) [A.CommShift M]
    (h₁ h₂ : D₁ ⥤ D₁) [h₁.CommShift M] [h₂.CommShift M]
    (B : C₀ ⥤ C₁) [B.CommShift M] (q' : C₁ ⥤ D₁) [q'.CommShift M]
    (u : C₁ ⥤ C₁) [u.CommShift M] (t : C₀ ⥤ C₀) [t.CommShift M]
    (ν : h₁ ⟶ h₂) (θ : q ⋙ A ⟶ B ⋙ q') (leg : q' ⋙ h₂ ⟶ u ⋙ q')
    (rho : B ⋙ u ⟶ t ⋙ B) (hν : NatTrans.CommShift ν M)
    (hθ : NatTrans.CommShift θ M) (hleg : NatTrans.CommShift leg M)
    (hrho : NatTrans.CommShift rho M) :
    NatTrans.CommShift ((Functor.associator q A h₁).inv ≫
      (Functor.whiskerRight θ h₁ ≫ Functor.whiskerLeft (B ⋙ q') ν) ≫
      (Functor.associator B q' h₂).hom ≫ Functor.whiskerLeft B leg ≫
      (Functor.associator B u q').inv ≫ Functor.whiskerRight rho q' ≫
      (Functor.associator t B q').hom) M := by
  have := hν
  have := hθ
  have := hleg
  have := hrho
  infer_instance

end CategoryTheory.NatTrans

end

module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacementDeltaFunctor
import StacksCore.Tactic.StacksAttribute

/-! # Universality of homological δ-functors, by transport to the opposite categories

`Stacks.CategoryHomology.HomologicalDeltaFunctor` is the homological counterpart of Stacks
010Q: additive functors `Hₙ : A ⥤ B` for `n ≥ 0` with connecting morphisms
`δ : Hₙ₊₁(X₃) ⟶ Hₙ(X₁)` for every short exact sequence `0 → X₁ → X₂ → X₃ → 0`, such that the
long sequence `⋯ → H₁(X₃) → H₀(X₁) → H₀(X₂) → H₀(X₃) → 0` is exact. This file equips it with
morphisms, with the dual of Stacks' effaceability hypothesis, and with the duals of 010T and
010U: *a coeffaceable homological δ-functor is universal, and a universal one is determined by
`H₀` up to unique isomorphism*.

## Design: op-transport, not mirroring

Nothing here re-proves Grothendieck's Tohoku argument. A homological δ-functor `H : A ⥤ B` is
*the same data* as a cohomological one `Aᵒᵖ ⥤ Bᵒᵖ`, because opposing both the source and the
target reverses the degree direction of `δ` exactly once: for `S : ShortComplex Aᵒᵖ` the
morphism `Hₙ₊₁(S.unop.X₃) ⟶ Hₙ(S.unop.X₁)` of `B` is, after `Quiver.Hom.op`, a morphism
`(Hₙ)ᵒᵖ(S.X₃) ⟶ (Hₙ₊₁)ᵒᵖ(S.X₁)` of `Bᵒᵖ`, which is the shape of a cohomological connecting
morphism. All ten fields of `HomologicalDeltaFunctor.op` are therefore the corresponding field
of `H` composed with `Quiver.Hom.op`, with `ShortComplex.unop`, `ShortComplex.ShortExact.unop`
and `ShortComplex.Exact.op` doing the bookkeeping; `exact_δ₁` transports to `exact_δ₂` and
back, and `epi_map_g` to `mono_map_f`.

The one point that has to be checked rather than asserted is that the *universality*
quantifier survives. It does, and it changes direction: `NatTrans.op` is contravariant, so a
morphism of homological δ-functors `H ⟶ G` is a cohomological morphism `G.op ⟶ H.op`
(`HomologicalDeltaFunctor.Hom.op`, with inverse `Hom.ofOp`). Hence Stacks 010S for `H.op` —
every `t : (H.op)⁰ ⟶ K⁰` extends uniquely to `H.op ⟶ K` — reads, at `K = G.op`, as: every
`t : G₀ ⟶ H₀` extends uniquely to `G ⟶ H`. That is `IsUniversal` below, and it is the correct
homological notion: a universal homological δ-functor is *terminal* among those with the given
`H₀`, just as left derived functors are terminal among homological δ-functors while right
derived functors are initial among cohomological ones. So the transport is not merely cheaper
than mirroring the 375 lines of
`StacksCore/CategoryTheory/Abelian/DeltaFunctor/Effaceable.lean`; it also delivers the dual
statement with the quantifier where the application needs it.

## Main definitions

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.Hom`: a morphism of homological δ-functors,
  a family `tₙ : Hₙ ⟶ Gₙ` commuting with the connecting morphisms, and the resulting category
  structure.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.op`: the cohomological δ-functor
  `Aᵒᵖ ⥤ Bᵒᵖ` carrying the same data.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffacement` and `Coeffaceable`: the dual
  of Stacks' effaceability — an epimorphism `π : P ⟶ X` with `Hₙ₊₁(π) = 0`.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal`: every `t : G₀ ⟶ H₀` extends
  uniquely to a morphism of δ-functors `G ⟶ H`.

## Main results

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_coeffaceable`: the dual of
  Stacks 010T — a coeffaceable homological δ-functor is universal.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_isZero_projective`: its
  standard source — if `A` has enough projectives and `Hₙ` vanishes on projectives for
  `n > 0`, then `H` is universal. This is the form the computation of `Hₙ(C, -)` uses.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.isoOfIso`: the dual of Stacks
  010U — two universal homological δ-functors with isomorphic degree-zero parts are
  isomorphic, by the unique isomorphism extending the given one.

## Implementation notes

**Two `Preadditive A` instances must never be in scope at once.** The statements that invoke
the cohomological theory are in a section whose source hypothesis is `[Abelian A]` *alone*,
with no `[Preadditive A]` beside it. With both in scope, `Preadditive Aᵒᵖ` has two
non-interchangeable spellings — `instPreadditiveOpposite` built on the `Preadditive A`
variable, and `Abelian.toPreadditive` of `Abelian Aᵒᵖ` built on the `Abelian A` variable — so
`H.op` is a `DeltaFunctor` of a different type from the one `DeltaFunctor.Effacement` is
indexed by, and the mismatch is a hard application type error, not a transparency wall. Under
`[Abelian A]` alone the two spellings share their underlying instance and everything
elaborates.

**Term mode for the `op` fields.** Each equational field of `op` is proved by
`congrArg Quiver.Hom.op` of the corresponding field of `H`, not by `rw` on a restatement: the
restatement elaborates `Bᵒᵖ`'s quiver through a different instance path, so `rw` reports "did
not find an occurrence" on a pattern that prints identically.

No `@[stacks]` attribute is placed here. Stacks' δ-functors are cohomological throughout, and
010T/010U are already carried, in full, by
`CategoryTheory.DeltaFunctor.isUniversal_of_effaceable` and
`CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso`. The statements below are the duals, which
the source does not state; tagging them would assert a second covering set for a tag that is
already covered.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public section

universe v v' u u'

namespace Stacks.CategoryHomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

namespace HomologicalDeltaFunctor

section Preadditive

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B]

/-- A morphism of homological δ-functors `H ⟶ G`: a family of natural transformations
`tₙ : Hₙ ⟶ Gₙ` commuting with the connecting morphisms of every short exact sequence. This is
the homological form of Stacks 010R. -/
@[ext]
structure Hom (H G : HomologicalDeltaFunctor A B) where
  /-- The components `tₙ : Hₙ ⟶ Gₙ`. -/
  app : ∀ n : ℕ, H.functor n ⟶ G.functor n
  /-- Compatibility with the connecting morphisms: `δ_H ≫ tₙ(X₁) = tₙ₊₁(X₃) ≫ δ_G`. -/
  comm : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    H.δ hS n ≫ (app n).app S.X₁ = (app (n + 1)).app S.X₃ ≫ G.δ hS n := by cat_disch

/-- Homological δ-functors from `A` to `B` form a category. -/
instance category : Category (HomologicalDeltaFunctor A B) where
  Hom := Hom
  id H := { app := fun _ ↦ 𝟙 _ }
  comp η γ :=
    { app := fun n ↦ η.app n ≫ γ.app n
      comm := fun hS n ↦ by
        rw [NatTrans.comp_app, NatTrans.comp_app, ← assoc, η.comm hS n, assoc, γ.comm hS n,
          assoc] }

@[simp]
lemma id_app (H : HomologicalDeltaFunctor A B) (n : ℕ) :
    Hom.app (𝟙 H) n = 𝟙 (H.functor n) :=
  rfl

@[simp]
lemma comp_app {H G K : HomologicalDeltaFunctor A B} (η : H ⟶ G) (γ : G ⟶ K) (n : ℕ) :
    (η ≫ γ).app n = η.app n ≫ γ.app n :=
  rfl

variable {H G : HomologicalDeltaFunctor A B}

/-- Two morphisms of homological δ-functors agree if all their components do. -/
@[ext]
lemma hom_ext {η γ : H ⟶ G} (h : ∀ n, η.app n = γ.app n) : η = γ :=
  Hom.ext (funext h)

/-- **A homological δ-functor, read as a cohomological δ-functor on the opposite
categories.** Opposing both the source and the target reverses the degree direction of the
connecting morphism, so the same data satisfies Stacks 010Q: the degree-`n` functor is
`(Hₙ)ᵒᵖ` and the connecting morphism of `S : ShortComplex Aᵒᵖ` is `Quiver.Hom.op` of the
connecting morphism of `S.unop`. -/
noncomputable def op (H : HomologicalDeltaFunctor A B) :
    CategoryTheory.DeltaFunctor Aᵒᵖ Bᵒᵖ where
  functor n := (H.functor n).op
  additive n := have := H.additive n; inferInstance
  δ := fun {S} hS n ↦ (H.δ hS.unop n).op
  map_g_δ := fun {S} hS n ↦
    (congrArg Quiver.Hom.op (H.δ_map_f hS.unop n)).trans (op_zero _ _)
  δ_map_f := fun {S} hS n ↦
    (congrArg Quiver.Hom.op (H.map_g_δ hS.unop n)).trans (op_zero _ _)
  mono_map_f := fun {S} hS ↦ by
    have := H.epi_map_g hS.unop
    exact inferInstanceAs (Mono ((H.functor 0).map S.unop.g).op)
  exact_map := fun {S} hS n ↦ (H.exact_map hS.unop n).op
  exact_δ₁ := fun {S} hS n ↦ (H.exact_δ₂ hS.unop n).op
  exact_δ₂ := fun {S} hS n ↦ (H.exact_δ₁ hS.unop n).op
  δ_naturality := fun {S T} hS hT φ n ↦
    congrArg Quiver.Hom.op
      (H.δ_naturality hT.unop hS.unop (ShortComplex.unopMap φ) n).symm

@[simp]
lemma op_functor (H : HomologicalDeltaFunctor A B) (n : ℕ) :
    H.op.functor n = (H.functor n).op :=
  rfl

@[simp]
lemma op_δ (H : HomologicalDeltaFunctor A B) {S : ShortComplex Aᵒᵖ} (hS : S.ShortExact)
    (n : ℕ) : H.op.δ hS n = (H.δ hS.unop n).op :=
  rfl

/-- The opposite of a morphism of homological δ-functors. `NatTrans.op` is contravariant, so
`η : H ⟶ G` becomes a *cohomological* morphism `G.op ⟶ H.op`. -/
noncomputable def Hom.op (η : H ⟶ G) : G.op ⟶ H.op where
  app n := NatTrans.op (η.app n)
  comm := fun {_S} hS n ↦ congrArg Quiver.Hom.op (η.comm hS.unop n)

@[simp]
lemma Hom.op_app (η : H ⟶ G) (n : ℕ) : (Hom.op η).app n = NatTrans.op (η.app n) :=
  rfl

/-- The inverse of `HomologicalDeltaFunctor.Hom.op`: a cohomological morphism `H.op ⟶ G.op`
is a homological morphism `G ⟶ H`. -/
noncomputable def Hom.ofOp (θ : H.op ⟶ G.op) : G ⟶ H where
  app n := NatTrans.removeOp (θ.app n)
  comm := fun {_S} hS n ↦ Quiver.Hom.op_inj (θ.comm hS.op n)

@[simp]
lemma Hom.ofOp_app (θ : H.op ⟶ G.op) (n : ℕ) :
    (Hom.ofOp θ).app n = NatTrans.removeOp (θ.app n) :=
  rfl

@[simp]
lemma Hom.ofOp_op (η : H ⟶ G) : Hom.ofOp (Hom.op η) = η :=
  hom_ext fun _ ↦ rfl

@[simp]
lemma Hom.op_ofOp (θ : H.op ⟶ G.op) : Hom.op (Hom.ofOp θ) = θ :=
  CategoryTheory.DeltaFunctor.hom_ext fun _ ↦ rfl

/-- A *coeffacement* of `X` in degree `n + 1` for the homological δ-functor `H`: an
epimorphism `π : P ⟶ X` with `Hₙ₊₁(π) = 0`. This is the dual of
`CategoryTheory.DeltaFunctor.Effacement`. -/
structure Coeffacement (H : HomologicalDeltaFunctor A B) (X : A) (n : ℕ) where
  /-- The source of the coeffacing epimorphism. -/
  P : A
  /-- The coeffacing epimorphism. -/
  π : P ⟶ X
  [epi : Epi π]
  /-- `Hₙ₊₁` kills the coeffacing epimorphism. -/
  map_π : (H.functor (n + 1)).map π = 0

namespace Coeffacement

attribute [instance] epi

attribute [simp] map_π

end Coeffacement

/-- The dual of Stacks' hypothesis in 010T: every object has a coeffacement in every positive
degree. -/
class Coeffaceable (H : HomologicalDeltaFunctor A B) : Prop where
  /-- Every object has a coeffacement in every positive degree. -/
  nonempty (X : A) (n : ℕ) : Nonempty (H.Coeffacement X n)

/-- The dual of Stacks 010S: a homological δ-functor `H` is *universal* if every natural
transformation `t : G₀ ⟶ H₀` extends uniquely to a morphism of δ-functors `G ⟶ H`. Note the
direction: a universal homological δ-functor is terminal among those with the given
degree-zero part, as left derived functors are. -/
class IsUniversal (H : HomologicalDeltaFunctor A B) : Prop where
  /-- Existence and uniqueness of the extension of `t : G₀ ⟶ H₀`. -/
  existsUnique (G : HomologicalDeltaFunctor A B) (t : G.functor 0 ⟶ H.functor 0) :
    ∃! η : G ⟶ H, η.app 0 = t

/-- If the cohomological δ-functor `H.op` is universal in the sense of Stacks 010S, then `H`
is universal as a homological δ-functor. The two quantifiers match because `Hom.op` and
`Hom.ofOp` are mutually inverse bijections between `G ⟶ H` and `H.op ⟶ G.op`. -/
theorem isUniversal_of_isUniversal_op (H : HomologicalDeltaFunctor A B)
    [H.op.IsUniversal] : H.IsUniversal where
  existsUnique G t := by
    obtain ⟨θ, hθ, huniq⟩ :=
      CategoryTheory.DeltaFunctor.IsUniversal.existsUnique (F := H.op) G.op (NatTrans.op t)
    refine ⟨Hom.ofOp θ, ?_, fun γ hγ ↦ ?_⟩
    · change (Hom.ofOp θ).app 0 = t
      rw [Hom.ofOp_app, hθ]
      exact NatTrans.ext rfl
    · have h : Hom.op γ = θ :=
        huniq _ (show (Hom.op γ).app 0 = NatTrans.op t by rw [Hom.op_app, hγ])
      rw [← Hom.ofOp_op γ, h]

namespace IsUniversal

variable [H.IsUniversal]

/-- The extension of `t : G₀ ⟶ H₀` to a morphism of δ-functors into a universal `H`. -/
noncomputable def lift (t : G.functor 0 ⟶ H.functor 0) : G ⟶ H :=
  (IsUniversal.existsUnique G t).choose

@[simp]
lemma lift_app_zero (t : G.functor 0 ⟶ H.functor 0) : (lift (H := H) t).app 0 = t :=
  (IsUniversal.existsUnique G t).choose_spec.1

/-- Morphisms into a universal homological δ-functor are determined by their degree-zero
component. -/
lemma hom_ext_zero {η γ : G ⟶ H} (h : η.app 0 = γ.app 0) : η = γ := by
  obtain ⟨_, _, hu⟩ := IsUniversal.existsUnique (H := H) G (η.app 0)
  exact (hu η rfl).trans (hu γ h.symm).symm

lemma eq_lift (η : G ⟶ H) : η = lift (H := H) (η.app 0) :=
  hom_ext_zero (by simp)

/-- **The dual of Stacks 010U, uniqueness.** An isomorphism into a universal homological
δ-functor is determined by its degree-zero component. -/
lemma iso_ext {α β : G ≅ H} (h : α.hom.app 0 = β.hom.app 0) : α = β :=
  Iso.ext (hom_ext_zero h)

variable [G.IsUniversal]

/-- **The dual of Stacks 010U.** Two universal homological δ-functors with isomorphic
degree-zero parts are isomorphic as δ-functors, by the isomorphism extending the given
one. -/
noncomputable def isoOfIso (e : H.functor 0 ≅ G.functor 0) : H ≅ G where
  hom := lift (H := G) e.hom
  inv := lift (H := H) e.inv
  hom_inv_id := hom_ext_zero (H := H) (by simp)
  inv_hom_id := hom_ext_zero (H := G) (by simp)

@[simp]
lemma isoOfIso_hom_app_zero (e : H.functor 0 ≅ G.functor 0) :
    (isoOfIso e).hom.app 0 = e.hom :=
  lift_app_zero e.hom

@[simp]
lemma isoOfIso_inv_app_zero (e : H.functor 0 ≅ G.functor 0) :
    (isoOfIso e).inv.app 0 = e.inv :=
  lift_app_zero e.inv

end IsUniversal

end Preadditive

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] (H : HomologicalDeltaFunctor A B)

/-- A coeffacement of `X` for `H` is an effacement of `Opposite.op X` for the cohomological
δ-functor `H.op`: the epimorphism `π` becomes a monomorphism `π.op`, and `Hₙ₊₁(π) = 0`
becomes `(Hₙ₊₁)ᵒᵖ(π.op) = 0`. -/
noncomputable def Coeffacement.toEffacement {X : A} {n : ℕ} (e : H.Coeffacement X n) :
    H.op.Effacement (Opposite.op X) n where
  I := Opposite.op e.P
  ι := e.π.op
  mono := inferInstance
  map_ι := (congrArg Quiver.Hom.op e.map_π).trans (op_zero _ _)

/-- A coeffaceable homological δ-functor is an effaceable cohomological δ-functor on the
opposite categories. -/
theorem effaceable_op [H.Coeffaceable] : H.op.Effaceable where
  nonempty X n := ⟨Coeffacement.toEffacement H (Coeffaceable.nonempty (H := H) X.unop n).some⟩

/-- **The dual of Stacks 010T: a coeffaceable homological δ-functor is universal.** The proof
is Grothendieck's Tohoku argument for `H.op`, i.e.
`CategoryTheory.DeltaFunctor.isUniversal_of_effaceable`. -/
theorem isUniversal_of_coeffaceable [HasZeroObject B] [Balanced B] [H.Coeffaceable] :
    H.IsUniversal :=
  have := H.effaceable_op
  have := CategoryTheory.DeltaFunctor.isUniversal_of_effaceable H.op
  H.isUniversal_of_isUniversal_op

/-- If `A` has enough projectives and `Hₙ` vanishes on projectives for `n > 0`, then `H` is
coeffaceable: cover `X` by the projective `Projective.over X`. -/
theorem Coeffaceable.of_isZero_projective [EnoughProjectives A]
    (h : ∀ (n : ℕ) (P : A) [Projective P], IsZero ((H.functor (n + 1)).obj P)) :
    H.Coeffaceable where
  nonempty X n :=
    ⟨{ P := Projective.over X
       π := Projective.π X
       map_π := (h n _).eq_of_src _ _ }⟩

/-- **The dual of Stacks 010T for the standard source of coeffaceability.** If `A` has enough
projectives and `Hₙ` vanishes on projectives for `n > 0`, then `H` is universal. This is the
form used for left derived functors. -/
theorem isUniversal_of_isZero_projective [HasZeroObject B] [Balanced B] [EnoughProjectives A]
    (h : ∀ (n : ℕ) (P : A) [Projective P], IsZero ((H.functor (n + 1)).obj P)) :
    H.IsUniversal :=
  have := Coeffaceable.of_isZero_projective H h
  H.isUniversal_of_coeffaceable

end Abelian

end HomologicalDeltaFunctor

end Stacks.CategoryHomology

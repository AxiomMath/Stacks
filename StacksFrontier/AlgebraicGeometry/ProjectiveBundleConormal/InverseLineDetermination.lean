module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.InvIsoPin

/-!
# The inverse-line comparison of Tag 0B3V determines the comparison that classifies the section

`Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso E Q e` identifies `σ^*𝒪_{𝐏(ℰ)}(-1)`
with `(Q.L)^{⊗ -1}`, given a comparison `e : σ^*𝒪_{𝐏(ℰ)}(1) ≅ Q.L`. This file records that it
*determines* `e`: distinct comparisons of the positive lines give distinct comparisons of the
inverse lines.

## Main results

* `Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso_injective`.
* `Stacks.TensorPowers.TensorInverse.pin_invIso_ofIso`, `pin_comp` and `pin_unique`, with
  `TensorInverse.ofIso_snake`: the characterisation of a comparison of inverse objects by what it
  does to the two trivialisations — see "The pin calculus" below.

## What this settles

It settles that the hypothesis `hinv` of `Stacks.ProjectiveBundleConormal.sourceCoherence` — the
inverse-line factor of the source coherence, and the last open piece of Tag 0B3V's base-change
clause for the conormal isomorphism — **is not provable from the hypotheses that statement
carries.** Its two sides are

`g^*(inverseTwistBaseChangeIso E Q e) ≫ Stacks.Divisors.inverseQuotientBaseChange g E E' Q Q' hL`

and

`schemePullbackCompIso comm ≫ σ'^*(inverseTwistBundleBaseChangeIso g E E' hE) ≫
  inverseTwistBaseChangeIso E' Q' e'`,

and `e'` occurs only in the second. By the result below the second side therefore takes distinct
values at distinct `e'`, while the first takes none at all; so no proof can exist while `e` and
`e'` are independent parameters, which in `sourceCoherence` they are. The two comparisons are
genuinely distinct for distinct `e'`: `e'` may be replaced by `e' ≪≫ u` for any automorphism `u`
of `Q'.L`, and a quotient line admits automorphisms other than the identity.

The relation that is missing is the one `Stacks.ProjectiveBundleConormal.conormalCanonicalMap`
already carries, as its hypothesis `hqe`: that `e` is the comparison through which `σ^*` of the
tautological map becomes `q`. With `hqe` at `ℰ` and `hqe'` at `ℰ'`, together with the
identification `hq` of the quotients and the commuting square `comm`, the comparisons `e` and
`e'` are no longer independent, and the compatibility of the *positive* lines that `hinv` needs
is **proved**: `Stacks.ProjectiveBundleConormal.positiveLine_coherence`. Both hypotheses are
available at every assembly point of the clause —
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_source` and
`conormalCanonicalMap_baseChange_of_twistedSourceBaseChange` take them — so the clause is not
harmed by the dependence.

## The pin calculus

What the positive-line compatibility is still owed is the passage from it to `hinv`, and this
file carries that passage's general half, in a bare monoidal category and with no geometry. A
morphism `u : a⁻¹ ⟶ b⁻¹` between the inverse objects of `a : TensorInverse L₁` and
`b : TensorInverse L₂` is *pinned along* `ε : L₁ ≅ L₂` when

`u ▷ L₁ ≫ b⁻¹ ◁ ε ≫ b.mulIso' = a.mulIso'`.

* `Stacks.TensorPowers.TensorInverse.pin_invIso_ofIso`: the canonical comparison
  `Stacks.TensorPowers.TensorInverse.invIso` taken at
  `Stacks.TensorPowers.TensorInverse.ofIso` is pinned along the isomorphism it is taken at. This
  is `invIso_whiskerRight_mulIso'` at the transported structure, whose snake hypothesis is
  `TensorInverse.ofIso_snake`.
* `Stacks.TensorPowers.TensorInverse.pin_comp`: being pinned composes, the two isomorphisms
  composing with it. One `CategoryTheory.MonoidalCategory.whisker_exchange`.
* `Stacks.TensorPowers.TensorInverse.pin_unique`: being pinned determines the morphism.

Both sides of `hinv` are composites of comparisons of inverse objects, so `pin_comp` pins each
along the composite of the corresponding positive-line isomorphisms — which are the two sides of
`positiveLine_coherence` — and `pin_unique` then yields `hinv`.

**The assembly wants the mirror of this calculus, not this one.** The pin
above is taken against the right trivialisation `mulIso'`, and the geometric inputs of `hinv`
arrive pinned against the left one — the twist factor's pin
`Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp` reads
`(ε ⊗ₘ u) ≫ b.mulIso = a.mulIso`, its two pairings taking `𝒪(1)` with `𝒪(-1)` in that order, and
converting it to the form above costs the snake of both structures. The left form is cheaper on
the two general facts as well: its uniqueness is already available as
`Stacks.Monoidal.eq_of_tensorHom_comp_eq`, and composing left pins is one
`CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom` against one `whisker_exchange` here.
The left calculus is
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.InvIsoLeftPin`. What is still missing
of the geometry is in the
"What is still owed" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceCoherence`.

**No `@[stacks 0B3V]` attribute is attached, and none is earned**: this is a negative result about
one hypothesis, not any part of the tag's assertion.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe v u

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The snake relating the two trivialisations transports along a transported inverse.** If the
two ways of cancelling the middle factor of `b⁻¹ ⊗ L₂ ⊗ b⁻¹` agree, so do the two ways of
cancelling the middle factor of `b⁻¹ ⊗ L₁ ⊗ b⁻¹` for the structure
`Stacks.TensorPowers.TensorInverse.ofIso` transports `b` to along `ε : L₁ ≅ L₂`.

Both trivialisations of the transport are the given ones with `ε` whiskered into the factor that
is not `b⁻¹`, so the only step is the naturality of the associator in its middle argument. -/
theorem TensorInverse.ofIso_snake {L₁ L₂ : C} (b : TensorInverse L₂) (ε : L₁ ≅ L₂)
    (hs : (α_ b.inv L₂ b.inv).hom ≫ b.inv ◁ b.mulIso.hom ≫ (ρ_ b.inv).hom =
      b.mulIso'.hom ▷ b.inv ≫ (λ_ b.inv).hom) :
    (α_ (TensorInverse.ofIso ε b).inv L₁ (TensorInverse.ofIso ε b).inv).hom ≫
        (TensorInverse.ofIso ε b).inv ◁ (TensorInverse.ofIso ε b).mulIso.hom ≫
          (ρ_ (TensorInverse.ofIso ε b).inv).hom =
      (TensorInverse.ofIso ε b).mulIso'.hom ▷ (TensorInverse.ofIso ε b).inv ≫
        (λ_ (TensorInverse.ofIso ε b).inv).hom := by
  change (α_ b.inv L₁ b.inv).hom ≫ b.inv ◁ (ε.hom ▷ b.inv ≫ b.mulIso.hom) ≫ (ρ_ b.inv).hom =
    (b.inv ◁ ε.hom ≫ b.mulIso'.hom) ▷ b.inv ≫ (λ_ b.inv).hom
  rw [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (α_ b.inv L₁ b.inv).hom (b.inv ◁ ε.hom ▷ b.inv),
    ← MonoidalCategory.associator_naturality_middle]
  simp only [Category.assoc]
  rw [hs]

/-- **A comparison of the inverses of two isomorphic objects is pinned by the trivialisations.**
For `a : TensorInverse L₁`, `b : TensorInverse L₂` and `ε : L₁ ≅ L₂`, a morphism
`u : a⁻¹ ⟶ b⁻¹` is *pinned along `ε`* when

`u ▷ L₁ ≫ b⁻¹ ◁ ε ≫ b.mulIso' = a.mulIso'`,

that is, when whiskering by `L₁` and contracting through `ε` carries the right trivialisation of
`b` to that of `a`. This is the single-tensor form of
`Stacks.TensorPowers.TensorInverse.invIso_whiskerRight_mulIso'` read at the transported structure
`Stacks.TensorPowers.TensorInverse.ofIso`, whose right trivialisation is exactly `ε` whiskered
into `b`'s: the canonical comparison is pinned along the isomorphism it is taken at. -/
theorem TensorInverse.pin_invIso_ofIso {L₁ L₂ : C} (a : TensorInverse L₁) (b : TensorInverse L₂)
    (ε : L₁ ≅ L₂)
    (hs : (α_ b.inv L₂ b.inv).hom ≫ b.inv ◁ b.mulIso.hom ≫ (ρ_ b.inv).hom =
      b.mulIso'.hom ▷ b.inv ≫ (λ_ b.inv).hom) :
    (TensorInverse.invIso a (TensorInverse.ofIso ε b)).hom ▷ L₁ ≫
        b.inv ◁ ε.hom ≫ b.mulIso'.hom = a.mulIso'.hom :=
  TensorInverse.invIso_whiskerRight_mulIso' a (TensorInverse.ofIso ε b)
    (TensorInverse.ofIso_snake b ε hs)

/-- **Being pinned composes**, the two isomorphisms of the objects being inverted composing with
it. The one step is `CategoryTheory.MonoidalCategory.whisker_exchange`, which moves the second
comparison past the first contraction; nothing about the inverses themselves is used. -/
theorem TensorInverse.pin_comp {L₁ L₂ L₃ : C} (a : TensorInverse L₁) (b : TensorInverse L₂)
    (c : TensorInverse L₃) (ε : L₁ ≅ L₂) (δ : L₂ ≅ L₃) {u : a.inv ⟶ b.inv} {v : b.inv ⟶ c.inv}
    (hu : u ▷ L₁ ≫ b.inv ◁ ε.hom ≫ b.mulIso'.hom = a.mulIso'.hom)
    (hv : v ▷ L₂ ≫ c.inv ◁ δ.hom ≫ c.mulIso'.hom = b.mulIso'.hom) :
    (u ≫ v) ▷ L₁ ≫ c.inv ◁ (ε ≪≫ δ).hom ≫ c.mulIso'.hom = a.mulIso'.hom := by
  rw [MonoidalCategory.comp_whiskerRight, Iso.trans_hom, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Category.assoc, ← Category.assoc (v ▷ L₁),
    ← MonoidalCategory.whisker_exchange v ε.hom]
  simp only [Category.assoc]
  rw [hv, hu]

/-- **Being pinned determines the morphism.** Two morphisms `a⁻¹ ⟶ b⁻¹` pinned along the same
isomorphism are equal: the contraction is an isomorphism, so it cancels, and whiskering on the
right by `L₁` is faithful because `a.mulIso` exhibits `a⁻¹` as a tensor inverse of `L₁` —
`Stacks.TensorPowers.whiskerRight_injective_of_mulIso`.

This is the uniqueness that makes the pin usable as a *characterisation*: a composite of
comparisons that is pinned along a given isomorphism is the canonical comparison taken at it, and
two such composites pinned along isomorphisms that are *equal* agree. -/
theorem TensorInverse.pin_unique {L₁ L₂ : C} (a : TensorInverse L₁) (b : TensorInverse L₂)
    (ε : L₁ ≅ L₂) {u v : a.inv ⟶ b.inv}
    (hu : u ▷ L₁ ≫ b.inv ◁ ε.hom ≫ b.mulIso'.hom = a.mulIso'.hom)
    (hv : v ▷ L₁ ≫ b.inv ◁ ε.hom ≫ b.mulIso'.hom = a.mulIso'.hom) : u = v := by
  have : IsIso (b.inv ◁ ε.hom ≫ b.mulIso'.hom) := by
    have : IsIso (b.inv ◁ ε.hom) := (MonoidalCategory.whiskerLeftIso b.inv ε).isIso_hom
    infer_instance
  exact whiskerRight_injective_of_mulIso a.mulIso
    ((cancel_mono (b.inv ◁ ε.hom ≫ b.mulIso'.hom)).mp (hu.trans hv.symm))

end Stacks.TensorPowers

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E) {σ : X ⟶ (bundle E).scheme}

/-- **Tag 0B3V's identification of `σ^*𝒪(-1)` with `(Q.L)^{⊗ -1}` determines the comparison of the
positive lines it is taken at.** If `e` and `e₂` induce the same comparison of the inverse lines,
they are equal.

`Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso` is
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` at `e.symm`, so this is
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso_injective`, which is in turn the
observation that the comparison of two tensor inverses determines the trivialisation of its target
— `Stacks.TensorPowers.TensorInverse.mulIso_eq_of_invIso_eq`. -/
theorem inverseTwistBaseChangeIso_injective
    (e e₂ : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
    (he : inverseTwistBaseChangeIso E Q e = inverseTwistBaseChangeIso E Q e₂) :
    e = e₂ := by
  have h := Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso_injective
    σ (tautologicalTwist E (symPieces E)) Q.L e.symm e₂.symm he
  simpa using congrArg Iso.symm h

end Stacks.ProjectiveBundleConormal

end

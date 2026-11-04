module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincare

/-!
# The crystalline Poincaré lemma for a finite family of divided power variables

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, and let
`M` be a `B`-module with an integrable connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`.  Tag 07LD asserts
that for a divided power polynomial ring `P = B⟨x_i⟩` over `B`, with divided power ideal
`J = IP + B⟨x_i⟩₊`, the canonical map of de Rham complexes

`M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ}`

is a quasi-isomorphism.  `Crystalline.quasiIso_oneVariableDeRhamComparison` proves this for a
single variable, `P = B⟨z⟩`.  This module widens that to any finite number of variables, by
iterating the one-variable case along the tower

`B ⟶ B⟨x₁⟩ ⟶ B⟨x₁⟩⟨x₂⟩ ⟶ … ⟶ B⟨x₁⟩…⟨x_n⟩`,

whose `n`-th term is the divided power polynomial ring on `n` variables over `B`.

The tower is organised by `Crystalline.ConnectionStage`, which bundles everything the
one-variable lemma consumes: a divided power `A`-algebra, a module over it, and an integrable
connection.  `Crystalline.ConnectionStage.next` adjoins one divided power variable and base
changes the module and the connection along `B ⟶ B⟨z⟩`.  The point that makes the iteration go
through is `Crystalline.ConnectionStage.next_deRhamComplex`: the de Rham complex of the next
stage *is* — definitionally, not merely up to isomorphism — the target complex of the
one-variable comparison out of the current stage.  So the one-variable maps compose on the nose,
with no transport along an isomorphism of rings, and the composite is a quasi-isomorphism because
each factor is.

## Main definitions

* `Crystalline.oneVariableExtension` — `B⟨z⟩` packaged as a divided power ring, so that it can
  serve as the base of the next stage.
* `Crystalline.ConnectionStage` — one stage of the tower: a divided power `A`-algebra, a module
  over it, and an integrable connection.
* `Crystalline.ConnectionStage.next`, `Crystalline.ConnectionStage.iterate` — adjoining one
  divided power variable, and the `n`-fold iterate.
* `Crystalline.ConnectionStage.IsCanonicalComparison` — the two properties of equation 07PY, the
  value on pure wedges and the commutation with the differentials, which
  `Crystalline.existsUnique_baseChangeDeRhamMap` shows pin a degreewise family uniquely.
* `Crystalline.IsIteratedOneVariableComparison` — the predicate cutting out the composites of `n`
  successive canonical one-variable comparison maps.

## Main results

* `Crystalline.quasiIso_isIteratedOneVariableComparison` — an `n`-fold iterated canonical
  one-variable comparison is a quasi-isomorphism.
* `Crystalline.exists_isIteratedOneVariableComparison` — such a map exists for every `n` and
  every stage, so the statement above is not vacuous; its target is the de Rham complex of the
  `n`-th stage of the tower.
* `Crystalline.IsIteratedOneVariableComparison.unique` — there is only one such map, so "the"
  `n`-fold comparison is well defined.

## Relation to Tag 07LD

The statement here is for `B⟨x₁,…,x_n⟩` presented as the `n`-fold iterated one-variable
extension `B⟨x₁⟩…⟨x_n⟩`.  The first clause of [Stacks, Tag 07LD], for the divided power
polynomial ring `B⟨x_w : w ∈ W⟩` on an arbitrary, possibly infinite, family of variables, is
`Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincareModuleQuasiIso.lean`,
proved there directly rather than by iteration; the clause over the `p`-adic completions is
`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`.

One universe constraint is forced by the iteration and is worth stating plainly: a stage carries
its module in `Type (max u v)` rather than in an arbitrary `Type w`, because base changing along
`B ⟶ B⟨z⟩` takes a module in `Type w` to one in `Type (max u w)`, and the tower has to land in
the universe it started in.  So the modules covered here are those whose universe is at least
that of the base ring.  The one-variable statement
`Crystalline.quasiIso_oneVariableDeRhamComparison`, which is applied only once per step and so
need not be iterated, has no such constraint.

## References

* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07PY](https://stacks.math.columbia.edu/tag/07PY)
* [Stacks Project, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
-/

@[expose] public section

open DividedPowers
open CategoryTheory
open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u v

namespace Crystalline

/-! ### Adjoining one divided power variable to the base -/

/-- The divided power polynomial ring `B⟨z⟩` on one variable, packaged as a divided power ring
with its divided power ideal `IB⟨z⟩ + B⟨z⟩₊`.  Packaging it this way is what lets it serve as
the base of a further one-variable extension, and hence lets the one-variable Poincaré lemma be
iterated. -/
public noncomputable abbrev oneVariableExtension (B : DividedPowerRing.{u}) :
    DividedPowerRing.{u} :=
  .of (oneVariableDividedPowerPolynomial B) (dividedPowerPolynomialIdeal B.ideal Unit)
    (oneVariableDividedPowers B)

/-- `B⟨z⟩` is an `A`-algebra whenever `B` is. -/
public noncomputable instance oneVariableExtensionAlgebra (A : Type u) [CommRing A]
    (B : DividedPowerRing.{u}) [Algebra A B] : Algebra A (oneVariableExtension B) :=
  inferInstanceAs (Algebra A (oneVariableDividedPowerPolynomial B))

/-! ### Stages of the tower -/

/-- One stage of an iterated divided power polynomial extension: a divided power ring which is
an `A`-algebra, a module over it, and an integrable connection on that module.  This is exactly
the data that the one-variable Poincaré lemma consumes, bundled so that adjoining a variable
takes a stage to a stage. -/
public structure ConnectionStage (A : Type u) [CommRing A] where
  /-- The divided power ring of the stage. -/
  ring : DividedPowerRing.{u}
  /-- Its `A`-algebra structure. -/
  [alg : Algebra A ring]
  /-- The module of the stage. -/
  carrier : Type (max u v)
  /-- Its additive structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its module structure over the ring of the stage. -/
  [mod : Module ring carrier]
  /-- The connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`. -/
  nabla : Connection A (ring : Type u) (oneVariableBaseProjection A ring) carrier
  /-- Integrability of the connection. -/
  hint : Connection.IsIntegrable (oneVariableBaseSource A ring)
    (oneVariableBaseProjection A ring) (Submodule.mkQ_surjective _)
    (oneVariableBaseGenerationHypothesis A ring) nabla

namespace ConnectionStage

attribute [instance] alg addCommGroup mod

variable {A : Type u} [CommRing A]

/-- The de Rham complex `M ⊗_B Ω^*_{B/A,δ}` of the stage. -/
public noncomputable abbrev deRhamComplex (S : ConnectionStage.{u, v} A) :
    CochainComplex (ModuleCat.{max u v} A) ℕ :=
  oneVariableSourceDeRhamComplex A S.ring S.nabla S.hint

/-- The next stage of the tower: adjoin one divided power variable to the base, and base change
the module and the connection along `B ⟶ B⟨z⟩`. -/
public noncomputable def next (S : ConnectionStage.{u, v} A) : ConnectionStage.{u, v} A where
  ring := oneVariableExtension S.ring
  alg := inferInstanceAs (Algebra A (oneVariableDividedPowerPolynomial S.ring))
  carrier := oneVariableDividedPowerPolynomial S.ring ⊗[(S.ring : Type u)] S.carrier
  addCommGroup := inferInstanceAs (AddCommGroup
    (oneVariableDividedPowerPolynomial S.ring ⊗[(S.ring : Type u)] S.carrier))
  mod := inferInstanceAs (Module (oneVariableDividedPowerPolynomial S.ring)
    (oneVariableDividedPowerPolynomial S.ring ⊗[(S.ring : Type u)] S.carrier))
  nabla := oneVariableBaseChangeConnection A S.ring S.nabla
  hint := oneVariableBaseChangeConnection_isIntegrable A S.ring S.nabla S.hint

/-- The de Rham complex of the next stage is the target complex of the one-variable comparison
out of the current stage.  This holds definitionally, which is what lets the one-variable maps
be composed without transporting anything along an isomorphism. -/
public theorem next_deRhamComplex (S : ConnectionStage.{u, v} A) :
    S.next.deRhamComplex = oneVariableTargetDeRhamComplex A S.ring S.nabla S.hint :=
  rfl

/-- The `n`-th stage of the tower over `S`, obtained by adjoining `n` divided power variables
one at a time.  Its ring is the divided power polynomial ring on `n` variables over the ring of
`S`, presented as an `n`-fold iterated one-variable extension. -/
public noncomputable def iterate : ℕ → ConnectionStage.{u, v} A → ConnectionStage.{u, v} A
  | 0, S => S
  | n + 1, S => iterate n S.next

/-- A degreewise `A`-linear family from the de Rham complex of a stage to that of the next. -/
public noncomputable abbrev Comparison (S : ConnectionStage.{u, v} A) : Type (max u v) :=
  ∀ p : ℕ, oneVariableSourceTerm A S.ring S.carrier p →ₗ[A]
    oneVariableTargetTerm A S.ring S.carrier p

/-- The two properties of equation 07PY which pin a degreewise family down to the canonical
comparison map: its value on a pure wedge of one-forms, and its commutation with the two
extended connections.  `Crystalline.existsUnique_baseChangeDeRhamMap` shows that they are
satisfied by exactly one family, so requiring them is not a weakening — it names the canonical
map. -/
public def IsCanonicalComparison (S : ConnectionStage.{u, v} A) (c : S.Comparison) : Prop :=
  (∀ (p : ℕ) (m : S.carrier)
      (omega : Fin p → dividedPowerDifferentials (A := A) S.ring.dividedPowers),
    c p (m ⊗ₜ[(S.ring : Type u)] exteriorPower.ιMulti (S.ring : Type u) p omega) =
      ((1 : oneVariableDividedPowerPolynomial S.ring) ⊗ₜ[(S.ring : Type u)] m) ⊗ₜ[
        oneVariableDividedPowerPolynomial S.ring]
        exteriorPower.ιMulti (oneVariableDividedPowerPolynomial S.ring) p
          (dividedPowerPolynomialOneFormComparison A S.ring ∘ omega)) ∧
  (∀ (p : ℕ) (x : oneVariableSourceTerm A S.ring S.carrier p),
    c (p + 1) ((extendedConnection (oneVariableBaseSource A S.ring)
          (oneVariableBaseProjection A S.ring) (Submodule.mkQ_surjective _)
          (oneVariableBaseGenerationHypothesis A S.ring) S.nabla).toLinearMap p x) =
      (extendedConnection (oneVariablePolySource A S.ring) (oneVariablePolyProjection A S.ring)
        (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A S.ring)
        (oneVariableBaseChangeConnection A S.ring S.nabla)).toLinearMap p (c p x))

/-- Exactly one degreewise family is canonical. -/
public theorem existsUnique_isCanonicalComparison (S : ConnectionStage.{u, v} A) :
    ∃! c : S.Comparison, S.IsCanonicalComparison c :=
  existsUnique_baseChangeDeRhamMap (S := oneVariableBaseSource A S.ring)
    (S' := oneVariablePolySource A S.ring) (pi := oneVariableBaseProjection A S.ring)
    (pi' := oneVariablePolyProjection A S.ring) (hpi := Submodule.mkQ_surjective _)
    (hgen := oneVariableBaseGenerationHypothesis A S.ring)
    (hpi' := Submodule.mkQ_surjective _)
    (hgen' := oneVariablePolyGenerationHypothesis A S.ring)
    (psi := dividedPowerPolynomialOneFormComparison A S.ring)
    (hpsi := oneVariableOneFormComparison_compatible A S.ring) (nabla := S.nabla) S.hint

/-- The canonical one-variable comparison map out of a stage, as a map of de Rham complexes. -/
public noncomputable abbrev comparisonMap (S : ConnectionStage.{u, v} A) {c : S.Comparison}
    (hc : S.IsCanonicalComparison c) : S.deRhamComplex ⟶ S.next.deRhamComplex :=
  oneVariableDeRhamComparison A S.ring S.nabla S.hint c hc.2

end ConnectionStage

/-! ### Iterated comparison maps -/

/-- `IsIteratedOneVariableComparison n S X f` says that `f` is the composite of `n` successive
canonical one-variable comparison maps starting from the stage `S`, so that `X` is the de Rham
complex of the `n`-th stage of the tower over `S`.  For `n = 0` this is the identity, and for
`n = 1` it is the single comparison map of
`Crystalline.quasiIso_oneVariableDeRhamComparison`. -/
public inductive IsIteratedOneVariableComparison {A : Type u} [CommRing A] :
    (n : ℕ) → (S : ConnectionStage.{u, v} A) →
      (X : CochainComplex (ModuleCat.{max u v} A) ℕ) → (S.deRhamComplex ⟶ X) → Prop
  /-- No variables adjoined: the identity map. -/
  | id (S : ConnectionStage.{u, v} A) :
      IsIteratedOneVariableComparison 0 S S.deRhamComplex (CategoryStruct.id S.deRhamComplex)
  /-- Adjoin one more variable on the left of an `n`-fold iterated comparison. -/
  | step {n : ℕ} (S : ConnectionStage.{u, v} A) {c : S.Comparison}
      (hc : S.IsCanonicalComparison c) {X : CochainComplex (ModuleCat.{max u v} A) ℕ}
      (g : S.next.deRhamComplex ⟶ X) (hg : IsIteratedOneVariableComparison n S.next X g) :
      IsIteratedOneVariableComparison (n + 1) S X (S.comparisonMap hc ≫ g)

namespace IsIteratedOneVariableComparison

variable {A : Type u} [CommRing A]

/-- An `n`-fold iterated comparison map is unique: at each stage the canonical family is
unique, by `Crystalline.ConnectionStage.existsUnique_isCanonicalComparison`. -/
public theorem unique {n : ℕ} {S : ConnectionStage.{u, v} A}
    {X : CochainComplex (ModuleCat.{max u v} A) ℕ} {f f' : S.deRhamComplex ⟶ X}
    (h : IsIteratedOneVariableComparison n S X f)
    (h' : IsIteratedOneVariableComparison n S X f') : f = f' := by
  induction h with
  | id S => cases h'; rfl
  | step S hc g hg ih =>
      cases h' with
      | step S hc' g' hg' =>
          obtain rfl := (S.existsUnique_isCanonicalComparison).unique hc hc'
          exact congrArg (fun y => S.comparisonMap hc ≫ y) (ih hg')

end IsIteratedOneVariableComparison

/-- **The crystalline Poincaré lemma for a finite family of variables, as an iterated one-variable
extension.**  Let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `M` be a
`B`-module with an integrable connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`, and let
`P = B⟨x₁⟩…⟨x_n⟩` be the `n`-fold iterated one-variable divided power polynomial extension.  Then
the composite of the `n` canonical one-variable comparison maps
`M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ}` is a quasi-isomorphism.  By
`Crystalline.ConnectionStage.existsUnique_isCanonicalComparison` and
`Crystalline.IsIteratedOneVariableComparison.unique` there is exactly one such composite.  The
case `n = 1` is `Crystalline.quasiIso_oneVariableDeRhamComparison`, which supplies the inductive
step.

The first clause of [Stacks, Tag 07LD] itself, for `P = B⟨x_w : w ∈ W⟩` on an arbitrary family of
variables, is `Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison`. -/
public theorem quasiIso_isIteratedOneVariableComparison {A : Type u} [CommRing A] {n : ℕ}
    {S : ConnectionStage.{u, v} A} {X : CochainComplex (ModuleCat.{max u v} A) ℕ}
    {f : S.deRhamComplex ⟶ X} (h : IsIteratedOneVariableComparison n S X f) : QuasiIso f := by
  induction h with
  | id S => infer_instance
  | step S hc g hg ih =>
      have hone : QuasiIso (S.comparisonMap hc) :=
        quasiIso_oneVariableDeRhamComparison A S.ring S.nabla S.hint _ hc.1 hc.2
      exact quasiIso_comp _ _

/-- For every stage `S` and every `n` there is an `n`-fold iterated canonical one-variable
comparison map, with target the de Rham complex of the `n`-th stage of the tower over `S`.  So
`Crystalline.quasiIso_isIteratedOneVariableComparison` is not vacuous: it applies to a genuine
map `M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ}` for `P = B⟨x₁,…,x_n⟩`. -/
public theorem exists_isIteratedOneVariableComparison {A : Type u} [CommRing A] (n : ℕ)
    (S : ConnectionStage.{u, v} A) :
    ∃ f : S.deRhamComplex ⟶ (S.iterate n).deRhamComplex,
      IsIteratedOneVariableComparison n S (S.iterate n).deRhamComplex f := by
  induction n generalizing S with
  | zero => exact ⟨_, .id S⟩
  | succ n ih =>
      obtain ⟨g, hg⟩ := ih S.next
      obtain ⟨c, hc, -⟩ := S.existsUnique_isCanonicalComparison
      exact ⟨_, .step S hc g hg⟩

/-- The iterated one-variable Poincaré lemma, in existential form: the canonical map of de Rham
complexes from a stage to the `n`-th stage of the tower over it is a quasi-isomorphism. -/
public theorem exists_quasiIso_iteratedOneVariableComparison {A : Type u} [CommRing A] (n : ℕ)
    (S : ConnectionStage.{u, v} A) :
    ∃ f : S.deRhamComplex ⟶ (S.iterate n).deRhamComplex, QuasiIso f := by
  obtain ⟨f, hf⟩ := exists_isIteratedOneVariableComparison n S
  exact ⟨f, quasiIso_isIteratedOneVariableComparison hf⟩

end Crystalline

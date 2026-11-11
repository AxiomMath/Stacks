module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness properties of a morphism of topoi

Stacks tag 04D6 lists eleven properties of the pushforward `f_*` of a morphism of topoi
`f : Sh(C) → Sh(D)` and eight implications (a)–(h) among them.

## Main results

* `exactness_properties_bundled`: the part of the lemma that holds for an arbitrary adjunction
  `L ⊣ R`, namely (a) `(2) ⇒ (1)`, (b) `(3) ⇒ (1)`, the `(9) ⇒ (3)` direction of (d) and both
  directions of (h) `(2) ⇔ (7)`.

The complete lemma, for a morphism of topoi `f : Sh(C) → Sh(D)`, is
`MorphismOfTopoi.pushforward_exactness_implications` in
`StacksFrontier.CategoryTheory.Sites.Topos.PushforwardExactness`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

/-- A fully faithful right adjoint has an invertible counit. -/
private theorem isIso_counit_app_of_fullyFaithful
    (hRff : R.FullyFaithful) (X : D) : IsIso (h.counit.app X) :=
  have : R.Full := hRff.full
  have : R.Faithful := hRff.faithful
  inferInstance

/-- Part of Stacks 04D6, for an arbitrary adjunction `L ⊣ R` in the role of `f⁻¹ ⊣ f_*`: the
implications among properties (1) `R` faithful, (2) `R` fully faithful, (3) the counit
`L R X ⟶ X` epi for all `X`, (7) the counit an isomorphism for all `X`, and (9) `R` reflects
epimorphisms that need no topos structure. The five conjuncts are, in order,

* (a) `(2) ⇒ (1)`;
* (b) `(3) ⇒ (1)`;
* `(9) ⇒ (3)`, one direction of (d): `R` of the counit is split epi by the triangle identity;
* `(7) ⇒ (2)`, one direction of (h);
* `(2) ⇒ (7)`, the other direction of (h).

The complete lemma, for a morphism of topoi, is
`MorphismOfTopoi.pushforward_exactness_implications`. -/
@[sga "4 I 5.6" "iv) <=> v)", sga "4 I 6.4" "epic counit ⇒ ψ faithful"]
theorem exactness_properties_bundled :
    (R.FullyFaithful → R.Faithful) ∧
    ((∀ X, Epi (h.counit.app X)) → R.Faithful) ∧
    (R.ReflectsEpimorphisms → ∀ X, Epi (h.counit.app X)) ∧
    ((∀ X, IsIso (h.counit.app X)) → Nonempty R.FullyFaithful) ∧
    (R.FullyFaithful → ∀ X, IsIso (h.counit.app X)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a) FullyFaithful ⇒ Faithful
    intro hRff
    exact hRff.faithful
  · -- (b) Counit pointwise epi ⇒ R faithful
    intro hEpi
    have : ∀ X, Epi (h.counit.app X) := hEpi
    exact h.faithful_R_of_epi_counit_app
  · -- (d) R reflects epis ⇒ counit pointwise epi
    intro _ X
    -- `h.right_triangle_components X : h.unit.app (R.obj X) ≫ R.map (h.counit.app X) = 𝟙 _`
    -- shows `R.map (h.counit.app X)` is a split epimorphism, hence epi.
    have hsplit : IsSplitEpi (R.map (h.counit.app X)) :=
      ⟨⟨{ section_ := h.unit.app (R.obj X)
          id := h.right_triangle_components X }⟩⟩
    have : Epi (R.map (h.counit.app X)) := inferInstance
    exact R.epi_of_epi_map this
  · -- (h) counit pointwise iso ⇒ R fully faithful
    intro hIso
    have : IsIso h.counit := NatIso.isIso_of_isIso_app _
    exact ⟨h.fullyFaithfulROfIsIsoCounit⟩
  · -- (h) R fully faithful ⇒ counit pointwise iso
    exact isIso_counit_app_of_fullyFaithful h

/-- **Stacks 04D6 (h), forward direction.** If the right adjoint of an
adjunction is fully faithful, then each component of the counit is an
isomorphism. This is the Mathlib instance
`Adjunction.counit_isIso_of_R_fully_faithful` repackaged as a plain lemma. -/
@[sga "4 I 6.4" "partial", sga "4 IV 9.1.1" "partial"]
lemma counit_app_isIso_of_R_fullyFaithful
    (hRff : R.FullyFaithful) (X : D) : IsIso (h.counit.app X) :=
  isIso_counit_app_of_fullyFaithful h hRff X

/-- **Stacks 04D6 (h), backward direction.** If each component of the counit
is an isomorphism, then the right adjoint is fully faithful. This packages
`Adjunction.fullyFaithfulROfIsIsoCounit`. -/
@[sga "4 I 5.6" "v⇒iv",
  sga "4 I 5.7" "Remark 5.7 a)",
  sga "4 I 6.4" "partial",
  sga "4 IV 9.1.1" "partial"]
noncomputable def fullyFaithful_R_of_counit_app_isIso
    (hIso : ∀ X, IsIso (h.counit.app X)) : R.FullyFaithful :=
  have : IsIso h.counit := NatIso.isIso_of_isIso_app _
  h.fullyFaithfulROfIsIsoCounit

/-- **Stacks 04D6 (a).** A fully faithful right adjoint is, in particular,
faithful. -/
lemma faithful_R_of_fullyFaithful (hRff : R.FullyFaithful) : R.Faithful :=
  hRff.faithful

/-- **Stacks 04D6 (b).** If each component of the counit is an epimorphism,
then the right adjoint is faithful. This wraps
`Adjunction.faithful_R_of_epi_counit_app`. -/
@[sga "4 I 6.4" "partial"]
lemma faithful_R_of_counit_app_epi
    (hepi : ∀ X, Epi (h.counit.app X)) : R.Faithful :=
  h.faithful_R_of_epi_counit_app

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

Stacks tag 04D6 lists eight implications among eleven properties of a morphism of topoi
`f`, that is, of an adjunction `f⁻¹ ⊣ f_*`.  Formalized here, in that topos-free
adjunction form, are (a) `(2) ⇒ (1)`, (b) `(3) ⇒ (1)`, (d) `(9) ⇒ (3)`, the `(1) ⇒ (8)`
half of (g), and both directions of (h) `(7) ⇔ (2)`, relating full faithfulness of `f_*`,
faithfulness of `f_*`, the counit of the adjunction being pointwise epi or pointwise iso,
and `f_*` reflecting epimorphisms.
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

/-- **Stacks Tag 04D6** (abstract bundled form for an adjunction `L ⊣ R`,
playing the role of a morphism of topoi `f⁻¹ ⊣ f_*`). Five of the eight
sub-implications of the Stacks lemma in their topos-free formulation:

* (a) (2) ⇒ (1):       `R` fully faithful implies `R` faithful;
* (b) (3) ⇒ (1):       each component of the counit `L∘R ⟶ id` being an
                       epimorphism implies `R` is faithful;
* (d) (9) ⇒ (3):       if `R` reflects epimorphisms, then each component of
                       the counit is an epimorphism (since the counit-image
                       under `R` is split epi, hence epi);
* (g) (9) ⇒ (8), (10): a faithful functor reflects monomorphisms (8) and
                       bijections (10) automatically; we record (8) here, and
                       (10) follows by combining (8) with (9);
* (h) (7) ⇒ (2):       counit pointwise iso implies `R` fully faithful;
* (h) (2) ⇒ (7):       `R` fully faithful implies the counit is pointwise
                       iso.

All six are immediate consequences of existing Mathlib lemmas:
`Adjunction.faithful_R_of_epi_counit_app`, `Adjunction.counit_epi_of_R_faithful`,
`Adjunction.fullyFaithfulROfIsIsoCounit`,
`Adjunction.counit_isIso_of_R_fully_faithful`,
`Functor.reflectsMonomorphisms_of_faithful`. -/
@[stacks 04D6, sga "4 I 5.6" "iv) <=> v)", sga "4 I 6.4" "epic counit ⇒ ψ faithful"]
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


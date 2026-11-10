module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback

/-!
# Relative Proj as a functor: the witness of a strict equivalence is unique

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and `d` an integer. Two
quadruples `(d, f : T → S, L, ψ)` and `(d, f, L', ψ')` over a test scheme `T` are *strictly
equivalent* (Section 01NS) when there is an isomorphism `β : L ≅ L'` carrying `ψ` to `ψ'`, the
composite `β ∘ ψ` being spelled through the isomorphism `γ` of Laurent algebras induced by `β`.
`...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent` records that as an existential
statement. This file proves that **the pair `(β, γ)` it asserts the existence of is uniquely
determined**, so that the relation comes with a canonical comparison rather than a chosen one.

## Why uniqueness is the interesting half

A comparison that is merely chosen satisfies no identity it is not given. With uniqueness, every
identity between composites of comparisons holds automatically, because both sides are
comparisons of the same pair of quadruples: that is `Quadruple.eq_trans_of_witness` below, the
statement that the comparison of `P` with `R` is the composite of the comparisons of `P` with `Q`
and of `Q` with `R`. For a family of quadruples given on the members of an open cover, agreeing
pairwise on the overlaps, that is the cocycle condition on the triple overlaps, which is what the
glueing of the invertible modules `L` into a single invertible module consumes.

## Where the surjectivity of `ψ` enters

Section 01NS requires the degree-one component `f^*𝒜_d ⟶ L` of `ψ` to be surjective, and
`Quadruple.epi_app_one` carries that. It is exactly the hypothesis that makes the witness unique:
the two conditions on a witness say that `ψ ≫ γ = ψ'` in every degree, so in degree one two
witnesses agree after composition with the epimorphism `ψ_1`, hence agree. The degree-one
component of `γ` is `β` read through the identification `L^{⊗ 1} = L` of Tag 01CU, so `β` is
determined as well, and `γ` is then determined in every other degree by its multiplicativity.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent_app_eq_of_app_one`: **a homomorphism
  of the Laurent algebras of two invertible modules is determined by its degree-one component**,
  provided that component is the image of an isomorphism `L ≅ L'` under the identification
  `L^{⊗ 1} = L`. This is the statement the implementation notes of
  `...RelativeProjQcohSheaf.Quadruple` assert informally when they explain why recording a strict
  equivalence as a pair `(β, γ)` describes the same relation as recording `β` alone.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_witness_unique`:
  **the witness of a strict equivalence of quadruples is unique**, in both components.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_iff_existsUnique`:
  strict equivalence, restated as the existence of a *unique* isomorphism of the invertible
  modules carrying one `ψ` to the other.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.eq_trans_of_witness`: **the
  comparisons of three quadruples compose**, the form in which uniqueness is consumed by a
  glueing argument.

## Implementation notes

The degreewise statement is an induction out of degree one, two-sided, and it is the same
induction as the one `...RelativeProjQcohSheaf.LaurentCongr.congrIso_mul` and
`...RelativeProjQcohSheaf.UnionFunctor.pieceIso_hom_eq_laurentPullback` carry out. Upwards it is
the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n+1)}` of Tag 01CU, which is invertible.
Downwards there is no recursion to unfold — the negative tensor powers are iterates of a chosen
quasi-inverse of right tensoring — so the step is taken by cancellation: the two sides in degree
`n` become equal after tensoring on the right by `L'`, and tensoring by an invertible module is
an equivalence, hence faithful.

What turns the multiplicativity of a homomorphism of sheaves of graded algebras, which is stated
on homogeneous local sections, into the commuting square the induction consumes is
`...RelativeProjQcohSheaf.mulSheaf_comp_app`, and what identifies multiplication by the first
power with the successor comparison is `...LaurentPullback.mulIso_one_right`. The multiplication
of the Laurent algebra is read through `...LaurentPullback.mulSheaf_laurent`, which identifies
the morphism-level multiplication of a sheaf of graded algebras with the coherent multiplication
of Tag 01CU. `...RelativeProjQcohSheaf.mulSheaf_comp_app` is stated for a ringed space, and at a
scheme its conclusion mixes `Stacks.RingedSpace.structureRingSheaf` with
`AlgebraicGeometry.SheafedSpace.sheaf`; the two are equal by `rfl` and not syntactically equal,
so a `rw` into it reports a missing pattern rather than the cause. The crossing is made once, by
writing out the multiplicativity square at the spelling of a scheme and closing it by `exact`.

Degree zero is reached by the downward step from degree one rather than from the unit law of Tag
01CU: taking it that way avoids writing an identity morphism of the degree-zero piece, which is
the one place where the definitionally equal spellings `(laurent L).piece 0`,
`(laurent L').piece 0` and `𝟙_` would have to be reconciled inside a `rw`.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T : Scheme.{u}} {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-! ### A homomorphism of Laurent algebras is determined by its degree-one component -/

/-- **The successor law of a homomorphism of the Laurent algebras.** A homomorphism `γ` whose
degree-one component is an isomorphism `e : L ⟶ L'` read through the identification
`L^{⊗ 1} = L` of Tag 01CU satisfies, in every integral degree, the commuting square expressing
its component in degree `n + 1` through its component in degree `n` and `e`.

This is the multiplicativity of `γ` in bidegree `(n, 1)`, with multiplication by the first power
rewritten as the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` on either side and the
identification `L^{⊗ 1} = L` cancelled out. -/
theorem laurent_succIso_comp_app (γ : laurent L ⟶ laurent L') (e : L ⟶ L')
    (hone : γ.app 1 ≫ (oneIsoL L').hom = (oneIsoL L).hom ≫ e) (n : ℤ) :
    (succIso L n).hom ≫ γ.app (n + 1) =
      ((laurent L).piece n ◁ e) ≫ (γ.app n ▷ L') ≫ (succIso L' n).hom := by
  have h : (mulIso L n 1).hom ≫ γ.app (n + 1) =
      (γ.app n ⊗ₘ γ.app 1) ≫ (mulIso L' n 1).hom := by
    rw [← mulSheaf_laurent, ← mulSheaf_laurent]
    exact mulSheaf_comp_app (laurent L) (laurent L') γ n 1
  rw [mulIso_one_right, mulIso_one_right, Category.assoc] at h
  refine (Iso.cancel_iso_hom_left
    (MonoidalCategory.whiskerLeftIso ((laurent L).piece n) (oneIsoL L)) _ _).mp (h.trans ?_)
  rw [MonoidalCategory.whiskerLeftIso_hom, ← MonoidalCategory.whiskerLeft_comp_assoc, ← hone]
  simp only [tensorHom_def', Category.assoc, MonoidalCategory.whiskerLeft_comp]
  rw [whisker_exchange_assoc (γ.app n) ((oneIsoL L').hom)]

/-- The upward step: two homomorphisms of the Laurent algebras with the same degree-one
component, which agree in degree `n`, agree in degree `n + 1`, because the successor comparison
of Tag 01CU is invertible. -/
private theorem laurent_app_eq_succ {γ γ' : laurent L ⟶ laurent L'} {e : L ⟶ L'}
    (hone : γ.app 1 ≫ (oneIsoL L').hom = (oneIsoL L).hom ≫ e)
    (hone' : γ'.app 1 ≫ (oneIsoL L').hom = (oneIsoL L).hom ≫ e)
    {n : ℤ} (h : γ.app n = γ'.app n) : γ.app (n + 1) = γ'.app (n + 1) := by
  refine (Iso.cancel_iso_hom_left (succIso L n) _ _).mp ?_
  rw [laurent_succIso_comp_app γ e hone n, laurent_succIso_comp_app γ' e hone' n, h]

/-- The downward step, which is what reaches the negative degrees: the two components in degree
`n` become equal after tensoring on the right by `L'`, and tensoring by an invertible module is
an equivalence, hence faithful. The isomorphism cancelled on the left is the whiskering of the
degree-one component, which is invertible because it comes from an isomorphism of the invertible
modules. -/
private theorem laurent_app_eq_of_succ {γ γ' : laurent L ⟶ laurent L'} {e : L ≅ L'}
    (hone : γ.app 1 ≫ (oneIsoL L').hom = (oneIsoL L).hom ≫ e.hom)
    (hone' : γ'.app 1 ≫ (oneIsoL L').hom = (oneIsoL L).hom ≫ e.hom)
    {n : ℤ} (h : γ.app (n + 1) = γ'.app (n + 1)) : γ.app n = γ'.app n := by
  have h2 : ((laurent L).piece n ◁ e.hom) ≫ (γ.app n ▷ L') ≫ (succIso L' n).hom =
      ((laurent L).piece n ◁ e.hom) ≫ (γ'.app n ▷ L') ≫ (succIso L' n).hom := by
    rw [← laurent_succIso_comp_app γ e.hom hone n, ← laurent_succIso_comp_app γ' e.hom hone' n, h]
  have h3 := (Iso.cancel_iso_hom_left
    (MonoidalCategory.whiskerLeftIso ((laurent L).piece n) e) _ _).mp h2
  have h4 := (Iso.cancel_iso_hom_right _ _ (succIso L' n)).mp h3
  refine ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
      (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').map_injective ?_
  exact (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) (γ.app n) L').trans
    (h4.trans
      (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) (γ'.app n) L').symm)

/-- **A homomorphism of the Laurent algebras of two invertible modules is determined by its
degree-one component**, as soon as that component is the image of an isomorphism `e : L ≅ L'`
under the identification `L^{⊗ 1} = L` of Tag 01CU: two such homomorphisms with the same `e`
agree in every integral degree.

The induction is two-sided out of degree one: upwards the successor comparison of Tag 01CU is
invertible, downwards the whiskering `- ⊗ L'` is faithful. Degree zero is the downward step from
degree one. -/
theorem laurent_app_eq_of_app_one {γ γ' : laurent L ⟶ laurent L'} {e : L ≅ L'}
    (hone : γ.app 1 ≫ (oneIsoL L').hom = (oneIsoL L).hom ≫ e.hom)
    (hone' : γ'.app 1 ≫ (oneIsoL L').hom = (oneIsoL L).hom ≫ e.hom) (n : ℤ) :
    γ.app n = γ'.app n := by
  have hone1 : γ.app 1 = γ'.app 1 :=
    (Iso.cancel_iso_hom_right _ _ (oneIsoL L')).mp (hone.trans hone'.symm)
  induction n using Int.induction_on with
  | zero => exact laurent_app_eq_of_succ hone hone' (n := 0) (by rwa [zero_add])
  | succ i ih => exact laurent_app_eq_succ hone hone' ih
  | pred i ih =>
    exact laurent_app_eq_of_succ hone hone' (n := -(i : ℤ) - 1) (by rwa [sub_add_cancel])

namespace Quadruple

variable {S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- The first condition on a witness of a strict equivalence, read as the identification of the
degree-one component of `γ` with `β` through `L^{⊗ 1} = L`. This is the form
`laurent_app_eq_of_app_one` consumes. -/
private theorem app_one_comp_oneIso {P Q : Quadruple f A d} (β : P.L ≅ Q.L)
    (γ : laurent P.L ≅ laurent Q.L) (h1 : γ.hom.app 1 = (pieceOneIso β).hom) :
    γ.hom.app 1 ≫ (oneIsoL Q.L).hom = (oneIsoL P.L).hom ≫ β.hom := by
  rw [show γ.hom.app 1 = P.oneIso.hom ≫ β.hom ≫ Q.oneIso.inv from h1]
  simp

/-- **The witness of a strict equivalence of quadruples is unique.** Two pairs `(β, γ)` and
`(β', γ')` witnessing the strict equivalence of the same two quadruples are equal.

The degree-one components of `γ` and `γ'` agree because both compose with the degree-one
component of `ψ`, an epimorphism by `Quadruple.epi_app_one`, to the degree-one component of
`ψ'`; `β` and `β'` are those components read through `L^{⊗ 1} = L`, hence equal; and `γ` and
`γ'` then agree in every degree by `laurent_app_eq_of_app_one`. -/
theorem strictlyEquivalent_witness_unique {P Q : Quadruple f A d}
    {β β' : P.L ≅ Q.L} {γ γ' : laurent P.L ≅ laurent Q.L}
    (h1 : γ.hom.app 1 = (pieceOneIso β).hom)
    (hψ : ∀ n : ℤ, P.twisting.app n ≫ γ.hom.app n = Q.twisting.app n)
    (h1' : γ'.hom.app 1 = (pieceOneIso β').hom)
    (hψ' : ∀ n : ℤ, P.twisting.app n ≫ γ'.hom.app n = Q.twisting.app n) :
    β = β' ∧ γ = γ' := by
  have := P.epi_app_one
  have hone : γ.hom.app 1 = γ'.hom.app 1 :=
    (cancel_epi (P.twisting.app 1)).mp ((hψ 1).trans (hψ' 1).symm)
  have hβ : β = β' := Iso.ext ((Iso.cancel_iso_hom_left (oneIsoL P.L) _ _).mp
    ((app_one_comp_oneIso β γ h1).symm.trans
      (hone ▸ app_one_comp_oneIso β' γ' h1')))
  subst hβ
  exact ⟨rfl, Iso.ext (SheafOfModules.GradedAlgebra.Hom.ext fun n =>
      laurent_app_eq_of_app_one (e := β) (app_one_comp_oneIso β γ h1)
        (app_one_comp_oneIso β γ' h1') n)⟩

/-- **Strict equivalence of quadruples, with the witness pinned down**: two quadruples over the
same morphism are strictly equivalent exactly when there is a *unique* isomorphism of their
invertible modules carrying one `ψ` to the other.

The source writes the condition as the existence of an isomorphism `β`; this says that the `β`
so obtained is canonical. -/
theorem strictlyEquivalent_iff_existsUnique (P Q : Quadruple f A d) :
    StrictlyEquivalent P Q ↔
      ∃! β : P.L ≅ Q.L, ∃ γ : laurent P.L ≅ laurent Q.L,
        γ.hom.app 1 = (pieceOneIso β).hom ∧
          ∀ n : ℤ, P.twisting.app n ≫ γ.hom.app n = Q.twisting.app n := by
  constructor
  · rintro ⟨β, γ, h1, hψ⟩
    refine ⟨β, ⟨γ, h1, hψ⟩, ?_⟩
    rintro β' ⟨γ', h1', hψ'⟩
    exact (strictlyEquivalent_witness_unique h1' hψ' h1 hψ).1
  · rintro ⟨β, ⟨γ, h1, hψ⟩, -⟩
    exact ⟨β, γ, h1, hψ⟩

/-- **The comparisons of three quadruples compose**: if `β` witnesses the strict equivalence of
`P` with `Q`, `δ` that of `Q` with `R` and `ε` that of `P` with `R`, then `ε` is the composite of
`β` and `δ`.

This is the form in which the uniqueness of the witness is consumed by a glueing argument: for a
family of quadruples on the members of an open cover which agree pairwise on the overlaps, it is
the cocycle condition on the triple overlaps. -/
theorem eq_trans_of_witness {P Q R : Quadruple f A d}
    {β : P.L ≅ Q.L} {γ : laurent P.L ≅ laurent Q.L}
    (h1 : γ.hom.app 1 = (pieceOneIso β).hom)
    (hψ : ∀ n : ℤ, P.twisting.app n ≫ γ.hom.app n = Q.twisting.app n)
    {δ : Q.L ≅ R.L} {γ' : laurent Q.L ≅ laurent R.L}
    (h2 : γ'.hom.app 1 = (pieceOneIso δ).hom)
    (hψ' : ∀ n : ℤ, Q.twisting.app n ≫ γ'.hom.app n = R.twisting.app n)
    {ε : P.L ≅ R.L} {γ'' : laurent P.L ≅ laurent R.L}
    (h3 : γ''.hom.app 1 = (pieceOneIso ε).hom)
    (hψ'' : ∀ n : ℤ, P.twisting.app n ≫ γ''.hom.app n = R.twisting.app n) :
    β ≪≫ δ = ε := by
  refine (strictlyEquivalent_witness_unique (β := β ≪≫ δ) (γ := γ ≪≫ γ') ?_ ?_ h3 hψ'').1
  · change γ.hom.app 1 ≫ γ'.hom.app 1 = (pieceOneIso (β ≪≫ δ)).hom
    rw [h1, h2]
    simp
  · intro n
    change P.twisting.app n ≫ γ.hom.app n ≫ γ'.hom.app n = R.twisting.app n
    rw [← Category.assoc, hψ n, hψ' n]

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end

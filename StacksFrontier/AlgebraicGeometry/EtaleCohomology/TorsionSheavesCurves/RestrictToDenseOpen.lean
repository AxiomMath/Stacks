module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointsVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ClosedComplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.StatementsShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# Reduction of the assertions for torsion sheaves on curves to a dense open subscheme

Let `k` be an algebraically closed field, let `X` be a separated finite type scheme over `k` of
dimension at most one and let `F` be a constructible torsion abelian sheaf on `X_étale`. Stacks
Project Tag 0GJA asserts that if `j : X' ⟶ X` is the inclusion of a *dense* open subscheme, then
the eight statements of Situation 0A52 hold for `F` **if and only if** they hold for
`j_! j^{-1} F`.

The source proves both directions at once from the localization sequence of Tag 095L,

```
0 ⟶ j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F ⟶ 0,
```

`i : Z ⟶ X` being the closed immersion of the complement. Density of `X'` is used exactly once,
and only to control the right-hand term: it makes `Z` zero-dimensional, hence a finite set of
`k`-rational points, so `H^q_étale(X, i_* i^{-1} F) = H^q_étale(Z, i^{-1} F)` vanishes for
`q > 0`, is the finite direct sum `⨁ F_{x_i}` of the stalks for `q = 0`, and is unchanged by an
extension of the algebraically closed ground field. Everything else is the long exact sequence.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafCohomology_X₁_of_shortExact_of_two_le` and
  `Stacks.EtaleCohomology.finite_sheafCohomology_X₁_of_shortExact_of_acyclic`: vanishing and
  finiteness of cohomology pass from the middle term of a short exact sequence to the
  **sub**-sheaf, when the quotient has cohomology concentrated in degree zero. These are the
  converses of the two dévissage steps of `…TorsionSheavesCurves.PrimaryVanishing`, which go to
  the middle term.
* `Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_pred`,
  `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_injective`
  and `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_X₁_of_shortExact`: the
  same for the restriction map on étale cohomology, in the direction the sub-sheaf needs.
* `Stacks.EtaleCohomology.curveCohomologyStatements_of_cohomology_concentrated`: a sheaf whose
  étale cohomology vanishes in positive degrees, is finite in degree zero and has bijective
  restriction satisfies **all eight** statements of Situation 0A52.
* `Stacks.EtaleCohomology.curveCohomologyStatements_of_isZero`: the eight statements for the zero
  sheaf.
* `Stacks.EtaleCohomology.curveCohomologyStatements_X₁_of_shortExact`: all eight statements pass
  from the middle term of such a short exact sequence to the sub-sheaf.
* `Stacks.EtaleCohomology.curveCohomologyStatements_extensionByZero_iff_of_closedComplement`:
  **Tag 0GJA**, the biconditional, for the localization sequence of Tag 095L.
* `Stacks.EtaleCohomology.subsingleton_etaleCohomology_directImage_of_closed_points`: the
  positive-degree half of the closed-part input, *proved*: if the closed complement `Z` is affine
  with all points closed and separably closed residue fields, then `H^q(X, i_* G) = 0` for
  `q > 0`.

## Implementation notes

**The long exact sequence, in the direction towards the sub-sheaf.** Writing `A^q`, `B^q`, `C^q`
for the degree-`q` étale cohomology of the three terms, the segment `C^{q-1} → A^q → B^q` and
the monomorphism `A^0 ↪ B^0` bound the sub-sheaf. Both come from
Mathlib's covariant long exact sequence of `Ext` (`Abelian.Ext.covariant_sequence_exact₁`,
`covariant_sequence_exact₁'` and `Ext.postcomp_mk₀_injective_of_mono`). Because `C^q` vanishes
for `q > 0`, the vanishing statements transfer in the degree range `q ≥ 2` in which Situation
0A52 states them, and the finiteness statements transfer in every degree.

**What is carried as a hypothesis and why.** Two groups.

*The cohomology of the closed part.* `hvanish`, `hfinite` and `hrestr` say that the cohomology of
`i_* i^{-1} F` vanishes above degree zero, is finite in degree zero, and has bijective
restriction. This is where the whole geometric content of the source's density hypothesis sits.
Of the three, the first is **proved** here as
`subsingleton_etaleCohomology_directImage_of_closed_points`, from the vanishing of positive-degree
étale cohomology on a scheme of separably closed closed points (Tag 09AY,
`AlgebraicGeometry.subsingleton_etaleCohomology_of_closed_points'`) and the Leray collapse along
an integral morphism (Tag 03QP, `sheafHSmallEtalePushforwardAddEquiv`); it is at the coefficient
universe `AddCommGrpCat.{u + 1}` in which those two results are stated, which is a specialization
of the `AddCommGrpCat.{max (u + 1) v}` the statements below are at. The other two are not
available: `hfinite` needs the stalks of a constructible sheaf to be finite, and `hrestr` needs
the invariance of those stalks under an extension of algebraically closed fields, neither of
which this library has. In particular the dimension bound, the density of `X'` and the
constructibility of `F` do not appear below — they enter only through these three hypotheses, and
the statements are correspondingly more general than the source's.

*The side-condition transfers.* The eight statements are implications whose hypotheses constrain
the coefficient sheaf, so transferring a statement between two different sheaves requires
transferring its side condition in the opposite direction. `hprimePower`, `hprimeToChar` and
`hconstructible` are those transfers, and they go from the sub-sheaf to the middle term. That is
the direction the dévissage consumes here, and it is the opposite of the one proved in
`Stacks.EtaleCohomology.isPrimePowerTorsion_of_shortExact` and
`isPrimeToCharacteristicTorsion_of_shortExact`, which descend a torsion condition from the middle
term to the outer ones (what Tag 0A5C needs and what the source's remark (a) records), and so
do not apply. This is the same treatment the three conditions receive in
`Stacks.EtaleCohomology.curveCohomologyStatements_X₂_of_shortExact_of_constructible_and` (Tag 0A5C)
and `Stacks.EtaleCohomology.curveCohomologyStatements_smallEtaleDirectImageAb` (Tag 0A5D), the
only other results stated at the level of the bundled conjunction. Constructibility is in addition
an abstract predicate parameter of `CurveCohomologyStatements` rather than
`AlgebraicGeometry.IsConstructibleAbelianSheaf`, for the reason recorded there.

**Tag 095L is not a hypothesis.** Unlike the module-coefficient analogue
`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_iff_extensionByZero` (Tag 0GJE),
which carries the localization sequence as `h095L` because it is only available for abelian
sheaves, the biconditional below is for abelian sheaves and so uses
`Stacks.EtaleCohomology.openClosedShortComplex_shortExact` directly.

Vanishing is spelled `Subsingleton`, matching Mathlib's `CategoryTheory.Sheaf.H`, which is an
`Ext`-group from the constant sheaf `ℤ` and so has no canonical zero element to compare against.

## References

* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 09AY](https://stacks.math.columbia.edu/tag/09AY)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w w'

namespace Stacks.EtaleCohomology

/-! ### The long exact sequence towards the sub-sheaf -/

section ExtDevissage

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact) (A : C)

/-- **Vanishing passes from the middle term of a short exact sequence to the sub-object**, in the
degree range `q ≥ 2`, when `Ext^n(A, S.X₃)` vanishes for every `n > 0`.

The class to be killed lies in the middle of the exact segment
`Ext^{q-1}(A, S.X₃) → Ext^q(A, S.X₁) → Ext^q(A, S.X₂)`, whose left-hand group vanishes because
`q - 1 > 0` and whose right-hand group vanishes by hypothesis. -/
theorem subsingleton_ext_X₁_of_shortExact_of_vanishing (hS : S.ShortExact) (A : C)
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Ext.{w} A S.X₃ q)) (q : ℕ) (hq : 2 ≤ q)
    (h₂ : Subsingleton (Ext.{w} A S.X₂ q)) :
    Subsingleton (Ext.{w} A S.X₁ q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  refine ⟨fun x y => ?_⟩
  suffices hxy : x - y = 0 by exact sub_eq_zero.mp hxy
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ A hS (x - y) (h₂.elim _ _) rfl
  have : Subsingleton (Ext.{w} A S.X₃ n) := hpos n (by omega)
  rw [Subsingleton.elim c 0] at hc
  simpa using hc.symm

/-- A family of types which is finite in degree zero and subsingleton in positive degrees is
finite in every degree. -/
private theorem finite_of_finite_zero_of_subsingleton_pos {α : ℕ → Type*} (h₀ : Finite (α 0))
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (α q)) (q : ℕ) : Finite (α q) := by
  rcases q with _ | n
  · exact h₀
  · have := hpos (n + 1) n.succ_pos
    exact Finite.of_subsingleton

/-- **Finiteness passes from the middle term of a short exact sequence to the sub-object**, in
every degree, when `Ext^0(A, S.X₃)` is finite and `Ext^n(A, S.X₃)` vanishes for every `n > 0`.

In degree zero the sub-object injects into the middle one, because `S.f` is a monomorphism; in
degree `n + 1` it sits in the exact segment
`Ext^n(A, S.X₃) → Ext^{n+1}(A, S.X₁) → Ext^{n+1}(A, S.X₂)` between two finite groups. -/
theorem finite_ext_X₁_of_shortExact_of_acyclic (hS : S.ShortExact) (A : C)
    (hfinite : Finite (Ext.{w} A S.X₃ 0))
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Ext.{w} A S.X₃ q)) (q : ℕ)
    (h₂ : Finite (Ext.{w} A S.X₂ q)) :
    Finite (Ext.{w} A S.X₁ q) := by
  match q with
  | 0 =>
    have := h₂
    exact Finite.of_injective _
      (Ext.postcomp_mk₀_injective_of_mono (hf := hS.mono_f) A S.f)
  | (n + 1) =>
    have h₃ := finite_of_finite_zero_of_subsingleton_pos
      (α := fun q => Ext.{w} A S.X₃ q) hfinite hpos n
    have := h₂
    exact (Ext.covariant_sequence_exact₁' A hS n (n + 1) rfl).ab_finite

/-- **`Ext` out of anything into a zero object vanishes.** A class into `B` factors through the
identity of `B`, which is zero. -/
theorem subsingleton_ext_of_isZero_right (A : C) {B : C} (hB : IsZero B) (q : ℕ) :
    Subsingleton (Ext.{w} A B q) := by
  have key : ∀ z : Ext.{w} A B q, z = 0 := fun z =>
    (Ext.comp_mk₀_id z).symm.trans (by rw [hB.eq_of_src (𝟙 B) 0, Ext.mk₀_zero, Ext.comp_zero])
  exact ⟨fun x y => by rw [key x, key y]⟩

end ExtDevissage

section CohomologyDevissage

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- **Vanishing of sheaf cohomology passes from the middle term of a short exact sequence of
abelian sheaves to the sub-sheaf**, in the degree range `q ≥ 2`, when the cohomology of the
quotient vanishes in every positive degree. -/
theorem subsingleton_sheafCohomology_X₁_of_shortExact_of_two_le (hS : S.ShortExact)
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w', w} S.X₃ q)) (q : ℕ) (hq : 2 ≤ q)
    (h₂ : Subsingleton (Sheaf.H.{w', w} S.X₂ q)) :
    Subsingleton (Sheaf.H.{w', w} S.X₁ q) :=
  subsingleton_ext_X₁_of_shortExact_of_vanishing hS _ hpos q hq h₂

/-- **Finiteness of sheaf cohomology passes from the middle term of a short exact sequence of
abelian sheaves to the sub-sheaf**, in every degree, when the cohomology of the quotient is
finite in degree zero and vanishes in every positive degree. -/
theorem finite_sheafCohomology_X₁_of_shortExact_of_acyclic (hS : S.ShortExact)
    (hfinite : Finite (Sheaf.H.{w', w} S.X₃ 0))
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w', w} S.X₃ q)) (q : ℕ)
    (h₂ : Finite (Sheaf.H.{w', w} S.X₂ q)) :
    Finite (Sheaf.H.{w', w} S.X₁ q) :=
  finite_ext_X₁_of_shortExact_of_acyclic hS _ hfinite hpos q h₂

end CohomologyDevissage

section SmallEtaleSite

variable {X : Scheme.{u}}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- `Stacks.EtaleCohomology.subsingleton_sheafCohomology_X₁_of_shortExact_of_two_le` on the small
étale site of a scheme, at the coefficient universe `AddCommGrpCat.{max (u + 1) v}` in which étale
cohomology of a scheme in `Scheme.{u}` is computed. The coefficient-universe side condition of the
site-generic statement is discharged by name rather than by instance search, for the reason
recorded on
`Stacks.EtaleCohomology.subsingleton_etaleCohomology_of_shortExact_of_isPrimePowerTorsion'`. -/
theorem subsingleton_etaleCohomology_X₁_of_shortExact (hS : S.ShortExact)
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w, max (u + 1) v} S.X₃ q)) (q : ℕ)
    (hq : 2 ≤ q) (h₂ : Subsingleton (Sheaf.H.{w, max (u + 1) v} S.X₂ q)) :
    Subsingleton (Sheaf.H.{w, max (u + 1) v} S.X₁ q) :=
  let : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
    Scheme.hasSheafify_smallEtaleTopology X
  subsingleton_sheafCohomology_X₁_of_shortExact_of_two_le hS hpos q hq h₂

/-- `Stacks.EtaleCohomology.finite_sheafCohomology_X₁_of_shortExact_of_acyclic` on the small étale
site of a scheme, at the coefficient universe `AddCommGrpCat.{max (u + 1) v}`. -/
theorem finite_etaleCohomology_X₁_of_shortExact (hS : S.ShortExact)
    (hfinite : Finite (Sheaf.H.{w, max (u + 1) v} S.X₃ 0))
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w, max (u + 1) v} S.X₃ q)) (q : ℕ)
    (h₂ : Finite (Sheaf.H.{w, max (u + 1) v} S.X₂ q)) :
    Finite (Sheaf.H.{w, max (u + 1) v} S.X₁ q) :=
  let : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
    Scheme.hasSheafify_smallEtaleTopology X
  finite_sheafCohomology_X₁_of_shortExact_of_acyclic hS hfinite hpos q h₂

end SmallEtaleSite

/-! ### The restriction map towards the sub-sheaf -/

section Restriction

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- **Injectivity of the restriction map passes from the middle term of a short exact sequence
to the sub-sheaf.** In degree `r` it needs injectivity for the middle term in degree `r`, and —
when `r` has a predecessor `q` — surjectivity for the middle term and injectivity for the
quotient in degree `q`.

A class restricting to zero is killed by the composite into the middle term, hence in degree
zero is zero outright, and in degree `q + 1` comes from a class on the quotient in degree `q`
which, by the two hypotheses in degree `q`, is the image of a class on the middle term; the
connecting map then kills it. -/
theorem injective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_pred (hS : S.ShortExact) (r : ℕ)
    (h₂ : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ r))
    (hprev : ∀ q : ℕ, q + 1 = r →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q) ∧
        Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q)) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ r) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
  have hzf : ∀ z : Sheaf.H.{w} S.X₁ r,
      etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ r z = 0 →
        z.comp (Ext.mk₀ S.f) (add_zero r) = 0 := fun z hrz => by
    refine h₂ ?_
    rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.f r z, hrz, Ext.zero_comp, map_zero]
  have key : ∀ z : Sheaf.H.{w} S.X₁ r,
      etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ r z = 0 → z = 0 := by
    rcases r with _ | n
    · intro z hrz
      exact Ext.postcomp_mk₀_injective_of_mono (hf := hS.mono_f) _ S.f (by simpa using hzf z hrz)
    · obtain ⟨h₂surj, h₃inj⟩ := hprev n rfl
      intro z hrz
      have hzf := hzf z hrz
      obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS z hzf rfl
      have hcr : (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ n c).comp hS'.extClass rfl
          = 0 := by
        rw [← etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} i hS n (n + 1) rfl c, hc, hrz]
      obtain ⟨b', hb'⟩ := Ext.covariant_sequence_exact₃ _ hS' _ rfl hcr
      obtain ⟨b, hb⟩ := h₂surj b'
      have hbg : b.comp (Ext.mk₀ S.g) (add_zero n) = c := by
        refine h₃inj ?_
        rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.g n b, hb]
        exact hb'
      rw [← hc, ← hbg, Ext.comp_assoc_of_second_deg_zero,
        ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
  intro x y hxy
  exact sub_eq_zero.mp (key (x - y) (by rw [map_sub, hxy, sub_self]))

/-- **Surjectivity of the restriction map passes from the middle term of a short exact sequence
to the sub-sheaf.** In degree `r` it needs surjectivity for the middle term and injectivity for
the quotient in degree `r`, and — when `r` has a predecessor `q` — surjectivity for the quotient
in degree `q`.

The source uses this for statement (8) of Situation 0A52, in degree `r = 2`. -/
theorem surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_injective
    (hS : S.ShortExact) (r : ℕ)
    (h₂ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ r))
    (h₃ : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ r))
    (hprev : ∀ q : ℕ, q + 1 = r →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ r) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
  have main : ∀ y : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj S.X₁) r,
      ∃ x₁ : Sheaf.H.{w} S.X₁ r,
        (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ r x₁ - y).comp
          (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) (add_zero r) = 0 := by
    intro y
    obtain ⟨x₂, hx₂⟩ := h₂
      (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) (add_zero r))
    have hx₂g : x₂.comp (Ext.mk₀ S.g) (add_zero r) = 0 := by
      refine h₃ ?_
      rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.g r x₂, hx₂, map_zero,
        Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp,
        S.zero, Functor.map_zero, Ext.mk₀_zero, Ext.comp_zero]
    obtain ⟨x₁, hx₁⟩ := Ext.covariant_sequence_exact₂ _ hS x₂ hx₂g
    refine ⟨x₁, ?_⟩
    have hsub : ∀ a b : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj S.X₁) r,
        (a - b).comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) (add_zero r) =
          a.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) (add_zero r) -
            b.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) (add_zero r) :=
      fun a b => map_sub (Ext.postcomp
        (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) _ (add_zero r)) a b
    rw [hsub, ← etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.f r x₁, hx₁, hx₂, sub_self]
  rcases r with _ | n
  · intro y
    obtain ⟨x₁, hkey⟩ := main y
    refine ⟨x₁, ?_⟩
    have hz0 : etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ 0 x₁ - y = 0 :=
      Ext.postcomp_mk₀_injective_of_mono (hf := hS'.mono_f) _
        ((etaleAbelianInverseImage.{u, v} i).map S.f) (by rw [map_zero]; exact hkey)
    exact sub_eq_zero.mp hz0
  · intro y
    obtain ⟨x₁, hkey⟩ := main y
    obtain ⟨c', hc'⟩ := Ext.covariant_sequence_exact₁ _ hS' _ hkey rfl
    obtain ⟨c, hc⟩ := hprev n rfl c'
    refine ⟨x₁ - c.comp hS.extClass rfl, ?_⟩
    rw [map_sub, etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} i hS n (n + 1) rfl c, hc,
      hc']
    abel

/-- **Bijectivity of the restriction map passes from the middle term of a short exact sequence to
the sub-sheaf**, in every degree, when it is bijective for the quotient in every degree.

This is the converse direction of
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_shortExact`, and it is what
statements (6) and (7) of Situation 0A52 need. -/
theorem bijective_etaleCohomologyRestrictionMap_X₁_of_shortExact (hS : S.ShortExact)
    (h₂ : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q))
    (h₃ : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q)) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ q) :=
  ⟨injective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_pred.{u, v, w} i hS q (h₂ q).1
      (fun n _ => ⟨(h₂ n).2, (h₃ n).1⟩),
    surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_injective.{u, v, w} i hS q
      (h₂ q).2 (h₃ q).1
      (fun n _ => (h₃ n).2)⟩

end Restriction

/-! ### All eight statements towards the sub-sheaf -/

section Statements

variable {X Y : Scheme.{u}} (i : Y ⟶ X) {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (l p : ℕ)
  {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **A sheaf whose cohomology is concentrated, finite and insensitive to restriction satisfies
all eight statements of Situation 0A52.** If the étale cohomology of `G` vanishes in every
positive degree, is finite in degree zero, and has bijective restriction along `i` in every
degree, then every one of the eight statements holds for `G`, unconditionally on its side
conditions.

In Tag 0GJA this is applied to `G = i_* i^{-1} F` for the closed complement `i : Z ⟶ X` of a
dense open: the source's computation of the cohomology of that sheaf is exactly the three
hypotheses. It is also the first construction of a term of
`Stacks.EtaleCohomology.CurveCohomologyStatements` in this library. -/
theorem curveCohomologyStatements_of_cohomology_concentrated
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hvanish : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w} G q))
    (hfinite : Finite (Sheaf.H.{w} G 0))
    (hrestr : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i G q)) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible G where
  vanishing q hq := hvanish q (by omega)
  vanishing_of_isAffine _ q hq := hvanish q (by omega)
  vanishing_of_isPrimePowerTorsion _ q hq := hvanish q (by omega)
  finite_of_isPrimeToCharacteristicTorsion _ _ q := finite_of_finite_zero_of_subsingleton_pos
    (α := fun q => Sheaf.H.{w} G q) hfinite hvanish q
  finite_of_isProper _ _ q := finite_of_finite_zero_of_subsingleton_pos
    (α := fun q => Sheaf.H.{w} G q) hfinite hvanish q
  bijective_restriction_of_isPrimeToCharacteristicTorsion _ q := hrestr q
  bijective_restriction_of_isProper _ q := hrestr q
  surjective_restriction := (hrestr 2).2

/-- **The eight statements of Situation 0A52 hold for the zero sheaf**, on any scheme and
relative to any structure morphism, any pair of integers, any constructibility predicate and any
morphism along which cohomology is restricted. Its cohomology vanishes in every degree, and so
does that of its inverse image, so the three hypotheses of
`Stacks.EtaleCohomology.curveCohomologyStatements_of_cohomology_concentrated` hold.

This is recorded because it exhibits `Stacks.EtaleCohomology.CurveCohomologyStatements` as
inhabited: before it, the structure appeared in the library only as the hypothesis and the
conclusion of implications (Tags 0A5C and 0A5D), with no term of it ever constructed. -/
theorem curveCohomologyStatements_of_isZero
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hG : IsZero G) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible G := by
  have hGY : IsZero ((etaleAbelianInverseImage.{u, v} i).obj G) :=
    (etaleAbelianInverseImage.{u, v} i).map_isZero hG
  have hvanish : ∀ q : ℕ, Subsingleton (Sheaf.H.{w} G q) := fun q =>
    subsingleton_ext_of_isZero_right _ hG q
  have hvanishY : ∀ q : ℕ,
      Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj G) q) := fun q =>
    subsingleton_ext_of_isZero_right _ hGY q
  refine curveCohomologyStatements_of_cohomology_concentrated.{u, v, w} i π l p
    (fun q _ => hvanish q) (have := hvanish 0; Finite.of_subsingleton) fun q => ?_
  have := hvanish q
  have := hvanishY q
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

variable {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- **All eight statements of Situation 0A52 pass from the middle term of a short exact sequence
of abelian étale sheaves to the sub-sheaf**, when the cohomology of the quotient vanishes above
degree zero, is finite in degree zero, and has bijective restriction in every degree.

`hprimePower`, `hprimeToChar` and `hconstructible` are the transfers of the three side conditions
on the coefficient sheaf, from the sub-sheaf to the middle term — the direction the dévissage
consumes. See the implementation notes of this file. -/
theorem curveCohomologyStatements_X₁_of_shortExact (hS : S.ShortExact)
    (hvanish : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w} S.X₃ q))
    (hfinite : Finite (Sheaf.H.{w} S.X₃ 0))
    (hrestr : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q))
    (hprimePower : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₁ →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₂)
    (hprimeToChar : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₁ →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₂)
    (hconstructible : constructible S.X₁ → constructible S.X₂)
    (h₂ : CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₂) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₁ where
  vanishing q hq :=
    subsingleton_etaleCohomology_X₁_of_shortExact.{u, v, w} hS hvanish q (by omega)
      (h₂.vanishing q hq)
  vanishing_of_isAffine hX q hq :=
    subsingleton_etaleCohomology_X₁_of_shortExact.{u, v, w} hS hvanish q (by omega)
      (h₂.vanishing_of_isAffine hX q hq)
  vanishing_of_isPrimePowerTorsion htorsion q hq :=
    subsingleton_etaleCohomology_X₁_of_shortExact.{u, v, w} hS hvanish q (by omega)
      (h₂.vanishing_of_isPrimePowerTorsion (hprimePower htorsion) q hq)
  finite_of_isPrimeToCharacteristicTorsion hconstr htorsion q :=
    finite_etaleCohomology_X₁_of_shortExact.{u, v, w} hS hfinite hvanish q
      (h₂.finite_of_isPrimeToCharacteristicTorsion (hconstructible hconstr)
        (hprimeToChar htorsion) q)
  finite_of_isProper hconstr hπ q :=
    finite_etaleCohomology_X₁_of_shortExact.{u, v, w} hS hfinite hvanish q
      (h₂.finite_of_isProper (hconstructible hconstr) hπ q)
  bijective_restriction_of_isPrimeToCharacteristicTorsion htorsion q :=
    bijective_etaleCohomologyRestrictionMap_X₁_of_shortExact.{u, v, w} i hS
      (h₂.bijective_restriction_of_isPrimeToCharacteristicTorsion (hprimeToChar htorsion)) hrestr q
  bijective_restriction_of_isProper hπ q :=
    bijective_etaleCohomologyRestrictionMap_X₁_of_shortExact.{u, v, w} i hS
      (h₂.bijective_restriction_of_isProper hπ) hrestr q
  surjective_restriction :=
    surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_injective.{u, v, w} i hS 2
      h₂.surjective_restriction (hrestr 2).1 (fun n hn => by
        obtain rfl : n = 1 := by omega
        exact (hrestr 1).2)

end Statements

/-! ### Tag 0GJA: the reduction to a dense open subscheme -/

section DenseOpen

variable {X Z X' Y : Scheme.{u}} (i' : Z ⟶ X) (j : X' ⟶ X) (i : Y ⟶ X)
  [IsClosedImmersion i'] [IsOpenImmersion j]
  {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (l p : ℕ)
  {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks Project, Tag 0GJA.** Let `j : X' ⟶ X` be an open immersion and let `i' : Z ⟶ X` be a
closed immersion onto the complement of its image. Let `F` be an abelian sheaf on the small étale
site of `X`. Then the eight statements of Situation 0A52 hold for `F` **if and only if** they
hold for `j_! j^{-1} F`.

Both directions are read off the localization short exact sequence
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0` of Tag 095L, which is
`Stacks.EtaleCohomology.openClosedShortComplex_shortExact`. The forward direction is
`Stacks.EtaleCohomology.curveCohomologyStatements_X₁_of_shortExact` and the backward one is
Tag 0A5C, `Stacks.EtaleCohomology.curveCohomologyStatements_X₂_of_shortExact_of_constructible_and`,
fed with the eight statements for `i_* i^{-1} F` supplied by
`Stacks.EtaleCohomology.curveCohomologyStatements_of_cohomology_concentrated`.

The hypotheses `hvanish`, `hfinite` and `hrestr` are the cohomology of the closed part, which is
where the source's density assumption, its dimension bound and the constructibility of `F` all
act: `Z` becomes a finite set of `k`-rational points, so that cohomology is concentrated in degree
zero, is the finite direct sum of the stalks of `F` at those points, and does not change under an
extension of the algebraically closed ground field. The positive-degree half is proved in this
file as `Stacks.EtaleCohomology.subsingleton_etaleCohomology_directImage_of_closed_points`; the
other two halves are not available in this library.

`hprimePower`, `hprimeToChar`, `hconstructible` and `hconstructible'` are the transfers of the
three side conditions of the eight statements between the two sheaves, in the two directions the
two implications consume.

Since the cohomology of the closed part and the side-condition transfers are carried, this is a
reference to Stacks Project, Tag 0GJA and not a registration of it; the tag has no registration in
this library. -/
theorem curveCohomologyStatements_extensionByZero_iff_of_closedComplement
    (hij : Set.range j.base = (Set.range i'.base)ᶜ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hvanish : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w}
      ((etaleAbelianDirectImage.{u, v} i').obj ((etaleAbelianInverseImage.{u, v} i').obj F)) q))
    (hfinite : Finite (Sheaf.H.{w}
      ((etaleAbelianDirectImage.{u, v} i').obj ((etaleAbelianInverseImage.{u, v} i').obj F)) 0))
    (hrestr : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i
      ((etaleAbelianDirectImage.{u, v} i').obj ((etaleAbelianInverseImage.{u, v} i').obj F)) q))
    (hprimePower : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l
        ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l F)
    (hprimeToChar : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p
        ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p F)
    (hconstructible :
      constructible ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) →
        constructible F)
    (hconstructible' : constructible F →
      constructible ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) ∧
        constructible ((etaleAbelianDirectImage.{u, v} i').obj
          ((etaleAbelianInverseImage.{u, v} i').obj F))) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible F ↔
      CurveCohomologyStatements.{u, v, w} i π l p constructible
        ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) := by
  have hS := openClosedShortComplex_shortExact.{u, v} i' j hij F
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact curveCohomologyStatements_X₁_of_shortExact.{u, v, w} i π l p hS hvanish hfinite hrestr
      hprimePower hprimeToChar hconstructible h
  · exact curveCohomologyStatements_X₂_of_shortExact_of_constructible_and.{u, v, w} i π l p hS
      hconstructible' h
      (curveCohomologyStatements_of_cohomology_concentrated.{u, v, w} i π l p hvanish hfinite
        hrestr)

end DenseOpen

/-! ### The cohomology of the closed part, in positive degrees -/

section ClosedPart

/-- **The positive-degree étale cohomology of the direct image along a closed immersion whose
source has only closed points with separably closed residue fields vanishes.**

This is the positive-degree half of the closed-part input of Tag 0GJA, and it is the half this
library can prove. The two inputs are the Leray collapse along an integral morphism, Tag 03QP,
in the form `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`, and the vanishing of
positive-degree étale cohomology on such a scheme, Tag 09AY, in the form
`AlgebraicGeometry.subsingleton_etaleCohomology_of_closed_points'`. In Tag 0GJA the source `Z` is
the complement of a dense open in a scheme of dimension at most one over an algebraically closed
field, hence a finite set of `k`-rational points, which satisfies the three hypotheses.

The coefficient universe is `AddCommGrpCat.{u + 1}`, the one in which both inputs are stated; it
is the specialization `v := u + 1` of the `AddCommGrpCat.{max (u + 1) v}` of the statements
above. -/
theorem subsingleton_etaleCohomology_directImage_of_closed_points {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsAffine Z]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hclosed : ∀ z : Z, IsClosed ({z} : Set Z))
    (hsep : ∀ z : Z, IsSepClosed (Z.residueField z))
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} i).obj G) q) := by
  have := AlgebraicGeometry.subsingleton_etaleCohomology_of_closed_points'.{u, u + 1}
    Z hclosed hsep G q hq
  exact (sheafHSmallEtalePushforwardAddEquiv i G q).symm.injective.subsingleton

end ClosedPart

end Stacks.EtaleCohomology

end

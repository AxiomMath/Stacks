module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Order.RelClasses

/-!
# A transfinite recursion producing a strictly transitive system of morphisms

Let `E` be a well ordered set, let `C` be a category and let `G : E → C` be a family of objects.
A *strictly transitive system* on `G` is a family of morphisms `τ_{β,α} : G β ⟶ G α`, one for
each `β ≤ α`, with `τ_{α,α} = 𝟙` and `τ_{β,γ} ≫ τ_{γ,α} = τ_{β,α}` — equivalently, a functor
`E ⥤ C` whose value at `α` is `G α`.

Such a system cannot be assembled out of unrelated choices stage by stage: the transitions into
a stage have to be chosen compatibly with *every* earlier choice, and that compatibility is not
a property of one stage.  What this file proves is that one local obligation suffices — if at
every stage `α` the morphisms into `G α` can be chosen compatibly with an arbitrary strictly
transitive system already given below `α`, then a strictly transitive system exists on all of
`E`.  That is `Stacks.Transfinite.exists_coherentSystem_of_step`.

It is the transfinite recursion of [Stacks, Tag 0D6B] with the sheaf theory stripped out: there
`G α` is the extension by zero of a chosen K-injective representative of the prescribed object on
the `α`-th member of the cover, and the step at `α` is the choice of a map of complexes out of
the colimit of the earlier stages — unconstrained at a successor stage, and pinned at a limit
stage by uniqueness of a solution.

## Main definitions

* `Stacks.Transfinite.IsGoodBelow`: a family of morphisms given below a stage is strictly
  transitive there and has the prescribed property.
* `Stacks.Transfinite.HasStep`: the step obligation, at every stage.
* `Stacks.Transfinite.column`: the recursion itself.
* `Stacks.Transfinite.ofSystem`: the functor `E ⥤ C` of a strictly transitive system.  Its value
  at `α` is `G α` *definitionally*, so no `eqToHom` is interposed between it and the family it
  was built from.

## Main results

* `Stacks.Transfinite.exists_coherentSystem_of_step`: **a strictly transitive system exists as
  soon as every stage can be filled compatibly with the stages below it.**
* `Stacks.Transfinite.exists_coherentSystem_of_step_nondegenerate`: the non-degeneracy
  certificate.  The hypotheses of that theorem are satisfiable with a conclusion in which no
  transition between distinct stages is invertible — the system of initial segments of `E` and
  their inclusions, where `τ_{β,α}` is not surjective as soon as `β < α`.

## The default morphism

The recursion is a `WellFoundedLT.fix`, so it must return a value at every stage, including the
stages at which the data handed to it is not yet known to be strictly transitive: inside the
recursion that knowledge is not available, and it is established afterwards, by transfinite
induction, out of the recursion's own unfolding equation
(`Stacks.Transfinite.isGood_column`).  The hypothesis `z` supplies the value used there.  It is
book-keeping and never appears in the conclusion: in an additive category take
`z = fun _ _ => 0`, and in `Type v` any family of constant maps will do.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Transfinite

universe w v u

/-! ### The functor of a strictly transitive system -/

/-- **The functor of a strictly transitive system of morphisms.** A family `τ` of morphisms
`G β ⟶ G α`, one for each `β ≤ α`, which is the identity at `β = α` and composes strictly, is a
functor out of the index preorder.  Its value at `α` is `G α` by definition. -/
def ofSystem {E : Type v} [Preorder E] {C : Type u} [Category.{w} C] (G : E → C)
    (τ : ∀ β α : E, β ≤ α → (G β ⟶ G α)) (hid : ∀ α : E, τ α α le_rfl = 𝟙 (G α))
    (hcomp : ∀ (β γ α : E) (h₁ : β ≤ γ) (h₂ : γ ≤ α),
      τ β γ h₁ ≫ τ γ α h₂ = τ β α (h₁.trans h₂)) :
    E ⥤ C where
  obj := G
  map {_ _} h := τ _ _ (leOfHom h)
  map_id α := hid α
  map_comp f g := (hcomp _ _ _ (leOfHom f) (leOfHom g)).symm

/-- The value of `Stacks.Transfinite.ofSystem G τ hid hcomp` at `α` is `G α`. -/
@[simp]
theorem ofSystem_obj {E : Type v} [Preorder E] {C : Type u} [Category.{w} C] (G : E → C)
    (τ : ∀ β α : E, β ≤ α → (G β ⟶ G α)) (hid : ∀ α : E, τ α α le_rfl = 𝟙 (G α))
    (hcomp : ∀ (β γ α : E) (h₁ : β ≤ γ) (h₂ : γ ≤ α),
      τ β γ h₁ ≫ τ γ α h₂ = τ β α (h₁.trans h₂)) (α : E) :
    (ofSystem G τ hid hcomp).obj α = G α :=
  rfl

/-- The functor `Stacks.Transfinite.ofSystem G τ hid hcomp` sends the morphism `h.hom : β ⟶ α`
of the preorder to `τ β α h`. -/
@[simp]
theorem ofSystem_map {E : Type v} [Preorder E] {C : Type u} [Category.{w} C] (G : E → C)
    (τ : ∀ β α : E, β ≤ α → (G β ⟶ G α)) (hid : ∀ α : E, τ α α le_rfl = 𝟙 (G α))
    (hcomp : ∀ (β γ α : E) (h₁ : β ≤ γ) (h₂ : γ ≤ α),
      τ β γ h₁ ≫ τ γ α h₂ = τ β α (h₁.trans h₂)) {β α : E} (h : β ≤ α) :
    (ofSystem G τ hid hcomp).map h.hom = τ β α h :=
  rfl

/-! ### The step obligation -/

section Recursion

variable {E : Type v} [LinearOrder E] [WellFoundedLT E] {C : Type u} [Category.{w} C]

/-- **The data already produced below a stage is strictly transitive with the property `P`.**
This is the hypothesis the step of the recursion is given at a stage `α`: morphisms `G β ⟶ G γ`
for every `β ≤ γ < α`, each with the property `P`, with identities on the diagonal and strictly
composing. -/
def IsGoodBelow {G : E → C} (P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop) {α : E}
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (G β ⟶ G γ)) : Prop :=
  (∀ (β γ : E) (h : β ≤ γ) (hγ : γ < α), P β γ h (r γ hγ β h)) ∧
    (∀ (γ : E) (hγ : γ < α), r γ hγ γ le_rfl = 𝟙 (G γ)) ∧
      ∀ (β γ δ : E) (h₁ : β ≤ γ) (h₂ : γ ≤ δ) (hδ : δ < α),
        r γ (lt_of_le_of_lt h₂ hδ) β h₁ ≫ r δ hδ γ h₂ = r δ hδ β (h₁.trans h₂)

/-- **The step obligation of the recursion.** At every stage `α`, and for every strictly
transitive system with the property `P` already given below `α`, the morphisms into `G α` from
the stages below `α` can be chosen with the property `P` and compatibly with that system. -/
def HasStep (G : E → C) (P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop) : Prop :=
  ∀ (α : E) (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (G β ⟶ G γ)), IsGoodBelow P r →
    ∃ t : ∀ β : E, β < α → (G β ⟶ G α),
      (∀ (β : E) (hβ : β < α), P β α hβ.le (t β hβ)) ∧
        ∀ (β γ : E) (h : β ≤ γ) (hγ : γ < α), r γ hγ β h ≫ t γ hγ = t β (lt_of_le_of_lt h hγ)

/-! ### The recursion -/

open scoped Classical in
/-- One step of the recursion of `Stacks.Transfinite.column`: the morphisms into `G α`, given the
ones already produced below `α`.  The step obligation applies exactly when those are strictly
transitive with the property `P`; where they are not, the default morphism is used. -/
def columnStep {G : E → C} {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop}
    (z : ∀ β α : E, G β ⟶ G α) (hstep : HasStep G P) (α : E)
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (G β ⟶ G γ)) :
    ∀ β : E, β ≤ α → (G β ⟶ G α) :=
  if h : IsGoodBelow P r then
    Function.update
      (fun β (_ : β ≤ α) => if hβ : β < α then (hstep α r h).choose β hβ else z β α) α
      fun _ => 𝟙 (G α)
  else fun β _ => z β α

/-- **The transfinite recursion**: the morphisms into `G α` from every stage `β ≤ α`. -/
def column {G : E → C} {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop}
    (z : ∀ β α : E, G β ⟶ G α) (hstep : HasStep G P) :
    ∀ α : E, ∀ β : E, β ≤ α → (G β ⟶ G α) :=
  WellFoundedLT.fix (columnStep z hstep)

/-- The system `Stacks.Transfinite.column` produces, indexed by a pair of stages. -/
def system {G : E → C} {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop}
    (z : ∀ β α : E, G β ⟶ G α) (hstep : HasStep G P) (β α : E) (h : β ≤ α) : G β ⟶ G α :=
  column z hstep α β h

/-- **The unfolding equation of the recursion.** -/
theorem column_eq {G : E → C} {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop}
    (z : ∀ β α : E, G β ⟶ G α) (hstep : HasStep G P) (α : E) :
    column z hstep α = columnStep z hstep α fun γ _ => column z hstep γ :=
  WellFoundedLT.fix_eq (columnStep z hstep) α

/-- **The unfolding equation at a stage below which the recursion has gone well.** -/
theorem column_eq_of_isGoodBelow {G : E → C}
    {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop} (z : ∀ β α : E, G β ⟶ G α)
    (hstep : HasStep G P) {α : E}
    (h : IsGoodBelow P fun γ (_ : γ < α) => column z hstep γ) :
    column z hstep α =
      Function.update
        (fun β (_ : β ≤ α) =>
          if hβ : β < α then
            (hstep α (fun γ (_ : γ < α) => column z hstep γ) h).choose β hβ
          else z β α)
        α fun _ => 𝟙 (G α) := by
  rw [column_eq]
  exact dif_pos h

/-- **The recursion is the identity on the diagonal**, at a stage below which it has gone
well. -/
theorem column_self_of_isGoodBelow {G : E → C}
    {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop} (z : ∀ β α : E, G β ⟶ G α)
    (hstep : HasStep G P) {α : E}
    (h : IsGoodBelow P fun γ (_ : γ < α) => column z hstep γ) (hα : α ≤ α) :
    column z hstep α α hα = 𝟙 (G α) := by
  rw [column_eq_of_isGoodBelow z hstep h, Function.update_self]

/-- **Below a stage below which the recursion has gone well, the recursion is the chosen
step.** -/
theorem column_of_lt_of_isGoodBelow {G : E → C}
    {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop} (z : ∀ β α : E, G β ⟶ G α)
    (hstep : HasStep G P) {α : E}
    (h : IsGoodBelow P fun γ (_ : γ < α) => column z hstep γ) {β : E} (hβ : β < α)
    (hβ' : β ≤ α) :
    column z hstep α β hβ' =
      (hstep α (fun γ (_ : γ < α) => column z hstep γ) h).choose β hβ := by
  rw [column_eq_of_isGoodBelow z hstep h, Function.update_of_ne hβ.ne, dif_pos hβ]

/-- **The recursion produces a strictly transitive system with the property `P`.** This is the
transfinite induction that supplies, at each stage, the hypothesis the step obligation was stated
with. -/
theorem isGood_column {G : E → C} {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop}
    (z : ∀ β α : E, G β ⟶ G α) (hstep : HasStep G P)
    (hid : ∀ α : E, P α α le_rfl (𝟙 (G α))) (α : E) :
    (∀ (β : E) (h : β ≤ α), P β α h (column z hstep α β h)) ∧
      (∀ hα : α ≤ α, column z hstep α α hα = 𝟙 (G α)) ∧
        ∀ (β γ : E) (h₁ : β ≤ γ) (h₂ : γ ≤ α),
          column z hstep γ β h₁ ≫ column z hstep α γ h₂ =
            column z hstep α β (h₁.trans h₂) := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    have hbelow : IsGoodBelow P fun γ (_ : γ < α) => column z hstep γ :=
      ⟨fun β γ h hγ => (ih γ hγ).1 β h, fun γ hγ => (ih γ hγ).2.1 le_rfl,
        fun β γ δ h₁ h₂ hδ => (ih δ hδ).2.2 β γ h₁ h₂⟩
    obtain ⟨hP, hcompat⟩ :=
      (hstep α (fun γ (_ : γ < α) => column z hstep γ) hbelow).choose_spec
    have hdiag : ∀ hα : α ≤ α, column z hstep α α hα = 𝟙 (G α) :=
      column_self_of_isGoodBelow z hstep hbelow
    have hlow : ∀ (β : E) (hβ : β < α) (hβ' : β ≤ α),
        column z hstep α β hβ' =
          (hstep α (fun γ (_ : γ < α) => column z hstep γ) hbelow).choose β hβ :=
      fun β hβ hβ' => column_of_lt_of_isGoodBelow z hstep hbelow hβ hβ'
    refine ⟨fun β h => ?_, hdiag, fun β γ h₁ h₂ => ?_⟩
    · rcases eq_or_lt_of_le h with rfl | hβ
      · rw [hdiag h]
        exact hid β
      · rw [hlow β hβ h]
        exact hP β hβ
    · rcases eq_or_lt_of_le h₂ with rfl | hγ
      · rw [hdiag h₂, Category.comp_id]
      · rw [hlow γ hγ h₂, hlow β (lt_of_le_of_lt h₁ hγ) (h₁.trans h₂)]
        exact hcompat β γ h₁ hγ

/-- **A strictly transitive system of morphisms exists as soon as every stage can be filled
compatibly with the stages below it.** Let `E` be a well ordered set, let `G : E → C` be a family
of objects of a category and let `P` be a property of the morphisms `G β ⟶ G α`.  Suppose that

* the identity of `G α` has the property `P` at every stage, and
* at every stage `α`, for every family of morphisms with the property `P` already defined and
  strictly transitive below `α`, the morphisms into `G α` from the stages below `α` can be chosen
  with the property `P` and compatibly with that family — which is
  `Stacks.Transfinite.HasStep`.

Then there is a family `τ_{β,α} : G β ⟶ G α`, one for every `β ≤ α`, which is the identity on the
diagonal, composes strictly, and has the property `P` throughout; equivalently, by
`Stacks.Transfinite.ofSystem`, a functor `E ⥤ C` whose value at `α` is `G α`.

The hypothesis `z` is a default morphism, needed only because the recursion must return a value
at the stages where the step obligation has not yet been shown to apply; see the section *The
default morphism* of the module documentation.  It does not weaken the statement: in an additive
category it is `fun _ _ => 0`, and the certificate
`Stacks.Transfinite.exists_coherentSystem_of_step_nondegenerate` supplies it in `Type v`. -/
theorem exists_coherentSystem_of_step {G : E → C}
    {P : ∀ β α : E, β ≤ α → (G β ⟶ G α) → Prop} (z : ∀ β α : E, G β ⟶ G α)
    (hid : ∀ α : E, P α α le_rfl (𝟙 (G α))) (hstep : HasStep G P) :
    ∃ τ : ∀ β α : E, β ≤ α → (G β ⟶ G α),
      (∀ α : E, τ α α le_rfl = 𝟙 (G α)) ∧
        (∀ (β γ α : E) (h₁ : β ≤ γ) (h₂ : γ ≤ α),
            τ β γ h₁ ≫ τ γ α h₂ = τ β α (h₁.trans h₂)) ∧
          ∀ (β α : E) (h : β ≤ α), P β α h (τ β α h) :=
  ⟨system z hstep, fun α => (isGood_column z hstep hid α).2.1 le_rfl,
    fun β γ α h₁ h₂ => (isGood_column z hstep hid α).2.2 β γ h₁ h₂,
    fun β α h => (isGood_column z hstep hid α).1 β h⟩

end Recursion

/-! ### The non-degeneracy certificate -/

section NonDegenerate

variable (E : Type v) [LinearOrder E] [WellFoundedLT E]

/-- The initial segment of `E` at a stage, as an object of `Type v`.  It is the family of objects
the certificate `Stacks.Transfinite.exists_coherentSystem_of_step_nondegenerate` runs the
recursion on. -/
abbrev segment (α : E) : Type v := {γ : E // γ ≤ α}

/-- The inclusion of one initial segment of `E` into a larger one. -/
def segmentIncl {β α : E} (h : β ≤ α) : segment E β ⟶ segment E α :=
  TypeCat.ofHom fun x => ⟨x.1, x.2.trans h⟩

omit [WellFoundedLT E] in
/-- The inclusion `segmentIncl E h` sends an element `x` of the segment at `β` to the same element
of `E`, viewed in the segment at `α`. -/
@[simp]
theorem segmentIncl_apply {β α : E} (h : β ≤ α) (x : segment E β) :
    (segmentIncl E h) x = ⟨x.1, x.2.trans h⟩ :=
  rfl

omit [WellFoundedLT E] in
/-- The inclusion of an initial segment into itself is the identity. -/
theorem segmentIncl_self (α : E) : segmentIncl E (le_refl α) = 𝟙 (segment E α) := by
  ext x
  rfl

omit [WellFoundedLT E] in
/-- The inclusions of initial segments compose strictly. -/
theorem segmentIncl_comp {β γ α : E} (h₁ : β ≤ γ) (h₂ : γ ≤ α) :
    segmentIncl E h₁ ≫ segmentIncl E h₂ = segmentIncl E (h₁.trans h₂) := by
  ext x
  rfl

/-- **The hypotheses of `Stacks.Transfinite.exists_coherentSystem_of_step` are satisfiable, with a
non-degenerate conclusion.** Run the recursion on the initial segments of `E` inside `Type v`,
with the property that a morphism *be* the inclusion.  The system produced is then the system of
inclusions, in which `τ_{β,α}` fails to be surjective — hence is not an isomorphism — as soon as
`β < α`.

This is the positive test for vacuity: the step obligation of that theorem is satisfiable, and
what it produces there is not a family of isomorphisms, so neither the hypothesis nor the
conclusion is degenerate. -/
theorem exists_coherentSystem_of_step_nondegenerate :
    ∃ τ : ∀ β α : E, β ≤ α → (segment E β ⟶ segment E α),
      (∀ α : E, τ α α le_rfl = 𝟙 (segment E α)) ∧
        (∀ (β γ α : E) (h₁ : β ≤ γ) (h₂ : γ ≤ α),
            τ β γ h₁ ≫ τ γ α h₂ = τ β α (h₁.trans h₂)) ∧
          ∀ (β α : E) (h : β ≤ α),
            α ≤ β ∨ ∃ y : segment E α, ∀ x : segment E β, (τ β α h) x ≠ y := by
  obtain ⟨τ, hdiag, hcomp, hP⟩ :=
    exists_coherentSystem_of_step (G := segment E)
      (P := fun _ _ h t => t = segmentIncl E h)
      (fun _ α => TypeCat.ofHom fun _ => ⟨α, le_rfl⟩)
      (fun α => (segmentIncl_self E α).symm)
      fun _ r hr => ⟨fun _ hβ => segmentIncl E hβ.le, fun _ _ => rfl, fun β γ h hγ => by
        rw [hr.1 β γ h hγ]
        exact segmentIncl_comp E h hγ.le⟩
  refine ⟨τ, hdiag, hcomp, fun β α h => ?_⟩
  rcases le_or_gt α β with hαβ | hβα
  · exact Or.inl hαβ
  · refine Or.inr ⟨⟨α, le_rfl⟩, fun x hx => ?_⟩
    rw [hP β α h] at hx
    have hx1 : x.1 = α := Subtype.ext_iff.1 hx
    exact absurd (hx1 ▸ x.2) (not_le.2 hβα)

end NonDegenerate

end Stacks.Transfinite

end

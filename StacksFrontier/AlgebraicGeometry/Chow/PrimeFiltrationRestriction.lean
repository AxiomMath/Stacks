module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GoodSequenceColength

/-!
# Restricting a filtration with prime quotients to a submodule

A sequence in a module whose successive quotients are copies of `R / q` and all of whose terms
lie in a submodule `P` is a sequence in `P` with the same successive quotients: an injective
linear map identifies each subquotient of the spans of initial segments with the corresponding
subquotient downstairs.

## Main results

* `Module.FiniteLength.map_submoduleOf_equivMapOfInjective`: an injective linear map carries the
  copy of `B` inside `A` onto the copy of `B.map f` inside `A.map f`.
* `Module.FiniteLength.subquotEquivOfMapEq`: an injective linear map identifies a subquotient
  with its image.
* `Module.FiniteLength.primeFiltration_restrict`: the filtration hypothesis of Tags 02QB and
  02QC descends to a submodule containing the terms of the sequence.

## Implementation notes

The filtration hypothesis is the one used throughout this development: for each index the
quotient of `spanBefore x i ⊔ R ∙ x i` by `spanBefore x i` is isomorphic to `R / q`. Restricting
it needs the two spans of a prefix upstairs to be the images of the spans downstairs, which is
`Module.FiniteLength.spanBefore_comp` for the first and the same together with
`Submodule.map_span` for the second. Together with Mathlib's
`Submodule.span_range_subtype_eq_top_iff` for the spanning half, this supplies the hypotheses of
Tag 02QB for the inclusion of one span of such a sequence into another.

## References

* [Stacks Project, Tag 02QB](https://stacks.math.columbia.edu/tag/02QB)
* [Stacks Project, Tag 02QC](https://stacks.math.columbia.edu/tag/02QC)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v w

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An injective linear map carries the copy of `B` inside `A` onto the copy of `B.map f`
inside `A.map f`. -/
theorem map_submoduleOf_equivMapOfInjective (f : M →ₗ[R] N)
    (hf : Function.Injective f) {B A : Submodule R M} (hBA : B ≤ A) :
    (B.submoduleOf A).map (Submodule.equivMapOfInjective f hf A).toLinearMap =
      (B.map f).submoduleOf (A.map f) := by
  ext z
  simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
    Submodule.subtype_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Submodule.coe_equivMapOfInjective_apply]
    exact Submodule.mem_map_of_mem hw
  · rintro ⟨b, hb, hbz⟩
    exact ⟨⟨b, hBA hb⟩, hb, Subtype.ext (by rwa [Submodule.coe_equivMapOfInjective_apply])⟩

/-- An injective linear map identifies the subquotient `A / B` with the subquotient cut out by
the images of `A` and `B`, presented as any pair of submodules equal to them. -/
def subquotEquivOfMapEq (f : M →ₗ[R] N) (hf : Function.Injective f)
    {B A : Submodule R M} (hBA : B ≤ A) {A₂ B₂ : Submodule R N}
    (hA : A.map f = A₂) (hB : B.map f = B₂) :
    (↥A ⧸ B.submoduleOf A) ≃ₗ[R] (↥A₂ ⧸ B₂.submoduleOf A₂) := by
  subst hA hB
  exact Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf A)
    (map_submoduleOf_equivMapOfInjective f hf hBA)

/-- A sequence whose successive quotients are copies of `R / q` and whose terms all lie in a
submodule `P` has the same successive quotients when read as a sequence in `P`. -/
theorem primeFiltration_restrict (P : Submodule R M) {l : ℕ} (q : Ideal R)
    (x : Fin l → M) (hx : ∀ i, x i ∈ P)
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q)) :
    ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) (fun j ↦ (⟨x j, hx j⟩ : ↥P)) i ⊔
              R ∙ (⟨x i, hx i⟩ : ↥P) : Submodule R ↥P) ⧸
            (spanBefore (R := R) (fun j ↦ (⟨x j, hx j⟩ : ↥P)) i).comap
              (spanBefore (R := R) (fun j ↦ (⟨x j, hx j⟩ : ↥P)) i ⊔
                R ∙ (⟨x i, hx i⟩ : ↥P) : Submodule R ↥P).subtype) ≃ₗ[R]
          R ⧸ q) := by
  intro i
  set xP : Fin l → ↥P := fun j ↦ (⟨x j, hx j⟩ : ↥P)
  have hB : (spanBefore (R := R) xP i).map P.subtype = spanBefore (R := R) x i := by
    rw [← show P.subtype ∘ xP = x from rfl, spanBefore_comp]
  have hA : (spanBefore (R := R) xP i ⊔ R ∙ xP i : Submodule R ↥P).map P.subtype =
      (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) := by
    rw [Submodule.map_sup, hB, Submodule.map_span, Set.image_singleton]
    rfl
  exact ⟨(subquotEquivOfMapEq P.subtype (Submodule.injective_subtype P) le_sup_left
    hA hB).trans (hxf i).some⟩

end Module.FiniteLength

end

end

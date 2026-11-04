module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite morphisms out of a finite coproduct

A morphism induced from a finite family of finite morphisms with a common target is finite.

## Main results

* `AlgebraicGeometry.isFinite_sigmaDesc`: the morphism from a finite coproduct induced by finite
  morphisms is finite.

## Implementation notes

The finite disjoint union is expressed as the categorical coproduct of a family of schemes, and
its induced morphism as `CategoryTheory.Limits.Sigma.desc`. The statement also covers the empty
finite family, whose induced morphism is finite.

## References

* [Stacks Project, Tag 0CYI](https://stacks.math.columbia.edu/tag/0CYI)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The coproduct over `Option ι` splits off the component at `none`. -/
private noncomputable def sigmaOptionIso {ι : Type v} [Finite ι]
    (Y : Option ι → AlgebraicGeometry.Scheme.{u}) :
    (∐ Y) ≅ Y none ⨿ (∐ fun i ↦ Y (some i)) where
  hom := Limits.Sigma.desc (Option.rec Limits.coprod.inl
    (fun i ↦ Limits.Sigma.ι (fun i ↦ Y (some i)) i ≫ Limits.coprod.inr))
  inv := Limits.coprod.desc (Limits.Sigma.ι Y none)
    (Limits.Sigma.desc fun i ↦ Limits.Sigma.ι Y (some i))
  hom_inv_id := by
    ext i
    cases i with
    | none => simp only [← Category.assoc, Limits.Sigma.ι_desc, Limits.coprod.inl_desc,
        Category.comp_id]
    | some i =>
      rw [Limits.Sigma.ι_desc_assoc, Category.assoc, Limits.coprod.inr_desc,
        Limits.Sigma.ι_desc, Category.comp_id]
  inv_hom_id := by
    apply Limits.coprod.hom_ext
    · simp only [← Category.assoc, Limits.coprod.inl_desc, Limits.Sigma.ι_desc, Category.comp_id]
    · simp only [← Category.assoc, Limits.coprod.inr_desc]
      ext i
      simp only [← Category.assoc, Limits.Sigma.ι_desc, Category.comp_id]

/-- A morphism from a finite coproduct of schemes is finite when its restriction to every
component is finite. -/
@[stacks 0CYI]
instance isFinite_sigmaDesc {ι : Type v} [Finite ι]
    {X : AlgebraicGeometry.Scheme.{u}} {Y : ι → AlgebraicGeometry.Scheme.{u}}
    {f : ∀ i, Y i ⟶ X} [∀ i, AlgebraicGeometry.IsFinite (f i)] :
    AlgebraicGeometry.IsFinite (Limits.Sigma.desc f) := by
  revert X Y f
  let P : Type v → Prop := fun ι ↦ ∀ (hι : Finite ι),
    letI : Finite ι := hι
    (∀ {X : AlgebraicGeometry.Scheme.{u}} {Y : ι → AlgebraicGeometry.Scheme.{u}}
      {f : ∀ i, Y i ⟶ X} [∀ i, AlgebraicGeometry.IsFinite (f i)],
      AlgebraicGeometry.IsFinite (Limits.Sigma.desc f))
  have hp : P ι := by
    apply Finite.induction_empty_option (P := P)
    · intro ι κ e ih hκ X Y f h
      let hι : Finite ι := @Finite.of_injective ι κ hκ e e.injective
      let E := Limits.Sigma.reindex e Y
      have hf' := ih hι (Y := Y ∘ e) (f := fun i ↦ f (e i))
      have heq : E.inv ≫ Limits.Sigma.desc (fun i ↦ f (e i)) = Limits.Sigma.desc f := by
        ext i
        rw [← e.apply_symm_apply i, Limits.Sigma.ι_reindex_inv_assoc, Limits.Sigma.ι_desc]
        simp
      rw [← heq]
      infer_instance
    · intro hι X Y f h
      have : IsEmpty (∐ Y : AlgebraicGeometry.Scheme.{u}) :=
        ⟨fun x ↦ isEmptyElim ((Limits.Sigma.desc fun i ↦ i.elim :
          (∐ Y) ⟶ (∅ : AlgebraicGeometry.Scheme.{u})).base x)⟩
      infer_instance
    · intro ι hι ih hOption X Y f h
      have hf' := ih (Finite.of_fintype ι)
        (Y := fun i ↦ Y (some i)) (f := fun i ↦ f (some i))
      have heq : (sigmaOptionIso Y).hom ≫
          Limits.coprod.desc (f none) (Limits.Sigma.desc fun i ↦ f (some i)) =
          Limits.Sigma.desc f := by
        ext i
        cases i with
        | none => simp only [← Category.assoc, sigmaOptionIso, Limits.Sigma.ι_desc,
            Limits.coprod.inl_desc]
        | some i =>
          dsimp only [sigmaOptionIso]
          rw [← Category.assoc, Limits.Sigma.ι_desc, Category.assoc, Limits.coprod.inr_desc,
            Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      rw [← heq]
      infer_instance
  exact fun _ _ _ _ ↦ hp inferInstance

end AlgebraicGeometry

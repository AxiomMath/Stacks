module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# Relocalizing twice (Stacks 03EH)

Let `b : A' ⟶ A` and `a : A ⟶ X` be morphisms of a category `C`. Stacks 03EH records that the
localization functors compose, `j_{A'!} = j_{A!} ∘ j_!`; at the level of presheaves the two
functors `CategoryTheory.OverShriek.relocalizePresheafFunctor` attached to `b` and to `a`
compose to the one attached to `b ≫ a`, because a section of `Λ_a (Λ_b F)` over `W` is a
factorization `χ : W.left ⟶ A` of the structure morphism of `W` together with a factorization
`ψ : W.left ⟶ A'` of `χ` and a section of `F` over `(W.left, ψ)` — and `χ` is determined by `ψ`.

The same computation identifies `Λ_a` of the representable presheaf of `(A' ⟶ A)` with the
representable presheaf of `(A' ⟶ X)`, and under both identifications the two structural
morphisms `CategoryTheory.OverShriek.relocalizeToYoneda` agree.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeCompIso`: relocalizing along `b` and then along `a` is
  relocalizing along `b ≫ a`.
* `CategoryTheory.OverShriek.relocalizeYonedaComp`: the representable comparison that goes with
  it.
* `CategoryTheory.OverShriek.relocalizePresheafFunctorIdIso`: relocalizing along an identity is
  the identity functor.

## Main results

* `CategoryTheory.OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp`: the structural
  morphism of `Λ_{b ≫ a} F` is the image under `Λ_a` of the structural morphism of `Λ_b F`, read
  through the two comparisons. This is what transports a property of the structural morphism of
  an algebraic space over `A'` from one base to a larger one.

## Implementation notes

Both comparisons are built from the explicit description of a section of a relocalization as a
`CategoryTheory.OverShriek.relocalizeMk`, so that the two structural morphisms agree by `rfl`
once the comparisons are in place.

The two round trips need the factorization carried by a section to be substituted for the
factorization recorded one level up. That substitution is not available by `subst`: the
factorization occurs in the *type* of the section it is read off, so the occurs check fails. The
sections of a relocalization are a subtype of a sigma type whose ambient type does not depend on
the factorization, so `Sigma.subtype_ext` performs the substitution instead; for the
representable comparison, where the second component is a morphism of a slice rather than a
subtype, `CategoryTheory.OverShriek.overSlice_sigma_ext` does it with the factorization
generalized first.

## References

* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {X A A' : C} (b : A' ⟶ A) (a : A ⟶ X)

/-- Two sections of a slice over `A` indexed by their own structure morphisms agree as soon as
those structure morphisms do and the underlying morphisms agree. The structure morphism is
generalized, which is what makes the substitution available. -/
theorem overSlice_sigma_ext {L : C} {χ χ' : L ⟶ A} (e : χ' = χ)
    (t : (Over.mk χ : Over A) ⟶ Over.mk b) (t' : (Over.mk χ' : Over A) ⟶ Over.mk b)
    (hl : t'.left = t.left) :
    (⟨χ', t'⟩ : Σ ξ : L ⟶ A, ((Over.mk ξ : Over A) ⟶ Over.mk b)) = ⟨χ, t⟩ := by
  subst e
  exact congrArg _ (Over.OverMorphism.ext hl)

/-- **Relocalizing along `b` and then along `a` is relocalizing along `b ≫ a`.** A section of
`Λ_a (Λ_b F)` over `W` carries a factorization of the structure morphism of `W` through `A` and a
factorization of *that* through `A'`; the first is the second followed by `b`, so the section is
determined by the factorization through `A'` and the section of `F` it carries. -/
def relocalizeCompIso (F : (Over A')ᵒᵖ ⥤ Type v) :
    (relocalizePresheafFunctor a).obj ((relocalizePresheafFunctor b).obj F) ≅
      (relocalizePresheafFunctor (b ≫ a)).obj F :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun x =>
        relocalizeMk (W := W) (b ≫ a) F x.1.2.1.1 x.1.2.1.2 (by
          have hy : x.1.2.1.1 ≫ b = x.1.1 := relocalizeFactors b F x.1.2
          have hz : x.1.1 ≫ a = (unop W).hom :=
            relocalizeFactors a ((relocalizePresheafFunctor b).obj F) x
          rw [← Category.assoc, hy]
          exact hz)
      invFun := fun y =>
        relocalizeMk (W := W) a ((relocalizePresheafFunctor b).obj F) (y.1.1 ≫ b)
          (relocalizeMk (W := op (Over.mk (y.1.1 ≫ b))) b F y.1.1 y.1.2 rfl) (by
            have hy : y.1.1 ≫ b ≫ a = (unop W).hom := relocalizeFactors (b ≫ a) F y
            rw [Category.assoc]
            exact hy)
      left_inv := by
        intro x
        have hw : x.1.2.1.1 ≫ b = x.1.1 := relocalizeFactors b F x.1.2
        apply Subtype.ext
        refine Sigma.subtype_ext (x₀ := ⟨x.1.2.1.1 ≫ b, ⟨x.1.2.1, rfl⟩⟩) (x₁ := x.1) hw ?_
        rfl
      right_inv := fun _ => rfl })
    (by intro W W' f; ext x; rfl)

/-- `Λ_a` of the representable presheaf of `(A' ⟶ A)` is the representable presheaf of
`(A' ⟶ X)`: a section of the former over `W` is a factorization of the structure morphism of `W`
through `A` together with a morphism of the slice over `A` from it to `b`, which is exactly a
morphism `W ⟶ (A' ⟶ X)`. -/
def relocalizeYonedaComp :
    yoneda.obj (Over.mk (b ≫ a)) ≅
      (relocalizePresheafFunctor a).obj (yoneda.obj (Over.mk b)) :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun k =>
        relocalizeMk (W := W) a (yoneda.obj (Over.mk b)) (k.left ≫ b)
          (Over.homMk k.left rfl) (by
            have hk : k.left ≫ b ≫ a = (unop W).hom := Over.w k
            rw [Category.assoc]
            exact hk)
      invFun := fun x => Over.homMk x.1.2.left (by
        have hw : x.1.2.left ≫ b = x.1.1 := Over.w x.1.2
        have hx : x.1.1 ≫ a = (unop W).hom :=
          relocalizeFactors a (yoneda.obj (Over.mk b)) x
        have hgoal : x.1.2.left ≫ b ≫ a = (unop W).hom := by
          rw [← Category.assoc, hw]
          exact hx
        exact hgoal)
      left_inv := fun _ => Over.OverMorphism.ext rfl
      right_inv := fun x =>
        Subtype.ext (overSlice_sigma_ext b (Over.w x.1.2) x.1.2 _ rfl) })
    (by
      intro W W' f
      ext k
      refine Subtype.ext (overSlice_sigma_ext b (Category.assoc _ _ _) _ _ ?_)
      rfl)

/-- **The structural morphisms agree across the two comparisons.** Read through
`CategoryTheory.OverShriek.relocalizeCompIso` and
`CategoryTheory.OverShriek.relocalizeYonedaComp`, the structural morphism of `Λ_{b ≫ a} F` is the
image under `Λ_a` of the structural morphism of `Λ_b F`: both read off the factorization through
`A'` that a section carries. -/
theorem relocalizeToYoneda_comp_relocalizeYonedaComp (F : (Over A')ᵒᵖ ⥤ Type v) :
    relocalizeToYoneda (b ≫ a) F ≫ (relocalizeYonedaComp b a).hom =
      (relocalizeCompIso b a F).inv ≫
        (relocalizePresheafFunctor a).map (relocalizeToYoneda b F) := by
  ext W y
  rfl

/-- **Relocalizing along an identity is the identity functor.** The left adjoint of restriction
along `Over.map (𝟙 A)` is a left adjoint of the identity functor, restriction along
`Over.map (𝟙 A)` being isomorphic to the identity through `CategoryTheory.Over.mapId`. -/
noncomputable def relocalizePresheafFunctorIdIso (A : C) :
    relocalizePresheafFunctor (𝟙 A) ≅ 𝟭 ((Over A)ᵒᵖ ⥤ Type v) :=
  (relocalizeAdjunction (𝟙 A)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      ((Functor.whiskeringLeft (Over A)ᵒᵖ (Over A)ᵒᵖ (Type v)).mapIso
        (NatIso.op (Over.mapId A))))

end CategoryTheory.OverShriek

end

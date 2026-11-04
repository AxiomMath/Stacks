module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# A left adjoint is a coproduct when its right adjoint is a product

Let `L ⊣ R` and `L i ⊣ R i` for `i` in an index type, all between the same two categories, and
let `β i : R ⟶ R i` be a family of natural transformations. If for every object `T` the family
`β i` exhibits `R.obj T` as the product of the `(R i).obj T`, then the conjugate transformations
`L i ⟶ L` exhibit `L` as the coproduct of the `L i`.

This is the step that turns a formula for a right adjoint into the corresponding formula for the
left adjoint. The whole content is the single computation `homEquiv_conjugateInj`, which says
that transposing along `L i ⊣ R i` after precomposing with the conjugate of `β i` is the same as
transposing along `L ⊣ R` and then postcomposing with `β i`; it discharges both the existence and
the uniqueness half of the universal property of the coproduct.

## Main definitions

* `CategoryTheory.Adjunction.conjugateInj`: the conjugate `L i ⟶ L` of `β i`, i.e. the image of
  `β i` under `CategoryTheory.conjugateEquiv`.

## Main results

* `CategoryTheory.Adjunction.homEquiv_conjugateInj`: the transposition formula.
* `CategoryTheory.Adjunction.isColimitCofanObjOfIsLimitFan`: at each object, `L.obj X` with the
  components of the conjugates is a coproduct of the `(L i).obj X`.
* `CategoryTheory.Adjunction.isColimitCofanOfIsLimitFan`: hence `L` with the conjugates is a
  coproduct of the `L i` in the functor category.
* `CategoryTheory.Adjunction.coproductIsoOfIsLimitFan`: hence `∐ L ≅ L`, when the coproduct of
  the family exists.

## Implementation notes

The product hypothesis is phrased as `IsLimit (Fan.mk (R.obj T) fun i => (β i).app T)` for every
`T` rather than as an isomorphism `R ≅ ∏ᶜ R i`, because that is the form in which it arises: one
proves it pointwise on sections and transports it up through the evaluation functors, and an
isomorphism with a chosen product would have to be built and then discarded again.

Colimits in a functor category are computed pointwise, but the two diagrams
`Discrete.functor L ⋙ (evaluation _ _).obj X` and `Discrete.functor fun i => (L i).obj X` are
only isomorphic and not definitionally equal — their actions on the morphisms of the discrete
index category differ — so passing from the pointwise statement to the functor-category one goes
through `CategoryTheory.Limits.IsColimit.equivOfNatIsoOfIso` rather than
`IsColimit.ofIsoColimit`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe w v₁ u₁ v₂ u₂

variable {I : Type w} {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} {L' : I → (C ⥤ D)} {R' : I → (D ⥤ C)}
  (adjL : L ⊣ R) (adj' : ∀ i, L' i ⊣ R' i) (β : ∀ i, R ⟶ R' i)

/-- The conjugate `L' i ⟶ L` of a natural transformation `β i : R ⟶ R' i` of right adjoints. -/
noncomputable def conjugateInj (i : I) : L' i ⟶ L :=
  (conjugateEquiv adjL (adj' i)).symm (β i)

/-- Transposing along `L' i ⊣ R' i` after precomposing with the conjugate of `β i` is the same as
transposing along `L ⊣ R` and then postcomposing with `β i`. -/
lemma homEquiv_conjugateInj (i : I) {X : C} {T : D} (f : L.obj X ⟶ T) :
    (adj' i).homEquiv X T ((conjugateInj adjL adj' β i).app X ≫ f) =
      adjL.homEquiv X T f ≫ (β i).app T := by
  dsimp only [conjugateInj]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm adjL (adj' i) (β i) X, Category.assoc,
    ← (β i).naturality f, ← Category.assoc]

variable (hβ : ∀ T : D, IsLimit (Fan.mk (R.obj T) fun i => (β i).app T))

/-- If the right adjoint is, at every object, the product of the `R' i`, then at every object the
left adjoint is the coproduct of the `L' i`, with the components of the conjugates as
injections. -/
noncomputable def isColimitCofanObjOfIsLimitFan (X : C) :
    IsColimit (Cofan.mk (L.obj X) fun i => (conjugateInj adjL adj' β i).app X) := by
  refine Cofan.IsColimit.mk _ (fun t => (adjL.homEquiv X t.pt).symm
      ((hβ t.pt).lift (Fan.mk X fun i => (adj' i).homEquiv X t.pt (t.inj i))))
    (fun t i => ?_) (fun t m hm => ?_)
  · refine ((adj' i).homEquiv X t.pt).injective ?_
    rw [show (Cofan.mk (L.obj X) fun i => (conjugateInj adjL adj' β i).app X).inj i =
        (conjugateInj adjL adj' β i).app X from rfl,
      homEquiv_conjugateInj adjL adj' β i, Equiv.apply_symm_apply]
    exact (hβ t.pt).fac (Fan.mk X fun i => (adj' i).homEquiv X t.pt (t.inj i)) ⟨i⟩
  · refine (adjL.homEquiv X t.pt).injective ?_
    rw [Equiv.apply_symm_apply]
    refine (hβ t.pt).hom_ext fun i => ?_
    obtain ⟨i⟩ := i
    simp only [cofan_mk_inj] at hm
    rw [(hβ t.pt).fac]
    exact ((homEquiv_conjugateInj adjL adj' β i m).symm.trans
      (congrArg ((adj' i).homEquiv X t.pt) (hm i)))

/-- If the right adjoint is, at every object, the product of the `R' i`, then the left adjoint is
the coproduct of the `L' i` in the functor category, with the conjugates as injections. -/
noncomputable def isColimitCofanOfIsLimitFan :
    IsColimit (Cofan.mk L fun i => conjugateInj adjL adj' β i) := by
  refine evaluationJointlyReflectsColimits _ fun X => ?_
  refine (IsColimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        (Discrete.functor fun i => (L' i).obj X) ≅
          Discrete.functor L' ⋙ (evaluation C D).obj X))
    (Cofan.mk (L.obj X) fun i => (conjugateInj adjL adj' β i).app X)
    (((evaluation C D).obj X).mapCocone (Cofan.mk L fun i => conjugateInj adjL adj' β i))
    (Cocone.ext (Iso.refl _) ?_)) (isColimitCofanObjOfIsLimitFan adjL adj' β hβ X)
  intro j
  obtain ⟨j⟩ := j
  simp

/-- If the right adjoint is, at every object, the product of the `R' i`, then the left adjoint is
the coproduct of the `L' i`. -/
noncomputable def coproductIsoOfIsLimitFan [HasCoproduct L'] : (∐ L') ≅ L :=
  colimit.isoColimitCocone ⟨_, isColimitCofanOfIsLimitFan adjL adj' β hβ⟩

end CategoryTheory.Adjunction

end

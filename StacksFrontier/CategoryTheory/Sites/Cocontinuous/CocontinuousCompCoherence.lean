module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Coherence of the right Kan extension compositor

For a functor `u : C ⥤ D` between small categories, `u.op.ran` is the direct image on
presheaves of the morphism of topoi attached to a cocontinuous `u` (Stacks 00XO), and
`ranOpCompIso u v : (u.op ⋙ v.op).ran ≅ u.op.ran ⋙ v.op.ran` is the canonical compositor
of Stacks 03L5.  This file proves that the compositor is *coherent*: it satisfies the cocycle
law and the two unit laws, i.e. the assignment `u ↦ u.op.ran` together with `ranOpCompIso` is
a pseudofunctor.

The proofs are a formal consequence of the way the compositor is built.  All these isomorphisms
are instances of `CategoryTheory.Adjunction.rightAdjointUniq`, the comparison of two right
adjoints of one functor, and on the *left* adjoints — precomposition
`(whiskeringLeft _ _ _).obj u.op` — there is nothing to compare: precomposition along a
composite *is* the composite of the precompositions, and precomposition along an identity *is*
the identity.  The mates calculus of `Mathlib.CategoryTheory.Adjunction.Mates` turns that
strictness into the three coherences, through `CategoryTheory.conjugateEquiv_associator_hom`,
`CategoryTheory.conjugateEquiv_leftUnitor_hom` and
`CategoryTheory.conjugateEquiv_rightUnitor_hom`.

## Main results

* `CategoryTheory.Adjunction.whiskerLeft_rightAdjointUniq_hom`,
  `CategoryTheory.Adjunction.whiskerRight_rightAdjointUniq_hom`: whiskering a comparison of
  right adjoints is the comparison of the composed adjunctions.
* `CategoryTheory.Adjunction.rightAdjointUniq_comp_assoc_hom`,
  `CategoryTheory.Adjunction.rightAdjointUniq_comp_id_hom`,
  `CategoryTheory.Adjunction.rightAdjointUniq_id_comp_hom`: the comparison of right adjoints
  attached to the associativity and unit isomorphisms of `Adjunction.comp` is the identity.
* `ranOpCompIso_assoc`: the cocycle law for the compositor.
* `ranOpCompIso_id_left`, `ranOpCompIso_id_right`: the two unit laws for the compositor.

## References

* [Stacks Project, Tag 03L5](https://stacks.math.columbia.edu/tag/03L5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Adjunction

universe u

namespace CategoryTheory.Adjunction

/-- The comparison of two right adjoints of one functor is the conjugate of the identity
transformation of that functor. -/
public theorem rightAdjointUniq_hom_eq_conjugateEquiv {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L ⊣ R') :
    (rightAdjointUniq adj adj').hom = conjugateEquiv adj adj' (𝟙 L) := rfl

/-- Whiskering a comparison of right adjoints on the right by a right adjoint `R` is the
comparison of the right adjoints of the two adjunctions composed with `adj`. -/
public theorem whiskerRight_rightAdjointUniq_hom {A B E : Type*} [Category A] [Category B]
    [Category E] {L₁ : B ⥤ E} {R₁ R₂ : E ⥤ B} {L : A ⥤ B} {R : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₁ ⊣ R₂) (adj : L ⊣ R) :
    Functor.whiskerRight (rightAdjointUniq adj₁ adj₂).hom R =
      (rightAdjointUniq (adj.comp adj₁) (adj.comp adj₂)).hom := by
  rw [rightAdjointUniq_hom_eq_conjugateEquiv, rightAdjointUniq_hom_eq_conjugateEquiv,
    ← conjugateEquiv_whiskerLeft adj₁ adj₂ adj (𝟙 L₁)]
  congr 1

/-- Whiskering a comparison of right adjoints on the left by a right adjoint `R` is the
comparison of the right adjoints of the two adjunctions composed with `adj`. -/
public theorem whiskerLeft_rightAdjointUniq_hom {A B E : Type*} [Category A] [Category B]
    [Category E] {L₁ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ E} {R : E ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₁ ⊣ R₂) (adj : L ⊣ R) :
    Functor.whiskerLeft R (rightAdjointUniq adj₁ adj₂).hom =
      (rightAdjointUniq (adj₁.comp adj) (adj₂.comp adj)).hom := by
  rw [rightAdjointUniq_hom_eq_conjugateEquiv, rightAdjointUniq_hom_eq_conjugateEquiv,
    ← conjugateEquiv_whiskerRight adj₁ adj₂ adj (𝟙 L₁)]
  congr 1
  simp

/-- Composition of adjunctions is associative on the nose on the underlying functors, so the
comparison of the right adjoints of its two bracketings is the identity. -/
public theorem rightAdjointUniq_comp_assoc_hom {A B E F : Type*} [Category A] [Category B]
    [Category E] [Category F] {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ E} {R₂₁ : E ⥤ B}
    {L₂₃ : E ⥤ F} {R₃₂ : F ⥤ E} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) :
    (rightAdjointUniq (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)).hom
      = 𝟙 _ :=
  conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃

/-- The comparison of `R` with the right adjoint of `adj.comp Adjunction.id` is the
identity. -/
public theorem rightAdjointUniq_comp_id_hom {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    (rightAdjointUniq adj (adj.comp Adjunction.id)).hom = 𝟙 _ :=
  conjugateEquiv_rightUnitor_hom adj

/-- The comparison of `R` with the right adjoint of `Adjunction.id.comp adj` is the
identity. -/
public theorem rightAdjointUniq_id_comp_hom {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    (rightAdjointUniq adj (Adjunction.id.comp adj)).hom = 𝟙 _ :=
  conjugateEquiv_leftUnitor_hom adj

end CategoryTheory.Adjunction

/-- The opposite of a composition of functors is the composition of the opposites. -/
public theorem CategoryTheory.Functor.op_comp_eq {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).op = F.op ⋙ G.op := rfl

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {E : Type u} [SmallCategory E] {F : Type u} [SmallCategory F]

/-- The cocycle law for the right Kan extension compositor of Stacks 03L5: the two ways of
comparing the right Kan extension along `u ⋙ v ⋙ w` with the composition of the three right
Kan extensions agree. -/
public theorem ranOpCompIso_assoc (u : C ⥤ D) (v : D ⥤ E) (w : E ⥤ F) :
    (ranOpCompIso u (v ⋙ w)).hom ≫ Functor.whiskerLeft u.op.ran (ranOpCompIso v w).hom =
      (ranOpCompIso (u ⋙ v) w).hom ≫
        Functor.whiskerRight (ranOpCompIso u v).hom w.op.ran := by
  rw [ranOpCompIso_def, ranOpCompIso_def, ranOpCompIso_def, ranOpCompIso_def]
  simp only [Functor.op_comp_eq]
  rw [whiskerLeft_rightAdjointUniq_hom ((v.op ⋙ w.op).ranAdjunction (Type u))
      ((w.op.ranAdjunction (Type u)).comp (v.op.ranAdjunction (Type u)))
      (u.op.ranAdjunction (Type u)),
    whiskerRight_rightAdjointUniq_hom ((u.op ⋙ v.op).ranAdjunction (Type u))
      ((v.op.ranAdjunction (Type u)).comp (u.op.ranAdjunction (Type u)))
      (w.op.ranAdjunction (Type u)),
    rightAdjointUniq_trans, rightAdjointUniq_trans,
    ← rightAdjointUniq_trans ((u.op ⋙ v.op ⋙ w.op).ranAdjunction (Type u))
      ((w.op.ranAdjunction (Type u)).comp
        ((v.op.ranAdjunction (Type u)).comp (u.op.ranAdjunction (Type u))))
      (((w.op.ranAdjunction (Type u)).comp (v.op.ranAdjunction (Type u))).comp
        (u.op.ranAdjunction (Type u))),
    rightAdjointUniq_comp_assoc_hom, Category.comp_id]
  rfl

/-- The left unit law for the right Kan extension compositor of Stacks 03L5: the compositor at
`𝟭 ≫ f`, followed by the identification of the right Kan extension along the identity with the
identity functor, is the identity. -/
public theorem ranOpCompIso_id_left (f : C ⥤ D) :
    (ranOpCompIso (𝟭 C) f).hom ≫
        Functor.whiskerRight
          (Adjunction.rightAdjointUniq ((𝟭 C).op.ranAdjunction (Type u)) Adjunction.id).hom
          f.op.ran =
      𝟙 f.op.ran := by
  rw [ranOpCompIso_def,
    whiskerRight_rightAdjointUniq_hom ((𝟭 C).op.ranAdjunction (Type u)) Adjunction.id
      (f.op.ranAdjunction (Type u)),
    rightAdjointUniq_trans]
  exact rightAdjointUniq_comp_id_hom (f.op.ranAdjunction (Type u))

/-- The right unit law for the right Kan extension compositor of Stacks 03L5: the compositor at
`f ≫ 𝟭`, followed by the identification of the right Kan extension along the identity with the
identity functor, is the identity. -/
public theorem ranOpCompIso_id_right (f : C ⥤ D) :
    (ranOpCompIso f (𝟭 D)).hom ≫
        Functor.whiskerLeft f.op.ran
          (Adjunction.rightAdjointUniq ((𝟭 D).op.ranAdjunction (Type u)) Adjunction.id).hom =
      𝟙 f.op.ran := by
  rw [ranOpCompIso_def,
    whiskerLeft_rightAdjointUniq_hom ((𝟭 D).op.ranAdjunction (Type u)) Adjunction.id
      (f.op.ranAdjunction (Type u)),
    rightAdjointUniq_trans]
  exact rightAdjointUniq_id_comp_hom (f.op.ranAdjunction (Type u))

end

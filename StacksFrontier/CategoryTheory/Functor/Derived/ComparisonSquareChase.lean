module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Plumbing for a chase of comparison squares

`StacksFrontier/AlgebraicGeometry/AffinePullbackComparisonComp.lean` performs the chase that compares
the composite of two base change squares with the square of the composite, on variables
(`StacksDraft.ComparisonSquare.comp_app`).  This file collects the remaining purely formal steps
that the *derived* instance of that chase needs, again on variables: five rearrangements of
composites in an arbitrary category, and the identification of the comparison isomorphism of
`CategoryTheory.Functor.mapHomotopyCategory` with the degreewise one.

Everything here is stated for arbitrary categories and functors on purpose.  At the concrete data
of a derived base change square — three algebraic spaces, three rings and two presentations of each
derived category — the `isDefEq` check a `rw` performs on such a goal exhausts the heartbeat
budget, while at the general spelling every type is a variable and no such check arises.  The same
reason is recorded at greater length in the implementation notes of
`StacksFrontier/AlgebraicGeometry/AffinePullbackComparisonComp.lean`.

## Main results

* `StacksDraft.ComparisonSquare.comp_split_right`: two factorisations of a composite, glued along
  a shared middle term.
* `StacksDraft.ComparisonSquare.map_hom_inv_id_app`: a functor carries a component of an
  isomorphism of functors to an isomorphism.
* `StacksDraft.ComparisonSquare.inv_comp_eq_of_comp_eq`: a commuting square transposed along the
  inverses of two of its sides.
* `StacksDraft.ComparisonSquare.comp_cancel_right` and
  `StacksDraft.ComparisonSquare.comp_cancel_right'`: a factorisation through the inverse of an
  isomorphism, read forwards.
* `StacksDraft.ComparisonSquare.comp_four_map` and
  `StacksDraft.ComparisonSquare.comp_four_map_of_eq`: a composite of four morphisms in the image
  of a functor.
* `StacksDraft.ComparisonSquare.hom_app_congr`: equal isomorphisms of functors have equal
  components.
* `StacksDraft.ComparisonSquare.associator_inv_comp_whiskerRight_app`: the comparison datum of a
  left derived functor of a composite, evaluated at an object.
* `StacksDraft.ComparisonSquare.factorIso_inv_app_quotient`: the same, with a renaming along an
  equality of indices appended on both sides.
* `StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient`: the comparison
  `F^K ⋙ G^K ≅ H^K` of `CategoryTheory.Functor.mapHomotopyCategory` is, at the image of a complex,
  the image of the degreewise comparison `CategoryTheory.NatIso.mapHomologicalComplex`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksDraft.ComparisonSquare

variable {C : Type*} [Category* C]

/-- **Two factorisations of a composite, glued.**  If `a ≫ b ≫ m₁` factors as `ψ ≫ k₀` and
`k₀ ≫ m₂` factors as `t ≫ k`, then `a ≫ b ≫ m₁ ≫ m₂` factors as `(ψ ≫ t) ≫ k`. -/
theorem comp_split_right {X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ : C}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (m₁ : X₃ ⟶ X₄) (m₂ : X₄ ⟶ X₅)
    (ψ : X₁ ⟶ Y₁) (k₀ : Y₁ ⟶ X₄) (t : Y₁ ⟶ Y₂) (k : Y₂ ⟶ X₅)
    (h₁ : a ≫ b ≫ m₁ = ψ ≫ k₀) (h₂ : k₀ ≫ m₂ = t ≫ k) :
    a ≫ b ≫ m₁ ≫ m₂ = (ψ ≫ t) ≫ k := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- **A functor carries a component of an isomorphism of functors to an isomorphism**, in the
split form a chase consumes: the composite of the images of the two components is an identity. -/
theorem map_hom_inv_id_app {D E : Type*} [Category* D] [Category* E] {F G : D ⥤ E}
    (e : F ≅ G) {H : Type*} [Category* H] (Q : E ⥤ H) (X : D) :
    Q.map (e.hom.app X) ≫ Q.map (e.inv.app X) = 𝟙 _ := by
  rw [← Q.map_comp, ← NatTrans.comp_app, e.hom_inv_id, NatTrans.id_app, Q.map_id]

/-- **A commuting square transposed along two inverses.**  If `γ ≫ p = x ≫ δ`, if `γ'` is a
retraction of `γ` and `δ'` a section of `δ`, then `γ' ≫ x = p ≫ δ'`. -/
theorem inv_comp_eq_of_comp_eq {X₁ X₂ X₃ X₄ : C}
    {γ : X₁ ⟶ X₂} {γ' : X₂ ⟶ X₁} {p : X₂ ⟶ X₄} {x : X₁ ⟶ X₃} {δ : X₃ ⟶ X₄} {δ' : X₄ ⟶ X₃}
    (hγ : γ' ≫ γ = 𝟙 X₂) (hδ : δ ≫ δ' = 𝟙 X₃) (hsq : γ ≫ p = x ≫ δ) :
    γ' ≫ x = p ≫ δ' := by
  have hx : x = γ ≫ p ≫ δ' := by rw [reassoc_of% hsq, hδ, Category.comp_id]
  rw [hx, ← Category.assoc, hγ, Category.id_comp]

/-- **A factorisation through the inverse of an isomorphism, read forwards.**  If `α ≫ β` is
`w` followed by a retraction `m'` of `m`, then `α ≫ β ≫ m` is `w`. -/
theorem comp_cancel_right {X Y T Z : C} {α : X ⟶ Y} {β : Y ⟶ T} {w : X ⟶ Z}
    {m : T ⟶ Z} {m' : Z ⟶ T} (hm : m' ≫ m = 𝟙 Z) (H : α ≫ β = w ≫ m') :
    α ≫ β ≫ m = w := by
  rw [← Category.assoc, H, Category.assoc, hm, Category.comp_id]

/-- `StacksDraft.ComparisonSquare.comp_cancel_right` with the factorisation given as a composite
of three morphisms, which is the shape `CategoryTheory.Functor.leftDerived_fac_app` produces. -/
theorem comp_cancel_right' {X Y T Z W V : C} {α : X ⟶ Y} {β : Y ⟶ T} {a : X ⟶ W} {b : W ⟶ V}
    {d : V ⟶ Z} {m : T ⟶ Z} {m' : Z ⟶ T} (hm : m' ≫ m = 𝟙 Z)
    (H : α ≫ β = a ≫ b ≫ d ≫ m') :
    α ≫ β ≫ m = a ≫ b ≫ d :=
  comp_cancel_right hm (H.trans (by simp only [Category.assoc]))

/-- **A composite of four morphisms in the image of a functor.** -/
theorem comp_four_map {D : Type*} [Category* D] (Q : C ⥤ D) {a b₁ b₂ b₃ b₄ : C}
    (m₁ : a ⟶ b₁) (m₂ : b₁ ⟶ b₂) (m₃ : b₂ ⟶ b₃) (m₄ : b₃ ⟶ b₄) {m : a ⟶ b₄}
    (hm : m₁ ≫ m₂ ≫ m₃ ≫ m₄ = m) :
    Q.map m₁ ≫ Q.map m₂ ≫ Q.map m₃ ≫ Q.map m₄ = Q.map m := by
  rw [← Q.map_comp, ← Q.map_comp, ← Q.map_comp, hm]

/-- **A cocycle of four morphisms, each recognised as the image of one under a functor.**  This is
`StacksDraft.ComparisonSquare.comp_four_map` with the recognition of each factor supplied as a
hypothesis, so that the rewriting happens here, where every object is a variable, rather than on a
goal whose objects are categories of sheaves of modules. -/
theorem comp_four_map_of_eq {D : Type*} [Category* D] (Q : C ⥤ D) {a b₁ b₂ b₃ b₄ : C}
    {m₁ : a ⟶ b₁} {m₂ : b₁ ⟶ b₂} {m₃ : b₂ ⟶ b₃} {m₄ : b₃ ⟶ b₄} {m : a ⟶ b₄}
    {α₁ : Q.obj a ⟶ Q.obj b₁} {α₂ : Q.obj b₁ ⟶ Q.obj b₂} {α₃ : Q.obj b₂ ⟶ Q.obj b₃}
    {α₄ : Q.obj b₃ ⟶ Q.obj b₄} {α : Q.obj a ⟶ Q.obj b₄}
    (h₁ : α₁ = Q.map m₁) (h₂ : α₂ = Q.map m₂) (h₃ : α₃ = Q.map m₃) (h₄ : α₄ = Q.map m₄)
    (hα : α = Q.map m) (hm : m₁ ≫ m₂ ≫ m₃ ≫ m₄ = m) :
    α₁ ≫ α₂ ≫ α₃ ≫ α₄ = α := by
  rw [h₁, h₂, h₃, h₄, hα]
  exact comp_four_map Q m₁ m₂ m₃ m₄ hm

/-- **Two equal isomorphisms of functors have equal components.** -/
theorem hom_app_congr {D E : Type*} [Category* D] [Category* E] {F G : D ⥤ E} {e₁ e₂ : F ≅ G}
    (he : e₁ = e₂) (X : D) : e₁.hom.app X = e₂.hom.app X := by rw [he]

/-- **The comparison datum of a left derived functor of a composite, evaluated.**  The inverse of
an associator followed by a whiskering on the right contributes, at an object, only the image of
the component. -/
theorem associator_inv_comp_whiskerRight_app {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] (L : C₁ ⥤ C₂) {F : C₂ ⥤ C₃} {G : C₁ ⥤ C₃} (α : L ⋙ F ⟶ G)
    (K : C₃ ⥤ C₄) (X : C₁) :
    ((Functor.associator L F K).inv ≫ Functor.whiskerRight α K).app X = K.map (α.app X) := by
  rw [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]

/-- **The comparison of the functors induced on homotopy categories is the degreewise one.**  At
the image of a complex, the inverse of `CategoryTheory.Functor.mapHomotopyCategoryCompIso` is the
image of the inverse of `CategoryTheory.NatIso.mapHomologicalComplex`.

Both sides are, by construction, the same morphism: the comparison on homotopy categories is
lifted through the quotient from the degreewise one.  Recording it is what lets a chase on
homotopy categories be reduced to a chase on complexes without unfolding either construction at
concrete functors. -/
theorem mapHomotopyCategoryCompIso_inv_app_quotient {V W W' : Type*} [Category* V] [Category* W]
    [Category* W'] [Preadditive V] [Preadditive W] [Preadditive W'] {F : V ⥤ W} {G : W ⥤ W'}
    {H : V ⥤ W'} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (c : ComplexShape ℤ)
    (N : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c).inv.app ((HomotopyCategory.quotient V c).obj N) =
      (HomotopyCategory.quotient W' c).map ((NatIso.mapHomologicalComplex e c).inv.app N) :=
  rfl

/-- **The identification of a factorisation, on homotopy categories, is the image of the
degreewise one.**  `StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient` with
a renaming along an equality of indices appended on both sides.

The equality of indices is a hypothesis rather than a `rfl`, which is what makes the statement
provable: the two renamings are `CategoryTheory.eqToIso` of the image of that equality under two
different families of functors, and substituting it is the only way to see that they agree. -/
theorem factorIso_inv_app_quotient {V W W' : Type*} [Category* V] [Category* W] [Category* W']
    [Preadditive V] [Preadditive W] [Preadditive W'] {ι : Type*} {F : V ⥤ W} {G : W ⥤ W'}
    [F.Additive] [G.Additive] (P : ι → (V ⥤ W')) [∀ i, (P i).Additive] (c : ComplexShape ℤ)
    {i j : ι} (e : F ⋙ G ≅ P i) (hij : i = j) (N : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c ≪≫
          eqToIso (congrArg (fun k => (P k).mapHomotopyCategory c) hij)).inv.app
        ((HomotopyCategory.quotient V c).obj N) =
      (HomotopyCategory.quotient W' c).map
        ((NatIso.mapHomologicalComplex (e ≪≫ eqToIso (congrArg P hij)) c).inv.app N) := by
  subst hij
  rw [show eqToIso (congrArg (fun k => (P k).mapHomotopyCategory c) (rfl : i = i)) =
      Iso.refl ((P i).mapHomotopyCategory c) from rfl, Iso.trans_refl,
    show eqToIso (congrArg P (rfl : i = i)) = Iso.refl (P i) from rfl, Iso.trans_refl]
  exact mapHomotopyCategoryCompIso_inv_app_quotient e c N

end StacksDraft.ComparisonSquare

end

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The boundary of a standard simplex as a gluing of its faces

The boundary `∂Δ[n]` is the union of the `n + 1` codimension-one faces of `Δ[n]`, and two of
those faces meet in the codimension-two face indexed by the complement of the two missing
vertices. This file records that presentation as a multicoequalizer diagram and uses it to
construct a morphism out of `∂Δ[n + 1]` from a compatible family of morphisms out of `Δ[n]`.

Mathlib has the analogous material for horns, in
`Mathlib/AlgebraicTopology/SimplicialSet/HornColimits.lean`; the only difference here is that
no face is omitted, so the index type is the whole of `Fin (n + 2)` and the compatibility
condition is imposed on every pair of faces.

## Main definitions

* `SSet.boundary.multicoequalizerDiagram`: the presentation of `∂Δ[n]` as the union of its
  faces, glued along the codimension-two faces.
* `SSet.boundary.isColimit`: that presentation is a colimit.
* `SSet.boundary.IsCompatible`: the condition on a family of morphisms `Δ[n] ⟶ X`, one for each
  face of `Δ[n + 1]`, that makes them the faces of a morphism `∂Δ[n + 1] ⟶ X`.
* `SSet.boundary.IsCompatible.desc`: the glued morphism, with `SSet.boundary.IsCompatible.ι_desc`
  computing its faces.

## Implementation notes

The compatibility condition is vacuous for `∂Δ[1]`, whose two faces are points meeting in the
empty subcomplex; the two codimension-two face lemmas that drive the general case are stated for
`Fin (n + 3)` and so do not apply there. That case is therefore separated out, and the relation
it asks for holds because a morphism out of the initial subcomplex is unique.
-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Opposite Limits

open scoped Simplicial

/-- Two morphisms out of a subcomplex which is the bottom one are equal. -/
theorem Subcomplex.hom_ext_of_eq_bot {X Z : SSet.{u}} {A : X.Subcomplex} (hA : A = ⊥)
    (f g : (A : SSet.{u}) ⟶ Z) : f = g := by
  subst hA
  exact Subcomplex.isInitialBot.hom_ext f g

namespace boundary

/-- **The boundary is the union of the codimension-one faces, glued along the codimension-two
faces.** -/
lemma multicoequalizerDiagram (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex)
      (fun j : Fin (n + 1) ↦ stdSimplex.face {j}ᶜ)
      (fun j k : Fin (n + 1) ↦ stdSimplex.face {j, k}ᶜ) where
  iSup_eq := (boundary_eq_iSup n).symm
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr 1
    ext x
    simp

/-- **The boundary is a multicoequalizer of the codimension-one faces.** -/
noncomputable def isColimit (n : ℕ) :
    IsColimit ((multicoequalizerDiagram.{u} n).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram n).isColimit'

variable {X : SSet.{u}} {n : ℕ}

/-- The condition that a family of morphisms `Δ[n] ⟶ X`, one for each vertex of `⦋n + 1⦌`, are
the faces of a morphism `∂Δ[n + 1] ⟶ X`. -/
protected def IsCompatible (f : ∀ _ : Fin (n + 2), (Δ[n] : SSet.{u}) ⟶ X) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => ∀ (j k : Fin _) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
        stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k

/-- Every family of two morphisms `Δ[0] ⟶ X` is compatible. -/
@[simp]
lemma isCompatible_zero_iff_true (f : ∀ _ : Fin 2, (Δ[0] : SSet.{u}) ⟶ X) :
    boundary.IsCompatible f ↔ True := Iff.rfl

/-- A family of morphisms `Δ[n + 1] ⟶ X` indexed by `Fin (n + 3)` is compatible if and only if
for all `j < k`, the `j`-th morphism restricted to its `k.pred`-th face agrees with the `k`-th
morphism restricted to its `j.castPred`-th face. -/
@[simp]
lemma isCompatible_succ_iff (f : ∀ _ : Fin (n + 3), (Δ[n + 1] : SSet.{u}) ⟶ X) :
    boundary.IsCompatible f ↔
      ∀ (j k : Fin (n + 3)) (hjk : j < k),
        stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
          stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k := Iff.rfl

namespace IsCompatible

/-- The faces `boundary.ι j ≫ g` of a morphism `g : ∂Δ[n + 1] ⟶ X` form a compatible family. -/
lemma of_hom (g : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
    boundary.IsCompatible (fun j ↦ boundary.ι j ≫ g) := by
  obtain _ | n := n
  · simp
  · simp only [isCompatible_succ_iff, ← Category.assoc]
    intro j k hjk
    congr 1
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Category.assoc, ι_ι, ι_ι,
      Fin.pred_succ, Fin.castPred_castSucc, stdSimplex.δ_comp_δ (by grind)]

variable {f : ∀ _ : Fin (n + 2), (Δ[n] : SSet.{u}) ⟶ X}

open stdSimplex in
/-- The relation satisfied by the faces of a compatible family on a codimension-two face. -/
private theorem homOfLE_comp (hf : boundary.IsCompatible f) (a b : Fin (n + 2)) (hab : a < b) :
    Subcomplex.homOfLE
        (show face ({a, b}ᶜ) ≤ face ({a}ᶜ) by simp [face_le_face_iff]) ≫
      (faceSingletonComplIso a).inv ≫ f a =
    Subcomplex.homOfLE
        (show face ({a, b}ᶜ) ≤ face ({b}ᶜ) by simp [face_le_face_iff]) ≫
      (faceSingletonComplIso b).inv ≫ f b := by
  obtain _ | n := n
  · refine Subcomplex.hom_ext_of_eq_bot (A := face ({a, b}ᶜ)) ?_ _ _
    have h : ({a, b}ᶜ : Finset (Fin 2)) = ∅ := by
      revert hab; fin_cases a <;> fin_cases b <;> decide
    rw [h, face_empty]
  · rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc _ _ hab,
      homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc _ _ hab,
      hf a b hab]

/-- The multicofork with vertex `X` whose component on the `j`-th face is `f j`. -/
private def multicofork (hf : boundary.IsCompatible f) :
    Multicofork ((multicoequalizerDiagram.{u} (n + 1)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun j ↦ (stdSimplex.faceSingletonComplIso j).inv ≫ f j)
    (fun r ↦ hf.homOfLE_comp r.1.1 r.1.2 r.2)

/-- A compatible family `f` admits a morphism `φ : ∂Δ[n + 1] ⟶ X` with `boundary.ι j ≫ φ = f j`
for every `j`. -/
lemma exists_desc (hf : boundary.IsCompatible f) :
    ∃ φ : (∂Δ[n + 1] : SSet.{u}) ⟶ X, ∀ j : Fin (n + 2), boundary.ι j ≫ φ = f j :=
  ⟨(boundary.isColimit.{u} (n + 1)).desc hf.multicofork, fun j ↦
    (cancel_epi (stdSimplex.faceSingletonComplIso j).inv).1
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ (boundary.isColimit.{u} (n + 1)).desc hf.multicofork)
          (faceSingletonComplIso_inv_ι j))).trans
        ((boundary.isColimit.{u} (n + 1)).fac hf.multicofork (.right j)))⟩

/-- **A compatible family of faces glues to a morphism out of the boundary.** -/
@[no_expose]
noncomputable def desc (hf : boundary.IsCompatible f) : (∂Δ[n + 1] : SSet.{u}) ⟶ X :=
  hf.exists_desc.choose

/-- The `j`-th face of `SSet.boundary.IsCompatible.desc` is the `j`-th member of the family. -/
@[reassoc (attr := simp)]
lemma ι_desc (hf : boundary.IsCompatible f) (j : Fin (n + 2)) :
    boundary.ι j ≫ hf.desc = f j :=
  hf.exists_desc.choose_spec j

end IsCompatible

end boundary

end SSet

end

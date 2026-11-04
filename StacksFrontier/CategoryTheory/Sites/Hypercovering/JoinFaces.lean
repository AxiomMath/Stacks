module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The two complementary faces of a simplex

Let `m n : ℕ` and write `N = m + n + 1`. The vertices of `⦋N⦌` split into the first `m + 1` and
the last `n + 1`, and the two faces of `Δ[N]` they span are disjoint subcomplexes whose union is
the subcomplex `Δ[m] ⊔ Δ[n] ⊆ Δ[N]` -- the "ends" of the join `Δ[m] ⋆ Δ[n] = Δ[N]`.

This file records that splitting: the two simplex maps `⦋m⦌ ⟶ ⦋N⦌` and `⦋n⦌ ⟶ ⦋N⦌`, the union
of their images as a subcomplex, and the fact that a morphism out of that union is exactly a
pair of morphisms out of `Δ[m]` and `Δ[n]`.

## Main definitions

* `SSet.stdSimplex.joinFst` and `.joinSnd`: the two simplex maps, injective with complementary
  images.
* `SSet.stdSimplex.joinEnds`: their union as a subcomplex of `Δ[N]`.
* `SSet.stdSimplex.joinFstIso` and `.joinSndIso`: the two faces are copies of `Δ[m]` and `Δ[n]`.
* `SSet.stdSimplex.joinEndsHomEquiv`: a morphism out of `joinEnds` is a pair of morphisms out of
  `Δ[m]` and `Δ[n]`.

## Implementation notes

The two faces are `SSet.stdSimplex.face` of the two halves of `Finset.univ`, so that Mathlib's
`SSet.stdSimplex.faceRepresentableBy` supplies the isomorphisms with the standard simplices, and
`SSet.stdSimplex.face_inter_face` their disjointness. The simplex maps are *defined* as the ones
`faceRepresentableBy` produces from the order isomorphisms, which makes the compatibility
`joinFstIso_hom_ι` hold by `rfl`, exactly as for Mathlib's `faceSingletonComplIso_hom_ι`.

A morphism out of the union is a pair of morphisms because the square of the two faces, their
intersection and their union is bicartesian in the lattice of subcomplexes, hence a pushout
square of simplicial sets (`SSet.Subcomplex.BicartSq.isPushout`), and the intersection is the
initial subcomplex, so the pushout is a coproduct.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace SSet.stdSimplex

variable (m n : ℕ)

/-- The first `m + 1` vertices of `⦋m + n + 1⦌`. -/
def joinFstFinset : Finset (Fin (m + n + 2)) :=
  Finset.univ.filter fun x => (x : ℕ) ≤ m

/-- The last `n + 1` vertices of `⦋m + n + 1⦌`. -/
def joinSndFinset : Finset (Fin (m + n + 2)) :=
  Finset.univ.filter fun x => m < (x : ℕ)

/-- A vertex lies in `joinFstFinset m n` if and only if its index is at most `m`. -/
@[simp]
theorem mem_joinFstFinset {x : Fin (m + n + 2)} : x ∈ joinFstFinset m n ↔ (x : ℕ) ≤ m := by
  simp [joinFstFinset]

/-- A vertex lies in `joinSndFinset m n` if and only if its index exceeds `m`. -/
@[simp]
theorem mem_joinSndFinset {x : Fin (m + n + 2)} : x ∈ joinSndFinset m n ↔ m < (x : ℕ) := by
  simp [joinSndFinset]

/-- The first `m + 1` and the last `n + 1` vertices of `⦋m + n + 1⦌` are disjoint. -/
theorem joinFstFinset_inf_joinSndFinset : joinFstFinset m n ⊓ joinSndFinset m n = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have h₁ := (mem_joinFstFinset m n).1 (Finset.mem_inter.1 hx).1
  have h₂ := (mem_joinSndFinset m n).1 (Finset.mem_inter.1 hx).2
  omega

/-- The order isomorphism of `Fin (m + 1)` with the first `m + 1` vertices. -/
def joinFstOrderIso : Fin (m + 1) ≃o (joinFstFinset m n) where
  toFun i := ⟨⟨i.1, by omega⟩, (mem_joinFstFinset m n).2 (by change (i : ℕ) ≤ m; omega)⟩
  invFun x := ⟨x.1.1, by have := (mem_joinFstFinset m n).1 x.2; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The order isomorphism of `Fin (n + 1)` with the last `n + 1` vertices. -/
def joinSndOrderIso : Fin (n + 1) ≃o (joinSndFinset m n) where
  toFun i := ⟨⟨m + 1 + i.1, by omega⟩,
    (mem_joinSndFinset m n).2 (by change m < m + 1 + (i : ℕ); omega)⟩
  invFun x := ⟨x.1.1 - (m + 1), by have := (mem_joinSndFinset m n).1 x.2; omega⟩
  left_inv i := by
    apply Fin.ext
    change m + 1 + (i : ℕ) - (m + 1) = (i : ℕ)
    omega
  right_inv x := by
    have hx := (mem_joinSndFinset m n).1 x.2
    apply Subtype.ext
    apply Fin.ext
    change m + 1 + ((x : Fin (m + n + 2)) - (m + 1) : ℕ) = ((x : Fin (m + n + 2)) : ℕ)
    omega
  map_rel_iff' := by
    intro i j
    change m + 1 + (i : ℕ) ≤ m + 1 + (j : ℕ) ↔ i ≤ j
    rw [Fin.le_def]
    omega

/-- The simplex map `⦋m⦌ ⟶ ⦋m + n + 1⦌` onto the first `m + 1` vertices. -/
def joinFst : (⦋m⦌ : SimplexCategory) ⟶ ⦋m + n + 1⦌ :=
  SimplexCategory.Hom.mk ((OrderHom.Subtype.val (· ∈ joinFstFinset m n)).comp
    (joinFstOrderIso m n).toOrderEmbedding.toOrderHom)

/-- The simplex map `⦋n⦌ ⟶ ⦋m + n + 1⦌` onto the last `n + 1` vertices. -/
def joinSnd : (⦋n⦌ : SimplexCategory) ⟶ ⦋m + n + 1⦌ :=
  SimplexCategory.Hom.mk ((OrderHom.Subtype.val (· ∈ joinSndFinset m n)).comp
    (joinSndOrderIso m n).toOrderEmbedding.toOrderHom)

/-- The union of the two complementary faces of `Δ[m + n + 1]`. -/
def joinEnds : (Δ[m + n + 1] : SSet.{u}).Subcomplex :=
  face (joinFstFinset m n) ⊔ face (joinSndFinset m n)

/-- The first face is a copy of `Δ[m]`. -/
def joinFstIso : (Δ[m] : SSet.{u}) ≅ (face (joinFstFinset m n) : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (joinFstOrderIso m n))

/-- The second face is a copy of `Δ[n]`. -/
def joinSndIso : (Δ[n] : SSet.{u}) ≅ (face (joinSndFinset m n) : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (joinSndOrderIso m n))

/-- The isomorphism `joinFstIso` followed by the inclusion of the first face is the map of
standard simplices induced by `joinFst`. -/
@[reassoc]
theorem joinFstIso_hom_ι :
    (joinFstIso.{u} m n).hom ≫ (face (joinFstFinset m n)).ι = stdSimplex.map (joinFst m n) :=
  rfl

/-- The isomorphism `joinSndIso` followed by the inclusion of the second face is the map of
standard simplices induced by `joinSnd`. -/
@[reassoc]
theorem joinSndIso_hom_ι :
    (joinSndIso.{u} m n).hom ≫ (face (joinSndFinset m n)).ι = stdSimplex.map (joinSnd m n) :=
  rfl

/-- The square of the two complementary faces, their intersection and their union is
bicartesian in the lattice of subcomplexes of `Δ[m + n + 1]`. -/
theorem joinBicartSq :
    Subcomplex.BicartSq (⊥ : (Δ[m + n + 1] : SSet.{u}).Subcomplex)
      (face (joinFstFinset m n)) (face (joinSndFinset m n)) (joinEnds m n) where
  sup_eq := rfl
  inf_eq := by
    rw [face_inter_face, joinFstFinset_inf_joinSndFinset, face_empty]

/-- The two complementary faces of `Δ[m + n + 1]` exhibit their union as a pushout, the
intersection being the initial subcomplex. -/
theorem joinEnds_isPushout :
    IsPushout (Subcomplex.homOfLE (joinBicartSq.{u} m n).le₁₂)
      (Subcomplex.homOfLE (joinBicartSq.{u} m n).le₁₃)
      (Subcomplex.homOfLE (joinBicartSq.{u} m n).le₂₄)
      (Subcomplex.homOfLE (joinBicartSq.{u} m n).le₃₄) :=
  (joinBicartSq m n).isPushout

/-- The inclusion of the first face into the union of the two complementary faces, read on
`Δ[m]`. -/
def joinFstInclusion : (Δ[m] : SSet.{u}) ⟶ (joinEnds.{u} m n : SSet.{u}) :=
  (joinFstIso m n).hom ≫ Subcomplex.homOfLE (joinBicartSq m n).le₂₄

/-- The inclusion of the second face into the union of the two complementary faces, read on
`Δ[n]`. -/
def joinSndInclusion : (Δ[n] : SSet.{u}) ⟶ (joinEnds.{u} m n : SSet.{u}) :=
  (joinSndIso m n).hom ≫ Subcomplex.homOfLE (joinBicartSq m n).le₃₄

/-- The inclusion `joinFstInclusion` followed by the inclusion of `joinEnds` into
`Δ[m + n + 1]` is the map of standard simplices induced by `joinFst`. -/
@[reassoc]
theorem joinFstInclusion_comp_ι :
    joinFstInclusion.{u} m n ≫ (joinEnds m n).ι = stdSimplex.map (joinFst m n) := by
  rw [joinFstInclusion, Category.assoc, Subcomplex.homOfLE_ι, joinFstIso_hom_ι]

/-- The inclusion `joinSndInclusion` followed by the inclusion of `joinEnds` into
`Δ[m + n + 1]` is the map of standard simplices induced by `joinSnd`. -/
@[reassoc]
theorem joinSndInclusion_comp_ι :
    joinSndInclusion.{u} m n ≫ (joinEnds m n).ι = stdSimplex.map (joinSnd m n) := by
  rw [joinSndInclusion, Category.assoc, Subcomplex.homOfLE_ι, joinSndIso_hom_ι]

/-- The union of the two complementary faces of `Δ[m + n + 1]` is nonempty. -/
instance : SSet.Nonempty (joinEnds.{u} m n : SSet.{u}) :=
  SSet.nonempty_of_hom (joinFstInclusion m n)

/-- The morphism out of the union of the two faces determined by a pair of morphisms. -/
noncomputable def joinEndsDesc {Z : SSet.{u}} (a : (Δ[m] : SSet.{u}) ⟶ Z)
    (b : (Δ[n] : SSet.{u}) ⟶ Z) :
    (joinEnds.{u} m n : SSet.{u}) ⟶ Z :=
  (joinEnds_isPushout m n).desc ((joinFstIso m n).inv ≫ a) ((joinSndIso m n).inv ≫ b)
    (Subcomplex.isInitialBot.hom_ext _ _)

/-- The morphism `joinEndsDesc m n a b` restricts to `a` on the first face. -/
@[reassoc (attr := simp)]
theorem joinFstInclusion_comp_joinEndsDesc {Z : SSet.{u}} (a : (Δ[m] : SSet.{u}) ⟶ Z)
    (b : (Δ[n] : SSet.{u}) ⟶ Z) :
    joinFstInclusion m n ≫ joinEndsDesc m n a b = a := by
  rw [joinFstInclusion, joinEndsDesc, Category.assoc, (joinEnds_isPushout m n).inl_desc,
    Iso.hom_inv_id_assoc]

/-- The morphism `joinEndsDesc m n a b` restricts to `b` on the second face. -/
@[reassoc (attr := simp)]
theorem joinSndInclusion_comp_joinEndsDesc {Z : SSet.{u}} (a : (Δ[m] : SSet.{u}) ⟶ Z)
    (b : (Δ[n] : SSet.{u}) ⟶ Z) :
    joinSndInclusion m n ≫ joinEndsDesc m n a b = b := by
  rw [joinSndInclusion, joinEndsDesc, Category.assoc, (joinEnds_isPushout m n).inr_desc,
    Iso.hom_inv_id_assoc]

/-- Two morphisms out of the union of the two complementary faces are equal if they agree on
each face. -/
theorem joinEnds_hom_ext {Z : SSet.{u}} {φ ψ : (joinEnds.{u} m n : SSet.{u}) ⟶ Z}
    (h₁ : joinFstInclusion m n ≫ φ = joinFstInclusion m n ≫ ψ)
    (h₂ : joinSndInclusion m n ≫ φ = joinSndInclusion m n ≫ ψ) : φ = ψ := by
  refine (joinEnds_isPushout m n).hom_ext ?_ ?_
  · exact (cancel_epi (joinFstIso m n).hom).1 h₁
  · exact (cancel_epi (joinSndIso m n).hom).1 h₂

/-- Composing `joinEndsDesc m n a b` with `u` is `joinEndsDesc` of the composites `a ≫ u` and
`b ≫ u`. -/
theorem joinEndsDesc_comp {Z Z' : SSet.{u}} (a : (Δ[m] : SSet.{u}) ⟶ Z)
    (b : (Δ[n] : SSet.{u}) ⟶ Z) (u : Z ⟶ Z') :
    joinEndsDesc m n a b ≫ u = joinEndsDesc m n (a ≫ u) (b ≫ u) := by
  exact joinEnds_hom_ext m n (by simp) (by simp)

/-- A morphism out of the union of the two complementary faces is a pair of morphisms out of
`Δ[m]` and `Δ[n]`: the union is the pushout of the two faces over their intersection, which is
the initial subcomplex, so it is their coproduct. -/
noncomputable def joinEndsHomEquiv (Z : SSet.{u}) :
    ((joinEnds.{u} m n : SSet.{u}) ⟶ Z) ≃
      (((Δ[m] : SSet.{u}) ⟶ Z) × ((Δ[n] : SSet.{u}) ⟶ Z)) where
  toFun φ := (joinFstInclusion m n ≫ φ, joinSndInclusion m n ≫ φ)
  invFun p := joinEndsDesc m n p.1 p.2
  left_inv _ :=
    joinEnds_hom_ext m n (joinFstInclusion_comp_joinEndsDesc m n _ _)
      (joinSndInclusion_comp_joinEndsDesc m n _ _)
  right_inv p :=
    Prod.ext (joinFstInclusion_comp_joinEndsDesc m n p.1 p.2)
      (joinSndInclusion_comp_joinEndsDesc m n p.1 p.2)

/-- The equivalence `joinEndsHomEquiv` sends a morphism to its restrictions to the two faces. -/
@[simp]
theorem joinEndsHomEquiv_apply (Z : SSet.{u}) (φ : (joinEnds.{u} m n : SSet.{u}) ⟶ Z) :
    joinEndsHomEquiv m n Z φ = (joinFstInclusion m n ≫ φ, joinSndInclusion m n ≫ φ) :=
  rfl

end SSet.stdSimplex

end

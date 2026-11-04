module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Basic
public import StacksFrontier.Cotangent.StandardResolution

/-!
# The standard resolution in a slice category

The free-polynomial-algebra adjunction lifts to the categories of objects over a fixed
commutative algebra. Its standard simplicial resolution of the identity arrow has, after
forgetting the arrow to that algebra, the usual standard resolution.

## Main definitions

* `CommAlgCat.slicePolynomialComonad`: the comonad of the lifted adjunction.
* `CommAlgCat.IsSliceStandardEndofunctor`: the defining equations of the standard augmented
  simplicial endofunctor of that comonad.

## Main results

* `CommAlgCat.existsSliceStandardEndofunctor`: the standard simplicial endofunctor of the lifted
  adjunction exists.
* `CommAlgCat.sliceStandardResolution_iso`: every such resolution of the identity arrow is
  isomorphic to the ordinary standard resolution after forgetting to algebras.

## Implementation notes

The category of arrows of `A`-algebras to `B` is `Over B`; that of maps of sets to the underlying
set of `B` is `Over ((forget (CommAlgCat A)).obj B)`. The slice adjunction
`CategoryTheory.Over.postAdjunctionRight` and the commuting square of forgetful functors
`CategoryTheory.Over.post_forget_eq_forget_comp` are the instances of the two general Mathlib
constructions for the polynomial-algebra/underlying-set adjunction. Since the two standard
endofunctors are obtained by independent choices, their resolutions are stated to be isomorphic
rather than definitionally equal.

## References

* [Stacks Project, Tag 08PP](https://stacks.math.columbia.edu/tag/08PP)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

namespace CommAlgCat


/-- A family of equalities between the terms of two simplicial objects which is compatible with
all faces and degeneracies gives an isomorphism of simplicial objects. -/
private noncomputable def simplicialIsoOfFaces
    {C : Type*} [Category C] (F G : SimplexCategoryᵒᵖ ⥤ C)
    (hObj : ∀ n : SimplexCategory, F.obj (op n) = G.obj (op n))
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)),
      F.map (SimplexCategory.δ i).op ≫ eqToHom (hObj (⦋n⦌)) =
        eqToHom (hObj (⦋n + 1⦌)) ≫ G.map (SimplexCategory.δ i).op)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)),
      F.map (SimplexCategory.σ i).op ≫ eqToHom (hObj (⦋n + 1⦌)) =
        eqToHom (hObj (⦋n⦌)) ≫ G.map (SimplexCategory.σ i).op) : F ≅ G := by
  refine NatIso.ofComponents (fun n => eqToIso (hObj n.unop)) ?_
  intro i j f
  have h := SimplicialObject.naturality_of_δ_σ (U := F) (U' := G)
    (fun n => eqToHom (hObj (⦋n⦌))) hδ hσ f.unop
  have hi : (⦋i.unop.len⦌ : SimplexCategory) = i.unop := SimplexCategory.mk_len i.unop
  have hj : (⦋j.unop.len⦌ : SimplexCategory) = j.unop := SimplexCategory.mk_len j.unop
  simpa only [hi, hj, Quiver.Hom.op_unop, eqToIso.hom] using h

universe u v

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

add_to_stacks 08PP "the adjunction" CategoryTheory.Over.postAdjunctionRight
add_to_stacks 08PP "the commutative square" CategoryTheory.Over.post_forget_eq_forget_comp
add_to_sga "3 I 1.6" "more general" CategoryTheory.Over.post_forget_eq_forget_comp

/-- The comonad of the free-forget adjunction in the slice over `B`. -/
noncomputable def slicePolynomialComonad : Comonad (Over B) :=
  (Over.postAdjunctionRight (Y := B)
    (adj.{u, v} A)).toComonad

private theorem sliceIterate_forget (n : ℕ) (Y : Over B) :
    (Over.forget B).obj (((slicePolynomialComonad A B).toFunctor.iterate n).obj Y) =
      ((polynomialComonad A).toFunctor.iterate n).obj Y.left := by
  induction n with
  | zero => simp [Functor.iterate]
  | succ n ih =>
      simp only [Functor.iterate]
      change (Over.forget B).obj ((slicePolynomialComonad A B).toFunctor.obj
        (((slicePolynomialComonad A B).toFunctor.iterate n).obj Y)) =
        (polynomialComonad A).toFunctor.obj
          (((polynomialComonad A).toFunctor.iterate n).obj Y.left)
      exact congrArg (polynomialComonad A).toFunctor.obj ih

private abbrev sliceForget_square :
    (slicePolynomialComonad A B).toFunctor ⋙ Over.forget B =
      Over.forget B ⋙ (polynomialComonad A).toFunctor := rfl

private theorem sliceForget_obj_cast (Y : Over B) :
    eqToHom (congrArg (fun K : Over B ⥤ CommAlgCat A => K.obj Y)
      (sliceForget_square A B)) = 𝟙 _ := by
  change eqToHom (rfl : _ = _) = _
  simp

private theorem sliceIterate_succ_forget (n : ℕ) (Y : Over B) :
    sliceIterate_forget A B (n + 1) Y =
      (congrArg (fun K : Over B ⥤ CommAlgCat A =>
          K.obj (((slicePolynomialComonad A B).toFunctor.iterate n).obj Y))
        (sliceForget_square A B)).trans
        (congrArg (fun Z : CommAlgCat A => (polynomialComonad A).toFunctor.obj Z)
          (sliceIterate_forget A B n Y)) := Subsingleton.elim _ _

private theorem sliceIterate_succ_cast (n : ℕ) (Y : Over B) :
    eqToHom (sliceIterate_forget A B (n + 1) Y) =
      eqToHom (congrArg (fun K : Over B ⥤ CommAlgCat A =>
        K.obj (((slicePolynomialComonad A B).toFunctor.iterate n).obj Y))
        (sliceForget_square A B)) ≫
      (polynomialComonad A).toFunctor.map
        (eqToHom (sliceIterate_forget A B n Y)) := by
  rw [eqToHom_map, eqToHom_trans]

private theorem sliceIterate_succ_eqToHom (n : ℕ) (Y : Over B) :
    eqToHom (sliceIterate_forget A B (n + 1) Y) =
      (polynomialComonad A).toFunctor.map (eqToHom (sliceIterate_forget A B n Y)) := by
  rw [sliceIterate_succ_cast, sliceForget_obj_cast]
  exact Category.id_comp _

private theorem forget_map_sliceFunctor_map {X Z : Over B} (f : X ⟶ Z) :
    (Over.forget B).map ((slicePolynomialComonad A B).toFunctor.map f) =
      (polynomialComonad A).toFunctor.map ((Over.forget B).map f) := rfl

private theorem sliceFace_forget_zero (n : ℕ) (Y : Over B) :
    (Over.forget B).map
        ((Godement.face (slicePolynomialComonad A B).ε (n + 1) 0).app Y) ≫
      eqToHom (sliceIterate_forget A B (n + 1) Y) =
    eqToHom (sliceIterate_forget A B (n + 2) Y) ≫
      (Godement.face (polynomialComonad A).ε (n + 1) 0).app Y.left := by
  simp only [Godement.face, Fin.cases_zero, Functor.whiskerLeft_app]
  let Z := (((slicePolynomialComonad A B).toFunctor.iterate (n + 1)).obj Y)
  let hsquare : (slicePolynomialComonad A B).toFunctor ⋙ Over.forget B =
      Over.forget B ⋙ (polynomialComonad A).toFunctor := rfl
  let hbase := congrArg (fun K : Over B ⥤ CommAlgCat A => K.obj Z) hsquare
  have hc : (Over.forget B).map
      ((slicePolynomialComonad A B).ε.app Z) =
      eqToHom hbase ≫ (polynomialComonad A).ε.app
        ((Over.forget B).obj Z) := by
    apply CommAlgCat.hom_ext
    ext x
    dsimp [hbase, hsquare, eqToHom, Over.forget, slicePolynomialComonad,
      polynomialComonad, adj]
    rfl
  have hR : eqToHom (sliceIterate_forget A B (n + 2) Y) ≫
      (polynomialComonad A).ε.app
        (((polynomialComonad A).toFunctor.iterate (n + 1)).obj Y.left) =
      eqToHom hbase ≫
        (polynomialComonad A).toFunctor.map
          (eqToHom (sliceIterate_forget A B (n + 1) Y)) ≫
        (polynomialComonad A).ε.app
          (((polynomialComonad A).toFunctor.iterate (n + 1)).obj Y.left) := by
    rw [sliceIterate_succ_cast A B (n + 1) Y, Category.assoc]
  rw [hc, hR]
  have hn := (polynomialComonad A).ε.naturality
    (eqToHom (sliceIterate_forget A B (n + 1) Y))
  cat_disch

private theorem sliceFace_forget (n : ℕ) (i : Fin (n + 1)) (Y : Over B) :
    (Over.forget B).map ((Godement.face (slicePolynomialComonad A B).ε n i).app Y) ≫
      eqToHom (sliceIterate_forget A B n Y) =
    eqToHom (sliceIterate_forget A B (n + 1) Y) ≫
      (Godement.face (polynomialComonad A).ε n i).app Y.left := by
  induction n generalizing Y with
  | zero =>
      fin_cases i
      cases sliceIterate_forget A B 1 Y
      cases sliceIterate_forget A B 0 Y
      rfl
  | succ n ih =>
      cases i using Fin.cases with
      | zero => exact sliceFace_forget_zero A B n Y
      | succ i =>
          simp only [Godement.face, Fin.cases_succ, Functor.whiskerRight_app]
          have hi := congrArg ((polynomialComonad A).toFunctor.map) (ih i Y)
          rw [forget_map_sliceFunctor_map, sliceIterate_succ_eqToHom A B n,
            sliceIterate_succ_eqToHom A B (n + 1)]
          simp only [Functor.map_comp] at hi
          exact hi

private theorem sliceDegeneracy_forget_zero (n : ℕ) (Y : Over B) :
    (Over.forget B).map
      ((Godement.degeneracy (slicePolynomialComonad A B).δ n 0).app Y) ≫
      eqToHom (sliceIterate_forget A B (n + 2) Y) =
    eqToHom (sliceIterate_forget A B (n + 1) Y) ≫
      (Godement.degeneracy (polynomialComonad A).δ n 0).app Y.left := by
  simp only [Godement.Prep.degeneracy_zero, Functor.whiskerLeft_app]
  have hδ : (Over.forget B).map ((slicePolynomialComonad A B).δ.app
      (((slicePolynomialComonad A B).toFunctor.iterate n).obj Y)) =
      (polynomialComonad A).δ.app
        ((Over.forget B).obj (((slicePolynomialComonad A B).toFunctor.iterate n).obj Y)) := rfl
  rw [hδ, sliceIterate_succ_eqToHom A B (n + 1), sliceIterate_succ_eqToHom A B n]
  exact ((polynomialComonad A).δ.naturality (eqToHom (sliceIterate_forget A B n Y))).symm

private theorem sliceDegeneracy_forget (n : ℕ) (i : Fin (n + 1)) (Y : Over B) :
    (Over.forget B).map
      ((Godement.degeneracy (slicePolynomialComonad A B).δ n i).app Y) ≫
      eqToHom (sliceIterate_forget A B (n + 2) Y) =
    eqToHom (sliceIterate_forget A B (n + 1) Y) ≫
      (Godement.degeneracy (polynomialComonad A).δ n i).app Y.left := by
  induction n generalizing Y with
  | zero =>
      fin_cases i
      convert sliceDegeneracy_forget_zero A B 0 Y using 1 <;> rfl
  | succ n ih =>
      cases i using Fin.cases with
      | zero => exact sliceDegeneracy_forget_zero A B (n + 1) Y
      | succ i =>
          simp only [Godement.degeneracy, Fin.cases_succ, Functor.whiskerRight_app]
          have hi := congrArg ((polynomialComonad A).toFunctor.map) (ih i Y)
          rw [forget_map_sliceFunctor_map, sliceIterate_succ_eqToHom A B (n + 1),
            sliceIterate_succ_eqToHom A B (n + 2)]
          simp only [Functor.map_comp] at hi
          exact hi

/-- The defining equations of the standard augmented simplicial endofunctor of the
polynomial comonad on algebras over `B`. -/
def IsSliceStandardEndofunctor
    (X : SimplicialObject.Augmented (Over B ⥤ Over B)) : Prop :=
  ∃ (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) =
      ((slicePolynomialComonad A B).toFunctor.iterate (n + 1)))
    (hX : X.right = (𝟭 (Over B) : Over B ⥤ Over B)),
    (∀ (n : ℕ) (j : Fin (n + 2)),
      X.left.δ j = eqToHom (h (n + 1)) ≫
        Godement.face (slicePolynomialComonad A B).ε (n + 1) j ≫
          eqToHom (h n).symm) ∧
    (∀ (n : ℕ) (j : Fin (n + 1)),
      X.left.σ j = eqToHom (h n) ≫
        Godement.degeneracy (slicePolynomialComonad A B).δ n j ≫
          eqToHom (h (n + 1)).symm) ∧
    X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫
      Godement.face (slicePolynomialComonad A B).ε 0 0 ≫ eqToHom hX.symm

/-- The comonad of the lifted adjunction has a standard augmented simplicial
endofunctor in the category of algebras over `B`. -/
@[stacks 08PP "the standard endofunctor in the slice"]
theorem existsSliceStandardEndofunctor :
    ∃ X : SimplicialObject.Augmented (Over B ⥤ Over B),
      IsSliceStandardEndofunctor A B X := by
  let G := slicePolynomialComonad A B
  unfold IsSliceStandardEndofunctor
  obtain ⟨X, h, hX, hδ, hσ, hhom⟩ :=
    CategoryTheory.Godement.exists_augmented_standardResolution G.ε G.δ
      (NatTrans.ext (funext G.left_counit)) (NatTrans.ext (funext G.right_counit))
      (NatTrans.ext (funext fun Y => (G.coassoc Y).symm))
  exact ⟨X, by simpa only [G] using ⟨h, hX, hδ, hσ, hhom⟩⟩

/-- Under `Over.forget B`, the faces of a slice standard endofunctor evaluated on the
identity of `B` agree with those of the standard resolution of `B`. -/
private theorem sliceStandardResolution_face_comm {X : SimplicialObject.Augmented (Over B ⥤ Over B)}
    (hX : IsSliceStandardEndofunctor A B X) (n : ℕ) (j : Fin (n + 2))
    (P : (Over.forget B).obj ((X.left.obj (op ⦋n⦌)).obj (Over.mk (𝟙 B))) =
      (standardResolution A B).left.obj (op ⦋n⦌))
    (Q : (Over.forget B).obj ((X.left.obj (op ⦋n + 1⦌)).obj (Over.mk (𝟙 B))) =
      (standardResolution A B).left.obj (op ⦋n + 1⦌)) :
    (Over.forget B).map ((X.left.δ j).app (Over.mk (𝟙 B))) ≫ eqToHom P =
      eqToHom Q ≫ (standardResolution A B).left.δ j := by
  obtain ⟨_, _, hFaces, -, -⟩ := hX
  have hb := sliceFace_forget A B (n + 1) j (Over.mk (𝟙 B))
  rw [comp_eqToHom_iff] at hb
  rw [hFaces, standardResolution_face]
  simp only [NatTrans.comp_app, eqToHom_app, Functor.map_comp, eqToHom_map, hb,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- Under `Over.forget B`, the degeneracies of a slice standard endofunctor evaluated on
the identity of `B` agree with those of the standard resolution of `B`. -/
private theorem sliceStandardResolution_degeneracy_comm
    {X : SimplicialObject.Augmented (Over B ⥤ Over B)}
    (hX : IsSliceStandardEndofunctor A B X) (n : ℕ) (j : Fin (n + 1))
    (P : (Over.forget B).obj ((X.left.obj (op ⦋n + 1⦌)).obj (Over.mk (𝟙 B))) =
      (standardResolution A B).left.obj (op ⦋n + 1⦌))
    (Q : (Over.forget B).obj ((X.left.obj (op ⦋n⦌)).obj (Over.mk (𝟙 B))) =
      (standardResolution A B).left.obj (op ⦋n⦌)) :
    (Over.forget B).map ((X.left.σ j).app (Over.mk (𝟙 B))) ≫ eqToHom P =
      eqToHom Q ≫ (standardResolution A B).left.σ j := by
  obtain ⟨_, _, -, hDegeneracies, -⟩ := hX
  have hb := sliceDegeneracy_forget A B n j (Over.mk (𝟙 B))
  rw [comp_eqToHom_iff] at hb
  rw [hDegeneracies, standardResolution_degeneracy]
  simp only [NatTrans.comp_app, eqToHom_app, Functor.map_comp, eqToHom_map, hb,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- Under `Over.forget B`, the augmentation of a slice standard endofunctor evaluated on
the identity of `B` agrees with that of the standard resolution of `B`. -/
private theorem sliceStandardResolution_augmentation_comm
    {X : SimplicialObject.Augmented (Over B ⥤ Over B)}
    (hX : IsSliceStandardEndofunctor A B X)
    (P : (Over.forget B).obj ((X.left.obj (op ⦋0⦌)).obj (Over.mk (𝟙 B))) =
      (standardResolution A B).left.obj (op ⦋0⦌))
    (R : (Over.forget B).obj (X.right.obj (Over.mk (𝟙 B))) = B) :
    eqToHom P ≫ (standardResolution A B).hom.app (op ⦋0⦌) =
      (Over.forget B).map ((X.hom.app (op ⦋0⦌)).app (Over.mk (𝟙 B))) ≫ eqToHom R := by
  obtain ⟨_, _, -, -, hAug⟩ := hX
  have hb := sliceFace_forget A B 0 0 (Over.mk (𝟙 B))
  rw [comp_eqToHom_iff] at hb
  have hp : eqToHom (rfl : CommAlgCat.of A (MvPolynomial B A) = _) ≫
      CommAlgCat.ofHom (MvPolynomial.aeval (id : B → B)) =
        (Godement.face (polynomialComonad A).ε 0 0).app (Over.mk (𝟙 B)).left := by
    apply CommAlgCat.hom_ext
    with_unfolding_all rfl
  rw [hAug, standardResolution_augmentation]
  simp only [NatTrans.comp_app, eqToHom_app, Functor.map_comp, eqToHom_map, hb,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rw [← hp]
  rfl

/-- Every standard simplicial endofunctor arising from the slice adjunction, evaluated on
the identity of `B`, gives the ordinary augmented standard resolution of `B`. -/
@[stacks 08PP "comparison of standard resolutions"]
theorem sliceStandardResolution_iso
    (X : SimplicialObject.Augmented (Over B ⥤ Over B))
    (hX : IsSliceStandardEndofunctor A B X) :
    Nonempty
      (((SimplicialObject.Augmented.whiskeringObj _ _ (Over.forget B)).obj
        ((SimplicialObject.Augmented.whiskeringObj _ _
        ((evaluation (Over B) (Over B)).obj (Over.mk (𝟙 B)))).obj X)) ≅
        standardResolution A B) := by
  obtain ⟨h, hRight, -, -, -⟩ := id hX
  let I : Over B := Over.mk (𝟙 B)
  let ev := (evaluation (Over B) (Over B)).obj I
  let S := ((SimplicialObject.Augmented.whiskeringObj _ _ (Over.forget B)).obj
    ((SimplicialObject.Augmented.whiskeringObj _ _ ev).obj X))
  let SLeft : SimplicialObject (CommAlgCat A) := X.left ⋙ ev ⋙ Over.forget B
  change Nonempty (S ≅ standardResolution A B)
  have hObj (n : SimplexCategory) :
      SLeft.obj (op n) = (standardResolution A B).left.obj (op n) := by
    change (Over.forget B).obj ((X.left.obj (op n)).obj I) = _
    exact (congrArg (fun F : Over B ⥤ Over B => (Over.forget B).obj (F.obj I)) (h n.len)).trans
      ((sliceIterate_forget A B (n.len + 1) I).trans (standardResolution_obj A B n.len).symm)
  let l := simplicialIsoOfFaces SLeft (standardResolution A B).left hObj
    (fun n j => sliceStandardResolution_face_comm A B hX n j _ _)
    (fun n j => sliceStandardResolution_degeneracy_comm A B hX n j _ _)
  have hr : S.right = B := by
    change (Over.forget B).obj (X.right.obj I) = B
    exact congrArg (fun F : Over B ⥤ Over B => (Over.forget B).obj (F.obj I)) hRight
  refine ⟨Comma.isoMk l (eqToIso hr) ?_⟩
  simp only [Functor.id_map]
  apply NatTrans.ext
  funext n
  let g : n ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ n.unop 0).op
  have h0 : l.hom.app (op ⦋0⦌) ≫ (standardResolution A B).hom.app (op ⦋0⦌) =
      S.hom.app (op ⦋0⦌) ≫ eqToHom hr :=
    sliceStandardResolution_augmentation_comm A B hX (hObj ⦋0⦌) hr
  have hStdNat : (standardResolution A B).left.map g ≫
      (standardResolution A B).hom.app (op ⦋0⦌) = (standardResolution A B).hom.app n := by
    simp
  have hSNat : SLeft.map g ≫ S.hom.app (op ⦋0⦌) = S.hom.app n :=
    (S.hom.naturality g).trans (Category.comp_id _)
  change l.hom.app n ≫ (standardResolution A B).hom.app n = S.hom.app n ≫ eqToHom hr
  rw [← hStdNat, ← reassoc_of% (l.hom.naturality g), h0]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom hr) hSNat)

end CommAlgCat

end

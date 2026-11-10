module

public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.Algebra.DGA.HomotopyCategoryShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.Abelian
public import StacksFrontier.Algebra.DifferentialGraded.Module.ConnectingHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DistinguishedTriangle
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeAdmissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeFunctorial
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeRotation
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeTriangle
public import StacksFrontier.CategoryTheory.EqToHomAbsorption
public import StacksCore.Tactic.StacksAttribute

/-! # The homotopy category of differential graded modules is pretriangulated

For a differential graded algebra `(A, d)` over a commutative ring `R`, the homotopy category
`K(A, d)` of right differential graded `A`-modules carries a pretriangulated structure: its
shift is the one induced by the signed shift of differential graded modules, and its
distinguished triangles are exactly the triangles of
`DifferentialGradedModule.IsDistinguishedTriangle`, namely those isomorphic to the triangle of
an admissible short exact sequence. This file supplies that structure, together with the
additivity instances on the homotopy quotient that it presupposes; the preadditive structure and
the zero object are the ones of `StacksFrontier.Algebra.DGA.HomotopyCategoryShift`.

## Main results

* `DifferentialGradedModule.exists_pretriangulated_structure`: a pretriangulated structure on
  `K(A, d)` whose distinguished triangles are precisely the designated ones.
* `DifferentialGradedModule.instPretriangulatedHomotopyCategory'`: that structure, as a
  definition which is *not* an instance; see the implementation notes.
* `DifferentialGradedModule.distinguishedTriangles_eq`: the distinguished triangles of that
  structure are the designated ones, which is what makes it usable.
* `DifferentialGradedModule.homotopyRel_add'`, together with
  `DifferentialGradedModule.instAdditiveToHomotopyCategory`,
  `DifferentialGradedModule.instAdditiveShiftFunctor` and
  `DifferentialGradedModule.instAdditiveShiftFunctorHomotopyCategory`: the additivity the
  pretriangulated axioms are stated against, over the preadditive structure
  `DifferentialGradedModule.instPreadditiveHomotopyCategory`.

## Implementation notes

The default pretriangulated structure on `K(A, d)` is the cone-triangle structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`
(`StacksFrontier.Algebra.DGA.Pretriangulated`). The structure of this file uses the other sign
convention for the third arrow, so it is a definition rather than a second global instance on the
same category: material stated against it activates it with
`attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'`,
and `StacksFrontier.Algebra.DGA.ConeSignClasses` compares the two classes of triangles.

`CategoryTheory.Pretriangulated` is data, so the structure is produced as an existential and
then chosen; no formula for it should be relied upon beyond
`DifferentialGradedModule.distinguishedTriangles_eq`, which is the only way clients should
recognise a distinguished triangle. The two octahedron-free axioms that do real work are
`distinguished_cocone_triangle`, discharged by the cone triangle of Tag 09KF, and
`rotate_distinguished_triangle`, discharged in one direction by the rotated cone triangle and
in the other by comparing the inverse rotation of Tag 09KC with Mathlib's `invRotate`.

The `unseal` of `CategoryTheory.HasShift.quotient` and `CategoryTheory.Quotient.functor_commShift`
records a gap in Mathlib: those two are sealed, so the fact that the homotopy quotient commutes
*strictly* with the shift —
`DifferentialGradedModule.toHomotopyCategory_commShiftIso_hom_app_eq_id` and its companions
below — is true by `rfl` but unprovable without unsealing them. Mathlib exposes no `simp`
lemma for the shift it induces on a quotient category.

Because of that gap the identity morphism supplied by
`DifferentialGradedModule.toHomotopyCategory_commShiftIso_hom_app_eq_id` sits at an object
that is only *definitionally* the source of whatever it is composed with, and
`Category.id_comp`, whose pattern needs those two objects to be syntactically equal, does not
apply. The four absorption
lemmas below — `DifferentialGradedModule.toHomotopyCategory_commShiftIso_hom_app_comp` and its
three companions — state the composite forms instead, so that a composite can be simplified in
term position, where the elaborator unfolds definitions fully. The same device for an `eqToHom`
rather than a `commShiftIso` component is
`CategoryTheory.eqToHom_comp_of_refl` (`StacksFrontier/CategoryTheory/EqToHomAbsorption.lean`).

## References

* [Stacks Project, Tag 09KH](https://stacks.math.columbia.edu/tag/09KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

section

unseal CategoryTheory.HasShift.quotient CategoryTheory.Quotient.functor_commShift

/-- The identification of objects along which the homotopy quotient commutes with the shift is
the identity: the quotient commutes with the shift strictly. -/
theorem quotient_shift_eqToHom_eq_id (X : DifferentialGradedModule A) (n : ℤ) :
    eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ X n).symm = 𝟙 _ := rfl

/-- The shift-commutation isomorphism of the homotopy quotient functor is the identity. -/
theorem toHomotopyCategory_commShiftIso_hom_app_eq_id (X : DifferentialGradedModule A) (n : ℤ) :
    ((toHomotopyCategory A).commShiftIso n).hom.app X = 𝟙 _ := rfl

/-- The inverse form of `toHomotopyCategory_commShiftIso_hom_app_eq_id`. -/
theorem toHomotopyCategory_commShiftIso_inv_app_eq_id (X : DifferentialGradedModule A) (n : ℤ) :
    ((toHomotopyCategory A).commShiftIso n).inv.app X = 𝟙 _ := rfl

/-- The shift-commutation isomorphism of the homotopy quotient functor, written as the object
identification of `CategoryTheory.Quotient.functor_obj_shift`. Unlike
`toHomotopyCategory_commShiftIso_hom_app_eq_id`, this form elaborates without unsealing the
shift on the quotient, so it is the one to use in a statement that must typecheck on its own. -/
theorem toHomotopyCategory_commShiftIso_hom_app_eq_eqToHom
    (X : DifferentialGradedModule A) (n : ℤ) :
    ((toHomotopyCategory A).commShiftIso n).hom.app X =
      eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ X n).symm := rfl

/-- The inverse form of `toHomotopyCategory_commShiftIso_hom_app_eq_eqToHom`. -/
theorem toHomotopyCategory_commShiftIso_inv_app_eq_eqToHom
    (X : DifferentialGradedModule A) (n : ℤ) :
    ((toHomotopyCategory A).commShiftIso n).inv.app X =
      eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ X n) := rfl

/-- The shift-commutation isomorphism of the homotopy quotient functor is absorbed on the left
of a composite. Mathlib offers no `simp` lemma for the shift it induces on a quotient category,
and the identity supplied by `toHomotopyCategory_commShiftIso_hom_app_eq_id` sits at an object
that is only *definitionally* the source of the rest of the composite, so `Category.id_comp`
cannot be applied to it directly; this form can. -/
theorem toHomotopyCategory_commShiftIso_hom_app_comp
    {X : DifferentialGradedModule A} (n : ℤ) {Z : HomotopyCategory A}
    (g : (CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙
      toHomotopyCategory A).obj X ⟶ Z) :
    ((toHomotopyCategory A).commShiftIso n).hom.app X ≫ g = g :=
  (congrArg (fun q => q ≫ g) (toHomotopyCategory_commShiftIso_hom_app_eq_id A X n)).trans
    (Category.id_comp g)

/-- The inverse of the shift-commutation isomorphism of the homotopy quotient functor is
absorbed on the right of a composite. -/
theorem comp_toHomotopyCategory_commShiftIso_inv_app
    {X : DifferentialGradedModule A} (n : ℤ) {W : HomotopyCategory A}
    (f : W ⟶ (CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙
      toHomotopyCategory A).obj X) :
    f ≫ ((toHomotopyCategory A).commShiftIso n).inv.app X = f :=
  (congrArg (fun q => f ≫ q) (toHomotopyCategory_commShiftIso_inv_app_eq_id A X n)).trans
    (Category.comp_id f)

/-- A shift of the shift-commutation isomorphism of the homotopy quotient functor is absorbed on
the left of a composite. -/
theorem toHomotopyCategory_commShiftIso_hom_app_shift_comp
    {X : DifferentialGradedModule A} (n m : ℤ) {Z : HomotopyCategory A}
    (g : (CategoryTheory.shiftFunctor (HomotopyCategory A) m).obj
      ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙
        toHomotopyCategory A).obj X) ⟶ Z) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) m).map
        (((toHomotopyCategory A).commShiftIso n).hom.app X) ≫ g = g :=
  (congrArg (fun q => (CategoryTheory.shiftFunctor (HomotopyCategory A) m).map q ≫ g)
      (toHomotopyCategory_commShiftIso_hom_app_eq_id A X n)).trans
    ((congrArg (fun q => q ≫ g)
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) m).map_id _)).trans
      (Category.id_comp g))

/-- A shift of the inverse of the shift-commutation isomorphism of the homotopy quotient functor
is absorbed on the right of a composite. -/
theorem comp_toHomotopyCategory_commShiftIso_inv_app_shift
    {X : DifferentialGradedModule A} (n m : ℤ) {W : HomotopyCategory A}
    (f : W ⟶ (CategoryTheory.shiftFunctor (HomotopyCategory A) m).obj
      ((toHomotopyCategory A ⋙
        CategoryTheory.shiftFunctor (HomotopyCategory A) n).obj X)) :
    f ≫ (CategoryTheory.shiftFunctor (HomotopyCategory A) m).map
        (((toHomotopyCategory A).commShiftIso n).inv.app X) = f :=
  (congrArg (fun q => f ≫ (CategoryTheory.shiftFunctor (HomotopyCategory A) m).map q)
      (toHomotopyCategory_commShiftIso_inv_app_eq_id A X n)).trans
    ((congrArg (fun q => f ≫ q)
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) m).map_id _)).trans
      (Category.comp_id f))

/-- The shift commutes strictly with the homotopy quotient functor on morphisms. -/
theorem toHomotopyCategory_map_shift {X Y : DifferentialGradedModule A} (h : X ⟶ Y) (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) n).map ((toHomotopyCategory A).map h) =
      (toHomotopyCategory A).map
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).map h) := rfl

end

section

unseal CategoryTheory.HasShift.quotient CategoryTheory.Quotient.functor_commShift

/-- Homotopy of homomorphisms of differential graded modules is compatible with addition, which
is what makes the homotopy category preadditive. -/
theorem homotopyRel_add'
    ⦃M N : DifferentialGradedModule A⦄
    (f₁ f₂ g₁ g₂ : M ⟶ N)
    (hf : homotopyRel A f₁ f₂)
    (hg : homotopyRel A g₁ g₂) :
    homotopyRel A (f₁ + g₁) (f₂ + g₂) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  refine ⟨{
    toLinearMap := hf.toLinearMap + hg.toLinearMap
    map_grading := ?_
    homotopy_eq := ?_ }⟩
  · intro n x hx
    simp only [LinearMap.add_apply]
    exact (N.grading (n - 1)).add_mem
      (hf.map_grading n x hx) (hg.map_grading n x hx)
  · intro x
    change (f₁.toFun x + g₁.toFun x) - (f₂.toFun x + g₂.toFun x) =
      N.d (hf.toLinearMap x + hg.toLinearMap x) +
        (hf.toLinearMap + hg.toLinearMap) (M.d x)
    rw [map_add, LinearMap.add_apply]
    calc
      _ = (f₁.toFun x - f₂.toFun x) + (g₁.toFun x - g₂.toFun x) := by abel
      _ = _ := by rw [hf.homotopy_eq x, hg.homotopy_eq x]; abel

/-- The homotopy quotient functor is additive. -/
instance instAdditiveToHomotopyCategory : (toHomotopyCategory A).Additive :=
  Quotient.functor_additive (homotopyRel A) (homotopyRel_add' A)

/-- Shifting differential graded modules by a fixed integer is an additive functor. -/
instance instAdditiveShiftFunctor (n : ℤ) :
    (CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).Additive where
  map_add := by
    intro M N f g
    apply Hom.ext
    rfl

/-- The shift induced on the homotopy category is additive. -/
noncomputable instance instAdditiveShiftFunctorHomotopyCategory (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) n).Additive where
  map_add := by
    intro M N f g
    induction f using Quot.inductionOn with
    | _ f =>
      induction g using Quot.inductionOn with
      | _ g =>
        change
          (CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
              ((toHomotopyCategory A).map (f + g)) =
            (CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
                ((toHomotopyCategory A).map f) +
              (CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
                ((toHomotopyCategory A).map g)
        let F := toHomotopyCategory A
        let e := F.commShiftIso n
        rw [← cancel_epi (e.hom.app M.as)]
        calc
          _ = F.map ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).map
              (f + g)) ≫ e.hom.app N.as :=
              (F.commShiftIso_hom_naturality (f + g) n).symm
          _ = (F.map ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).map f) ≫
                e.hom.app N.as) +
              (F.map ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).map g) ≫
                e.hom.app N.as) := by
                rw [Functor.map_add, Functor.map_add, Preadditive.add_comp]
          _ = (e.hom.app M.as ≫
                (CategoryTheory.shiftFunctor (HomotopyCategory A) n).map (F.map f)) +
              (e.hom.app M.as ≫
                (CategoryTheory.shiftFunctor (HomotopyCategory A) n).map (F.map g)) := by
                rw [F.commShiftIso_hom_naturality f n,
                  F.commShiftIso_hom_naturality g n]
          _ = _ := by rw [Preadditive.comp_add]

/-- Shifting in the homotopy category commutes strictly with the quotient on objects. -/
private theorem shiftFunctor_obj_toHomotopyCategory (X : DifferentialGradedModule A) (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory A) n).obj ((toHomotopyCategory A).obj X) =
      (toHomotopyCategory A).obj
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).obj X) := by
  simpa [HomotopyCategory] using CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ X n

/-- The sequence `X → X → 0` formed by the identity and the zero map is admissible short exact.
This is what makes Mathlib's contractible triangles distinguished. -/
theorem isAdmissibleShortExact_id_zero
    {X : DifferentialGradedModule A} :
    IsAdmissibleShortExact (𝟙 X) (0 : X ⟶ (0 : DifferentialGradedModule A)) := by
  let _ : Subsingleton (0 : DifferentialGradedModule A).M := by
    have hid : (𝟙 (0 : DifferentialGradedModule A) :
        Hom (0 : DifferentialGradedModule A) 0) = 0 :=
      (isZero_zero (DifferentialGradedModule A)).eq_of_src _ _
    refine ⟨fun x y => ?_⟩
    have hfun := congrArg Hom.toFun hid
    have hx := congrArg (fun f : (0 : DifferentialGradedModule A).M →ₗ[R]
        (0 : DifferentialGradedModule A).M => f x) hfun
    have hy := congrArg (fun f : (0 : DifferentialGradedModule A).M →ₗ[R]
        (0 : DifferentialGradedModule A).M => f y) hfun
    change x = 0 at hx
    change y = 0 at hy
    exact hx.trans hy.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ h => h
  · intro z
    exact ⟨0, Subsingleton.elim _ _⟩
  · change LinearMap.range (LinearMap.id : X.M →ₗ[R] X.M) =
      LinearMap.ker (0 : X.M →ₗ[R] (0 : DifferentialGradedModule A).M)
    simp
  · refine ⟨Hom.toGradedHom (𝟙 X), ?_⟩
    intro x
    rfl
  · refine ⟨{
      toFun := 0
      map_smul := by intros; simp
      map_grading := by intros; simp }, ?_⟩
    intro x
    exact Subsingleton.elim _ _


/-- Every cone triangle is distinguished: by Tag 09KF it is isomorphic to the triangle of an
admissible short exact sequence. -/
theorem isDistinguishedTriangle_mappingConeTriangle
    {K L : DifferentialGradedModule A} (f : K ⟶ L) :
    IsDistinguishedTriangle A (mappingConeTriangle f) := by
  obtain ⟨L', M', f', g', hfg, b, hfb, e, he₁, he₂⟩ :=
    exists_associatedTriangle_iso_mappingConeTriangle f
  exact isDistinguishedTriangle_of_iso A e
    (isDistinguishedTriangle_associatedTriangle A f' g' hfg)

/-- The inverse rotation of Tag 09KC of the triangle of an admissible short exact sequence is
isomorphic to Mathlib's `Pretriangulated.Triangle.invRotate` of that triangle. This is the
comparison that makes the rotation axiom hold in the backward direction. -/
theorem inverseRotatedAssociatedTriangle_iso_invRotate
    {K L M : DifferentialGradedModule A}
    (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    Nonempty (inverseRotatedAssociatedTriangle f g hfg ≅
      (associatedTriangle A f g hfg).invRotate) := by
  let T := associatedTriangle A f g hfg
  let U := inverseRotatedAssociatedTriangle f g hfg
  let F := toHomotopyCategory A
  let c := Classical.choice (nonempty_compatibleSplittings A f g hfg)
  let δ := (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val
  have hSplit : associatedTriangle A f g hfg =
      associatedTriangleOfSplittings A f g hfg c :=
    (associatedTriangleOfSplittings_eq A f g hfg c).symm
  let H : (n : ℤ) → ∀ (X Y : DifferentialGradedModule A)
      (f₁ f₂ : X ⟶ Y), homotopyRel A f₁ f₂ →
        (CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙ F).map f₁ =
          (CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙ F).map f₂ :=
    fun n _ _ f₁ f₂ hf => CategoryTheory.Quotient.sound
      (homotopyRel A)
      (HomRel.IsCompatibleWithShift.condition n f₁ f₂ hf)
  let s : ℤ → CategoryTheory.Functor
      (HomotopyCategory A)
      (HomotopyCategory A) := fun n =>
    CategoryTheory.Quotient.lift (homotopyRel A)
      (CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙ F)
      (H n)
  let i : ∀ n, F ⋙ s n ≅
      CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙ F := fun n =>
    CategoryTheory.Quotient.lift.isLift (homotopyRel A)
      (CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙ F) (H n)
  have hComm (n : ℤ) (X : DifferentialGradedModule A) :
      (F.commShiftIso n).hom.app X = 𝟙 _ := by
    exact toHomotopyCategory_commShiftIso_hom_app_eq_id A X n
  have hCommInv (n : ℤ) (X : DifferentialGradedModule A) :
      (F.commShiftIso n).inv.app X = 𝟙 _ := by
    exact toHomotopyCategory_commShiftIso_inv_app_eq_id A X n
  have hM := shiftFunctor_obj_toHomotopyCategory A M (-1)
  have hEqM : eqToHom hM.symm = 𝟙 _ := by
    cases hM
    rfl
  have hK1 := shiftFunctor_obj_toHomotopyCategory A (shift K 1) (-1)
  have hnat : F.map (shiftMap δ (-1)) ≫ eqToHom hK1.symm =
      eqToHom hM.symm ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map (F.map δ) := by
    have h := F.commShiftIso_hom_naturality δ (-1 : ℤ)
    change F.map (shiftMap δ (-1)) ≫ eqToHom hK1.symm =
      eqToHom hM.symm ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map (F.map δ) at h
    exact h
  have hCompHom : F.map
      ((shiftFunctorCompIsoId (DifferentialGradedModule A)
          (1 : ℤ) (-1) (by omega)).hom.app K) =
      (shiftFunctorCompIsoId (HomotopyCategory A)
        (1 : ℤ) (-1) (by omega)).hom.app (F.obj K) := by
    refine (Functor.map_shiftFunctorCompIsoId_hom_app F K (1 : ℤ) (-1 : ℤ)
      (by omega)).trans ?_
    refine (toHomotopyCategory_commShiftIso_hom_app_comp (A := A) (n := -1) _).trans ?_
    exact toHomotopyCategory_commShiftIso_hom_app_shift_comp (A := A) (n := 1) (m := -1) _
  have hCompInv : F.map
      ((shiftFunctorCompIsoId (DifferentialGradedModule A)
          (-1 : ℤ) 1 (by omega)).inv.app M) =
      (shiftFunctorCompIsoId (HomotopyCategory A)
        (-1 : ℤ) 1 (by omega)).inv.app (F.obj M) := by
    refine (Functor.map_shiftFunctorCompIsoId_inv_app F M (-1 : ℤ) 1 (by omega)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (comp_toHomotopyCategory_commShiftIso_inv_app (A := A) (n := 1) _).trans ?_
    exact comp_toHomotopyCategory_commShiftIso_inv_app_shift (A := A) (n := -1) (m := 1) _
  have hGamma : F.map (shiftAddInv A K 1 (-1) ≫
      shiftZeroHom A K) =
      (shiftFunctorCompIsoId (HomotopyCategory A)
        (1 : ℤ) (-1) (by omega)).hom.app (F.obj K) := by
    change F.map ((shiftFunctorCompIsoId
      (DifferentialGradedModule A) (1 : ℤ) (-1) (by omega)).hom.app K) = _
    exact hCompHom
  have hGammaInv : F.map (shiftZeroInv A M ≫
      shiftAddHom A M (-1) 1) =
      (shiftFunctorCompIsoId (HomotopyCategory A)
        (-1 : ℤ) 1 (by omega)).inv.app (F.obj M) := by
    change F.map ((shiftFunctorCompIsoId
      (DifferentialGradedModule A) (-1 : ℤ) 1 (by omega)).inv.app M) = _
    exact hCompInv
  have hFirst : F.map (desuspendedConnectingHom f g hfg) =
      eqToHom hM.symm ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map (F.map δ) ≫
          (shiftFunctorCompIsoId (HomotopyCategory A)
          (1 : ℤ) (-1) (by omega)).hom.app (F.obj K) := by
    change F.map (shiftMap δ (-1) ≫
        shiftAddInv A K 1 (-1) ≫ shiftZeroHom A K) = _
    simp only [Functor.map_comp]
    calc
      _ = (F.map (shiftMap δ (-1)) ≫ eqToHom hK1.symm) ≫
          eqToHom hK1 ≫ F.map (shiftAddInv A K 1 (-1) ≫
            shiftZeroHom A K) := by simp
      _ = (eqToHom hM.symm ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map
            (F.map δ)) ≫ eqToHom hK1 ≫
            F.map (shiftAddInv A K 1 (-1) ≫
              shiftZeroHom A K) := by rw [hnat]
      _ = eqToHom hM.symm ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map
            (F.map δ) ≫
            (shiftFunctorCompIsoId (HomotopyCategory A)
              (1 : ℤ) (-1) (by omega)).hom.app (F.obj K) := by
          simp only [hGamma, Category.assoc]
          exact congrArg (fun q => eqToHom hM.symm ≫
            (CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map (F.map δ) ≫ q)
            (CategoryTheory.eqToHom_comp_of_refl _ _)
  have hLast : F.map (resuspensionHom M) ≫
      eqToHom (CategoryTheory.Quotient.functor_obj_shift
        (homotopyRel A) ℤ (shift M (-1)) 1).symm =
      (shiftFunctorCompIsoId (HomotopyCategory A)
        (-1 : ℤ) 1 (by omega)).inv.app (F.obj M) := by
    refine (CategoryTheory.comp_eqToHom_of_refl _ _).trans ?_
    simpa [resuspensionHom, shiftZeroInv,
      shiftAddHom, Functor.map_comp] using hGammaInv
  have hLast' : F.map (resuspensionHom M) ≫
      eqToHom (CategoryTheory.Quotient.functor_obj_shift
        (homotopyRel A) ℤ (shift M (-1)) 1).symm =
      (shiftEquiv (HomotopyCategory A) (1 : ℤ)).counitIso.inv.app
        (F.obj M) := by
    change _ = (shiftFunctorCompIsoId
      (HomotopyCategory A) (-1 : ℤ) 1 (by omega)).inv.app (F.obj M)
    exact hLast
  have hShiftObj : shift M (-1) =
      ((instHasShift (A := A)).shift.obj ⟨(-1 : ℤ)⟩).obj M := by
    rfl
  let e₁ : U.obj₁ ≅ T.invRotate.obj₁ := by
    dsimp [U, T, inverseRotatedAssociatedTriangle,
      associatedTriangle, associatedTriangleOfSplittings,
      Pretriangulated.Triangle.invRotate]
    exact (F.commShiftIso (-1)).app M
  have he₁ : e₁.hom = 𝟙 _ := by
    dsimp [e₁]
    exact hComm (-1) M
  have heCast : e₁.hom = eqToHom hM.symm := by
    rw [he₁]
    exact hEqM.symm
  have hTmor₃ : T.mor₃ =
      F.map δ ≫ eqToHom (CategoryTheory.Quotient.functor_obj_shift
        (homotopyRel A) ℤ K 1).symm := by
    dsimp [T, associatedTriangle,
      associatedTriangleOfSplittings, δ]
  have hIso₁ : U.mor₁ ≫ (𝟙 U.obj₂) = e₁.hom ≫ T.invRotate.mor₁ := by
    rw [he₁]
    dsimp only [U, inverseRotatedAssociatedTriangle,
      Pretriangulated.Triangle.invRotate, Pretriangulated.Triangle.mk]
    simp only [Category.comp_id, Functor.map_neg]
    have hp : F.map (desuspendedConnectingHom f g hfg) =
        e₁.hom ≫ ((CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map T.mor₃ ≫
          (shiftFunctorCompIsoId (HomotopyCategory A)
            (1 : ℤ) (-1) (by omega)).hom.app T.obj₁) := by
      rw [← heCast] at hFirst
      rw [hTmor₃]
      change F.map (desuspendedConnectingHom f g hfg) =
        e₁.hom ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory A) (-1)).map (F.map δ) ≫
          (shiftFunctorCompIsoId (HomotopyCategory A)
            (1 : ℤ) (-1) (by omega)).hom.app (F.obj K)
      exact hFirst
    rw [he₁] at hp
    rw [hp]
    simp only [Int.reduceNeg, Functor.id_obj, Functor.comp_obj, shiftEquiv'_unitIso,
      Iso.symm_inv]
    exact (congrArg (fun q => -q) (Category.id_comp _)).trans (Category.id_comp _).symm
  refine ⟨Pretriangulated.Triangle.isoMk U T.invRotate e₁ (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_⟩
  · exact hIso₁
  · simp [U, T, inverseRotatedAssociatedTriangle,
      associatedTriangle, associatedTriangleOfSplittings,
      Pretriangulated.Triangle.invRotate]
  · have h3 := congrArg (fun q => T.mor₂ ≫ q) hLast'
    have hshiftId : ∀ {W : HomotopyCategory A}
        (q : W ⟶ (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).obj U.obj₁),
        q ≫ (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map e₁.hom = q := by
      intro W q
      refine (congrArg (fun z => q ≫ (CategoryTheory.shiftFunctor (HomotopyCategory A)
        (1 : ℤ)).map z) he₁).trans ?_
      exact (congrArg (fun z => q ≫ z)
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map_id _)).trans
        (Category.comp_id q)
    refine (hshiftId U.mor₃).trans ?_
    refine Eq.trans ?_ (Category.id_comp T.invRotate.mor₃).symm
    simp only [Pretriangulated.Triangle.invRotate_mor₃, Int.reduceNeg] at h3 ⊢
    exact h3

/-- The rotation of a cone triangle is distinguished: it is the triangle of the admissible short
exact sequence `L → C(f) → K[1]` of Tag 09KB. -/
theorem isDistinguishedTriangle_mappingConeTriangle_rotate
    {K L : DifferentialGradedModule A} (f : K ⟶ L) :
    IsDistinguishedTriangle A
      ((mappingConeTriangle f).rotate) := by
  let h := mappingCone_isAdmissibleShortExact f
  let Tpos := Pretriangulated.Triangle.mk
    ((toHomotopyCategory A).map (coneInclusion f))
    ((toHomotopyCategory A).map (coneProjection f))
    ((toHomotopyCategory A).map (shiftMap f 1) ≫
      eqToHom (CategoryTheory.Quotient.functor_obj_shift
        (homotopyRel A) ℤ L 1).symm)
  let F := toHomotopyCategory A
  have hK := shiftFunctor_obj_toHomotopyCategory A K 1
  have hL := shiftFunctor_obj_toHomotopyCategory A L 1
  let e₃ : ((mappingConeTriangle f).rotate).obj₃ ≅ Tpos.obj₃ := by
    change (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).obj
        (F.obj K) ≅ F.obj ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) (1 : ℤ)).obj K)
    exact {
      hom := -(𝟙 _) ≫ eqToHom hK
      inv := eqToHom hK.symm ≫ (-(𝟙 _))
      hom_inv_id := by simp
      inv_hom_id := by simp }
  have e : (mappingConeTriangle f).rotate ≅ Tpos := by
    refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e₃ ?_ ?_ ?_
    · simp [Tpos, mappingConeTriangle, Pretriangulated.Triangle.rotate]
    · dsimp [Tpos, mappingConeTriangle, Pretriangulated.Triangle.rotate, coneProjection]
      change -(F.map (coneProjection f)) ≫ (-(𝟙 (F.obj (shift K 1)))) =
        F.map (coneProjection f)
      exact (Preadditive.neg_comp_neg (f := F.map (coneProjection f))
        (g := 𝟙 (F.obj (shift K 1)))).trans (Category.comp_id _)
    · dsimp [Tpos, mappingConeTriangle, Pretriangulated.Triangle.rotate]
      have hmap : (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map
          (F.map f) ≫ eqToHom hL = eqToHom hK ≫ F.map (shiftMap f 1) :=
        (CategoryTheory.comp_eqToHom_of_refl _ _).trans ((toHomotopyCategory_map_shift A f 1).trans
          (CategoryTheory.eqToHom_comp_of_refl _ _).symm)
      change -((CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map (F.map f)) ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map (𝟙 (F.obj L)) =
        (-(𝟙 _) ≫ eqToHom hK) ≫ F.map (shiftMap f 1) ≫ eqToHom hL.symm
      calc
        -((CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map (F.map f)) =
          -(((CategoryTheory.shiftFunctor (HomotopyCategory A)
              (1 : ℤ)).map (F.map f) ≫ eqToHom hL) ≫ eqToHom hL.symm) := by simp
        _ = -((eqToHom hK ≫ F.map (shiftMap f 1)) ≫ eqToHom hL.symm) := by rw [hmap]
        _ = _ := by simp
  exact isDistinguishedTriangle_of_iso A
    ((eqToIso (associatedTriangle_mappingCone_eq f h)).symm ≪≫ e.symm)
    (isDistinguishedTriangle_associatedTriangle A (coneInclusion f) (coneProjection f) h)

/-- There is a pretriangulated structure on the homotopy category of differential
graded modules whose distinguished triangles are precisely those arising from
admissible short exact sequences. -/
@[stacks 09KH]
theorem exists_pretriangulated_structure :
    ∃ p : Pretriangulated (HomotopyCategory A),
      p.distinguishedTriangles = {T | IsDistinguishedTriangle A T} := by
  let p : Pretriangulated (HomotopyCategory A) := {
    distinguishedTriangles := {T | IsDistinguishedTriangle A T}
    isomorphic_distinguished := fun _ hT₁ _ e => isDistinguishedTriangle_of_iso A e.symm hT₁
    contractible_distinguished := by
      intro X
      have h := isAdmissibleShortExact_id_zero (A := A) (X := X.as)
      let T := associatedTriangle A (𝟙 X.as) 0 h
      have hzero : IsZero T.obj₃ := by
        change IsZero ((toHomotopyCategory A).obj (0 : DifferentialGradedModule A))
        exact (toHomotopyCategory A).map_isZero (isZero_zero _)
      have e : T ≅ Pretriangulated.contractibleTriangle X := by
        refine Pretriangulated.Triangle.isoMk T _ (Iso.refl _) (Iso.refl _)
          (hzero.iso (isZero_zero (HomotopyCategory A))) ?_ ?_ ?_
        · simp [T, associatedTriangle, associatedTriangleOfSplittings,
            Pretriangulated.contractibleTriangle]
        · simp [T, associatedTriangle, associatedTriangleOfSplittings,
            Pretriangulated.contractibleTriangle]
        · exact hzero.eq_of_src _ _
      exact isDistinguishedTriangle_of_iso A e
        (isDistinguishedTriangle_associatedTriangle A (𝟙 X.as) 0 h)
    distinguished_cocone_triangle := by
      intro X Y f
      induction f using Quot.inductionOn with
      | _ f => exact ⟨_, _, _, isDistinguishedTriangle_mappingConeTriangle A f⟩
    rotate_distinguished_triangle := by
      intro T
      constructor
      · rintro ⟨K, L, M, f, g, hfg, ⟨eT⟩⟩
        obtain ⟨_, _, ec, _⟩ := exists_mappingConeTriangle_iso_associatedTriangle f g hfg
        exact isDistinguishedTriangle_of_iso A
          ((Pretriangulated.rotate (HomotopyCategory A)).mapIso (eT ≪≫ ec.symm)).symm
          (isDistinguishedTriangle_mappingConeTriangle_rotate A f)
      · rintro ⟨K, L, M, f, g, hfg, ⟨eT⟩⟩
        obtain ⟨e⟩ := inverseRotatedAssociatedTriangle_iso_mappingConeTriangle f g hfg
        have eInv : T ≅ inverseRotatedAssociatedTriangle f g hfg :=
          (Pretriangulated.rotCompInvRot (C := HomotopyCategory A)).app T ≪≫
            (Pretriangulated.invRotate (HomotopyCategory A)).mapIso eT ≪≫
              (inverseRotatedAssociatedTriangle_iso_invRotate A f g hfg).some.symm
        exact isDistinguishedTriangle_of_iso A eInv.symm
          (isDistinguishedTriangle_of_iso A e.symm
            (isDistinguishedTriangle_mappingConeTriangle A _))
    complete_distinguished_triangle_morphism := by
      intro T₁ T₂ hT₁ hT₂ a b hab
      rcases hT₁ with ⟨K₁, L₁, M₁, f₁, g₁, hfg₁, ⟨eT₁⟩⟩
      rcases hT₂ with ⟨K₂, L₂, M₂, f₂, g₂, hfg₂, ⟨eT₂⟩⟩
      obtain ⟨_, _, eC₁, he₁₁, he₁₂, _⟩ :=
        exists_mappingConeTriangle_iso_associatedTriangle f₁ g₁ hfg₁
      obtain ⟨_, _, eC₂, he₂₁, he₂₂, _⟩ :=
        exists_mappingConeTriangle_iso_associatedTriangle f₂ g₂ hfg₂
      let ψ₁ : T₁ ≅ mappingConeTriangle f₁ := eT₁ ≪≫ eC₁.symm
      let ψ₂ : T₂ ≅ mappingConeTriangle f₂ := eT₂ ≪≫ eC₂.symm
      let aC := ψ₁.inv.hom₁ ≫ a ≫ ψ₂.hom.hom₁
      let bC := ψ₁.inv.hom₂ ≫ b ≫ ψ₂.hom.hom₂
      have hC : (mappingConeTriangle f₁).mor₁ ≫ bC = aC ≫ (mappingConeTriangle f₂).mor₁ := by
        dsimp only [aC, bC]
        rw [reassoc_of% ψ₁.inv.comm₁, reassoc_of% hab, ψ₂.hom.comm₁]
        simp only [Category.assoc]
      have hcompl : ∀
          (a : (mappingConeTriangle f₁).obj₁ ⟶ (mappingConeTriangle f₂).obj₁)
          (b : (mappingConeTriangle f₁).obj₂ ⟶ (mappingConeTriangle f₂).obj₂)
          (hab : (mappingConeTriangle f₁).mor₁ ≫ b = a ≫ (mappingConeTriangle f₂).mor₁),
          ∃ c : (mappingConeTriangle f₁).obj₃ ⟶ (mappingConeTriangle f₂).obj₃,
            (mappingConeTriangle f₁).mor₂ ≫ c = b ≫ (mappingConeTriangle f₂).mor₂ ∧
              (mappingConeTriangle f₁).mor₃ ≫
                  (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map a =
                c ≫ (mappingConeTriangle f₂).mor₃ := by
        intro a b hab
        let F := toHomotopyCategory A
        obtain ⟨a', ha'⟩ :=
          (CategoryTheory.Quotient.full_functor (homotopyRel A)).map_surjective a
        obtain ⟨b', hb'⟩ :=
          (CategoryTheory.Quotient.full_functor (homotopyRel A)).map_surjective b
        have hRep : F.map (f₁ ≫ b') = F.map (a' ≫ f₂) := by
          rw [Functor.map_comp, Functor.map_comp, ha', hb']
          exact hab
        obtain ⟨c, hc₁, hc₂⟩ := exists_mappingConeMap_of_homotopic_square f₁ f₂ a' b'
          ((CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ _).mp hRep)
        have hNeg : F.map (-coneProjection f₁) ≫ F.map (shiftMap a' 1) =
            F.map c ≫ F.map (-coneProjection f₂) := by
          have h' : (-coneProjection f₁) ≫ shiftMap a' 1 = c ≫ (-coneProjection f₂) := by
            simpa only [Preadditive.comp_neg, Preadditive.neg_comp] using
              (congrArg (fun q => -q) hc₂).symm
          simpa only [Functor.map_comp] using congrArg F.map h'
        have hShiftSimple : (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map
            (F.map a') = F.map (shiftMap a' 1) := toHomotopyCategory_map_shift A a' 1
        refine ⟨F.map c, ?_, ?_⟩
        · change F.map (coneInclusion f₁) ≫ F.map c = b ≫ F.map (coneInclusion f₂)
          rw [← hb']
          exact congrArg F.map hc₁
        · dsimp [mappingConeTriangle]
          refine Eq.trans (congrArg (fun q => q ≫ _)
            (CategoryTheory.comp_eqToHom_of_refl _ _)) ?_
          refine Eq.trans ?_ (congrArg (fun q => _ ≫ q)
            (CategoryTheory.comp_eqToHom_of_refl _ _)).symm
          change F.map (-coneProjection f₁) ≫
              (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map a =
            F.map c ≫ F.map (-coneProjection f₂)
          rw [← ha']
          change F.map (-coneProjection f₁) ≫
              (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map (F.map a') =
            F.map c ≫ F.map (-coneProjection f₂)
          exact (congrArg (fun q => F.map (-coneProjection f₁) ≫ q) hShiftSimple).trans hNeg
      obtain ⟨c, hc₂, hc₃⟩ := hcompl aC bC hC
      let m := ψ₁.hom ≫ Pretriangulated.Triangle.homMk _ _ aC bC c hC hc₂ hc₃ ≫ ψ₂.inv
      have hm₁ : m.hom₁ = a := by simp [m, aC, ψ₁, ψ₂]
      have hm₂ : m.hom₂ = b := by simp [m, bC, ψ₁, ψ₂]
      refine ⟨m.hom₃, ?_, ?_⟩
      · rw [← hm₂]
        exact m.comm₂
      · rw [← hm₁]
        exact m.comm₃
  }
  exact ⟨p, rfl⟩

/-- The admissible-sequence pretriangulated structure on the homotopy category of differential
graded modules, chosen from `exists_pretriangulated_structure`: its distinguished triangles are
`DifferentialGradedModule.IsDistinguishedTriangle`, the triangles isomorphic to the triangle of an
*admissible short exact sequence* (`DifferentialGradedModule.distinguishedTriangles_eq` below).

This is **not** an instance. The default pretriangulated structure on the homotopy category is
the cone-triangle structure `DifferentialGradedModule.instPretriangulatedHomotopyCategory`, whose
distinguished triangles are `DifferentialGradedModule.distinguishedConeTriangles`. The two
classes are the two sign conventions for the third arrow: a triangle is distinguished for this
structure exactly when negating its third arrow gives a distinguished triangle for the cone
structure (`DifferentialGradedModule.mem_distinguishedTriangles_admissible_iff`), so the two
need not agree and a statement made against one is not a statement about the other. Material
written against this convention activates it explicitly, with
`attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'`
in a section of its own. -/
@[reducible] noncomputable def instPretriangulatedHomotopyCategory' :
    Pretriangulated (HomotopyCategory A) :=
  Classical.choose (exists_pretriangulated_structure A)

/-- The distinguished triangles of the admissible-sequence pretriangulated structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` are exactly the triangles of
`IsDistinguishedTriangle`. This is how a client recognises a distinguished triangle; no
other property of the chosen structure should be relied upon. -/
theorem distinguishedTriangles_eq :
    (instPretriangulatedHomotopyCategory' A).distinguishedTriangles =
      {T | IsDistinguishedTriangle A T} :=
  Classical.choose_spec (exists_pretriangulated_structure A)

end

end DifferentialGradedModule

module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorShift

/-!
# Tensoring with a bimodule is exact on homotopy categories

Tensoring with a differential graded `(A, B)`-bimodule `N` induces an exact — that is,
triangulated — functor between the triangulated homotopy categories of differential graded
modules.

## Main results

* `DifferentialGraded.Bimodule.tensorHomotopyFunctor_isTriangulated'`: the tensor functor on
  homotopy categories commutes with translation and preserves distinguished triangles.

## Implementation notes

*The shift.* The two equivalences out of which `tensorHomotopyFunctor` is built are the identity
on objects, so the ordinary tensor functor agrees on objects with the differential graded functor
of Tag 09LM and the sign-free comparison `(M ⊗_A N)[k] ≅ M[k] ⊗_A N` of Tag 0FQN supplies the
components of a shift-commutation isomorphism. Its naturality and its compatibility with
`shiftFunctorZero` and `shiftFunctorAdd` are equalities of morphisms out of a tensor product, so
all three are checked on pure tensors, where every structural map in sight is the identity. The
tool for that is `DifferentialGraded.Bimodule.tensorObj_hom_ext'`, the uniqueness half of the
universal property of Tag 09LM. The result is then transported to the homotopy category by
presenting the functor as a quotient lift, which is where the compatibility of Tag 09LM with the
quotient is used.

*The triangles.* A distinguished triangle is, by Tag 09K8, isomorphic to the triangle of an
admissible short exact sequence, so it suffices to carry such a triangle to such a triangle. The
point is that admissibility is witnessed by splittings `s` and `π` that are maps of *graded*
modules, not homomorphisms of differential graded modules — but the differential graded functor
acts on homogeneous morphisms of every degree, so it transports them, and admissibility of the
image is then a formal consequence of the identities `π f = 𝟙`, `g s = 𝟙` and `𝟙 = f π + s g`.
Writing the connecting homomorphism as the degree-one homogeneous map `π ∘ d_L ∘ s` of the
differential graded category makes it transportable in the same way, because the functor commutes
with the differential of the Hom-complexes; `tensor_connectingHom` then identifies the image with
the connecting homomorphism of the image sequence, up to the shift comparison above. No
construction on mapping cones is needed.

*Reducibility.* Comparing the shift of the homotopy category with the shift of differential
graded modules across the quotient functor needs Mathlib's sealed `HasShift.quotient` and
`Quotient.functor_commShift`, exactly as in
`StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated`; the triangle section therefore
runs under a section-scoped `unseal` of those two definitions and of nothing else.

## Naming

The three primed names here — `DifferentialGraded.Bimodule.tensorObj_hom_ext'`,
`DifferentialGraded.Bimodule.tensorCompFunctor_map_pure'` and
`DifferentialGraded.Bimodule.tensorHomotopyFunctor_isTriangulated'` — are primed to keep them
apart from the homonymous declarations in
`StacksFrontier/Algebra/DGA/BimoduleTensorExact.lean`, a parallel
treatment of the same tag. The first two are the same statements at a different spelling of
the tensor product; the third is genuinely a different statement, since it asserts exactness
against `DifferentialGradedModule.instPretriangulatedHomotopyCategory'` (admissible short
exact sequences) rather than against the cone-triangle structure that file uses.

## References

* [Stacks Project, Tag 09LR](https://stacks.math.columbia.edu/tag/09LR)
-/

@[expose] public section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

open DifferentialGradedModule

/-- The balanced bilinear map obtained by composing the universal pure tensor of `M ⊗_A N` with
a homomorphism out of it. -/
private noncomputable def pureComp (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule.{u, u, u} B}
    (g : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P) :
    BalancedBilinearMap M N P where
  toLinearMap := LinearMap.compr₂ ((tensorDGFunctor N).pure M).toLinearMap g.toFun
  map_grading p q x y :=
    g.map_grading (p + q) _ (((tensorDGFunctor N).pure M).map_grading p q x y)
  map_d p x y := by
    have hd : g.toFun (((tensorDGFunctor N).functor.obj M).d
        (((tensorDGFunctor N).pure M).toLinearMap x y)) =
        P.d (g.toFun (((tensorDGFunctor N).pure M).toLinearMap x y)) :=
      LinearMap.congr_fun g.map_d _
    change P.d (g.toFun (((tensorDGFunctor N).pure M).toLinearMap x y)) = _
    rw [← hd, ((tensorDGFunctor N).pure M).map_d p x y, map_add, map_zsmul]
    rfl
  balance p q n x y a := congrArg g.toFun
    (((tensorDGFunctor N).pure M).balance p q n x y a)
  map_right x y b := by
    change g.toFun (((tensorDGFunctor N).pure M).toLinearMap x (MulOpposite.op b • y)) = _
    rw [((tensorDGFunctor N).pure M).map_right x y b, g.map_smul]
    rfl

/-- **Extensionality for the relative tensor product.** Two homomorphisms out of `M ⊗_A N` that
agree on every pure tensor are equal: this is the uniqueness half of the universal property of
Tag 09LM. -/
theorem tensorObj_hom_ext' (N : Bimodule A B) (M : DifferentialGradedModule A)
    {P : DifferentialGradedModule.{u, u, u} B}
    (g h : DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M) P)
    (H : ∀ (x : M.M) (y : N.rightModule.M),
      g.toFun (((tensorDGFunctor N).pure M).toLinearMap x y) =
        h.toFun (((tensorDGFunctor N).pure M).toLinearMap x y)) :
    g = h := by
  obtain ⟨_, _, huniq⟩ := (tensorDGFunctor N).universal M P (pureComp N M g)
  exact (huniq g (fun _ _ => rfl)).trans (huniq h (fun x y => (H x y).symm)).symm

/-- The ordinary tensor functor acts on pure tensors through the first factor only. -/
theorem tensorCompFunctor_map_pure' (N : Bimodule A B)
    {L M : DifferentialGradedModule A} (f : L ⟶ M) (x : L.M) (y : N.rightModule.M) :
    ((tensorCompFunctor N).map f).toFun (((tensorDGFunctor N).pure L).toLinearMap x y) =
      ((tensorDGFunctor N).pure M).toLinearMap (f.toFun x) y :=
  (tensorDGFunctor N).map_pure (cocycleOfHom A f).1 x y

/-- The shift comparison of Tag 0FQN, read through its inverse: it is the identity on pure
tensors in that direction too. -/
theorem tensorShiftIso_inv_pure (N : Bimodule A B) (M : DifferentialGradedModule A) (k : ℤ)
    (x : M.M) (y : N.rightModule.M) :
    (tensorShiftIso N M k).1.inv.toFun
        (((tensorDGFunctor N).pure (shift M k)).toLinearMap x y) =
      ((tensorDGFunctor N).pure M).toLinearMap x y := by
  have hid : ∀ z, (tensorShiftIso N M k).1.inv.toFun
      ((tensorShiftIso N M k).1.hom.toFun z) = z := by
    intro z
    exact LinearMap.congr_fun
      (congrArg DifferentialGradedModule.Hom.toFun (tensorShiftIso N M k).1.hom_inv_id) z
  have h := congrArg (tensorShiftIso N M k).1.inv.toFun ((tensorShiftIso N M k).2 x y)
  rw [hid] at h
  exact h.symm

section ShiftStructure

variable (A)

/-- The unit isomorphism `M[0] ≅ M` of the shift on differential graded `A`-modules is the
identity on underlying elements. -/
theorem shiftFunctorZero_hom_toFun (M : DifferentialGradedModule A) (x : M.M) :
    ((shiftFunctorZero (DifferentialGradedModule A) ℤ).hom.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The inverse of the unit isomorphism `M[0] ≅ M` of the shift on differential graded
`A`-modules is the identity on underlying elements. -/
theorem shiftFunctorZero_inv_toFun (M : DifferentialGradedModule A) (x : M.M) :
    ((shiftFunctorZero (DifferentialGradedModule A) ℤ).inv.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The additivity isomorphism `M[a + b] ≅ M[a][b]` of the shift on differential graded
`A`-modules is the identity on underlying elements. -/
theorem shiftFunctorAdd_hom_toFun (M : DifferentialGradedModule A) (a b : ℤ)
    (x : M.M) :
    ((shiftFunctorAdd (DifferentialGradedModule A) a b).hom.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

/-- The inverse of the additivity isomorphism `M[a + b] ≅ M[a][b]` of the shift on differential
graded `A`-modules is the identity on underlying elements. -/
theorem shiftFunctorAdd_inv_toFun (M : DifferentialGradedModule A) (a b : ℤ)
    (x : M.M) :
    ((shiftFunctorAdd (DifferentialGradedModule A) a b).inv.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

end ShiftStructure

/-- The shift comparison of the ordinary tensor functor, as a natural isomorphism: the component
at `M` is the inverse of the sign-free comparison `(M ⊗_A N)[n] ≅ M[n] ⊗_A N` of Tag 0FQN.
Naturality is checked on pure tensors, where every map in sight is the identity. -/
noncomputable def tensorCompCommShiftIso' (N : Bimodule A B) (n : ℤ) :
    CategoryTheory.shiftFunctor (DifferentialGradedModule A) n ⋙ tensorCompFunctor N ≅
      tensorCompFunctor N ⋙ CategoryTheory.shiftFunctor (DifferentialGradedModule B) n :=
  NatIso.ofComponents (fun M => (tensorShiftIso N M n).1.symm) (by
    intro M M' f
    refine tensorObj_hom_ext' N (shift M n) _ _ ?_
    intro x y
    change (tensorShiftIso N M' n).1.inv.toFun
        (((tensorCompFunctor N).map (shiftMap f n)).toFun
          (((tensorDGFunctor N).pure (shift M n)).toLinearMap x y)) =
      ((tensorCompFunctor N).map f).toFun
        ((tensorShiftIso N M n).1.inv.toFun
          (((tensorDGFunctor N).pure (shift M n)).toLinearMap x y))
    rw [tensorCompFunctor_map_pure', tensorShiftIso_inv_pure, tensorShiftIso_inv_pure,
      tensorCompFunctor_map_pure']
    rfl)

/-- **The ordinary tensor functor commutes with the shift.** Both compatibilities are equalities
of morphisms out of a tensor product, so both are checked on pure tensors, where every
structural map involved is the identity. -/
@[instance_reducible, ega "II 2.1.2" "special case"]
noncomputable instance tensorCompFunctorCommShift' (N : Bimodule A B) :
    (tensorCompFunctor N).CommShift ℤ where
  commShiftIso := tensorCompCommShiftIso' N
  commShiftIso_zero := by
    ext M
    refine tensorObj_hom_ext' N (shift M 0) _ _ ?_
    intro x y
    have h1 : ((tensorCompFunctor N).map
          ((shiftFunctorZero (DifferentialGradedModule A) ℤ).hom.app M)).toFun
        (((tensorDGFunctor N).pure (shift M 0)).toLinearMap x y) =
        ((tensorDGFunctor N).pure M).toLinearMap x y :=
      (tensorCompFunctor_map_pure' N _ x y).trans
        (congrArg (fun z => ((tensorDGFunctor N).pure M).toLinearMap z y)
          (shiftFunctorZero_hom_toFun A M x))
    have hR := (congrArg (fun z => ((shiftFunctorZero (DifferentialGradedModule B) ℤ).inv.app
          ((tensorDGFunctor N).functor.obj M)).toFun z) h1).trans
      (shiftFunctorZero_inv_toFun B ((tensorDGFunctor N).functor.obj M)
        (((tensorDGFunctor N).pure M).toLinearMap x y))
    rw [Functor.CommShift.isoZero_hom_app]
    exact (tensorShiftIso_inv_pure N M 0 x y).trans hR.symm
  commShiftIso_add a b := by
    ext M
    refine tensorObj_hom_ext' N (shift M (a + b)) _ _ ?_
    intro x y
    have h1 : ((tensorCompFunctor N).map
          ((shiftFunctorAdd (DifferentialGradedModule A) a b).hom.app M)).toFun
        (((tensorDGFunctor N).pure (shift M (a + b))).toLinearMap x y) =
        ((tensorDGFunctor N).pure (shift (shift M a) b)).toLinearMap x y :=
      (tensorCompFunctor_map_pure' N _ x y).trans
        (congrArg (fun z => ((tensorDGFunctor N).pure (shift (shift M a) b)).toLinearMap z y)
          (shiftFunctorAdd_hom_toFun A M a b x))
    have h2 := (congrArg (fun z => ((tensorShiftIso N (shift M a) b).1.inv).toFun z) h1).trans
      (tensorShiftIso_inv_pure N (shift M a) b x y)
    have h3 := (congrArg (fun z => ((tensorShiftIso N M a).1.inv).toFun z) h2).trans
      (tensorShiftIso_inv_pure N M a x y)
    have h4 := (congrArg (fun z => ((shiftFunctorAdd (DifferentialGradedModule B) a b).inv.app
          ((tensorDGFunctor N).functor.obj M)).toFun z) h3).trans
      (shiftFunctorAdd_inv_toFun B ((tensorDGFunctor N).functor.obj M) a b
        (((tensorDGFunctor N).pure M).toLinearMap x y))
    rw [Functor.CommShift.isoAdd_hom_app]
    exact (tensorShiftIso_inv_pure N M (a + b) x y).trans h4.symm

/-- Tensoring and then passing to homotopy classes identifies homotopic morphisms. This is read
off from the compatibility of Tag 09LM with the quotient: the composite is isomorphic to one
that factors through the homotopy category of `A`. -/
theorem tensorComp_quotient_respects_homotopy (N : Bimodule A B)
    (X Y : DifferentialGradedModule A) (f₁ f₂ : X ⟶ Y) (h : homotopyRel A f₁ f₂) :
    (tensorCompFunctor N ⋙ toHomotopyCategory B).map f₁ =
      (tensorCompFunctor N ⋙ toHomotopyCategory B).map f₂ := by
  have e := tensorCompFunctor_quotient N
  have key : ∀ f : X ⟶ Y, (tensorCompFunctor N ⋙ toHomotopyCategory B).map f =
      (e.hom.app X ≫ (toHomotopyCategory A ⋙ tensorHomotopyFunctor N).map f) ≫ e.inv.app Y := by
    intro f
    rw [← e.hom.naturality f, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hq : (toHomotopyCategory A ⋙ tensorHomotopyFunctor N).map f₁ =
      (toHomotopyCategory A ⋙ tensorHomotopyFunctor N).map f₂ := by
    change (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map f₁) =
      (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map f₂)
    rw [CategoryTheory.Quotient.sound (homotopyRel A) h]
  rw [key f₁, key f₂, hq]

/-- The tensor functor on homotopy categories, presented as a lift through the quotient. -/
noncomputable abbrev tensorHomotopyLift (N : Bimodule A B) :
    HomotopyCategory A ⥤ HomotopyCategory B :=
  CategoryTheory.Quotient.lift (homotopyRel A) (tensorCompFunctor N ⋙ toHomotopyCategory B)
    (tensorComp_quotient_respects_homotopy N)

/-- The lift agrees with the tensor functor of Tag 09LM on homotopy categories. -/
noncomputable def tensorHomotopyLiftIso (N : Bimodule A B) :
    tensorHomotopyLift N ≅ tensorHomotopyFunctor N :=
  CategoryTheory.Quotient.natIsoLift _
    (CategoryTheory.Quotient.lift.isLift (homotopyRel A)
        (tensorCompFunctor N ⋙ toHomotopyCategory B)
        (tensorComp_quotient_respects_homotopy N) ≪≫
      tensorCompFunctor_quotient N)

/-- **The tensor functor on homotopy categories commutes with translation.** -/
@[instance_reducible]
noncomputable instance tensorHomotopyLiftCommShift (N : Bimodule A B) :
    (tensorHomotopyLift N).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift
    (tensorCompFunctor N ⋙ toHomotopyCategory B) (homotopyRel A) ℤ
    (tensorComp_quotient_respects_homotopy N)

/-- **The tensor functor on homotopy categories commutes with translation.** -/
@[instance_reducible]
noncomputable def tensorHomotopyCommShift (N : Bimodule A B) :
    (tensorHomotopyFunctor N).CommShift ℤ :=
  Functor.CommShift.ofIso (tensorHomotopyLiftIso N) ℤ

/-! ### Transport of graded maps along the tensor functor

An admissible short exact sequence is split by maps of *graded* modules, which are not
homomorphisms of differential graded modules. The tensor differential graded functor nevertheless
acts on them, because it acts on homogeneous morphisms of every degree; that is what makes
admissibility, and with it the class of distinguished triangles, survive tensoring. -/

/-- A degree-zero graded map, read as a homogeneous morphism of the differential graded
category. -/
private def gradedToHomogeneous {X Y : DifferentialGradedModule A} (u : GradedHom X Y) :
    HomogeneousMap A X Y 0 :=
  ⟨u.toFun, fun i x hx => by simpa using u.map_grading i x hx, fun a x => u.map_smul x a⟩

/-- The image of a degree-zero graded map under the tensor differential graded functor, again as
a graded map. -/
private noncomputable def tensorGradedHom (N : Bimodule A B)
    {X Y : DifferentialGradedModule A} (u : GradedHom X Y) :
    GradedHom ((tensorDGFunctor N).functor.obj X) ((tensorDGFunctor N).functor.obj Y) where
  toFun := ((tensorDGFunctor N).functor.map (gradedToHomogeneous u)).1
  map_smul x a := ((tensorDGFunctor N).functor.map (gradedToHomogeneous u)).2.2 a x
  map_grading n x hx := by
    simpa using ((tensorDGFunctor N).functor.map (gradedToHomogeneous u)).2.1 n x hx

/-- The image of a graded map acts on pure tensors through the first factor. -/
private theorem tensorGradedHom_pure (N : Bimodule A B)
    {X Y : DifferentialGradedModule A} (u : GradedHom X Y)
    (x : X.M) (y : N.rightModule.M) :
    (tensorGradedHom N u).toFun (((tensorDGFunctor N).pure X).toLinearMap x y) =
      ((tensorDGFunctor N).pure Y).toLinearMap (u.toFun x) y :=
  (tensorDGFunctor N).map_pure (gradedToHomogeneous u) x y

/-- The tensor functor preserves composition of homogeneous degree-zero maps. -/
private theorem tensorMap_comp (N : Bimodule A B) {X Y Z : DifferentialGradedModule A}
    (v : HomogeneousMap A Y Z 0) (u : HomogeneousMap A X Y 0)
    (x : ((tensorDGFunctor N).functor.obj X).M) :
    ((tensorDGFunctor N).functor.map
        ((dgCategory A).comp (show (0 : ℤ) + 0 = 0 from rfl) v u)).1 x =
      ((tensorDGFunctor N).functor.map v).1 (((tensorDGFunctor N).functor.map u).1 x) := by
  rw [(tensorDGFunctor N).functor.map_comp]
  rfl

/-- The tensor functor preserves identities. -/
private theorem tensorMap_id (N : Bimodule A B) (X : DifferentialGradedModule A)
    (x : ((tensorDGFunctor N).functor.obj X).M) :
    ((tensorDGFunctor N).functor.map ((dgCategory A).id X)).1 x = x := by
  rw [(tensorDGFunctor N).functor.map_id]
  rfl

/-- If two homogeneous degree-zero maps compose to a third, so do their images. -/
private theorem tensorMap_comp_eq (N : Bimodule A B) {X Y Z : DifferentialGradedModule A}
    (v : HomogeneousMap A Y Z 0) (u : HomogeneousMap A X Y 0) (w : HomogeneousMap A X Z 0)
    (h : ∀ x : X.M, v.1 (u.1 x) = w.1 x)
    (x : ((tensorDGFunctor N).functor.obj X).M) :
    ((tensorDGFunctor N).functor.map v).1 (((tensorDGFunctor N).functor.map u).1 x) =
      ((tensorDGFunctor N).functor.map w).1 x := by
  have hcomp : (dgCategory A).comp (show (0 : ℤ) + 0 = 0 from rfl) v u = w :=
    Subtype.ext (LinearMap.ext h)
  rw [← tensorMap_comp N v u x, hcomp]

/-- The tensor functor kills the zero homogeneous map. -/
private theorem tensorMap_zero (N : Bimodule A B) {X Y : DifferentialGradedModule A} (n : ℤ)
    (x : ((tensorDGFunctor N).functor.obj X).M) :
    ((tensorDGFunctor N).functor.map (0 : HomogeneousMap A X Y n)).1 x = 0 := by
  rw [(tensorDGFunctor N).functor.map_zero]
  rfl

/-- If two homogeneous degree-zero maps compose to zero, so do their images. -/
private theorem tensorMap_comp_eq_zero (N : Bimodule A B) {X Y Z : DifferentialGradedModule A}
    (v : HomogeneousMap A Y Z 0) (u : HomogeneousMap A X Y 0)
    (h : ∀ x : X.M, v.1 (u.1 x) = 0)
    (x : ((tensorDGFunctor N).functor.obj X).M) :
    ((tensorDGFunctor N).functor.map v).1 (((tensorDGFunctor N).functor.map u).1 x) = 0 :=
  (tensorMap_comp_eq N v u 0 h x).trans (tensorMap_zero N 0 x)

/-- A two-term identity between composites of homogeneous degree-zero maps transports through
the tensor functor; this is what carries the splitting `𝟙 = f π + s g` to the image. -/
private theorem tensorMap_add_comp_eq (N : Bimodule A B)
    {W X Y Z : DifferentialGradedModule A}
    (v₁ : HomogeneousMap A Y X 0) (u₁ : HomogeneousMap A W Y 0)
    (v₂ : HomogeneousMap A Z X 0) (u₂ : HomogeneousMap A W Z 0)
    (w : HomogeneousMap A W X 0)
    (h : ∀ x : W.M, v₁.1 (u₁.1 x) + v₂.1 (u₂.1 x) = w.1 x)
    (x : ((tensorDGFunctor N).functor.obj W).M) :
    ((tensorDGFunctor N).functor.map v₁).1 (((tensorDGFunctor N).functor.map u₁).1 x) +
        ((tensorDGFunctor N).functor.map v₂).1 (((tensorDGFunctor N).functor.map u₂).1 x) =
      ((tensorDGFunctor N).functor.map w).1 x := by
  have hsum : (dgCategory A).comp (show (0 : ℤ) + 0 = 0 from rfl) v₁ u₁ +
      (dgCategory A).comp (show (0 : ℤ) + 0 = 0 from rfl) v₂ u₂ = w :=
    Subtype.ext (LinearMap.ext h)
  rw [← tensorMap_comp N v₁ u₁ x, ← tensorMap_comp N v₂ u₂ x, ← hsum,
    (tensorDGFunctor N).functor.map_add]
  rfl

/-! ### The image of an admissible short exact sequence -/

section ImageSequence

variable (N : Bimodule A B) {K L M : DifferentialGradedModule A}

/-- Compatible splittings satisfy `π ∘ s = 0`. -/
private theorem compatibleSplittings_pi_s {f : K ⟶ L} {g : L ⟶ M}
    (c : CompatibleSplittings A f g) (x : M.M) : c.π.toFun (c.s.toFun x) = 0 := by
  apply LinearMap.mem_ker.mp
  rw [c.hker]
  exact ⟨x, rfl⟩

/-- The image of the retraction retracts the image of `f`. -/
private theorem tensor_pi_f {f : K ⟶ L} {g : L ⟶ M} (c : CompatibleSplittings A f g)
    (x : ((tensorDGFunctor N).functor.obj K).M) :
    (tensorGradedHom N c.π).toFun (((tensorCompFunctor N).map f).toFun x) = x :=
  (tensorMap_comp_eq N (gradedToHomogeneous c.π) (cocycleOfHom A f).1
    ((dgCategory A).id K) c.hπ x).trans (tensorMap_id N K x)

/-- The image of the section sections the image of `g`. -/
private theorem tensor_g_s {f : K ⟶ L} {g : L ⟶ M} (c : CompatibleSplittings A f g)
    (x : ((tensorDGFunctor N).functor.obj M).M) :
    ((tensorCompFunctor N).map g).toFun ((tensorGradedHom N c.s).toFun x) = x :=
  (tensorMap_comp_eq N (cocycleOfHom A g).1 (gradedToHomogeneous c.s)
    ((dgCategory A).id M) c.hs x).trans (tensorMap_id N M x)

/-- The image splittings remain compatible. -/
private theorem tensor_pi_s {f : K ⟶ L} {g : L ⟶ M} (c : CompatibleSplittings A f g)
    (x : ((tensorDGFunctor N).functor.obj M).M) :
    (tensorGradedHom N c.π).toFun ((tensorGradedHom N c.s).toFun x) = 0 :=
  tensorMap_comp_eq_zero N (gradedToHomogeneous c.π) (gradedToHomogeneous c.s)
    (compatibleSplittings_pi_s c) x

/-- The image composite `g ∘ f` is still zero. -/
private theorem tensor_g_f {f : K ⟶ L} {g : L ⟶ M} (hfg : IsAdmissibleShortExact f g)
    (x : ((tensorDGFunctor N).functor.obj K).M) :
    ((tensorCompFunctor N).map g).toFun (((tensorCompFunctor N).map f).toFun x) = 0 :=
  tensorMap_comp_eq_zero N (cocycleOfHom A g).1 (cocycleOfHom A f).1
    (fun z => by
      change g.toFun (f.toFun z) = 0
      apply LinearMap.mem_ker.mp
      rw [← hfg.exact]
      exact ⟨z, rfl⟩) x

/-- The graded splitting `𝟙 = f π + s g` of the sequence survives tensoring. -/
private theorem tensor_decomposition {f : K ⟶ L} {g : L ⟶ M}
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g)
    (x : ((tensorDGFunctor N).functor.obj L).M) :
    ((tensorDGFunctor N).functor.map (cocycleOfHom A f).1).1
          (((tensorDGFunctor N).functor.map (gradedToHomogeneous c.π)).1 x) +
        ((tensorDGFunctor N).functor.map (gradedToHomogeneous c.s)).1
          (((tensorDGFunctor N).functor.map (cocycleOfHom A g).1).1 x) = x :=
  (tensorMap_add_comp_eq N (cocycleOfHom A f).1 (gradedToHomogeneous c.π)
    (gradedToHomogeneous c.s) (cocycleOfHom A g).1 ((dgCategory A).id L)
    (c.decomposition hfg) x).trans (tensorMap_id N L x)

/-- **Tensoring with a bimodule preserves admissible short exact sequences.** Every part of
admissibility is formal consequence of the graded splitting, which the differential graded
functor transports because it acts on graded maps as well as on homomorphisms. -/
private theorem tensor_isAdmissibleShortExact {f : K ⟶ L} {g : L ⟶ M}
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) :
    IsAdmissibleShortExact ((tensorCompFunctor N).map f) ((tensorCompFunctor N).map g) where
  injective x₁ x₂ h := by
    rw [← tensor_pi_f N c x₁, ← tensor_pi_f N c x₂, h]
  surjective z := ⟨(tensorGradedHom N c.s).toFun z, tensor_g_s N c z⟩
  exact := by
    apply le_antisymm
    · rintro z ⟨w, rfl⟩
      exact LinearMap.mem_ker.mpr (tensor_g_f N hfg w)
    · intro z hz
      refine ⟨(tensorGradedHom N c.π).toFun z, ?_⟩
      have hzero : ((tensorDGFunctor N).functor.map (cocycleOfHom A g).1).1 z = 0 :=
        LinearMap.mem_ker.mp hz
      have hd := tensor_decomposition N hfg c z
      simp only [hzero, map_zero, add_zero] at hd
      exact hd
  admissibleMono := ⟨tensorGradedHom N c.π, tensor_pi_f N c⟩
  admissibleEpi := ⟨tensorGradedHom N c.s, tensor_g_s N c⟩

/-- The image compatible splittings. -/
private noncomputable def tensorCompatibleSplittings {f : K ⟶ L} {g : L ⟶ M}
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) :
    CompatibleSplittings B ((tensorCompFunctor N).map f) ((tensorCompFunctor N).map g) where
  s := tensorGradedHom N c.s
  π := tensorGradedHom N c.π
  hs := tensor_g_s N c
  hπ := tensor_pi_f N c
  hker := by
    apply le_antisymm
    · intro z hz
      refine ⟨((tensorCompFunctor N).map g).toFun z, ?_⟩
      have hzero : ((tensorDGFunctor N).functor.map (gradedToHomogeneous c.π)).1 z = 0 :=
        LinearMap.mem_ker.mp hz
      have hd := tensor_decomposition N hfg c z
      simp only [hzero, map_zero, zero_add] at hd
      exact hd
    · rintro z ⟨w, rfl⟩
      exact LinearMap.mem_ker.mpr (tensor_pi_s N c w)

end ImageSequence

/-! ### The connecting homomorphism of the image sequence -/

section ConnectingHom

variable (N : Bimodule A B) {K L M : DifferentialGradedModule A}
  {f : K ⟶ L} {g : L ⟶ M}

/-- The degree-one homogeneous map `π ∘ d_L ∘ s` of the differential graded category. Writing the
connecting homomorphism this way is what lets the differential graded functor be applied to it:
the functor acts on homogeneous morphisms of every degree, and commutes with the differential of
the Hom-complexes. -/
private noncomputable def connectingHomogeneous (c : CompatibleSplittings A f g) :
    HomogeneousMap A M K 1 :=
  (dgCategory A).comp (show (0 : ℤ) + 1 = 1 from rfl) (gradedToHomogeneous c.π)
    ((dgCategory A).d (gradedToHomogeneous c.s))

/-- Its underlying linear map is the connecting homomorphism. -/
private theorem connectingHomogeneous_val (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) (x : M.M) :
    (connectingHomogeneous c).1 x =
      (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun x := by
  refine Eq.trans ?_ ((connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).property x).symm
  change c.π.toFun (((dgCategory A).d (gradedToHomogeneous c.s)).1 x) = _
  rw [dgCategory_d_val]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, DifferentialGraded.gradedSign_zero,
    one_smul, map_sub]
  change c.π.toFun (L.d (c.s.toFun x)) - c.π.toFun (c.s.toFun (M.d x)) = _
  rw [compatibleSplittings_pi_s c, sub_zero]

/-- The same computation after applying the tensor functor: the image of `π ∘ d_L ∘ s` is
`π' ∘ d ∘ s'`, which is the connecting homomorphism of the image sequence. -/
private theorem tensor_connectingHom_toFun (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g)
    (z : ((tensorDGFunctor N).functor.obj M).M) :
    (connectingHom ((tensorCompFunctor N).map f) ((tensorCompFunctor N).map g)
        (tensor_isAdmissibleShortExact N hfg c)
        (tensorGradedHom N c.s) (tensorGradedHom N c.π)
        (tensor_g_s N c) (tensor_pi_f N c)
        (tensorCompatibleSplittings N hfg c).hker).val.toFun z =
      ((tensorDGFunctor N).functor.map (connectingHomogeneous c)).1 z := by
  refine ((connectingHom ((tensorCompFunctor N).map f) ((tensorCompFunctor N).map g)
    (tensor_isAdmissibleShortExact N hfg c) (tensorGradedHom N c.s) (tensorGradedHom N c.π)
    (tensor_g_s N c) (tensor_pi_f N c)
    (tensorCompatibleSplittings N hfg c).hker).property z).trans ?_
  rw [connectingHomogeneous, (tensorDGFunctor N).functor.map_comp, dgCategory_comp_val,
    (tensorDGFunctor N).functor.map_d, dgCategory_d_val]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, DifferentialGraded.gradedSign_zero,
    one_smul, map_sub]
  change _ = (tensorGradedHom N c.π).toFun (((tensorDGFunctor N).functor.obj L).d
      ((tensorGradedHom N c.s).toFun z)) -
    (tensorGradedHom N c.π).toFun
      ((tensorGradedHom N c.s).toFun (((tensorDGFunctor N).functor.obj M).d z))
  rw [tensor_pi_s N c, sub_zero]
  rfl

/-- **The connecting homomorphism of the image sequence is the image of the connecting
homomorphism**, read through the sign-free shift comparison of Tag 0FQN. -/
private theorem tensor_connectingHom (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) :
    (connectingHom ((tensorCompFunctor N).map f) ((tensorCompFunctor N).map g)
        (tensor_isAdmissibleShortExact N hfg c)
        (tensorGradedHom N c.s) (tensorGradedHom N c.π)
        (tensor_g_s N c) (tensor_pi_f N c)
        (tensorCompatibleSplittings N hfg c).hker).val =
      (tensorCompFunctor N).map
          (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val ≫
        (tensorShiftIso N K 1).1.inv := by
  refine tensorObj_hom_ext' N M _ _ ?_
  intro x y
  refine (tensor_connectingHom_toFun N hfg c _).trans ?_
  rw [(tensorDGFunctor N).map_pure (connectingHomogeneous c) x y,
    connectingHomogeneous_val hfg c x]
  change _ = (tensorShiftIso N K 1).1.inv.toFun
    (((tensorCompFunctor N).map
      (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val).toFun
        (((tensorDGFunctor N).pure M).toLinearMap x y))
  rw [tensorCompFunctor_map_pure', tensorShiftIso_inv_pure]

end ConnectingHom

/-! ### Preservation of distinguished triangles -/

section Triangles

variable (N : Bimodule A B) {K L M : DifferentialGradedModule A}
  {f : K ⟶ L} {g : L ⟶ M}

unseal CategoryTheory.HasShift.quotient CategoryTheory.Quotient.functor_commShift

/-- The image of the triangle of an admissible short exact sequence is the triangle of the image
sequence. All three vertices agree on the nose, because the lift of the tensor functor commutes
strictly with the homotopy quotient; only the connecting arrow needs an argument, and that is
`tensor_connectingHom`. -/
private noncomputable def tensorMapTriangleIso (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) :
    (tensorHomotopyLift N).mapTriangle.obj (associatedTriangleOfSplittings A f g hfg c) ≅
      associatedTriangleOfSplittings B ((tensorCompFunctor N).map f)
        ((tensorCompFunctor N).map g) (tensor_isAdmissibleShortExact N hfg c)
        (tensorCompatibleSplittings N hfg c) := by
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have hδ := tensor_connectingHom N hfg c
    set ι := (tensorShiftIso N K 1).1.inv with hιdef
    set δ := (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val with hδdef
    have hmap : (toHomotopyCategory B).map
          (connectingHom ((tensorCompFunctor N).map f) ((tensorCompFunctor N).map g)
            (tensor_isAdmissibleShortExact N hfg c) (tensorGradedHom N c.s)
            (tensorGradedHom N c.π) (tensor_g_s N c) (tensor_pi_f N c)
            (tensorCompatibleSplittings N hfg c).hker).val =
        (toHomotopyCategory B).map ((tensorCompFunctor N).map δ) ≫
          (toHomotopyCategory B).map ι := by
      rw [hδ]
      exact (toHomotopyCategory B).map_comp _ _
    have hC : (Functor.commShiftIso (tensorCompFunctor N ⋙ toHomotopyCategory B)
        (1 : ℤ)).hom.app K = (toHomotopyCategory B).map ι := by
      rw [Functor.commShiftIso_comp_hom_app]
      erw [toHomotopyCategory_commShiftIso_hom_app_eq_id B ((tensorCompFunctor N).obj K) 1,
        Category.comp_id]
      rfl
    have hcs : ((tensorHomotopyLift N).commShiftIso (1 : ℤ)).hom.app
        ((toHomotopyCategory A).obj K) = (toHomotopyCategory B).map ι := by
      rw [CategoryTheory.Quotient.liftCommShift_commShiftIso,
        CategoryTheory.Quotient.LiftCommShift.iso_hom_app,
        toHomotopyCategory_commShiftIso_inv_app_eq_id, hC]
      exact (congrArg (fun u => u ≫ (toHomotopyCategory B).map ι)
        ((tensorHomotopyLift N).map_id _)).trans (Category.id_comp _)
    simp only [Iso.refl_hom]
    erw [(CategoryTheory.shiftFunctor (HomotopyCategory B) (1 : ℤ)).map_id, Category.comp_id,
      Category.id_comp]
    change (tensorHomotopyLift N).map
          ((toHomotopyCategory A).map δ ≫
            eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ K 1).symm) ≫
          ((tensorHomotopyLift N).commShiftIso (1 : ℤ)).hom.app
            ((toHomotopyCategory A).obj K) =
        (toHomotopyCategory B).map
            (connectingHom ((tensorCompFunctor N).map f) ((tensorCompFunctor N).map g)
              (tensor_isAdmissibleShortExact N hfg c) (tensorGradedHom N c.s)
              (tensorGradedHom N c.π) (tensor_g_s N c) (tensor_pi_f N c)
              (tensorCompatibleSplittings N hfg c).hker).val ≫
          eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel B) ℤ
            ((tensorCompFunctor N).obj K) 1).symm
    rw [quotient_shift_eqToHom_eq_id, quotient_shift_eqToHom_eq_id, hcs, hmap]
    erw [Category.comp_id, Category.comp_id]
    rfl

end Triangles

/-- The lift of the tensor functor to the homotopy category is triangulated: every distinguished
triangle is isomorphic to the triangle of an admissible short exact sequence, and such a triangle
is carried to the triangle of the image sequence. -/
instance tensorHomotopyLift_isTriangulated (N : Bimodule A B) :
    (tensorHomotopyLift N).IsTriangulated where
  map_distinguished T hT := by
    rw [distinguishedTriangles_eq] at hT ⊢
    obtain ⟨K, L, M, f, g, hfg, ⟨e⟩⟩ := hT
    let c := Classical.choice (nonempty_compatibleSplittings A f g hfg)
    have hT' : T ≅ associatedTriangleOfSplittings A f g hfg c :=
      e ≪≫ (eqToIso (associatedTriangleOfSplittings_eq A f g hfg c)).symm
    refine isDistinguishedTriangle_of_iso B
      (((tensorHomotopyLift N).mapTriangle.mapIso hT' ≪≫
        tensorMapTriangleIso N hfg c).symm) ?_
    exact isDistinguishedTriangle_associatedTriangleOfSplittings B _ _ _ _

/-- **Stacks 09LR.** Tensoring with a differential graded `(A, B)`-bimodule is an exact functor
from the homotopy category of differential graded `A`-modules to that of differential graded
`B`-modules: it commutes with translation and carries distinguished triangles to distinguished
triangles. -/
@[stacks 09LR]
theorem tensorHomotopyFunctor_isTriangulated' (N : Bimodule A B) :
    ∃ h : (tensorHomotopyFunctor N).CommShift ℤ,
      letI := h
      (tensorHomotopyFunctor N).IsTriangulated := by
  refine ⟨tensorHomotopyCommShift N, ?_⟩
  let _ := tensorHomotopyCommShift N
  let _ : NatTrans.CommShift (tensorHomotopyLiftIso N).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (tensorHomotopyLiftIso N) ℤ
  exact Functor.isTriangulated_of_iso (tensorHomotopyLiftIso N)

end DifferentialGraded.Bimodule

module

public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory

/-!
# Changing the base ring of a differential graded algebra

Let `S → R` be a homomorphism of commutative rings and let `(A, d)` be a differential graded
algebra over `R`. Then `(A, d)` is also a differential graded algebra over `S`: the same ring,
the same grading and the same differential, with `S` acting through `R`. A right differential
graded `A`-module is the same thing over `R` as over `S`, because the `R`-module structure of a
differential graded module is forced: `r` acts as right multiplication by the central element
`algebraMap R A r`, which lies in degree `0` and is closed. This file makes both statements
precise: forgetting the `R`-module structure down to `S` is an equivalence between the
categories of differential graded modules over the two algebras, with inverse letting `R` act
through the algebra, and both functors preserve homotopies, so they descend to the homotopy
categories.

## Main definitions

* `DifferentialGradedAlgebra.restrictBase`: a differential graded algebra over `R`, regarded
  over `S`.
* `DifferentialGradedAlgebra.Hom.restrictBase` and `DifferentialGradedAlgebra.restrictBaseFunctor`:
  the same on homomorphisms, functorially.
* `DifferentialGradedModule.restrictBaseObj` and `DifferentialGradedModule.restrictBase`: a
  differential graded `A`-module, with its `R`-module structure forgotten down to `S`, and the
  functor this defines.
* `DifferentialGradedModule.extendBaseObj` and `DifferentialGradedModule.extendBase`: a
  differential graded module over `A` regarded over `S`, with `R` acting through `algebraMap R A`,
  and the functor this defines.
* `DifferentialGradedModule.restrictBaseEquiv`: the two are inverse equivalences.
* `DifferentialGradedModule.restrictBaseHomotopyFunctor` and
  `DifferentialGradedModule.extendBaseHomotopyFunctor`: the induced functors between the homotopy
  categories, and `DifferentialGradedModule.restrictBaseHomotopyEquiv`, the equivalence they form.

## Main results

* `DifferentialGradedAlgebra.d_algebraMap`: the differential kills the image of the base ring.
* `DifferentialGradedModule.Homotopy.restrictBase` and
  `DifferentialGradedModule.Homotopy.extendBase`: both functors preserve homotopies.

## Implementation notes

The `S`-algebra structure of `A` is `Algebra.compHom`, and the `S`-module structure of a module is
`Module.compHom`; the gradings are the restrictions of scalars of the given ones, so that their
carriers, and hence their direct-sum decompositions, are literally the given ones. In the other
direction the `R`-module structure is `Module.compHom` along `algebraMap R Aᵐᵒᵖ`, and its graded
pieces are the given additive subgroups, which are closed under it because `algebraMap R A r` lies
in degree `0`. In neither direction does the underlying type, the right action, the grading as a
set or the differential change, so every homomorphism and every homotopy is carried by its
underlying map.

## References

* [Stacks Project, Tag 061V](https://stacks.math.columbia.edu/tag/061V)
* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u' v w

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (S : Type u') [CommRing S] [Algebra S R]

/-- The differential of a differential graded algebra kills the unit. -/
private theorem d_one_eq_zero_aux (A : DifferentialGradedAlgebra.{u, v} R) : A.d 1 = 0 := by
  simpa using A.leibniz 0 0 1 1 (SetLike.one_mem_graded A.grading)
    (SetLike.one_mem_graded A.grading)

/-- The differential of a differential graded algebra kills the image of the base ring. -/
theorem d_algebraMap (A : DifferentialGradedAlgebra.{u, v} R) (r : R) :
    A.d (algebraMap R A.A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, d_one_eq_zero_aux, smul_zero]

/-- A differential graded algebra over `R`, regarded as a differential graded algebra over `S`
through `algebraMap S R`: the same ring, grading and differential. -/
@[implicit_reducible]
def restrictBase (A : DifferentialGradedAlgebra.{u, v} R) :
    DifferentialGradedAlgebra.{u', v} S :=
  letI : Algebra S A.A := Algebra.compHom A.A (algebraMap S R)
  haveI : IsScalarTower S R A.A :=
    ⟨fun s r a => by rw [Algebra.smul_def s r, mul_smul]; rfl⟩
  { A := A.A
    isAlg := Algebra.compHom A.A (algebraMap S R)
    grading := fun n => (A.grading n).restrictScalars S
    gradedAlg :=
      { one_mem := (SetLike.one_mem_graded A.grading :)
        mul_mem := fun _ _ _ _ ha hb => (SetLike.mul_mem_graded (A := A.grading) ha hb :)
        decompose' := DirectSum.Decomposition.decompose' (ℳ := A.grading)
        left_inv := DirectSum.Decomposition.left_inv (ℳ := A.grading)
        right_inv := DirectSum.Decomposition.right_inv (ℳ := A.grading) }
    d := A.d.restrictScalars S
    d_comp_d := by
      ext a
      exact LinearMap.congr_fun A.d_comp_d a
    d_mem := A.d_mem
    leibniz := A.leibniz }

variable (A : DifferentialGradedAlgebra.{u, v} R)

/-- The scalar action of `S` on the algebra regarded over `S` is that of its image in `R`. -/
theorem restrictBase_smul (s : S) (a : (A.restrictBase S).A) :
    s • a = (algebraMap S R s • (show A.A from a) : A.A) := rfl

/-- The structure map of the algebra regarded over `S` factors through `R`. -/
theorem restrictBase_algebraMap (s : S) :
    (show A.A from algebraMap S (A.restrictBase S).A s) = algebraMap R A.A (algebraMap S R s) :=
  rfl

variable {A}

/-- A homomorphism of differential graded algebras over `R`, regarded over `S`. -/
def Hom.restrictBase {B : DifferentialGradedAlgebra.{u, v} R} (φ : A.Hom B) :
    (A.restrictBase S).Hom (B.restrictBase S) where
  toAlgebraHom :=
    { toRingHom := φ.toAlgebraHom.toRingHom
      commutes' := fun s => φ.toAlgebraHom.commutes (algebraMap S R s) }
  map_grading := φ.map_grading
  map_d := φ.map_d

/-- The homomorphism regarded over `S` has the same underlying map. -/
@[simp]
theorem Hom.restrictBase_apply {B : DifferentialGradedAlgebra.{u, v} R} (φ : A.Hom B)
    (a : A.A) : (φ.restrictBase S).toAlgebraHom a = φ.toAlgebraHom a := rfl

/-- Regarding differential graded algebras over `S`, as a functor. -/
@[simps]
def restrictBaseFunctor {R S : Type u} [CommRing R] [CommRing S] [Algebra S R] :
    DifferentialGradedAlgebra.{u, u} R ⥤ DifferentialGradedAlgebra.{u, u} S where
  obj A := A.restrictBase S
  map φ := Hom.restrictBase S φ
  map_id _ := rfl
  map_comp _ _ := rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (S : Type u') [CommRing S] [Algebra S R]
  {A : DifferentialGradedAlgebra.{u, v} R}

section restrictBase

/-- A differential graded `A`-module with its `R`-module structure forgotten down to `S`: a
differential graded module over `A` regarded over `S`. -/
@[implicit_reducible]
def restrictBaseObj (M : DifferentialGradedModule.{u, v, w} A) :
    DifferentialGradedModule.{u', v, w} (A.restrictBase S) :=
  letI : Module S M.M := Module.compHom M.M (algebraMap S R)
  letI : Module (MulOpposite (A.restrictBase S).A) M.M := M.rmodule
  haveI : IsScalarTower S R M.M :=
    ⟨fun s r x => by rw [Algebra.smul_def s r, mul_smul]; rfl⟩
  haveI : IsScalarTower S (MulOpposite (A.restrictBase S).A) M.M :=
    ⟨fun s a x => by
      change (algebraMap S R s • (show MulOpposite A.A from a)) • x =
        algebraMap S R s • (show MulOpposite A.A from a) • x
      exact smul_assoc _ _ _⟩
  { M := M.M
    rmodule := M.rmodule
    grading := fun n => (M.grading n).restrictScalars S
    decomposition :=
      { decompose' := DirectSum.Decomposition.decompose' (ℳ := M.grading)
        left_inv := DirectSum.Decomposition.left_inv (ℳ := M.grading)
        right_inv := DirectSum.Decomposition.right_inv (ℳ := M.grading) }
    smul_mem := M.smul_mem
    d := M.d.restrictScalars S
    d_comp_d := by
      ext x
      exact LinearMap.congr_fun M.d_comp_d x
    d_mem := M.d_mem
    leibniz := M.leibniz }

/-- The scalar action of `S` on a module regarded over `S` is that of its image in `R`. -/
theorem restrictBaseObj_smul (M : DifferentialGradedModule.{u, v, w} A) (s : S)
    (x : (restrictBaseObj S M).M) : s • x = (algebraMap S R s • (show M.M from x) : M.M) := rfl

/-- A homomorphism of differential graded `A`-modules, regarded over `S`. -/
def restrictBaseHom {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    restrictBaseObj S M ⟶ restrictBaseObj S N where
  toFun :=
    { toFun := f.toFun
      map_add' := f.toFun.map_add
      map_smul' := fun s x => f.toFun.map_smul (algebraMap S R s) x }
  map_smul := f.map_smul
  map_grading := f.map_grading
  map_d := by
    ext x
    exact LinearMap.congr_fun f.map_d x

variable (A) in
/-- Regarding differential graded `A`-modules over `S`, as a functor
`Mod_(A, d) ⥤ Mod_(A_S, d)`. -/
def restrictBase :
    DifferentialGradedModule.{u, v, w} A ⥤ DifferentialGradedModule.{u', v, w} (A.restrictBase S)
    where
  obj M := restrictBaseObj S M
  map f := restrictBaseHom S f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor regarding over `S` acts on objects by `restrictBaseObj`. -/
@[simp]
theorem restrictBase_obj (M : DifferentialGradedModule.{u, v, w} A) :
    (restrictBase S A).obj M = restrictBaseObj S M := rfl

end restrictBase

section extendBase

/-- The structure map `R → Aᵐᵒᵖ` through which a differential graded module over `A` regarded
over `S` becomes an `R`-module again. -/
abbrev opAlgebraMap (A : DifferentialGradedAlgebra.{u, v} R) : R →+* MulOpposite A.A :=
  algebraMap R (MulOpposite A.A)

/-- The graded piece of degree `n` of a differential graded module over `A` regarded over `S`,
as an `R`-submodule for the action of `R` through `algebraMap R A`. -/
def extendBaseGrading (N : DifferentialGradedModule.{u', v, w} (A.restrictBase S)) (n : ℤ) :
    @Submodule R N.M _ _ (@Module.compHom _ _ N.M _ _ N.rmodule _ (opAlgebraMap A)) :=
  letI : Module R N.M := @Module.compHom _ _ N.M _ _ N.rmodule _ (opAlgebraMap A)
  { carrier := N.grading n
    add_mem' := (N.grading n).add_mem
    zero_mem' := (N.grading n).zero_mem
    smul_mem' := fun r x hx => by
      have h := N.smul_mem n 0 x (algebraMap R A.A r) hx (SetLike.algebraMap_mem_graded A.grading r)
      rw [add_zero] at h
      exact h }

/-- The differential of a differential graded module over `A` regarded over `S` commutes with
right multiplication by the image of the base ring `R`. -/
theorem d_op_algebraMap_smul (N : DifferentialGradedModule.{u', v, w} (A.restrictBase S))
    (r : R) (x : N.M) :
    N.d (MulOpposite.op (show (A.restrictBase S).A from algebraMap R A.A r) • x) =
      MulOpposite.op (show (A.restrictBase S).A from algebraMap R A.A r) • N.d x := by
  induction x using DirectSum.Decomposition.inductionOn N.grading with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | @homogeneous n x =>
    rw [N.leibniz n 0 x (algebraMap R A.A r) x.property (SetLike.algebraMap_mem_graded A.grading r)]
    have h0 : (A.restrictBase S).d (algebraMap R A.A r) = 0 :=
      DifferentialGradedAlgebra.d_algebraMap A r
    rw [h0, MulOpposite.op_zero, zero_smul, smul_zero, add_zero]

/-- A differential graded module over `A` regarded over `S`, made into a differential graded
`A`-module by letting `r : R` act as right multiplication by `algebraMap R A r`. -/
@[implicit_reducible]
def extendBaseObj (N : DifferentialGradedModule.{u', v, w} (A.restrictBase S)) :
    DifferentialGradedModule.{u, v, w} A :=
  letI : Module (MulOpposite A.A) N.M := N.rmodule
  letI : Module R N.M := Module.compHom N.M (opAlgebraMap A)
  haveI : IsScalarTower R (MulOpposite A.A) N.M :=
    ⟨fun r a x => by
      change (r • a) • x = (algebraMap R (MulOpposite A.A) r) • a • x
      rw [← mul_smul, Algebra.smul_def]⟩
  { M := N.M
    rmodule := N.rmodule
    grading := extendBaseGrading S N
    decomposition :=
      { decompose' := DirectSum.Decomposition.decompose' (ℳ := N.grading)
        left_inv := DirectSum.Decomposition.left_inv (ℳ := N.grading)
        right_inv := DirectSum.Decomposition.right_inv (ℳ := N.grading) }
    smul_mem := N.smul_mem
    d :=
      { toFun := N.d
        map_add' := N.d.map_add
        map_smul' := fun r x => d_op_algebraMap_smul S N r x }
    d_comp_d := by
      ext x
      exact LinearMap.congr_fun N.d_comp_d x
    d_mem := N.d_mem
    leibniz := N.leibniz }

/-- The scalar action of `R` on a module made into a differential graded `A`-module is right
multiplication by the image of `R` in `A`. -/
theorem extendBaseObj_smul (N : DifferentialGradedModule.{u', v, w} (A.restrictBase S)) (r : R)
    (x : (extendBaseObj S N).M) :
    r • x = (MulOpposite.op (show (A.restrictBase S).A from algebraMap R A.A r) •
      (show N.M from x) : N.M) := rfl

/-- A homomorphism of differential graded modules over `A` regarded over `S`, as a homomorphism
of differential graded `A`-modules. -/
def extendBaseHom {N N' : DifferentialGradedModule.{u', v, w} (A.restrictBase S)} (f : N ⟶ N') :
    extendBaseObj S N ⟶ extendBaseObj S N' where
  toFun :=
    { toFun := f.toFun
      map_add' := f.toFun.map_add
      map_smul' := fun r x => f.map_smul x (algebraMap R A.A r) }
  map_smul := f.map_smul
  map_grading := f.map_grading
  map_d := by
    ext x
    exact LinearMap.congr_fun f.map_d x

variable (A) in
/-- Making differential graded modules over `A` regarded over `S` into differential graded
`A`-modules, as a functor `Mod_(A_S, d) ⥤ Mod_(A, d)`. -/
def extendBase :
    DifferentialGradedModule.{u', v, w} (A.restrictBase S) ⥤ DifferentialGradedModule.{u, v, w} A
    where
  obj N := extendBaseObj S N
  map f := extendBaseHom S f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor letting `R` act through `A` acts on objects by `extendBaseObj`. -/
@[simp]
theorem extendBase_obj (N : DifferentialGradedModule.{u', v, w} (A.restrictBase S)) :
    (extendBase S A).obj N = extendBaseObj S N := rfl

end extendBase


section equivalence

/-- In a differential graded module, a scalar of the base ring acts as right multiplication by its
image in the algebra. -/
theorem smul_eq_op_algebraMap_smul {T : Type u} [CommRing T]
    {B : DifferentialGradedAlgebra.{u, v} T} (M : DifferentialGradedModule.{u, v, w} B) (t : T)
    (x : M.M) : t • x = MulOpposite.op (algebraMap T B.A t) • x := by
  rw [← smul_one_smul (MulOpposite B.A) t x, Algebra.algebraMap_eq_smul_one]
  rfl

variable (A) in
/-- Regarding a differential graded `A`-module over `S` and letting `R` act through `A` again
gives back the module: the identity of the underlying type is an isomorphism, because the action
of `r : R` is in both cases right multiplication by `algebraMap R A r`. -/
def restrictBaseUnitIso (M : DifferentialGradedModule.{u, v, w} A) :
    M ≅ extendBaseObj S (restrictBaseObj S M) where
  hom :=
    { toFun :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => smul_eq_op_algebraMap_smul M r x }
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ h => h
      map_d := rfl }
  inv :=
    { toFun :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => (smul_eq_op_algebraMap_smul M r x).symm }
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ h => h
      map_d := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

variable (A) in
/-- Letting `R` act through `A` on a differential graded module over `A` regarded over `S`, and
regarding the result over `S` again, gives back the module: the identity of the underlying type is
an isomorphism, because the action of `s : S` is in both cases right multiplication by
`algebraMap S A s`. -/
def restrictBaseCounitIso (N : DifferentialGradedModule.{u', v, w} (A.restrictBase S)) :
    restrictBaseObj S (extendBaseObj S N) ≅ N where
  hom :=
    { toFun :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun s x => (smul_eq_op_algebraMap_smul N s x).symm }
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ h => h
      map_d := rfl }
  inv :=
    { toFun :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun s x => smul_eq_op_algebraMap_smul N s x }
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ h => h
      map_d := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

variable (A) in
/-- **Differential graded modules do not see the base ring.** Regarding differential graded
`A`-modules over `S` is an equivalence `Mod_(A, d) ≌ Mod_(A_S, d)`, whose inverse lets `R` act
through `algebraMap R A`. -/
def restrictBaseEquiv :
    DifferentialGradedModule.{u, v, w} A ≌ DifferentialGradedModule.{u', v, w} (A.restrictBase S) :=
  CategoryTheory.Equivalence.mk (restrictBase S A) (extendBase S A)
    (NatIso.ofComponents (restrictBaseUnitIso S A) (fun _ => rfl))
    (NatIso.ofComponents (restrictBaseCounitIso S A) (fun _ => rfl))

/-- The functor of `restrictBaseEquiv` regards modules over `S`. -/
@[simp]
theorem restrictBaseEquiv_functor : (restrictBaseEquiv S A).functor = restrictBase S A := rfl

/-- The inverse of `restrictBaseEquiv` lets `R` act through `A`. -/
@[simp]
theorem restrictBaseEquiv_inverse : (restrictBaseEquiv S A).inverse = extendBase S A := rfl

end equivalence

section homotopy

/-- A homotopy between homomorphisms of differential graded `A`-modules is a homotopy between
the homomorphisms regarded over `S`: it is the same map. -/
def Homotopy.restrictBase {M N : DifferentialGradedModule.{u, v, w} A} {f g : M ⟶ N}
    (h : Homotopy f g) : Homotopy ((restrictBase S A).map f) ((restrictBase S A).map g) where
  toLinearMap := h.toLinearMap
  map_grading := h.map_grading
  homotopy_eq := h.homotopy_eq

/-- A homotopy between homomorphisms of differential graded modules over `A` regarded over `S` is
a homotopy between the homomorphisms of differential graded `A`-modules: it is the same map. -/
def Homotopy.extendBase {N N' : DifferentialGradedModule.{u', v, w} (A.restrictBase S)}
    {f g : N ⟶ N'} (h : Homotopy f g) :
    Homotopy ((extendBase S A).map f) ((extendBase S A).map g) where
  toLinearMap := h.toLinearMap
  map_grading := h.map_grading
  homotopy_eq := h.homotopy_eq

variable (A) in
/-- Regarding differential graded `A`-modules over `S`, on homotopy categories. -/
def restrictBaseHomotopyFunctor :
    HomotopyCategory.{u, v, w} A ⥤ HomotopyCategory.{u', v, w} (A.restrictBase S) :=
  CategoryTheory.Quotient.lift (homotopyRel A) (restrictBase S A ⋙ toHomotopyCategory _)
    (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ ⟨Homotopy.restrictBase S h.some⟩)

variable (A) in
/-- Regarding over `S` on homotopy categories is induced by regarding over `S` on modules. -/
def restrictBaseHomotopyFunctorIso :
    toHomotopyCategory A ⋙ restrictBaseHomotopyFunctor S A ≅
      restrictBase S A ⋙ toHomotopyCategory (A.restrictBase S) :=
  CategoryTheory.Quotient.lift.isLift _ _ _

variable (A) in
/-- Letting `R` act through `A`, on homotopy categories. -/
def extendBaseHomotopyFunctor :
    HomotopyCategory.{u', v, w} (A.restrictBase S) ⥤ HomotopyCategory.{u, v, w} A :=
  CategoryTheory.Quotient.lift (homotopyRel (A.restrictBase S))
    (extendBase S A ⋙ toHomotopyCategory A)
    (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ ⟨Homotopy.extendBase S h.some⟩)

variable (A) in
/-- Letting `R` act through `A` on homotopy categories is induced by the same on modules. -/
def extendBaseHomotopyFunctorIso :
    toHomotopyCategory (A.restrictBase S) ⋙ extendBaseHomotopyFunctor S A ≅
      extendBase S A ⋙ toHomotopyCategory A :=
  CategoryTheory.Quotient.lift.isLift _ _ _

variable (A) in
/-- **The homotopy category does not see the base ring.** The equivalence
`DifferentialGradedModule.restrictBaseEquiv` descends to the homotopy categories,
`K(A, d) ≌ K(A_S, d)`. -/
def restrictBaseHomotopyEquiv :
    HomotopyCategory.{u, v, w} A ≌ HomotopyCategory.{u', v, w} (A.restrictBase S) :=
  CategoryTheory.Equivalence.mk (restrictBaseHomotopyFunctor S A) (extendBaseHomotopyFunctor S A)
    (CategoryTheory.Quotient.natIsoLift _
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (restrictBaseEquiv S A).unitIso (toHomotopyCategory A) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (restrictBase S A) (extendBaseHomotopyFunctorIso S A).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (restrictBaseHomotopyFunctorIso S A).symm _ ≪≫
        Functor.associator _ _ _))
    (CategoryTheory.Quotient.natIsoLift _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (extendBaseHomotopyFunctorIso S A) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (extendBase S A) (restrictBaseHomotopyFunctorIso S A) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (restrictBaseEquiv S A).counitIso
          (toHomotopyCategory (A.restrictBase S)) ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm))

/-- The functor of `restrictBaseHomotopyEquiv` regards modules over `S`. -/
@[simp]
theorem restrictBaseHomotopyEquiv_functor :
    (restrictBaseHomotopyEquiv S A).functor = restrictBaseHomotopyFunctor S A := rfl

/-- The inverse of `restrictBaseHomotopyEquiv` lets `R` act through `A`. -/
@[simp]
theorem restrictBaseHomotopyEquiv_inverse :
    (restrictBaseHomotopyEquiv S A).inverse = extendBaseHomotopyFunctor S A := rfl

end homotopy

end DifferentialGradedModule

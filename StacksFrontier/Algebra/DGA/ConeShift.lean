module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.TriangleShift
public import StacksFrontier.Algebra.DGA.ConeRotate

/-!
# Shifting the cone of a homomorphism of differential graded modules

Shifting the cone of `f : K ⟶ L` by `n` is the cone of the shift of `f`: both have underlying
module `L × K`, and the comparison multiplies the `K`-coordinate by the sign of the shift.  This
file also records that every comparison isomorphism of the shift on differential graded modules
is carried by the identity of the underlying module, and that the cone triangle in the homotopy
category is the image, under the quotient functor, of a triangle of differential graded modules.

## Main definitions

* `DifferentialGradedModule.coneShiftIso` compares the shift of a cone with the cone of a shift.
* `DifferentialGradedModule.coneTriangleDG` is the cone triangle before passing to the homotopy
  category, of which `DifferentialGradedModule.coneTriangle` is the image under the quotient
  functor.
* `DifferentialGradedModule.negOnePowIso` is multiplication by the sign of a shift, as an
  automorphism.
* `DifferentialGradedModule.shiftedConeTriangleIso` compares the shift of a cone triangle, in
  the category of triangles, with the cone triangle of a shift.

## Main results

* `DifferentialGradedModule.shiftFunctorComm_hom_app_toFun` and its companions for
  `CategoryTheory.shiftFunctorAdd` and `CategoryTheory.shiftFunctorAdd'`: every comparison
  isomorphism between iterated shifts is carried by the identity of the underlying module.
* `DifferentialGradedModule.coneTriangle_eq_mapTriangle`.
* `DifferentialGradedModule.shiftedConeTriangle_comm₁`,
  `DifferentialGradedModule.shiftedConeTriangle_comm₂` and
  `DifferentialGradedModule.shiftedConeTriangle_comm₃` are the three squares of that
  comparison.

## Implementation notes

The comparison isomorphism is `(l, k) ↦ (l, (-1)^n · k)` and not `(l, k) ↦ ((-1)^n · l, k)`,
although both commute with the differentials: only the first is compatible with the inclusions
of the targets, which is what a comparison of cone triangles needs.

The comparison isomorphisms of the shift are computable here because the shift on differential
graded modules is assembled from `CategoryTheory.ShiftMkCore`, whose comparison maps are the
identity of the underlying module.  The corresponding statement on the homotopy category is
unavailable: the shift there is induced from this one and the induced shift is irreducible.  So
the comparison of a shifted cone triangle with the cone triangle of a shifted homomorphism has
to be built on differential graded modules and transported along the quotient functor, which is
why `DifferentialGradedModule.coneTriangleDG` is recorded here.

The three squares of that comparison are stated separately, each in a single spelling of the
shift: the shift of an object is written either as `DifferentialGradedModule.shift` or as the
image of the shift functor, and a statement mixing the two is type-correct only at the
transparency the elaborator uses, not at the one rewriting uses, so no rewrite fires inside it.
For the same reason the exchange of the two shifts enters
`DifferentialGradedModule.shiftedConeTriangle_comm₃` as a morphism assumed to be carried by the
identity of the underlying module rather than as `CategoryTheory.shiftFunctorComm`, whose type
is spelled with a composite of shift functors.  The three are then supplied to
`CategoryTheory.Pretriangulated.Triangle.isoMk` as terms, which is checked at full
definitional equality.

## References

* [Stacks Project, Tag 09KA](https://stacks.math.columbia.edu/tag/09KA)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

section ShiftComparisons

variable (M : DifferentialGradedModule.{u, v, w} A)

/-- Every comparison isomorphism between iterated shifts of a differential graded module is
carried by the identity of the underlying module. -/
theorem shiftFunctorAdd'_hom_app_toFun (i j k : ℤ) (h : i + j = k) (x : M.M) :
    ((shiftFunctorAdd' (DifferentialGradedModule.{u, v, w} A) i j k h).hom.app M).toFun x = x := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd,
    ShiftMkCore.shiftFunctorAdd_eq (shiftMkCore.{u, v, w} (A := A)) i j]
  rfl

/-- Every comparison isomorphism between iterated shifts of a differential graded module is
carried by the identity of the underlying module. -/
theorem shiftFunctorAdd'_inv_app_toFun (i j k : ℤ) (h : i + j = k) (x : M.M) :
    ((shiftFunctorAdd' (DifferentialGradedModule.{u, v, w} A) i j k h).inv.app M).toFun x = x := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd,
    ShiftMkCore.shiftFunctorAdd_eq (shiftMkCore.{u, v, w} (A := A)) i j]
  rfl

/-- Every comparison isomorphism between iterated shifts of a differential graded module is
carried by the identity of the underlying module. -/
theorem shiftFunctorAdd_inv_app_toFun (i j : ℤ) (x : M.M) :
    ((shiftFunctorAdd (DifferentialGradedModule.{u, v, w} A) i j).inv.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorAdd_eq (shiftMkCore.{u, v, w} (A := A)) i j]
  rfl

/-- The isomorphism exchanging two shifts of a differential graded module is carried by the
identity of the underlying module: shifting changes the indexing of the grading and the sign of
the differential, not the module. -/
theorem shiftFunctorComm_hom_app_toFun (a b : ℤ) (x : M.M) :
    ((shiftFunctorComm (DifferentialGradedModule.{u, v, w} A) a b).hom.app M).toFun x = x :=
  (shiftFunctorAdd'_hom_app_toFun M b a (a + b) (add_comm b a) _).trans
    (shiftFunctorAdd_inv_app_toFun M a b x)

end ShiftComparisons

section Zsmul

variable {M N : DifferentialGradedModule.{u, v, w} A}

/-- Evaluation at an element, as an additive map in the homomorphism. -/
def Hom.evalAddMonoidHom (M N : DifferentialGradedModule.{u, v, w} A) (x : M.M) :
    (M ⟶ N) →+ N.M where
  toFun g := g.toFun x
  map_zero' := by rw [Hom.hom_zero_toFun]; rfl
  map_add' g h := by rw [Hom.hom_add_toFun]; rfl

/-- An integer multiple of a homomorphism acts as that multiple of its underlying map. -/
theorem Hom.hom_zsmul_toFun (m : ℤ) (g : M ⟶ N) (x : M.M) :
    (m • g).toFun x = m • g.toFun x :=
  map_zsmul (Hom.evalAddMonoidHom M N x) m g

/-- A multiple of a homomorphism by a unit of `ℤ` acts as that multiple of its underlying map. -/
theorem Hom.hom_units_zsmul_toFun (u : ℤˣ) (g : M ⟶ N) (x : M.M) :
    (u • g).toFun x = (u : ℤ) • g.toFun x := by
  rw [Units.smul_def, Hom.hom_zsmul_toFun]

/-- The identity homomorphism acts as the identity. -/
@[simp] theorem Hom.id_toFun_apply (M : DifferentialGradedModule.{u, v, w} A) (x : M.M) :
    (𝟙 M : M ⟶ M).toFun x = x := rfl

end Zsmul

variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- The underlying map of the comparison between the shift of a cone and the cone of a shift:
the identity on the coordinate of the target, the sign of the shift on the coordinate of the
source. -/
noncomputable def coneShiftLinearMap (K L : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    L.M × K.M →ₗ[R] L.M × K.M :=
  LinearMap.prod (LinearMap.fst R L.M K.M) ((n.negOnePow : ℤ) • LinearMap.snd R L.M K.M)

/-- `coneShiftLinearMap K L n` is `(l, k) ↦ (l, (-1)^n · k)`. -/
@[simp] theorem coneShiftLinearMap_apply (K L : DifferentialGradedModule.{u, v, w} A) (n : ℤ)
    (x : L.M × K.M) :
    coneShiftLinearMap K L n x = (x.1, (n.negOnePow : ℤ) • x.2) := rfl

private theorem negOnePow_mul_self (n : ℤ) : ((n.negOnePow : ℤ) * (n.negOnePow : ℤ)) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

/-- Multiplying twice by the sign of a shift is the identity. -/
private theorem negOnePow_smul_smul {X : Type*} [AddCommGroup X] (n : ℤ) (y : X) :
    (n.negOnePow : ℤ) • (n.negOnePow : ℤ) • y = y := by
  rw [smul_smul, negOnePow_mul_self, one_smul]

/-- The differential of a shift is the differential multiplied by the sign of the shift. -/
theorem shift_d_apply (M : DifferentialGradedModule.{u, v, w} A) (k : ℤ) (x : M.M) :
    (shift M k).d x = (k.negOnePow : ℤ) • M.d x := by
  rw [shift_d, LinearMap.smul_apply, Units.smul_def]

/-- The comparison map is an involution of `L × K`. -/
theorem coneShiftLinearMap_involutive (K L : DifferentialGradedModule.{u, v, w} A) (n : ℤ)
    (x : L.M × K.M) :
    coneShiftLinearMap K L n (coneShiftLinearMap K L n x) = x := by
  exact Prod.ext rfl (negOnePow_smul_smul n x.2)

/-- The comparison map carries the differential of the shift of the cone to the differential of
the cone of the shift. -/
theorem coneShiftLinearMap_d (f : K ⟶ L) (n : ℤ) (x : L.M × K.M) :
    coneShiftLinearMap K L n ((n.negOnePow : ℤ) • (coneObject f).d x) =
      (coneObject (shiftMap f n)).d (coneShiftLinearMap K L n x) := by
  rw [coneObject_d_apply, coneObject_d_apply, coneShiftLinearMap_apply,
    coneShiftLinearMap_apply]
  refine Prod.ext ?_ ?_
  · show (n.negOnePow : ℤ) • (L.d x.1 + f.toFun x.2) =
      (shift L n).d x.1 + (shiftMap f n).toFun ((n.negOnePow : ℤ) • x.2)
    rw [shift_d_apply, shiftMap_toFun, map_zsmul, smul_add]
  · show (n.negOnePow : ℤ) • (n.negOnePow : ℤ) • -K.d x.2 =
      -(shift K n).d ((n.negOnePow : ℤ) • x.2)
    rw [shift_d_apply, map_zsmul, smul_neg, smul_neg, negOnePow_smul_smul]

/-- The comparison map is right `A`-linear. -/
theorem coneShiftLinearMap_smul (K L : DifferentialGradedModule.{u, v, w} A) (n : ℤ)
    (x : L.M × K.M) (c : A.A) :
    coneShiftLinearMap K L n (MulOpposite.op c • x) =
      MulOpposite.op c • coneShiftLinearMap K L n x := by
  refine Prod.ext rfl ?_
  show (n.negOnePow : ℤ) • (MulOpposite.op c • x.2) =
    MulOpposite.op c • ((n.negOnePow : ℤ) • x.2)
  exact (map_zsmul (DistribSMul.toAddMonoidHom K.M (MulOpposite.op c))
    (n.negOnePow : ℤ) x.2).symm

/-- The comparison map from the shift of the cone of `f` to the cone of the shift of `f`. -/
noncomputable def coneShiftHom (f : K ⟶ L) (n : ℤ) :
    shift (coneObject f) n ⟶ coneObject (shiftMap f n) where
  toFun := coneShiftLinearMap K L n
  map_smul x c := coneShiftLinearMap_smul K L n x c
  map_grading m x hx := by
    obtain ⟨hx₁, hx₂⟩ := (coneGrading_mem (K := K) (L := L) (m + n) x).mp hx
    refine (coneGrading_mem (K := shift K n) (L := shift L n) m _).mpr ⟨hx₁, ?_⟩
    change (n.negOnePow : ℤ) • x.2 ∈ K.grading (m + 1 + n)
    rw [show m + 1 + n = m + n + 1 by ring]
    exact zsmul_mem hx₂ _
  map_d := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply]
    rw [show (shift (coneObject f) n).d x = (n.negOnePow : ℤ) • (coneObject f).d x from
      shift_d_apply (coneObject f) n x]
    exact coneShiftLinearMap_d f n x

/-- The underlying map of `coneShiftHom f n` is `coneShiftLinearMap K L n`. -/
@[simp] theorem coneShiftHom_toFun (f : K ⟶ L) (n : ℤ) :
    (coneShiftHom f n).toFun = coneShiftLinearMap K L n := rfl

/-- The comparison map from the cone of the shift of `f` to the shift of the cone of `f`: it is
carried by the same map, the sign of the shift being its own inverse. -/
noncomputable def coneShiftInv (f : K ⟶ L) (n : ℤ) :
    coneObject (shiftMap f n) ⟶ shift (coneObject f) n where
  toFun := coneShiftLinearMap K L n
  map_smul x c := coneShiftLinearMap_smul K L n x c
  map_grading m x hx := by
    obtain ⟨hx₁, hx₂⟩ :=
      (coneGrading_mem (K := shift K n) (L := shift L n) m x).mp hx
    refine (coneGrading_mem (K := K) (L := L) (m + n) _).mpr ⟨hx₁, ?_⟩
    have hx₂' : x.2 ∈ K.grading (m + 1 + n) := hx₂
    rw [show m + 1 + n = m + n + 1 by ring] at hx₂'
    exact zsmul_mem hx₂' _
  map_d := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply]
    have h := coneShiftLinearMap_d f n (coneShiftLinearMap K L n x)
    rw [coneShiftLinearMap_involutive] at h
    rw [show (shift (coneObject f) n).d (coneShiftLinearMap K L n x) =
        (n.negOnePow : ℤ) • (coneObject f).d (coneShiftLinearMap K L n x) from
      shift_d_apply (coneObject f) n _, ← h, coneShiftLinearMap_involutive]

/-- The shift of the cone of `f` is the cone of the shift of `f`. -/
noncomputable def coneShiftIso (f : K ⟶ L) (n : ℤ) :
    shift (coneObject f) n ≅ coneObject (shiftMap f n) where
  hom := coneShiftHom f n
  inv := coneShiftInv f n
  hom_inv_id := Hom.ext (LinearMap.ext fun x => coneShiftLinearMap_involutive K L n x)
  inv_hom_id := Hom.ext (LinearMap.ext fun x => coneShiftLinearMap_involutive K L n x)

/-- The forward map of `coneShiftIso f n` is `coneShiftHom f n`. -/
@[simp] theorem coneShiftIso_hom (f : K ⟶ L) (n : ℤ) :
    (coneShiftIso f n).hom = coneShiftHom f n := rfl

/-- The comparison is compatible with the inclusions of the targets. -/
theorem shiftFunctor_coneIncl_coneShiftHom (f : K ⟶ L) (n : ℤ) :
    (CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map (coneIncl f) ≫
        coneShiftHom f n =
      coneIncl ((CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map f) := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  refine Prod.ext rfl ?_
  show (n.negOnePow : ℤ) • (0 : K.M) = 0
  rw [smul_zero]

/-- Multiplication by the sign of a shift, as an automorphism of a differential graded
module. -/
noncomputable def negOnePowIso (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) : M ≅ M where
  hom := (n.negOnePow : ℤ) • 𝟙 M
  inv := (n.negOnePow : ℤ) • 𝟙 M
  hom_inv_id := by
    apply Hom.ext
    refine LinearMap.ext fun x => ?_
    simp only [Hom.comp_toFun_apply, Hom.hom_zsmul_toFun, Hom.id_toFun_apply, smul_smul,
      negOnePow_mul_self, one_smul]
  inv_hom_id := by
    apply Hom.ext
    refine LinearMap.ext fun x => ?_
    simp only [Hom.comp_toFun_apply, Hom.hom_zsmul_toFun, Hom.id_toFun_apply, smul_smul,
      negOnePow_mul_self, one_smul]

/-- The forward map of `negOnePowIso M n` is multiplication by the sign of the shift. -/
@[simp] theorem negOnePowIso_hom (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    (negOnePowIso M n).hom = (n.negOnePow : ℤ) • 𝟙 M := rfl

/-- The cone triangle of `f : K ⟶ L` before passing to the homotopy category. -/
noncomputable def coneTriangleDG (f : K ⟶ L) :
    Triangle (DifferentialGradedModule.{u, v, w} A) :=
  Triangle.mk f (coneIncl f) (coneProj f)

/-- The cone triangle is the image of the cone triangle of differential graded modules under the
quotient functor. -/
theorem coneTriangle_eq_mapTriangle (f : K ⟶ L) :
    coneTriangle f = (toHomotopyCategory.{u, v, w} A).mapTriangle.obj (coneTriangleDG f) := rfl

section ShiftedConeTriangle

/-- The first square of the comparison between the shift of a cone triangle and the cone
triangle of a shift: the sign of the shift occurs on the first morphism and again on the
comparison of the targets, and the two cancel. -/
theorem shiftedConeTriangle_comm₁ (f : K ⟶ L) (n : ℤ) :
    ((n.negOnePow : ℤ) • (shiftFunctor.{u, v, w} A n).map f) ≫
        ((n.negOnePow : ℤ) • 𝟙 ((shiftFunctor.{u, v, w} A n).obj L)) =
      𝟙 ((shiftFunctor.{u, v, w} A n).obj K) ≫ (shiftFunctor.{u, v, w} A n).map f := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  simp only [Hom.comp_toFun_apply, Hom.hom_zsmul_toFun, Hom.id_toFun_apply,
    shiftFunctor_map_toFun, negOnePow_smul_smul]

/-- The second square of the comparison between the shift of a cone triangle and the cone
triangle of a shift: the comparison of the cones is the identity on the coordinate of the
target, so both sides multiply the inclusion by the sign of the shift. -/
theorem shiftedConeTriangle_comm₂ (f : K ⟶ L) (n : ℤ) :
    ((n.negOnePow : ℤ) • (shiftFunctor.{u, v, w} A n).map (coneIncl f)) ≫ coneShiftHom f n =
      ((n.negOnePow : ℤ) • 𝟙 ((shiftFunctor.{u, v, w} A n).obj L)) ≫
        coneIncl ((shiftFunctor.{u, v, w} A n).map f) := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  simp only [Hom.comp_toFun_apply, Hom.hom_zsmul_toFun, Hom.id_toFun_apply,
    shiftFunctor_map_toFun, coneShiftHom_toFun, coneIncl_toFun_apply]
  refine Prod.ext rfl ?_
  show (n.negOnePow : ℤ) • (n.negOnePow : ℤ) • (0 : K.M) = 0
  rw [smul_zero, smul_zero]

/-- The third square of the comparison between the shift of a cone triangle and the cone
triangle of a shift: both sides send `(l, k)` to the sign of the shift times `k`.  The
isomorphism exchanging the two shifts enters only through its underlying map, which is the
identity of the underlying module by
`DifferentialGradedModule.shiftFunctorComm_hom_app_toFun`; it is taken here as a morphism with
that property rather than written out, which keeps the shifts in this statement spelled by the
shift functor of differential graded modules alone. -/
theorem shiftedConeTriangle_comm₃ (f : K ⟶ L) (n : ℤ)
    (θ : shift (shift K 1) n ⟶ shift (shift K n) 1) (hθ : ∀ x, θ.toFun x = x) :
    ((n.negOnePow : ℤ) • ((shiftFunctor.{u, v, w} A n).map (coneProj f) ≫ θ)) ≫
        𝟙 (shift (shift K n) 1) =
      coneShiftHom f n ≫ coneProj ((shiftFunctor.{u, v, w} A n).map f) := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  simp only [Hom.comp_toFun_apply, Hom.hom_zsmul_toFun, Hom.id_toFun_apply,
    shiftFunctor_map_toFun, hθ]
  exact rfl

/-- The shift of the cone triangle of `f : K ⟶ L` by `n` is the cone triangle of the shift of
`f` by `n`.  The source is the shift of `DifferentialGradedModule.coneTriangleDG f` in the
category of triangles, written out: the three morphisms multiplied by the sign of the shift,
the third one followed by the exchange of the two shifts. -/
noncomputable def shiftedConeTriangleIso (f : K ⟶ L) (n : ℤ) :
    Triangle.mk
        (n.negOnePow •
          (CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map
            (coneTriangleDG f).mor₁)
        (n.negOnePow •
          (CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map
            (coneTriangleDG f).mor₂)
        (n.negOnePow •
          (CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map
              (coneTriangleDG f).mor₃ ≫
            (shiftFunctorComm (DifferentialGradedModule.{u, v, w} A) 1 n).hom.app
              (coneTriangleDG f).obj₁) ≅
      coneTriangleDG
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).map f) :=
  Triangle.isoMk _ _ (Iso.refl _)
    (negOnePowIso ((CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v, w} A) n).obj L) n)
    (coneShiftIso f n)
    (shiftedConeTriangle_comm₁ f n) (shiftedConeTriangle_comm₂ f n)
    (shiftedConeTriangle_comm₃ f n
      ((shiftFunctorComm (DifferentialGradedModule.{u, v, w} A) 1 n).hom.app K)
      (shiftFunctorComm_hom_app_toFun K 1 n))

end ShiftedConeTriangle

end DifferentialGradedModule

end

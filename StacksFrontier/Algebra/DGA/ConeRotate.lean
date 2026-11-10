module

public import StacksFrontier.Algebra.DGA.ConeMap

/-!
# Rotating a cone triangle

The cone of the inclusion `L ⟶ C(f)` of the target of `f : K ⟶ L` into its own cone is homotopy
equivalent to `K[1]`: the equivalence sends `k` to `((0, k), -f k)` in the coordinates
`(L × K) × L`, and its inverse is the projection to the `K`-coordinate.  Under this equivalence
the rotation of the cone triangle of `f` is the cone triangle of the inclusion, which is the
rotation axiom of a pretriangulated category for the class of cone triangles.

## Main definitions

* `DifferentialGradedModule.rotateConeHom` and `DifferentialGradedModule.rotateConeInv` are the
  two homomorphisms of the homotopy equivalence, and
  `DifferentialGradedModule.rotateConeIso` is the resulting isomorphism of the homotopy
  category.
* `DifferentialGradedModule.rotateConeTriangleIso` identifies the rotation of a cone triangle
  with the cone triangle of the inclusion.
* `DifferentialGradedModule.isoOfHomotopyInverse` turns a pair of homomorphisms inverse up to
  homotopy into an isomorphism of the homotopy category.

## Main results

* `DifferentialGradedModule.rotate_mem_distinguishedConeTriangles`: the rotation of a triangle
  in `DifferentialGradedModule.distinguishedConeTriangles` lies in that class.

## Implementation notes

The signs are forced.  Writing `C(i)` for the cone of the inclusion `i : L ⟶ C(f)`, with
coordinates `((l, k), l')` and differential `((l, k), l') ↦ ((d l + f k + l', -d k), -d l')`, a
homomorphism `K[1] ⟶ C(i)` of the form `k ↦ ((0, k), c · f k)` commutes with the differentials
only for `c = -1`, because the differential of `K[1]` is the negative of that of `K` while the
`L`-coordinate of the differential of `C(i)` carries no sign.  The same computation fixes the
sign of the contracting homotopies: each is `((l, k), l') ↦ ((0, 0), -l)` or a restriction of
it, the coefficient being determined by the `L`-coordinate `f k + l'` of the differential.

One of the two composites of the equivalence is the identity on the nose, so only one
contracting homotopy is needed.

## References

* [Stacks Project, Tag 09KA](https://stacks.math.columbia.edu/tag/09KA)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

section Generalities

variable {M N : DifferentialGradedModule.{u, v, w} A}

/-- Equal homomorphisms are homotopic, by the zero homotopy. -/
def Homotopy.ofEq {f g : M ⟶ N} (h : f = g) : Homotopy f g where
  toLinearMap := 0
  map_grading _ _ _ := (N.grading _).zero_mem
  homotopy_eq x := by rw [h]; simp

/-- An isomorphism of the homotopy category out of a pair of homomorphisms inverse up to
homotopy. -/
noncomputable def isoOfHomotopyInverse (φ : M ⟶ N) (ψ : N ⟶ M)
    (h₁ : Homotopy (φ ≫ ψ) (𝟙 M)) (h₂ : Homotopy (ψ ≫ φ) (𝟙 N)) :
    (toHomotopyCategory.{u, v, w} A).obj M ≅ (toHomotopyCategory.{u, v, w} A).obj N where
  hom := (toHomotopyCategory A).map φ
  inv := (toHomotopyCategory A).map ψ
  hom_inv_id := by
    rw [← Functor.map_comp, ← (toHomotopyCategory A).map_id]
    exact (Quotient.functor_map_eq_iff (homotopyRel.{u, v, w} A) _ _).mpr ⟨h₁⟩
  inv_hom_id := by
    rw [← Functor.map_comp, ← (toHomotopyCategory A).map_id]
    exact (Quotient.functor_map_eq_iff (homotopyRel.{u, v, w} A) _ _).mpr ⟨h₂⟩

/-- The differential of a shift by one is the negative of the differential. -/
theorem shift_one_d_apply (M : DifferentialGradedModule.{u, v, w} A) (x : M.M) :
    (shift M 1).d x = -M.d x := by
  rw [shift_d, LinearMap.smul_apply, Int.negOnePow_one]
  simp

end Generalities

variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- The inclusion of the target into the cone is `l ↦ (l, 0)`. -/
@[simp] theorem coneIncl_toFun_apply (f : K ⟶ L) (x : L.M) :
    (coneIncl f).toFun x = (x, (0 : K.M)) := rfl

/-- The projection from the cone to the shifted source is `(l, k) ↦ k`. -/
@[simp] theorem coneProj_toFun_apply (f : K ⟶ L) (x : L.M × K.M) :
    (coneProj f).toFun x = x.2 := rfl

/-- The differential of a cone, in the coordinates `L × K`. -/
@[simp] theorem coneObject_d_apply (f : K ⟶ L) (x : L.M × K.M) :
    (coneObject f).d x = (L.d x.1 + f.toFun x.2, -K.d x.2) := rfl

/-- The differential of the cone of the inclusion `L ⟶ C(f)`, in the coordinates
`(L × K) × L`. -/
theorem coneIncl_coneD_apply (f : K ⟶ L) (x : (L.M × K.M) × L.M) :
    (coneObject (coneIncl f)).d x =
      ((L.d x.1.1 + f.toFun x.1.2 + x.2, -K.d x.1.2), -L.d x.2) := by
  refine Prod.ext (Prod.ext rfl ?_) rfl
  change -K.d x.1.2 + (0 : K.M) = -K.d x.1.2
  rw [add_zero]

/-- The homomorphism `K[1] ⟶ C(L ⟶ C(f))` of the rotation equivalence: in the coordinates
`(L × K) × L` it sends `k` to `((0, k), -f k)`. -/
noncomputable def rotateConeHom (f : K ⟶ L) : shift K 1 ⟶ coneObject (coneIncl f) where
  toFun := LinearMap.prod (LinearMap.prod (0 : K.M →ₗ[R] L.M) LinearMap.id) (-f.toFun)
  map_smul x c := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change (0 : L.M) = MulOpposite.op c • (0 : L.M)
      rw [smul_zero]
    · rfl
    · change -f.toFun (MulOpposite.op c • x) = MulOpposite.op c • -f.toFun x
      rw [f.map_smul, smul_neg]
  map_grading n x hx := by
    have hx' : x ∈ K.grading (n + 1) := hx
    refine (coneGrading_mem n _).mpr ⟨?_, ?_⟩
    · exact (coneGrading_mem (K := K) (L := L) n ((0 : L.M), x)).mpr
        ⟨(L.grading n).zero_mem, hx'⟩
    · exact (L.grading (n + 1)).neg_mem (f.map_grading (n + 1) x hx')
  map_d := by
    refine LinearMap.ext fun x => ?_
    have hf := LinearMap.congr_fun f.map_d x
    simp only [LinearMap.comp_apply] at hf ⊢
    rw [shift_one_d_apply, coneIncl_coneD_apply]
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change (0 : L.M) = L.d 0 + f.toFun x + -f.toFun x
      rw [map_zero]
      abel
    · rfl
    · change -f.toFun (-K.d x) = -L.d (-f.toFun x)
      rw [map_neg, map_neg, hf]

/-- In the coordinates `(L × K) × L`, `rotateConeHom f` sends `k` to `((0, k), -f k)`. -/
@[simp] theorem rotateConeHom_toFun_apply (f : K ⟶ L) (x : K.M) :
    (rotateConeHom f).toFun x = (((0 : L.M), x), -f.toFun x) := rfl

/-- The inclusion of the target into the cone, followed by the projection to the shifted source,
is zero. -/
theorem coneIncl_coneProj (f : K ⟶ L) : coneIncl f ≫ coneProj f = 0 := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  simp

/-- The homomorphism `C(L ⟶ C(f)) ⟶ K[1]` of the rotation equivalence: it is the projection to
the `K`-coordinate. -/
noncomputable def rotateConeInv (f : K ⟶ L) : coneObject (coneIncl f) ⟶ shift K 1 :=
  coneDesc (coneIncl f) (coneProj f) (Homotopy.ofEq (coneIncl_coneProj f))

/-- `rotateConeInv f` is the projection to the `K`-coordinate. -/
@[simp] theorem rotateConeInv_toFun_apply (f : K ⟶ L) (x : (L.M × K.M) × L.M) :
    (rotateConeInv f).toFun x = x.1.2 := by
  rw [rotateConeInv, coneDesc_toFun_apply, coneProj_toFun_apply,
    show (Homotopy.ofEq (coneIncl_coneProj f)).toLinearMap = 0 from rfl,
    LinearMap.zero_apply, add_zero]

/-- The composition `K[1] ⟶ C(L ⟶ C(f)) ⟶ K[1]` is the identity. -/
theorem rotateConeHom_rotateConeInv (f : K ⟶ L) :
    rotateConeHom f ≫ rotateConeInv f = 𝟙 (shift K 1) := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  rw [Hom.comp_toFun_apply, rotateConeHom_toFun_apply, rotateConeInv_toFun_apply]
  rfl

/-- The underlying map of the contracting homotopy of the rotation equivalence: in the
coordinates `(L × K) × L` it sends `((l, k), l')` to `((0, 0), -l)`. -/
noncomputable def rotateConeContraction (f : K ⟶ L) :
    (coneObject (coneIncl f)).M →ₗ[MulOpposite A.A] (coneObject (coneIncl f)).M :=
  (LinearMap.inr (MulOpposite A.A) (L.M × K.M) L.M).comp
    (-(LinearMap.fst (MulOpposite A.A) L.M K.M).comp
      (LinearMap.fst (MulOpposite A.A) (L.M × K.M) L.M))

/-- `rotateConeContraction f` sends `((l, k), l')` to `((0, 0), -l)`. -/
@[simp] theorem rotateConeContraction_apply (f : K ⟶ L) (x : (L.M × K.M) × L.M) :
    rotateConeContraction f x = (((0 : L.M), (0 : K.M)), -x.1.1) := rfl

/-- The composition `C(L ⟶ C(f)) ⟶ K[1] ⟶ C(L ⟶ C(f))` is homotopic to the identity. -/
noncomputable def rotateConeInvHomHomotopy (f : K ⟶ L) :
    Homotopy (rotateConeInv f ≫ rotateConeHom f) (𝟙 (coneObject (coneIncl f))) where
  toLinearMap := rotateConeContraction f
  map_grading n x hx := by
    obtain ⟨hx₁, _⟩ := (coneGrading_mem n x).mp hx
    refine (coneGrading_mem (n - 1) _).mpr
      ⟨((coneObject f).grading (n - 1)).zero_mem, ?_⟩
    rw [show n - 1 + 1 = n by ring]
    exact (L.grading n).neg_mem ((coneGrading_mem n x.1).mp hx₁).1
  homotopy_eq x := by
    have hcomp : (rotateConeInv f ≫ rotateConeHom f).toFun x =
        (((0 : L.M), x.1.2), -f.toFun x.1.2) := by
      rw [Hom.comp_toFun_apply, rotateConeInv_toFun_apply, rotateConeHom_toFun_apply]
    have hid : (𝟙 (coneObject (coneIncl f)) : _ ⟶ _).toFun x = x := rfl
    rw [hcomp, hid, coneIncl_coneD_apply, rotateConeContraction_apply,
      rotateConeContraction_apply, coneIncl_coneD_apply]
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change (0 : L.M) - x.1.1 = L.d 0 + f.toFun 0 + -x.1.1 + 0
      rw [map_zero, map_zero]
      abel
    · change x.1.2 - x.1.2 = -K.d (0 : K.M) + 0
      rw [map_zero, neg_zero]
      abel
    · change -f.toFun x.1.2 - x.2 =
        -L.d (-x.1.1) + -(L.d x.1.1 + f.toFun x.1.2 + x.2)
      rw [map_neg, neg_neg]
      abel

/-- The rotation equivalence: in the homotopy category the class of the shift of `K` is the
class of the cone of the inclusion `L ⟶ C(f)`. -/
noncomputable def rotateConeIso (f : K ⟶ L) :
    (toHomotopyCategory.{u, v, w} A).obj (shift K 1) ≅
      (toHomotopyCategory.{u, v, w} A).obj (coneObject (coneIncl f)) :=
  isoOfHomotopyInverse (rotateConeHom f) (rotateConeInv f)
    (Homotopy.ofEq (rotateConeHom_rotateConeInv f)) (rotateConeInvHomHomotopy f)

/-- The forward map of the rotation equivalence is the class of `rotateConeHom f`. -/
@[simp] theorem rotateConeIso_hom (f : K ⟶ L) :
    (rotateConeIso f).hom = (toHomotopyCategory A).map (rotateConeHom f) := rfl

/-- The underlying map of the homotopy `rotateConeComm₂Homotopy`: in the coordinates `L × K` and
`(L × K) × L` it sends `(l, k)` to `((0, 0), -l)`. -/
noncomputable def rotateConeComm₂Contraction (f : K ⟶ L) :
    (coneObject f).M →ₗ[MulOpposite A.A] (coneObject (coneIncl f)).M :=
  (LinearMap.inr (MulOpposite A.A) (L.M × K.M) L.M).comp
    (-LinearMap.fst (MulOpposite A.A) L.M K.M)

/-- `rotateConeComm₂Contraction f` sends `(l, k)` to `((0, 0), -l)`. -/
@[simp] theorem rotateConeComm₂Contraction_apply (f : K ⟶ L) (x : L.M × K.M) :
    rotateConeComm₂Contraction f x = (((0 : L.M), (0 : K.M)), -x.1) := rfl

/-- The projection to `K[1]` followed by the rotation equivalence is homotopic to the inclusion
of `C(f)` into the cone of its own inclusion. -/
noncomputable def rotateConeComm₂Homotopy (f : K ⟶ L) :
    Homotopy (coneProj f ≫ rotateConeHom f) (coneIncl (coneIncl f)) where
  toLinearMap := rotateConeComm₂Contraction f
  map_grading n x hx := by
    obtain ⟨hx₁, _⟩ := (coneGrading_mem n x).mp hx
    refine (coneGrading_mem (n - 1) _).mpr
      ⟨((coneObject f).grading (n - 1)).zero_mem, ?_⟩
    rw [show n - 1 + 1 = n by ring]
    exact (L.grading n).neg_mem hx₁
  homotopy_eq x := by
    have h1 : (coneProj f ≫ rotateConeHom f).toFun x = (((0 : L.M), x.2), -f.toFun x.2) := rfl
    have h2 : (coneIncl (coneIncl f)).toFun x = (x, (0 : L.M)) := rfl
    have h3 : (coneObject (coneIncl f)).d (rotateConeComm₂Contraction f x) =
        ((-x.1, (0 : K.M)), L.d x.1) := by
      rw [rotateConeComm₂Contraction_apply, coneIncl_coneD_apply]
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · change L.d 0 + f.toFun 0 + -x.1 = -x.1
        rw [map_zero, map_zero]
        abel
      · change -K.d (0 : K.M) = 0
        rw [map_zero, neg_zero]
      · change -L.d (-x.1) = L.d x.1
        rw [map_neg, neg_neg]
    have h4 : rotateConeComm₂Contraction f ((coneObject f).d x) =
        (((0 : L.M), (0 : K.M)), -(L.d x.1 + f.toFun x.2)) := by
      rw [rotateConeComm₂Contraction_apply, coneObject_d_apply]
    rw [h1, h2, h3, h4]
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change (0 : L.M) - x.1 = -x.1 + 0
      abel
    · change x.2 - x.2 = (0 : K.M) + 0
      abel
    · change -f.toFun x.2 - (0 : L.M) = L.d x.1 + -(L.d x.1 + f.toFun x.2)
      abel

/-- The rotation equivalence followed by the projection out of the cone of the inclusion is the
negative of the shift of `f`. -/
theorem rotateConeHom_coneProj (f : K ⟶ L) :
    rotateConeHom f ≫ coneProj (coneIncl f) = -shiftMap f 1 := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  rw [Hom.comp_toFun_apply, Hom.hom_neg_toFun, rotateConeHom_toFun_apply]
  change -f.toFun x = -(shiftMap f 1).toFun x
  rw [shiftMap_toFun]

/-- The first square of the rotation isomorphism: both sides are the class of the inclusion. -/
theorem rotateConeTriangle_comm₁ (f : K ⟶ L) :
    (toHomotopyCategory A).map (coneIncl f) ≫ 𝟙 ((toHomotopyCategory A).obj (coneObject f)) =
      𝟙 ((toHomotopyCategory A).obj L) ≫ (toHomotopyCategory A).map (coneIncl f) := by
  rw [Category.comp_id, Category.id_comp]

/-- The second square of the rotation isomorphism: the projection to `K[1]` followed by the
rotation equivalence is the class of the inclusion of `C(f)` into the cone of its own
inclusion. -/
theorem rotateConeTriangle_comm₂ (f : K ⟶ L) :
    ((toHomotopyCategory A).map (coneProj f) ≫ (quotientShiftIso K 1).hom) ≫
        ((quotientShiftIso K 1).symm ≪≫ rotateConeIso f).hom =
      𝟙 ((toHomotopyCategory A).obj (coneObject f)) ≫
        (toHomotopyCategory A).map (coneIncl (coneIncl f)) := by
  rw [Category.id_comp, Iso.trans_hom, Iso.symm_hom, rotateConeIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp]
  exact (Quotient.functor_map_eq_iff (homotopyRel.{u, v, w} A) _ _).mpr
    ⟨rotateConeComm₂Homotopy f⟩

/-- The third square of the rotation isomorphism: the rotation equivalence followed by the
projection out of the cone of the inclusion is the negative of the shift of `f`. -/
theorem rotateConeTriangle_comm₃ (f : K ⟶ L) :
    (-((toHomotopyCategory A).map f)⟦(1 : ℤ)⟧') ≫ (𝟙 ((toHomotopyCategory A).obj L))⟦(1 : ℤ)⟧' =
      ((quotientShiftIso K 1).symm ≪≫ rotateConeIso f).hom ≫
        ((toHomotopyCategory A).map (coneProj (coneIncl f)) ≫ (quotientShiftIso L 1).hom) := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
    rotateConeIso_hom,
    Category.assoc, ← Functor.map_comp_assoc, rotateConeHom_coneProj, Functor.map_neg,
    Preadditive.neg_comp, Preadditive.comp_neg,
    quotient_map_shiftMap_comp_quotientShiftIso, Iso.inv_hom_id_assoc]

/-- The rotation of the cone triangle of `f : K ⟶ L` is the cone triangle of the inclusion
`L ⟶ C(f)`. -/
noncomputable def rotateConeTriangleIso (f : K ⟶ L) :
    (coneTriangle f).rotate ≅ coneTriangle (coneIncl f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((quotientShiftIso K 1).symm ≪≫ rotateConeIso f)
    (rotateConeTriangle_comm₁ f) (rotateConeTriangle_comm₂ f) (rotateConeTriangle_comm₃ f)

/-- The rotation of a triangle isomorphic to a cone triangle is isomorphic to a cone triangle:
it is isomorphic to the cone triangle of the inclusion. -/
theorem rotate_mem_distinguishedConeTriangles (T : Triangle (HomotopyCategory.{u, v, w} A))
    (hT : T ∈ distinguishedConeTriangles.{u, v, w} (A := A)) :
    T.rotate ∈ distinguishedConeTriangles.{u, v, w} (A := A) := by
  obtain ⟨K, L, f, ⟨e⟩⟩ := hT
  exact ⟨L, coneObject f, coneIncl f,
    ⟨(rotate (HomotopyCategory.{u, v, w} A)).mapIso e ≪≫ rotateConeTriangleIso f⟩⟩

end DifferentialGradedModule

end

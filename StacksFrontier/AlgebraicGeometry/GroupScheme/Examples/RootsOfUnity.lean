module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The group scheme of roots of unity

For a natural number `n`, the scheme of `n`-th roots of unity is the spectrum of
`ℤ[X] / (Xⁿ - 1)`. It represents the functor sending a scheme to the units of its ring of global
sections whose `n`-th power is one, for positive `n` it is a group scheme over the integers, and
its version over an arbitrary scheme is obtained by base change.

## Main definitions

* `AlgebraicGeometry.rootsOfUnityCoordinateRing` is the coordinate ring `ℤ[X] / (Xⁿ - 1)`,
  `AlgebraicGeometry.rootsOfUnity` the scheme of `n`-th roots of unity over the integers, and
  `AlgebraicGeometry.rootsOfUnityBaseChange` its base change to an arbitrary scheme.
* `AlgebraicGeometry.rootsOfUnitySections` is the functor of units in global sections whose
  `n`-th power is one, and `AlgebraicGeometry.rootsOfUnityGroupFunctor` its group-valued form on
  schemes over the integers.
* `AlgebraicGeometry.rootsOfUnityMultiplicationRingHom` is the coordinate-ring homomorphism
  defining multiplication, and `AlgebraicGeometry.rootsOfUnityMultiplication` the resulting
  scheme morphism.
* `AlgebraicGeometry.rootsOfUnityCoordinate` is the polynomial coordinate `X` as a unit,
  `AlgebraicGeometry.rootsOfUnityUniversalRoot` that coordinate as a global section of the
  roots-of-unity scheme, and `AlgebraicGeometry.rootsOfUnityBaseChangeUniversalRoot` its
  pullback to the base change.

## Main results

* `AlgebraicGeometry.rootsOfUnitySections_representableBy_rootsOfUnity` identifies the scheme of
  `n`-th roots of unity as a representing object for the functor of `n`-th roots of unity in
  global sections.
* `AlgebraicGeometry.rootsOfUnityGrpObj` equips the roots-of-unity scheme with a group-object
  structure, and `AlgebraicGeometry.rootsOfUnityGrpObj_mul` identifies its multiplication with
  the displayed morphism.
* `AlgebraicGeometry.rootsOfUnitySectionsOver_representableBy_rootsOfUnityBaseChange` gives the
  natural identification of the functor of points of the base change with roots of unity in
  global sections.

## Implementation notes

In universe `u` the integer base is represented by `ULift.{u} ℤ`, and the structure morphism is
induced by the inclusion of constants into the polynomial quotient. Base change is expressed by
`CategoryTheory.Over.pullback`, so its underlying scheme is the categorical fibre product from
the source. A group scheme over `Spec ℤ` is a group object in the category of schemes over
`Spec ℤ`; the source of multiplication is its categorical fibre product, which the canonical
affine fibre-product isomorphism identifies with the spectrum of the tensor product of the two
coordinate rings.

The values of `rootsOfUnitySections` are subtypes of the unit groups of global-section rings, and
`Functor.RepresentableBy` records the specified representing scheme together with a natural
family of bijections; the equality of sets in the source is expressed by
`Functor.IsRepresentedBy` on the category of schemes over `S`, whose specified universal element
is the image of the coordinate `X` under the global-sections isomorphism for `Spec`, pulled back
along the first projection of the defining fibre product.

For `n = 0` the coordinate ring is `ℤ[X]`, whose universal element is not invertible, so the
group-scheme assertions require `0 < n`; this is also the Stacks Project convention that natural
numbers are positive.

## References

* [Stacks Project, Tag 040M](https://stacks.math.columbia.edu/tag/040M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The coordinate ring of the scheme of `n`-th roots of unity. -/
@[sga "1 XI 6.1" "partial", sga "3 I 4.4.4"]
abbrev rootsOfUnityCoordinateRing (n : ℕ) : Type u :=
  Polynomial (ULift.{u} ℤ) ⧸
    Ideal.span ({Polynomial.X ^ n - 1} : Set (Polynomial (ULift.{u} ℤ)))

/-- **Stacks Project, Tag 040M.** The scheme of `n`-th roots of unity over the integers is
`Spec (ℤ[X] / (Xⁿ - 1))`. -/
@[stacks 040M "roots_of_unity_scheme",
  sga "3 I 4.4.4" "μ_n = Spec Z[x]/(x^n-1)",
  sga "1 XI 6.1" "special case"]
noncomputable abbrev rootsOfUnity (n : ℕ) : Scheme.{u} :=
  Spec (.of (rootsOfUnityCoordinateRing.{u} n))

/-- The canonical structure morphism from the scheme of roots of unity to the integer base. -/
@[stacks 040M "roots_of_unity_scheme"]
noncomputable instance rootsOfUnityCanonicallyOver (n : ℕ) :
    (rootsOfUnity n).CanonicallyOver (Spec (.of (ULift.{u} ℤ))) where
  hom := Spec.map <| CommRingCat.ofHom <| (Ideal.Quotient.mk _).comp Polynomial.C

/-- **Stacks Project, Tag 040M.** The scheme of `n`-th roots of unity over `S` is the base change
of the scheme of roots of unity over the integers along the unique map from `S` to the integer
base. -/
@[stacks 040M "roots_of_unity_scheme",
  sga "3 I 4.4.4" "μ_{n,S}",
  sga "1 XI 6.1",
  sga "3 VIIB 2.5.2.A" "partial"]
noncomputable abbrev rootsOfUnityBaseChange (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  ((Over.pullback (specULiftZIsTerminal.from S)).obj
    (Scheme.asOver (rootsOfUnity n) (Spec (.of (ULift.{u} ℤ))))).left

/-- The set-valued functor sending a scheme `T` to the units `f` of its ring of global sections
such that `f ^ n = 1`. -/
def rootsOfUnitySections (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := { f : (Scheme.Γ.obj T)ˣ // f ^ n = 1 }
  map {X Y} g := ↾fun (f : { f : (Scheme.Γ.obj X)ˣ // f ^ n = 1 }) =>
    ⟨Units.map (Scheme.Γ.map g).hom.toMonoidHom f.1, by
      rw [← map_pow, f.property, map_one]⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact congrArg (fun k => k f.1)
      ((Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
        forget CommGrpCat).map_id T)
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact congrArg (fun k => k f.1)
      ((Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
        forget CommGrpCat).map_comp g h)

/-- The coordinate-ring homomorphism attached to a root of unity in a ring. -/
noncomputable def rootsRingHom {A : Type u} [CommRing A] (n : ℕ)
    (f : { f : Aˣ // f ^ n = 1 }) : rootsOfUnityCoordinateRing.{u} n →+* A :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) f.1) <| by
      intro p hp
      rw [Ideal.mem_span_singleton] at hp
      obtain ⟨q, rfl⟩ := hp
      have hf' : (f.1 : A) ^ n = 1 := congrArg Units.val f.2
      simp [hf']

/-- A ring homomorphism between the carriers of two bundled commutative rings, as a morphism of
`CommRingCat`. -/
def bundledRingHom {R S : CommRingCat} (f : R →+* S) : R ⟶ S := by
  cases R
  cases S
  exact CommRingCat.ofHom f

@[simp] private theorem bundledRingHom_hom {R S : CommRingCat} (f : R →+* S) :
    (bundledRingHom f).hom = f := by
  cases R
  cases S
  rfl

@[simp] private theorem bundledRingHom_apply {R S : CommRingCat} (f : R →+* S) (x : R) :
    (bundledRingHom f).hom x = f x := by rw [bundledRingHom_hom]

@[simp] private theorem bundledRingHom_unop_op_apply {R S : CommRingCat} (f : R →+* S) (x : R) :
    (Opposite.unop (bundledRingHom f).op).hom x = f x :=
  congrArg (fun h : R ⟶ S => h.hom x) (Quiver.Hom.unop_op (bundledRingHom f))

/-- Morphisms from a scheme to the roots-of-unity scheme are exactly `n`-th roots of unity in its
ring of global sections. -/
noncomputable def rootsEquiv (n : ℕ) (hn : 0 < n) (X : Scheme.{u}) :
    (X ⟶ rootsOfUnity n) ≃ { f : (Scheme.Γ.obj (Opposite.op X))ˣ // f ^ n = 1 } where
  toFun g := by
    let h : rootsOfUnityCoordinateRing.{u} n →+* Scheme.Γ.obj (Opposite.op X) :=
      ((ΓSpec.adjunction.homEquiv X
        (Opposite.op (.of (rootsOfUnityCoordinateRing.{u} n)))).symm g).unop.hom
    let a := h (Ideal.Quotient.mk _ Polynomial.X)
    have ha : a ^ n = 1 := by
      have hx : (Ideal.Quotient.mk (Ideal.span ({Polynomial.X ^ n - 1} :
          Set (Polynomial (ULift.{u} ℤ)))) Polynomial.X) ^ n = 1 := by
        change Ideal.Quotient.mk _ (Polynomial.X ^ n) = Ideal.Quotient.mk _ 1
        exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))
      exact (map_pow h _ n).symm.trans (by rw [hx, map_one])
    exact ⟨Units.ofPowEqOne a n ha (Nat.ne_of_gt hn),
      Units.pow_ofPowEqOne ha (Nat.ne_of_gt hn)⟩
  invFun f := ΓSpec.adjunction.homEquiv X
    (Opposite.op (.of (rootsOfUnityCoordinateRing.{u} n)))
    (bundledRingHom (rootsRingHom (A := Scheme.Γ.obj (Opposite.op X)) n f)).op
  left_inv g := by
    apply (ΓSpec.adjunction.homEquiv _ _).symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Opposite.unop_injective
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · rintro ⟨z⟩
      change (Opposite.unop (bundledRingHom
        (R := CommRingCat.of (rootsOfUnityCoordinateRing.{u} n))
        (S := Scheme.Γ.obj (Opposite.op X)) (rootsRingHom n _)).op).hom
        (Ideal.Quotient.mk _ (Polynomial.C (ULift.up z))) = _
      rw [bundledRingHom_unop_op_apply, rootsRingHom, Ideal.Quotient.lift_mk,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      have hz : Polynomial.C (ULift.up z) = (z : Polynomial (ULift.{u} ℤ)) := by
        rw [show ULift.up z = (z : ULift.{u} ℤ) by apply ULift.ext; simp]
        exact map_intCast (Polynomial.C : ULift.{u} ℤ →+* _) z
      rw [hz]
      exact (map_intCast _ z).symm
    · change (Opposite.unop (bundledRingHom
        (R := CommRingCat.of (rootsOfUnityCoordinateRing.{u} n))
        (S := Scheme.Γ.obj (Opposite.op X)) (rootsRingHom n _)).op).hom
        (Ideal.Quotient.mk _ Polynomial.X) = _
      rw [bundledRingHom_unop_op_apply, rootsRingHom, Ideal.Quotient.lift_mk,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  right_inv f := by
    apply Subtype.ext
    apply Units.ext
    simp only [Equiv.symm_apply_apply]
    change (bundledRingHom (R := CommRingCat.of (rootsOfUnityCoordinateRing.{u} n))
      (S := Scheme.Γ.obj (Opposite.op X)) (rootsRingHom n f)).hom
      (Ideal.Quotient.mk _ Polynomial.X) = f.1
    rw [bundledRingHom_apply, rootsRingHom, Ideal.Quotient.lift_mk]
    simpa only [Polynomial.coe_eval₂RingHom] using
      (Polynomial.eval₂_X
        ((Int.castRingHom (Scheme.Γ.obj (Opposite.op X))).comp ULift.ringEquiv.toRingHom) f.1)

/-- **Stacks Project, Tag 040M.** The functor of units in global sections whose `n`-th power is
one is represented by `Spec (ℤ[X] / (Xⁿ - 1))`. -/
@[stacks 040M "representability", sga "1 XI 6.1" "special case"]
theorem rootsOfUnitySections_representableBy_rootsOfUnity (n : ℕ) (hn : 0 < n) :
    Nonempty ((rootsOfUnitySections n).RepresentableBy (rootsOfUnity n : Scheme.{u})) :=
  ⟨⟨fun {X} ↦ rootsEquiv n hn X, fun _ _ ↦ Subtype.ext (Units.ext rfl)⟩⟩

/-- The product of the images of the universal root in the two tensor factors. -/
noncomputable def rootsOfUnityTensorRoot (n : ℕ) :
    TensorProduct (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
      (rootsOfUnityCoordinateRing.{u} n) :=
  (Algebra.TensorProduct.includeLeft (R := ULift.{u} ℤ) (S := ULift.{u} ℤ)
      (A := rootsOfUnityCoordinateRing.{u} n) (B := rootsOfUnityCoordinateRing.{u} n))
      (Ideal.Quotient.mk _ Polynomial.X) *
    (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
      (A := rootsOfUnityCoordinateRing.{u} n) (B := rootsOfUnityCoordinateRing.{u} n))
      (Ideal.Quotient.mk _ Polynomial.X)

/-- The class of `X` in `ℤ[X] / (Xⁿ - 1)` has `n`-th power one. -/
private theorem mk_X_pow_eq_one (n : ℕ) :
    (Ideal.Quotient.mk (Ideal.span ({Polynomial.X ^ n - 1} : Set (Polynomial (ULift.{u} ℤ))))
      Polynomial.X) ^ n = 1 := by
  change Ideal.Quotient.mk _ (Polynomial.X ^ n) = Ideal.Quotient.mk _ 1
  exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The ideal defining the coordinate ring is annihilated by evaluation at the product of the
images of the universal root. -/
lemma aeval_rootsOfUnityTensorRoot_eq_zero (n : ℕ)
    (p : Polynomial (ULift.{u} ℤ))
    (hp : p ∈ Ideal.span ({Polynomial.X ^ n - 1} : Set (Polynomial (ULift.{u} ℤ)))) :
    Polynomial.aeval (rootsOfUnityTensorRoot.{u} n) p = 0 := by
  have hroot : rootsOfUnityTensorRoot.{u} n ^ n = 1 := by
    rw [rootsOfUnityTensorRoot, mul_pow, ← map_pow _ (Ideal.Quotient.mk _ Polynomial.X),
      ← map_pow _ (Ideal.Quotient.mk _ Polynomial.X), mk_X_pow_eq_one,
      _root_.map_one, _root_.map_one, _root_.mul_one]
  refine Submodule.span_induction
    (p := fun p _ ↦ Polynomial.aeval (rootsOfUnityTensorRoot.{u} n) p = 0) ?_ (map_zero _)
    ?_ ?_ hp
  · intro q hq
    rw [Set.mem_singleton_iff.mp hq, map_sub, map_pow, Polynomial.aeval_X, map_one, hroot,
      sub_self]
  · intro a b ha hb hfa hfb
    rw [map_add, hfa, hfb, add_zero]
  · intro a b hb hfb
    rw [smul_eq_mul, map_mul, hfb, mul_zero]

/-- The coordinate-ring homomorphism defining multiplication of roots of unity. It sends
the universal root to the product of its images in the two tensor factors. -/
noncomputable def rootsOfUnityMultiplicationRingHom (n : ℕ) :
    rootsOfUnityCoordinateRing.{u} n →+*
      TensorProduct (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
        (rootsOfUnityCoordinateRing.{u} n) :=
  (Ideal.Quotient.liftₐ _ (Polynomial.aeval (rootsOfUnityTensorRoot.{u} n))
    (aeval_rootsOfUnityTensorRoot_eq_zero n)).toRingHom

/-- `rootsOfUnityMultiplicationRingHom` sends the class of a polynomial `p` to `p` evaluated at
`rootsOfUnityTensorRoot n`. -/
lemma rootsOfUnityMultiplicationRingHom_mk (n : ℕ) (p : Polynomial (ULift.{u} ℤ)) :
    rootsOfUnityMultiplicationRingHom.{u} n (Ideal.Quotient.mk _ p) =
      Polynomial.aeval (rootsOfUnityTensorRoot.{u} n) p := rfl

/-- The multiplication morphism on the scheme of roots of unity. -/
noncomputable def rootsOfUnityMultiplication (n : ℕ) :
    pullback (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))
        (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ))) ⟶ rootsOfUnity n :=
  (pullbackSpecIso (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
      (rootsOfUnityCoordinateRing.{u} n)).hom ≫
    Spec.map (CommRingCat.ofHom (rootsOfUnityMultiplicationRingHom n))

open CartesianMonoidalCategory

/-- The subgroup of units whose `n`-th power is one. -/
@[implicit_reducible]
def rootsUnitsSubgroup {A : Type u} [CommRing A] (n : ℕ) : Subgroup Aˣ where
  carrier := {x | x ^ n = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a ^ n = 1 at ha
    change b ^ n = 1 at hb
    change (a * b) ^ n = 1
    simp [mul_pow, ha, hb]
  inv_mem' := by
    intro a ha
    change a ^ n = 1 at ha
    change (a⁻¹) ^ n = 1
    simp [inv_pow, ha]

/-- The group structure on the `n`-th roots of unity in a commutative ring. -/
@[instance_reducible, sga "1 XI 6.1" "partial"]
noncomputable def rootsSectionsGroup {A : Type u} [CommRing A] (n : ℕ) :
    Group {x : Aˣ // x ^ n = 1} := by
  change Group ↑(rootsUnitsSubgroup (A := A) n)
  infer_instance

/-- The group-valued functor of `n`-th roots of unity in global sections, on schemes over the
integers. -/
@[sga "1 XI 6.1" "special case", sga "3 I 4.4.4"]
noncomputable def rootsOfUnityGroupFunctor (n : ℕ) :
    (Over (Spec (.of (ULift.{u} ℤ))) : Type (u + 1))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := by
    letI : Group ((rootsOfUnitySections n).obj (Opposite.op T.unop.left)) :=
      rootsSectionsGroup (A := Scheme.Γ.obj (Opposite.op T.unop.left)) n
    exact GrpCat.of ((rootsOfUnitySections n).obj (Opposite.op T.unop.left))
  map {X Y} f := by
    letI : Group ((rootsOfUnitySections n).obj (Opposite.op X.unop.left)) :=
      rootsSectionsGroup (A := Scheme.Γ.obj (Opposite.op X.unop.left)) n
    letI : Group ((rootsOfUnitySections n).obj (Opposite.op Y.unop.left)) :=
      rootsSectionsGroup (A := Scheme.Γ.obj (Opposite.op Y.unop.left)) n
    exact GrpCat.ofHom
      { toFun := (rootsOfUnitySections n).map f.unop.left.op
        map_one' := Subtype.ext (map_one (Units.map (Scheme.Γ.map f.unop.left.op).hom.toMonoidHom))
        map_mul' a b := Subtype.ext
          (map_mul (Units.map (Scheme.Γ.map f.unop.left.op).hom.toMonoidHom) a.1 b.1) }
  map_id T := by
    apply GrpCat.ext
    intro x
    exact congrArg (fun k => k x)
      ((rootsOfUnitySections n).map_id (Opposite.op T.unop.left))
  map_comp f g := by
    apply GrpCat.ext
    intro x
    exact congrArg (fun k => k x)
      ((rootsOfUnitySections n).map_comp f.unop.left.op g.unop.left.op)

attribute [local instance] rootsSectionsGroup

private noncomputable abbrev rootsTensorProductCat (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (TensorProduct (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
    (rootsOfUnityCoordinateRing.{u} n))

private noncomputable def rootsTensorIncludeLeft (n : ℕ) :
    CommRingCat.of (rootsOfUnityCoordinateRing.{u} n) ⟶ rootsTensorProductCat n :=
  CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft
    (R := ULift.{u} ℤ) (S := ULift.{u} ℤ)
    (A := rootsOfUnityCoordinateRing.{u} n) (B := rootsOfUnityCoordinateRing.{u} n) :
    rootsOfUnityCoordinateRing.{u} n →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
        (rootsOfUnityCoordinateRing.{u} n)).toRingHom)

private noncomputable def rootsTensorIncludeRight (n : ℕ) :
    CommRingCat.of (rootsOfUnityCoordinateRing.{u} n) ⟶ rootsTensorProductCat n :=
  CommRingCat.ofHom ((Algebra.TensorProduct.includeRight
    (R := ULift.{u} ℤ)
    (A := rootsOfUnityCoordinateRing.{u} n) (B := rootsOfUnityCoordinateRing.{u} n) :
    rootsOfUnityCoordinateRing.{u} n →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
        (rootsOfUnityCoordinateRing.{u} n)).toRingHom)

private theorem rootsEquiv_val (n : ℕ) (hn : 0 < n) {X : Scheme.{u}}
    (g : X ⟶ rootsOfUnity n) :
    (↑(rootsEquiv n hn X g).1 : Scheme.Γ.obj (Opposite.op X)) =
      ((Scheme.ΓSpecIso (.of (rootsOfUnityCoordinateRing.{u} n))).inv ≫ g.appTop)
        (Ideal.Quotient.mk _ Polynomial.X) := rfl

private theorem rootsEquiv_comp (n : ℕ) (hn : 0 < n) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ rootsOfUnity n) :
    rootsEquiv n hn X (f ≫ g) = (rootsOfUnitySections n).map f.op (rootsEquiv n hn Y g) := by
  apply Subtype.ext
  apply Units.ext
  rfl

private theorem rootsEquiv_specMap_val (n : ℕ) (hn : 0 < n) {B : CommRingCat.{u}}
    (f : CommRingCat.of (rootsOfUnityCoordinateRing.{u} n) ⟶ B) :
    (↑(rootsEquiv n hn (Spec B) (Spec.map f)).1 : Scheme.Γ.obj (Opposite.op (Spec B))) =
      (Scheme.ΓSpecIso B).inv (f (Ideal.Quotient.mk _ Polynomial.X)) := by
  rw [rootsEquiv_val]
  exact (congrArg (fun h : CommRingCat.of (rootsOfUnityCoordinateRing.{u} n) ⟶
      Scheme.Γ.obj (Opposite.op (Spec B)) => h (Ideal.Quotient.mk _ Polynomial.X))
    (Scheme.ΓSpecIso_inv_naturality f)).symm

private theorem rootsEquiv_specMap_mul (n : ℕ) (hn : 0 < n) :
    rootsEquiv.{u} n hn (Spec.{u} (rootsTensorProductCat n))
        (Spec.map (rootsTensorIncludeLeft n)) *
      rootsEquiv.{u} n hn (Spec.{u} (rootsTensorProductCat n))
        (Spec.map (rootsTensorIncludeRight n)) =
      rootsEquiv.{u} n hn (Spec.{u} (rootsTensorProductCat n))
        (Spec.map (CommRingCat.ofHom (rootsOfUnityMultiplicationRingHom n))) := by
  apply Subtype.ext
  apply Units.ext
  change (rootsEquiv n hn (Spec (rootsTensorProductCat n))
      (Spec.map (rootsTensorIncludeLeft n))).1.1 *
    (rootsEquiv n hn (Spec (rootsTensorProductCat n))
      (Spec.map (rootsTensorIncludeRight n))).1.1 =
    (rootsEquiv n hn (Spec (rootsTensorProductCat n))
      (Spec.map (CommRingCat.ofHom (rootsOfUnityMultiplicationRingHom n)))).1.1
  rw [rootsEquiv_specMap_val, rootsEquiv_specMap_val, rootsEquiv_specMap_val]
  let x : rootsOfUnityCoordinateRing.{u} n := Ideal.Quotient.mk
    (Ideal.span ({Polynomial.X ^ n - 1} : Set (Polynomial (ULift.{u} ℤ)))) Polynomial.X
  have hx : (rootsTensorIncludeLeft n).hom x * (rootsTensorIncludeRight n).hom x =
      rootsOfUnityMultiplicationRingHom n x := by
    rw [rootsOfUnityMultiplicationRingHom_mk, Polynomial.aeval_X, rootsOfUnityTensorRoot]
    rfl
  calc
    _ = (Scheme.ΓSpecIso (rootsTensorProductCat n)).inv
        ((rootsTensorIncludeLeft n).hom x * (rootsTensorIncludeRight n).hom x) :=
          (map_mul _ _ _).symm
    _ = (Scheme.ΓSpecIso (rootsTensorProductCat n)).inv
        (rootsOfUnityMultiplicationRingHom n x) := congrArg _ hx

private theorem rootsSectionsMap_injective (n : ℕ) {X Y : Scheme.{u}} (f : X ≅ Y) :
    Function.Injective ((rootsOfUnitySections n).map f.hom.op) := by
  intro a b hab
  apply Subtype.ext
  have hleft : Function.LeftInverse
      (Units.map (Scheme.Γ.map f.symm.hom.op).hom.toMonoidHom)
      (Units.map (Scheme.Γ.map f.hom.op).hom.toMonoidHom) := by
    intro x
    apply Units.ext
    have hcomp : Scheme.Γ.map f.hom.op ≫ Scheme.Γ.map f.symm.hom.op = 𝟙 _ := by
      rw [← Functor.map_comp]
      simp
    change (Scheme.Γ.map f.hom.op ≫ Scheme.Γ.map f.symm.hom.op).hom
      (x : Scheme.Γ.obj (Opposite.op Y)) = x
    exact congrArg (fun g : CommRingCat.Hom _ _ =>
      g.hom (x : Scheme.Γ.obj (Opposite.op Y))) hcomp
  exact hleft.injective (congrArg Subtype.val hab)

/-- Morphisms of schemes over the integers to the roots-of-unity scheme are exactly `n`-th roots
of unity in global sections. -/
noncomputable def rootsOverEquiv (n : ℕ) (hn : 0 < n) (X : Over (Spec (.of (ULift.{u} ℤ)))) :
    (X ⟶ Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))) ≃
      ↑(rootsUnitsSubgroup (A := Scheme.Γ.obj (Opposite.op X.left)) n) where
  toFun f := rootsEquiv n hn X.left f.left
  invFun x := Over.homMk ((rootsEquiv n hn X.left).symm x) (specULiftZIsTerminal.hom_ext _ _)
  left_inv f := Over.OverMorphism.ext ((rootsEquiv n hn X.left).left_inv f.left)
  right_inv x := (rootsEquiv n hn X.left).right_inv x

/-- `rootsOverEquiv` sends a morphism over the integers to the root of unity that `rootsEquiv`
assigns to its underlying morphism of schemes. -/
theorem rootsOverEquiv_apply (n : ℕ) (hn : 0 < n) (X : Over (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))) :
    rootsOverEquiv n hn X f = rootsEquiv n hn X.left f.left := rfl

/-- The roots-of-unity scheme over the integers, as a representing object for the group-valued
functor of roots of unity in global sections. -/
@[sga "3 I 4.4.4"]
noncomputable def rootsOfUnityRepresentableBy (n : ℕ) (hn : 0 < n) :
    (rootsOfUnityGroupFunctor n ⋙ forget GrpCat).RepresentableBy
      (Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))) where
  homEquiv {X} := rootsOverEquiv n hn X
  homEquiv_comp _ _ := Subtype.ext (Units.ext rfl)

/-- The group-object structure on the scheme of positive-order roots of unity over the
integers. -/
@[stacks 040M "group_scheme", sga "3 I 4.4.4"]
noncomputable instance rootsOfUnityGrpObj (n : ℕ) [Fact (0 < n)] :
    GrpObj (Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))) :=
  GrpObj.ofRepresentableBy _ (rootsOfUnityGroupFunctor n)
    (rootsOfUnityRepresentableBy n Fact.out)

/-- **Stacks Project, Tag 040M.** The scheme of `n`-th roots of unity is a group scheme over
the integers, with multiplication induced by `X ↦ X ⊗ X` on coordinate rings. -/
@[stacks 040M "group_scheme"]
theorem rootsOfUnityGrpObj_mul (n : ℕ) (hn : 0 < n) :
    (letI : Fact (0 < n) := ⟨hn⟩
    μ[Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))].left =
      rootsOfUnityMultiplication n) := by
  let : Fact (0 < n) := ⟨hn⟩
  let G := Over.mk (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))
  let α := rootsOfUnityRepresentableBy n hn
  let : GrpObj G := GrpObj.ofRepresentableBy G (rootsOfUnityGroupFunctor n) α
  let : Group {x : (Scheme.Γ.obj (Opposite.op (G ⊗ G).left))ˣ // x ^ n = 1} :=
    rootsSectionsGroup (A := Scheme.Γ.obj (Opposite.op (G ⊗ G).left)) n
  let rhs : G ⊗ G ⟶ G :=
    Over.homMk (rootsOfUnityMultiplication n) (specULiftZIsTerminal.hom_ext _ _)
  have hmul : μ[G] = rhs := by
    apply α.homEquiv'.injective
    change α.homEquiv' (α.homEquiv'.symm
      (α.homEquiv' (CartesianMonoidalCategory.fst G G) *
        α.homEquiv' (CartesianMonoidalCategory.snd G G))) = α.homEquiv' rhs
    simp only [Equiv.apply_symm_apply]
    change rootsEquiv n hn (G ⊗ G).left (CartesianMonoidalCategory.fst G G).left *
      rootsEquiv n hn (G ⊗ G).left (CartesianMonoidalCategory.snd G G).left =
      rootsEquiv n hn (G ⊗ G).left rhs.left
    let B := TensorProduct (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
      (rootsOfUnityCoordinateRing.{u} n)
    let P := pullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n))))
    let : Group ((rootsOfUnitySections n).obj (Opposite.op P)) :=
      rootsSectionsGroup (A := Scheme.Γ.obj (Opposite.op P)) n
    let e := pullbackSpecIso (ULift.{u} ℤ) (rootsOfUnityCoordinateRing.{u} n)
      (rootsOfUnityCoordinateRing.{u} n)
    let iL := rootsTensorIncludeLeft n
    let iR := rootsTensorIncludeRight n
    let : Group ((rootsOfUnitySections n).obj (Opposite.op (Spec (CommRingCat.of B)))) :=
      rootsSectionsGroup (A := Scheme.Γ.obj (Opposite.op (Spec (CommRingCat.of B)))) n
    have hfst : e.hom ≫ Spec.map iL = pullback.fst _ _ := pullbackSpecIso_hom_fst _ _ _
    have hsnd : e.hom ≫ Spec.map iR = pullback.snd _ _ := pullbackSpecIso_hom_snd _ _ _
    let m : CommRingCat.of (rootsOfUnityCoordinateRing.{u} n) ⟶ CommRingCat.of B :=
      CommRingCat.ofHom (rootsOfUnityMultiplicationRingHom n)
    have hmapmul (a b : (rootsOfUnitySections n).obj (Opposite.op P)) :
        (rootsOfUnitySections n).map e.symm.hom.op (a * b) =
          (rootsOfUnitySections n).map e.symm.hom.op a *
            (rootsOfUnitySections n).map e.symm.hom.op b := by
      apply Subtype.ext
      apply Units.ext
      change (Scheme.Γ.map e.symm.hom.op).hom
          ((a.1 : Scheme.Γ.obj (Opposite.op P)) * (b.1 : Scheme.Γ.obj (Opposite.op P))) =
        (Scheme.Γ.map e.symm.hom.op).hom (a.1 : Scheme.Γ.obj (Opposite.op P)) *
          (Scheme.Γ.map e.symm.hom.op).hom (b.1 : Scheme.Γ.obj (Opposite.op P))
      exact map_mul _ _ _
    have hfsti : e.symm.hom ≫ pullback.fst _ _ = Spec.map iL := by
      rw [← hfst, Iso.symm_hom, Iso.inv_hom_id_assoc]
    have hsndi : e.symm.hom ≫ pullback.snd _ _ = Spec.map iR := by
      rw [← hsnd, Iso.symm_hom, Iso.inv_hom_id_assoc]
    have hr : e.symm.hom ≫ (e.hom ≫ Spec.map m) = Spec.map m := e.inv_hom_id_assoc _
    change rootsEquiv n hn P (pullback.fst _ _) * rootsEquiv n hn P (pullback.snd _ _) =
      rootsEquiv n hn P (e.hom ≫ Spec.map m)
    apply rootsSectionsMap_injective n e.symm
    apply (hmapmul _ _).trans
    rw [← rootsEquiv_comp, ← rootsEquiv_comp, ← rootsEquiv_comp, hfsti, hsndi, hr]
    change rootsEquiv n hn (Spec (CommRingCat.of B)) (Spec.map iL) *
      rootsEquiv n hn (Spec (CommRingCat.of B)) (Spec.map iR) =
        rootsEquiv n hn (Spec (CommRingCat.of B)) (Spec.map m)
    exact rootsEquiv_specMap_mul n hn
  exact congrArg Over.Hom.left hmul

add_to_stacks 040M "base_change_group_scheme" AlgebraicGeometry.Scheme.GrpObjAsOverPullback
add_to_stacks 040M "base_change_group_scheme" CategoryTheory.Functor.obj.μ_def

/-- The polynomial coordinate `X`, as a unit in `ℤ[X] / (X ^ n - 1)`. -/
noncomputable def rootsOfUnityCoordinate (n : ℕ) (hn : 0 < n) :
    (rootsOfUnityCoordinateRing.{u} n)ˣ where
  val := Ideal.Quotient.mk _ Polynomial.X
  inv := Ideal.Quotient.mk _ Polynomial.X ^ (n - 1)
  val_inv := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
    change Ideal.Quotient.mk _ (Polynomial.X ^ n) = Ideal.Quotient.mk _ 1
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))
  inv_val := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
    change Ideal.Quotient.mk _ (Polynomial.X ^ n) = Ideal.Quotient.mk _ 1
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The coordinate unit has `n`-th power one. -/
lemma rootsOfUnityCoordinate_pow (n : ℕ) (hn : 0 < n) :
    rootsOfUnityCoordinate.{u} n hn ^ n = 1 := by
  exact Units.ext (mk_X_pow_eq_one n)

/-- The universal `n`-th root of unity in the global sections of `μ_n`, obtained from its
polynomial coordinate. -/
noncomputable def rootsOfUnityUniversalRoot (n : ℕ) (hn : 0 < n) :
    (rootsOfUnitySections n).obj (Opposite.op (rootsOfUnity n : Scheme.{u})) :=
  (⟨Units.map
      (Scheme.ΓSpecIso (.of (rootsOfUnityCoordinateRing.{u} n))).inv.hom.toMonoidHom
      (rootsOfUnityCoordinate n hn), by
        rw [← map_pow, rootsOfUnityCoordinate_pow n hn, map_one]⟩ :
    { f : Γ(Spec (.of (rootsOfUnityCoordinateRing.{u} n)), ⊤)ˣ // f ^ n = 1 })

/-- The universal root on the base change `μ_{n,S}`. It is the pullback of the coordinate root
on `μ_n` along the first projection of the fibre product defining `μ_{n,S}`. -/
noncomputable def rootsOfUnityBaseChangeUniversalRoot (n : ℕ) (hn : 0 < n) (S : Scheme.{u}) :
    (((Over.forget S).op ⋙ rootsOfUnitySections n).obj
      (Opposite.op (Scheme.asOver (rootsOfUnityBaseChange n S) S))) := by
  change { f : (Scheme.Γ.obj (Opposite.op (rootsOfUnityBaseChange n S)))ˣ // f ^ n = 1 }
  let projection : rootsOfUnityBaseChange n S ⟶ rootsOfUnity n :=
    Limits.pullback.fst (rootsOfUnity n ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S)
  refine ⟨Units.map (Scheme.Γ.map projection.op).hom.toMonoidHom
        (rootsOfUnityUniversalRoot n hn).1, ?_⟩
  rw [← map_pow, (rootsOfUnityUniversalRoot n hn).property, map_one]

private noncomputable def ringHomOfRoot (n : ℕ) {A : Type u} [CommRing A] (x : Aˣ)
    (hx : x ^ n = 1) : rootsOfUnityCoordinateRing.{u} n →+* A :=
  rootsRingHom n ⟨x, hx⟩

private theorem ringHomOfRoot_unique (n : ℕ) {A : Type u} [CommRing A]
    (f g : rootsOfUnityCoordinateRing.{u} n →+* A)
    (h : f (Ideal.Quotient.mk _ Polynomial.X) = g (Ideal.Quotient.mk _ Polynomial.X)) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext'
  · apply RingHom.ext
    rintro ⟨z⟩
    change f (Ideal.Quotient.mk _ (Polynomial.C (z : ULift.{u} ℤ))) =
      g (Ideal.Quotient.mk _ (Polynomial.C (z : ULift.{u} ℤ)))
    simp only [map_intCast]
  · exact h

private lemma ringHomOfRoot_X (n : ℕ) {A : Type u} [CommRing A] (x : Aˣ) (hx : x ^ n = 1) :
    ringHomOfRoot n x hx (Ideal.Quotient.mk _ Polynomial.X) = x := by
  simp [ringHomOfRoot, rootsRingHom, Polynomial.eval₂RingHom]

@[sga "3 I 4.4.4" "partial, special case"]
private theorem coordinate_represents (n : ℕ) (hn : 0 < n) :
    (rootsOfUnitySections n).IsRepresentedBy (rootsOfUnityUniversalRoot.{u} n hn) := by
  constructor
  intro T
  constructor
  · intro f g h
    apply ext_to_Spec
    apply CommRingCat.hom_ext
    apply ringHomOfRoot_unique n
    exact congrArg (fun a : {z : (Scheme.Γ.obj (Opposite.op T))ˣ // z ^ n = 1} =>
      (a.1 : Scheme.Γ.obj (Opposite.op T))) h
  · intro x
    let φ := ringHomOfRoot n x.1 x.2
    let f : T ⟶ rootsOfUnity n :=
      (ΓSpec.adjunction.homEquiv T (.op (.of _))) (CommRingCat.ofHom φ).op
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change f.appTop ((Scheme.ΓSpecIso
      (.of (rootsOfUnityCoordinateRing.{u} n))).inv
      (Ideal.Quotient.mk _ Polynomial.X)) = x.1.val
    have hφ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := T)
      (B := .of (rootsOfUnityCoordinateRing.{u} n)) (CommRingCat.ofHom φ)
    have hv := congrArg
        (fun h : (CommRingCat.of (rootsOfUnityCoordinateRing.{u} n)) ⟶ Γ(T, ⊤) =>
          h (Ideal.Quotient.mk _ Polynomial.X)) hφ
    change f.appTop ((Scheme.ΓSpecIso
      (.of (rootsOfUnityCoordinateRing.{u} n))).inv (Ideal.Quotient.mk _ Polynomial.X)) =
      φ (Ideal.Quotient.mk _ Polynomial.X) at hv
    exact hv.trans (ringHomOfRoot_X n x.1 x.2)

/-- **Stacks Project, Tag 040M.** For every scheme `S`, the base change to `S` of the scheme of
`n`-th roots of unity represents, naturally in an `S`-scheme `T`, the units in `Γ(T, 𝒪_T)` whose
`n`-th power is one. The representing universal element is the pullback of the polynomial
coordinate `X` along the base-change projection. -/
@[stacks 040M "base_change_points", sga "1 XI 6.1", sga "3 I 4.4.4", sga "3 VIIA 4.1.4" "partial"]
theorem rootsOfUnitySectionsOver_representableBy_rootsOfUnityBaseChange
    (n : ℕ) (hn : 0 < n) (S : Scheme.{u}) :
    ((Over.forget S).op ⋙ rootsOfUnitySections n).IsRepresentedBy
      (rootsOfUnityBaseChangeUniversalRoot n hn S) := by
  let R := rootsOfUnity.{u} n
  let Z := Spec (.of (ULift.{u} ℤ))
  let b : S ⟶ Z := specULiftZIsTerminal.from S
  let P := rootsOfUnityBaseChange n S
  let π : P ⟶ R := Limits.pullback.fst (R ↘ Z) b
  have hmap (T : Over S) (f : T ⟶ Scheme.asOver P S) :
      (((Over.forget S).op ⋙ rootsOfUnitySections n).map
        f.op (rootsOfUnityBaseChangeUniversalRoot n hn S)) =
      (rootsOfUnitySections n).map (f.left ≫ π).op (rootsOfUnityUniversalRoot n hn) := by
    let F := rootsOfUnitySections.{u} n
    let q : (Scheme.asOver P S).left ⟶ R := π
    change F.map f.left.op (F.map q.op (rootsOfUnityUniversalRoot n hn)) =
      F.map (f.left ≫ q).op (rootsOfUnityUniversalRoot n hn)
    exact congrArg (fun h => h (rootsOfUnityUniversalRoot n hn))
      (F.map_comp q.op f.left.op).symm
  constructor
  intro T
  have hrep := (coordinate_represents n hn).map_bijective (Y := T.left)
  constructor
  · intro f g h
    apply CostructuredArrow.hom_ext
    apply Limits.pullback.hom_ext
    · exact hrep.injective ((hmap T f).symm.trans (h.trans (hmap T g)))
    · exact (Over.w f).trans (Over.w g).symm
  · intro x
    obtain ⟨m, hm⟩ := hrep.surjective x
    let l : T.left ⟶ P := Limits.pullback.lift m T.hom
      (specULiftZIsTerminal.hom_ext (m ≫ (R ↘ Z)) (T.hom ≫ b))
    let f : T ⟶ Scheme.asOver P S := Over.homMk l (Limits.pullback.lift_snd _ _ _)
    refine ⟨f, ?_⟩
    change (((Over.forget S).op ⋙ rootsOfUnitySections n).map
      f.op (rootsOfUnityBaseChangeUniversalRoot n hn S)) = x
    rw [hmap]
    change (rootsOfUnitySections n).map (l ≫ π).op (rootsOfUnityUniversalRoot n hn) = x
    rwa [show l ≫ π = m from Limits.pullback.lift_fst _ _ _]

end AlgebraicGeometry

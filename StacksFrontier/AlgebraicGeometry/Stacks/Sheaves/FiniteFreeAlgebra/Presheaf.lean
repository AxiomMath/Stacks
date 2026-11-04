module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The presheaf in groupoids of finite free algebras

For a positive integer `d`, commutative algebra structures on a free module of rank `d`, with
the first basis vector as unit, and their algebra isomorphisms form a groupoid. Extension of
their structure constants and isomorphism matrices makes these groupoids into the presheaf
`FA_d` on the big fppf site.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.StructureIso`: an isomorphism between two free algebra
  structures, described by its invertible matrix.
* `AlgebraicGeometry.FiniteFreeAlgebra.baseChange`: extension of scalars as a functor of
  groupoids.
* `AlgebraicGeometry.FiniteFreeAlgebra.Presheaf`: the functor `FA_d`, including its
  identifications on objects and arrows and their compatibility with base change.
* `AlgebraicGeometry.FiniteFreeAlgebra.presheaf`: the construction of `FA_d`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.sum_four_swap`,
  `AlgebraicGeometry.FiniteFreeAlgebra.sum_four_rotate`: reorderings of a fourfold sum.
* `AlgebraicGeometry.FiniteFreeAlgebra.sum_bilinear_change`: the effect of a change of basis on
  a bilinear expression in structure constants.
* `AlgebraicGeometry.FiniteFreeAlgebra.StructureIso.ext`: an isomorphism of structures is
  determined by its matrix.
* `AlgebraicGeometry.FiniteFreeAlgebra.baseChange_id`,
  `AlgebraicGeometry.FiniteFreeAlgebra.baseChange_comp`: functoriality of base change.

## Implementation notes

An isomorphism is represented by an element of `GL d`. Its matrix sends the `i`th basis vector
to the linear combination whose coefficient at `k` is `matrix k i`; the two displayed conditions
say precisely that it preserves the unit and the multiplication.

## References

* [Stacks Project, Tag 05YN](https://stacks.math.columbia.edu/tag/05YN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

noncomputable section

/-- An isomorphism of free algebra structures, expressed in the standard bases. The matrix
sends the `i`th basis vector to `∑ k, matrix k i · e_k`. -/
structure StructureIso {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (A B : FiniteFreeAlgebra R d) where
  /-- The invertible matrix of the underlying linear isomorphism. -/
  matrix : Matrix.GeneralLinearGroup (Fin d) R
  /-- The first basis vector, which is the unit, is fixed. -/
  map_unit : ∀ k, matrix k 0 = if k = 0 then 1 else 0
  /-- The matrix respects multiplication, written in structure constants. -/
  map_mul : ∀ i j k,
    ∑ l, A.coeff i j l * matrix k l =
      ∑ p, ∑ q, matrix p i * matrix q j * B.coeff p q k

/-- The functor in groupoids of free rank-`d` algebras, together with the concrete
identifications that specify its groupoids and its functorial base-change maps. -/
structure Presheaf (B : BigFppfSite.{u}) (d : ℕ) [NeZero d] where
  /-- The presheaf in groupoids. -/
  functor : B.Schemesᵒᵖ ⥤ Grpd.{u, u}
  /-- Objects over `T` are free algebra structures over the global sections of `T`. -/
  objectEquiv (T : B.Schemesᵒᵖ) :
    (functor.obj T : Type u) ≃ FiniteFreeAlgebra Γ(T.unop.1, ⊤) d
  /-- Arrows are precisely algebra isomorphisms in the chosen standard bases. -/
  arrowEquiv (T : B.Schemesᵒᵖ) (x y : functor.obj T) :
    (x ⟶ y) ≃ StructureIso (objectEquiv T x) (objectEquiv T y)
  /-- Identity arrows have the identity matrix. -/
  arrowEquiv_id (T : B.Schemesᵒᵖ) (x : functor.obj T) :
    (arrowEquiv T x x (𝟙 x)).matrix = 1
  /-- Composition of algebra isomorphisms is multiplication of their matrices. -/
  arrowEquiv_comp (T : B.Schemesᵒᵖ) {x y z : functor.obj T} (f : x ⟶ y) (g : y ⟶ z) :
    (arrowEquiv T x z (f ≫ g)).matrix =
      (arrowEquiv T y z g).matrix * (arrowEquiv T x y f).matrix
  /-- Pullback extends the structure constants along the induced map on global sections. -/
  map_object {T U : B.Schemesᵒᵖ} (f : T ⟶ U)
      (A : FiniteFreeAlgebra Γ(T.unop.1, ⊤) d) :
    objectEquiv U ((functor.map f).obj ((objectEquiv T).symm A)) =
      A.map (B.inclusion.map f.unop).appTop.hom
  /-- Pullback extends the entries of an algebra-isomorphism matrix along the same map on
  global sections. -/
  map_arrow {T U : B.Schemesᵒᵖ} (f : T ⟶ U) {x y : functor.obj T} (e : x ⟶ y) :
    (arrowEquiv U _ _ ((functor.map f).map e)).matrix =
      Matrix.GeneralLinearGroup.map (B.inclusion.map f.unop).appTop.hom
        (arrowEquiv T x y e).matrix

/-- The identity isomorphism of a free algebra structure. -/
def StructureIso.refl {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (A : FiniteFreeAlgebra R d) : StructureIso A A where
  matrix := 1
  map_unit := by simp [Matrix.one_apply]
  map_mul := by simp [Matrix.one_apply]

/-- Extension of scalars of an isomorphism of free algebra structures. -/
def StructureIso.map {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S)
    {A B : FiniteFreeAlgebra R d} (e : StructureIso A B) :
    StructureIso (A.map f) (B.map f) where
  matrix := Matrix.GeneralLinearGroup.map f e.matrix
  map_unit := by simp [Matrix.GeneralLinearGroup.map_apply, e.map_unit]
  map_mul := by
    intro i j k
    change (∑ l, f (A.coeff i j l) * f (e.matrix k l)) =
      ∑ p, ∑ q, f (e.matrix p i) * f (e.matrix q j) * f (B.coeff p q k)
    calc
      (∑ l, f (A.coeff i j l) * f (e.matrix k l)) =
          f (∑ l, A.coeff i j l * e.matrix k l) := by simp
      _ = f (∑ p, ∑ q, e.matrix p i * e.matrix q j * B.coeff p q k) :=
        congrArg f (e.map_mul i j k)
      _ = ∑ p, ∑ q, f (e.matrix p i) * f (e.matrix q j) * f (B.coeff p q k) := by simp

/-- A fourfold sum may be reordered so that its last two indices come first. -/
lemma sum_four_swap {R : Type*} [AddCommMonoid R] {d : ℕ}
    (F : Fin d → Fin d → Fin d → Fin d → R) :
    (∑ a, ∑ b, ∑ p, ∑ q, F a b p q) = ∑ p, ∑ q, ∑ a, ∑ b, F a b p q := by
  calc
    _ = ∑ a, ∑ p, ∑ b, ∑ q, F a b p q := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ p, ∑ a, ∑ b, ∑ q, F a b p q := Finset.sum_comm
    _ = ∑ p, ∑ a, ∑ q, ∑ b, F a b p q :=
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ a, ∑ b, F a b p q := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- The effect of a change of basis on a bilinear expression in structure constants. -/
lemma sum_bilinear_change {R : Type*} [CommRing R] {d : ℕ}
    (g h : Matrix (Fin d) (Fin d) R) (B : Fin d → Fin d → Fin d → R) (i j l : Fin d) :
    (∑ a, ∑ b, h a i * h b j * (∑ p, ∑ q, g p a * g q b * B p q l)) =
      ∑ p, ∑ q, (∑ a, g p a * h a i) * (∑ b, g q b * h b j) * B p q l := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_swap (fun a b p q => h a i * h b j * (g p a * g q b * B p q l))]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Finset.sum_comm]
  simp [mul_comm, mul_left_comm]

/-- A fourfold sum may be reordered so that its first index comes last. -/
lemma sum_four_rotate {R : Type*} [AddCommMonoid R] {d : ℕ}
    (F : Fin d → Fin d → Fin d → Fin d → R) :
    (∑ l, ∑ a, ∑ b, ∑ t, F l a b t) = ∑ a, ∑ b, ∑ t, ∑ l, F l a b t := by
  calc
    _ = ∑ a, ∑ l, ∑ b, ∑ t, F l a b t := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ l, ∑ t, F l a b t := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ t, ∑ l, F l a b t :=
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- Composition of isomorphisms of free algebra structures. -/
def StructureIso.comp {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    {A B C : FiniteFreeAlgebra R d} (e : StructureIso A B) (f : StructureIso B C) :
    StructureIso A C where
  matrix := f.matrix * e.matrix
  map_unit := by simp [Matrix.mul_apply, e.map_unit, f.map_unit]
  map_mul := by
    intro i j k
    simp only [Units.val_mul, Matrix.mul_apply]
    calc
      (∑ l, A.coeff i j l * ∑ t, f.matrix k t * e.matrix t l) =
          ∑ t, f.matrix k t * (∑ l, A.coeff i j l * e.matrix t l) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            simp [mul_comm, mul_assoc]
      _ = ∑ t, f.matrix k t *
            (∑ p, ∑ q, e.matrix p i * e.matrix q j * B.coeff p q t) := by
              simp_rw [e.map_mul]
      _ = ∑ p, ∑ q, (∑ a, f.matrix p a * e.matrix a i) *
            (∑ b, f.matrix q b * e.matrix b j) * C.coeff p q k := by
              calc
                _ = ∑ a, ∑ b, e.matrix a i * e.matrix b j *
                    (∑ t, B.coeff a b t * f.matrix k t) := by
                      simp only [Finset.mul_sum]
                      rw [Finset.sum_comm]
                      congr 1
                      ext a
                      rw [Finset.sum_comm]
                      congr 1
                      ext b
                      congr 1
                      ext t
                      ring
                _ = ∑ a, ∑ b, e.matrix a i * e.matrix b j *
                    (∑ p, ∑ q, f.matrix p a * f.matrix q b * C.coeff p q k) := by
                      simp_rw [f.map_mul]
                _ = _ := sum_bilinear_change f.matrix e.matrix C.coeff i j k

/-- The inverse of an isomorphism of free algebra structures. -/
def StructureIso.inv {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    {A B : FiniteFreeAlgebra R d} (e : StructureIso A B) : StructureIso B A where
  matrix := e.matrix⁻¹
  map_unit := by
    intro k
    calc
      e.matrix⁻¹ k 0 = ∑ l, e.matrix⁻¹ k l * e.matrix l 0 := by simp [e.map_unit]
      _ = (1 : Matrix (Fin d) (Fin d) R) k 0 := by
        rw [← Matrix.mul_apply]
        simp
      _ = if k = 0 then 1 else 0 := by simp [Matrix.one_apply]
  map_mul := by
    intro i j k
    let g : Matrix (Fin d) (Fin d) R := e.matrix
    let h : Matrix (Fin d) (Fin d) R := (e.matrix⁻¹ : Matrix.GeneralLinearGroup (Fin d) R)
    have hgh (p t : Fin d) : (∑ a, g p a * h a t) = if p = t then 1 else 0 := by
      change (g * h) p t = _
      simp [g, h, Matrix.one_apply]
    have hhg (p t : Fin d) : (∑ a, h p a * g a t) = if p = t then 1 else 0 := by
      change (h * g) p t = _
      simp [g, h, Matrix.one_apply]
    have key (l : Fin d) :
        (∑ a, ∑ b, h a i * h b j * (∑ p, ∑ q, g p a * g q b * B.coeff p q l)) =
          B.coeff i j l := by
      rw [sum_bilinear_change]
      simp [hgh]
    have hmul (a b l : Fin d) :
        (∑ p, ∑ q, g p a * g q b * B.coeff p q l) = ∑ t, A.coeff a b t * g l t :=
      (e.map_mul a b l).symm
    change (∑ l, B.coeff i j l * h k l) = ∑ a, ∑ b, h a i * h b j * A.coeff a b k
    calc
      _ = ∑ l, (∑ a, ∑ b, h a i * h b j *
          (∑ p, ∑ q, g p a * g q b * B.coeff p q l)) * h k l := by
            simp_rw [key]
      _ = ∑ l, (∑ a, ∑ b, h a i * h b j *
          (∑ t, A.coeff a b t * g l t)) * h k l := by
            simp_rw [hmul]
      _ = ∑ a, ∑ b, h a i * h b j * (∑ t, A.coeff a b t * (∑ l, h k l * g l t)) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [sum_four_rotate (fun l a b t =>
              (h a i * h b j * (A.coeff a b t * g l t)) * h k l)]
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = _ := by simp [hhg]

/-- An isomorphism of free algebra structures is determined by its matrix. -/
theorem StructureIso.ext {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    {A B : FiniteFreeAlgebra R d} {e f : StructureIso A B} (h : e.matrix = f.matrix) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- Free rank-`d` algebra structures over a fixed ring and their isomorphisms form a
groupoid. -/
local instance groupoid {R : Type*} [CommRing R] {d : ℕ} [NeZero d] :
    Groupoid (FiniteFreeAlgebra R d) where
  Hom := StructureIso
  id A := StructureIso.refl A
  comp e f := e.comp f
  inv e := e.inv
  id_comp e := StructureIso.ext (by simp [StructureIso.comp, StructureIso.refl])
  comp_id e := StructureIso.ext (by simp [StructureIso.comp, StructureIso.refl])
  assoc e f g := StructureIso.ext (by simp [StructureIso.comp, mul_assoc])
  inv_comp e := StructureIso.ext (by simp [StructureIso.comp, StructureIso.inv]; rfl)
  comp_inv e := StructureIso.ext (by simp [StructureIso.comp, StructureIso.inv]; rfl)

/-- Extension of scalars as a functor between the groupoids of free algebra structures. -/
def baseChange {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S) :
    Grpd.of (FiniteFreeAlgebra R d) ⟶ Grpd.of (FiniteFreeAlgebra S d) where
  obj A := A.map f
  map e := e.map f
  map_id A := StructureIso.ext (by
    change Matrix.GeneralLinearGroup.map f 1 = 1
    simp)
  map_comp e g := StructureIso.ext (by
    change Matrix.GeneralLinearGroup.map f (g.matrix * e.matrix) =
      Matrix.GeneralLinearGroup.map f g.matrix * Matrix.GeneralLinearGroup.map f e.matrix
    simp)

/-- Base change along the identity is the identity. -/
theorem baseChange_id {R : Type u} [CommRing R] {d : ℕ} [NeZero d] :
    baseChange (d := d) (RingHom.id R) = 𝟙 (Grpd.of (FiniteFreeAlgebra R d)) := by
  exact Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq (StructureIso.ext rfl)

/-- Base change along a composite is the composite of the base changes. -/
theorem baseChange_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {d : ℕ} [NeZero d] (f : R →+* S) (g : S →+* T) :
    baseChange (d := d) (g.comp f) = baseChange f ≫ baseChange g := by
  exact Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq (StructureIso.ext rfl)

/-- The presheaf in groupoids `FA_d` of free rank-`d` commutative algebra structures and their
isomorphisms. -/
@[stacks 05YN]
noncomputable def presheaf (B : BigFppfSite.{u}) (d : ℕ) [NeZero d] : Presheaf B d := by
  let F : B.Schemesᵒᵖ ⥤ Grpd.{u, u} := {
    obj T := Grpd.of (FiniteFreeAlgebra Γ(T.unop.1, ⊤) d)
    map f := baseChange (B.inclusion.map f.unop).appTop.hom
    map_id T := by simpa using baseChange_id (R := Γ(T.unop.1, ⊤)) (d := d)
    map_comp f g :=
      baseChange_comp (B.inclusion.map f.unop).appTop.hom (B.inclusion.map g.unop).appTop.hom }
  exact {
    functor := F
    objectEquiv := fun T => Equiv.refl _
    arrowEquiv := fun T x y => Equiv.refl _
    arrowEquiv_id := by intros; rfl
    arrowEquiv_comp := by intros; rfl
    map_object := by intros; rfl
    map_arrow := by intros; rfl }

end

end AlgebraicGeometry.FiniteFreeAlgebra

end

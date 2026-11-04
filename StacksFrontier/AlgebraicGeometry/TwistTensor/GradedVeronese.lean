module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `d`-th Veronese regrading of a sheaf of graded algebras

Let `R` be a sheaf of rings on a site and `A` a sheaf of `ℤ`-graded `R`-algebras. For an integer
`d` the **`d`-th Veronese regrading** `A^{(d)}` is the sheaf of `ℤ`-graded algebras whose
degree-`n` piece is `A_{nd}`, with the multiplication and the unit of `A` read through the
identifications `nd + md = (n + m)d` and `0 = 0 · d` of degrees.

It is the source of the comparison `θ` of [Stacks, Tag 01O1], an isomorphism

`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`,

since `⨁_{n ∈ ℤ} 𝒪(nd)` is the `d`-th Veronese regrading of the sheaf of graded algebras of the
twists of [Stacks, Tag 01NR]. It is also the source of the map `ψ` of a quadruple of Section
01NS: `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting` is a homomorphism out of
`f^*𝒜^{(d)}` written degreewise.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedVeronese.veronese`: **the `d`-th Veronese regrading `A^{(d)}`.**
* `Stacks.AlgebraicGeometry.GradedVeronese.veroneseHom`: a homomorphism of sheaves of graded
  algebras regraded.
* `Stacks.AlgebraicGeometry.GradedVeronese.veroneseIso`: an isomorphism regraded.
* `Stacks.AlgebraicGeometry.GradedVeronese.isoOfPiecesOfHoms`: **a degreewise family of
  isomorphisms, both of whose directions preserve products of homogeneous local sections, is an
  isomorphism of sheaves of graded algebras.**

## Main results

* `Stacks.AlgebraicGeometry.GradedVeronese.veronese_piece`: the degree-`n` piece of `A^{(d)}` is
  `A_{nd}`, by `rfl`.
* `Stacks.AlgebraicGeometry.GradedVeronese.veronese_mul_app`: the product of two homogeneous local
  sections of `A^{(d)}` is their product in `A`, transported along `nd + md = (n + m)d`.
* `Stacks.AlgebraicGeometry.GradedVeronese.veronese_one_eval`: the unit of `A^{(d)}` is the unit of
  `A`, transported along `0 = 0 · d`.
* `Stacks.AlgebraicGeometry.GradedVeronese.veronese_mulSheaf`: the same for the multiplication
  read as a morphism out of the tensor product sheaf.
* `Stacks.AlgebraicGeometry.GradedVeronese.isIso_veronese_mulSheaf`: **the multiplications of the
  regrading are isomorphisms as soon as the multiplications of `A` in the `d`-divisible degrees
  are.**

## Implementation notes

The degree map is `fun n => n * d` rather than `fun n => d * n`, matching
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting`, whose components are indexed by
`A.piece (i * d)`.

No `stacks` attribute is attached: the Veronese regrading is a construction the source performs
silently inside Situation 01NS, not an assertion of a tag.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf

universe t a v u w

namespace Stacks.AlgebraicGeometry.GradedVeronese

section Congr

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (A : SheafOfModules.GradedAlgebra.{t, a} R)

/-- Replacing the degree of the first argument of the multiplication by an equal one, the argument
being transported along the same equality, does not change the product up to `HEq`. -/
theorem mul_app_heq_left {p p' q : ℤ} (hp : p = p') (U : Cᵒᵖ)
    {x : (A.piece p).val.obj U} {x' : (A.piece p').val.obj U} (hx : HEq x x')
    (y : (A.piece q).val.obj U) :
    HEq ((A.mul p q).app U x y) ((A.mul p' q).app U x' y) := by
  subst hp; rw [eq_of_heq hx]

/-- Replacing the degree of the second argument of the multiplication by an equal one, the argument
being transported along the same equality, does not change the product up to `HEq`. -/
theorem mul_app_heq_right {p q q' : ℤ} (hq : q = q') (U : Cᵒᵖ)
    (x : (A.piece p).val.obj U)
    {y : (A.piece q).val.obj U} {y' : (A.piece q').val.obj U} (hy : HEq y y') :
    HEq ((A.mul p q).app U x y) ((A.mul p q').app U x y') := by
  subst hq; rw [eq_of_heq hy]

end Congr

section Veronese

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (A : SheafOfModules.GradedAlgebra.{t, a} R) (d : ℤ)

/-- The transport of degrees that turns the multiplication of `A` in the degrees `(nd, md)` into
the multiplication of the Veronese regrading in the degrees `(n, m)`. -/
def mulShift (n m : ℤ) : A.piece (n * d + m * d) ⟶ A.piece ((n + m) * d) :=
  eqToHom (congrArg A.piece (by ring : n * d + m * d = (n + m) * d))

/-- The transport of degrees that turns the unit of `A` into the unit of the Veronese
regrading. -/
def oneShift : A.piece 0 ⟶ A.piece (0 * d) :=
  eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))

/-- The multiplication of the `d`-th Veronese regrading: the multiplication of `A` in the degrees
`(nd, md)`, transported along `nd + md = (n + m)d`. -/
def veroneseMul (n m : ℤ) :
    SheafOfModules.BilinearMap (A.piece (n * d)) (A.piece (m * d)) (A.piece ((n + m) * d)) :=
  Stacks.BilinearMap.postcomp (A.mul (n * d) (m * d)) (mulShift A d n m).val

/-- The multiplication of the `d`-th Veronese regrading on local sections is the multiplication of
`A`, followed by `mulShift`. -/
theorem veroneseMul_app (n m : ℤ) (U : Cᵒᵖ)
    (x : (A.piece (n * d)).val.obj U) (y : (A.piece (m * d)).val.obj U) :
    (veroneseMul A d n m).app U x y =
      (mulShift A d n m).val.app U ((A.mul (n * d) (m * d)).app U x y) :=
  rfl

/-- The product of two homogeneous local sections of the Veronese regrading is their product in
`A`, up to the transport of degrees, hence equal to it up to `HEq`. -/
theorem veroneseMul_app_heq (n m : ℤ) (U : Cᵒᵖ)
    (x : (A.piece (n * d)).val.obj U) (y : (A.piece (m * d)).val.obj U) :
    HEq ((veroneseMul A d n m).app U x y) ((A.mul (n * d) (m * d)).app U x y) :=
  Stacks.TensorSheafWorld.heq_eqToHom_val_app A.piece
    (by ring : n * d + m * d = (n + m) * d) U _

/-- **The `d`-th Veronese regrading `A^{(d)}` of a sheaf of graded algebras**: the sheaf of
`ℤ`-graded algebras whose degree-`n` piece is `A_{nd}`, with the multiplication and the unit of `A`
read through the identifications `nd + md = (n + m)d` and `0 = 0 · d`. -/
@[ega "II 3.1.1"]
def veronese : SheafOfModules.GradedAlgebra.{t, a} R where
  piece n := A.piece (n * d)
  mul n m := veroneseMul A d n m
  one := SheafOfModules.sectionsMap (oneShift A d) A.one
  mul_assoc n m k U x y z := by
    refine HEq.trans (veroneseMul_app_heq A d (n + m) k U _ z) ?_
    refine HEq.trans (mul_app_heq_left A (by ring : (n + m) * d = n * d + m * d) U
      (veroneseMul_app_heq A d n m U x y) z) ?_
    refine HEq.trans (A.mul_assoc (n * d) (m * d) (k * d) U x y z) ?_
    refine HEq.symm (HEq.trans (veroneseMul_app_heq A d n (m + k) U x _) ?_)
    exact mul_app_heq_right A (by ring : (m + k) * d = m * d + k * d) U x
      (veroneseMul_app_heq A d m k U y z)
  one_mul n U x := by
    refine HEq.trans (veroneseMul_app_heq A d 0 n U _ x) ?_
    refine HEq.trans (mul_app_heq_left A (by ring : 0 * d = (0 : ℤ)) U
      (Stacks.TensorSheafWorld.heq_eqToHom_val_app A.piece
        (by ring : (0 : ℤ) = 0 * d) U (A.one.eval U)) x) ?_
    exact A.one_mul (n * d) U x
  mul_one n U x := by
    refine HEq.trans (veroneseMul_app_heq A d n 0 U x _) ?_
    refine HEq.trans (mul_app_heq_right A (by ring : 0 * d = (0 : ℤ)) U x
      (Stacks.TensorSheafWorld.heq_eqToHom_val_app A.piece
        (by ring : (0 : ℤ) = 0 * d) U (A.one.eval U))) ?_
    exact A.mul_one (n * d) U x

/-- **The degree-`n` piece of the `d`-th Veronese regrading is `A_{nd}`**, on the nose. -/
theorem veronese_piece (n : ℤ) : (veronese A d).piece n = A.piece (n * d) := rfl

/-- **The product of two homogeneous local sections of `A^{(d)}` is their product in `A`**,
transported along `nd + md = (n + m)d`. -/
theorem veronese_mul_app (n m : ℤ) (U : Cᵒᵖ)
    (x : (A.piece (n * d)).val.obj U) (y : (A.piece (m * d)).val.obj U) :
    ((veronese A d).mul n m).app U x y =
      (eqToHom (congrArg A.piece (by ring : n * d + m * d = (n + m) * d))).val.app U
        ((A.mul (n * d) (m * d)).app U x y) :=
  rfl

/-- **The unit of `A^{(d)}` is the unit of `A`**, transported along `0 = 0 · d`. -/
theorem veronese_one_eval (U : Cᵒᵖ) :
    (veronese A d).one.eval U =
      (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))).val.app U (A.one.eval U) :=
  rfl

/-- The product of two homogeneous local sections of `A^{(d)}` agrees with their product in `A`
up to `HEq`. -/
theorem veronese_mul_app_heq (n m : ℤ) (U : Cᵒᵖ)
    (x : (A.piece (n * d)).val.obj U) (y : (A.piece (m * d)).val.obj U) :
    HEq (((veronese A d).mul n m).app U x y) ((A.mul (n * d) (m * d)).app U x y) :=
  veroneseMul_app_heq A d n m U x y

end Veronese

/-! ### Functoriality -/

section Functoriality

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : SheafOfModules.GradedAlgebra.{t, a} R} (d : ℤ)

/-- A homomorphism of sheaves of graded algebras commutes with the transport of a homogeneous
piece along an equality of degrees, read on local sections. -/
theorem app_val_app_eqToHom (φ : A ⟶ B) {k k' : ℤ} (h : k = k') (U : Cᵒᵖ)
    (z : (A.piece k).val.obj U) :
    (φ.app k').val.app U ((eqToHom (congrArg A.piece h)).val.app U z) =
      (eqToHom (congrArg B.piece h)).val.app U ((φ.app k).val.app U z) := by
  subst h; rfl

/-- **A homomorphism of sheaves of graded algebras regraded**: the components of `φ` in the degrees
`nd`, as a homomorphism `A^{(d)} ⟶ B^{(d)}`. -/
def veroneseHom (φ : A ⟶ B) : veronese A d ⟶ veronese B d where
  app n := φ.app (n * d)
  map_mul n m U x y :=
    (app_val_app_eqToHom φ (by ring : n * d + m * d = (n + m) * d) U _).trans
      (congrArg ((eqToHom (congrArg B.piece
        (by ring : n * d + m * d = (n + m) * d))).val.app U)
        (φ.map_mul (n * d) (m * d) U x y))

@[simp] theorem veroneseHom_app (φ : A ⟶ B) (n : ℤ) :
    (veroneseHom d φ).app n = φ.app (n * d) := rfl

/-- **An isomorphism of sheaves of graded algebras regraded.** -/
def veroneseIso (e : A ≅ B) : veronese A d ≅ veronese B d where
  hom := veroneseHom d e.hom
  inv := veroneseHom d e.inv
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    congrArg (fun φ : A ⟶ A => φ.app (n * d)) e.hom_inv_id
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    congrArg (fun φ : B ⟶ B => φ.app (n * d)) e.inv_hom_id

@[simp] theorem veroneseIso_hom_app (e : A ≅ B) (n : ℤ) :
    (veroneseIso d e).hom.app n = e.hom.app (n * d) := rfl

@[simp] theorem veroneseIso_inv_app (e : A ≅ B) (n : ℤ) :
    (veroneseIso d e).inv.app n = e.inv.app (n * d) := rfl

end Functoriality

/-! ### Isomorphisms from a degreewise family -/

section IsoOfPieces

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : SheafOfModules.GradedAlgebra.{t, a} R}

/-- Two homomorphisms whose components are inverse to each other compose to the identity. -/
theorem comp_eq_id_of_app (φ : A ⟶ B) (ψ : B ⟶ A)
    (h : ∀ n : ℤ, φ.app n ≫ ψ.app n = CategoryStruct.id _) : φ ≫ ψ = CategoryStruct.id A :=
  SheafOfModules.GradedAlgebra.Hom.ext fun n => h n

/-- **A degreewise family of isomorphisms, both of whose directions preserve products of
homogeneous local sections, is an isomorphism of sheaves of graded algebras.** -/
def isoOfPiecesOfHoms (e : ∀ n : ℤ, A.piece n ≅ B.piece n)
    (hhom : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      ((e (i + j)).hom.val.app U) ((A.mul i j).app U x y) =
        (B.mul i j).app U (((e i).hom.val.app U) x) (((e j).hom.val.app U) y))
    (hinv : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (B.piece i).val.obj U) (y : (B.piece j).val.obj U),
      ((e (i + j)).inv.val.app U) ((B.mul i j).app U x y) =
        (A.mul i j).app U (((e i).inv.val.app U) x) (((e j).inv.val.app U) y)) :
    A ≅ B where
  hom := { app := fun n => (e n).hom, map_mul := hhom }
  inv := { app := fun n => (e n).inv, map_mul := hinv }
  hom_inv_id := comp_eq_id_of_app _ _ fun n => (e n).hom_inv_id
  inv_hom_id := comp_eq_id_of_app _ _ fun n => (e n).inv_hom_id

@[simp] theorem isoOfPiecesOfHoms_hom_app (e : ∀ n : ℤ, A.piece n ≅ B.piece n) (hhom) (hinv)
    (n : ℤ) : (isoOfPiecesOfHoms e hhom hinv).hom.app n = (e n).hom := rfl

@[simp] theorem isoOfPiecesOfHoms_inv_app (e : ∀ n : ℤ, A.piece n ≅ B.piece n) (hhom) (hinv)
    (n : ℤ) : (isoOfPiecesOfHoms e hhom hinv).inv.app n = (e n).inv := rfl

end IsoOfPieces

/-- Transport along an equality of objects is an isomorphism, with the equality passed explicitly
and in a bare category. -/
theorem isIso_eqToHom {D : Type*} [Category D] {X Y : D} (h : X = Y) : IsIso (eqToHom h) := by
  subst h; exact inferInstanceAs (IsIso (CategoryStruct.id X))

/-- A composite of two isomorphisms is an isomorphism, with both hypotheses passed explicitly and
in a bare category. -/
theorem isIso_comp_of {D : Type*} [Category D] {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso f) (hg : IsIso g) : IsIso (f ≫ g) := by
  have := hf; have := hg; infer_instance

/-! ### The multiplication of the regrading, as a morphism out of the tensor product sheaf -/

section MulSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (A : SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp)) (d : ℤ)

/-- **The multiplication of the `d`-th Veronese regrading, as a morphism out of the tensor product
sheaf, is the multiplication of `A` in the degrees `(nd, md)` followed by the transport of degrees
along `nd + md = (n + m)d`.** -/
theorem veronese_mulSheaf (n m : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (veronese A d) n m =
      SheafOfModules.GradedAlgebra.mulSheaf A (n * d) (m * d) ≫
        eqToHom (congrArg A.piece (by ring : n * d + m * d = (n + m) * d)) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := A.piece (n * d)) (G := A.piece (m * d))
    (Q := A.piece ((n + m) * d)) fun U x y ↦ ?_
  refine Eq.trans (SheafOfModules.GradedAlgebra.mulSheaf_unit (veronese A d) n m U x y) ?_
  refine Eq.trans (veronese_mul_app A d n m U x y) ?_
  exact congrArg _
    (SheafOfModules.GradedAlgebra.mulSheaf_unit A (n * d) (m * d) U x y).symm

/-- **The multiplications of the `d`-th Veronese regrading are isomorphisms as soon as the
multiplications of `A` in the `d`-divisible degrees are.** -/
theorem isIso_veronese_mulSheaf (n m : ℤ)
    (h : IsIso (SheafOfModules.GradedAlgebra.mulSheaf A (n * d) (m * d))) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (veronese A d) n m) := by
  rw [veronese_mulSheaf A d n m]
  exact isIso_comp_of _ _ h (isIso_eqToHom _)

end MulSheaf

end Stacks.AlgebraicGeometry.GradedVeronese

end

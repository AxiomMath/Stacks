module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraFunctoriality
public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentRecognition
public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedVeronese
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerAssoc

/-!
# Recognising a Laurent algebra: multiplicativity, and the isomorphism of graded algebras

`Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso` compares the degree-`n` piece of a
sheaf of `ℤ`-graded algebras `ℛ` with invertible multiplications and invertible degree-zero piece
with the `n`-th integral tensor power of an invertible module `ℒ` identified with `ℛ_1` by
`β : ℛ_1 ≅ ℒ`, in every integer degree. This file proves that the comparison is multiplicative
in every integer bidegree and assembles the degreewise family into an isomorphism

`ℛ ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of graded algebras.

## Main results

* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso_mul`: multiplicativity of the
  comparison in an arbitrary integer bidegree.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.mulCompat_one`: multiplicativity in the
  bidegree `(n, 1)`.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso_one_comp_oneIsoL`: the comparison
  in degree one is `β`, read through the identification `ℒ^{⊗ 1} = ℒ` of [Stacks, Tag 01CU].
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso_mulSheaf` and
  `pieceIso_inv_mulSheaf`: the comparison and its inverse are multiplicative against
  `SheafOfModules.GradedAlgebra.mulSheaf` on both sides.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso`: the isomorphism
  `ℛ ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` of sheaves of `ℤ`-graded algebras, with `gradedIso_hom_app` and
  `gradedIso_inv_app` its degreewise components.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.Monoidal

/-- The forward map of an isomorphism is a monomorphism. -/
theorem mono_iso_hom {D : Type*} [Category D] {X Y : D} (e : X ≅ Y) : Mono e.hom :=
  inferInstance

/-- `Stacks.Monoidal.square_step_left` with its `Mono` instance as an explicit hypothesis. -/
theorem square_step_left_of_mono {D : Type*} [Category D] [MonoidalCategory D]
    {A B Cc AB BC ABC A' B' C' AB' BC' ABC' Z' : D}
    {a : A ⊗ B ⟶ AB} {b : B ⊗ Cc ≅ BC} {p : AB ⊗ Cc ⟶ ABC} {r : A ⊗ BC ⟶ ABC}
    {a' : A' ⊗ B' ⟶ AB'} {b' : B' ⊗ C' ⟶ BC'} {p' : AB' ⊗ C' ⟶ ABC'}
    {r' : A' ⊗ BC' ⟶ ABC'}
    {f : A ⟶ A'} {g : B ⟶ B'} {h : Cc ≅ C'} {fg : AB ⟶ AB'} {gh : BC ⟶ BC'}
    {fgh : ABC ⟶ ABC'} (hmono : Mono p') (e : Cc ⊗ Z' ≅ 𝟙_ D)
    (hL : a ▷ Cc ≫ p = (α_ A B Cc).hom ≫ A ◁ b.hom ≫ r)
    (hR : a' ▷ C' ≫ p' = (α_ A' B' C').hom ≫ A' ◁ b' ≫ r')
    (h2 : p ≫ fgh = (fg ⊗ₘ h.hom) ≫ p')
    (h3 : b.hom ≫ gh = (g ⊗ₘ h.hom) ≫ b')
    (hD : r ≫ fgh = (f ⊗ₘ gh) ≫ r') :
    a ≫ fg = (f ⊗ₘ g) ≫ a' :=
  let := hmono
  square_step_left e hL hR h2 h3 hD

end Stacks.Monoidal

namespace Stacks.AlgebraicGeometry.GradedLaurentRecognition

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### Identities in a monoidal category -/

/-- Cancelling a left inverse out of a whiskered composite: if `z ≫ one = 𝟙` then whiskering `z`
into `B` and following the unit law `one ▷ B ≫ m = lam` recovers `m`. -/
private theorem whisker_cancel_free {D : Type*} [Category D] [MonoidalCategory D]
    {A B P : D} (z : A ⟶ 𝟙_ D) (one : 𝟙_ D ⟶ A) (hzo : z ≫ one = CategoryStruct.id A)
    (m : A ⊗ B ⟶ P) (lam : 𝟙_ D ⊗ B ⟶ P) (hu : one ▷ B ≫ m = lam) :
    (z ▷ B) ≫ lam = m := by
  rw [← hu, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hzo,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- Appending an endomorphism known to be the identity changes nothing. -/
private theorem comp_eq_id_right {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) (g : Y ⟶ Y)
    (hg : g = CategoryStruct.id Y) : f ≫ g = f := by
  rw [hg, Category.comp_id]

/-- Dropping an endomorphism known to be the identity out of the middle of a composite. -/
private theorem id_mid_free {D : Type*} [Category D] {X Y Z : D} (f : X ⟶ Y) (i : Y ⟶ Y)
    (g : Y ⟶ Z) (hi : i = CategoryStruct.id Y) : (f ≫ i) ≫ g = f ≫ g := by
  rw [hi, Category.comp_id]

/-- If whiskering `z` into `B` and following the left unitor is `m`, then tensoring `z` with `bb`
and following the left unitor is `m` followed by `bb`. -/
private theorem degree_one_free {D : Type*} [Category D] [MonoidalCategory D]
    {A B Q : D} (z : A ⟶ 𝟙_ D) (bb : B ⟶ Q) (m : A ⊗ B ⟶ B)
    (hm : (z ▷ B) ≫ (λ_ B).hom = m) :
    (z ⊗ₘ bb) ≫ (λ_ Q).hom = m ≫ bb := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    MonoidalCategory.leftUnitor_naturality, ← Category.assoc, hm]

/-- Moving a transport between the two sides of a square: given `tr ≫ psi = phi ≫ rx.hom`, the
square `m ≫ phi = t ≫ u` holds exactly when `(m ≫ tr) ≫ psi = t ≫ u ≫ rx.hom` does. -/
private theorem corner_free {D : Type*} [Category D] {A B Bt F G H : D}
    (m : A ⟶ B) (tr : B ⟶ Bt) (phi : B ⟶ F) (psi : Bt ⟶ G) (rx : F ≅ G)
    (t : A ⟶ H) (u : H ⟶ F) (hphi : tr ≫ psi = phi ≫ rx.hom) :
    (m ≫ phi = t ≫ u) ↔ ((m ≫ tr) ≫ psi = t ≫ u ≫ rx.hom) := by
  rw [Category.assoc, hphi, ← Category.assoc m phi rx.hom, ← Category.assoc t u rx.hom]
  exact (Iso.cancel_iso_hom_right _ _ rx).symm

/-- A commuting square of isomorphisms read backwards. -/
private theorem inv_square_free {D : Type*} [Category D] {A B A' B' : D}
    (f : A ⟶ B) (g : A' ⟶ B') (t : A ⟶ A') (ti : A' ⟶ A) (c : B ⟶ B') (ci : B' ⟶ B)
    (ht : ti ≫ t = CategoryStruct.id A') (hc : c ≫ ci = CategoryStruct.id B)
    (h : f ≫ c = t ≫ g) : g ≫ ci = ti ≫ f := by
  rw [← Category.id_comp (g ≫ ci), ← ht, Category.assoc, ← Category.assoc t g ci, ← h,
    Category.assoc, hc, Category.comp_id]

/-! ### Multiplicativity -/

variable {T : Scheme.{u}}
  (R : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace))
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (β : R.piece 1 ≅ L)
  (hmul : ∀ i j : ℤ, IsIso (SheafOfModules.GradedAlgebra.mulSheaf R i j))
  (hinv : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
    (R.piece 0))

/-- **The associativity constraint of `ℛ` with its middle multiplication spelled as an
isomorphism.** -/
theorem mulSheaf_assoc_mulIsoR (n m j : ℤ) :
    MonoidalCategoryStruct.whiskerRight
          (C := SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
          (SheafOfModules.GradedAlgebra.mulSheaf R n m) (R.piece j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf R (n + m) j =
      (α_ (R.piece n) (R.piece m) (R.piece j)).hom ≫
        R.piece n ◁ (mulIsoR R hmul m j).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf R n (m + j) ≫
            eqToHom (congrArg R.piece (add_assoc n m j).symm) :=
  Stacks.TensorSheafWorld.mulSheaf_assoc T.sheaf (isSheafStruct T) R n m j

/-- **The comparison commutes with the transport along an equality of degrees**: on the left the
transport is `CategoryTheory.eqToHom`, on the right the reindexing of tensor powers of [Stacks,
Tag 01CU]. -/
theorem pieceIso_reindex {p q : ℤ} (h : p = q) :
    eqToHom (congrArg R.piece h) ≫ (pieceIso R L β hmul hinv q).hom =
      (pieceIso R L β hmul hinv p).hom ≫ (reindexIso L h).hom := by
  subst h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The left unit law of `ℛ` in degree one: the algebra unit whiskered into `ℛ_1`, followed by
the multiplication in the bidegree `(0, 1)`, is the left unitor. -/
theorem oneHom_whiskerRight_mulSheaf_one :
    SheafOfModules.GradedAlgebra.oneHom R ▷ R.piece 1 ≫
        SheafOfModules.GradedAlgebra.mulSheaf R 0 1 =
      (λ_ (R.piece 1)).hom :=
  (SheafOfModules.GradedAlgebra.mulSheaf_one_mul R (isSheafStruct T) 1).trans
    (comp_eq_id_right (λ_ (R.piece 1)).hom _ (eqToHom_refl _ _))

/-- **The degree-zero comparison, whiskered into `ℛ_1` and followed by the left unitor, is the
multiplication of `ℛ` in the bidegree `(0, 1)`.** -/
theorem pieceIsoZero_whiskerRight_leftUnitor :
    ((pieceIso R L β hmul hinv 0).hom ▷ R.piece 1) ≫ (λ_ (R.piece 1)).hom =
      SheafOfModules.GradedAlgebra.mulSheaf R 0 1 :=
  whisker_cancel_free _ (SheafOfModules.GradedAlgebra.oneHom R)
    (zeroCmp R L hmul hinv).hom_inv_id _ _ (oneHom_whiskerRight_mulSheaf_one R)

/-- **The comparison in degree one is `β`**, read through the identification `ℒ^{⊗ 1} = ℒ` of
[Stacks, Tag 01CU]. -/
theorem pieceIso_one_comp_oneIsoL :
    (pieceIso R L β hmul hinv 1).hom ≫ (oneIsoL L).hom = β.hom := by
  refine (Iso.cancel_iso_hom_left (mulIsoR R hmul 0 1) _ _).mp ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (oneIsoL L).hom)
    (mulSheaf_comp_pieceIso_succ R L β hmul hinv 0)) ?_
  refine Eq.trans (id_mid_free ((pieceIso R L β hmul hinv 0).hom ⊗ₘ β.hom) _
    (oneIsoL L).hom rfl) ?_
  refine Eq.trans (congrArg (fun w => ((pieceIso R L β hmul hinv 0).hom ⊗ₘ β.hom) ≫ w)
    (oneIsoL_eq_leftUnitor L)) ?_
  exact degree_one_free _ β.hom _ (pieceIsoZero_whiskerRight_leftUnitor R L β hmul hinv)

/-- **The multiplicativity square of the comparison in the bidegree `(n, m)`**: the multiplication
of `ℛ`, followed by the comparison in the degree `n + m`, is the comparisons in the degrees `n`
and `m` on the two factors, followed by the coherent multiplication of the Laurent algebra of
[Stacks, Tag 01CU]. -/
abbrev MulCompat (n m : ℤ) : Prop :=
  SheafOfModules.GradedAlgebra.mulSheaf R n m ≫ (pieceIso R L β hmul hinv (n + m)).hom =
    ((pieceIso R L β hmul hinv n).hom ⊗ₘ (pieceIso R L β hmul hinv m).hom) ≫ (mulIso L n m).hom

/-- **The multiplicativity square transported along equalities of the two degrees.** -/
theorem mulCompat_of_eq {n m n' m' : ℤ} (hn : n = n') (hm : m = m')
    (H : MulCompat R L β hmul hinv n m) : MulCompat R L β hmul hinv n' m' := by
  cases hn; cases hm; exact H

/-- **Multiplicativity in the bidegree `(n, 1)`, for every integer `n`.** -/
theorem mulCompat_one (n : ℤ) : MulCompat R L β hmul hinv n 1 := by
  change SheafOfModules.GradedAlgebra.mulSheaf R n 1 ≫ (pieceIso R L β hmul hinv (n + 1)).hom =
    ((pieceIso R L β hmul hinv n).hom ⊗ₘ (pieceIso R L β hmul hinv 1).hom) ≫ (mulIso L n 1).hom
  rw [mulIso_one_right L n, ← Category.assoc, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
    pieceIso_one_comp_oneIsoL R L β hmul hinv]
  exact mulSheaf_comp_pieceIso_succ R L β hmul hinv n

/-- **The multiplicativity square in the bidegree `(n, m + 1)`, read at the `(A, BC)` corner of
the associativity diagram in the tridegree `(n, m, 1)`.** The two sides differ only by where the
transport between the two spellings `n + (m + 1)` and `n + m + 1` of the total degree sits: on the
comparison, or on the coherent multiplication of the Laurent algebra. -/
theorem mulCompat_corner_iff (n m : ℤ) :
    MulCompat R L β hmul hinv n (m + 1) ↔
      ((SheafOfModules.GradedAlgebra.mulSheaf R n (m + 1) ≫
            eqToHom (congrArg R.piece (add_assoc n m 1).symm)) ≫
          (pieceIso R L β hmul hinv (n + m + 1)).hom =
        ((pieceIso R L β hmul hinv n).hom ⊗ₘ (pieceIso R L β hmul hinv (m + 1)).hom) ≫
          (mulIso L n (m + 1)).hom ≫ (reindexIso L (add_assoc n m 1).symm).hom) :=
  corner_free _ _ _ _ (reindexIso L (add_assoc n m 1).symm) _ _
    (pieceIso_reindex R L β hmul hinv (add_assoc n m 1).symm)

/-- **The tensor inverse of `ℛ_1`**: the degree-one piece of `ℛ` against the degree `-1` piece of
the Laurent algebra. -/
def oneTensorInv : R.piece 1 ⊗ (laurent L).piece (-1) ≅
    𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :=
  MonoidalCategory.whiskerRightIso (pieceIso R L β hmul hinv 1) ((laurent L).piece (-1)) ≪≫
    mulIso L 1 (-1) ≪≫ reindexIso L (show (1 : ℤ) + -1 = 0 from by ring)

/-- Multiplicativity in the bidegree `(n, m + 1)` gives it in the bidegree `(n, m)`. -/
theorem mulCompat_of_succ (n m : ℤ) (H : MulCompat R L β hmul hinv n (m + 1)) :
    MulCompat R L β hmul hinv n m :=
  Stacks.Monoidal.square_step_left_of_mono
    (Stacks.Monoidal.mono_iso_hom (mulIso L (n + m) 1))
    (oneTensorInv R L β hmul hinv)
    (mulSheaf_assoc_mulIsoR R hmul n m 1)
    (mulIso_assoc L n m 1)
    (mulCompat_one R L β hmul hinv (n + m))
    (mulCompat_one R L β hmul hinv m)
    ((mulCompat_corner_iff R L β hmul hinv n m).mp H)

/-- **Multiplicativity in the bidegree `(n, 0)`, for every integer `n`.** -/
theorem mulCompat_zero (n : ℤ) : MulCompat R L β hmul hinv n 0 :=
  mulCompat_of_succ R L β hmul hinv n 0
    (mulCompat_of_eq R L β hmul hinv rfl (zero_add 1).symm (mulCompat_one R L β hmul hinv n))

/-- Multiplicativity in the bidegree `(n, m)` gives it in the bidegree `(n, m + 1)`. -/
theorem mulCompat_succ (n m : ℤ) (H : MulCompat R L β hmul hinv n m) :
    MulCompat R L β hmul hinv n (m + 1) :=
  (mulCompat_corner_iff R L β hmul hinv n m).mpr
    (Stacks.AlgebraicGeometry.ThetaMul.square_step
      (mulSheaf_assoc_mulIsoR R hmul n m 1)
      (mulIso_assoc L n m 1)
      H
      (mulCompat_one R L β hmul hinv (n + m))
      (mulCompat_one R L β hmul hinv m))

/-- **Multiplicativity of the comparison `ℛ_n ≅ ℒ^{⊗ n}` in an arbitrary integer bidegree.** The
multiplication of `ℛ` in the bidegree `(n, m)`, followed by the comparison in the degree `n + m`,
is the comparisons in the degrees `n` and `m` on the two factors, followed by the coherent
multiplication of the Laurent algebra of [Stacks, Tag 01CU]. Both degrees are arbitrary integers.
-/
theorem pieceIso_mul (n m : ℤ) : MulCompat R L β hmul hinv n m := by
  induction m using Int.induction_on with
  | zero => exact mulCompat_zero R L β hmul hinv n
  | succ i ih => exact mulCompat_succ R L β hmul hinv n (i : ℤ) ih
  | pred i ih =>
      exact mulCompat_of_succ R L β hmul hinv n _
        (mulCompat_of_eq R L β hmul hinv rfl (sub_add_cancel _ 1).symm ih)

/-! ### The isomorphism of sheaves of graded algebras -/

/-- **The comparison is multiplicative, against `SheafOfModules.GradedAlgebra.mulSheaf` on both
sides.** This is `pieceIso_mul` with the coherent multiplication of [Stacks, Tag 01CU] replaced by
the multiplication of the Laurent algebra read as a morphism out of the tensor product sheaf. -/
theorem pieceIso_mulSheaf (n m : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf R n m ≫ (pieceIso R L β hmul hinv (n + m)).hom =
      ((pieceIso R L β hmul hinv n).hom ⊗ₘ (pieceIso R L β hmul hinv m).hom) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent L) n m := by
  rw [mulSheaf_laurent L n m]
  exact pieceIso_mul R L β hmul hinv n m

/-- **The inverse comparison is multiplicative**, against
`SheafOfModules.GradedAlgebra.mulSheaf` on both sides. -/
theorem pieceIso_inv_mulSheaf (n m : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (laurent L) n m ≫
        (pieceIso R L β hmul hinv (n + m)).inv =
      ((pieceIso R L β hmul hinv n).inv ⊗ₘ (pieceIso R L β hmul hinv m).inv) ≫
        SheafOfModules.GradedAlgebra.mulSheaf R n m :=
  inv_square_free _ _ _ _ _ _
    (MonoidalCategory.tensorIso (pieceIso R L β hmul hinv n)
      (pieceIso R L β hmul hinv m)).inv_hom_id
    (pieceIso R L β hmul hinv (n + m)).hom_inv_id
    (pieceIso_mulSheaf R L β hmul hinv n m)

/-- **The recognition theorem.** A sheaf of `ℤ`-graded algebras `ℛ` on a scheme, all of whose
multiplications `ℛ_i ⊗ ℛ_j ⟶ ℛ_{i+j}` are isomorphisms and whose degree-zero piece is invertible,
is isomorphic **as a sheaf of graded algebras** to the Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of any
invertible module `ℒ` identified with its degree-one piece. Degreewise it is `pieceIso`. -/
def gradedIso : R ≅ laurent L :=
  Stacks.AlgebraicGeometry.GradedVeronese.isoOfPiecesOfHoms (pieceIso R L β hmul hinv)
    (fun i j => (SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff (isSheafStruct T) R (laurent L)
      (fun n => (pieceIso R L β hmul hinv n).hom) i j).mp
      (pieceIso_mulSheaf R L β hmul hinv i j))
    (fun i j => (SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff (isSheafStruct T) (laurent L) R
      (fun n => (pieceIso R L β hmul hinv n).inv) i j).mp
      (pieceIso_inv_mulSheaf R L β hmul hinv i j))

/-- The degree-`n` component of `gradedIso` is the comparison `pieceIso` in degree `n`. -/
@[simp] theorem gradedIso_hom_app (n : ℤ) :
    (gradedIso R L β hmul hinv).hom.app n = (pieceIso R L β hmul hinv n).hom := rfl

/-- The degree-`n` component of the inverse of `gradedIso` is the inverse of the comparison
`pieceIso` in degree `n`. -/
@[simp] theorem gradedIso_inv_app (n : ℤ) :
    (gradedIso R L β hmul hinv).inv.app n = (pieceIso R L β hmul hinv n).inv := rfl

end Stacks.AlgebraicGeometry.GradedLaurentRecognition

end

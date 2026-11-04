module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorTwoTrivialisations
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixUnitPointDecomposition
public import StacksFrontier.CategoryTheory.Monoidal.MonObjImagePointFunctor

/-!
# Saltman's point as a sum of tensors of matrix units

Let `T` be a scheme, let `d = n + 1`, let `B` be a sheaf of `𝒪_T`-algebras and let
`M : B ≅ Mat_d(𝒪_T)` be a trivialisation of it. The induced trivialisation
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowTrivIso` of `B^{⊗ d}` as the endomorphism
algebra of the free sheaf of rank `d ^ d` reads Saltman's projector
`Stacks.EtaleCohomology.BrauerScheme.altProjFree` as a point of `B^{⊗ d}`, and the content of
this file is the **normal form of that point**: it is the combination, with the entries of
`Matrix.altProj` as coefficients, of the tensors over `j` of the images under `M⁻¹` of the matrix
units of `Mat_d(𝒪_T)`,
$$
  \sum_{c, e} \mathrm{altProj}(c, e) \cdot \bigotimes_{j} M^{-1}(E_{c_j, e_j}).
$$
Nothing on the right-hand side mentions the tensor-power identifications, so the normal form is
what makes Saltman's point computable along a pullback: a pullback of schemes is a monoidal
functor, and a monoidal functor commutes with a finite sum, with a coefficient in
`R₀ T = End(𝒪_T)` and with a tensor of points, whereas its interaction with
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowEndAlgebraIso` and with
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowFreeIso` is a coherence this development does
not have.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowPoint`: the tensor of a finite family of
  points of a sheaf of `𝒪_S`-algebras, a point of its tensor power.

## Main results

* `CategoryTheory.MonoidalClosed.curry'_comp_internalEndCongr_hom` and
  `curry'_comp_internalEndCongr_inv`: conjugating a point of an internal endomorphism monoid by
  the isomorphism induced by an isomorphism of objects conjugates the endomorphism.
* `CategoryTheory.Mon.mapPoint_curry'`: **a lax monoidal functor carries the point of an
  endomorphism to the point of its image**, through the internal-hom comparison.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowPoint_curry'`: **the tensor of the points of a
  family of endomorphisms is the point of the tensor of that family**, through
  `natTensorPowEndAlgebraIso`.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowPoint_matIncl`: **a matrix unit of the algebra
  of size `d ^ (n+1)` is the tensor of matrix units of the algebra of size `d`**, as points.
* `Stacks.EtaleCohomology.BrauerScheme.curry'_altProjFree_comp_natTensorPowTrivIso_inv_eq_sum`:
  **the normal form of Saltman's point.**

## Implementation notes

Every step of the two inductions is taken in term mode, by `Eq.trans` and `congrArg`, and every
manipulation of unitors and of associativity is isolated in a lemma stated for an **abstract**
monoidal category. This is not decoration. At the scheme spelling the type `ModuleSheaf S`
carries `Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf`, which is not type-correct at the
`implicit` transparency `rw` builds its motive at, so a `rw` whose motive has to abstract an
object of `ModuleSheaf S` — `Category.id_comp` and `MonoidalCategory.id_tensorHom` are two —
is rejected on a goal that a `show` has already unfolded. The same consideration shapes
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorFreeSheaf`; here it
is answered by keeping the rewriting in the abstract lemmas, where every object is a variable,
and using `exact` at the scheme spelling, which unifies at default transparency.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **Whiskering with the monoidal unit on the left is conjugation by the left unitor.** Stated
with every object a variable, so that it applies at a spelling where `rw` cannot build its
motive; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerAlgebraPoints`. -/
theorem whiskerLeft_unit_eq_conj {X Y : C} (g : X ⟶ Y) :
    𝟙_ C ◁ g = (λ_ X).hom ≫ g ≫ (λ_ Y).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact leftUnitor_naturality g

/-- **A point tensored with the identity of the unit, read through the left unitor, is the
point.** -/
theorem leftUnitorInv_id_tensorHom_leftUnitor {Y : C} (g : 𝟙_ C ⟶ Y) :
    (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ g) ≫ (λ_ Y).hom = g := by
  rw [id_tensorHom, leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- `CategoryTheory.MonoidalCategory.leftUnitorInv_id_tensorHom_leftUnitor` with a further
factor on the right. -/
theorem leftUnitorInv_id_tensorHom_leftUnitor_comp {Y Z : C} (g : 𝟙_ C ⟶ Y) (t : Y ⟶ Z) :
    (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ g) ≫ ((λ_ Y).hom ≫ t) = g ≫ t :=
  calc (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ g) ≫ ((λ_ Y).hom ≫ t)
      = ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ g) ≫ (λ_ Y).hom) ≫ t := by
        simp only [Category.assoc]
    _ = g ≫ t := congrArg (fun z => z ≫ t) (leftUnitorInv_id_tensorHom_leftUnitor g)

/-- **Absorbing a factor into the left half of a tensor of two points.** -/
theorem leftUnitorInv_tensorHom_comp_tensorHom_id {A B A' Z : C} (P : 𝟙_ C ⟶ A) (q : 𝟙_ C ⟶ B)
    (x : A ⟶ A') (t : A' ⊗ B ⟶ Z) :
    (λ_ (𝟙_ C)).inv ≫ (P ⊗ₘ q) ≫ ((x ⊗ₘ 𝟙 B) ≫ t)
      = (λ_ (𝟙_ C)).inv ≫ ((P ≫ x) ⊗ₘ q) ≫ t := by
  rw [← Category.assoc (P ⊗ₘ q), tensorHom_comp_tensorHom, Category.comp_id]

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- **Conjugating a point of an internal endomorphism monoid by the isomorphism induced by an
isomorphism `e : X ≅ Y` of objects conjugates the underlying endomorphism.** -/
theorem curry'_comp_internalEndCongr_hom {X Y : C} (e : X ≅ Y) (f : X ⟶ X) :
    curry' f ≫ (internalEndCongr e).hom.hom = curry' (e.inv ≫ f ≫ e.hom) :=
  (curry'_pointMap (internalEndCongr e).hom f).symm.trans
    (congrArg curry' (pointMap_internalEndCongr e f))

/-- `CategoryTheory.MonoidalClosed.curry'_comp_internalEndCongr_hom` for the inverse
isomorphism. -/
theorem curry'_comp_internalEndCongr_inv {X Y : C} (e : X ≅ Y) (f : Y ⟶ Y) :
    curry' f ≫ (internalEndCongr e).inv.hom = curry' (e.hom ≫ f ≫ e.inv) :=
  curry'_comp_internalEndCongr_hom e.symm f

end CategoryTheory.MonoidalClosed

namespace CategoryTheory.Mon

variable {C : Type*} {D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D] (F : C ⥤ D) [F.LaxMonoidal]

/-- **A lax monoidal functor carries the point of an endomorphism to the point of its image**:
the transported point of `curry' f`, followed by the internal-hom comparison
`CategoryTheory.MonoidalClosed.ihomFunctorComparison`, is the point of `F.map f`.

This is the currying rule `CategoryTheory.MonoidalClosed.curry_comp_ihomFunctorComparison`
together with the right unitality of `F`. -/
theorem mapPoint_curry' {X : C} (f : X ⟶ X) :
    mapPoint F (C := MonoidalClosed.internalEnd X) (MonoidalClosed.curry' f) ≫
        MonoidalClosed.ihomFunctorComparison F X X
      = MonoidalClosed.curry' (F.map f) := by
  have h1 : F.map (MonoidalClosed.curry' f) ≫ MonoidalClosed.ihomFunctorComparison F X X
      = MonoidalClosed.curry (Functor.LaxMonoidal.μ F X (𝟙_ C) ≫ F.map ((ρ_ X).hom ≫ f)) :=
    MonoidalClosed.curry_comp_ihomFunctorComparison F ((ρ_ X).hom ≫ f)
  have h2 : (ρ_ (F.obj X)).hom ≫ F.map f
      = (F.obj X ◁ Functor.LaxMonoidal.ε F) ≫
        (Functor.LaxMonoidal.μ F X (𝟙_ C) ≫ F.map ((ρ_ X).hom ≫ f)) := by
    rw [Functor.LaxMonoidal.right_unitality F X, Functor.map_comp]
    simp only [Category.assoc]
  show (Functor.LaxMonoidal.ε F ≫ F.map (MonoidalClosed.curry' f)) ≫
      MonoidalClosed.ihomFunctorComparison F X X
    = MonoidalClosed.curry ((ρ_ (F.obj X)).hom ≫ F.map f)
  rw [Category.assoc, h1, h2, MonoidalClosed.curry_natural_left]

end CategoryTheory.Mon

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

variable {S : Scheme.{u}}

/-! ### The tensor of a family of points -/

/-- **The tensor of a finite family of points of a sheaf of `𝒪_S`-algebras**, a point of its
`m`-fold tensor power. `Stacks.TensorPowers.natTensorPow` adds its factors on the right, so the
recursion puts `p (Fin.last m)` on the right. -/
def natTensorPowPoint {A : AlgebraSheaf S} :
    ∀ (m : ℕ), (Fin m → (𝟙_ (ModuleSheaf S) ⟶ A.X)) →
      (𝟙_ (ModuleSheaf S) ⟶ (Stacks.TensorPowers.natTensorPow A m).X)
  | 0, _ => 𝟙 (𝟙_ (ModuleSheaf S))
  | m + 1, p => (λ_ (𝟙_ (ModuleSheaf S))).inv ≫
      (natTensorPowPoint m (Fin.init p) ⊗ₘ p (Fin.last m))

/-- The empty tensor of points is the identity of the unit. -/
@[simp]
lemma natTensorPowPoint_zero {A : AlgebraSheaf S} (p : Fin 0 → (𝟙_ (ModuleSheaf S) ⟶ A.X)) :
    natTensorPowPoint 0 p = 𝟙 (𝟙_ (ModuleSheaf S)) :=
  rfl

/-- One more factor, added on the right. -/
@[simp]
lemma natTensorPowPoint_succ {A : AlgebraSheaf S} {m : ℕ}
    (p : Fin (m + 1) → (𝟙_ (ModuleSheaf S) ⟶ A.X)) :
    natTensorPowPoint (m + 1) p = (λ_ (𝟙_ (ModuleSheaf S))).inv ≫
      (natTensorPowPoint m (Fin.init p) ⊗ₘ p (Fin.last m)) :=
  rfl

/-- **The tensor of a family of points is natural in the sheaf of algebras**, for the inverse of
an isomorphism. -/
theorem natTensorPowPoint_comp_natTensorPowCongr_inv {A B : AlgebraSheaf S} (e : A ≅ B) :
    ∀ (m : ℕ) (p : Fin m → (𝟙_ (ModuleSheaf S) ⟶ B.X)),
      natTensorPowPoint m p ≫ (natTensorPowCongr e m).inv.hom
        = natTensorPowPoint m (fun j => p j ≫ e.inv.hom)
  | 0, p => by
    show 𝟙 (𝟙_ (ModuleSheaf S)) ≫ (natTensorPowCongr e 0).inv.hom = 𝟙 (𝟙_ (ModuleSheaf S))
    exact Category.id_comp _
  | m + 1, p => by
    have ih := natTensorPowPoint_comp_natTensorPowCongr_inv e m (Fin.init p)
    show (λ_ (𝟙_ (ModuleSheaf S))).inv ≫
        (natTensorPowPoint m (Fin.init p) ⊗ₘ p (Fin.last m)) ≫
        ((natTensorPowCongr e m).inv.hom ⊗ₘ e.inv.hom)
      = (λ_ (𝟙_ (ModuleSheaf S))).inv ≫
        (natTensorPowPoint m (fun j => Fin.init p j ≫ e.inv.hom) ⊗ₘ
          (p (Fin.last m) ≫ e.inv.hom))
    exact congrArg (fun z => (λ_ (𝟙_ (ModuleSheaf S))).inv ≫ z)
      ((tensorHom_comp_tensorHom _ _ _ _).trans
        (congrArg (fun z => z ⊗ₘ (p (Fin.last m) ≫ e.inv.hom)) ih))

/-! ### The tensor of the points of a family of endomorphisms -/

/-- **The tensor of the points of a family of endomorphisms of `E` is the point of the tensor of
that family**, through the identification `natTensorPowEndAlgebraIso` of the tensor power of the
endomorphism algebra with the endomorphism algebra of the tensor power. -/
theorem natTensorPowPoint_curry' {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E) :
    ∀ (n : ℕ) (f : Fin (n + 1) → (E ⟶ E)),
      natTensorPowPoint (n + 1) (fun j => MonoidalClosed.curry' (f j)) ≫
          (natTensorPowEndAlgebraIso hE n).hom.hom
        = MonoidalClosed.curry' (natTensorPowFam (n + 1) f)
  | 0, f => by
    have h1 : 𝟙 (𝟙_ (ModuleSheaf S)) ⊗ₘ f (Fin.last 0)
        = (λ_ E).hom ≫ f (Fin.last 0) ≫ (λ_ E).inv :=
      (id_tensorHom _ _).trans (whiskerLeft_unit_eq_conj _)
    show (λ_ (𝟙_ (ModuleSheaf S))).inv ≫
        (𝟙 (𝟙_ (ModuleSheaf S)) ⊗ₘ MonoidalClosed.curry' (f (Fin.last 0))) ≫
        ((λ_ ((MonoidalClosed.internalEnd E).X)).hom ≫
          (MonoidalClosed.internalEndCongr (λ_ E).symm).hom.hom)
      = MonoidalClosed.curry' (𝟙 (𝟙_ (ModuleSheaf S)) ⊗ₘ f (Fin.last 0))
    exact (leftUnitorInv_id_tensorHom_leftUnitor_comp _ _).trans
      ((MonoidalClosed.curry'_comp_internalEndCongr_hom _ _).trans
        (congrArg MonoidalClosed.curry' h1.symm))
  | n + 1, f => by
    have ih := natTensorPowPoint_curry' hE n (Fin.init f)
    show (λ_ (𝟙_ (ModuleSheaf S))).inv ≫
        (natTensorPowPoint (n + 1) (fun j => MonoidalClosed.curry' (Fin.init f j)) ⊗ₘ
          MonoidalClosed.curry' (f (Fin.last (n + 1)))) ≫
        (((natTensorPowEndAlgebraIso hE n).hom.hom ⊗ₘ
            𝟙 ((MonoidalClosed.internalEnd E).X)) ≫
          MonoidalClosed.tensorInternalEnd (Stacks.TensorPowers.natTensorPow E (n + 1)) E)
      = MonoidalClosed.curry' (natTensorPowFam (n + 1) (Fin.init f) ⊗ₘ f (Fin.last (n + 1)))
    exact (leftUnitorInv_tensorHom_comp_tensorHom_id _ _ _ _).trans
      ((congrArg (fun z => (λ_ (𝟙_ (ModuleSheaf S))).inv ≫
          (z ⊗ₘ MonoidalClosed.curry' (f (Fin.last (n + 1)))) ≫
          MonoidalClosed.tensorInternalEnd
            (Stacks.TensorPowers.natTensorPow E (n + 1)) E) ih).trans
        (MonoidalClosed.curry'_tensorHom _ _).symm)

/-! ### A matrix unit of the big algebra is a tensor of matrix units of the small one -/

/-- **A matrix unit of the algebra of size `d ^ (n+1)` is the tensor of the matrix units of the
algebra of size `d`**, as points: the point-level form of
`Stacks.EtaleCohomology.BrauerScheme.conj_natTensorPowFreeIso_uncurry'_matIncl`. -/
theorem natTensorPowPoint_matIncl (T : Scheme.{u}) (d n : ℕ) (c e : Fin (n + 1) → Fin d) :
    natTensorPowPoint (n + 1)
        (fun j => matIncl (S := T) (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j)))
      = matIncl (S := T) (ULift.up.{u, 0} c, ULift.up.{u, 0} e) ≫
          (endAlgebraCongr (natTensorPowFreeIso T d (n + 1))).inv.hom ≫
          (natTensorPowEndAlgebraIso
            (isFiniteLocallyFree_free (S := T) (ULift.{u, 0} (Fin d))) n).inv.hom := by
  have key := natTensorPowPoint_curry'
    (isFiniteLocallyFree_free (S := T) (ULift.{u, 0} (Fin d))) n
    (fun j => MonoidalClosed.uncurry' (matIncl (S := T)
      (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j))))
  simp only [MonoidalClosed.curry'_uncurry'] at key
  refine ((Iso.eq_comp_inv ((Mon.forget _).mapIso (natTensorPowEndAlgebraIso
    (isFiniteLocallyFree_free (S := T) (ULift.{u, 0} (Fin d))) n))).2 ?_).trans
    (Category.assoc _ _ _)
  exact key.trans ((congrArg MonoidalClosed.curry'
        (conj_natTensorPowFreeIso_uncurry'_matIncl T d (n + 1) c e).symm).trans
      ((MonoidalClosed.curry'_comp_internalEndCongr_inv
          (natTensorPowFreeIso T d (n + 1)) _).symm.trans
        (congrArg
          (fun z => z ≫ (endAlgebraCongr (natTensorPowFreeIso T d (n + 1))).inv.hom)
          (MonoidalClosed.curry'_uncurry' _))))

/-! ### The normal form of Saltman's point -/

/-- **THE NORMAL FORM OF SALTMAN'S POINT.** The point of `B^{⊗ d}` which the trivialisation
`M : B ≅ Mat_d(𝒪_T)` attaches to Saltman's projector is the combination, with the entries of
`Matrix.altProj` as coefficients, of the tensors over `j` of the images under `M⁻¹` of the matrix
units of `Mat_d(𝒪_T)`.

Nothing on the right-hand side mentions `natTensorPowEndAlgebraIso` or `natTensorPowFreeIso`,
which is what makes the point computable along a pullback. -/
theorem curry'_altProjFree_comp_natTensorPowTrivIso_inv_eq_sum {T : Scheme.{u}}
    {B : AlgebraSheaf T} {n : ℕ} (M : B ≅ matrixAlgebra T (n + 1)) :
    MonoidalClosed.curry' (altProjFree T (n + 1)) ≫ (natTensorPowTrivIso M).inv.hom
      = ∑ k : ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)) ×
            ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)),
          Matrix.altProj (R₀ T) k.1.down k.2.down ≫
            natTensorPowPoint (n + 1) (fun j => matIncl (S := T)
              (ULift.up.{u, 0} (k.1.down j), ULift.up.{u, 0} (k.2.down j)) ≫ M.inv.hom) := by
  refine Eq.trans (congrArg (fun z => z ≫ (natTensorPowTrivIso M).inv.hom)
    (curry'_eq_sum_matIncl (altProjFree T (n + 1)))) ?_
  refine Eq.trans (Preadditive.sum_comp _ _ _) (Finset.sum_congr rfl fun k _ => ?_)
  obtain ⟨⟨c⟩, ⟨e⟩⟩ := k
  have hstep : matIncl (S := T) (ULift.up.{u, 0} c, ULift.up.{u, 0} e) ≫
        (natTensorPowTrivIso M).inv.hom
      = natTensorPowPoint (n + 1) (fun j => matIncl (S := T)
          (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j)) ≫ M.inv.hom) := by
    have hre : matIncl (S := T) (ULift.up.{u, 0} c, ULift.up.{u, 0} e) ≫
          (natTensorPowTrivIso M).inv.hom
        = (matIncl (S := T) (ULift.up.{u, 0} c, ULift.up.{u, 0} e) ≫
            (endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))).inv.hom ≫
            (natTensorPowEndAlgebraIso (isFiniteLocallyFree_free (S := T)
              (ULift.{u, 0} (Fin (n + 1)))) n).inv.hom) ≫
          (natTensorPowCongr M (n + 1)).inv.hom := by
      show matIncl (S := T) (ULift.up.{u, 0} c, ULift.up.{u, 0} e) ≫
          ((endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))).inv.hom ≫
            (natTensorPowEndAlgebraIso (isFiniteLocallyFree_free (S := T)
              (ULift.{u, 0} (Fin (n + 1)))) n).inv.hom ≫
            (natTensorPowCongr M (n + 1)).inv.hom) = _
      simp only [Category.assoc]
    exact hre.trans
      ((congrArg (fun z => z ≫ (natTensorPowCongr M (n + 1)).inv.hom)
        (natTensorPowPoint_matIncl T (n + 1) n c e).symm).trans
          (natTensorPowPoint_comp_natTensorPowCongr_inv M (n + 1) _))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => z ≫ matIncl (S := T) (ULift.up.{u, 0} c, ULift.up.{u, 0} e) ≫
        (natTensorPowTrivIso M).inv.hom)
      (freeDualMatrix_altProjFree T (n + 1) (ULift.up.{u, 0} c) (ULift.up.{u, 0} e))).trans
      (congrArg (fun z => Matrix.altProj (R₀ T) c e ≫ z) hstep))

end Stacks.EtaleCohomology.BrauerScheme

end

end

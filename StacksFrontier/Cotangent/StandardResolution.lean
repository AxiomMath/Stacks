module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.StandardResolution
public import StacksFrontier.AlgebraicTopology.StandardResolution.Basic

/-!
# The standard resolution of a commutative algebra

For a commutative ring `A` and a commutative `A`-algebra `B`, the comonad arising from the
polynomial-algebra/forgetful adjunction gives an augmented simplicial commutative `A`-algebra.
Its terms are the iterated polynomial algebras `A[B]`, `A[A[B]]`, and so on, and its
augmentation is polynomial evaluation.

## Main definitions

* `CommAlgCat.free`: the polynomial-algebra functor, left adjoint to the underlying-type
  functor on commutative `A`-algebras.
* `CommAlgCat.adj`: the polynomial-algebra/underlying-type adjunction.
* `CommAlgCat.polynomialComonad`: the comonad of that adjunction, with value `A[B]` at `B`.
* `CommAlgCat.standardEndofunctor`: Godement's standard augmented simplicial endofunctor for
  that comonad.
* `CommAlgCat.standardResolution`: the standard augmented simplicial resolution of a
  commutative `A`-algebra.
* `CommAlgCat.standardResolutionFunctor`: its functoriality in that algebra.
* `CommAlgCat.standardResolutionAugmentation`: the augmentation maps for inputs in independent
  universes, with values in the original algebra.

## Main results

* `CommAlgCat.standardResolution_obj` identifies every term with the corresponding iterate of
  the polynomial-algebra comonad, and `CommAlgCat.standardResolution_zero`,
  `CommAlgCat.standardResolution_one` identify the first two terms with `A[B]` and `A[A[B]]`.
* `CommAlgCat.standardResolution_face` and `CommAlgCat.standardResolution_degeneracy` identify
  its structure maps with Godement's standard maps.
* `CommAlgCat.standardResolution_augmentation` and
  `CommAlgCat.standardResolution_augmentation_X` identify the augmentation with polynomial
  evaluation.
* `CommAlgCat.standardResolutionAugmentation_naturality` and
  `CommAlgCat.standardResolutionAugmentation_map` express compatibility of the
  independent-universe augmentation with every simplicial operator and every algebra map.

## Implementation notes

The free commutative `A`-algebra on `S` is implemented by `MvPolynomial S A`. The standard
resolution is obtained by evaluating Godement's augmented simplicial endofunctor at `B`. The
counit is polynomial evaluation and comultiplication substitutes `[[b]]` for `[b]`, as recorded
by `CommAlgCat.polynomialComonad_counit` and `CommAlgCat.polynomialComonad_comul`.

The choice of Godement resolution is packaged by
`CategoryTheory.Comonad.standardResolutionFunctorData`, which supplies the term and
structure-map equations for an arbitrary comonad; `standardEndofunctor` is its underlying
augmented simplicial object of endofunctors and the `standardEndofunctor_*` lemmas are its
fields.

The canonical construction works in a common ambient universe containing `A` and `B`. Its
augmentation point is definitionally `B`, not a universe lift: its `hom` is directly a morphism
to the constant simplicial algebra on `B`. Its degree-zero term is `MvPolynomial B A`. The
exposed construction permits these types to be used directly, while the displayed term and
structure-map equations give its computational interface.

For an algebra supplied in an independent, possibly smaller universe,
`standardResolutionAugmentation` internally enlarges its universe and then evaluates back in
the original algebra, so these maps can also be used directly to extend scalars to `B`.

## References

* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace CommAlgCat

/-- The polynomial-algebra functor, left adjoint to the underlying-type functor on commutative
`A`-algebras. -/
@[implicit_reducible]
noncomputable def free (A : Type u) [CommRing A] :
    Type (max u v) ⥤ CommAlgCat.{max u v} A where
  obj S := CommAlgCat.of A (MvPolynomial S A)
  map f := CommAlgCat.ofHom (MvPolynomial.rename f)

/-- The polynomial-algebra/underlying-type adjunction for commutative `A`-algebras. -/
noncomputable def adj (A : Type u) [CommRing A] :
    free.{u, v} A ⊣ forget (CommAlgCat.{max u v} A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾fun x => f (MvPolynomial.X x)
          invFun := fun f => CommAlgCat.ofHom (MvPolynomial.aeval f)
          left_inv := fun f =>
            CommAlgCat.hom_ext (MvPolynomial.algHom_ext fun x => MvPolynomial.aeval_X _ _)
          right_inv := fun f => by
            ext x
            exact MvPolynomial.aeval_X _ _ }
      homEquiv_naturality_left_symm := fun f g => by
        apply CommAlgCat.hom_ext
        apply MvPolynomial.algHom_ext
        intro x
        change (MvPolynomial.aeval fun y => g (f y)) (MvPolynomial.X x) =
          (MvPolynomial.aeval g) ((MvPolynomial.rename f) (MvPolynomial.X x))
        simp }

/-- The free-forget comonad on commutative `A`-algebras. Its value on `B` is the polynomial
algebra `A[B]`. -/
@[implicit_reducible]
noncomputable def polynomialComonad (A : Type u) [CommRing A] :
    Comonad (CommAlgCat.{max u v} A) :=
  (adj.{u, v} A).toComonad

/-- The unit of the polynomial-algebra adjunction inserts the variables. -/
@[simp]
theorem adj_unit_app (A : Type u) [CommRing A] (S : Type (max u v)) (s : S) :
    (adj.{u, v} A).unit.app S s = MvPolynomial.X s := rfl

/-- The counit evaluates each variable at the element which indexes it. -/
@[simp]
theorem polynomialComonad_counit (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    ((polynomialComonad.{u, v} A).ε.app B).hom = MvPolynomial.aeval id := rfl

/-- Comultiplication replaces a variable `[b]` by the variable `[[b]]`. -/
@[simp]
theorem polynomialComonad_comul (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    ((polynomialComonad.{u, v} A).δ.app B).hom =
      MvPolynomial.rename (MvPolynomial.X : B → MvPolynomial B A) := rfl

/-- Godement's standard augmented simplicial endofunctor for the polynomial-algebra comonad. -/
noncomputable def standardEndofunctor (A : Type u) [CommRing A] :
    SimplicialObject.Augmented (CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A) :=
  (Comonad.standardResolutionFunctorData (polynomialComonad.{u, v} A)).augmentation

/-- The term in degree `n` of the standard endofunctor is the `(n + 1)`-fold iterate of the
polynomial-algebra comonad. -/
theorem standardEndofunctor_obj (A : Type u) [CommRing A] (n : ℕ) :
    (standardEndofunctor.{u, v} A).left.obj (op ⦋n⦌) =
      ((polynomialComonad.{u, v} A).toFunctor.iterate (n + 1)) :=
  (Comonad.standardResolutionFunctorData (polynomialComonad.{u, v} A)).obj_eq n

/-- The augmentation point of the standard endofunctor is the identity functor. -/
theorem standardEndofunctor_right (A : Type u) [CommRing A] :
    (standardEndofunctor.{u, v} A).right =
      (𝟭 (CommAlgCat.{max u v} A) : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A) :=
  (Comonad.standardResolutionFunctorData (polynomialComonad.{u, v} A)).point_eq

/-- The faces of the standard endofunctor are Godement's. -/
theorem standardEndofunctor_face (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 2)) :
    (standardEndofunctor.{u, v} A).left.δ j =
      eqToHom (standardEndofunctor_obj.{u, v} A (n + 1)) ≫
        Godement.face (polynomialComonad.{u, v} A).ε (n + 1) j ≫
          eqToHom (standardEndofunctor_obj.{u, v} A n).symm :=
  (Comonad.standardResolutionFunctorData (polynomialComonad.{u, v} A)).face_eq n j

/-- The degeneracies of the standard endofunctor are Godement's. -/
theorem standardEndofunctor_degeneracy (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 1)) :
    (standardEndofunctor.{u, v} A).left.σ j =
      eqToHom (standardEndofunctor_obj.{u, v} A n) ≫
        Godement.degeneracy (polynomialComonad.{u, v} A).δ n j ≫
          eqToHom (standardEndofunctor_obj.{u, v} A (n + 1)).symm :=
  (Comonad.standardResolutionFunctorData (polynomialComonad.{u, v} A)).degeneracy_eq n j

/-- The augmentation of the standard endofunctor is the counit in degree zero. -/
theorem standardEndofunctor_augmentation (A : Type u) [CommRing A] :
    (standardEndofunctor.{u, v} A).hom.app (op ⦋0⦌) =
      eqToHom (standardEndofunctor_obj.{u, v} A 0) ≫
        Godement.face (polynomialComonad.{u, v} A).ε 0 0 ≫
          eqToHom (standardEndofunctor_right.{u, v} A).symm :=
  (Comonad.standardResolutionFunctorData (polynomialComonad.{u, v} A)).augmentation_eq

/-- **Stacks Project, Tag 08PM.** The standard resolution of the commutative `A`-algebra `B`,
augmented to `B`. Its degree `n` term is the `(n + 1)`-fold iteration of `C ↦ A[C]`. -/
@[stacks 08PM, implicit_reducible]
noncomputable def standardResolution (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) : SimplicialObject.Augmented (CommAlgCat.{max u v} A) := by
  let Q := (SimplicialObject.Augmented.whiskeringObj _ _
    ((evaluation (CommAlgCat.{max u v} A) (CommAlgCat.{max u v} A)).obj B)).obj
      (standardEndofunctor.{u, v} A)
  let hB : Q.right = B :=
    congrArg (fun F : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A => F.obj B)
      (standardEndofunctor_right.{u, v} A)
  exact
    { left := (standardEndofunctor.{u, v} A).left ⋙
        (evaluation (CommAlgCat.{max u v} A) (CommAlgCat.{max u v} A)).obj B
      right := B
      hom := Q.hom ≫ (SimplicialObject.const (CommAlgCat.{max u v} A)).map (eqToHom hB) }

/-- The augmentation point of the standard resolution is the original algebra `B`. -/
@[simp]
theorem standardResolution_right (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).right = B := rfl

/-- The degree `n` term of the standard resolution is the `(n + 1)`-fold iterate of the
polynomial-algebra comonad, evaluated at `B`. -/
theorem standardResolution_obj (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution A B).left.obj (op ⦋n⦌) =
      ((polynomialComonad.{u, v} A).toFunctor.iterate (n + 1)).obj B := by
  show ((standardEndofunctor.{u, v} A).left.obj (op ⦋n⦌)).obj B = _
  exact congrArg
    (fun F : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A => F.obj B)
    (standardEndofunctor_obj.{u, v} A n)

/-- The degree-zero term is the polynomial `A`-algebra on the underlying set of `B`. -/
theorem standardResolution_zero (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).left.obj (op ⦋0⦌) = CommAlgCat.of A (MvPolynomial B A) := by
  rw [standardResolution_obj]
  rfl

/-- The algebra equivalence identifying degree zero with `A[B]`. -/
noncomputable abbrev standardResolutionZeroAlgEquiv (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).left.obj (op ⦋0⦌) ≃ₐ[A] MvPolynomial B A :=
  CommAlgCat.algEquivOfIso (eqToIso (standardResolution_zero A B))

/-- The degree-one term is the polynomial `A`-algebra on the underlying set of the degree-zero
term. -/
theorem standardResolution_one (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).left.obj (op ⦋1⦌) =
      CommAlgCat.of A (MvPolynomial (MvPolynomial B A) A) := by
  rw [standardResolution_obj]
  rfl

/-- The augmentation in degree zero is polynomial evaluation. -/
theorem standardResolution_augmentation (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).hom.app (op ⦋0⦌) =
      eqToHom (standardResolution_zero A B) ≫
        CommAlgCat.ofHom (MvPolynomial.aeval (id : B → B)) := by
  show (((standardEndofunctor.{u, v} A).hom.app (op ⦋0⦌)).app B ≫ 𝟙 _) ≫
      eqToHom (congrArg
        (fun F : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A => F.obj B)
        (standardEndofunctor_right.{u, v} A)) = _
  rw [Category.comp_id, standardEndofunctor_augmentation]
  simp only [NatTrans.comp_app, eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]
  rfl

/-- Augmentation sends the variable indexed by `b` to `b`. -/
@[simp↓]
theorem standardResolution_augmentation_X (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (b : B) :
    (standardResolution A B).hom.app (op ⦋0⦌)
      ((standardResolutionZeroAlgEquiv A B).symm (MvPolynomial.X b)) = b := by
  show (standardResolution A B).hom.app (op ⦋0⦌)
    (eqToHom (standardResolution_zero A B).symm (MvPolynomial.X b)) = b
  rw [standardResolution_augmentation, ← CommAlgCat.comp_apply]
  simp

/-- The faces of the standard resolution are the evaluations of Godement's faces for the
polynomial-algebra comonad. -/
theorem standardResolution_face (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
    (n : ℕ) (j : Fin (n + 2)) :
    (standardResolution A B).left.δ j =
      eqToHom (standardResolution_obj A B (n + 1)) ≫
        (Godement.face (polynomialComonad.{u, v} A).ε (n + 1) j).app B ≫
            eqToHom (standardResolution_obj A B n).symm := by
  show ((standardEndofunctor.{u, v} A).left.δ j).app B = _
  rw [congrArg (fun f => f.app B) (standardEndofunctor_face.{u, v} A n j)]
  simp only [NatTrans.comp_app, eqToHom_app]

/-- The degeneracies of the standard resolution are the evaluations of Godement's degeneracies
for the polynomial-algebra comonad. -/
theorem standardResolution_degeneracy (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) (j : Fin (n + 1)) :
    (standardResolution A B).left.σ j =
      eqToHom (standardResolution_obj A B n) ≫
        (Godement.degeneracy (polynomialComonad.{u, v} A).δ n j).app B ≫
            eqToHom (standardResolution_obj A B (n + 1)).symm := by
  show ((standardEndofunctor.{u, v} A).left.σ j).app B = _
  rw [congrArg (fun f => f.app B) (standardEndofunctor_degeneracy.{u, v} A n j)]
  simp only [NatTrans.comp_app, eqToHom_app]

/-- The standard resolution is functorial in the commutative `A`-algebra. On the augmentation
points this functor is the identity. -/
@[implicit_reducible]
noncomputable def standardResolutionFunctor (A : Type u) [CommRing A] :
    CommAlgCat.{max u v} A ⥤ SimplicialObject.Augmented (CommAlgCat.{max u v} A) where
  obj B := standardResolution A B
  map {B C} f :=
    { left :=
        { app n := ((standardEndofunctor.{u, v} A).left.obj n).map f
          naturality i j g :=
            ((standardEndofunctor.{u, v} A).left.map g).naturality f |>.symm }
      right := f
      w := by
        apply NatTrans.ext
        funext n
        let hB := congrArg
          (fun F : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A => F.obj B)
          (standardEndofunctor_right.{u, v} A)
        let hC := congrArg
          (fun F : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A => F.obj C)
          (standardEndofunctor_right.{u, v} A)
        change ((standardEndofunctor.{u, v} A).left.obj n).map f ≫
          ((((standardEndofunctor.{u, v} A).hom.app n).app C ≫ 𝟙 _) ≫ eqToHom hC) =
          ((((standardEndofunctor.{u, v} A).hom.app n).app B ≫ 𝟙 _) ≫ eqToHom hB) ≫ f
        simp only [Category.comp_id, Category.assoc]
        rw [← Category.assoc, NatTrans.naturality, Category.assoc]
        congr 1
        change (standardEndofunctor.{u, v} A).right.map f ≫ eqToHom hC =
          eqToHom hB ≫ f
        simpa only [eqToHom_app, Functor.id_map, hB, hC] using
          (eqToHom (standardEndofunctor_right.{u, v} A)).naturality f }
  map_id B := by
    ext n : 2 <;> simp
    rfl
  map_comp f g := by
    ext n : 2 <;> simp

/-- The resolution functor evaluates to the standard resolution. -/
@[simp]
theorem standardResolutionFunctor_obj (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (standardResolutionFunctor A).obj B = standardResolution A B := rfl

/-- The functorial map of resolutions lies over the original algebra map. -/
@[simp]
theorem standardResolutionFunctor_map_right (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    ((standardResolutionFunctor A).map f).right = f := rfl

/-- The degreewise augmentation for an algebra in an independent universe. Universe enlargement
is internal to the source; the scalar-extension map takes values in the original algebra. -/
noncomputable abbrev standardResolutionAugmentation (A : Type u) [CommRing A]
    (B : CommAlgCat.{v} A) (n : SimplexCategoryᵒᵖ) :
    (standardResolution A ((CommAlgCat.uliftFunctor.{u, v, u} A).obj B)).left.obj n →ₐ[A] B :=
  ULift.algEquiv.toAlgHom.comp
    ((standardResolution A ((CommAlgCat.uliftFunctor.{u, v, u} A).obj B)).hom.app n).hom

/-- The independent-universe augmentation commutes with every simplicial operator. -/
theorem standardResolutionAugmentation_naturality (A : Type u) [CommRing A]
    (B : CommAlgCat.{v} A) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (standardResolutionAugmentation A B j).comp
      ((standardResolution A ((CommAlgCat.uliftFunctor.{u, v, u} A).obj B)).left.map f).hom =
        standardResolutionAugmentation A B i := by
  let P := standardResolution A ((CommAlgCat.uliftFunctor.{u, v, u} A).obj B)
  have h : P.left.map f ≫ P.hom.app j = P.hom.app i := by
    simp
  ext x
  exact congrArg ULift.down (congrArg (fun g => g x) h)

/-- The independent-universe augmentation is natural in the original algebra `B`. -/
theorem standardResolutionAugmentation_map (A : Type u) [CommRing A]
    {B C : CommAlgCat.{v} A} (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    (standardResolutionAugmentation A C n).comp
      (((standardResolutionFunctor A).map
        ((CommAlgCat.uliftFunctor.{u, v, u} A).map f)).left.app n).hom =
          f.hom.comp (standardResolutionAugmentation A B n) := by
  let g := (standardResolutionFunctor A).map ((CommAlgCat.uliftFunctor.{u, v, u} A).map f)
  ext x
  exact congrArg ULift.down (congrArg (fun k => k x) (NatTrans.congr_app g.w n))

/-! ### The variables of the first two terms, and the faces in degree one -/

/-- Transport along an equality of algebras, then back, is the identity. -/
theorem eqToHom_symm_eqToHom_apply {A : Type u} [CommRing A] {X Y : CommAlgCat.{v} A}
    (h : X = Y) (x : X) : eqToHom h.symm (eqToHom h x) = x := by
  rw [← CommAlgCat.comp_apply, eqToHom_trans, eqToHom_refl, CommAlgCat.id_apply]

/-- Transport back along an equality of algebras, then forward, is the identity. -/
theorem eqToHom_eqToHom_symm_apply {A : Type u} [CommRing A] {X Y : CommAlgCat.{v} A}
    (h : X = Y) (y : Y) : eqToHom h (eqToHom h.symm y) = y := by
  rw [← CommAlgCat.comp_apply, eqToHom_trans, eqToHom_refl, CommAlgCat.id_apply]

/-- The variable `[b]` of the degree-zero term `P₀ = A[B]`, indexed by an element of `B`. -/
noncomputable def standardResolutionVarZero (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (b : B) : (standardResolution A B).left.obj (op ⦋0⦌) :=
  (standardResolutionZeroAlgEquiv A B).symm (MvPolynomial.X b)

/-- The variable `[p]` of the degree-one term `P₁ = A[A[B]]`, indexed by an element of the
degree-zero term `P₀ = A[B]`. -/
noncomputable def standardResolutionVarOne (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (p : (standardResolution A B).left.obj (op ⦋0⦌)) :
    (standardResolution A B).left.obj (op ⦋1⦌) :=
  eqToHom (standardResolution_one A B).symm
    (MvPolynomial.X (eqToHom (standardResolution_zero A B) p))

/-- The augmentation sends the variable `[b]` to `b`. -/
@[simp]
theorem standardResolution_augmentation_varZero (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (b : B) :
    (standardResolution A B).hom.app (op ⦋0⦌) (standardResolutionVarZero A B b) = b :=
  standardResolution_augmentation_X A B b

/-- Evaluating `[z]` at `z` recovers `z`, up to the transports along `h₁` and `h₂`. -/
private theorem eqToHom_aeval_id_eqToHom_apply {A : Type u} [CommRing A]
    {P Q : CommAlgCat.{max u v} A} {M : Type (max u v)} [CommRing M] [Algebra A M]
    (h₁ : P = CommAlgCat.of A (MvPolynomial M A))
    (h₂ : Q = CommAlgCat.of A M) (z : Q) :
    (eqToHom h₁ ≫ CommAlgCat.ofHom (MvPolynomial.aeval (id : M → M)) ≫ eqToHom h₂.symm)
      (eqToHom h₁.symm (MvPolynomial.X (eqToHom h₂ z))) = z := by
  rw [CommAlgCat.comp_apply, CommAlgCat.comp_apply, eqToHom_eqToHom_symm_apply,
    CommAlgCat.ofHom_apply, MvPolynomial.aeval_X, id_eq, eqToHom_symm_eqToHom_apply]

/-- The zeroth face `P₁ → P₀` is the counit of the polynomial-algebra comonad at `A[B]`, i.e.
evaluation of a polynomial in the variables `[f]` at `f ∈ A[B]`. -/
theorem standardResolution_δ_zero_eq (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).left.δ (0 : Fin 2) =
      eqToHom (standardResolution_one A B) ≫
        CommAlgCat.ofHom (MvPolynomial.aeval (id : MvPolynomial B A → MvPolynomial B A)) ≫
        eqToHom (standardResolution_zero A B).symm := by
  rw [standardResolution_face A B 0 (0 : Fin 2), Godement.Prep.face_zero]
  rfl

/-- The first face `P₁ → P₀` is the polynomial-algebra functor applied to the counit at `B`:
it renames the variable `[f]` to `[ε f]`. -/
theorem standardResolution_δ_one_eq (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (standardResolution A B).left.δ (1 : Fin 2) =
      eqToHom (standardResolution_one A B) ≫
        CommAlgCat.ofHom (MvPolynomial.rename (MvPolynomial.aeval (id : B → B))) ≫
        eqToHom (standardResolution_zero A B).symm := by
  rw [standardResolution_face A B 0 (1 : Fin 2),
    show (1 : Fin 2) = Fin.succ 0 from rfl, Godement.Prep.face_succ]
  rfl

/-- The zeroth face deletes the outermost variable: `δ₀ [p] = p`. -/
@[simp]
theorem standardResolution_δ_zero_varOne (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (p : (standardResolution A B).left.obj (op ⦋0⦌)) :
    (standardResolution A B).left.δ (0 : Fin 2) (standardResolutionVarOne A B p) = p := by
  rw [standardResolution_δ_zero_eq, standardResolutionVarOne]
  exact eqToHom_aeval_id_eqToHom_apply _ _ p

/-- The first face applies the augmentation inside the variable: `δ₁ [p] = [ε p]`. -/
@[simp]
theorem standardResolution_δ_one_varOne (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (p : (standardResolution A B).left.obj (op ⦋0⦌)) :
    (standardResolution A B).left.δ (1 : Fin 2) (standardResolutionVarOne A B p) =
      standardResolutionVarZero A B ((standardResolution A B).hom.app (op ⦋0⦌) p) := by
  rw [standardResolution_δ_one_eq, standardResolution_augmentation, standardResolutionVarOne,
    standardResolutionVarZero, CommAlgCat.comp_apply, CommAlgCat.comp_apply,
    CommAlgCat.comp_apply, eqToHom_eqToHom_symm_apply, CommAlgCat.ofHom_apply,
    CommAlgCat.ofHom_apply, MvPolynomial.rename_X]
  rfl

/-! ### Polynomiality of every term, and surjectivity of the augmentation -/

/-- Every term of the standard resolution is a polynomial algebra over `A`, on the underlying set
of the previous iterate. -/
theorem standardResolution_obj_mvPolynomial (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution A B).left.obj (op ⦋n⦌) =
      CommAlgCat.of A
        (MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) A) := by
  rw [standardResolution_obj]
  rfl

/-- The same, with the index type of the degree `n + 1` term written out as a polynomial algebra
in its turn. -/
theorem standardResolution_obj_mvPolynomial_succ (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution A B).left.obj (op ⦋n + 1⦌) =
      CommAlgCat.of A (MvPolynomial
        (MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) A) A) := by
  rw [standardResolution_obj]
  rfl

/-- In every degree the zeroth face is the counit of the polynomial-algebra comonad: polynomial
evaluation. -/
theorem standardResolution_δ_zero_aeval (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution A B).left.δ (0 : Fin (n + 2)) =
      eqToHom (standardResolution_obj_mvPolynomial_succ A B n) ≫
        CommAlgCat.ofHom (MvPolynomial.aeval
          (id : MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) A →
            MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) A)) ≫
        eqToHom (standardResolution_obj_mvPolynomial A B n).symm := by
  rw [standardResolution_face A B n (0 : Fin (n + 2)), Godement.Prep.face_zero]
  rfl

/-- The zeroth face is surjective in every degree: it evaluates the variable `[p]` at `p`. -/
theorem surjective_standardResolution_δ_zero (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    Function.Surjective ((standardResolution A B).left.δ (0 : Fin (n + 2))) := by
  rw [standardResolution_δ_zero_aeval]
  exact fun z => ⟨_, eqToHom_aeval_id_eqToHom_apply
    (standardResolution_obj_mvPolynomial_succ A B n) (standardResolution_obj_mvPolynomial A B n) z⟩

/-- The augmentation of the standard resolution is surjective in every degree: `Pₙ` surjects onto
`B`. This is the standing hypothesis of Stacks Remark 08QI. -/
theorem surjective_standardResolution_augmentation (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    Function.Surjective ((standardResolution A B).hom.app (op ⦋n⦌)) := by
  induction n with
  | zero =>
    exact fun b => ⟨standardResolutionVarZero A B b, standardResolution_augmentation_varZero A B b⟩
  | succ n ih =>
    have hnat : (standardResolution A B).left.δ (0 : Fin (n + 2)) ≫
        (standardResolution A B).hom.app (op ⦋n⦌) =
        (standardResolution A B).hom.app (op ⦋n + 1⦌) :=
      (standardResolution A B).hom.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op
    intro b
    obtain ⟨p, hp⟩ := ih b
    obtain ⟨q, hq⟩ := surjective_standardResolution_δ_zero A B n p
    exact ⟨q, by rw [← hnat, CommAlgCat.comp_apply, hq, hp]⟩

end CommAlgCat

end

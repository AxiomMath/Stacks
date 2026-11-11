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
* `CommAlgCat.face_eq_aeval_and_degeneracy_eq_rename`: those faces and degeneracies on the
  variables, `d₀([x]) = x`, `d₁([x]) = [ε x]`, `s₀([x]) = [[x]]`, and the recursive forms in every
  degree (Stacks Example 09CB).
* `CommAlgCat.standardResolution_augmentation` and
  `CommAlgCat.standardResolution_augmentation_X` identify the augmentation with polynomial
  evaluation.
* `CommAlgCat.standardResolutionAugmentation_naturality` and
  `CommAlgCat.standardResolutionAugmentation_map` express compatibility of the
  independent-universe augmentation with every simplicial operator and every algebra map.
* `CommAlgCat.exists_homotopyInverse_whiskered_standardResolution` (Stacks 08NE): the whiskered
  augmentations `1_V ⋆ ε` and `ε ⋆ 1_U` of the standard resolution are homotopy equivalences, with
  homotopy inverses the iterated variables `b ↦ [⋯[b]⋯]` and `[e] ↦ [⋯[e]⋯]`.

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
* [Stacks Project, Tag 09CB](https://stacks.math.columbia.edu/tag/09CB)
* [Stacks Project, Tag 08NE](https://stacks.math.columbia.edu/tag/08NE)
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
  change ((standardEndofunctor.{u, v} A).left.obj (op ⦋n⦌)).obj B = _
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
  change (((standardEndofunctor.{u, v} A).hom.app (op ⦋0⦌)).app B ≫ 𝟙 _) ≫
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
  change (standardResolution A B).hom.app (op ⦋0⦌)
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
  change ((standardEndofunctor.{u, v} A).left.δ j).app B = _
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
  change ((standardEndofunctor.{u, v} A).left.σ j).app B = _
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

/-! ### The faces and degeneracies on the variables -/

/-- **Stacks 09CB**.
Let `A` be a ring and `B` a commutative `A`-algebra, and let `Xₙ(B) = A[A[⋯[B]⋯]]` (`n + 1`
brackets, each a polynomial algebra over `A` on the underlying set of the previous term) be the
standard resolution of `B` for the polynomial-algebra/forgetful adjunction on commutative
`A`-algebras (Stacks Example 08NA; its faces and degeneracies are Godement's maps for
`polynomialComonad A` by `standardResolution_face` and `standardResolution_degeneracy`). As
`A`-algebra maps out of a polynomial algebra, the faces `dⁿⱼ` and degeneracies `sⁿⱼ` are determined
by their values on the variables `[z]`, and they are:
`dⁿ₀` substitutes `z` for `[z]` (`MvPolynomial.aeval id`), `sⁿ₀` sends `[z]` to `[[z]]`
(`MvPolynomial.rename MvPolynomial.X`), and `dⁿ⁺¹ⱼ₊₁`, `sⁿ⁺¹ⱼ₊₁` send `[z]` to `[dⁿⱼ(z)]`, resp.
`[sⁿⱼ(z)]` (`MvPolynomial.rename`). In degree one, for every
`x = ∑ a_k [b_{k,1}] ⋯ [b_{k,n_k}] ∈ A[B]`, this is the statement of the example:
`d₀([x]) = x`, `d₁([x]) = [∑ a_k b_{k,1} ⋯ b_{k,n_k}]`, `s₀([x]) = [[x]]` and
`s₁([x]) = [∑ a_k [[b_{k,1}]] ⋯ [[b_{k,n_k}]]]`. -/
@[stacks 09CB]
theorem face_eq_aeval_and_degeneracy_eq_rename (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    (∀ n : ℕ,
      ((Godement.face (polynomialComonad.{u, v} A).ε n 0).app B).hom = MvPolynomial.aeval id ∧
      (∀ j : Fin (n + 1),
        ((Godement.face (polynomialComonad.{u, v} A).ε (n + 1) j.succ).app B).hom =
          MvPolynomial.rename ((Godement.face (polynomialComonad.{u, v} A).ε n j).app B).hom) ∧
      ((Godement.degeneracy (polynomialComonad.{u, v} A).δ n 0).app B).hom =
        MvPolynomial.rename MvPolynomial.X ∧
      (∀ j : Fin (n + 1),
        ((Godement.degeneracy (polynomialComonad.{u, v} A).δ (n + 1) j.succ).app B).hom =
          MvPolynomial.rename
            ((Godement.degeneracy (polynomialComonad.{u, v} A).δ n j).app B).hom)) ∧
    ∀ x : MvPolynomial B A,
      (Godement.face (polynomialComonad.{u, v} A).ε 1 0).app B (MvPolynomial.X x) = x ∧
      (Godement.face (polynomialComonad.{u, v} A).ε 1 1).app B (MvPolynomial.X x) =
        MvPolynomial.X (MvPolynomial.aeval (id : B → B) x) ∧
      (Godement.degeneracy (polynomialComonad.{u, v} A).δ 1 0).app B (MvPolynomial.X x) =
        MvPolynomial.X (MvPolynomial.X x) ∧
      (Godement.degeneracy (polynomialComonad.{u, v} A).δ 1 1).app B (MvPolynomial.X x) =
        MvPolynomial.X (MvPolynomial.rename MvPolynomial.X x) := by
  refine ⟨fun n => ⟨by cases n <;> rfl, fun j => rfl, by cases n <;> rfl, fun j => rfl⟩,
    fun x => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact MvPolynomial.aeval_X (id : MvPolynomial B A → MvPolynomial B A) x
  · exact MvPolynomial.rename_X (MvPolynomial.aeval (R := A) (id : B → B)) x
  · exact MvPolynomial.rename_X
      (MvPolynomial.X : MvPolynomial B A → MvPolynomial (MvPolynomial B A) A) x
  · exact MvPolynomial.rename_X
      (MvPolynomial.rename (R := A) (MvPolynomial.X : B → MvPolynomial B A)) x

/-! ### The homotopy inverses of the standard resolution are the iterated variables -/

/-- In every degree the zeroth face `dⁿ₀` of Godement's resolution for the polynomial-algebra
comonad is polynomial evaluation `MvPolynomial.aeval id`. -/
theorem face_zero_hom (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ) :
    ((Godement.face (polynomialComonad.{u, v} A).ε n 0).app B).hom = MvPolynomial.aeval id :=
  ((face_eq_aeval_and_degeneracy_eq_rename A B).1 n).1

/-- In every degree the zeroth degeneracy `sⁿ₀` of Godement's resolution for the
polynomial-algebra comonad replaces each variable `[y]` by `[[y]]`. -/
theorem degeneracy_zero_hom (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ) :
    ((Godement.degeneracy (polynomialComonad.{u, v} A).δ n 0).app B).hom =
      MvPolynomial.rename MvPolynomial.X :=
  ((face_eq_aeval_and_degeneracy_eq_rename A B).1 n).2.2.1

/-- The zeroth face deletes the outer bracket of a variable: `dⁿ₀ [y] = y`. -/
theorem face_zero_hom_X (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ)
    (y : ((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) :
    ((Godement.face (polynomialComonad.{u, v} A).ε n 0).app B).hom
      (MvPolynomial.X y : MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B)
        A) = y := by
  exact (DFunLike.congr_fun (face_zero_hom A B n) _).trans (MvPolynomial.aeval_X _ _)

/-- The zeroth degeneracy doubles the bracket of a variable: `sⁿ₀ [y] = [[y]]`. -/
theorem degeneracy_zero_hom_X (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ)
    (y : ((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) :
    ((Godement.degeneracy (polynomialComonad.{u, v} A).δ n 0).app B).hom
      (MvPolynomial.X y : MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B)
        A) =
      (MvPolynomial.X (MvPolynomial.X y : MvPolynomial
        (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) A) :
        MvPolynomial (MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B) A)
          A) := by
  exact (DFunLike.congr_fun (degeneracy_zero_hom A B n) _).trans (MvPolynomial.rename_X _ _)

/-- The iterated variables `b ↦ [⋯[b]⋯]` of a commutative `A`-algebra split the augmentation of
the standard resolution: deleting the outer bracket of `ρ 0` recovers the identity of the
forgetful functor. -/
theorem iteratedX_comp_face_zero (A : Type u) [CommRing A]
    (ρ : ∀ n : ℕ, forget (CommAlgCat.{max u v} A) ⟶
      (polynomialComonad.{u, v} A).toFunctor.iterate (n + 1) ⋙ forget (CommAlgCat.{max u v} A))
    (hρ₀ : ∀ (B : CommAlgCat.{max u v} A) (x : B),
      (ρ 0).app B x = (MvPolynomial.X x : MvPolynomial B A)) :
    ρ 0 ≫ Functor.whiskerRight (Godement.face (polynomialComonad.{u, v} A).ε 0 0)
      (forget (CommAlgCat.{max u v} A)) = 𝟙 (forget (CommAlgCat.{max u v} A)) := by
  ext B x
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, NatTrans.id_app,
    CategoryTheory.id_apply]
  rw [hρ₀]
  exact face_zero_hom_X A B 0 x

/-- The iterated variables of a commutative `A`-algebra are compatible with the zeroth
degeneracy: doubling the innermost bracket of `ρ n` gives `ρ (n + 1)`. -/
theorem iteratedX_comp_degeneracy_zero (A : Type u) [CommRing A]
    (ρ : ∀ n : ℕ, forget (CommAlgCat.{max u v} A) ⟶
      (polynomialComonad.{u, v} A).toFunctor.iterate (n + 1) ⋙ forget (CommAlgCat.{max u v} A))
    (hρ₀ : ∀ (B : CommAlgCat.{max u v} A) (x : B),
      (ρ 0).app B x = (MvPolynomial.X x : MvPolynomial B A))
    (hρ : ∀ (n : ℕ) (B : CommAlgCat.{max u v} A) (x : B),
      (ρ (n + 1)).app B x = (MvPolynomial.X ((ρ n).app B x) :
        MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate (n + 1)).obj B) A))
    (n : ℕ) :
    ρ n ≫ Functor.whiskerRight (Godement.degeneracy (polynomialComonad.{u, v} A).δ n 0)
      (forget (CommAlgCat.{max u v} A)) = ρ (n + 1) := by
  ext B x
  obtain ⟨y, hy⟩ : ∃ y, (ρ n).app B x =
      (MvPolynomial.X y : MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj B)
        A) := by
    cases n with
    | zero => exact ⟨x, hρ₀ B x⟩
    | succ m => exact ⟨(ρ m).app B x, hρ m B x⟩
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  rw [hρ n B x, hy]
  exact degeneracy_zero_hom_X A B n y

/-- The iterated variables `[e] ↦ [⋯[e]⋯]` of a polynomial algebra split the augmentation of the
standard resolution: deleting the outer bracket of `τ 0` recovers the identity of the
polynomial-algebra functor. -/
theorem freeIteratedX_comp_face_zero (A : Type u) [CommRing A]
    (τ : ∀ n : ℕ, free.{u, v} A ⟶
      free.{u, v} A ⋙ (polynomialComonad.{u, v} A).toFunctor.iterate (n + 1))
    (hτ₀ : ∀ (E : Type (max u v)) (e : E),
      ((τ 0).app E).hom (MvPolynomial.X e) =
        (MvPolynomial.X (MvPolynomial.X e : MvPolynomial E A) :
          MvPolynomial (MvPolynomial E A) A)) :
    τ 0 ≫ Functor.whiskerLeft (free.{u, v} A)
      (Godement.face (polynomialComonad.{u, v} A).ε 0 0) = 𝟙 (free.{u, v} A) := by
  refine NatTrans.ext (funext fun E => CommAlgCat.hom_ext
    (MvPolynomial.algHom_ext fun e => ?_))
  rw [NatTrans.comp_app, NatTrans.id_app, CommAlgCat.hom_comp, AlgHom.comp_apply,
    CommAlgCat.hom_id, Functor.whiskerLeft_app, hτ₀]
  exact face_zero_hom_X A ((free.{u, v} A).obj E) 0 (MvPolynomial.X e)

/-- The iterated variables of a polynomial algebra are compatible with the zeroth degeneracy:
doubling the innermost bracket of `τ n` gives `τ (n + 1)`. -/
theorem freeIteratedX_comp_degeneracy_zero (A : Type u) [CommRing A]
    (τ : ∀ n : ℕ, free.{u, v} A ⟶
      free.{u, v} A ⋙ (polynomialComonad.{u, v} A).toFunctor.iterate (n + 1))
    (hτ₀ : ∀ (E : Type (max u v)) (e : E),
      ((τ 0).app E).hom (MvPolynomial.X e) =
        (MvPolynomial.X (MvPolynomial.X e : MvPolynomial E A) :
          MvPolynomial (MvPolynomial E A) A))
    (hτ : ∀ (n : ℕ) (E : Type (max u v)) (e : E),
      ((τ (n + 1)).app E).hom (MvPolynomial.X e) =
        (MvPolynomial.X (((τ n).app E).hom (MvPolynomial.X e)) : MvPolynomial
          (((polynomialComonad.{u, v} A).toFunctor.iterate (n + 1)).obj
            ((free.{u, v} A).obj E)) A))
    (n : ℕ) :
    τ n ≫ Functor.whiskerLeft (free.{u, v} A)
      (Godement.degeneracy (polynomialComonad.{u, v} A).δ n 0) = τ (n + 1) := by
  refine NatTrans.ext (funext fun E => CommAlgCat.hom_ext
    (MvPolynomial.algHom_ext fun e => ?_))
  obtain ⟨y, hy⟩ : ∃ y, ((τ n).app E).hom (MvPolynomial.X e) =
      (MvPolynomial.X y : MvPolynomial
        (((polynomialComonad.{u, v} A).toFunctor.iterate n).obj ((free.{u, v} A).obj E)) A) := by
    cases n with
    | zero => exact ⟨MvPolynomial.X e, hτ₀ E e⟩
    | succ m => exact ⟨((τ m).app E).hom (MvPolynomial.X e), hτ m E e⟩
  rw [NatTrans.comp_app, CommAlgCat.hom_comp, AlgHom.comp_apply, Functor.whiskerLeft_app,
    hτ n E e, hy]
  exact degeneracy_zero_hom_X A _ n y

/-- **Stacks 08NE**.
Let `A` be a ring, let `Alg_A` be the category of commutative `A`-algebras, let
`U : Sets → Alg_A` be the polynomial-algebra functor `E ↦ A[E]` (`MvPolynomial E A`) and `V` the
forgetful functor, and let `X` be the standard resolution of the comonad `Y = U ∘ V`
(Stacks 08NA): the augmented simplicial object of `Fun(Alg_A, Alg_A)` with terms the iterates
`Xₙ = Y^{n+1}`, so that `Xₙ(B) = A[A[⋯[B]⋯]]` with `n + 1` brackets, faces `Godement.face`,
degeneracies `Godement.degeneracy`, point `𝟭` and augmentation `d⁰₀` (for instance
`CommAlgCat.standardEndofunctor`). Then, by Lemma 08ND:

* the whiskered augmentation `1_V ⋆ ε : V ∘ X ⟶ V` is a homotopy equivalence whose homotopy
  inverse is, in degree `n`, the map of sets `b ↦ [⋯[b]⋯]` (`n + 1` brackets), given by the family
  `ρ`; evaluated at a commutative `A`-algebra `B`, this is the homotopy equivalence of underlying
  simplicial sets of `X(B) ⟶ B`, for any ring map `A → B`;
* the whiskered augmentation `ε ⋆ 1_U : X ∘ U ⟶ U` is a homotopy equivalence of simplicial objects
  of `Fun(Sets, Alg_A)` whose homotopy inverse is, in degree `n`, the `A`-algebra map
  `∑ a_{e₁,…,e_p} [e₁]⋯[e_p] ↦ ∑ a_{e₁,…,e_p} [⋯[e₁]⋯]⋯[⋯[e_p]⋯]`, sending a variable `[e]` of
  `A[E]` to `[⋯[e]⋯]` (`n + 2` brackets) in `Xₙ(A[E])`, given by the family `τ`; evaluated at a
  set `E`, this is the homotopy equivalence of simplicial rings `X(A[E]) ⟶ A[E]`.

In both clauses both composites with the inverse are homotopic to the identity, homotopic meaning
related by the equivalence relation generated by the existence of a simplicial homotopy. -/
@[stacks 08NE "both claims, for the polynomial-algebra adjunction on commutative algebras, with
the degree-`n` inverses `b ↦ [⋯[b]⋯]` and `[e] ↦ [⋯[e]⋯]`"]
theorem exists_homotopyInverse_whiskered_standardResolution (A : Type u) [CommRing A]
    (X : SimplicialObject.Augmented (CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} A))
    (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = (polynomialComonad.{u, v} A).toFunctor.iterate (n + 1))
    (hX : X.right = 𝟭 (CommAlgCat.{max u v} A))
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)), X.left.δ j =
      eqToHom (h (n + 1)) ≫ Godement.face (polynomialComonad.{u, v} A).ε (n + 1) j ≫
        eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)), X.left.σ j =
      eqToHom (h n) ≫ Godement.degeneracy (polynomialComonad.{u, v} A).δ n j ≫
        eqToHom (h (n + 1)).symm)
    (hε : X.hom.app (op ⦋0⦌) =
      eqToHom (h 0) ≫ Godement.face (polynomialComonad.{u, v} A).ε 0 0 ≫ eqToHom hX.symm)
    (a : X.left ⋙ (Functor.whiskeringRight (CommAlgCat.{max u v} A) (CommAlgCat.{max u v} A)
        (Type (max u v))).obj (forget (CommAlgCat.{max u v} A)) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ forget (CommAlgCat.{max u v} A)))
    (ha : ∀ n : SimplexCategoryᵒᵖ,
      a.app n = Functor.whiskerRight (X.hom.app n) (forget (CommAlgCat.{max u v} A)))
    (b : X.left ⋙ (Functor.whiskeringLeft (Type (max u v)) (CommAlgCat.{max u v} A)
        (CommAlgCat.{max u v} A)).obj (free.{u, v} A) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (free.{u, v} A ⋙ X.right))
    (hb : ∀ n : SimplexCategoryᵒᵖ, b.app n = Functor.whiskerLeft (free.{u, v} A) (X.hom.app n))
    (ρ : ∀ n : ℕ, forget (CommAlgCat.{max u v} A) ⟶
      (polynomialComonad.{u, v} A).toFunctor.iterate (n + 1) ⋙ forget (CommAlgCat.{max u v} A))
    (hρ₀ : ∀ (B : CommAlgCat.{max u v} A) (x : B),
      (ρ 0).app B x = (MvPolynomial.X x : MvPolynomial B A))
    (hρ : ∀ (n : ℕ) (B : CommAlgCat.{max u v} A) (x : B),
      (ρ (n + 1)).app B x = (MvPolynomial.X ((ρ n).app B x) :
        MvPolynomial (((polynomialComonad.{u, v} A).toFunctor.iterate (n + 1)).obj B) A))
    (τ : ∀ n : ℕ, free.{u, v} A ⟶
      free.{u, v} A ⋙ (polynomialComonad.{u, v} A).toFunctor.iterate (n + 1))
    (hτ₀ : ∀ (E : Type (max u v)) (e : E),
      ((τ 0).app E).hom (MvPolynomial.X e) =
        (MvPolynomial.X (MvPolynomial.X e : MvPolynomial E A) :
          MvPolynomial (MvPolynomial E A) A))
    (hτ : ∀ (n : ℕ) (E : Type (max u v)) (e : E),
      ((τ (n + 1)).app E).hom (MvPolynomial.X e) =
        (MvPolynomial.X (((τ n).app E).hom (MvPolynomial.X e)) : MvPolynomial
          (((polynomialComonad.{u, v} A).toFunctor.iterate (n + 1)).obj
            ((free.{u, v} A).obj E)) A)) :
    (∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (X.right ⋙ forget (CommAlgCat.{max u v} A)) ⟶
        X.left ⋙ (Functor.whiskeringRight (CommAlgCat.{max u v} A) (CommAlgCat.{max u v} A)
          (Type (max u v))).obj (forget (CommAlgCat.{max u v} A)),
      (∀ n : ℕ, r.app (op ⦋n⦌) =
        eqToHom (congrArg (fun F => F ⋙ forget (CommAlgCat.{max u v} A)) hX) ≫ ρ n ≫
          eqToHom (congrArg (fun F => F ⋙ forget (CommAlgCat.{max u v} A)) (h n)).symm) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (a ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ a) (𝟙 _)) ∧
    (∃ r : (Functor.const SimplexCategoryᵒᵖ).obj (free.{u, v} A ⋙ X.right) ⟶
        X.left ⋙ (Functor.whiskeringLeft (Type (max u v)) (CommAlgCat.{max u v} A)
          (CommAlgCat.{max u v} A)).obj (free.{u, v} A),
      (∀ n : ℕ, r.app (op ⦋n⦌) =
        eqToHom (congrArg (fun F => free.{u, v} A ⋙ F) hX) ≫ τ n ≫
          eqToHom (congrArg (fun F => free.{u, v} A ⋙ F) (h n)).symm) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (b ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun f g => Nonempty (SimplicialObject.Homotopy f g)) (r ≫ b) (𝟙 _)) :=
  ⟨Godement.exists_homotopyInverse_whiskerRight_eq _ _ _ X h hX hδ hσ hε a ha ρ
      (iteratedX_comp_face_zero A ρ hρ₀) (iteratedX_comp_degeneracy_zero A ρ hρ₀ hρ),
    Godement.exists_homotopyInverse_whiskerLeft_eq _ _ _ X h hX hδ hσ hε b hb τ
      (freeIteratedX_comp_face_zero A τ hτ₀) (freeIteratedX_comp_degeneracy_zero A τ hτ₀ hτ)⟩

end CommAlgCat

end

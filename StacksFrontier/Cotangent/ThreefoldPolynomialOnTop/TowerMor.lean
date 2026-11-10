module

public import StacksFrontier.Cotangent.ThreefoldPolynomialOnTop.Tower

/-!
# Morphisms out of the towers of a resolution

For the cosimplicial object `U_•` of towers `(P_n → B, P_n[E] → C)` of the threefold site
`C_{C/B/A}` of Tag 08QT, this file writes out the simplicial set `Mor_{C_{C/B/A}}(U_•, W)` and
proves that it is homotopy equivalent to a point for every object `W`: the point-resolution
hypothesis of the criterion of Tag 08Q9. A morphism of towers out of a presented tower
`(A[S] → B, A[S][T] → C)` is a function on `S` together with a function on `T`, and the two
layers of a lifting problem are filled separately.

## Main definitions

* `CommAlgCat.towerMor`: the simplicial set `Mor_{C_{C/B/A}}(U_•, W)`, written out, together
  with `CommAlgCat.towerMorIso` identifying it with the simplicial set of the criterion.

## Main results

* `CommAlgCat.trivialKanFibrations_towerMor` and
  `CommAlgCat.exists_homotopyEquivalences_towerMor`: each `Mor_{C_{C/B/A}}(U_•, W)` is homotopy
  equivalent to a singleton.

## References

* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CommAlgCat

/-! ### Morphisms of towers out of a presented tower -/

section Criterion

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)
  (hP : ∀ m, IsPolynomialAlgebra A (P.obj m))

/-- The simplicial set `Mor_{C_{C/B/A}}(U_•, W)` of morphisms of the site from the cosimplicial
object of the towers of a resolution to an object `W`, written out: its sections in degree `n`
are the morphisms of towers from `W` to `(P_n → B, P_n[E] → C)`. -/
def towerMor (W : polynomialTowerSite A B C) : SSet.{u} where
  obj m := W.unop ⟶ (towerSimplicialOfResolution ε eqv hP).obj m
  map f := ↾fun g => g ≫ (towerSimplicialOfResolution ε eqv hP).map f
  map_id m := ConcreteCategory.ext_apply fun g => by
    change g ≫ (towerSimplicialOfResolution ε eqv hP).map (𝟙 m) = g
    rw [(towerSimplicialOfResolution ε eqv hP).map_id, Category.comp_id]
  map_comp f f' := ConcreteCategory.ext_apply fun g => by
    change g ≫ (towerSimplicialOfResolution ε eqv hP).map (f ≫ f') =
      (g ≫ (towerSimplicialOfResolution ε eqv hP).map f) ≫
        (towerSimplicialOfResolution ε eqv hP).map f'
    rw [(towerSimplicialOfResolution ε eqv hP).map_comp, Category.assoc]

/-- `CommAlgCat.towerMor` is the simplicial set the criterion of Tag 08Q9 is about: the Yoneda
functor at `W` evaluated on the cosimplicial object of the towers of a resolution. The two
differ only by the `Opposite` wrapping of the morphisms of an opposite category. -/
def towerMorIso (W : polynomialTowerSite A B C) :
    towerMor ε eqv hP W ≅ (towerCosimplicialObject ε eqv hP).op ⋙ yoneda.obj W where
  hom := { app := fun _ => ↾fun g => Quiver.Hom.op g, naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => ↾fun g => Quiver.Hom.unop g, naturality := fun _ _ _ => rfl }
  hom_inv_id := NatTrans.ext (funext fun _ => ConcreteCategory.ext_apply fun _ => rfl)
  inv_hom_id := NatTrans.ext (funext fun _ => ConcreteCategory.ext_apply fun _ => rfl)

variable {W : polynomialTowerSite A B C} {S T : Type u}
  (e₁ : MvPolynomial S A ≃ₐ[A] ↑(towerLeftAlgebra W.unop.obj))
  (e₂ : MvPolynomial T ↑(towerLeftAlgebra W.unop.obj)
    ≃ₐ[↑(towerLeftAlgebra W.unop.obj)] ↑(towerRightAlgebra W.unop.obj))

/-- The `A`-algebra map `P → P_n` determined by the images of the variables of a presentation
`P = A[S]` of the first layer of a tower. -/
abbrev towerLeftHomOfGenerators (m : SimplexCategoryᵒᵖ) (a : S → ↑(P.obj m)) :
    ↑(towerLeftAlgebra W.unop.obj) →ₐ[A] ↑(P.obj m) :=
  (MvPolynomial.aeval a).comp e₁.symm.toAlgHom

/-- The `A`-algebra map `Q → P_n[E]` determined by a map `P → P_n` and the images of the
variables of a presentation `Q = P[T]`: on `P` it is the inclusion of the coefficients. -/
def towerRightHomOfGenerators (m : SimplexCategoryᵒᵖ)
    (φ : ↑(towerLeftAlgebra W.unop.obj) →ₐ[A] ↑(P.obj m))
    (b : T → MvPolynomial E ↑(P.obj m)) :
    ↑(towerRightAlgebra W.unop.obj) →ₐ[A] MvPolynomial E ↑(P.obj m) :=
  (MvPolynomial.aevalTower
      ((IsScalarTower.toAlgHom A (↑(P.obj m)) (MvPolynomial E ↑(P.obj m))).comp φ) b).comp
    (AlgEquiv.restrictScalars A e₂.symm).toAlgHom

/-- On the image of a coefficient, `CommAlgCat.towerRightHomOfGenerators` is the given map
`P → P_n` followed by the inclusion of the coefficients. -/
lemma towerRightHomOfGenerators_apply_C (m : SimplexCategoryᵒᵖ)
    (φ : ↑(towerLeftAlgebra W.unop.obj) →ₐ[A] ↑(P.obj m))
    (b : T → MvPolynomial E ↑(P.obj m)) (p : ↑(towerLeftAlgebra W.unop.obj)) :
    towerRightHomOfGenerators e₂ m φ b (e₂ (MvPolynomial.C p)) = MvPolynomial.C (φ p) := by
  change MvPolynomial.aevalTower _ b
    ((AlgEquiv.restrictScalars A e₂.symm) (e₂ (MvPolynomial.C p))) = _
  rw [show (AlgEquiv.restrictScalars A e₂.symm) (e₂ (MvPolynomial.C p)) = MvPolynomial.C p from
    e₂.symm_apply_apply _]
  exact MvPolynomial.aevalTower_C _ _ p

/-- On the image of a variable, `CommAlgCat.towerRightHomOfGenerators` is the prescribed
value. -/
lemma towerRightHomOfGenerators_apply_X (m : SimplexCategoryᵒᵖ)
    (φ : ↑(towerLeftAlgebra W.unop.obj) →ₐ[A] ↑(P.obj m))
    (b : T → MvPolynomial E ↑(P.obj m)) (t : T) :
    towerRightHomOfGenerators e₂ m φ b (e₂ (MvPolynomial.X t)) = b t := by
  change MvPolynomial.aevalTower _ b
    ((AlgEquiv.restrictScalars A e₂.symm) (e₂ (MvPolynomial.X t))) = _
  rw [show (AlgEquiv.restrictScalars A e₂.symm) (e₂ (MvPolynomial.X t)) = MvPolynomial.X t from
    e₂.symm_apply_apply _]
  exact MvPolynomial.aevalTower_X _ _ t

/-- The image of a coefficient is the image of the map `P → Q` of the tower. -/
lemma e₂_C_eq (p : ↑(towerLeftAlgebra W.unop.obj)) :
    e₂ (MvPolynomial.C p) = (CommAlgCat.Hom.hom W.unop.obj.hom) p :=
  e₂.commutes p

/-- A morphism of towers from `W = (P → B, Q → C)` to the tower `(P_n → B, P_n[E] → C)` of a
degree of a resolution, determined by presentations `P = A[S]` and `Q = P[T]` together with the
images of the variables: a map `a : S → P_n` whose values have the prescribed augmentations in
`B`, and a map `b : T → P_n[E]` whose values have the prescribed augmentations in `C`. -/
def towerHomOfGenerators (m : SimplexCategoryᵒᵖ)
    (a : S → ↑(P.obj m)) (b : T → MvPolynomial E ↑(P.obj m))
    (ha : ∀ s, (CommAlgCat.Hom.hom (ε.app m)) (a s) =
      (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hb : ∀ t, towerVariablesAugmentation ε eqv m (b t) =
      (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t))) :
    W.unop ⟶ (towerSimplicialOfResolution ε eqv hP).obj m :=
  ObjectProperty.homMk
    { left := homOfGenerators (Y := ((towerSimplicialOfResolution ε eqv hP).obj m).obj.left)
        e₁ a ha
      right := Over.homMk (CommAlgCat.ofHom (towerRightHomOfGenerators e₂ m
          (towerLeftHomOfGenerators e₁ m a) b)) (by
        apply CommAlgCat.hom_ext
        have hβ : ∀ p, (CommAlgCat.Hom.hom (ε.app m))
            ((towerLeftHomOfGenerators e₁ m a) p) =
              (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) p := fun p => by
          have h := ConcreteCategory.congr_hom
            (aeval_comp_symm_comp_hom (Y := ((towerSimplicialOfResolution ε eqv hP).obj m).obj.left)
              e₁ a ha) p
          rw [CategoryTheory.comp_apply] at h
          exact h
        have key : ((towerVariablesAugmentation ε eqv m).comp
              (towerRightHomOfGenerators e₂ m (towerLeftHomOfGenerators e₁ m a) b)).comp
            (AlgEquiv.restrictScalars A e₂).toAlgHom =
          (CommAlgCat.Hom.hom W.unop.obj.right.hom).comp
            (AlgEquiv.restrictScalars A e₂).toAlgHom := by
          refine MvPolynomial.algHom_ext' ?_ ?_
          · refine AlgHom.ext fun p => ?_
            change towerVariablesAugmentation ε eqv m
                (towerRightHomOfGenerators e₂ m (towerLeftHomOfGenerators e₁ m a) b
                  (e₂ (MvPolynomial.C p))) =
              (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.C p))
            rw [towerRightHomOfGenerators_apply_C, towerVariablesAugmentation_C, e₂_C_eq,
              towerRight_hom_towerMap_apply W.unop p, hβ]
          · intro t
            change towerVariablesAugmentation ε eqv m
                (towerRightHomOfGenerators e₂ m (towerLeftHomOfGenerators e₁ m a) b
                  (e₂ (MvPolynomial.X t))) =
              (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t))
            rw [towerRightHomOfGenerators_apply_X]
            exact hb t
        refine AlgHom.ext fun q => ?_
        obtain ⟨r, rfl⟩ := e₂.surjective q
        exact AlgHom.congr_fun key r)
      w := by
        apply CommAlgCat.hom_ext
        refine AlgHom.ext fun p => ?_
        change MvPolynomial.C ((towerLeftHomOfGenerators e₁ m a) p) =
          towerRightHomOfGenerators e₂ m (towerLeftHomOfGenerators e₁ m a) b
            ((CommAlgCat.Hom.hom W.unop.obj.hom) p)
        rw [← e₂_C_eq e₂ p, towerRightHomOfGenerators_apply_C] }

/-- `CommAlgCat.towerHomOfGenerators` sends the variable `X_s` of the first presentation to the
prescribed value. -/
lemma towerHomOfGenerators_left (m : SimplexCategoryᵒᵖ)
    (a : S → ↑(P.obj m)) (b : T → MvPolynomial E ↑(P.obj m))
    (ha : ∀ s, (CommAlgCat.Hom.hom (ε.app m)) (a s) =
      (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hb : ∀ t, towerVariablesAugmentation ε eqv m (b t) =
      (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t))) (s : S) :
    (CommAlgCat.Hom.hom
        (towerHomOfGenerators ε eqv hP e₁ e₂ m a b ha hb).hom.left.hom.left)
      (e₁ (MvPolynomial.X s)) = a s :=
  homOfGenerators_hom_left_apply (Y := ((towerSimplicialOfResolution ε eqv hP).obj m).obj.left)
    e₁ a ha s

/-- `CommAlgCat.towerHomOfGenerators` sends the variable `X_t` of the second presentation to the
prescribed value. -/
lemma towerHomOfGenerators_right (m : SimplexCategoryᵒᵖ)
    (a : S → ↑(P.obj m)) (b : T → MvPolynomial E ↑(P.obj m))
    (ha : ∀ s, (CommAlgCat.Hom.hom (ε.app m)) (a s) =
      (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hb : ∀ t, towerVariablesAugmentation ε eqv m (b t) =
      (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t))) (t : T) :
    (CommAlgCat.Hom.hom
        (towerHomOfGenerators ε eqv hP e₁ e₂ m a b ha hb).hom.right.left)
      (e₂ (MvPolynomial.X t)) = b t :=
  towerRightHomOfGenerators_apply_X e₂ m (towerLeftHomOfGenerators e₁ m a) b t

/-- **Two morphisms of towers from `W` to the tower of a degree of a resolution agreeing on the
variables of the two presentations are equal.** On the coefficients of the second layer both are
determined by the first layer, by the commutativity of the square of a morphism of towers. -/
lemma towerHom_ext_of_generators (m : SimplexCategoryᵒᵖ)
    {f₁ f₂ : W.unop ⟶ (towerSimplicialOfResolution ε eqv hP).obj m}
    (h₁ : ∀ s, (CommAlgCat.Hom.hom f₁.hom.left.hom.left) (e₁ (MvPolynomial.X s)) =
      (CommAlgCat.Hom.hom f₂.hom.left.hom.left) (e₁ (MvPolynomial.X s)))
    (h₂ : ∀ t, (CommAlgCat.Hom.hom f₁.hom.right.left) (e₂ (MvPolynomial.X t)) =
      (CommAlgCat.Hom.hom f₂.hom.right.left) (e₂ (MvPolynomial.X t))) :
    f₁ = f₂ := by
  have hleft : f₁.hom.left = f₂.hom.left := hom_ext_of_generators e₁ h₁
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · exact hleft
  · apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    have key : (CommAlgCat.Hom.hom f₁.hom.right.left).comp
          (AlgEquiv.restrictScalars A e₂).toAlgHom =
        (CommAlgCat.Hom.hom f₂.hom.right.left).comp
          (AlgEquiv.restrictScalars A e₂).toAlgHom := by
      refine MvPolynomial.algHom_ext' ?_ ?_
      · refine AlgHom.ext fun p => ?_
        change (CommAlgCat.Hom.hom f₁.hom.right.left) (e₂ (MvPolynomial.C p)) =
          (CommAlgCat.Hom.hom f₂.hom.right.left) (e₂ (MvPolynomial.C p))
        rw [e₂_C_eq]
        have hw1 := ConcreteCategory.congr_hom f₁.hom.w p
        have hw2 := ConcreteCategory.congr_hom f₂.hom.w p
        rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hw1 hw2
        refine (hw1.symm.trans ?_).trans hw2
        rw [hleft]
      · intro t
        exact h₂ t
    refine AlgHom.ext fun q => ?_
    obtain ⟨r, rfl⟩ := e₂.surjective q
    exact AlgHom.congr_fun key r

/-- The underlying map of the first layer of a composite of morphisms of towers. -/
lemma towerComp_hom_left_apply {X Y Z : PolynomialTower A B C} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (p : ↑(towerLeftAlgebra X.obj)) :
    (CommAlgCat.Hom.hom (φ ≫ ψ).hom.left.hom.left) p =
      (CommAlgCat.Hom.hom ψ.hom.left.hom.left)
        ((CommAlgCat.Hom.hom φ.hom.left.hom.left) p) :=
  rfl

/-- The underlying map of the second layer of a composite of morphisms of towers. -/
lemma towerComp_hom_right_apply {X Y Z : PolynomialTower A B C} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (q : ↑(towerRightAlgebra X.obj)) :
    (CommAlgCat.Hom.hom (φ ≫ ψ).hom.right.left) q =
      (CommAlgCat.Hom.hom ψ.hom.right.left) ((CommAlgCat.Hom.hom φ.hom.right.left) q) :=
  rfl

/-- The first layer of a simplicial operator of the towers of a resolution is the operator of
`P_•`. -/
lemma towerSimplicialOfResolution_map_left {m m' : SimplexCategoryᵒᵖ} (g : m ⟶ m') :
    ((towerSimplicialOfResolution ε eqv hP).map g).hom.left.hom.left = P.map g := rfl

/-- The second layer of a simplicial operator of the towers of a resolution acts on the
coefficients. -/
lemma towerSimplicialOfResolution_map_right {m m' : SimplexCategoryᵒᵖ} (g : m ⟶ m') :
    ((towerSimplicialOfResolution ε eqv hP).map g).hom.right.left =
      (mvPolynomialFunctor A E).map (P.map g) := rfl

/-- The morphism of towers `W ⟶ (P_n → B, P_n[E] → C)` determined, in a single degree, by
families of maps out of a simplicial set indexed by the variables of the two presentations of
`W`, with constant augmentations. -/
def towerMorOfFamilyApp {X : SSet.{u}}
    (La : S → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (Lb : T → (X ⟶ mvPolynomialSSet A E P))
    (hLa : ∀ (s : S) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      (CommAlgCat.Hom.hom (ε.app m)) ((La s).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hLb : ∀ (t : T) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      towerVariablesAugmentation ε eqv m ((Lb t).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) :
    W.unop ⟶ (towerSimplicialOfResolution ε eqv hP).obj m :=
  towerHomOfGenerators ε eqv hP e₁ e₂ m (fun s => (La s).app m z) (fun t => (Lb t).app m z)
    (fun s => hLa s m z) (fun t => hLb t m z)

/-- `CommAlgCat.towerMorOfFamilyApp` sends the variable `X_s` of the first presentation to the
value of the corresponding member of the first family. -/
lemma towerMorOfFamilyApp_left {X : SSet.{u}}
    (La : S → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (Lb : T → (X ⟶ mvPolynomialSSet A E P))
    (hLa : ∀ (s : S) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      (CommAlgCat.Hom.hom (ε.app m)) ((La s).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hLb : ∀ (t : T) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      towerVariablesAugmentation ε eqv m ((Lb t).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) (s : S) :
    (CommAlgCat.Hom.hom
        (towerMorOfFamilyApp ε eqv hP e₁ e₂ La Lb hLa hLb m z).hom.left.hom.left)
      (e₁ (MvPolynomial.X s)) = (La s).app m z :=
  towerHomOfGenerators_left ε eqv hP e₁ e₂ m _ _ _ _ s

/-- `CommAlgCat.towerMorOfFamilyApp` sends the variable `X_t` of the second presentation to the
value of the corresponding member of the second family. -/
lemma towerMorOfFamilyApp_right {X : SSet.{u}}
    (La : S → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (Lb : T → (X ⟶ mvPolynomialSSet A E P))
    (hLa : ∀ (s : S) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      (CommAlgCat.Hom.hom (ε.app m)) ((La s).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hLb : ∀ (t : T) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      towerVariablesAugmentation ε eqv m ((Lb t).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) (t : T) :
    (CommAlgCat.Hom.hom
        (towerMorOfFamilyApp ε eqv hP e₁ e₂ La Lb hLa hLb m z).hom.right.left)
      (e₂ (MvPolynomial.X t)) = (Lb t).app m z :=
  towerHomOfGenerators_right ε eqv hP e₁ e₂ m _ _ _ _ t

/-- **Families of maps into `P_•` and into `P_•[E]`, indexed by the variables of presentations
`P = A[S]` and `Q = P[T]` of an object of the site and with constant augmentations, assemble
into a map into `Mor_{C_{C/B/A}}(U_•, W)`.** -/
def towerMorOfFamily {X : SSet.{u}}
    (La : S → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (Lb : T → (X ⟶ mvPolynomialSSet A E P))
    (hLa : ∀ (s : S) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      (CommAlgCat.Hom.hom (ε.app m)) ((La s).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hLb : ∀ (t : T) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      towerVariablesAugmentation ε eqv m ((Lb t).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t))) :
    X ⟶ towerMor ε eqv hP W where
  app m := ↾fun z => towerMorOfFamilyApp ε eqv hP e₁ e₂ La Lb hLa hLb m z
  naturality m m' g := ConcreteCategory.ext_apply fun z => by
    change towerMorOfFamilyApp ε eqv hP e₁ e₂ La Lb hLa hLb m' (X.map g z) =
      towerMorOfFamilyApp ε eqv hP e₁ e₂ La Lb hLa hLb m z ≫
        (towerSimplicialOfResolution ε eqv hP).map g
    refine towerHom_ext_of_generators ε eqv hP e₁ e₂ m' (fun s => ?_) (fun t => ?_)
    · rw [towerMorOfFamilyApp_left, towerComp_hom_left_apply, towerMorOfFamilyApp_left,
        towerSimplicialOfResolution_map_left]
      exact ConcreteCategory.congr_hom ((La s).naturality g) z
    · rw [towerMorOfFamilyApp_right, towerComp_hom_right_apply, towerMorOfFamilyApp_right,
        towerSimplicialOfResolution_map_right]
      exact ConcreteCategory.congr_hom ((Lb t).naturality g) z

/-- `CommAlgCat.towerMorOfFamily` sends the variable `X_s` of the first presentation to the
value of the corresponding member of the first family. -/
lemma towerMorOfFamily_app_left {X : SSet.{u}}
    (La : S → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (Lb : T → (X ⟶ mvPolynomialSSet A E P))
    (hLa : ∀ (s : S) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      (CommAlgCat.Hom.hom (ε.app m)) ((La s).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hLb : ∀ (t : T) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      towerVariablesAugmentation ε eqv m ((Lb t).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) (s : S) :
    (CommAlgCat.Hom.hom
        ((towerMorOfFamily ε eqv hP e₁ e₂ La Lb hLa hLb).app m z).hom.left.hom.left)
      (e₁ (MvPolynomial.X s)) = (La s).app m z :=
  towerMorOfFamilyApp_left ε eqv hP e₁ e₂ La Lb hLa hLb m z s

/-- `CommAlgCat.towerMorOfFamily` sends the variable `X_t` of the second presentation to the
value of the corresponding member of the second family. -/
lemma towerMorOfFamily_app_right {X : SSet.{u}}
    (La : S → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (Lb : T → (X ⟶ mvPolynomialSSet A E P))
    (hLa : ∀ (s : S) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      (CommAlgCat.Hom.hom (ε.app m)) ((La s).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)))
    (hLb : ∀ (t : T) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      towerVariablesAugmentation ε eqv m ((Lb t).app m z) =
        (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X t)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) (t : T) :
    (CommAlgCat.Hom.hom
        ((towerMorOfFamily ε eqv hP e₁ e₂ La Lb hLa hLb).app m z).hom.right.left)
      (e₂ (MvPolynomial.X t)) = (Lb t).app m z :=
  towerMorOfFamilyApp_right ε eqv hP e₁ e₂ La Lb hLa hLb m z t

end Criterion

/-! ### The point criterion for the tower site -/

section PointCriterion

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)
  (hP : ∀ m, IsPolynomialAlgebra A (P.obj m))

/-- A boundary `∂Δ[n] ⟶ Mor_{C_{C/B/A}}(U_•, W)` followed by a natural projection to a simplicial
set `X` with a trivial Kan fibration `p` to `Y` lifts through `p`, when `p` is constant on the
projection. -/
private lemma exists_lift_towerMor_of_trivialKanFibrations
    {W : polynomialTowerSite A B C} {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : SSet.trivialKanFibrations p) (n : ℕ) (t : (∂Δ[n] : SSet.{u}) ⟶ towerMor ε eqv hP W)
    (proj : ∀ m, (W.unop ⟶ (towerSimplicialOfResolution ε eqv hP).obj m) → X.obj m)
    (hproj : ∀ m m' (g : m ⟶ m') f,
      proj m' (f ≫ (towerSimplicialOfResolution ε eqv hP).map g) = X.map g (proj m f))
    (val : ∀ m, Y.obj m) (hval : ∀ m m' (g : m ⟶ m'), Y.map g (val m) = val m')
    (hpv : ∀ m z, p.app m (proj m (t.app m z)) = val m) :
    ∃ L : (Δ[n] : SSet.{u}) ⟶ X,
      (∀ (m : SimplexCategoryᵒᵖ) (z : (∂Δ[n] : SSet.{u}).obj m),
          L.app m (∂Δ[n].ι.app m z) = proj m (t.app m z)) ∧
        ∀ (m : SimplexCategoryᵒᵖ) (z : (Δ[n] : SSet.{u}).obj m), p.app m (L.app m z) = val m := by
  let top : (∂Δ[n] : SSet.{u}) ⟶ X :=
    { app := fun m => ↾fun z => proj m (t.app m z)
      naturality := fun m m' g => ConcreteCategory.ext_apply fun z => by
        exact (congrArg (proj m') (ConcreteCategory.congr_hom (t.naturality g) z)).trans
          (hproj m m' g _) }
  let bot : (Δ[n] : SSet.{u}) ⟶ Y :=
    { app := fun m => ↾fun _ => val m
      naturality := fun m m' g => ConcreteCategory.ext_apply fun _ => (hval m m' g).symm }
  have hsq : CommSq top ∂Δ[n].ι p bot :=
    ⟨NatTrans.ext (funext fun m => ConcreteCategory.ext_apply fun z => hpv m z)⟩
  obtain ⟨⟨L, hL₁, hL₂⟩⟩ := (((SSet.trivialKanFibrations_iff _).mp hp n).sq_hasLift hsq).exists_lift
  exact ⟨L, fun m z => ConcreteCategory.congr_hom (NatTrans.congr_app hL₁ m) z,
    fun m z => ConcreteCategory.congr_hom (NatTrans.congr_app hL₂ m) z⟩

/-- **The fibre of `P_• → B` over `β(X_s)` fills a boundary.** The `s`-th coordinate of a map
`∂Δ[n] ⟶ Mor_{C_{C/B/A}}(U_•, W)` is a map `∂Δ[n] ⟶ P_•` whose composite with `ε` is constant at
the augmentation of `X_s`; it lands in that fibre, and `ε` fills it. -/
lemma exists_lift_towerMor_left
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    {W : polynomialTowerSite A B C} {S : Type u}
    (e₁ : MvPolynomial S A ≃ₐ[A] ↑(towerLeftAlgebra W.unop.obj)) (n : ℕ)
    (t : (∂Δ[n] : SSet.{u}) ⟶ towerMor ε eqv hP W) (s : S) :
    ∃ L : (Δ[n] : SSet.{u}) ⟶ P ⋙ forget (CommAlgCat.{u} A),
      (∀ (m : SimplexCategoryᵒᵖ) (z : (∂Δ[n] : SSet.{u}).obj m),
          L.app m (∂Δ[n].ι.app m z) =
            (CommAlgCat.Hom.hom (t.app m z).hom.left.hom.left) (e₁ (MvPolynomial.X s))) ∧
        ∀ (m : SimplexCategoryᵒᵖ) (z : (Δ[n] : SSet.{u}).obj m),
          (CommAlgCat.Hom.hom (ε.app m)) (L.app m z) =
            (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom) (e₁ (MvPolynomial.X s)) := by
  refine exists_lift_towerMor_of_trivialKanFibrations ε eqv hP hε n t
    (fun _ f => (CommAlgCat.Hom.hom f.hom.left.hom.left) (e₁ (MvPolynomial.X s)))
    (fun _ _ _ _ => rfl) (fun _ => (CommAlgCat.Hom.hom W.unop.obj.left.obj.hom)
      (e₁ (MvPolynomial.X s))) (fun _ _ _ => rfl) fun m z => ?_
  exact ConcreteCategory.congr_hom (t.app m z).hom.left.hom.w (e₁ (MvPolynomial.X s))

/-- **The fibre of `P_•[E] → C` over `γ(X_t)` fills a boundary.** The `t`-th coordinate of a map
`∂Δ[n] ⟶ Mor_{C_{C/B/A}}(U_•, W)` is a map `∂Δ[n] ⟶ P_•[E]` whose composite with the
augmentation is constant at the augmentation of `X_t`; it lands in that fibre, and the
augmentation — a trivial Kan fibration — fills it. -/
lemma exists_lift_towerMor_right
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    {W : polynomialTowerSite A B C} {T : Type u}
    (e₂ : MvPolynomial T ↑(towerLeftAlgebra W.unop.obj)
      ≃ₐ[↑(towerLeftAlgebra W.unop.obj)] ↑(towerRightAlgebra W.unop.obj)) (n : ℕ)
    (t : (∂Δ[n] : SSet.{u}) ⟶ towerMor ε eqv hP W) (tv : T) :
    ∃ L : (Δ[n] : SSet.{u}) ⟶ mvPolynomialSSet A E P,
      (∀ (m : SimplexCategoryᵒᵖ) (z : (∂Δ[n] : SSet.{u}).obj m),
          L.app m (∂Δ[n].ι.app m z) =
            (CommAlgCat.Hom.hom (t.app m z).hom.right.left) (e₂ (MvPolynomial.X tv))) ∧
        ∀ (m : SimplexCategoryᵒᵖ) (z : (Δ[n] : SSet.{u}).obj m),
          towerVariablesAugmentation ε eqv m (L.app m z) =
            (CommAlgCat.Hom.hom W.unop.obj.right.hom) (e₂ (MvPolynomial.X tv)) := by
  refine exists_lift_towerMor_of_trivialKanFibrations ε eqv hP
    (trivialKanFibrations_towerVariablesAugmentationNatTrans ε eqv hε) n t
    (fun _ f => (CommAlgCat.Hom.hom f.hom.right.left) (e₂ (MvPolynomial.X tv)))
    (fun _ _ _ _ => rfl) (fun _ => (CommAlgCat.Hom.hom W.unop.obj.right.hom)
      (e₂ (MvPolynomial.X tv))) (fun _ _ _ => rfl) fun m z => ?_
  exact ConcreteCategory.congr_hom (t.app m z).hom.right.w (e₂ (MvPolynomial.X tv))

/-- **Stacks 08QV, the point criterion.** Let `ε : P_• ⟶ B` be a resolution of `B` over `A` and
let `C = B[E]`. Then for every object `W = (P → B, Q → C)` of the site `C_{C/B/A}` the morphism
from the simplicial set `Mor_{C_{C/B/A}}(U_•, W)` to the constant simplicial set on a singleton
— there is only one — is a trivial Kan fibration, for `U_•` the cosimplicial object of the
towers `(P_n → B, P_n[E] → C)`.

This is the source's product decomposition into the fibres of `P_• → B` over the `β(s)` and of
`P_•[E] → C` over the `γ(t)`, carried out on a lifting problem: writing `P = A[S]` and
`Q = P[T]`, a map `∂Δ[n] ⟶ Mor(U_•, W)` is a family of maps `∂Δ[n] ⟶ P_•` and
`∂Δ[n] ⟶ P_•[E]` with constant augmentations, each of which the corresponding trivial Kan
fibration fills, and the fillers assemble. -/
theorem trivialKanFibrations_towerMor
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (W : polynomialTowerSite A B C)
    (f : towerMor ε eqv hP W ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}) :
    SSet.trivialKanFibrations f := by
  classical
  obtain ⟨S, ⟨e₁⟩⟩ := W.unop.obj.left.property
  obtain ⟨T, ⟨e₂⟩⟩ := W.unop.property.1
  rw [SSet.trivialKanFibrations_iff]
  intro n
  refine ⟨fun {t u} sq ↦ ?_⟩
  choose La hLa₁ hLa₂ using exists_lift_towerMor_left ε eqv hP hε e₁ n t
  choose Lb hLb₁ hLb₂ using exists_lift_towerMor_right ε eqv hP hε e₂ n t
  refine ⟨⟨{ l := towerMorOfFamily ε eqv hP e₁ e₂ La Lb hLa₂ hLb₂
             fac_left := ?_, fac_right := hom_ext_toConstPUnit _ _ }⟩⟩
  refine NatTrans.ext (funext fun m => ConcreteCategory.ext_apply fun z => ?_)
  refine towerHom_ext_of_generators ε eqv hP e₁ e₂ m (fun s => ?_) (fun tv => ?_)
  · exact (towerMorOfFamily_app_left ε eqv hP e₁ e₂ La Lb hLa₂ hLb₂ m
      (∂Δ[n].ι.app m z) s).trans (hLa₁ s m z)
  · exact (towerMorOfFamily_app_right ε eqv hP e₁ e₂ La Lb hLa₂ hLb₂ m
      (∂Δ[n].ι.app m z) tv).trans (hLb₁ tv m z)

/-- **Stacks 08QV, the hypothesis of the criterion of Tag 08Q9.** Let `ε : P_• ⟶ B` be a
resolution of `B` over `A` and let `C = B[E]`. Then for every object `W` of the site
`C_{C/B/A}` the simplicial set `Mor_{C_{C/B/A}}(U_•, W)` is homotopy equivalent to the constant
simplicial set on a singleton, for `U_•` the cosimplicial object of the towers
`(P_n → B, P_n[E] → C)`. -/
theorem exists_homotopyEquivalences_towerMor
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (W : polynomialTowerSite A B C) :
    ∃ f : (towerCosimplicialObject ε eqv hP).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f := by
  let pt : (towerCosimplicialObject ε eqv hP).op ⋙ yoneda.obj W ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} :=
    { app := fun _ => ↾fun _ => PUnit.unit
      naturality := fun _ _ _ => rfl }
  have htriv : SSet.trivialKanFibrations pt := by
    have h := trivialKanFibrations_towerMor ε eqv hP hε W ((towerMorIso ε eqv hP W).hom ≫ pt)
    have h' := MorphismProperty.RespectsIso.precomp SSet.trivialKanFibrations
      (towerMorIso ε eqv hP W).inv ((towerMorIso ε eqv hP W).hom ≫ pt) h
    rwa [Iso.inv_hom_id_assoc] at h'
  obtain ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ := SSet.trivialKanFibrations_isHomotopyEquiv _ htriv
  exact ⟨pt, g, Relation.EqvGen.rel _ _ ⟨h₁.toSimplicialObjectHomotopy⟩,
    Relation.EqvGen.rel _ _ ⟨h₂.toSimplicialObjectHomotopy⟩⟩

end PointCriterion

end CommAlgCat

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.UnitEndomorphismValues
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence

/-!
# Matrices of functions as morphisms of free modules

On the algebraic space of a scheme `T`, the morphisms `𝒪_T^n ⟶ 𝒪_T^m` of free modules are the
`n × m` matrices with entries in `Γ(T, 𝒪_T)`, composition being matrix multiplication; and the
inverse image along a morphism of schemes `g : T' ⟶ T`, read through `g^*𝒪_T^n ≅ 𝒪_{T'}^n`, is
pullback of the entries along `g`.

## Main definitions

* `CategoryTheory.freeObj`: the free object `O^n = ⨁_{Fin n} O` on an object of a preadditive
  category.
* `CategoryTheory.Functor.freeObjIso`: an additive functor carrying `O` to `O'` carries `O^n` to
  `O'^n`.
* `AlgebraicGeometry.Space.funEnd`: the endomorphism of `𝒪_T` given by a function on `T`.
* `AlgebraicGeometry.Space.matMap`: the morphism `𝒪_T^n ⟶ 𝒪_T^m` of a matrix of functions.

## Main results

* `AlgebraicGeometry.Space.matMap_mul`, `matMap_add`, `matMap_one`, `matMap_zero`: the matrix
  calculus.
* `AlgebraicGeometry.Space.pullFreeIso_inv_map_matMap`: inverse image of a matrix is the matrix
  of pulled back entries.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]

/-- The free object `O^n = ⨁_{Fin n} O`. -/
abbrev freeObj (O : C) (n : ℕ) : C := ⨁ (fun _ : Fin n => O)

/-- The morphism of free objects with the given matrix of components. -/
abbrev freeMat (O : C) {n m : ℕ} (M : Fin n → Fin m → (O ⟶ O)) : freeObj O n ⟶ freeObj O m :=
  biproduct.matrix M

/-- The components of `CategoryTheory.freeMat`. -/
@[reassoc (attr := simp)]
theorem ι_freeMat_π (O : C) {n m : ℕ} (M : Fin n → Fin m → (O ⟶ O)) (j : Fin n) (k : Fin m) :
    biproduct.ι _ j ≫ freeMat O M ≫ biproduct.π _ k = M j k := by
  rw [biproduct.ι_matrix_assoc, biproduct.lift_π]

/-- Composition of morphisms of free objects is multiplication of their matrices. -/
theorem freeMat_comp (O : C) {n m k : ℕ} (M : Fin n → Fin m → (O ⟶ O))
    (N : Fin m → Fin k → (O ⟶ O)) :
    freeMat O M ≫ freeMat O N = freeMat O (fun j l => ∑ i, M j i ≫ N i l) := by
  ext l j
  rw [ι_freeMat_π, Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π,
    biproduct.lift_desc]

/-- The sum of morphisms of free objects has the entrywise sum as matrix. -/
theorem freeMat_add (O : C) {n m : ℕ} (M N : Fin n → Fin m → (O ⟶ O)) :
    freeMat O M + freeMat O N = freeMat O (fun j k => M j k + N j k) := by
  ext j k
  rw [ι_freeMat_π, Preadditive.add_comp, Preadditive.comp_add, ι_freeMat_π, ι_freeMat_π]

/-- The zero matrix gives the zero morphism of free objects. -/
theorem freeMat_zero (O : C) {n m : ℕ} :
    freeMat O (fun (_ : Fin n) (_ : Fin m) => (0 : O ⟶ O)) = 0 := by
  ext j k
  rw [ι_freeMat_π, zero_comp, comp_zero]

/-- The identity matrix gives the identity of `O^n`. -/
theorem freeMat_id (O : C) (n : ℕ) :
    freeMat O (fun (j k : Fin n) => if j = k then 𝟙 O else 0) = 𝟙 (freeObj O n) := by
  ext j k
  rw [ι_freeMat_π, Category.id_comp]
  by_cases h : k = j
  · subst h; simp
  · rw [ite_eq_right h, biproduct.ι_π_ne _ h]

/-- Matrices with equal entries give equal morphisms of free objects. -/
private theorem freeMat_congr (O : C) {n m : ℕ} {M N : Fin n → Fin m → (O ⟶ O)}
    (h : ∀ j k, M j k = N j k) : freeMat O M = freeMat O N :=
  congrArg (freeMat O) (funext fun j => funext (h j))

variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]

/-- **An additive functor carrying `O` to `O'` carries `O^n` to `O'^n`.** -/
def Functor.freeObjIso (F : C ⥤ D) [F.Additive] {O : C} {O' : D} (e : F.obj O ≅ O') (n : ℕ) :
    F.obj (freeObj O n) ≅ freeObj O' n :=
  F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ => e)

/-- The inverse of `CategoryTheory.Functor.freeObjIso` on the `k`-th inclusion of `O'^n` is the
image under `F` of the `k`-th inclusion of `O^n`, preceded by `e.inv`. -/
@[reassoc (attr := simp)]
theorem Functor.ι_freeObjIso_inv (F : C ⥤ D) [F.Additive] {O : C} {O' : D} (e : F.obj O ≅ O')
    (n : ℕ) (k : Fin n) :
    biproduct.ι (fun _ : Fin n => O') k ≫ (F.freeObjIso e n).inv =
      e.inv ≫ F.map (biproduct.ι (fun _ : Fin n => O) k) := by
  simp only [Functor.freeObjIso, Iso.trans_inv, biproduct.mapIso_inv, Functor.mapBiproduct_inv,
    biproduct.ι_map_assoc, biproduct.ι_desc]

/-- `CategoryTheory.Functor.freeObjIso` followed by the `k`-th projection of `O'^n` is the image
under `F` of the `k`-th projection of `O^n`, followed by `e.hom`. -/
@[reassoc (attr := simp)]
theorem Functor.freeObjIso_hom_π (F : C ⥤ D) [F.Additive] {O : C} {O' : D} (e : F.obj O ≅ O')
    (n : ℕ) (k : Fin n) :
    (F.freeObjIso e n).hom ≫ biproduct.π (fun _ : Fin n => O') k =
      F.map (biproduct.π (fun _ : Fin n => O) k) ≫ e.hom := by
  simp only [Functor.freeObjIso, Iso.trans_hom, biproduct.mapIso_hom, Functor.mapBiproduct_hom,
    Category.assoc, biproduct.map_π]
  exact biproduct.lift_π_assoc _ _ _

/-- The image of a morphism of free objects with given components, read through
`CategoryTheory.Functor.freeObjIso`, has the conjugated components. -/
theorem Functor.freeObjIso_inv_map_freeMat (F : C ⥤ D) [F.Additive] {O : C} {O' : D}
    (e : F.obj O ≅ O') {n m : ℕ} (M : Fin n → Fin m → (O ⟶ O)) :
    (F.freeObjIso e n).inv ≫ F.map (freeMat O M) ≫ (F.freeObjIso e m).hom =
      freeMat O' (fun j k => e.inv ≫ F.map (M j k) ≫ e.hom) := by
  ext k j
  rw [ι_freeMat_π, Category.assoc, Category.assoc, Functor.ι_freeObjIso_inv_assoc,
    Functor.freeObjIso_hom_π, ← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc,
    ι_freeMat_π]

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The ring of functions on an object of the big fppf site. -/
abbrev Gam (T : BigFppfOver B S hS) : Type u := Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)

/-- The structure sheaf of the algebraic space of a scheme, in the spelling of the modules of the
small étale ringed topos. -/
abbrev unitT (T : BigFppfOver B S hS) : toposModules B S hS ((schemeSpaceFunctor B S hS).obj T) :=
  unitS ((schemeSpaceFunctor B S hS).obj T)

/-- Evaluation of an endomorphism of `𝒪_T` at the identity chart, as an additive map. -/
def unitEndValueHom (T : BigFppfOver B S hS) : (unitT T ⟶ unitT T) →+ Gam T where
  toFun s := unitEndValue (X := (schemeSpaceFunctor B S hS).obj T) (yonedaEtaleChart B S hS T) s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The endomorphism of `𝒪_T` given by a function on `T`**: multiplication by it. -/
def funEnd (T : BigFppfOver B S hS) (a : Gam T) : unitT T ⟶ unitT T :=
  Function.surjInv (unitEndValue_bijective (B := B) (S := S) (hS := hS) T).2 a

/-- The value of multiplication by `a` at the identity chart is `a`. -/
@[simp]
theorem unitEndValueHom_funEnd (T : BigFppfOver B S hS) (a : Gam T) :
    unitEndValueHom T (funEnd T a) = a :=
  Function.surjInv_eq _ a

/-- Two endomorphisms of `𝒪_T` with the same value at the identity chart are equal. -/
theorem funEnd_injective_eq (T : BigFppfOver B S hS) {s t : unitT T ⟶ unitT T}
    (h : unitEndValueHom T s = unitEndValueHom T t) : s = t :=
  (unitEndValue_bijective (B := B) (S := S) (hS := hS) T).1 h

/-- Every endomorphism of `𝒪_T` is multiplication by its value at the identity chart. -/
@[simp]
theorem funEnd_unitEndValueHom (T : BigFppfOver B S hS) (s : unitT T ⟶ unitT T) :
    funEnd T (unitEndValueHom T s) = s :=
  funEnd_injective_eq T (unitEndValueHom_funEnd T _)

/-- The value at the identity chart of a composite of endomorphisms of `𝒪_T` is the product of
their values. -/
theorem unitEndValueHom_comp (T : BigFppfOver B S hS) (s t : unitT T ⟶ unitT T) :
    unitEndValueHom T (s ≫ t) = unitEndValueHom T s * unitEndValueHom T t :=
  unitEndValue_comp (X := (schemeSpaceFunctor B S hS).obj T) _ s t

/-- Multiplication by `a * b` is the composite of multiplication by `a` and by `b`. -/
theorem funEnd_mul (T : BigFppfOver B S hS) (a b : Gam T) :
    funEnd T (a * b) = funEnd T a ≫ funEnd T b :=
  funEnd_injective_eq T (by rw [unitEndValueHom_comp]; simp)

/-- Multiplication by `a + b` is the sum of multiplication by `a` and by `b`. -/
theorem funEnd_add (T : BigFppfOver B S hS) (a b : Gam T) :
    funEnd T (a + b) = funEnd T a + funEnd T b :=
  funEnd_injective_eq T (by rw [map_add]; simp)

/-- Multiplication by `0` is the zero endomorphism of `𝒪_T`. -/
theorem funEnd_zero (T : BigFppfOver B S hS) : funEnd T 0 = 0 :=
  funEnd_injective_eq T (by rw [map_zero]; simp)

/-- Multiplication by `1` is the identity of `𝒪_T`. -/
theorem funEnd_one (T : BigFppfOver B S hS) : funEnd T 1 = 𝟙 (unitT T) :=
  funEnd_injective_eq T (by simp; rfl)

/-- Multiplication by a finite sum of functions is the sum of the multiplications. -/
theorem funEnd_sum (T : BigFppfOver B S hS) {ι : Type*} (s : Finset ι) (a : ι → Gam T) :
    funEnd T (∑ i ∈ s, a i) = ∑ i ∈ s, funEnd T (a i) :=
  funEnd_injective_eq T (by rw [map_sum]; simp)

/-- **The inverse image of multiplication by a function is multiplication by its pullback**, along
a morphism `f` of the algebraic spaces of two schemes induced by a morphism `g` of the schemes. -/
theorem pullEnd_funEnd {T' T : BigFppfOver B S hS}
    (f : (schemeSpaceFunctor B S hS).obj T' ⟶ (schemeSpaceFunctor B S hS).obj T) (g : T' ⟶ T)
    (hf : f.hom = yoneda.map g) (a : Gam T) :
    pullEnd f (funEnd T a) = funEnd T' (((BigFppfOver.toScheme B S hS).map g).appTop.hom a) := by
  refine funEnd_injective_eq T' ?_
  refine Eq.trans ?_ (unitEndValueHom_funEnd T' _).symm
  let d : ChartDiagram B S hS ((schemeSpaceFunctor B S hS).obj T').1
      ((schemeSpaceFunctor B S hS).obj T).1 f.hom :=
    ⟨yonedaEtaleChart B S hS T', yonedaEtaleChart B S hS T, g, by
      change 𝟙 _ ≫ f.hom = yoneda.map g ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, hf]⟩
  refine (unitEndValue_pullEnd f (funEnd T a) d).trans ?_
  exact congrArg (chartDiagramRestrict B S hS _ d) (unitEndValueHom_funEnd T a)

/-- **The morphism of free modules of a matrix of functions.** -/
abbrev matMap (T : BigFppfOver B S hS) {n m : ℕ} (M : Matrix (Fin n) (Fin m) (Gam T)) :
    freeObj (unitT T) n ⟶ freeObj (unitT T) m :=
  freeMat (unitT T) (fun j k => funEnd T (M j k))

/-- The morphism of a product of matrices is the composite of their morphisms. -/
theorem matMap_mul (T : BigFppfOver B S hS) {n m k : ℕ} (M : Matrix (Fin n) (Fin m) (Gam T))
    (N : Matrix (Fin m) (Fin k) (Gam T)) : matMap T (M * N) = matMap T M ≫ matMap T N := by
  refine Eq.trans ?_ (freeMat_comp _ _ _).symm
  refine freeMat_congr _ fun j l => ?_
  rw [Matrix.mul_apply, funEnd_sum]
  exact Finset.sum_congr rfl fun i _ => funEnd_mul T _ _

/-- The morphism of a sum of matrices is the sum of their morphisms. -/
theorem matMap_add (T : BigFppfOver B S hS) {n m : ℕ} (M N : Matrix (Fin n) (Fin m) (Gam T)) :
    matMap T (M + N) = matMap T M + matMap T N := by
  refine Eq.trans ?_ (freeMat_add _ _ _).symm
  exact freeMat_congr _ fun j k => funEnd_add T _ _

/-- The zero matrix gives the zero morphism `𝒪_T^n ⟶ 𝒪_T^m`. -/
theorem matMap_zero (T : BigFppfOver B S hS) {n m : ℕ} :
    matMap T (0 : Matrix (Fin n) (Fin m) (Gam T)) = 0 :=
  (freeMat_congr _ fun _ _ => funEnd_zero T).trans (freeMat_zero _)

/-- The identity matrix gives the identity of `𝒪_T^n`. -/
theorem matMap_one (T : BigFppfOver B S hS) (n : ℕ) :
    matMap T (1 : Matrix (Fin n) (Fin n) (Gam T)) = 𝟙 _ := by
  refine Eq.trans ?_ (freeMat_id _ n)
  refine freeMat_congr _ fun j k => ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact funEnd_one T
  · exact funEnd_zero T

/-- The identification `f^*𝒪_T^n ≅ 𝒪_{T'}^n`. -/
abbrev pullFreeIso {T' T : BigFppfOver B S hS}
    (f : (schemeSpaceFunctor B S hS).obj T' ⟶ (schemeSpaceFunctor B S hS).obj T) (n : ℕ) :
    ((toposModulePullbackData B S hS).pull f).obj (freeObj (unitT T) n) ≅ freeObj (unitT T') n :=
  ((toposModulePullbackData B S hS).pull f).freeObjIso (modulePullbackUnitIsoS f) n

/-- **The inverse image of the morphism of a matrix of functions is the morphism of the matrix of
pulled back functions.** -/
theorem pullFreeIso_inv_map_matMap {T' T : BigFppfOver B S hS}
    (f : (schemeSpaceFunctor B S hS).obj T' ⟶ (schemeSpaceFunctor B S hS).obj T) (g : T' ⟶ T)
    (hf : f.hom = yoneda.map g) {n m : ℕ} (M : Matrix (Fin n) (Fin m) (Gam T)) :
    (pullFreeIso f n).inv ≫ ((toposModulePullbackData B S hS).pull f).map (matMap T M) ≫
        (pullFreeIso f m).hom =
      matMap T' (M.map ((BigFppfOver.toScheme B S hS).map g).appTop.hom) := by
  refine (Functor.freeObjIso_inv_map_freeMat _ _ _).trans ?_
  exact freeMat_congr _ fun j k => pullEnd_funEnd f g hf (M j k)

/-- **The global sections of `𝒪_T^n` are the `n`-tuples of functions on `T`.** -/
def freePointEquiv (T : BigFppfOver B S hS) (n : ℕ) :
    (unitT T ⟶ freeObj (unitT T) n) ≃ (Fin n → Gam T) where
  toFun x j := unitEndValueHom T (x ≫ biproduct.π _ j)
  invFun v := biproduct.lift (fun j => funEnd T (v j))
  left_inv x := by
    refine biproduct.hom_ext _ _ fun j => ?_
    rw [biproduct.lift_π, funEnd_unitEndValueHom]
  right_inv v := funext fun j => by
    change unitEndValueHom T (biproduct.lift (fun j => funEnd T (v j)) ≫ biproduct.π _ j) = v j
    rw [biproduct.lift_π, unitEndValueHom_funEnd]

/-- **Composing a global section of `𝒪_T^n` with the morphism of a matrix multiplies the row of
functions by the matrix.** -/
theorem freePointEquiv_comp_matMap (T : BigFppfOver B S hS) {n m : ℕ}
    (x : unitT T ⟶ freeObj (unitT T) n) (M : Matrix (Fin n) (Fin m) (Gam T)) :
    freePointEquiv T m (x ≫ matMap T M) = Matrix.vecMul (freePointEquiv T n x) M := by
  funext k
  change unitEndValueHom T ((x ≫ matMap T M) ≫ biproduct.π _ k) = _
  have hx : x = biproduct.lift (fun j => x ≫ biproduct.π _ j) :=
    biproduct.hom_ext _ _ fun j => (biproduct.lift_π (fun j => x ≫ biproduct.π _ j) j).symm
  conv_lhs => rw [Category.assoc, biproduct.matrix_π, hx, biproduct.lift_desc, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitEndValueHom_comp, unitEndValueHom_funEnd]
  rfl

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConcreteDGFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDeltaFunctorTriangle

/-!
# Forgetting the action is an exact functor `K(Mod(A, d)) ⥤ K(Mod(O))`

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. Forgetting
the action of `A` sends a right differential graded `A`-module to its underlying complex of
`O`-modules, and homotopic morphisms to homotopic maps of complexes, so it induces a functor
`K(Mod(A, d)) ⥤ K(Mod(O))` from the homotopy category of [Stacks, Tag 0FS7] to the ordinary
homotopy category of complexes of `O`-modules. This file shows that it commutes with the
translations and is triangulated.

The translations of `K(Mod(A, d))` are those of the homotopy category of the differential graded
category of right differential graded modules, whose `n`-th shift of a module has the `n`-th shift
of its complex as underlying complex. Forgetting is therefore defined first on that differential
graded homotopy category, where the translations are strict and the comparison
`M[n] ⟶ M⟦n⟧` is a transport along an equality of complexes; on morphisms the shift multiplies
a closed degree-zero cochain by the sign `(-1)^{n · 0} = 1`, so the comparison is natural. A
distinguished triangle of `K(Mod(A, d))` is isomorphic to the triangle of the cone of a morphism,
whose underlying complexes and maps are Mathlib's mapping cone and its triangle.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.dgHomotopyForget`: forgetting the action on the
  homotopy category of the differential graded category of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.homotopyForgetComplex`: forgetting the action,
  `K(Mod(A, d)) ⥤ K(Mod(O))`.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopyForgetComplex_commShift` and
  `SheafOfModules.DifferentialGradedModule.homotopyForgetComplex_isTriangulated`: **forgetting
  the action commutes with the translations and is an exact functor of triangulated
  categories.**

## References

* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 09QU](https://stacks.math.columbia.edu/tag/09QU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.HomComplex

universe u v w

namespace SheafOfModules.DifferentialGradedModule

/-! ### Transports of maps of complexes in the homotopy category -/

section Transport

variable {C : Type*} [Category* C] [Preadditive C]

/-- Two maps of complexes with heterogeneously equal components between equal complexes are
conjugate by the transports of their classes in the homotopy category. -/
theorem quotient_map_comp_eqToHom {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ} (hX : X₁ = X₂)
    (hY : Y₁ = Y₂) (φ₁ : X₁ ⟶ Y₁) (φ₂ : X₂ ⟶ Y₂) (h : ∀ p, HEq (φ₁.f p) (φ₂.f p)) :
    (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ₁ ≫
        eqToHom (congrArg (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj hY) =
      eqToHom (congrArg (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj hX) ≫
        (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ₂ := by
  subst hX hY
  obtain rfl : φ₁ = φ₂ := HomologicalComplex.hom_ext _ _ fun p => eq_of_heq (h p)
  simp

/-- A map of complexes whose components are heterogeneously identities is, in the homotopy
category, a transport along an equality of complexes. -/
theorem eqToHom_comp_quotient_map {Y K₁ K₂ : CochainComplex C ℤ} (hY : Y = K₁) (hK : Y = K₂)
    (φ : K₁ ⟶ K₂) (h : ∀ p, HEq (φ.f p) (𝟙 (K₁.X p)))
    (e₁ : (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y =
      (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K₁)
    (e₂ : (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y =
      (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K₂) :
    eqToHom e₁ ≫ (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ =
      eqToHom e₂ := by
  subst hY hK
  obtain rfl : φ = 𝟙 _ := HomologicalComplex.hom_ext _ _ fun p => eq_of_heq (h p)
  simp

/-- An `eqToHom` is heterogeneously an identity. -/
theorem eqToHom_heq_id' {D : Type*} [Category* D] {P Q : D} (h : P = Q) :
    HEq (eqToHom h) (𝟙 P) := by
  subst h
  rfl

/-- The commutation of a functor with a translation is natural for transports along equalities
of objects. -/
@[reassoc]
theorem commShiftIso_hom_app_comp_eqToHom {D D' : Type*} [Category* D] [Category* D']
    {M : Type*} [AddMonoid M] [HasShift D M] [HasShift D' M] (F : D ⥤ D') [F.CommShift M]
    (a : M) {W W' : D} (h : W = W') (e : (F.obj W)⟦a⟧ = (F.obj W')⟦a⟧)
    (e' : F.obj (W⟦a⟧) = F.obj (W'⟦a⟧)) :
    (F.commShiftIso a).hom.app W ≫ eqToHom e = eqToHom e' ≫ (F.commShiftIso a).hom.app W' := by
  subst h
  simp

/-- Two commuting squares paste. -/
theorem comp_comp_eq_of_comp_eq {D : Type*} [Category* D] {P Q R S T U : D} {m : P ⟶ Q}
    {a : Q ⟶ R} {c : R ⟶ T} {b : P ⟶ S} {q : S ⟶ R} {c' : S ⟶ U} {t : U ⟶ T}
    (h₁ : m ≫ a = b ≫ q) (h₂ : q ≫ c = c' ≫ t) : m ≫ a ≫ c = (b ≫ c') ≫ t := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Heterogeneously equal maps of complexes between equal complexes have heterogeneously equal
components. -/
theorem hom_f_heq {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ} (hX : X₁ = X₂) (hY : Y₁ = Y₂)
    {φ₁ : X₁ ⟶ Y₁} {φ₂ : X₂ ⟶ Y₂} (h : HEq φ₁ φ₂) (p : ℤ) : HEq (φ₁.f p) (φ₂.f p) := by
  subst hX hY
  obtain rfl := eq_of_heq h
  rfl

/-- Heterogeneously equal cochains between equal complexes have heterogeneously equal
components. -/
theorem forgetComplex_cochain_v_heq {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ} {n : ℤ} (hX : X₁ = X₂)
    (hY : Y₁ = Y₂) {c₁ : Cochain X₁ Y₁ n} {c₂ : Cochain X₂ Y₂ n} (h : HEq c₁ c₂) (p q : ℤ)
    (hpq : p + n = q) :
    HEq (c₁.v p q hpq) (c₂.v p q hpq) := by
  subst hX hY
  obtain rfl := eq_of_heq h
  rfl

/-- Negation preserves heterogeneous equality of morphisms between equal objects. -/
theorem neg_heq {D : Type*} [Category* D] [Preadditive D] {P₁ P₂ Q₁ Q₂ : D} (hP : P₁ = P₂)
    (hQ : Q₁ = Q₂) {a : P₁ ⟶ Q₁} {b : P₂ ⟶ Q₂} (h : HEq a b) : HEq (-a) (-b) := by
  subst hP hQ
  obtain rfl := eq_of_heq h
  rfl

/-- A commutation isomorphism conjugated by transports is the commutation isomorphism at the
transported object. -/
theorem eqToHom_comp_commShiftIso_hom_app_comp_eqToHom {D D' : Type*} [Category* D]
    [Category* D'] {M : Type*} [AddMonoid M] [HasShift D M] [HasShift D' M] (F : D ⥤ D')
    [F.CommShift M] (a : M) {P : D'} {W W' : D} (h : W = W') (e₁ : P = F.obj (W⟦a⟧))
    (e₂ : (F.obj W)⟦a⟧ = (F.obj W')⟦a⟧) (e₃ : P = F.obj (W'⟦a⟧)) :
    eqToHom e₁ ≫ (F.commShiftIso a).hom.app W ≫ eqToHom e₂ =
      eqToHom e₃ ≫ (F.commShiftIso a).hom.app W' := by
  subst h
  simp

/-- Pasting a commuting square with a morphism on the right. -/
theorem comp_eqToHom_comp_eq {D : Type*} [Category* D] {P P' Q Q' R : D} {m : P ⟶ Q}
    {m' : P' ⟶ Q'} {hP : P = P'} {hQ : Q = Q'} (c : Q' ⟶ R)
    (h : m ≫ eqToHom hQ = eqToHom hP ≫ m') : m ≫ eqToHom hQ ≫ c = eqToHom hP ≫ m' ≫ c := by
  rw [← Category.assoc, h, Category.assoc]

end Transport

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-! ### Forgetting the action on the differential graded homotopy category -/

section DG

/-- The underlying cochain of a sum of homogeneous morphisms. -/
theorem cochainOf_add' {x y : (dgCategoryData.{u, v, w} A).category.Obj} {k : ℤ}
    (f g : (dgCategoryData.{u, v, w} A).category.Hom x y k) :
    cochainOf A (dgCategoryData A) (f + g) =
      cochainOf A (dgCategoryData A) f + cochainOf A (dgCategoryData A) g :=
  cochainOf_add A _ (Classical.choice (hasBinaryBiproducts A x x)) f g

/-- The underlying cochain of a difference of homogeneous morphisms. -/
theorem cochainOf_sub' {x y : (dgCategoryData.{u, v, w} A).category.Obj} {k : ℤ}
    (f g : (dgCategoryData.{u, v, w} A).category.Hom x y k) :
    cochainOf A (dgCategoryData A) (f - g) =
      cochainOf A (dgCategoryData A) f - cochainOf A (dgCategoryData A) g :=
  eq_sub_of_add_eq (by rw [← cochainOf_add', sub_add_cancel])

/-- The underlying cochain of the differential of a homogeneous morphism, in a prescribed
degree. -/
theorem cochainOf_d'' {x y : (dgCategoryData.{u, v, w} A).category.Obj} {k l : ℤ} (e : k + 1 = l)
    (f : (dgCategoryData.{u, v, w} A).category.Hom x y k) :
    cochainOf A (dgCategoryData A) ((dgCategoryData.{u, v, w} A).category.d' e f) =
      δ k l (cochainOf A (dgCategoryData A) f) := by
  subst e
  exact ConcreteDGFunctor.cochainOf_d' f

/-- The underlying cocycle of a closed degree-zero homogeneous morphism. -/
def cocycleCochain {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) :
    Cocycle (moduleOf A (dgCategoryData A) x).complex (moduleOf A (dgCategoryData A) y).complex 0 :=
  Cocycle.mk (cochainOf A (dgCategoryData A) c.1) 1 (zero_add 1) (by
    rw [← cochainOf_d'' A (zero_add 1) c.1]
    have h : (dgCategoryData.{u, v, w} A).category.d' (zero_add 1) c.1 = 0 := c.2
    rw [h, cochainOf_zero])

/-- The underlying cochain of `cocycleCochain`. -/
@[simp]
theorem cocycleCochain_coe {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) :
    (cocycleCochain A c : Cochain _ _ 0) = cochainOf A (dgCategoryData A) c.1 := rfl

/-- The map of complexes underlying a closed degree-zero homogeneous morphism. -/
abbrev cocycleHom {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) :
    (moduleOf A (dgCategoryData A) x).complex ⟶ (moduleOf A (dgCategoryData A) y).complex :=
  Cocycle.homOf (cocycleCochain A c)

/-- The components of the underlying map of a closed degree-zero morphism. -/
theorem cocycleHom_f {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) (p : ℤ) :
    (cocycleHom A c).f p = (cochainOf A (dgCategoryData A) c.1).v p p (add_zero p) := by
  simp [cocycleHom]

/-- Homotopic closed homogeneous morphisms have homotopic underlying maps of complexes. -/
theorem quotient_map_cocycleHom_eq {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c₁ c₂ : (dgCategoryData.{u, v, w} A).category.Cocycle x y)
    (h : (dgCategoryData.{u, v, w} A).category.Homotopic c₁ c₂) :
    (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (cocycleHom A c₁) =
      (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (cocycleHom A c₂) := by
  obtain ⟨g, hg⟩ := h
  have hc := congrArg (cochainOf A (dgCategoryData A)) hg
  rw [cochainOf_sub', cochainOf_d''] at hc
  refine _root_.HomotopyCategory.eq_of_homotopy _ _
    ((Cochain.equivHomotopy _ _).symm ⟨cochainOf A (dgCategoryData A) g, ?_⟩)
  simp only [Cocycle.cochain_ofHom_homOf_eq_coe, cocycleCochain_coe]
  rw [← hc]
  abel

/-- The underlying map of a composite is the composite of the underlying maps. -/
theorem cocycleHom_comp {x y z : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y)
    (c' : (dgCategoryData.{u, v, w} A).category.Cocycle y z) :
    cocycleHom A ((dgCategoryData.{u, v, w} A).category.compCocycle c' c) =
      cocycleHom A c ≫ cocycleHom A c' := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [HomologicalComplex.comp_f, cocycleHom_f, cocycleHom_f, cocycleHom_f]
  change (cochainOf A (dgCategoryData A) ((dgCategoryData.{u, v, w} A).category.comp
    (show (0 : ℤ) + 0 = 0 from rfl) c'.1 c.1)).v p p (add_zero p) = _
  rw [cochainOf_comp, Cochain.comp_v _ _ _ p p p (add_zero p) (add_zero p)]

/-- The underlying map of an identity is the identity. -/
theorem cocycleHom_id (x : (dgCategoryData.{u, v, w} A).category.Obj) :
    cocycleHom A (⟨(dgCategoryData.{u, v, w} A).category.id x,
      (dgCategoryData.{u, v, w} A).category.d_id x⟩) = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [HomologicalComplex.id_f, cocycleHom_f]
  rw [ConcreteDGFunctor.cochainOf_id', Cochain.ofHom_v]
  rfl

/-- The underlying complex of an object of the differential graded homotopy category. -/
abbrev dgComplex (x : (dgCategoryData.{u, v, w} A).category.K) :
    CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (moduleOf A (dgCategoryData A) (x : (dgCategoryData.{u, v, w} A).category.Obj)).complex

/-- **Forgetting the action on the differential graded homotopy category**: a right differential
graded module goes to its underlying complex, and the class of a closed degree-zero homogeneous
morphism to the class of its underlying map of complexes. -/
abbrev dgHomotopyForget : (dgCategoryData.{u, v, w} A).category.K ⥤
    _root_.HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) where
  obj x := (_root_.HomotopyCategory.quotient _ _).obj (dgComplex A x)
  map {x y} f := Quotient.lift (s := (dgCategoryData.{u, v, w} A).category.homotopySetoid x y)
    (fun c => (_root_.HomotopyCategory.quotient _ _).map (cocycleHom A c))
    (fun c₁ c₂ h => quotient_map_cocycleHom_eq A c₁ c₂ h) f
  map_id x :=
    (congrArg (_root_.HomotopyCategory.quotient _ _).map (cocycleHom_id A x)).trans
      ((_root_.HomotopyCategory.quotient _ _).map_id _)
  map_comp {x y z} f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g =>
    exact (congrArg (_root_.HomotopyCategory.quotient _ _).map (cocycleHom_comp A f g)).trans
      ((_root_.HomotopyCategory.quotient _ _).map_comp _ _)

/-- Forgetting the action on the class of a cocycle. -/
theorem dgHomotopyForget_map_mk {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) :
    (dgHomotopyForget A).map (X := x) (Y := y)
        (Quotient.mk ((dgCategoryData.{u, v, w} A).category.homotopySetoid x y) c) =
      (_root_.HomotopyCategory.quotient _ _).map (cocycleHom A c) := rfl

end DG


/-! ### Forgetting the action commutes with the translations -/

section Shift

/-- Equal objects and heterogeneously equal morphisms have heterogeneously equal images under
forgetting the action. -/
theorem dgHomotopyForget_map_heq {x x' y y' : (dgCategoryData.{u, v, w} A).category.K}
    (hx : x = x') (hy : y = y') {f : x ⟶ y} {f' : x' ⟶ y'} (h : HEq f f') :
    HEq ((dgHomotopyForget A).map f) ((dgHomotopyForget A).map f') := by
  subst hx hy
  obtain rfl := eq_of_heq h
  rfl

/-- Maps of complexes with heterogeneously equal components between equal complexes have
heterogeneously equal classes. -/
theorem quotient_map_heq {C : Type*} [Category* C] [Preadditive C]
    {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ} (hX : X₁ = X₂) (hY : Y₁ = Y₂) (φ₁ : X₁ ⟶ Y₁)
    (φ₂ : X₂ ⟶ Y₂) (h : ∀ p, HEq (φ₁.f p) (φ₂.f p)) :
    HEq ((_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ₁)
      ((_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ₂) := by
  subst hX hY
  obtain rfl : φ₁ = φ₂ := HomologicalComplex.hom_ext _ _ fun p => eq_of_heq (h p)
  rfl

/-- Equal functors have heterogeneously equal values on a morphism. -/
theorem heq_map_of_functor_eq {B E : Type*} [Category* B] [Category* E] {F G : B ⥤ E}
    (h : F = G) {x y : B} (f : x ⟶ y) : HEq (F.map f) (G.map f) := by
  subst h
  rfl

/-- Every object of the differential graded category of modules is the object of a module. -/
private theorem exists_asObject_eq (x : (dgCategoryData.{u, v, w} A).category.Obj) :
    ∃ M : DifferentialGradedModule.{u, v, w} A, asObject A M = x :=
  ⟨asModule A x, asObject_asModule A x⟩

/-- The complex of the module of the object of a module is the complex of the module. -/
private theorem asModule_asObject_complex (M : DifferentialGradedModule.{u, v, w} A) :
    (asModule A (asObject A M)).complex = M.complex :=
  congrArg DifferentialGradedModule.complex (asModule_asObject M)

/-- The complex underlying the canonical differential graded shift of a module is the shift of
its complex. -/
theorem canonicalShift_complex (S : DGCategory.ShiftAxiomB (dgCategoryData.{u, v, w} A).category)
    (hS : S = (shiftAxiomB.{u, v, w} A).axiomB) (n : ℤ)
    (x : (dgCategoryData.{u, v, w} A).category.Obj) :
    (moduleOf A (dgCategoryData A) ((S.shiftFunctor n).obj x)).complex =
      (moduleOf A (dgCategoryData A) x).complex⟦n⟧ := by
  subst hS
  obtain ⟨M, rfl⟩ := exists_asObject_eq A x
  refine ((shiftAxiomB.{u, v, w} A).shifted_complex n M).trans ?_
  change _ = (asModule A (asObject A M)).complex⟦n⟧
  rw [asModule_asObject]
  rfl

/-- The components of the canonical differential graded shift of a closed degree-zero morphism
are those of the morphism, in the shifted degree. -/
theorem canonicalShift_cocycleHom_f (S : DGCategory.ShiftAxiomB
    (dgCategoryData.{u, v, w} A).category) (hS : S = (shiftAxiomB.{u, v, w} A).axiomB) (n : ℤ)
    {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) (p : ℤ) :
    HEq ((cocycleHom A ((S.shiftFunctor n).mapCocycle c)).f p) ((cocycleHom A c).f (p + n)) := by
  subst hS
  obtain ⟨M, rfl⟩ := exists_asObject_eq A x
  obtain ⟨N, rfl⟩ := exists_asObject_eq A y
  rw [cocycleHom_f, cocycleHom_f]
  have h := (shiftAxiomB.{u, v, w} A).shifted_map n 0 M N c.1 p p (add_zero p)
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, one_smul] at h
  exact h

/-- The complex underlying the translate of an object of the differential graded homotopy
category is the shift of its complex. -/
theorem dgShift_complex (n : ℤ) (x : (dgCategoryData.{u, v, w} A).category.K) :
    dgComplex A ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).obj x) =
      (dgComplex A x)⟦n⟧ :=
  (congrArg (dgComplex A)
    (Functor.congr_obj ((dgConeSituation.{u, v, w} A).shift.kShift_functor n) x)).trans
    (canonicalShift_complex A _ (dgConeSituation_shift A) n x)

/-- The comparison `x[n] ⟶ x⟦n⟧` of forgetting the action with the translations, at one
object: the transport along `dgShift_complex` followed by the commutation of the quotient
functor with the shift. -/
def dgHomotopyForgetShiftIso (n : ℤ) (x : (dgCategoryData.{u, v, w} A).category.K) :
    (dgHomotopyForget A).obj ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).obj x) ≅
      ((dgHomotopyForget A).obj x)⟦n⟧ :=
  eqToIso (congrArg (_root_.HomotopyCategory.quotient _ _).obj (dgShift_complex A n x)) ≪≫
    ((_root_.HomotopyCategory.quotient _ _).commShiftIso n).app _

/-- The translate of the class of a cocycle is, heterogeneously, the class of its canonical
differential graded shift, after forgetting the action. -/
theorem dgHomotopyForget_map_shift_heq (n : ℤ) {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) :
    HEq ((dgHomotopyForget A).map ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).map
        (X := x) (Y := y) (Quotient.mk _ c)))
      ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ((cocycleHom A c)⟦n⟧')) := by
  refine (dgHomotopyForget_map_heq A
    (Functor.congr_obj ((dgConeSituation.{u, v, w} A).shift.kShift_functor n) x)
    (Functor.congr_obj ((dgConeSituation.{u, v, w} A).shift.kShift_functor n) y)
    (heq_map_of_functor_eq ((dgConeSituation.{u, v, w} A).shift.kShift_functor n) _)).trans ?_
  exact quotient_map_heq (canonicalShift_complex A _ (dgConeSituation_shift A) n x)
    (canonicalShift_complex A _ (dgConeSituation_shift A) n y) _ _
    (canonicalShift_cocycleHom_f A _ (dgConeSituation_shift A) n c)


/-- The comparison `x[n] ⟶ x⟦n⟧`, unfolded. -/
theorem dgHomotopyForgetShiftIso_hom (n : ℤ) (x : (dgCategoryData.{u, v, w} A).category.K) :
    (dgHomotopyForgetShiftIso A n x).hom =
      eqToHom (congrArg (_root_.HomotopyCategory.quotient _ _).obj (dgShift_complex A n x)) ≫
        ((_root_.HomotopyCategory.quotient _ _).commShiftIso n).hom.app (dgComplex A x) :=
  rfl

/-- The comparison `x[n] ⟶ x⟦n⟧` is natural. -/
theorem dgHomotopyForgetShiftIso_naturality (n : ℤ)
    {x y : (dgCategoryData.{u, v, w} A).category.K}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle
      (x : (dgCategoryData.{u, v, w} A).category.Obj)
      (y : (dgCategoryData.{u, v, w} A).category.Obj)) :
    (dgHomotopyForget A).map ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).map
        (X := x) (Y := y) (Quotient.mk _ c)) ≫ (dgHomotopyForgetShiftIso A n y).hom =
      (dgHomotopyForgetShiftIso A n x).hom ≫
        ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (cocycleHom A c))⟦n⟧' := by
  have h₁ := ConcreteDGFunctor.comp_eqToHom_eq_of_heq _ _
    (congrArg (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (dgShift_complex A n x))
    (congrArg (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (dgShift_complex A n y))
    (dgHomotopyForget_map_shift_heq A n c)
  exact comp_comp_eq_of_comp_eq h₁ (Functor.commShiftIso_hom_naturality _ _ _)

/-- The comparisons `x[n] ⟶ x⟦n⟧`, as an isomorphism of functors. -/
def dgHomotopyForgetCommShiftIso (n : ℤ) :
    shiftFunctor (dgCategoryData.{u, v, w} A).category.K n ⋙ dgHomotopyForget A ≅
      dgHomotopyForget A ⋙ shiftFunctor (_root_.HomotopyCategory _ (ComplexShape.up ℤ)) n :=
  NatIso.ofComponents (dgHomotopyForgetShiftIso A n) (by
    intro x y f
    induction f using Quotient.inductionOn with | h c =>
    exact dgHomotopyForgetShiftIso_naturality A n c)

/-- The components of `dgHomotopyForgetCommShiftIso`. -/
theorem dgHomotopyForgetCommShiftIso_hom_app (n : ℤ)
    (x : (dgCategoryData.{u, v, w} A).category.K) :
    (dgHomotopyForgetCommShiftIso A n).hom.app x = (dgHomotopyForgetShiftIso A n x).hom :=
  rfl

/-- The comparison in degree `0` is the canonical one. -/
theorem dgHomotopyForgetShiftIso_zero (x : (dgCategoryData.{u, v, w} A).category.K) :
    (dgHomotopyForgetShiftIso A 0 x).hom =
      (dgHomotopyForget A).map
          ((shiftFunctorZero (dgCategoryData.{u, v, w} A).category.K ℤ).hom.app x) ≫
        (shiftFunctorZero (_root_.HomotopyCategory _ (ComplexShape.up ℤ)) ℤ).inv.app
          ((dgHomotopyForget A).obj x) := by
  obtain ⟨h₀, hZ⟩ := (ConcreteDGFunctor.dgConeSituation_isStrictKShift A).1
  have e : (shiftFunctorZero (dgCategoryData.{u, v, w} A).category.K ℤ).hom.app x =
      eqToHom (Functor.congr_obj h₀ x) := by
    rw [hZ]
    simp
  rw [e, eqToHom_map, dgHomotopyForgetShiftIso_hom, Functor.commShiftIso_zero,
    Functor.CommShift.isoZero_hom_app, ← Category.assoc]
  congr 1
  refine eqToHom_comp_quotient_map (dgShift_complex A 0 x)
    (congrArg (dgComplex A) (Functor.congr_obj h₀ x)) _ (fun p => ?_) _ _
  rw [CochainComplex.shiftFunctorZero_hom_app_f]
  exact eqToHom_heq_id' (by simp)

/-- The comparisons are additive in the degree. -/
theorem dgHomotopyForgetShiftIso_add (a b : ℤ) (x : (dgCategoryData.{u, v, w} A).category.K) :
    (dgHomotopyForgetShiftIso A (a + b) x).hom =
      (dgHomotopyForget A).map
          ((shiftFunctorAdd (dgCategoryData.{u, v, w} A).category.K a b).hom.app x) ≫
        (dgHomotopyForgetShiftIso A b
          ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K a).obj x)).hom ≫
          ((dgHomotopyForgetShiftIso A a x).hom)⟦b⟧' ≫
            (shiftFunctorAdd (_root_.HomotopyCategory _ (ComplexShape.up ℤ)) a b).inv.app
              ((dgHomotopyForget A).obj x) := by
  obtain ⟨hab, hA⟩ := (ConcreteDGFunctor.dgConeSituation_isStrictKShift A).2 a b
  have e : (shiftFunctorAdd (dgCategoryData.{u, v, w} A).category.K a b).hom.app x =
      eqToHom (Functor.congr_obj hab x) := by
    rw [hA]
    simp
  rw [e, eqToHom_map, dgHomotopyForgetShiftIso_hom, dgHomotopyForgetShiftIso_hom,
    dgHomotopyForgetShiftIso_hom, Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [commShiftIso_hom_app_comp_eqToHom_assoc _ b (dgShift_complex A a x) _
      (by rw [dgShift_complex A a x]),
    eqToHom_trans_assoc, eqToHom_trans_assoc, ← Category.assoc]
  congr 1
  refine eqToHom_comp_quotient_map (dgShift_complex A (a + b) x)
    ((congrArg (dgComplex A) (Functor.congr_obj hab x)).trans ((dgShift_complex A b _).trans
        (congrArg (fun K => K⟦b⟧) (dgShift_complex A a x)))) _ (fun p => ?_) _ _
  rw [CochainComplex.shiftFunctorAdd_hom_app_f]
  exact eqToHom_heq_id' (by simp [add_assoc, add_comm a b])

/-- **Forgetting the action on the differential graded homotopy category commutes with the
translations**, the comparison being a transport along the equality of the underlying complex of
a translate with the shift of the complex. -/
@[instance_reducible]
instance dgHomotopyForget_commShift : (dgHomotopyForget A).CommShift ℤ where
  commShiftIso n := dgHomotopyForgetCommShiftIso A n
  commShiftIso_zero := by
    ext x
    rw [Functor.CommShift.isoZero_hom_app, dgHomotopyForgetCommShiftIso_hom_app]
    exact dgHomotopyForgetShiftIso_zero A x
  commShiftIso_add a b := by
    ext x
    rw [Functor.CommShift.isoAdd_hom_app, dgHomotopyForgetCommShiftIso_hom_app,
      dgHomotopyForgetCommShiftIso_hom_app, dgHomotopyForgetCommShiftIso_hom_app]
    exact dgHomotopyForgetShiftIso_add A a b x

end Shift


/-! ### Forgetting the action on `K(Mod(A, d))` -/

section Homotopy

/-- **Forgetting the action**, `K(Mod(A, d)) ⥤ K(Mod(O))`: a right differential graded module
goes to its underlying complex of `O`-modules. -/
def homotopyForgetComplex : HomotopyCategory.{u, v, w} A ⥤
    _root_.HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _
    { obj M := (_root_.HomotopyCategory.quotient _ _).obj M.complex
      map f := (_root_.HomotopyCategory.quotient _ _).map f.toHomologicalComplex
      map_id M := (_root_.HomotopyCategory.quotient _ _).map_id M.complex
      map_comp _ _ := (_root_.HomotopyCategory.quotient _ _).map_comp _ _ }
    (fun _ _ _ _ ⟨h⟩ => _root_.HomotopyCategory.eq_of_homotopy _ _ h.toComplexHomotopy)

/-- Forgetting the action on the class of a module. -/
theorem homotopyForgetComplex_obj (M : DifferentialGradedModule.{u, v, w} A) :
    (homotopyForgetComplex A).obj ((HomotopyCategory.quotient A).obj M) =
      (_root_.HomotopyCategory.quotient _ _).obj M.complex := rfl

/-- Forgetting the action on the class of a morphism of modules. -/
theorem homotopyForgetComplex_map {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    (homotopyForgetComplex A).map ((HomotopyCategory.quotient A).map f) =
      (_root_.HomotopyCategory.quotient _ _).map f.toHomologicalComplex := rfl

/-- Forgetting the action on `K(Mod(A, d))` is forgetting it on the differential graded homotopy
category, through the identification of the two homotopy categories. -/
def homotopyForgetComplexIso :
    homotopyCategoryToDG.{u, v, w} A ⋙ dgHomotopyForget A ≅ homotopyForgetComplex A :=
  NatIso.ofComponents (fun Z => eqToIso (congrArg
      (fun M : DifferentialGradedModule.{u, v, w} A =>
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M.complex)
      (asModule_asObject Z.as))) (by
    rintro ⟨M⟩ ⟨N⟩ f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f
    exact quotient_map_comp_eqToHom (congrArg DifferentialGradedModule.complex
        (asModule_asObject M)) (congrArg DifferentialGradedModule.complex
        (asModule_asObject N)) _ g.toHomologicalComplex fun p =>
      (heq_of_eq (cocycleHom_f A _ p)).trans
        (forgetComplex_cochain_v_heq
          (congrArg DifferentialGradedModule.complex (asModule_asObject M))
          (congrArg DifferentialGradedModule.complex (asModule_asObject N))
          (ConcreteDGFunctor.cochainOf_homogeneousOfHom_heq g) p p (add_zero p)))

/-- The components of `homotopyForgetComplexIso` are transports. -/
theorem homotopyForgetComplexIso_hom_app (Z : HomotopyCategory.{u, v, w} A) :
    (homotopyForgetComplexIso A).hom.app Z = eqToHom (id <| congrArg
      (fun M : DifferentialGradedModule.{u, v, w} A =>
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M.complex)
      (asModule_asObject Z.as) : (homotopyCategoryToDG.{u, v, w} A ⋙ dgHomotopyForget A).obj Z =
        (homotopyForgetComplex A).obj Z) := rfl

/-- The inverse components of `homotopyForgetComplexIso` are transports. -/
theorem homotopyForgetComplexIso_inv_app (Z : HomotopyCategory.{u, v, w} A) :
    (homotopyForgetComplexIso A).inv.app Z = eqToHom (id <| (congrArg
      (fun M : DifferentialGradedModule.{u, v, w} A =>
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M.complex)
      (asModule_asObject Z.as)).symm : (homotopyForgetComplex A).obj Z =
        (homotopyCategoryToDG.{u, v, w} A ⋙ dgHomotopyForget A).obj Z) := rfl

/-- **Forgetting the action commutes with the translations.** -/
@[instance_reducible]
instance homotopyForgetComplex_commShift : (homotopyForgetComplex A).CommShift ℤ :=
  Functor.CommShift.ofIso (homotopyForgetComplexIso A) ℤ

/-- The commutation of `dgHomotopyForget` with the translations is `dgHomotopyForgetShiftIso`. -/
theorem dgHomotopyForget_commShiftIso_hom_app (n : ℤ)
    (x : (dgCategoryData.{u, v, w} A).category.K) :
    ((dgHomotopyForget A).commShiftIso n).hom.app x = (dgHomotopyForgetShiftIso A n x).hom :=
  rfl

/-- The comparison of `homotopyCategoryToDG` with the translations, with its type spelled as
the one of its components. -/
theorem homotopyCategoryToDG_commShiftIso_hom_app' (n : ℤ) (Z : HomotopyCategory.{u, v, w} A) :
    ((homotopyCategoryToDG.{u, v, w} A).commShiftIso n).hom.app Z = eqToHom
      (id <| homotopyCategoryToDG_obj_dgObjPreimage A _ :
        (homotopyCategoryToDG.{u, v, w} A).obj (Z⟦n⟧) =
        (shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).obj
          ((homotopyCategoryToDG.{u, v, w} A).obj Z)) :=
  commShiftIso_hom_app_eq n Z

/-- The underlying complex of the translate of a module is the shift of its complex. -/
theorem homotopyShift_complex (n : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    (((HomotopyCategory.quotient A).obj M)⟦n⟧).as.complex = M.complex⟦n⟧ :=
  (dgShift_complex A n (asObject A M)).trans
    (congrArg (fun K => K⟦n⟧) (asModule_asObject_complex A M))

/-- **The comparison of forgetting the action with the translations** is, at the class of a
module, the transport along `homotopyShift_complex` followed by the commutation of the quotient
functor with the shift. -/
theorem homotopyForgetComplex_commShiftIso_hom_app (n : ℤ)
    (M : DifferentialGradedModule.{u, v, w} A) :
    ((homotopyForgetComplex A).commShiftIso n).hom.app ((HomotopyCategory.quotient A).obj M) =
      eqToHom (congrArg (_root_.HomotopyCategory.quotient _ _).obj (homotopyShift_complex A n M)) ≫
        ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).commShiftIso n).hom.app
          M.complex := by
  rw [Functor.CommShift.ofIso_commShiftIso_hom_app, Functor.commShiftIso_comp_hom_app,
    homotopyCategoryToDG_commShiftIso_hom_app', eqToHom_map,
    dgHomotopyForget_commShiftIso_hom_app, dgHomotopyForgetShiftIso_hom,
    homotopyForgetComplexIso_inv_app, homotopyForgetComplexIso_hom_app, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans_assoc]
  exact eqToHom_comp_commShiftIso_hom_app_comp_eqToHom _ n (asModule_asObject_complex A M) _ _ _


/-- The third arrow of the triangle of a mapping cone is the negative of the morphism of the
first projection. -/
theorem _root_.CochainComplex.mappingCone.triangle_mor₃_eq {C : Type*} [Category* C]
    [Preadditive C] [HasBinaryBiproducts C] {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    (CochainComplex.mappingCone.triangle φ).mor₃ =
      -Cocycle.homOf ((CochainComplex.mappingCone.fst φ).rightShift 1 0 (zero_add 1)) := by
  refine HomologicalComplex.hom_ext _ _ fun q => ?_
  simp [CochainComplex.mappingCone.triangle, Cocycle.rightShift, Cochain.rightShift_neg]

section Triangulated

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The cone triangle of a morphism of right differential graded modules goes to the triangle
of the mapping cone of its underlying map of complexes**, so it is distinguished. -/
theorem homotopyForgetComplex_coneTriangle_distinguished
    {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) :
    (homotopyForgetComplex A).mapTriangle.obj (homotopyConeTriangle f) ∈
      distTriang (_root_.HomotopyCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) := by
  refine isomorphic_distinguished _
    (_root_.HomotopyCategory.mappingCone_triangleh_distinguished f.toHomologicalComplex) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (eqToIso (congrArg (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (conePackage f).cone_complex)) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (quotient_map_comp_eqToHom rfl (conePackage f).cone_complex _ _
      (hom_f_heq rfl (conePackage f).cone_complex (conePackage f).inclusion_complex)).trans
        (Category.id_comp _)
  · have hp : ∀ q, HEq ((-(conePackage f).projection).toHomologicalComplex.f q)
        ((CochainComplex.mappingCone.triangle f.toHomologicalComplex).mor₃.f q) := fun q =>
      (neg_heq (congrArg (fun C => C.X q) (conePackage f).cone_complex)
        (congrArg (fun C => C.X q) (shiftPackage K).shifted_complex)
        (hom_f_heq (conePackage f).cone_complex (shiftPackage K).shifted_complex
          (conePackage f).projection_complex q)).trans (heq_of_eq (by
            rw [CochainComplex.mappingCone.triangle_mor₃_eq]
            rfl))
    have h := comp_eqToHom_comp_eq
      (((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
        K.complex)
      (quotient_map_comp_eqToHom (conePackage f).cone_complex (shiftPackage K).shifted_complex
        _ _ hp)
    have e₂ : (homotopyForgetComplex A).map ((HomotopyCategory.quotient A).map
        (-(conePackage f).projection) ≫ eqToHom (HomotopyCategory.shiftFunctor_obj A K).symm) =
        (homotopyForgetComplex A).map ((HomotopyCategory.quotient A).map
          (-(conePackage f).projection)) ≫
          eqToHom (congrArg (homotopyForgetComplex A).obj
            (HomotopyCategory.shiftFunctor_obj A K).symm) := by
      rw [Functor.map_comp, eqToHom_map]
    exact ((congrArg (fun m => _ ≫ m) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _)).trans
      ((congrArg₂ (· ≫ ·) e₂ (homotopyForgetComplex_commShiftIso_hom_app A 1 K)).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun m => _ ≫ m)
          (eqToHom_trans_assoc _ _ _)).trans h)))

/-- **Forgetting the action is an exact functor of triangulated categories**: a distinguished
triangle of `K(Mod(A, d))` is isomorphic to the cone triangle of a morphism of modules, and that
goes to the triangle of a mapping cone. -/
instance homotopyForgetComplex_isTriangulated : (homotopyForgetComplex A).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨f, hf⟩ := (HomotopyCategory.quotient A).map_surjective (X := T.obj₁.as)
      (Y := T.obj₂.as) T.mor₁
    obtain ⟨e, -⟩ := exists_iso_of_arrow_iso T (homotopyConeTriangle f) hT
      (homotopyConeTriangle_distinguished f) (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
        simp [homotopyConeTriangle, hf]))
    exact isomorphic_distinguished _ (homotopyForgetComplex_coneTriangle_distinguished A f) _
      ((homotopyForgetComplex A).mapTriangle.mapIso e)

end Triangulated

end Homotopy

end SheafOfModules.DifferentialGradedModule

end

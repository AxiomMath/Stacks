module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexGeneral
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.SupportHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverComplex

/-!
# The Čech double complex of a family of objects with chosen products

Let `C` be a category and `D : ι → C` a family of objects whose finite nonempty products
`D_x = D (x 0) × ⋯ × D (x n)` exist. This file studies the cosimplicial object
`[n] ↦ ∏_{x : Fin (n + 1) → ι} P(D_x)` underlying the Čech complex of a presheaf `P` along `D`
(see `StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/FinalCoverComplex.lean`), and, for a
presheaf of cochain complexes `P`, the cochain complex of cosimplicial objects `a ↦ (P^a)(D_•)`,
the input of the double complex `Crystalline.CosimplicialDoubleComplex.functor`.

## Main definitions

All of this lives in the namespace `Stacks.CechSite.FinalCover`.

* `cosimplicialFunctor D A`, `cosimplicialObject D P` — the cosimplicial object
  `[n] ↦ ∏_x P(D_x)`, whose Moore complex is the Čech complex `(complexFunctor D A).obj P`.
* `doubleComplex D P`, `doubleComplexFunctor D` — for a presheaf of cochain complexes `P`, the
  cochain complex of cosimplicial objects `a ↦ cosimplicialObject D P^a`.
* `rowIsoProduct D P b` — its row `b` is the product of the complexes `P(D_x)`, `x` running over
  the tuples `Fin (b + 1) → ι`.
* `interComparison F c x`, `cosimplicialComparison`, `doubleComplexComparison` — a functor
  `F : C' ⥤ C` with maps `c i : F (D' i) ⟶ D i` induces maps `F (D'_x) ⟶ D_x` and hence a map from
  the cosimplicial object (or double complex) of `P` along `D` to that of `F.op ⋙ P` along `D'`.
* `supportProjections` — support projections on the factors give support projections on the
  cosimplicial object.

## Main results

* `quasiIso_rowMap` — a map of presheaves of complexes which is a quasi-isomorphism on every
  `D_x` is a quasi-isomorphism on every row, when `ι` is finite and the values are abelian.
* `isIso_cosimplicialComparison_app`, `isIso_complexComparison_app` — if every
  `F (D'_x) ⟶ D_x` is an isomorphism, the comparison of cosimplicial objects and of Čech complexes
  is an isomorphism.
* `quasiIso_rowMap_doubleComplexComparison` — if `P` carries every `F (D'_x) ⟶ D_x` to a
  quasi-isomorphism, the comparison of double complexes is a quasi-isomorphism on every row.
* `isZero_homology_of_supportProjections` — the Čech complex of a presheaf with support
  projections is acyclic.
* `hasProduct_fullSubcategory_of_isLimit`, `isIso_interComparison_ι` — products of objects of a
  full subcategory which exist in the ambient category and lie in the subcategory are products in
  the subcategory, preserved by the inclusion.

## References

* [Stacks Project, Tag 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Tag 07L7](https://stacks.math.columbia.edu/tag/07L7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe w v v' v'' u u' u''

namespace Stacks.CechSite.FinalCover

variable {C : Type u} [Category.{v} C] {ι : Type w} (D : ι → C)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]

/-! ### The cosimplicial object -/

section Cosimplicial

variable (A : Type u') [Category.{v'} A] [HasProducts.{w} A]

/-- The cosimplicial object `[n] ↦ ∏_{x : Fin (n + 1) → ι} P(D_x)`, as a functor of the
presheaf `P`. -/
def cosimplicialFunctor : (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  FormalCoproduct.cosimplicialObjectFunctor (simplicialObject D)

variable {A}

/-- The cosimplicial object `[n] ↦ ∏_{x : Fin (n + 1) → ι} P(D_x)` of a presheaf `P`. -/
abbrev cosimplicialObject (P : Cᵒᵖ ⥤ A) : CosimplicialObject A :=
  (cosimplicialFunctor D A).obj P

variable (P : Cᵒᵖ ⥤ A)

/-- The projection of the degree `n` term of `cosimplicialObject D P` onto the factor indexed by
the tuple `x`, namely the sections of `P` over `inter D x`. -/
def cosimplicialObjectπ (n : SimplexCategory) (x : Fin (n.len + 1) → ι) :
    (cosimplicialObject D P).obj n ⟶ P.obj (op (inter D x)) :=
  Pi.π _ x

/-- The degree `n` term of `cosimplicialObject D P` is the product of the sections of `P` over
the objects `inter D x`, with projections `cosimplicialObjectπ D P n`. -/
def isLimitCosimplicialObjectFan (n : SimplexCategory) :
    IsLimit (Fan.mk ((cosimplicialObject D P).obj n) (cosimplicialObjectπ D P n)) :=
  productIsProduct _

/-- Two morphisms into a term of `cosimplicialObject D P` agree as soon as they agree after every
projection. -/
@[ext]
theorem cosimplicialObject_hom_ext {n : SimplexCategory} {T : A}
    {f g : T ⟶ (cosimplicialObject D P).obj n}
    (h : ∀ x, f ≫ cosimplicialObjectπ D P n x = g ≫ cosimplicialObjectπ D P n x) : f = g :=
  Pi.hom_ext _ _ h

/-- The morphism into a term of `cosimplicialObject D P` determined by a family of morphisms into
the factors. -/
def cosimplicialObjectLift {n : SimplexCategory} {T : A}
    (f : ∀ x : Fin (n.len + 1) → ι, T ⟶ P.obj (op (inter D x))) :
    T ⟶ (cosimplicialObject D P).obj n :=
  Pi.lift f

/-- The components of `cosimplicialObjectLift`. -/
@[reassoc (attr := simp)]
theorem cosimplicialObjectLift_comp_π {n : SimplexCategory} {T : A}
    (f : ∀ x : Fin (n.len + 1) → ι, T ⟶ P.obj (op (inter D x))) (x : Fin (n.len + 1) → ι) :
    cosimplicialObjectLift D P f ≫ cosimplicialObjectπ D P n x = f x :=
  Pi.lift_π _ _

/-- **The structure maps of `cosimplicialObject D P`, componentwise**: for `f : m ⟶ n`, the
component at the tuple `y` of `K(f)` is the restriction along `inter D y ⟶ inter D (y ∘ f)` of
the component at `y ∘ f`. -/
@[reassoc (attr := simp)]
theorem cosimplicialObject_map_comp_π {m n : SimplexCategory} (f : m ⟶ n)
    (y : Fin (n.len + 1) → ι) :
    (cosimplicialObject D P).map f ≫ cosimplicialObjectπ D P n y =
      cosimplicialObjectπ D P m (y ∘ f.toOrderHom) ≫ P.map (interMap D y f.toOrderHom).op := by
  simp only [cosimplicialObject, cosimplicialFunctor,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_π _ _

/-- The cosimplicial object functor on morphisms, componentwise. -/
@[reassoc (attr := simp)]
theorem cosimplicialFunctor_map_app_comp_π {P P' : Cᵒᵖ ⥤ A} (φ : P ⟶ P') (n : SimplexCategory)
    (x : Fin (n.len + 1) → ι) :
    ((cosimplicialFunctor D A).map φ).app n ≫ cosimplicialObjectπ D P' n x =
      cosimplicialObjectπ D P n x ≫ φ.app (op (inter D x)) :=
  Limits.Pi.map_π (f := fun y : Fin (n.len + 1) → ι ↦ P.obj (op (inter D y)))
    (g := fun y ↦ P'.obj (op (inter D y))) (fun y ↦ φ.app (op (inter D y))) x

variable [Preadditive A]

/-- The Moore complex of `cosimplicialObject D P` is the Čech complex of `P` along `D`. -/
theorem alternatingCofaceMapComplex_obj_cosimplicialObject :
    (alternatingCofaceMapComplex A).obj (cosimplicialObject D P) = (complexFunctor D A).obj P :=
  rfl

/-- The cosimplicial object functor is additive. -/
instance cosimplicialFunctor_additive : (cosimplicialFunctor D A).Additive where
  map_add {P Q φ ψ} := by
    refine NatTrans.ext (funext fun n ↦ cosimplicialObject_hom_ext D Q fun x ↦ ?_)
    simp only [NatTrans.app_add, Preadditive.add_comp, Preadditive.comp_add,
      cosimplicialFunctor_map_app_comp_π]

end Cosimplicial

/-! ### The double complex of a presheaf of cochain complexes -/

section DoubleComplex

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]

/-- **The cochain complex of cosimplicial objects of a presheaf of cochain complexes** `P`: in
degree `a` it is the cosimplicial object `[n] ↦ ∏_x P^a(D_x)`, with the differential induced by
the differentials of `P`. -/
def doubleComplex (P : Cᵒᵖ ⥤ CochainComplex A ℕ) : CochainComplex (CosimplicialObject A) ℕ where
  X a := cosimplicialObject D (P ⋙ HomologicalComplex.eval A _ a)
  d a b :=
    (cosimplicialFunctor D A).map (Functor.whiskerLeft P (HomologicalComplex.dNatTrans A _ a b))
  shape a b h := by
    have : Functor.whiskerLeft P (HomologicalComplex.dNatTrans A _ a b) = 0 := by
      ext U
      exact (P.obj U).shape a b h
    rw [this, Functor.map_zero]
  d_comp_d' a b c _ _ := by
    rw [← Functor.map_comp]
    have : Functor.whiskerLeft P (HomologicalComplex.dNatTrans A _ a b) ≫
        Functor.whiskerLeft P (HomologicalComplex.dNatTrans A _ b c) = 0 := by
      ext U
      exact (P.obj U).d_comp_d a b c
    rw [this, Functor.map_zero]

/-- The degree `a` term of `doubleComplex D P` is the cosimplicial object of `P^a`. -/
theorem doubleComplex_X (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (a : ℕ) :
    (doubleComplex D P).X a = cosimplicialObject D (P ⋙ HomologicalComplex.eval A _ a) :=
  rfl

/-- The differential of `doubleComplex D P` is induced by the differential of `P`. -/
theorem doubleComplex_d (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (a b : ℕ) :
    (doubleComplex D P).d a b =
      (cosimplicialFunctor D A).map
        (Functor.whiskerLeft P (HomologicalComplex.dNatTrans A _ a b)) :=
  rfl

/-- The morphism of double complexes induced by a morphism of presheaves of cochain
complexes. -/
def doubleComplexMap {P P' : Cᵒᵖ ⥤ CochainComplex A ℕ} (ρ : P ⟶ P') :
    doubleComplex D P ⟶ doubleComplex D P' where
  f a := (cosimplicialFunctor D A).map (Functor.whiskerRight ρ (HomologicalComplex.eval A _ a))
  comm' a b _ := ((cosimplicialFunctor D A).map_comp _ _).symm.trans
    ((congrArg (cosimplicialFunctor D A).map
      (NatTrans.ext (funext fun U ↦ (ρ.app U).comm a b))).trans
      ((cosimplicialFunctor D A).map_comp _ _))

/-- The degree `a` component of `doubleComplexMap D ρ`. -/
theorem doubleComplexMap_f {P P' : Cᵒᵖ ⥤ CochainComplex A ℕ} (ρ : P ⟶ P') (a : ℕ) :
    (doubleComplexMap D ρ).f a =
      (cosimplicialFunctor D A).map (Functor.whiskerRight ρ (HomologicalComplex.eval A _ a)) :=
  rfl

variable (A) in
/-- `doubleComplex D P`, as a functor of the presheaf of cochain complexes `P`. -/
def doubleComplexFunctor :
    (Cᵒᵖ ⥤ CochainComplex A ℕ) ⥤ CochainComplex (CosimplicialObject A) ℕ where
  obj := doubleComplex D
  map := doubleComplexMap D
  map_id _ := HomologicalComplex.hom_ext _ _ fun _ ↦
    ((cosimplicialFunctor D A).congr_map (Functor.whiskerRight_id' _)).trans
      ((cosimplicialFunctor D A).map_id _)
  map_comp _ _ := HomologicalComplex.hom_ext _ _ fun _ ↦
    ((cosimplicialFunctor D A).congr_map (Functor.whiskerRight_comp _ _ _)).trans
      ((cosimplicialFunctor D A).map_comp _ _)

/-- `doubleComplexFunctor D A` on objects. -/
theorem doubleComplexFunctor_obj (P : Cᵒᵖ ⥤ CochainComplex A ℕ) :
    (doubleComplexFunctor D A).obj P = doubleComplex D P :=
  rfl

/-- `doubleComplexFunctor D A` on morphisms. -/
theorem doubleComplexFunctor_map {P P' : Cᵒᵖ ⥤ CochainComplex A ℕ} (ρ : P ⟶ P') :
    (doubleComplexFunctor D A).map ρ = doubleComplexMap D ρ :=
  rfl

end DoubleComplex

/-! ### The rows of the double complex -/

section Rows

open Crystalline.CosimplicialDoubleComplex

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Abelian A]

/-- Finite products of quasi-isomorphisms of cochain complexes in an abelian category are
quasi-isomorphisms. -/
theorem quasiIso_piMap {J : Type w} [Finite J] {K L : J → CochainComplex A ℕ}
    (g : ∀ j, K j ⟶ L j) [∀ j, QuasiIso (g j)] : QuasiIso (Limits.Pi.map g) := by
  rw [quasiIso_iff]
  intro t
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) t
  have hnat : H.map (Limits.Pi.map g) ≫ piComparison H L =
      piComparison H K ≫ Limits.Pi.map (fun j ↦ H.map (g j)) := by
    refine Limits.Pi.hom_ext _ _ fun j ↦ ?_
    simp only [Category.assoc, Limits.Pi.map_π, piComparison_comp_π_assoc,
      piComparison_comp_π, ← H.map_comp]
  have (j : J) : IsIso (H.map (g j)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap (g j) t))
  have : IsIso (H.map (Limits.Pi.map g) ≫ piComparison H L) := hnat ▸ inferInstance
  exact IsIso.of_isIso_comp_right (H.map (Limits.Pi.map g)) (piComparison H L)

variable (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

/-- The projection of the row `b` of `doubleComplex D P` onto the complex of sections of `P` over
`inter D x`, for a tuple `x : Fin (b + 1) → ι`. -/
def rowπ (b : ℕ) (x : Fin (b + 1) → ι) :
    rowComplex (doubleComplex D P) b ⟶ P.obj (op (inter D x)) where
  f a := cosimplicialObjectπ D (P ⋙ HomologicalComplex.eval A _ a) ⦋b⦌ x
  comm' a a' _ :=
    (cosimplicialFunctor_map_app_comp_π D
      (Functor.whiskerLeft P (HomologicalComplex.dNatTrans A _ a a')) ⦋b⦌ x).symm

/-- The degree `a` component of `rowπ`. -/
theorem rowπ_f (b : ℕ) (x : Fin (b + 1) → ι) (a : ℕ) :
    (rowπ D P b x).f a = cosimplicialObjectπ D (P ⋙ HomologicalComplex.eval A _ a) ⦋b⦌ x :=
  rfl

/-- **The row `b` of `doubleComplex D P` is the product of the complexes of sections of `P` over
the objects `inter D x`**, `x` running over the tuples `Fin (b + 1) → ι`, with projections
`rowπ D P b`. -/
def isLimitRowFan (b : ℕ) : IsLimit (Fan.mk (rowComplex (doubleComplex D P) b) (rowπ D P b)) :=
  HomologicalComplex.isLimitOfEval _ _ fun a ↦
    (isLimitMapConeFanMkEquiv (HomologicalComplex.eval A _ a) _ _).symm
      (isLimitCosimplicialObjectFan D (P ⋙ HomologicalComplex.eval A _ a) ⦋b⦌)

/-- **The row `b` of `doubleComplex D P`** is isomorphic to the product, in cochain complexes, of
the complexes of sections of `P` over the objects `inter D x`, `x : Fin (b + 1) → ι`. -/
def rowIsoProduct (b : ℕ) :
    rowComplex (doubleComplex D P) b ≅ ∏ᶜ fun x : Fin (b + 1) → ι ↦ P.obj (op (inter D x)) :=
  (isLimitRowFan D P b).conePointUniqueUpToIso (productIsProduct _)

/-- The components of `rowIsoProduct` are the projections `rowπ`. -/
@[reassoc (attr := simp)]
theorem rowIsoProduct_hom_comp_π (b : ℕ) (x : Fin (b + 1) → ι) :
    (rowIsoProduct D P b).hom ≫ Pi.π _ x = rowπ D P b x :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk x)

variable {P} {P' : Cᵒᵖ ⥤ CochainComplex A ℕ}

/-- The row maps of `doubleComplexMap D ρ`, componentwise. -/
@[reassoc (attr := simp)]
theorem rowMap_comp_rowπ (ρ : P ⟶ P') (b : ℕ) (x : Fin (b + 1) → ι) :
    rowMap (doubleComplexMap D ρ) b ≫ rowπ D P' b x =
      rowπ D P b x ≫ ρ.app (op (inter D x)) := by
  ext a
  exact cosimplicialFunctor_map_app_comp_π D
    (Functor.whiskerRight ρ (HomologicalComplex.eval A _ a)) ⦋b⦌ x

/-- **The identification of the rows is natural**: under `rowIsoProduct`, the row map of
`doubleComplexMap D ρ` is the product of the components of `ρ`. -/
theorem rowMap_comp_rowIsoProduct_hom (ρ : P ⟶ P') (b : ℕ) :
    rowMap (doubleComplexMap D ρ) b ≫ (rowIsoProduct D P' b).hom =
      (rowIsoProduct D P b).hom ≫ Limits.Pi.map fun x ↦ ρ.app (op (inter D x)) :=
  Limits.Pi.hom_ext _ _ fun x ↦ by simp

/-- A morphism of double complexes which, on the row `b`, is componentwise a quasi-isomorphism
of the factors is a quasi-isomorphism on the row `b`, when `ι` is finite. -/
theorem quasiIso_rowMap_of_comp_rowπ [Finite ι] {C' : Type u''} [Category.{v''} C']
    {D' : ι → C'} [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D' (x a))]
    {P' : C'ᵒᵖ ⥤ CochainComplex A ℕ} (g : doubleComplex D P ⟶ doubleComplex D' P') (b : ℕ)
    (gx : ∀ x : Fin (b + 1) → ι, P.obj (op (inter D x)) ⟶ P'.obj (op (inter D' x)))
    (hg : ∀ x, rowMap g b ≫ rowπ D' P' b x = rowπ D P b x ≫ gx x) [∀ x, QuasiIso (gx x)] :
    QuasiIso (rowMap g b) := by
  have := quasiIso_piMap gx
  refine quasiIso_of_arrow_mk_iso (Limits.Pi.map gx) (rowMap g b)
    (Arrow.isoMk (rowIsoProduct D P b).symm (rowIsoProduct D' P' b).symm ?_)
  dsimp only [Arrow.mk_hom, Iso.symm_hom]
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact Limits.Pi.hom_ext _ _ fun x ↦ by simp [hg]

/-- **The rowwise criterion**: when `ι` is finite, a morphism of presheaves of cochain complexes
which is a quasi-isomorphism on every finite product `inter D x` induces a quasi-isomorphism on
every row of the double complexes. -/
theorem quasiIso_rowMap [Finite ι] (ρ : P ⟶ P')
    (hρ : ∀ (n : ℕ) (x : Fin (n + 1) → ι), QuasiIso (ρ.app (op (inter D x)))) (b : ℕ) :
    QuasiIso (rowMap ((doubleComplexFunctor D A).map ρ) b) :=
  have := hρ b
  quasiIso_rowMap_of_comp_rowπ D (doubleComplexMap D ρ) b (fun x ↦ ρ.app (op (inter D x)))
    (rowMap_comp_rowπ D ρ b)

end Rows

/-! ### Change of category -/

section Comparison

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]

variable {D} {C' : Type u''} [Category.{v''} C'] (F : C' ⥤ C) {D' : ι → C'}
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D' (x a))]
  (c : ∀ i, F.obj (D' i) ⟶ D i)

/-- The comparison map `F (D'_x) ⟶ D_x` induced by maps `c i : F (D' i) ⟶ D i`: its component at
`a` is `F (D'_x) ⟶ F (D' (x a)) ⟶ D (x a)`. -/
def interComparison {n : ℕ} (x : Fin (n + 1) → ι) : F.obj (inter D' x) ⟶ inter D x :=
  interLift D fun a ↦ F.map (interπ D' x a) ≫ c (x a)

/-- The components of `interComparison`. -/
@[reassoc (attr := simp)]
theorem interComparison_comp_interπ {n : ℕ} (x : Fin (n + 1) → ι) (a : Fin (n + 1)) :
    interComparison F c x ≫ interπ D x a = F.map (interπ D' x a) ≫ c (x a) :=
  interLift_comp_interπ D _ a

/-- `interComparison` is compatible with the reindexing maps `interMap`. -/
@[reassoc]
theorem map_interMap_comp_interComparison {n m : ℕ} (y : Fin (n + 1) → ι)
    (h : Fin (m + 1) → Fin (n + 1)) :
    F.map (interMap D' y h) ≫ interComparison F c (y ∘ h) =
      interComparison F c y ≫ interMap D y h :=
  inter_hom_ext D fun a ↦ by
    rw [Category.assoc, Category.assoc, interComparison_comp_interπ, interMap_comp_interπ,
      interComparison_comp_interπ, ← F.map_comp_assoc, interMap_comp_interπ]
    rfl

/-- The degree `n` component of the comparison of cosimplicial objects: on the factor indexed by
`x`, the restriction of `P` along `interComparison F c x`. -/
def cosimplicialComparisonApp (P : Cᵒᵖ ⥤ A) (n : SimplexCategory) :
    (cosimplicialObject D P).obj n ⟶ (cosimplicialObject D' (F.op ⋙ P)).obj n :=
  cosimplicialObjectLift D' (F.op ⋙ P) fun x ↦
    cosimplicialObjectπ D P n x ≫ P.map (interComparison F c x).op

/-- The components of `cosimplicialComparisonApp`. -/
@[reassoc (attr := simp)]
theorem cosimplicialComparisonApp_comp_π (P : Cᵒᵖ ⥤ A) (n : SimplexCategory)
    (x : Fin (n.len + 1) → ι) :
    cosimplicialComparisonApp F c P n ≫ cosimplicialObjectπ D' (F.op ⋙ P) n x =
      cosimplicialObjectπ D P n x ≫ P.map (interComparison F c x).op :=
  cosimplicialObjectLift_comp_π D' (F.op ⋙ P) _ x

/-- If every `interComparison F c x` is an isomorphism, so is `cosimplicialComparisonApp`. -/
theorem isIso_cosimplicialComparisonApp
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsIso (interComparison F c x)) (P : Cᵒᵖ ⥤ A)
    (n : SimplexCategory) : IsIso (cosimplicialComparisonApp F c P n) := by
  have := h n.len
  refine ⟨cosimplicialObjectLift D P fun x ↦
    cosimplicialObjectπ D' (F.op ⋙ P) n x ≫ inv (P.map (interComparison F c x).op),
    cosimplicialObject_hom_ext D P fun x ↦ by simp,
    cosimplicialObject_hom_ext D' (F.op ⋙ P) fun x ↦ by simp⟩

variable (A) in
/-- **The comparison of cosimplicial objects** induced by a functor `F : C' ⥤ C` and maps
`c i : F (D' i) ⟶ D i`: the natural map from the cosimplicial object of `P` along `D` to that of
`F.op ⋙ P` along `D'`, restricting along the maps `interComparison F c x`. -/
def cosimplicialComparison :
    cosimplicialFunctor D A ⟶ (Functor.whiskeringLeft _ _ A).obj F.op ⋙ cosimplicialFunctor D' A
    where
  app P :=
    { app := cosimplicialComparisonApp F c P
      naturality m n f := cosimplicialObject_hom_ext D' (F.op ⋙ P) fun y ↦ by
        simp only [Category.assoc, cosimplicialComparisonApp_comp_π,
          cosimplicialObject_map_comp_π, cosimplicialObject_map_comp_π_assoc,
          cosimplicialComparisonApp_comp_π_assoc, Functor.comp_map, Functor.op_map,
          Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
          Quiver.Hom.unop_op, ← Functor.map_comp, ← op_comp, map_interMap_comp_interComparison] }
  naturality P P' φ := NatTrans.ext (funext fun n ↦ cosimplicialObject_hom_ext D' _ fun y ↦ by
    simp only [NatTrans.comp_app, Functor.comp_map, Functor.whiskeringLeft_obj_map,
      Category.assoc, cosimplicialComparisonApp_comp_π, cosimplicialFunctor_map_app_comp_π,
      cosimplicialComparisonApp_comp_π_assoc, cosimplicialFunctor_map_app_comp_π_assoc,
      Functor.whiskerLeft_app, Functor.op_obj, Functor.whiskeringLeft_obj_obj]
    exact (congrArg (_ ≫ ·) (φ.naturality _)).symm)

/-- The components of `cosimplicialComparison`. -/
theorem cosimplicialComparison_app_app (P : Cᵒᵖ ⥤ A) (n : SimplexCategory) :
    ((cosimplicialComparison A F c).app P).app n = cosimplicialComparisonApp F c P n :=
  rfl

/-- **If every `interComparison F c x` is an isomorphism, the comparison of cosimplicial objects
is an isomorphism.** -/
theorem isIso_cosimplicialComparison_app
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsIso (interComparison F c x)) (P : Cᵒᵖ ⥤ A) :
    IsIso ((cosimplicialComparison A F c).app P) := by
  have (n : SimplexCategory) : IsIso (((cosimplicialComparison A F c).app P).app n) :=
    isIso_cosimplicialComparisonApp F c h P n
  exact NatIso.isIso_of_isIso_app _

section Preadditive

variable [Preadditive A]

variable (A) in
/-- **The comparison of Čech complexes** induced by a functor `F : C' ⥤ C` and maps
`c i : F (D' i) ⟶ D i`: the Moore complex of `cosimplicialComparison`. -/
def complexComparison :
    complexFunctor D A ⟶ (Functor.whiskeringLeft _ _ A).obj F.op ⋙ complexFunctor D' A :=
  Functor.whiskerRight (cosimplicialComparison A F c) (alternatingCofaceMapComplex A)

/-- The components of `complexComparison` are the Moore complex maps of the components of
`cosimplicialComparison`. -/
theorem complexComparison_app (P : Cᵒᵖ ⥤ A) :
    (complexComparison A F c).app P =
      (alternatingCofaceMapComplex A).map ((cosimplicialComparison A F c).app P) :=
  rfl

/-- **If every `interComparison F c x` is an isomorphism, the comparison of Čech complexes is an
isomorphism.** -/
theorem isIso_complexComparison_app
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsIso (interComparison F c x)) (P : Cᵒᵖ ⥤ A) :
    IsIso ((complexComparison A F c).app P) := by
  have := isIso_cosimplicialComparison_app F c h P
  exact Functor.map_isIso (alternatingCofaceMapComplex A) ((cosimplicialComparison A F c).app P)

/-- The comparison of double complexes at a presheaf of cochain complexes `P`: in degree `a` the
comparison of cosimplicial objects of `P^a`. -/
def doubleComplexComparisonApp (P : Cᵒᵖ ⥤ CochainComplex A ℕ) :
    doubleComplex D P ⟶ doubleComplex D' (F.op ⋙ P) where
  f a := (cosimplicialComparison A F c).app (P ⋙ HomologicalComplex.eval A _ a)
  comm' a b _ := ((cosimplicialComparison A F c).naturality
    (Functor.whiskerLeft P (HomologicalComplex.dNatTrans A _ a b))).symm

/-- The degree `a` component of `doubleComplexComparisonApp`. -/
theorem doubleComplexComparisonApp_f (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (a : ℕ) :
    (doubleComplexComparisonApp F c P).f a =
      (cosimplicialComparison A F c).app (P ⋙ HomologicalComplex.eval A _ a) :=
  rfl

variable (A) in
/-- **The comparison of double complexes** induced by a functor `F : C' ⥤ C` and maps
`c i : F (D' i) ⟶ D i`, natural in the presheaf of cochain complexes. -/
def doubleComplexComparison :
    doubleComplexFunctor D A ⟶
      (Functor.whiskeringLeft _ _ (CochainComplex A ℕ)).obj F.op ⋙ doubleComplexFunctor D' A where
  app := doubleComplexComparisonApp F c
  naturality _ _ ρ := HomologicalComplex.hom_ext _ _ fun a ↦
    (cosimplicialComparison A F c).naturality
      (Functor.whiskerRight ρ (HomologicalComplex.eval A _ a))

/-- The components of `doubleComplexComparison`. -/
theorem doubleComplexComparison_app (P : Cᵒᵖ ⥤ CochainComplex A ℕ) :
    (doubleComplexComparison A F c).app P = doubleComplexComparisonApp F c P :=
  rfl

end Preadditive

section Abelian

open Crystalline.CosimplicialDoubleComplex

variable [Abelian A]

/-- **The rows of the comparison of double complexes**: on the row `b`, the comparison is the
product over the tuples `x : Fin (b + 1) → ι` of the restrictions along `interComparison F c x`. -/
@[reassoc (attr := simp)]
theorem rowMap_doubleComplexComparisonApp_comp_rowπ (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (b : ℕ)
    (x : Fin (b + 1) → ι) :
    rowMap (doubleComplexComparisonApp F c P) b ≫ rowπ D' (F.op ⋙ P) b x =
      rowπ D P b x ≫ P.map (interComparison F c x).op := by
  ext a
  exact cosimplicialComparisonApp_comp_π F c (P ⋙ HomologicalComplex.eval A _ a) ⦋b⦌ x

/-- **The rowwise criterion for the comparison of double complexes**: when `ι` is finite and `P`
carries every `interComparison F c x` to a quasi-isomorphism, the comparison of double complexes
is a quasi-isomorphism on every row. -/
theorem quasiIso_rowMap_doubleComplexComparison [Finite ι] (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), QuasiIso (P.map (interComparison F c x).op)) (b : ℕ) :
    QuasiIso (rowMap ((doubleComplexComparison A F c).app P) b) :=
  have := h b
  quasiIso_rowMap_of_comp_rowπ D (doubleComplexComparisonApp F c P) b
    (fun x ↦ P.map (interComparison F c x).op)
    (rowMap_doubleComplexComparisonApp_comp_rowπ F c P b)

end Abelian

end Comparison

/-! ### Support projections -/

section Support

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A] (P : Cᵒᵖ ⥤ A)
  (Q : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
    Set (Fin (n + 1)) → (P.obj (op (inter D x)) ⟶ P.obj (op (inter D x))))
  (hQ_univ : ∀ (n : ℕ) (x : Fin (n + 1) → ι), Q n x Set.univ = 𝟙 _)
  (hQ_empty : ∀ (n : ℕ) (x : Fin (n + 1) → ι), Q n x ∅ = 0)
  (hQ_map : ∀ {m n : ℕ} (h : Fin (m + 1) →o Fin (n + 1)) (y : Fin (n + 1) → ι)
    (Z : Set (Fin (n + 1))),
    P.map (interMap D y h).op ≫ Q n y Z = Q m (y ∘ h) (h ⁻¹' Z) ≫ P.map (interMap D y h).op)

/-- **Support projections on the factors give support projections on the cosimplicial object**:
if every `P(D_x)` carries endomorphisms `Q n x Z` ("the part supported on `Z ⊆ [n]`") with
`Q_{[n]} = 1`, `Q_∅ = 0`, compatible with the restrictions along the reindexings `interMap`, then
their products are support projections on `cosimplicialObject D P`. -/
def supportProjections : Crystalline.SupportProjections (cosimplicialObject D P) where
  proj n Z := cosimplicialObjectLift D P fun x ↦ cosimplicialObjectπ D P n x ≫ Q n.len x Z
  proj_univ n := cosimplicialObject_hom_ext D P fun x ↦ by
    rw [cosimplicialObjectLift_comp_π, hQ_univ, Category.comp_id, Category.id_comp]
  proj_empty n := cosimplicialObject_hom_ext D P fun x ↦ by
    rw [cosimplicialObjectLift_comp_π, hQ_empty, comp_zero, zero_comp]
  map_proj f Z := cosimplicialObject_hom_ext D P fun y ↦ by
    simp only [Category.assoc, cosimplicialObjectLift_comp_π, cosimplicialObject_map_comp_π,
      cosimplicialObject_map_comp_π_assoc, cosimplicialObjectLift_comp_π_assoc, hQ_map]

/-- The components of the support projections `supportProjections`. -/
theorem supportProjections_proj_comp_π (n : SimplexCategory) (Z : Set (Fin (n.len + 1)))
    (x : Fin (n.len + 1) → ι) :
    (supportProjections D P Q hQ_univ hQ_empty hQ_map).proj n Z ≫ cosimplicialObjectπ D P n x =
      cosimplicialObjectπ D P n x ≫ Q n.len x Z :=
  cosimplicialObjectLift_comp_π D P _ x

include hQ_univ hQ_empty hQ_map in
/-- **The Čech complex of a presheaf with support projections on the factors is acyclic**, in
every degree. -/
theorem isZero_homology_of_supportProjections [CategoryWithHomology A] (j : ℕ) :
    IsZero (((complexFunctor D A).obj P).homology j) :=
  (supportProjections D P Q hQ_univ hQ_empty hQ_map).isZero_homology j

end Support

/-! ### Products in a full subcategory -/

section FullSubcategory

variable {Pr : ObjectProperty C}

/-- A limit fan in the ambient category with cone point in the subcategory gives creation of the
limit by the inclusion. -/
private theorem nonempty_createsLimit_and_hasLimit {J : Type*} (G : J → Pr.FullSubcategory)
    {c : Fan fun j ↦ (G j).obj} (hc : IsLimit c) (h : Pr c.pt) :
    Nonempty (CreatesLimit (Discrete.functor G) Pr.ι) ∧ HasLimit (Discrete.functor G ⋙ Pr.ι) :=
  have hc' := (IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete G Pr.ι) c).symm hc
  ⟨⟨createsLimitFullSubcategoryInclusion' (Discrete.functor G) hc' h⟩, ⟨⟨⟨_, hc'⟩⟩⟩⟩

/-- **Products in a full subcategory**: a family of objects of a full subcategory has a product as
soon as it has a limit fan in the ambient category whose cone point lies in the subcategory. -/
theorem hasProduct_fullSubcategory_of_isLimit {J : Type*} (G : J → Pr.FullSubcategory)
    {c : Fan fun j ↦ (G j).obj} (hc : IsLimit c) (h : Pr c.pt) : HasProduct G := by
  obtain ⟨⟨_⟩, _⟩ := nonempty_createsLimit_and_hasLimit G hc h
  exact hasLimit_of_created (Discrete.functor G) Pr.ι

/-- **The inclusion of a full subcategory preserves such products**: if a family of objects of a
full subcategory has a limit fan in the ambient category whose cone point lies in the
subcategory, the inclusion preserves its product. -/
theorem preservesLimit_fullSubcategoryι_of_isLimit {J : Type*} (G : J → Pr.FullSubcategory)
    {c : Fan fun j ↦ (G j).obj} (hc : IsLimit c) (h : Pr c.pt) :
    PreservesLimit (Discrete.functor G) Pr.ι := by
  obtain ⟨⟨_⟩, _⟩ := nonempty_createsLimit_and_hasLimit G hc h
  exact preservesLimit_of_createsLimit_and_hasLimit _ _

variable (D'' : ι → Pr.FullSubcategory)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct fun a ↦ (D'' (x a)).obj]

/-- **The products `inter` of a family in a full subcategory**: if the products of the underlying
objects lie in the subcategory, they are products in the subcategory. -/
theorem hasProduct_inter_fullSubcategory
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), Pr (inter (fun i ↦ (D'' i).obj) x)) (n : ℕ)
    (x : Fin (n + 1) → ι) : HasProduct fun a ↦ D'' (x a) :=
  hasProduct_fullSubcategory_of_isLimit _ (isLimitInterFan (fun i ↦ (D'' i).obj) x) (h n x)

/-- **The inclusion of a full subcategory preserves the products `inter`**: if the products of the
underlying objects of a family in a full subcategory lie in the subcategory, the comparison maps
`interComparison Pr.ι (fun i ↦ 𝟙 _) x` are isomorphisms. -/
theorem isIso_interComparison_ι [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct fun a ↦ D'' (x a)]
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), Pr (inter (fun i ↦ (D'' i).obj) x)) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    IsIso (interComparison (D := fun i ↦ (D'' i).obj) Pr.ι (fun _ ↦ 𝟙 _) x) := by
  have := preservesLimit_fullSubcategoryι_of_isLimit _
    (isLimitInterFan (fun i ↦ (D'' i).obj) x) (h n x)
  have : HasProduct fun a ↦ Pr.ι.obj (D'' (x a)) :=
    inferInstanceAs (HasProduct fun a ↦ (D'' (x a)).obj)
  have e : interComparison (D := fun i ↦ (D'' i).obj) Pr.ι (fun i ↦ 𝟙 _) x =
      piComparison Pr.ι fun a ↦ D'' (x a) :=
    inter_hom_ext _ fun a ↦ by
      rw [interComparison_comp_interπ, Category.comp_id]
      exact (piComparison_comp_π Pr.ι (fun a ↦ D'' (x a)) a).symm
  rw [e]
  exact (PreservesProduct.iso Pr.ι _).isIso_hom

end FullSubcategory

end Stacks.CechSite.FinalCover

end

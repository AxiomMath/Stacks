module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Mat
public import Mathlib.CategoryTheory.Preadditive.SingleObj

/-!
# Matrices over a commutative ring acting on a linear category

Let `A` be a commutative ring and `C` an `A`-linear category with finite biproducts.  A finite
family of copies of an object `X` of `C`, together with a matrix with entries in `A`, defines a
morphism between two finite direct sums of copies of `X`: the entry `a` at `(i, j)` acts by
`a • 𝟙 X` from the `i`-th summand to the `j`-th.  This is the tensor product `X ⊗_A A^ι` of `X`
with a finite free `A`-module with a chosen basis, available in any `A`-linear category without
any monoidal or colimit structure.

The finite free `A`-modules with chosen bases are the objects of `Mat_ (SingleObj A)`, the
matrix category over the preadditive one-object category with endomorphism ring `A`; its
morphisms are matrices with entries in `A`.  This file builds the bifunctor

`matrixAction A C : C ⥤ Mat_ (SingleObj A) ⥤ C`, `(X, ι) ↦ ⨁_{i : ι} X`,

and shows that an additive `A`-linear functor commutes with it.  Totalizing it against a
complex of matrices is what tensoring a complex of `C` with a complex of finite free
`A`-modules means in an `A`-linear category.

## Main definitions

* `CategoryTheory.MatrixAction.realize`: for an object `X` of `C`, the additive functor
  `Mat_ (SingleObj A) ⥤ C`, `ι ↦ ⨁_{i : ι} X`.
* `CategoryTheory.MatrixAction.matrixAction`: the bifunctor `C ⥤ Mat_ (SingleObj A) ⥤ C`.
* `CategoryTheory.MatrixAction.matrixActionCompIso`: an additive `A`-linear functor
  `G : C ⥤ D` commutes with the action, `G (⨁_ι X) ≅ ⨁_ι G X`, naturally in `X` and in `ι`.

## Implementation notes

Mathlib's `CategoryTheory.Mat_.lift` would produce `realize X` from the functor
`SingleObj A ⥤ C`, `a ↦ a • 𝟙 X`, but it asks the target to live in the universe of the source;
the categories of modules this is used for have their objects one universe above their
morphisms, so the functor is written down directly.

Composition in `SingleObj A` is multiplication in the opposite order, `f ≫ g = g * f`; since `A`
is commutative this is invisible in the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C] [HasFiniteBiproducts C]

/-- The entry of a morphism of `Mat_ (SingleObj A)`, read as an element of `A`. -/
abbrev entry {M N : Mat_ (SingleObj A)} (f : M ⟶ N) (i : M.ι) (j : N.ι) : A := f i j

/-- The diagonal entries of the identity matrix are `1`. -/
lemma entry_id_self (M : Mat_ (SingleObj A)) (i : M.ι) : entry A (𝟙 M) i i = 1 := by
  rw [entry, Mat_.id_apply_self]
  rfl

/-- The off-diagonal entries of the identity matrix are `0`. -/
lemma entry_id_of_ne (M : Mat_ (SingleObj A)) {i j : M.ι} (h : i ≠ j) :
    entry A (𝟙 M) i j = 0 := by
  rw [entry, Mat_.id_apply_of_ne _ _ _ h]

/-- An entry of a composite of matrices is the sum over the middle index of the products of
the entries. -/
lemma entry_comp {M N P : Mat_ (SingleObj A)} (f : M ⟶ N) (g : N ⟶ P) (i : M.ι) (k : P.ι) :
    entry A (f ≫ g) i k = ∑ j, entry A f i j * entry A g j k := by
  rw [entry, Mat_.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SingleObj.comp_as_mul]
  exact mul_comm _ _

/-- Entries of a sum of matrices are the sums of the entries. -/
lemma entry_add {M N : Mat_ (SingleObj A)} (f g : M ⟶ N) (i : M.ι) (j : N.ι) :
    entry A (f + g) i j = entry A f i j + entry A g i j := rfl

/-- The matrix of a morphism of `Mat_ (SingleObj A)` acting on the direct sums of copies of an
object `X`: the entry at `(i, j)` acts by scalar multiplication on `X`. -/
def realizeMap (X : C) {M N : Mat_ (SingleObj A)} (f : M ⟶ N) :
    (⨁ fun _ : M.ι => X) ⟶ ⨁ fun _ : N.ι => X :=
  biproduct.matrix fun i j => entry A f i j • 𝟙 X

/-- The `(i, j)` component of `realizeMap A X f` is scalar multiplication by the entry
`entry A f i j` on `X`. -/
@[reassoc (attr := simp)]
lemma ι_realizeMap_π (X : C) {M N : Mat_ (SingleObj A)} (f : M ⟶ N) (i : M.ι) (j : N.ι) :
    biproduct.ι _ i ≫ realizeMap A X f ≫ biproduct.π _ j = entry A f i j • 𝟙 X := by
  simp [realizeMap]

/-- The identity matrix acts as the identity on `⨁_{i : ι} X`. -/
lemma realizeMap_id (X : C) (M : Mat_ (SingleObj A)) :
    realizeMap A X (𝟙 M) = 𝟙 _ := by
  ext j i
  rw [ι_realizeMap_π, Category.id_comp]
  by_cases h : i = j
  · subst h
    rw [entry_id_self, one_smul, biproduct.ι_π_self]
  · rw [entry_id_of_ne A M h, zero_smul, biproduct.ι_π_ne _ h]

omit [Linear A C] in
/-- An entry of a composite of two morphisms between finite biproducts is the sum over the
middle index of the products of the entries. -/
lemma ι_comp_π_eq_sum {ι κ μ : Type} [Finite ι] [Fintype κ] [Finite μ]
    {f : ι → C} {g : κ → C} {h : μ → C} (φ : (⨁ f) ⟶ ⨁ g) (ψ : (⨁ g) ⟶ ⨁ h) (i : ι) (k : μ) :
    biproduct.ι f i ≫ (φ ≫ ψ) ≫ biproduct.π h k =
      ∑ j, (biproduct.ι f i ≫ φ ≫ biproduct.π g j) ≫ (biproduct.ι g j ≫ ψ ≫ biproduct.π h k) := by
  classical
  have : φ ≫ ψ = φ ≫ (∑ j, biproduct.π g j ≫ biproduct.ι g j) ≫ ψ := by
    rw [biproduct.total, Category.id_comp]
  rw [this, Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_sum]
  simp only [Category.assoc]

/-- The action of matrices is compatible with composition: the composite of two matrices acts
as the composite of their actions. -/
lemma realizeMap_comp (X : C) {M N P : Mat_ (SingleObj A)} (f : M ⟶ N) (g : N ⟶ P) :
    realizeMap A X (f ≫ g) = realizeMap A X f ≫ realizeMap A X g := by
  ext k i
  rw [ι_comp_π_eq_sum, ι_realizeMap_π, entry_comp, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ι_realizeMap_π, ι_realizeMap_π, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    smul_smul]

/-- **The realization of finite free `A`-modules with chosen bases as direct sums of copies of
an object `X`.**  The object `ι` goes to `⨁_{i : ι} X` and a matrix with entries in `A` acts
entrywise by scalar multiplication. -/
abbrev realize (X : C) : Mat_ (SingleObj A) ⥤ C where
  obj M := ⨁ fun _ : M.ι => X
  map f := realizeMap A X f
  map_id M := realizeMap_id A X M
  map_comp f g := realizeMap_comp A X f g

/-- Morphisms between realizations are determined by their matrix entries. -/
@[ext]
lemma realize_hom_ext {X X' : C} {M N : Mat_ (SingleObj A)}
    {φ ψ : (realize A X).obj M ⟶ (realize A X').obj N}
    (h : ∀ i j, biproduct.ι _ i ≫ φ ≫ biproduct.π _ j = biproduct.ι _ i ≫ ψ ≫ biproduct.π _ j) :
    φ = ψ :=
  biproduct.hom_ext _ _ fun j => biproduct.hom_ext' _ _ fun i => by
    simpa only [Category.assoc] using h i j

/-- The realization `ι ↦ ⨁_{i : ι} X` is an additive functor: a sum of matrices acts as the sum
of their actions. -/
instance (X : C) : (realize A X).Additive where
  map_add {M N} f g := by
    ext i j
    simp only [ι_realizeMap_π, Preadditive.add_comp, Preadditive.comp_add,
      entry_add, add_smul]

/-- A morphism `X ⟶ X'` of `C` induces a natural transformation of the realizations, by acting
on every summand. -/
@[simps]
def realizeNatTrans {X X' : C} (φ : X ⟶ X') : realize A X ⟶ realize A X' where
  app M := biproduct.map fun _ => φ
  naturality M N f := by
    ext i j
    simp only [Category.assoc, biproduct.map_π, ι_realizeMap_π_assoc,
      Linear.smul_comp, Category.id_comp, biproduct.ι_map_assoc]
    rw [ι_realizeMap_π, Linear.comp_smul, Category.comp_id]

/-- **The action of finite free `A`-modules with chosen bases on an `A`-linear category**,
`(X, ι) ↦ ⨁_{i : ι} X`, as a bifunctor `C ⥤ Mat_ (SingleObj A) ⥤ C`. -/
abbrev matrixAction : C ⥤ Mat_ (SingleObj A) ⥤ C where
  obj X := realize A X
  map φ := realizeNatTrans A φ
  map_id X := by
    ext M : 2
    simp only [realizeNatTrans_app, NatTrans.id_app]
    refine realize_hom_ext A fun i j => ?_
    simp
  map_comp φ ψ := by
    ext M : 2
    simp only [realizeNatTrans_app, NatTrans.comp_app]
    refine realize_hom_ext A fun i j => ?_
    simp

/-- The matrix action is additive in the object of `C`. -/
instance : (matrixAction A (C := C)).Additive where
  map_add {X Y} φ ψ := by
    ext M : 2
    refine realize_hom_ext A fun i j => ?_
    rw [NatTrans.app_add, Preadditive.add_comp, Preadditive.comp_add]
    simp only [realizeNatTrans_app]
    by_cases h : i = j
    · subst h
      simp
    · simp

/-- For each object `X`, the functor `ι ↦ ⨁_{i : ι} X` is additive. -/
instance (X : C) : ((matrixAction A (C := C)).obj X).Additive :=
  inferInstanceAs (realize A X).Additive


section Exactness

variable (M : Mat_ (SingleObj A))

/-- For each finite free `A`-module `M` with a chosen basis, the functor `X ↦ ⨁_{i : M.ι} X`
is additive. -/
instance : ((matrixAction A (C := C)).flip.obj M).Additive where
  map_add {X Y} φ ψ := by
    refine realize_hom_ext A fun i j => ?_
    simp only [Functor.flip_obj_map, realizeNatTrans_app, Preadditive.add_comp,
      Preadditive.comp_add]
    by_cases h : i = j
    · subst h
      simp
    · simp

/-- `X ↦ ⨁_{i : ι} X` is the limit of the constant diagram on the discrete category `ι`. -/
def matrixActionFlipIsoConstLim :
    (matrixAction A (C := C)).flip.obj M ≅ Functor.const (Discrete M.ι) ⋙ lim :=
  NatIso.ofComponents
    (fun X => biproduct.isoProduct (fun _ : M.ι => X) ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl X))
    (fun {X Y} φ => by
      refine limit.hom_ext fun ⟨i⟩ => ?_
      simp [biproduct.isoProduct_hom])

/-- `X ↦ ⨁_{i : ι} X` is the colimit of the constant diagram on the discrete category `ι`. -/
def matrixActionFlipIsoConstColim :
    (matrixAction A (C := C)).flip.obj M ≅ Functor.const (Discrete M.ι) ⋙ colim :=
  NatIso.ofComponents
    (fun X => biproduct.isoCoproduct (fun _ : M.ι => X) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl X))
    (fun {X Y} φ => by
      rw [← cancel_epi (biproduct.isoCoproduct (fun _ : M.ι => X)).inv]
      refine Sigma.hom_ext _ _ fun i => ?_
      simp [biproduct.isoCoproduct_inv])

/-- Tensoring with a finite free `A`-module preserves finite limits. -/
instance : PreservesFiniteLimits ((matrixAction A (C := C)).flip.obj M) := by
  have := (constLimAdj (J := Discrete M.ι) (C := C)).rightAdjoint_preservesLimits.{0, 0}
  have : PreservesFiniteLimits (lim : (Discrete M.ι ⥤ C) ⥤ C) :=
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  exact preservesFiniteLimits_of_natIso (matrixActionFlipIsoConstLim A M).symm

/-- Tensoring with a finite free `A`-module preserves finite colimits. -/
instance : PreservesFiniteColimits ((matrixAction A (C := C)).flip.obj M) := by
  have := (colimConstAdj (J := Discrete M.ι) (C := C)).leftAdjoint_preservesColimits.{0, 0}
  have : PreservesFiniteColimits (colim : (Discrete M.ι ⥤ C) ⥤ C) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  exact preservesFiniteColimits_of_natIso (matrixActionFlipIsoConstColim A M).symm

end Exactness

section Functoriality

variable {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasFiniteBiproducts D]
  (G : C ⥤ D) [G.Additive] [G.Linear A]

/-- **An additive `A`-linear functor commutes with the matrix action**: `G (⨁_ι X) ≅ ⨁_ι G X`,
the comparison being the canonical one of a functor preserving finite biproducts. -/
def realizeCompIso (X : C) : realize A X ⋙ G ≅ realize A (G.obj X) :=
  NatIso.ofComponents (fun M => G.mapBiproduct fun _ : M.ι => X) fun {M N} f => by
    classical
    refine biproduct.hom_ext _ _ fun k => ?_
    simp only [Functor.comp_map, Category.assoc, Functor.mapBiproduct_hom, biproduct.lift_π,
      ← G.map_comp, realizeMap, biproduct.matrix_π, biproduct.desc_eq,
      Functor.map_sum, Linear.comp_smul, Category.comp_id, Functor.map_smul,
      Preadditive.comp_sum, biproduct.lift_π]

end Functoriality

end CategoryTheory.MatrixAction

end

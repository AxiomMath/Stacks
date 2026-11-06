module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# Positive-degree Čech cohomology of an injective presheaf

Let `U : ι → C` be a family of objects of a category with finite products and let `A` be an
abelian category with enough injectives and with products of the relevant sizes. This file
proves that the Čech cohomology objects `Ȟ^n(U, P)` of a presheaf `P : Cᵒᵖ ⥤ A` which is
injective in the presheaf category vanish for every `n > 0`. This is the step of
[Stacks, Tag 01EP] which uses injectivity, in the generality of a presheaf category; the tag
itself asks for it for an injective *sheaf* of modules on a ringed space, which needs in
addition that such a sheaf is injective as a presheaf of modules (Stacks Tag 015Z and the
sheafification adjunction) and the identification of the module-valued Čech complex of a
covering of an open `V` with the one taken in the slice category over `V`. Neither of those two
steps is carried out here.

The *cofree* presheaf `cofree obj val` on a family of objects `obj : κ → C` with values
`val : κ → A` is the product over `k` of the presheaves `W ↦ ∏_{obj k ⟶ W} val k`. Its Čech
complex is, degreewise, the product of the `val k` indexed by the pairs consisting of an index
`k` and a tuple of `n + 1` factorisations of `obj k` through members of the family `U`, and its
differential is the alternating sum of the face maps of those tuples. Prepending a factorisation
to a tuple is a contracting homotopy, so its positive-degree Čech cohomology vanishes, and an
injective presheaf is a retract of a cofree one. This is dual to the argument of the Stacks
Project, which identifies `Č^•(U, P)` with `Hom_{PMod}(K(U)_•, P)` for a chain complex `K(U)_•`
of presheaves built from extensions by zero (Tag 01EL).

## Main definitions

* `Stacks.CategoryTheory.CechComplex.cofreeOne V J` is the cofree presheaf on a single object.
* `Stacks.CategoryTheory.CechComplex.cofree obj val` is the cofree presheaf on a family, and
  `cofreeDesc` turns a family of morphisms `Q.obj (op (obj k)) ⟶ val k` into a morphism of
  presheaves `Q ⟶ cofree obj val`.
* `Stacks.CategoryTheory.CechComplex.thru U V` is the type of factorisations of `V` through a
  member of the family `U`; for open subsets of a space it is the set of indices `i` with
  `V ≤ U i`.
* `Stacks.CategoryTheory.CechComplex.cofreeProj` is the projection of the Čech complex of a
  cofree presheaf onto the factor indexed by such a tuple, and
  `Stacks.CategoryTheory.CechComplex.cofreeContraction` is the contracting homotopy.

## Main results

* `Stacks.CategoryTheory.ShortComplex.exact_of_contraction`: a short complex whose middle
  identity splits as `S.g ≫ a + b ≫ S.f` is exact.
* `Stacks.CategoryTheory.CechComplex.d_comp_cofreeProj`: the Čech differential of a cofree
  presheaf is the alternating sum of the face maps of the tuples of factorisations.
* `Stacks.CategoryTheory.CechComplex.d_comp_cofreeContraction_add`: the contraction identity.
* `Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_cofree`: positive-degree Čech
  cohomology of a cofree presheaf vanishes.
* `Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract_of_isZero`: a
  retract of a presheaf whose Čech cohomology vanishes in a degree has vanishing Čech
  cohomology in that degree.
* `Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract`: positive-degree
  Čech cohomology of a retract of a cofree presheaf vanishes.
* `Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_injective` and its primed
  variant: positive-degree Čech cohomology of an injective presheaf vanishes.

## Implementation notes

The index type `ι` of the family lives in its own universe `w`, as in
`StacksFrontier/CategoryTheory/Sites/CechComplex.lean`, and the only hypothesis on `A` that it
imposes is `HasProducts.{w} A`; there is no smallness assumption and no reindexing of the Čech
complex. The index type `κ` of the cofree presheaf lives in its own universe `t`, and
`isZero_homology_cechComplex_of_injective` asks only that the family hit every object of `C`,
so that `κ` may be taken small when the objects of `C` are. Taking `κ` to be the objects of `C`
themselves gives `isZero_homology_cechComplex_of_injective'`, at the price of
`HasProducts.{u} A`.

`cofree obj val` is assembled as a pointwise product of the single-object cofree presheaves
`cofreeOne (obj k) (val k)`, and each of those is the composite of `coyoneda.obj (op (obj k))`
with the power functor `cofreePower (val k)`.

## References

* [Stacks Project, Tag 01EL](https://stacks.math.columbia.edu/tag/01EL)
* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v v' u u'

namespace Stacks.CategoryTheory

/-! ### A contraction criterion for exactness -/

section Contraction

variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- If the identity of the middle object of a short complex `S` splits as a sum
`S.g ≫ a + b ≫ S.f`, then `S` is exact. -/
theorem ShortComplex.exact_of_contraction (S : ShortComplex A) [S.HasHomology]
    (a : S.X₃ ⟶ S.X₂) (b : S.X₂ ⟶ S.X₁) (w : S.g ≫ a + b ≫ S.f = 𝟙 S.X₂) : S.Exact := by
  rw [ShortComplex.exact_iff_epi_toCycles]
  have key : (S.iCycles ≫ b) ≫ S.f = S.iCycles := by
    have h := congrArg (S.iCycles ≫ ·) w
    simp only [Preadditive.comp_add, Category.comp_id, ← Category.assoc, S.iCycles_g,
      zero_comp] at h
    simpa using h
  exact @IsSplitEpi.epi _ _ _ _ _ ⟨⟨S.iCycles ≫ b, by
    rw [← cancel_mono S.iCycles, Category.assoc, S.toCycles_i, key, Category.id_comp]⟩⟩

end Contraction

/-! ### Omitting an entry of an extended tuple -/

/-- Omitting the first entry of a tuple extended by `k₀` gives the tuple back. -/
theorem cons_comp_succAbove_zero {α : Type*} {n : ℕ} (k₀ : α) (y : Fin (n + 1) → α) :
    Fin.cons k₀ y ∘ (0 : Fin (n + 2)).succAbove = y :=
  funext fun a ↦ by rw [Function.comp_apply, Fin.succAbove_zero_apply, Fin.cons_succ]

namespace CechComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] {κ : Type t}

/-! ### Cofree presheaves -/

section Cofree

/-- The `S`-fold power of an object `J`, as a functor of `S` contravariant in the indexing
type: it sends a type `S` to the product of copies of `J` indexed by `S`, and a map of types
to the corresponding reindexing of the product. -/
@[simps]
noncomputable def cofreePower [HasProducts.{v} A] (J : A) : (Type v)ᵒᵖ ⥤ A where
  obj S := ∏ᶜ fun _ : S.unop ↦ J
  map f := Limits.Pi.lift fun s ↦ Limits.Pi.π _ (f.unop s)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

section One

variable [HasProducts.{v} A] (V : C) (J : A)

/-- The cofree presheaf on a single object `V` with value `J`: it sends `W` to the product of
copies of `J` indexed by the morphisms `V ⟶ W`. It corepresents evaluation at `V`, in the
sense that a morphism of presheaves `Q ⟶ cofreeOne V J` is the same thing as a morphism
`Q.obj (op V) ⟶ J`. -/
noncomputable def cofreeOne : Cᵒᵖ ⥤ A := (coyoneda.obj (op V)).op ⋙ cofreePower J

/-- The projection of `(cofreeOne V J).obj (op W)` onto the copy of `J` indexed by a morphism
`g : V ⟶ W`. -/
noncomputable def cofreeOneπ {W : C} (g : V ⟶ W) : (cofreeOne V J).obj (op W) ⟶ J :=
  Limits.Pi.π _ g

/-- Morphisms into `(cofreeOne V J).obj (op W)` agree if all their projections agree. -/
@[ext]
theorem cofreeOne_obj_hom_ext {W : C} {T : A} {f g : T ⟶ (cofreeOne V J).obj (op W)}
    (h : ∀ a : V ⟶ W, f ≫ cofreeOneπ V J a = g ≫ cofreeOneπ V J a) : f = g :=
  Limits.Pi.hom_ext _ _ h

/-- Restriction in `cofreeOne V J` followed by a projection is the projection indexed by the
composite. -/
@[reassoc (attr := simp)]
theorem cofreeOne_map_comp_cofreeOneπ {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : V ⟶ Y.unop) :
    (cofreeOne V J).map f ≫ cofreeOneπ V J g = cofreeOneπ V J (g ≫ f.unop) :=
  Limits.Pi.lift_comp_π _ _

/-- The morphism into `(cofreeOne V J).obj (op W)` determined by a family of morphisms into
`J` indexed by the morphisms `V ⟶ W`. -/
noncomputable def cofreeOneLift {W : C} {T : A} (f : (V ⟶ W) → (T ⟶ J)) :
    T ⟶ (cofreeOne V J).obj (op W) :=
  Limits.Pi.lift f

/-- The projections of `cofreeOneLift V J f` are the members of the family `f`. -/
@[reassoc (attr := simp)]
theorem cofreeOneLift_comp_cofreeOneπ {W : C} {T : A} (f : (V ⟶ W) → (T ⟶ J)) (g : V ⟶ W) :
    cofreeOneLift V J f ≫ cofreeOneπ V J g = f g :=
  Limits.Pi.lift_comp_π _ _

end One

variable [HasProducts.{t} A] [HasProducts.{v} A] (obj : κ → C) (val : κ → A)

/-- The cofree presheaf on a family of objects `obj : κ → C` with values `val : κ → A`: the
product, over `k : κ`, of the cofree presheaves on the single objects `obj k`. A morphism of
presheaves `Q ⟶ cofree obj val` is the same thing as a family of morphisms
`Q.obj (op (obj k)) ⟶ val k` (see `cofreeDesc`). -/
noncomputable def cofree : Cᵒᵖ ⥤ A where
  obj W := ∏ᶜ fun k ↦ (cofreeOne (obj k) (val k)).obj W
  map f := Limits.Pi.map fun k ↦ (cofreeOne (obj k) (val k)).map f
  map_id _ := Limits.Pi.hom_ext _ _ fun k ↦ by
    rw [Limits.Pi.map_π, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp f g := Limits.Pi.hom_ext _ _ fun k ↦ by
    rw [Limits.Pi.map_π, CategoryTheory.Functor.map_comp, Category.assoc, Limits.Pi.map_π,
      Limits.Pi.map_π_assoc]

/-- The projection of `cofree obj val` onto the cofree presheaf on the single object
`obj k`. -/
noncomputable def cofreeOuterπ (W : Cᵒᵖ) (k : κ) :
    (cofree obj val).obj W ⟶ (cofreeOne (obj k) (val k)).obj W :=
  Limits.Pi.π _ k

/-- Morphisms into `(cofree obj val).obj W` agree if all their projections `cofreeOuterπ`
agree. -/
theorem cofree_obj_outer_hom_ext {W : Cᵒᵖ} {T : A} {f g : T ⟶ (cofree obj val).obj W}
    (h : ∀ k, f ≫ cofreeOuterπ obj val W k = g ≫ cofreeOuterπ obj val W k) : f = g :=
  Limits.Pi.hom_ext _ _ h

/-- Restriction in `cofree obj val` is the restriction in each factor. -/
@[reassoc (attr := simp)]
theorem cofree_map_comp_cofreeOuterπ {X Y : Cᵒᵖ} (f : X ⟶ Y) (k : κ) :
    (cofree obj val).map f ≫ cofreeOuterπ obj val Y k =
      cofreeOuterπ obj val X k ≫ (cofreeOne (obj k) (val k)).map f :=
  Limits.Pi.map_π (fun k ↦ (cofreeOne (obj k) (val k)).map f) k

/-- The projection of `(cofree obj val).obj (op W)` onto the copy of `val k` indexed by a
morphism `g : obj k ⟶ W`. -/
noncomputable def cofreeπ {W : C} (k : κ) (g : obj k ⟶ W) :
    (cofree obj val).obj (op W) ⟶ val k :=
  cofreeOuterπ obj val (op W) k ≫ cofreeOneπ (obj k) (val k) g

/-- Morphisms into `(cofree obj val).obj (op W)` agree if all their projections `cofreeπ`
agree. -/
@[ext]
theorem cofree_obj_hom_ext {W : C} {T : A} {f g : T ⟶ (cofree obj val).obj (op W)}
    (h : ∀ (k : κ) (a : obj k ⟶ W), f ≫ cofreeπ obj val k a = g ≫ cofreeπ obj val k a) :
    f = g := by
  refine cofree_obj_outer_hom_ext obj val fun k ↦
    cofreeOne_obj_hom_ext (obj k) (val k) fun a ↦ ?_
  rw [Category.assoc, Category.assoc]
  exact h k a

/-- Restriction in `cofree obj val` followed by a projection is the projection indexed by the
composite. -/
@[reassoc (attr := simp)]
theorem cofree_map_comp_cofreeπ {X Y : Cᵒᵖ} (f : X ⟶ Y) (k : κ) (g : obj k ⟶ Y.unop) :
    (cofree obj val).map f ≫ cofreeπ obj val k g = cofreeπ obj val k (g ≫ f.unop) := by
  rw [cofreeπ, cofreeπ, cofree_map_comp_cofreeOuterπ_assoc, cofreeOne_map_comp_cofreeOneπ]

/-- The morphism into `(cofree obj val).obj (op W)` determined by a family of morphisms into
the values `val k`, indexed by the morphisms `obj k ⟶ W`. -/
noncomputable def cofreeObjLift {W : C} {T : A}
    (f : ∀ k : κ, (obj k ⟶ W) → (T ⟶ val k)) : T ⟶ (cofree obj val).obj (op W) :=
  Limits.Pi.lift fun k ↦ cofreeOneLift (obj k) (val k) (f k)

/-- The projections of `cofreeObjLift obj val f` are the members of the family `f`. -/
@[reassoc (attr := simp)]
theorem cofreeObjLift_comp_cofreeπ {W : C} {T : A}
    (f : ∀ k : κ, (obj k ⟶ W) → (T ⟶ val k)) (k : κ) (g : obj k ⟶ W) :
    cofreeObjLift obj val f ≫ cofreeπ obj val k g = f k g := by
  rw [cofreeπ, ← Category.assoc, show cofreeObjLift obj val f ≫ cofreeOuterπ obj val (op W) k =
    cofreeOneLift (obj k) (val k) (f k) from Limits.Pi.lift_comp_π _ _,
    cofreeOneLift_comp_cofreeOneπ]

/-- A family of morphisms `Q.obj (op (obj k)) ⟶ val k` induces a morphism of presheaves
`Q ⟶ cofree obj val`: its component at `W` sends a section to the family of its restrictions
along the morphisms `obj k ⟶ W`. -/
noncomputable def cofreeDesc (Q : Cᵒᵖ ⥤ A) (α : ∀ k, Q.obj (op (obj k)) ⟶ val k) :
    Q ⟶ cofree obj val where
  app W := cofreeObjLift obj val fun k g ↦ Q.map g.op ≫ α k
  naturality _ _ f := by
    refine cofree_obj_hom_ext obj val fun k a ↦ ?_
    rw [Category.assoc, cofreeObjLift_comp_cofreeπ, Category.assoc, cofree_map_comp_cofreeπ,
      cofreeObjLift_comp_cofreeπ, ← Category.assoc, ← Q.map_comp]
    simp

/-- The projection of `cofreeDesc obj val Q α` indexed by `k` and `g : obj k ⟶ W` is the
restriction along `g` followed by `α k`. -/
@[reassoc (attr := simp)]
theorem cofreeDesc_app_comp_cofreeπ (Q : Cᵒᵖ ⥤ A) (α : ∀ k, Q.obj (op (obj k)) ⟶ val k)
    {W : C} (k : κ) (g : obj k ⟶ W) :
    (cofreeDesc obj val Q α).app (op W) ≫ cofreeπ obj val k g = Q.map g.op ≫ α k :=
  cofreeObjLift_comp_cofreeπ obj val _ k g

end Cofree

/-! ### The Čech complex of a cofree presheaf -/

section CechCofree

variable [HasProducts.{w} A] [HasFiniteProducts C] {ι : Type w}

/-- `thru U V` is the type of pairs consisting of an index `i` and a morphism `V ⟶ U i`: the
ways in which `V` factors through a member of the family `U`. For a family of open subsets of
a topological space and `V` an open subset, it is the set of indices `i` with `V ≤ U i`. -/
abbrev thru (U : ι → C) (V : C) : Type max w v := Σ i : ι, (V ⟶ U i)

/-- The tuple of indices underlying a tuple of factorisations. -/
def thruIdx {U : ι → C} {V : C} {m : ℕ} (y : Fin m → thru U V) : Fin m → ι := fun a ↦ (y a).1

omit [HasFiniteProducts C] in
/-- Reindexing a tuple of factorisations reindexes its tuple of indices. -/
@[simp]
theorem thruIdx_comp {U : ι → C} {V : C} {m m' : ℕ} (y : Fin m → thru U V)
    (h : Fin m' → Fin m) : thruIdx (y ∘ h) = thruIdx y ∘ h := rfl

omit [HasFiniteProducts C] in
/-- An entry of a tuple of factorisations is recovered from its index and its morphism. -/
@[simp]
theorem thruIdx_sigmaMk {U : ι → C} {V : C} {m : ℕ} (y : Fin m → thru U V) (a : Fin m) :
    (⟨thruIdx y a, (y a).2⟩ : thru U V) = y a := rfl

/-- The morphism `V ⟶ inter U (thruIdx y)` assembled from a tuple of factorisations. -/
noncomputable def thruSec {U : ι → C} {V : C} {m : ℕ} (y : Fin m → thru U V) :
    V ⟶ inter U (thruIdx y) :=
  interLift U fun a ↦ (y a).2

/-- The components of `thruSec y` are the morphisms of the factorisations in `y`. -/
@[reassoc (attr := simp)]
theorem thruSec_comp_interπ {U : ι → C} {V : C} {m : ℕ} (y : Fin m → thru U V) (a : Fin m) :
    thruSec y ≫ interπ U (thruIdx y) a = (y a).2 :=
  interLift_comp_interπ U _ a

/-- Reindexing a tuple of factorisations reindexes the assembled morphism. -/
@[reassoc]
theorem thruSec_comp_interMap {U : ι → C} {V : C} {m m' : ℕ} (y : Fin m → thru U V)
    (h : Fin m' → Fin m) :
    thruSec y ≫ interMap U (thruIdx y) h = thruSec (y ∘ h) :=
  inter_hom_ext U fun a ↦ by
    rw [Category.assoc, interMap_comp_interπ, thruSec_comp_interπ]
    exact (thruSec_comp_interπ (y ∘ h) a).symm

/-- A morphism `a : V ⟶ inter U x` is recovered from the tuple of factorisations it induces. -/
@[simp]
theorem thruSec_ofHom {U : ι → C} {V : C} {m : ℕ} (x : Fin m → ι) (a : V ⟶ inter U x) :
    thruSec (fun b ↦ (⟨x b, a ≫ interπ U x b⟩ : thru U V)) = a :=
  inter_hom_ext U fun b ↦ thruSec_comp_interπ _ b

variable [Preadditive A] [HasProducts.{t} A] [HasProducts.{v} A] (U : ι → C) (obj : κ → C)
  (val : κ → A)

/-- The projection of the degree `n` term of the Čech complex of the cofree presheaf
`cofree obj val` onto the copy of `val k` indexed by a tuple `y` of `n + 1` factorisations of
`obj k` through members of the family `U`: project onto the sections over the intersection
selected by `y`, then onto the factor of the cofree presheaf indexed by `k` and the morphism
`thruSec y`. -/
noncomputable def cofreeProj (n : ℕ) (k : κ) (y : Fin (n + 1) → thru U (obj k)) :
    ((cechComplexFunctor U).obj (cofree obj val)).X n ⟶ val k :=
  π U (cofree obj val) n (thruIdx y) ≫ cofreeπ obj val k (thruSec y)

/-- The morphism into the degree `n` term of the Čech complex of `cofree obj val` determined
by a family of morphisms indexed by an index `k` and a tuple of `n + 1` factorisations.
Together with `cofreeCechLift_comp_cofreeProj` and `cofree_cech_hom_ext` this exhibits the
degree `n` term as the product of the `val k` over those indices. -/
noncomputable def cofreeCechLift {n : ℕ} {T : A}
    (f : ∀ (k : κ), (Fin (n + 1) → thru U (obj k)) → (T ⟶ val k)) :
    T ⟶ ((cechComplexFunctor U).obj (cofree obj val)).X n :=
  lift U (cofree obj val) fun x ↦ cofreeObjLift obj val fun k p ↦
    f k fun a ↦ ⟨x a, p ≫ interπ U x a⟩

/-- The projections of `cofreeCechLift U obj val f` are the members of the family `f`. -/
@[reassoc (attr := simp)]
theorem cofreeCechLift_comp_cofreeProj {n : ℕ} {T : A}
    (f : ∀ (k : κ), (Fin (n + 1) → thru U (obj k)) → (T ⟶ val k)) (k : κ)
    (y : Fin (n + 1) → thru U (obj k)) :
    cofreeCechLift U obj val f ≫ cofreeProj U obj val n k y = f k y := by
  rw [cofreeProj, cofreeCechLift, ← Category.assoc, lift_comp_π, cofreeObjLift_comp_cofreeπ]
  exact congrArg (f k) (funext fun a ↦ by rw [thruSec_comp_interπ, thruIdx_sigmaMk])

/-- Morphisms into the degree `n` term of the Čech complex of `cofree obj val` agree if all
their projections `cofreeProj` agree. -/
@[ext]
theorem cofree_cech_hom_ext {n : ℕ} {T : A}
    {f g : T ⟶ ((cechComplexFunctor U).obj (cofree obj val)).X n}
    (h : ∀ k y, f ≫ cofreeProj U obj val n k y = g ≫ cofreeProj U obj val n k y) : f = g :=
  hom_ext U (cofree obj val) fun x ↦ cofree_obj_hom_ext obj val fun k a ↦ by
    have hk := h k fun b ↦ (⟨x b, a ≫ interπ U x b⟩ : thru U (obj k))
    rw [cofreeProj, thruSec_ofHom, ← Category.assoc, ← Category.assoc] at hk
    exact hk

/-- **The Čech differential of a cofree presheaf.** After the identification of the degree
`n` term with the product of the values of the defining family indexed by the tuples of
factorisations, the differential is the alternating sum of the face maps of those tuples:
all the restriction maps of the cofree presheaf have become reindexings. -/
theorem d_comp_cofreeProj (n : ℕ) (k : κ) (z : Fin (n + 2) → thru U (obj k)) :
    ((cechComplexFunctor U).obj (cofree obj val)).d n (n + 1) ≫
        cofreeProj U obj val (n + 1) k z =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        cofreeProj U obj val n k (z ∘ i.succAbove) := by
  dsimp only [cofreeProj]
  rw [← Category.assoc, d_comp_π, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, Category.assoc, cofree_map_comp_cofreeπ, Quiver.Hom.unop_op,
    thruSec_comp_interMap]
  rfl

/-! ### The contracting homotopy -/

/-- The factorisation prepended by the contracting homotopy. A tuple of factorisations
exhibits `thru U (obj k)` as nonempty, and the chosen element depends only on `k`, because
`Nonempty` is a proposition and proof irrelevance is definitional. -/
noncomputable def cofreePick {n : ℕ} (k : κ) (y : Fin (n + 1) → thru U (obj k)) :
    thru U (obj k) :=
  (⟨y 0⟩ : Nonempty (thru U (obj k))).some

omit [HasFiniteProducts C] [HasProducts.{w} A] [Preadditive A] in
/-- The prepended factorisation does not depend on the tuple that exhibited it: the two
choices are made from proofs of the same proposition, and proof irrelevance is definitional. -/
theorem cofreePick_eq {n m : ℕ} (k : κ) (y : Fin (n + 1) → thru U (obj k))
    (y' : Fin (m + 1) → thru U (obj k)) : cofreePick U obj k y = cofreePick U obj k y' := rfl

/-- The contracting homotopy of the Čech complex of a cofree presheaf: the component at an
index `k` and a tuple `y` is the component of the next degree at the tuple `y` with
`cofreePick U obj k y` prepended. -/
noncomputable def cofreeContraction (n : ℕ) :
    ((cechComplexFunctor U).obj (cofree obj val)).X (n + 1) ⟶
      ((cechComplexFunctor U).obj (cofree obj val)).X n :=
  cofreeCechLift U obj val fun k y ↦
    cofreeProj U obj val (n + 1) k (Fin.cons (cofreePick U obj k y) y)

/-- The projection of the contracting homotopy at `k` and `y` is the projection at `y` with
`cofreePick U obj k y` prepended. -/
@[reassoc (attr := simp)]
theorem cofreeContraction_comp_cofreeProj (n : ℕ) (k : κ)
    (y : Fin (n + 1) → thru U (obj k)) :
    cofreeContraction U obj val n ≫ cofreeProj U obj val n k y =
      cofreeProj U obj val (n + 1) k (Fin.cons (cofreePick U obj k y) y) :=
  cofreeCechLift_comp_cofreeProj U obj val _ k y

/-- **The contraction identity.** In every degree `n + 1` the identity of the Čech complex of
a cofree presheaf is the sum of the two composites with the contracting homotopy. -/
theorem d_comp_cofreeContraction_add (n : ℕ) :
    ((cechComplexFunctor U).obj (cofree obj val)).d (n + 1) (n + 2) ≫
        cofreeContraction U obj val (n + 1) +
      cofreeContraction U obj val n ≫
        ((cechComplexFunctor U).obj (cofree obj val)).d n (n + 1) =
      𝟙 (((cechComplexFunctor U).obj (cofree obj val)).X (n + 1)) := by
  refine cofree_cech_hom_ext U obj val fun k y ↦ ?_
  rw [Preadditive.add_comp, Category.id_comp, Category.assoc,
    cofreeContraction_comp_cofreeProj, d_comp_cofreeProj, Fin.sum_univ_succ,
    cons_comp_succAbove_zero, Category.assoc, d_comp_cofreeProj, Preadditive.comp_sum]
  have hcancel : ∀ j : Fin (n + 2),
      (-1 : ℤ) ^ ((j.succ : Fin (n + 3)) : ℕ) • cofreeProj U obj val (n + 1) k
          (Fin.cons (cofreePick U obj k y) y ∘ (j.succ).succAbove) +
        cofreeContraction U obj val n ≫
          ((-1 : ℤ) ^ (j : ℕ) • cofreeProj U obj val n k (y ∘ j.succAbove)) = 0 := fun j ↦ by
    rw [Fin.cons_comp_succ_succAbove, Preadditive.comp_zsmul, cofreeContraction_comp_cofreeProj,
      Fin.val_succ, pow_succ, mul_neg_one, neg_smul, cofreePick_eq U obj k (y ∘ j.succAbove) y]
    exact neg_add_cancel _
  rw [add_assoc, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ ↦ hcancel j,
    Finset.sum_const_zero, add_zero]
  simp

end CechCofree

/-! ### Vanishing of the positive-degree Čech cohomology of a cofree presheaf -/

section Vanishing

variable [Abelian A] [HasProducts.{w} A] [HasFiniteProducts C] [HasProducts.{t} A]
  [HasProducts.{v} A] {ι : Type w} (U : ι → C) (obj : κ → C) (val : κ → A)

/-- **Positive-degree Čech cohomology of a cofree presheaf vanishes.** -/
theorem isZero_homology_cechComplex_cofree (n : ℕ) (hn : 0 < n) :
    IsZero ((((cechComplexFunctor U).obj (cofree obj val)).homology n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp)]
  exact ShortComplex.exact_of_contraction _ (cofreeContraction U obj val (m + 1))
    (cofreeContraction U obj val m) (d_comp_cofreeContraction_add U obj val m)

end Vanishing

/-! ### Vanishing of the positive-degree Čech cohomology of an injective presheaf -/

section Injective

variable [Abelian A] [HasProducts.{w} A] [HasFiniteProducts C] [HasProducts.{t} A]
  [HasProducts.{v} A] [EnoughInjectives A] {ι : Type w} (U : ι → C) (obj : κ → C)
  (P : Cᵒᵖ ⥤ A)

/-- The cofree presheaf on a family of objects of `C`, with the chosen injective hull of
`P.obj (op (obj k))` as the value at `k`. If the family hits every object of `C` then `P`
embeds into it, see `mono_toCofreeHull`. -/
noncomputable abbrev cofreeHull : Cᵒᵖ ⥤ A :=
  cofree obj fun k ↦ Injective.under (P.obj (op (obj k)))

/-- The canonical morphism from a presheaf into `cofreeHull obj P`, assembled from the
monomorphisms `P.obj (op (obj k)) ⟶ Injective.under (P.obj (op (obj k)))`. -/
noncomputable abbrev toCofreeHull : P ⟶ cofreeHull obj P :=
  cofreeDesc obj _ P fun k ↦ Injective.ι (P.obj (op (obj k)))

omit [HasProducts.{w} A] [HasFiniteProducts C] in
/-- If the family `obj` hits every object of `C`, then `toCofreeHull obj P` is a
monomorphism. -/
theorem mono_toCofreeHull (hobj : ∀ W : C, ∃ k, obj k = W) : Mono (toCofreeHull obj P) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨W⟩
  obtain ⟨k, rfl⟩ := hobj W
  have hfac : (toCofreeHull obj P).app (op (obj k)) ≫
      cofreeπ obj (fun k ↦ Injective.under (P.obj (op (obj k)))) k (𝟙 (obj k)) =
      Injective.ι (P.obj (op (obj k))) := by
    rw [cofreeDesc_app_comp_cofreeπ]
    simp
  exact mono_of_mono_fac hfac

omit [EnoughInjectives A] [HasProducts.{t} A] [HasProducts.{v} A] in
/-- **A retract of a presheaf with vanishing Čech cohomology in a degree has vanishing Čech
cohomology in that degree.** Nothing is assumed about the presheaf `Q` off which `P` splits. -/
theorem isZero_homology_cechComplex_of_retract_of_isZero {Q : Cᵒᵖ ⥤ A} (n : ℕ)
    (hQ : IsZero (((cechComplexFunctor U).obj Q).homology n)) (s : P ⟶ Q) (r : Q ⟶ P)
    (hsr : s ≫ r = 𝟙 P) : IsZero (((cechComplexFunctor U).obj P).homology n) := by
  have hid : HomologicalComplex.homologyMap ((cechComplexFunctor U).map s) n ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map r) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hsr,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  have hz := hQ.eq_zero_of_tgt
    (HomologicalComplex.homologyMap ((cechComplexFunctor U).map s) n)
  exact (IsZero.iff_id_eq_zero _).2 (by rw [← hid, hz, zero_comp])

omit [EnoughInjectives A] in
/-- **Positive-degree Čech cohomology of a retract of a cofree presheaf vanishes.** A presheaf
injective in the presheaf category is such a retract, see
`isZero_homology_cechComplex_of_injective`. -/
theorem isZero_homology_cechComplex_of_retract {val : κ → A} (s : P ⟶ cofree obj val)
    (r : cofree obj val ⟶ P) (hsr : s ≫ r = 𝟙 P) (n : ℕ) (hn : 0 < n) :
    IsZero (((cechComplexFunctor U).obj P).homology n) :=
  isZero_homology_cechComplex_of_retract_of_isZero U P n
    (isZero_homology_cechComplex_cofree U obj val n hn) s r hsr

/-- **Positive-degree Čech cohomology of an injective presheaf vanishes.** This is the step of
[Stacks, Tag 01EP] that uses injectivity: for a presheaf `P` injective in the presheaf
category `Cᵒᵖ ⥤ A`, all the Čech cohomology objects `Ȟ^n(U, P)` vanish for `n > 0`.

The family `obj` is only required to hit every object of `C`, so that its index type may be
taken small enough for the products involved to exist; see
`isZero_homology_cechComplex_of_injective'` for the version indexed by `C` itself. -/
theorem isZero_homology_cechComplex_of_injective (hobj : ∀ W : C, ∃ k, obj k = W)
    [Injective P] (n : ℕ) (hn : 0 < n) :
    IsZero (((cechComplexFunctor U).obj P).homology n) :=
  have := mono_toCofreeHull obj P hobj
  isZero_homology_cechComplex_of_retract U obj P (toCofreeHull obj P)
    (Injective.factorThru (𝟙 P) (toCofreeHull obj P)) (Injective.comp_factorThru _ _) n hn

omit [HasProducts.{t} A] in
/-- **Positive-degree Čech cohomology of an injective presheaf vanishes**, with the cofree
presheaf taken over the family of all objects of `C`. -/
theorem isZero_homology_cechComplex_of_injective' [HasProducts.{u} A] [Injective P] (n : ℕ)
    (hn : 0 < n) : IsZero (((cechComplexFunctor U).obj P).homology n) :=
  isZero_homology_cechComplex_of_injective U (id : C → C) P (fun W ↦ ⟨W, rfl⟩) n hn

end Injective

end CechComplex

end Stacks.CategoryTheory

end

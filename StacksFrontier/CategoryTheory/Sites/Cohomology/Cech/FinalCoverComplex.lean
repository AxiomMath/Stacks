module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# The Čech complex of a family of objects with chosen products

Let `C` be a category and `D : ι → C` a family of objects such that for every tuple
`x : Fin (n + 1) → ι` the product `D_x = D (x 0) × ⋯ × D (x n)` exists. For a presheaf
`P : Cᵒᵖ ⥤ A` with values in a preadditive category with products, the *Čech complex* of `P`
along `D` is the cochain complex whose degree `n` term is

`∏_{x : Fin (n + 1) → ι} P(D_x)`

with the alternating sum of the restrictions along the face maps as differential. When the family
covers the final object of a site (`CategoryTheory.GrothendieckTopology.CoversTop`), this is the
Čech complex of the covering of the final sheaf by the representables of the `D i`.

Mathlib's `CategoryTheory.cechComplexFunctor` is the same construction, but it asks for all finite
products in `C`, including a terminal object; the sites to which this file is applied (the big
crystalline site, for instance) have neither. Only the products of the members of the family are
asked for here, exactly as `Stacks.CechSite.cechComplexFunctor` asks only for the fibre products
of a family of morphisms with fixed target.

## Main definitions

All of this lives in the namespace `Stacks.CechSite.FinalCover`.

* `simplicialObject D` — the simplicial formal coproduct `[n] ↦ ∐_{x} D_x`.
* `complexFunctor D` — the Čech complex, as a functor of the presheaf.
* `inter D x`, `interπ`, `interLift`, `interMap` — the products `D_x` and their structure maps.
* `π D P n x`, `lift D P f` — the projections of the degree `n` term onto its factors and the
  universal map into it.

## Main results

* `d_comp_π` — the Čech differential, componentwise: the alternating sum of the restrictions
  along the face maps `Fin.succAbove i`.
* `map_f_π` — the action of the Čech complex functor on morphisms of presheaves, componentwise.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03OW](https://stacks.math.columbia.edu/tag/03OW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v' u u'

namespace Stacks.CechSite.FinalCover

variable {C : Type u} [Category.{v} C] {ι : Type w} (D : ι → C)

/-! ### The simplicial formal coproduct of the products of the members of the family -/

/-- The formal coproduct, indexed by the `α`-tuples of members of the family, of their
products. -/
noncomputable def formalCoproduct (α : Type) [∀ x : α → ι, HasProduct (fun a ↦ D (x a))] :
    FormalCoproduct.{w} C where
  I := α → ι
  obj x := ∏ᶜ (fun a ↦ D (x a))

/-- Reindexing tuples induces the corresponding map between the formal coproducts of
products. -/
noncomputable def formalCoproductMap {α β : Type}
    [hα : ∀ x : α → ι, HasProduct (fun a ↦ D (x a))]
    [hβ : ∀ x : β → ι, HasProduct (fun b ↦ D (x b))]
    (g : α → β) : formalCoproduct D β ⟶ formalCoproduct D α where
  f x := x ∘ g
  φ x := by
    letI := hβ x
    letI := hα (x ∘ g)
    change (∏ᶜ (fun b : β ↦ D (x b))) ⟶ ∏ᶜ (fun a : α ↦ D (x (g a)))
    exact Pi.lift (fun a ↦ Pi.π _ (g a))

/-- Reindexing along the identity is the identity. -/
@[simp]
lemma formalCoproductMap_id (α : Type) [hα : ∀ x : α → ι, HasProduct (fun a ↦ D (x a))] :
    formalCoproductMap D (id : α → α) = 𝟙 _ := by
  rw [FormalCoproduct.hom_ext_iff']
  intro x
  let : HasProduct (fun b : α ↦ D (x b)) := hα x
  let : HasProduct (fun a ↦ D (FormalCoproduct.Hom.f (𝟙 (formalCoproduct D α)) x a)) := hα x
  let : HasProduct (fun a ↦ D ((formalCoproductMap D (id : α → α)).f x a)) := hα x
  refine ⟨rfl, ?_⟩
  change (formalCoproductMap D (id : α → α)).φ x ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  change (Pi.lift fun a ↦ Pi.π (fun b : α ↦ D (x b)) a) = 𝟙 _
  exact Pi.hom_ext _ _ fun a ↦ by simp

/-- Reindexing is contravariantly functorial. -/
@[reassoc]
lemma formalCoproductMap_comp {α β γ : Type}
    [hα : ∀ x : α → ι, HasProduct (fun a ↦ D (x a))]
    [hβ : ∀ x : β → ι, HasProduct (fun b ↦ D (x b))]
    [hγ : ∀ x : γ → ι, HasProduct (fun c ↦ D (x c))]
    (g : α → β) (h : β → γ) :
    formalCoproductMap D (h ∘ g) = formalCoproductMap D h ≫ formalCoproductMap D g := by
  rw [FormalCoproduct.hom_ext_iff']
  intro x
  let : HasProduct (fun c : γ ↦ D (x c)) := hγ x
  let : HasProduct (fun b : β ↦ D (x (h b))) := hβ (fun b ↦ x (h b))
  let : HasProduct (fun a ↦ D (FormalCoproduct.Hom.f
      (formalCoproductMap D h ≫ formalCoproductMap D g) x a)) := hα (fun a ↦ x (h (g a)))
  let : HasProduct (fun a ↦ D ((formalCoproductMap D (h ∘ g)).f x a)) :=
    hα (fun a ↦ x (h (g a)))
  refine ⟨rfl, ?_⟩
  change (formalCoproductMap D (h ∘ g)).φ x ≫ 𝟙 _ =
    (formalCoproductMap D h ≫ formalCoproductMap D g).φ x
  rw [Category.comp_id]
  change (Pi.lift fun a ↦ Pi.π (fun c : γ ↦ D (x c)) (h (g a))) =
    (Pi.lift fun b ↦ Pi.π (fun c : γ ↦ D (x c)) (h b)) ≫
      (Pi.lift fun a ↦ Pi.π (fun b : β ↦ D (x (h b))) (g a))
  exact Pi.hom_ext _ _ fun a ↦ by simp

variable [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]

/-- The simplicial formal coproduct of all the finite nonempty products of members of the
family `D`: in degree `n` it is the formal coproduct of the products `D_x` over the tuples
`x : Fin (n + 1) → ι`. -/
@[implicit_reducible]
noncomputable def simplicialObject : SimplicialObject (FormalCoproduct.{w} C) where
  obj n := formalCoproduct D (ToType n.unop)
  map f := formalCoproductMap D f.unop.toOrderHom.toFun
  map_id _ := formalCoproductMap_id D _
  map_comp f g := by
    simpa [Function.comp_def] using formalCoproductMap_comp D
      g.unop.toOrderHom.toFun f.unop.toOrderHom.toFun

/-- **The Čech complex of a family of objects with chosen products**, as a functor of the
presheaf: in degree `n` it is the product over the tuples `x : Fin (n + 1) → ι` of the values of
the presheaf on the products `D_x`. -/
@[implicit_reducible]
noncomputable def complexFunctor (A : Type u') [Category.{v'} A] [HasProducts.{w} A]
    [Preadditive A] : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  FormalCoproduct.cochainComplexFunctor (simplicialObject D)

/-! ### The products of the members of the family -/

/-- `inter D x` is the product of the objects `D (x a)` for `a : Fin (n + 1)`. -/
noncomputable def inter {n : ℕ} (x : Fin (n + 1) → ι) : C :=
  ∏ᶜ fun a ↦ D (x a)

/-- The projection of `inter D x` onto the factor `D (x a)`. -/
noncomputable def interπ {n : ℕ} (x : Fin (n + 1) → ι) (a : Fin (n + 1)) :
    inter D x ⟶ D (x a) :=
  Pi.π _ a

/-- `inter D x` is the product of the objects `D (x a)`, with projections `interπ D x`. -/
noncomputable def isLimitInterFan {n : ℕ} (x : Fin (n + 1) → ι) :
    IsLimit (Fan.mk (inter D x) (interπ D x)) :=
  productIsProduct _

/-- Two morphisms into `inter D x` agree as soon as they agree after every projection. -/
@[ext]
theorem inter_hom_ext {n : ℕ} {x : Fin (n + 1) → ι} {T : C} {f g : T ⟶ inter D x}
    (h : ∀ a, f ≫ interπ D x a = g ≫ interπ D x a) : f = g :=
  Pi.hom_ext _ _ h

/-- The morphism into `inter D x` determined by a family of morphisms into the factors. -/
noncomputable def interLift {n : ℕ} {x : Fin (n + 1) → ι} {T : C} (f : ∀ a, T ⟶ D (x a)) :
    T ⟶ inter D x :=
  Pi.lift f

/-- The components of `interLift`. -/
@[reassoc (attr := simp)]
theorem interLift_comp_interπ {n : ℕ} {x : Fin (n + 1) → ι} {T : C} (f : ∀ a, T ⟶ D (x a))
    (a : Fin (n + 1)) : interLift D f ≫ interπ D x a = f a :=
  Pi.lift_comp_π _ _

/-- The reindexing morphism `inter D x ⟶ inter D (x ∘ h)` induced by a map of index sets
`h : Fin (m + 1) → Fin (n + 1)`. -/
noncomputable def interMap {n m : ℕ} (x : Fin (n + 1) → ι) (h : Fin (m + 1) → Fin (n + 1)) :
    inter D x ⟶ inter D (x ∘ h) :=
  interLift D fun a ↦ interπ D x (h a)

/-- The components of `interMap`. -/
@[reassoc (attr := simp)]
theorem interMap_comp_interπ {n m : ℕ} (x : Fin (n + 1) → ι) (h : Fin (m + 1) → Fin (n + 1))
    (a : Fin (m + 1)) : interMap D x h ≫ interπ D (x ∘ h) a = interπ D x (h a) :=
  interLift_comp_interπ D _ a

/-- Reindexing along the identity is the identity. -/
@[simp]
theorem interMap_id {n : ℕ} (x : Fin (n + 1) → ι) : interMap D x id = 𝟙 _ :=
  inter_hom_ext D fun a ↦ (interMap_comp_interπ D x id a).trans (Category.id_comp _).symm

/-- Reindexing is functorial. -/
@[reassoc]
theorem interMap_comp {n m k : ℕ} (x : Fin (n + 1) → ι) (h : Fin (m + 1) → Fin (n + 1))
    (h' : Fin (k + 1) → Fin (m + 1)) :
    interMap D x (h ∘ h') = interMap D x h ≫ interMap D (x ∘ h) h' :=
  inter_hom_ext D fun a ↦
    (interMap_comp_interπ D x (h ∘ h') a).trans
      (((interMap_comp_interπ D x h (h' a)).symm.trans
          (congrArg (interMap D x h ≫ ·)
            (interMap_comp_interπ D (x ∘ h) h' a).symm)).trans
        (Category.assoc _ _ _).symm)

/-! ### The degreewise description of the Čech complex -/

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A] (P : Cᵒᵖ ⥤ A)

/-- The projection of the degree `n` term of the Čech complex onto the factor indexed by the
tuple `x : Fin (n + 1) → ι`, namely the sections of `P` over `inter D x`. -/
noncomputable def π (n : ℕ) (x : Fin (n + 1) → ι) :
    ((complexFunctor D A).obj P).X n ⟶ P.obj (op (inter D x)) :=
  Pi.π _ x

/-- **Degreewise description of the Čech complex.** The degree `n` term is the product, indexed
by the tuples `x : Fin (n + 1) → ι`, of the sections of `P` over `inter D x`, with projections
`π D P n`. -/
noncomputable def isLimitFan (n : ℕ) :
    IsLimit (Fan.mk (((complexFunctor D A).obj P).X n) (π D P n)) :=
  productIsProduct _

/-- Two morphisms into the degree `n` term of the Čech complex agree as soon as they agree
after every projection. -/
@[ext]
theorem hom_ext {n : ℕ} {T : A} {f g : T ⟶ ((complexFunctor D A).obj P).X n}
    (h : ∀ x, f ≫ π D P n x = g ≫ π D P n x) : f = g :=
  Pi.hom_ext _ _ h

/-- The morphism into the degree `n` term of the Čech complex determined by a family of
morphisms into the sections of `P` over the objects `inter D x`. -/
noncomputable def lift {n : ℕ} {T : A}
    (f : ∀ x : Fin (n + 1) → ι, T ⟶ P.obj (op (inter D x))) :
    T ⟶ ((complexFunctor D A).obj P).X n :=
  Pi.lift f

/-- The components of `lift`. -/
@[reassoc (attr := simp)]
theorem lift_comp_π {n : ℕ} {T : A} (f : ∀ x : Fin (n + 1) → ι, T ⟶ P.obj (op (inter D x)))
    (x : Fin (n + 1) → ι) : lift D P f ≫ π D P n x = f x :=
  Pi.lift_comp_π _ _

/-- The `i`-th restriction map from degree `n` to degree `n + 1` of the Čech complex: its
component at the tuple `y` is the restriction of a section over `inter D (y ∘ i.succAbove)`. -/
noncomputable def face (n : ℕ) (i : Fin (n + 2)) :
    ((complexFunctor D A).obj P).X n ⟶ ((complexFunctor D A).obj P).X (n + 1) :=
  lift D P fun y ↦ π D P n (y ∘ i.succAbove) ≫ P.map (interMap D y i.succAbove).op

/-- The components of the restriction map `face`. -/
@[reassoc (attr := simp)]
theorem face_comp_π (n : ℕ) (i : Fin (n + 2)) (y : Fin (n + 2) → ι) :
    face D P n i ≫ π D P (n + 1) y =
      π D P n (y ∘ i.succAbove) ≫ P.map (interMap D y i.succAbove).op :=
  lift_comp_π D P _ y

/-- The coface maps of the cosimplicial object underlying the Čech complex, composed with a
projection, are the restrictions along the face maps. -/
theorem δ_comp_π (n : ℕ) (i : Fin (n + 2)) (y : Fin (n + 2) → ι) :
    ((FormalCoproduct.cosimplicialObjectFunctor (simplicialObject D)).obj P).δ i ≫
        π D P (n + 1) y =
      π D P n (y ∘ i.succAbove) ≫ P.map (interMap D y i.succAbove).op := by
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_comp_π _ _

/-- The coface maps of the cosimplicial object underlying the Čech complex are the restriction
maps `face`. -/
theorem δ_eq_face (n : ℕ) (i : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor (simplicialObject D)).obj P).δ i =
      face D P n i :=
  hom_ext D P (n := n + 1) fun y ↦ (δ_comp_π D P n i y).trans (face_comp_π D P n i y).symm

/-- **The Čech differential.** The differential from degree `n` to degree `n + 1` is the
alternating sum of the restriction maps `face D P n i`. -/
theorem d_eq (n : ℕ) :
    ((complexFunctor D A).obj P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • face D P n i :=
  (Stacks.CategoryTheory.CechComplex.alternatingCofaceMapComplex_obj_d
      ((FormalCoproduct.cosimplicialObjectFunctor (simplicialObject D)).obj P) n).trans
    (Finset.sum_congr rfl fun i _ ↦
      congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • z) (δ_eq_face D P n i))

/-- **The Čech differential, componentwise.** Composed with the projection indexed by
`y : Fin (n + 2) → ι`, the differential from degree `n` to degree `n + 1` is the alternating sum
of the restrictions along the face maps `Fin.succAbove i`. -/
theorem d_comp_π (n : ℕ) (y : Fin (n + 2) → ι) :
    ((complexFunctor D A).obj P).d n (n + 1) ≫ π D P (n + 1) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (π D P n (y ∘ i.succAbove) ≫ P.map (interMap D y i.succAbove).op) := by
  rw [d_eq, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Preadditive.zsmul_comp, face_comp_π]

/-- **The Čech differential in degree `0`**: the difference of the restrictions along the two
face maps. -/
theorem d_zero_comp_π (y : Fin 2 → ι) :
    ((complexFunctor D A).obj P).d 0 1 ≫ π D P 1 y =
      π D P 0 (y ∘ (0 : Fin 2).succAbove) ≫ P.map (interMap D y (0 : Fin 2).succAbove).op -
        π D P 0 (y ∘ (1 : Fin 2).succAbove) ≫ P.map (interMap D y (1 : Fin 2).succAbove).op := by
  have h := d_comp_π D P 0 y
  rw [Fin.sum_univ_two] at h
  refine h.trans ?_
  simp [sub_eq_add_neg]

/-- **The Čech complex functor on morphisms**, componentwise: the map induced by a morphism of
presheaves `φ` is, on the factor indexed by `x`, the component of `φ` at `inter D x`. -/
@[reassoc (attr := simp)]
theorem map_f_π {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) (n : ℕ) (x : Fin (n + 1) → ι) :
    ((complexFunctor D A).map φ).f n ≫ π D Q n x = π D P n x ≫ φ.app (op (inter D x)) :=
  Limits.Pi.map_π (f := fun y : Fin (n + 1) → ι ↦ P.obj (op (inter D y)))
    (g := fun y ↦ Q.obj (op (inter D y))) (fun y ↦ φ.app (op (inter D y))) x

/-- The Čech complex functor is additive. -/
instance complexFunctor_additive : (complexFunctor D A).Additive where
  map_add {P Q φ ψ} := by
    ext n : 1
    refine hom_ext D Q fun x ↦ ?_
    rw [HomologicalComplex.add_f_apply, Preadditive.add_comp, map_f_π, map_f_π, map_f_π,
      NatTrans.app_add, Preadditive.comp_add]

end Stacks.CechSite.FinalCover

end

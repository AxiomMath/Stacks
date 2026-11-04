module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech complex and Čech cohomology of a family of morphisms

Let `C` be a category, let `X` be an object of `C` and let `{U_i → X}_{i ∈ I}` be a family of
morphisms with target `X`. Assume that the finite nonempty fibre products
`U_{i_0} ×_X … ×_X U_{i_p}` exist. For an additive presheaf `F` on `C` the *Čech complex*
of Stacks 03AM is the cochain complex whose degree-`p` term is
`∏_{(i_0, …, i_p)} F(U_{i_0} ×_X … ×_X U_{i_p})` with the usual alternating differential, and
the *Čech cohomology objects* `Ȟ^p({U_i → X}, F)` are its homology objects.

## Main definitions

* `Stacks.CechSite.cechSimplicialObject`: the simplicial formal coproduct of all the finite
  nonempty fibre products of the family.
* `Stacks.CechSite.cechComplexFunctor` and `Stacks.CechSite.cechComplex`: the Čech complex,
  as a functor of the presheaf and as applied to one presheaf.
* `Stacks.CechSite.cechCohomology`: the Čech cohomology objects.

## Implementation notes

A family of morphisms with fixed target is represented by a `PreZeroHypercover X`. Its finite
fibre products over `X` are the products, taken in the slice category `Over X`, of the
selected objects `Over.mk (E.f i)`; the hypothesis below asks only for *those* products to
exist, and not for all finite products in `Over X`, which is what lets the construction apply
to a family on a site whose slices need not have finite limits. Had Mathlib's
`CategoryTheory.cechComplexFunctor` been used with the family `i ↦ Over.mk (E.f i)` instead,
`HasFiniteProducts (Over X)` would have been required.

The complex is obtained by forming the simplicial formal coproduct of those fibre products and
evaluating a presheaf on it, which is also where the functoriality in the presheaf comes from.
Evaluation on `Over X` is composed with restriction along `(Over.forget X).op`, so that the
construction takes a presheaf on `C` as input.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe t w v v' u u' uA vA

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

/-- The formal coproduct, indexed by `α`-tuples from `E`, of the corresponding fibre products
over `X`. -/
noncomputable def cechFormalCoproduct (α : Type t)
    [∀ i : α → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    FormalCoproduct.{max w t} (Over X) where
  I := α → E.I₀
  obj i := ∏ᶜ (fun a ↦ Over.mk (E.f (i a)))

/-- Reindexing tuples induces the corresponding map between the formal coproducts of fibre
products. -/
noncomputable def cechFormalCoproductMap {α β : Type t}
    [hα : ∀ i : α → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [hβ : ∀ i : β → E.I₀, HasProduct (fun b ↦ Over.mk (E.f (i b)))]
    (g : α → β) : cechFormalCoproduct E β ⟶ cechFormalCoproduct E α where
  f i := i ∘ g
  φ i := by
    letI := hβ i
    letI := hα (i ∘ g)
    change (∏ᶜ (fun b : β ↦ Over.mk (E.f (i b)))) ⟶
      ∏ᶜ (fun a : α ↦ Over.mk (E.f (i (g a))))
    exact Pi.lift (fun a ↦ Pi.π _ (g a))

/-- Reindexing along the identity is the identity. -/
@[simp]
lemma cechFormalCoproductMap_id (α : Type t)
    [hα : ∀ i : α → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    cechFormalCoproductMap E (id : α → α) = 𝟙 _ := by
  rw [FormalCoproduct.hom_ext_iff']
  intro i
  let hi : HasProduct (fun b : α ↦ Over.mk (E.f (i b))) := hα i
  let : HasProduct (fun a ↦ Over.mk
      (E.f (FormalCoproduct.Hom.f (𝟙 (cechFormalCoproduct E α)) i a))) := hα i
  let : HasProduct (fun a ↦ Over.mk
      (E.f ((cechFormalCoproductMap E (id : α → α)).f i a))) := hα i
  refine ⟨rfl, ?_⟩
  show (cechFormalCoproductMap E (id : α → α)).φ i ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  show (Pi.lift fun a ↦ Pi.π (fun b : α ↦ Over.mk (E.f (i b))) a) = 𝟙 _
  exact Pi.hom_ext _ _ fun a ↦ by simp

/-- Reindexing is contravariantly functorial. -/
@[reassoc]
lemma cechFormalCoproductMap_comp {α β γ : Type t}
    [hα : ∀ i : α → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [hβ : ∀ i : β → E.I₀, HasProduct (fun b ↦ Over.mk (E.f (i b)))]
    [hγ : ∀ i : γ → E.I₀, HasProduct (fun c ↦ Over.mk (E.f (i c)))]
    (g : α → β) (h : β → γ) :
    cechFormalCoproductMap E (h ∘ g) =
      cechFormalCoproductMap E h ≫ cechFormalCoproductMap E g := by
  rw [FormalCoproduct.hom_ext_iff']
  intro i
  let hi : HasProduct (fun c : γ ↦ Over.mk (E.f (i c))) := hγ i
  let hih : HasProduct (fun b : β ↦ Over.mk (E.f (i (h b)))) := hβ (fun b ↦ i (h b))
  let : HasProduct (fun a ↦ Over.mk
      (E.f (FormalCoproduct.Hom.f
        (cechFormalCoproductMap E h ≫ cechFormalCoproductMap E g) i a))) :=
    hα (fun a ↦ i (h (g a)))
  let : HasProduct (fun a ↦ Over.mk
      (E.f ((cechFormalCoproductMap E (h ∘ g)).f i a))) := hα (fun a ↦ i (h (g a)))
  refine ⟨rfl, ?_⟩
  show (cechFormalCoproductMap E (h ∘ g)).φ i ≫ 𝟙 _ =
    (cechFormalCoproductMap E h ≫ cechFormalCoproductMap E g).φ i
  rw [Category.comp_id]
  show (Pi.lift fun a ↦ Pi.π (fun b : γ ↦ Over.mk (E.f (i b))) (h (g a))) =
    (Pi.lift fun b ↦ Pi.π (fun c : γ ↦ Over.mk (E.f (i c))) (h b)) ≫
      (Pi.lift fun a ↦ Pi.π (fun b : β ↦ Over.mk (E.f (i (h b)))) (g a))
  exact Pi.hom_ext _ _ fun a ↦ by simp

/-- The simplicial formal coproduct of all finite nonempty fibre products of the family `E`. -/
@[implicit_reducible]
noncomputable def cechSimplicialObject
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    SimplicialObject (FormalCoproduct.{w} (Over X)) where
  obj n := cechFormalCoproduct E (ToType n.unop)
  map f := cechFormalCoproductMap E f.unop.toOrderHom.toFun
  map_id _ := cechFormalCoproductMap_id E _
  map_comp f g := by
    simpa [Function.comp_def] using cechFormalCoproductMap_comp E
      g.unop.toOrderHom.toFun f.unop.toOrderHom.toFun

/-- The Čech complex construction, as a functor of the presheaf. -/
@[implicit_reducible]
noncomputable def cechComplexFunctor
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  (CategoryTheory.Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ A).obj (Over.forget X).op ⋙
    FormalCoproduct.cochainComplexFunctor (cechSimplicialObject E)

/-- The Čech complex associated to an additive presheaf and a family of morphisms with fixed
target whose finite nonempty fibre products exist. -/
@[stacks 03AM "the Čech complex",
  stacks 03OL "the Čech complex of an abelian presheaf along a family with fixed target",
  stacks 03AL "the alternating-sum differential of the Čech complex",
  sga "4 V 2.4.3" "Čech complex"]
noncomputable abbrev cechComplex
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (F : CategoryTheory.Functor Cᵒᵖ A) : CochainComplex A ℕ :=
  (cechComplexFunctor E).obj F

/-- The degree-`n` Čech cohomology object of a presheaf with respect to a family of morphisms
with fixed target. For abelian-group-valued presheaves this is the Čech cohomology group. -/
@[stacks 03AM "the Čech cohomology groups",
  stacks 03OL "the Čech cohomology groups, as the cohomology of the Čech complex",
  sga "4 V 2.4.3" "Čech cohomology of 𝒰"]
noncomputable abbrev cechCohomology
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Abelian A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (F : CategoryTheory.Functor Cᵒᵖ A) (n : ℕ) : A :=
  (cechComplex E F).homology n


/-- Evaluating a presheaf at a formal coproduct is the product of its evaluations at the
summands. -/
noncomputable def evalOpCompEvaluationIso
    {D : Type u} [Category.{v} D] {A : Type uA} [Category.{vA} A]
    [HasProducts.{w} A] (T : FormalCoproduct.{w} D) :
    FormalCoproduct.evalOp D A ⋙ (evaluation _ _).obj (op T) ≅
      (Functor.whiskeringLeft _ _ A).obj
        (Discrete.functor (fun i : T.I ↦ op (T.obj i))) ⋙ lim :=
  NatIso.ofComponents (fun F ↦ Pi.isoLimit
    ((Discrete.functor (fun i : T.I ↦ op (T.obj i))) ⋙ F)) (by
      intro F G f
      apply limit.hom_ext
      intro ⟨i⟩
      simp [FormalCoproduct.evalOp])

end Stacks.CechSite

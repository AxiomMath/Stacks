module

public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
import StacksCore.Tactic.StacksAttribute

/-!
# The map of Čech complexes induced by a morphism of families

A morphism from one family of morphisms with fixed target to another — a refinement, in the
language of coverings — induces, by contravariance of the coefficient presheaf, a morphism of
the associated Čech complexes of Stacks 03AM in the opposite direction. This is Stacks 03F4.

## Main definitions

* `Stacks.CechSite.cechProductMap`: the map between the corresponding iterated fibre
  products of the two families.
* `Stacks.CechSite.cechComplexMap`: the induced morphism of Čech complexes.

## Main results

* `Stacks.CechSite.cechComplexMap_f_Pi_π`: the degreewise formula of the source, giving the
  components of `cechComplexMap` against the product projections.

## Implementation notes

Families with possibly different targets are `PreZeroHypercover`s related by a
`PreZeroHypercover.HomOver`. The construction is stated for presheaves valued in any
preadditive category admitting the required products; the abelian-group-valued case of the
source is the special case of that.

## References

* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe w w' v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] cechFormalCoproduct cechFormalCoproductMap

/-- The map from an iterated fibre product in the refining family to the corresponding
iterated fibre product in the refined family. -/
noncomputable def cechProductMap
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))] :
    (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left ⟶
      (∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (i a))))).left :=
  (Pi.lift (P := Over.mk ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).hom ≫ f))
    (fun a ↦ (Over.homMk
      ((Pi.π (fun b ↦ Over.mk (E.f (i b))) a).left ≫ φ.h₀ (i a)) (by
        simp only [Over.mk_hom]
        rw [Category.assoc, φ.w₀, ← Category.assoc]
        exact congrArg (· ≫ f) (Over.w (Pi.π (fun b ↦ Over.mk (E.f (i b))) a))) :
        Over.mk ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).hom ≫ f) ⟶
          Over.mk (G.f (φ.s₀ (i a)))))).left

universe t

private noncomputable def cechProductMapOver
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [hE : ∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [hG : ∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))] :
    (Over.map f).obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))) ⟶
      ∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) := by
  letI := hE i
  letI := hG (φ.s₀ ∘ i)
  exact Pi.lift (P := Over.mk ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).hom ≫ f))
    (fun a ↦ Over.homMk
      ((Pi.π (fun b ↦ Over.mk (E.f (i b))) a).left ≫ φ.h₀ (i a)) (by
        simp only [Over.mk_hom]
        rw [Category.assoc, φ.w₀, ← Category.assoc]
        exact congrArg (· ≫ f) (Over.w (Pi.π (fun b ↦ Over.mk (E.f (i b))) a))))

/-- Reindexing a formal coproduct of iterated fibre products along `r` is, componentwise, the
map of products that reindexes the projections along `r`. -/
theorem cechFormalCoproductMap_φ_comp_π
    {C : Type u} [Category.{v} C] {U : C}
    (E : PreZeroHypercover.{w} U) {α β : Type t}
    [hβ : ∀ i : β → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [hα : ∀ i : α → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (r : α → β) (i : β → E.I₀) (b : α) :
    (cechFormalCoproductMap E r).φ
        (i : (cechFormalCoproduct E β).I) ≫
        Pi.π (fun a ↦ Over.mk (E.f (i (r a)))) b =
      Pi.π (fun a ↦ Over.mk (E.f (i a))) (r b) := by
  show Pi.lift (fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (i b))) (r a)) ≫
      Pi.π (fun a ↦ Over.mk (E.f (i (r a)))) b = _
  exact Pi.lift_comp_π _ _

private theorem cechProductMapOver_comp_π
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [hE : ∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [hG : ∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (b : Fin (n + 1)) :
    cechProductMapOver E G φ n i ≫
        Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b =
      ((Over.homMk
        ((Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left ≫ φ.h₀ (i b))
        (by
          simp only [Over.mk_hom]
          rw [Category.assoc, φ.w₀, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w (Pi.π (fun a ↦ Over.mk (E.f (i a))) b)))) :
        Over.mk ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).hom ≫ f) ⟶
          Over.mk (G.f (φ.s₀ (i b)))) := by
  simp [cechProductMapOver]

private theorem cechProductMapOver_comp_π_left
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [hE : ∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [hG : ∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (b : Fin (n + 1)) :
    (cechProductMapOver E G φ n i).left ≫
        (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left =
      (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left ≫ φ.h₀ (i b) :=
  congrArg Over.Hom.left (cechProductMapOver_comp_π E G φ n i b)

private theorem cechFormalCoproductMap_φ_comp_π_left
    {C : Type u} [Category.{v} C] {U : C}
    (E : PreZeroHypercover.{w} U) {α β : Type t}
    [∀ i : β → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ i : α → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (r : α → β) (i : β → E.I₀) (b : α) :
    ((cechFormalCoproductMap E r).φ
        (i : (cechFormalCoproduct E β).I)).left ≫
        (Pi.π (fun a ↦ Over.mk (E.f (i (r a)))) b).left =
      (Pi.π (fun a ↦ Over.mk (E.f (i a))) (r b)).left :=
  congrArg Over.Hom.left (cechFormalCoproductMap_φ_comp_π E r i b)

private theorem cechProductMapOver_reindex
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (d : Fin (n + 1) → Fin (n + 2))
    (i : Fin (n + 2) → E.I₀)
    [hEFull : ∀ j : Fin (n + 2) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [hEFace : ∀ j : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [hGFull : ∀ j : Fin (n + 2) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))]
    [hGFace : ∀ j : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))] :
    (Over.map f).map ((cechFormalCoproductMap E d).φ i) ≫
        cechProductMapOver E G φ n (i ∘ d) =
      cechProductMapOver E G φ (n + 1) i ≫
    (cechFormalCoproductMap G d).φ (φ.s₀ ∘ i) := by
  apply Pi.hom_ext
  intro b
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.map_map_left]
  change
    (((cechFormalCoproductMap E d).φ
          (i : (cechFormalCoproduct E (Fin (n + 2))).I)).left ≫
        (cechProductMapOver E G φ n (i ∘ d)).left) ≫
      (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ ((i ∘ d) a)))) b).left =
    ((cechProductMapOver E G φ (n + 1) i).left ≫
        ((cechFormalCoproductMap G d).φ
          (φ.s₀ ∘ i : (cechFormalCoproduct G (Fin (n + 2))).I)).left) ≫
      (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ ((i ∘ d) a)))) b).left
  have hL : ((cechFormalCoproductMap E d).φ
        (i : (cechFormalCoproduct E (Fin (n + 2))).I)).left ≫
      (Pi.π (fun a ↦ Over.mk (E.f ((i ∘ d) a))) b).left =
    (Pi.π (fun a ↦ Over.mk (E.f (i a))) (d b)).left :=
    cechFormalCoproductMap_φ_comp_π_left E d i b
  have hR : ((cechFormalCoproductMap G d).φ
        (φ.s₀ ∘ i : (cechFormalCoproduct G (Fin (n + 2))).I)).left ≫
      (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ ((i ∘ d) a)))) b).left =
    (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) (d b)).left :=
    cechFormalCoproductMap_φ_comp_π_left G d (φ.s₀ ∘ i) b
  rw [Category.assoc, cechProductMapOver_comp_π_left, ← Category.assoc, hL,
    Category.assoc, hR, cechProductMapOver_comp_π_left]
  rfl

/-- The maps `cechProductMap` are natural with respect to reindexing along `d`: precomposing with
the reindexing map for the family `E` equals postcomposing with the reindexing map for the family
`G` along the indices `φ.s₀ ∘ i`. -/
theorem cechProductMap_face_naturality
    {C : Type u} [Category.{v} C] {U V : C} {f : U ⟶ V}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V)
    (φ : E.HomOver G f) (n : ℕ) (d : Fin (n + 1) → Fin (n + 2))
    (i : Fin (n + 2) → E.I₀)
    [hEFull : ∀ j : Fin (n + 2) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [hEFace : ∀ j : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [hGFull : ∀ j : Fin (n + 2) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))]
    [hGFace : ∀ j : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))] :
    ((cechFormalCoproductMap E d).φ i).left ≫
        cechProductMap E G φ n (i ∘ d) =
      cechProductMap E G φ (n + 1) i ≫
        ((cechFormalCoproductMap G d).φ (φ.s₀ ∘ i)).left := by
  have h := congrArg Over.Hom.left (cechProductMapOver_reindex E G φ n d i)
  rw [Over.comp_left, Over.comp_left, Over.map_map_left] at h
  exact h

/-- For a morphism `g` of formal coproducts, the map induced by `g` on the product of the values
of `P`, followed by the projection to the factor `i`, is the projection to the factor `g.f i`
followed by `P` applied to the component `g.φ i`. -/
theorem evalOpMapCompPi
    {D : Type*} [Category* D] {A : Type*} [Category* A] [HasProducts A]
    (P : Dᵒᵖ ⥤ A) {X Y : FormalCoproduct D} (g : X ⟶ Y) (i : X.I) :
    ((FormalCoproduct.evalOp D A).obj P).map g.op ≫
        Pi.π (fun j : X.I ↦ P.obj (op (X.obj j))) i =
      Pi.π (fun j : Y.I ↦ P.obj (op (Y.obj j))) (g.f i) ≫ P.map (g.φ i).op := by
  show (Pi.lift (fun i : X.I ↦
    Pi.π (fun j : Y.I ↦ P.obj (op (Y.obj j))) (g.f i) ≫ P.map (g.φ i).op) ≫
      Pi.π (fun j : X.I ↦ P.obj (op (X.obj j))) i) = _
  rw [Pi.lift_comp_π]

/-- The degree `n` component of the map of Čech complexes: the map from the product of the values
of `F` on the iterated fibre products of `G` to that for `E`, whose component at the tuple `i` is
the projection to the tuple `φ.s₀ ∘ i` followed by `F` applied to `cechProductMap E G φ n i`. -/
noncomputable def cechComplexMapDegree
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f)
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((FormalCoproduct.evalOp.{w'} (Over V) A).obj ((Over.forget V).op ⋙ F)).obj
        (op ((cechSimplicialObject G).obj (op (SimplexCategory.mk n)))) ⟶
      ((FormalCoproduct.evalOp.{w} (Over U) A).obj ((Over.forget U).op ⋙ F)).obj
        (op ((cechSimplicialObject E).obj (op (SimplexCategory.mk n)))) := by
  let XE := cechSimplicialObject E
  let XG := cechSimplicialObject G
  let e := XE.obj (op (SimplexCategory.mk n))
  let g := XG.obj (op (SimplexCategory.mk n))
  exact Pi.lift (fun i : e.I ↦
    Pi.π (fun j : g.I ↦ ((Over.forget V).op ⋙ F).obj (op (g.obj j))) (φ.s₀ ∘ i) ≫
      F.map (cechProductMap E G φ n i).op)

/-- The component of `cechComplexMapDegree` at the tuple `i` is the projection to the tuple
`φ.s₀ ∘ i` followed by `F` applied to `cechProductMap E G φ n i`. -/
theorem cechComplexMapDegree_comp_π_formal
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f)
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (F : Cᵒᵖ ⥤ A) (n : ℕ)
    (i : ToType (SimplexCategory.mk n) → E.I₀) :
    cechComplexMapDegree E G φ F n ≫
        Pi.π (fun i : ToType (SimplexCategory.mk n) → E.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) i =
        Pi.π (fun j : ToType (SimplexCategory.mk n) → G.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (j a)))).left)))
          (φ.s₀ ∘ i) ≫ F.map (cechProductMap E G φ n i).op := by
  show (Pi.lift (fun i : ToType (SimplexCategory.mk n) → E.I₀ ↦
    Pi.π (fun j : ToType (SimplexCategory.mk n) → G.I₀ ↦
      F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (j a)))).left))) (φ.s₀ ∘ i) ≫
      F.map (cechProductMap E G φ n i).op) ≫
    Pi.π (fun i : ToType (SimplexCategory.mk n) → E.I₀ ↦
      F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) i = _)
  rw [Pi.lift_comp_π]


/-- A degreewise family of maps commuting with each signed coface map commutes with the
alternating-coface differential. -/
theorem comp_objD_comm {A : Type u'} [Category.{v'} A] [Preadditive A]
    {XE XG : CosimplicialObject A}
    (τ : ∀ n : ℕ, XG.obj (SimplexCategory.mk n) ⟶ XE.obj (SimplexCategory.mk n))
    (hτ : ∀ (n : ℕ) (i : Fin (n + 2)),
      τ n ≫ ((-1 : ℤ) ^ (i : ℕ) • XE.δ i) = ((-1 : ℤ) ^ (i : ℕ) • XG.δ i) ≫ τ (n + 1))
    (n : ℕ) :
    τ n ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD XE n =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD XG n ≫ τ (n + 1) := by
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Preadditive.comp_sum,
    Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ ↦ hτ n i

attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- The degreewise maps of `cechComplexMapDegree` commute with each signed coface map of the
cosimplicial objects whose alternating-coface complexes are the two Čech complexes. -/
theorem cechComplexMapDegree_zsmul_δ_comm
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f)
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (F : Cᵒᵖ ⥤ A) (n : ℕ) (i : Fin (n + 2)) :
    cechComplexMapDegree E G φ F n ≫
        ((-1 : ℤ) ^ (i : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over U) A).obj ((Over.forget U).op ⋙ F)).map
            ((cechSimplicialObject E).map (SimplexCategory.δ i).op).op) =
      ((-1 : ℤ) ^ (i : ℕ) •
          ((FormalCoproduct.evalOp.{w'} (Over V) A).obj ((Over.forget V).op ⋙ F)).map
            ((cechSimplicialObject G).map (SimplexCategory.δ i).op).op) ≫
        cechComplexMapDegree E G φ F (n + 1) := by
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine congrArg (fun z ↦ ((-1 : ℤ) ^ (i : ℕ)) • z) ?_
  apply Pi.hom_ext
  intro j
  set gE := (cechSimplicialObject E).map (SimplexCategory.δ i).op with hgE
  set gG := (cechSimplicialObject G).map (SimplexCategory.δ i).op with hgG
  have hE := evalOpMapCompPi ((Over.forget U).op ⋙ F) gE j
  have hG := evalOpMapCompPi ((Over.forget V).op ⋙ F) gG (φ.s₀ ∘ j)
  have hπ : ∀ (m : ℕ) (k : ToType (SimplexCategory.mk m) → E.I₀),
      cechComplexMapDegree E G φ F m ≫
        Pi.π (fun l ↦ ((Over.forget U).op ⋙ F).obj
          (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk m))).obj l))) k =
      Pi.π (fun l ↦ ((Over.forget V).op ⋙ F).obj
          (op (((cechSimplicialObject G).obj (op (SimplexCategory.mk m))).obj l))) (φ.s₀ ∘ k) ≫
        F.map (cechProductMap E G φ m k).op := fun m k ↦ by
    simpa [cechSimplicialObject, cechFormalCoproduct,
      Functor.comp_obj, Over.forget_obj] using cechComplexMapDegree_comp_π_formal E G φ F m k
  let d : Fin (n + 1) → Fin (n + 2) :=
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)).toFun
  have hProd := cechProductMap_face_naturality E G φ n d j
  have hOver :
      (Over.Hom.left (gE.φ j)) ≫ cechProductMap E G φ n (gE.f j) =
        cechProductMap E G φ (n + 1) j ≫
          Over.Hom.left (gG.φ (φ.s₀ ∘ j)) := by
    simpa [gE, gG, cechSimplicialObject,
      cechFormalCoproductMap, Function.comp_def, d] using hProd
  have hFMap :
      F.map (cechProductMap E G φ n (gE.f j)).op ≫
          F.map (Over.Hom.left (gE.φ j)).op =
        F.map (Over.Hom.left (gG.φ (φ.s₀ ∘ j))).op ≫
          F.map (cechProductMap E G φ (n + 1) j).op := by
    have hOpp :
        (cechProductMap E G φ n (gE.f j)).op ≫ (Over.Hom.left (gE.φ j)).op =
          (Over.Hom.left (gG.φ (φ.s₀ ∘ j))).op ≫
            (cechProductMap E G φ (n + 1) j).op := by
      rw [← op_comp, ← op_comp]
      exact congrArg Quiver.Hom.op hOver
    rw [← Functor.map_comp, ← Functor.map_comp, hOpp]
  conv_lhs => rw [Category.assoc, hE, ← Category.assoc, hπ n, Category.assoc]
  conv_rhs => rw [Category.assoc, hπ (n + 1), ← Category.assoc, hG, Category.assoc]
  simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op]
  rw [hFMap]
  congr 1

/-- The degreewise maps of `cechComplexMapDegree` commute with the differentials of the two
Čech complexes. -/
theorem cechComplexMapDegree_comm
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f)
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechComplexMapDegree E G φ F n ≫ (cechComplex E F).d n (n + 1) =
      (cechComplex G F).d n (n + 1) ≫ cechComplexMapDegree E G φ F (n + 1) := by
  show cechComplexMapDegree E G φ F n ≫
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj
          ((Over.forget U).op ⋙ F))).d n (n + 1) =
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w'} (cechSimplicialObject G)).obj
          ((Over.forget V).op ⋙ F))).d n (n + 1) ≫ cechComplexMapDegree E G φ F (n + 1)
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  exact comp_objD_comm
    (XE := (FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj
      ((Over.forget U).op ⋙ F))
    (XG := (FormalCoproduct.cosimplicialObjectFunctor.{w'} (cechSimplicialObject G)).obj
      ((Over.forget V).op ⋙ F))
    (fun m ↦ cechComplexMapDegree E G φ F m)
    (fun m k ↦ cechComplexMapDegree_zsmul_δ_comm E G φ F m k) n

/-- The map of Čech complexes induced by a morphism of families of morphisms with fixed target,
from the Čech complex of the refined family `G` to that of the refining family `E`. -/
@[stacks 03F4]
noncomputable def cechComplexMap
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f)
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (F : Cᵒᵖ ⥤ A) :
    cechComplex G F ⟶ cechComplex E F :=
  CochainComplex.ofHom (fun n ↦ cechComplexMapDegree E G φ F n)
    (cechComplexMapDegree_comm E G φ F)

/-- In degree `n`, the component of `cechComplexMap` indexed by `i` is restriction along
the map of iterated fibre products induced by `φ`. -/
theorem cechComplexMap_f_Pi_π
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f)
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (F : Cᵒᵖ ⥤ A) (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    (cechComplexMap E G φ F).f n ≫
        Pi.π (fun i : Fin (n + 1) → E.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) i =
      Pi.π (fun j : Fin (n + 1) → G.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (j a)))).left))) (φ.s₀ ∘ i) ≫
        F.map (cechProductMap E G φ n i).op := by
  show cechComplexMapDegree E G φ F n ≫
      Pi.π (fun i : Fin (n + 1) → E.I₀ ↦
        F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) i = _
  simpa [cechSimplicialObject, cechFormalCoproduct,
    Functor.comp_obj, Over.forget_obj] using
      (cechComplexMapDegree_comp_π_formal E G φ F n i)

end Stacks.CechSite

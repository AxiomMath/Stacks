module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology

/-!
# The fibre of a morphism of abelian sheaves over a section on an object

Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of abelian sheaves on a site `(C, J)`
and let `σ` be a section of `X₃` over an object `X` of `C`. The presheaf of sets

  `W ↦ {(a, e) | a : W ⟶ X, e ∈ X₂(W), g(e) = a^* σ}`

with its projection to `yoneda.obj X` is the torsor under `X₁` on the slice site over `X`
attached to `σ`, viewed as a presheaf on `C` over `X`. This file proves that it is a sheaf when
`yoneda.obj X` is one, that it has sections locally on `X`, and that over any `W` with a
section `(a, e)` it is the product `h_W × X₁`, through a cartesian square over `a`.

## Main definitions

* `Stacks.Cohomology.Torsors.fiberOverObject`: the presheaf of sets above.
* `Stacks.Cohomology.Torsors.fiberOverObjectToYoneda`: its projection to `yoneda.obj X`.

## Main results

* `Stacks.Cohomology.Torsors.fiberOverObject_isSheaf`: it is a sheaf.
* `Stacks.Cohomology.Torsors.exists_cover_fiberOverObject`: it has sections over the arrows of
  a covering sieve of `X`.
* `Stacks.Cohomology.Torsors.isPullback_fiberOverObject`: over a section `(a, e)` on `W`, it is
  the base change of `yoneda.map a` along a morphism from `h_W × X₁`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A section of a binary product of presheaves of sets, from its two components. -/
def prodSectionMk {A B : Cᵒᵖ ⥤ Type v} {V : C} (a : A.obj (op V)) (b : B.obj (op V)) :
    (A ⨯ B).obj (op V) :=
  yonedaEquiv (prod.lift (yonedaEquiv.symm a) (yonedaEquiv.symm b))

@[simp]
lemma fst_app_prodSectionMk {A B : Cᵒᵖ ⥤ Type v} {V : C} (a : A.obj (op V))
    (b : B.obj (op V)) : (prod.fst : A ⨯ B ⟶ A).app (op V) (prodSectionMk a b) = a := by
  rw [prodSectionMk, ← yonedaEquiv_comp, prod.lift_fst, Equiv.apply_symm_apply]

@[simp]
lemma snd_app_prodSectionMk {A B : Cᵒᵖ ⥤ Type v} {V : C} (a : A.obj (op V))
    (b : B.obj (op V)) : (prod.snd : A ⨯ B ⟶ B).app (op V) (prodSectionMk a b) = b := by
  rw [prodSectionMk, ← yonedaEquiv_comp, prod.lift_snd, Equiv.apply_symm_apply]

/-- Two sections of a binary product of presheaves of sets agree when their components do. -/
lemma prod_section_ext' {A B : Cᵒᵖ ⥤ Type v} {V : C} {z z' : (A ⨯ B).obj (op V)}
    (h₁ : (prod.fst : A ⨯ B ⟶ A).app (op V) z = (prod.fst : A ⨯ B ⟶ A).app (op V) z')
    (h₂ : (prod.snd : A ⨯ B ⟶ B).app (op V) z = (prod.snd : A ⨯ B ⟶ B).app (op V) z') :
    z = z' := by
  refine yonedaEquiv.symm.injective (prod.hom_ext ?_ ?_) <;> refine yonedaEquiv.injective ?_ <;>
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) {X : C} (σ : S.X₃.obj.obj (op X))

/-- The fibre of `S.g` over the restrictions of a section `σ` of `S.X₃` over `X`: over `W`, the
pairs of a morphism `a : W ⟶ X` and a section of `S.X₂` over `W` mapping to `a^* σ`. -/
public def fiberOverObject : Cᵒᵖ ⥤ Type v where
  obj W := {x : (W.unop ⟶ X) × S.X₂.obj.obj W // S.g.hom.app W x.2 = S.X₃.obj.map x.1.op σ}
  map {W W'} f := ↾(fun x => ⟨(f.unop ≫ x.1.1, S.X₂.obj.map f x.1.2), by
    calc
      S.g.hom.app W' (S.X₂.obj.map f x.1.2) = S.X₃.obj.map f (S.g.hom.app W x.1.2) :=
        NatTrans.naturality_apply S.g.hom f x.1.2
      _ = S.X₃.obj.map f (S.X₃.obj.map x.1.1.op σ) := congrArg _ x.2
      _ = S.X₃.obj.map (f.unop ≫ x.1.1).op σ := by
        rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]⟩)
  map_id := by
    intro W
    ext x
    · simp
    · simp
  map_comp := by
    intro W W' W'' f g
    ext x
    · simp
    · simp

/-- The projection of `fiberOverObject S σ` to `yoneda.obj X`. -/
public def fiberOverObjectToYoneda : fiberOverObject S σ ⟶ yoneda.obj X where
  app W := ↾fun x => x.1.1
  naturality := by
    intro W W' f
    ext x
    rfl

@[simp]
lemma fiberOverObjectToYoneda_app {W : C} (x : (fiberOverObject S σ).obj (op W)) :
    (fiberOverObjectToYoneda S σ).app (op W) x = x.1.1 := rfl

/-- **The fibre over a section on an object is a sheaf**, when the representable presheaf of
the object is one. -/
public lemma fiberOverObject_isSheaf (hX : Presheaf.IsSheaf J (yoneda.obj X)) :
    Presheaf.IsSheaf J (fiberOverObject S σ) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR x hx
  let E := S.X₂.obj ⋙ forget AddCommGrpCat
  let Q := S.X₃.obj ⋙ forget AddCommGrpCat
  have hE : Presieve.IsSheaf J E :=
    (isSheaf_iff_isSheaf_of_type J E).1
      (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat) S.X₂.property)
  have hQ : Presieve.IsSheaf J Q :=
    (isSheaf_iff_isSheaf_of_type J Q).1
      (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat) S.X₃.property)
  have hY : Presieve.IsSheaf J (yoneda.obj X) := (isSheaf_iff_isSheaf_of_type J _).1 hX
  let iE : fiberOverObject S σ ⟶ E :=
    { app := fun W => ↾fun y => y.1.2
      naturality := by intro W W' f; ext y; rfl }
  obtain ⟨e, he, hue⟩ := (hE R hR) (x.map iE) (hx.map iE)
  obtain ⟨a, ha, hua⟩ := (hY R hR) (x.map (fiberOverObjectToYoneda S σ))
    (hx.map (fiberOverObjectToYoneda S σ))
  have he' (V : C) (f : V ⟶ U) (hf : R.arrows f) : S.X₂.obj.map f.op e = (x f hf).1.2 :=
    he f hf
  have ha' (V : C) (f : V ⟶ U) (hf : R.arrows f) : f ≫ a = (x f hf).1.1 := ha f hf
  have heq : S.g.hom.app (op U) e = S.X₃.obj.map a.op σ := by
    apply (hQ R hR).isSeparatedFor.ext
    intro V f hf
    calc
      S.X₃.obj.map f.op (S.g.hom.app (op U) e) =
          S.g.hom.app (op V) (S.X₂.obj.map f.op e) :=
        (NatTrans.naturality_apply S.g.hom f.op e).symm
      _ = S.g.hom.app (op V) (x f hf).1.2 := by rw [he' V f hf]
      _ = S.X₃.obj.map (x f hf).1.1.op σ := (x f hf).2
      _ = S.X₃.obj.map f.op (S.X₃.obj.map a.op σ) := by
        rw [← ha' V f hf, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  refine ⟨⟨(a, e), heq⟩, ?_, ?_⟩
  · intro V f hf
    exact Subtype.ext (Prod.ext (ha' V f hf) (he' V f hf))
  · intro y hy
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact hua y.1.1 (hy.map (fiberOverObjectToYoneda S σ))
    · exact hue y.1.2 (hy.map iE)

/-- **The fibre over a section on an object has sections locally on the object**: over every
arrow of a covering sieve of `X` there is a section mapping to that arrow. -/
public lemma exists_cover_fiberOverObject [HasSheafify J AddCommGrpCat.{v}] (hS : S.ShortExact) :
    ∃ R ∈ J X, ∀ ⦃W : C⦄ (a : W ⟶ X), R a →
      ∃ l : (fiberOverObject S σ).obj (op W), (fiberOverObjectToYoneda S σ).app (op W) l = a := by
  refine ⟨Presheaf.imageSieve S.g.hom σ, shortExact_locallySurjective S hS (op X) σ, ?_⟩
  rintro W a ⟨t, ht⟩
  exact ⟨⟨(a, t), ht⟩, rfl⟩

/-- The morphism `h_W × X₁ ⟶ fiberOverObject S σ` attached to a section `(a, e)` on `W`: a pair
`(b, f)` over `V` goes to `(b ≫ a, b^* e + f)`. -/
public def fiberOverObjectTrivialization {W : C} (l : (fiberOverObject S σ).obj (op W)) :
    yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ fiberOverObject S σ where
  app V := ↾fun m =>
    ⟨(((prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V m) ≫ l.1.1,
      S.X₂.obj.map ((prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V m).op
          l.1.2 +
        S.f.hom.app V ((prod.snd : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V m)),
      by
        rw [map_add, shortComplex_sections_zero, add_zero, NatTrans.naturality_apply, l.2,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]⟩
  naturality := by
    intro V V' h
    ext m
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change (prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V'
          ((yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat)).map h m) ≫ l.1.1 =
        h.unop ≫ (prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V m ≫
          l.1.1
      rw [NatTrans.naturality_apply]
      exact Category.assoc _ _ _
    · change S.X₂.obj.map ((prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V'
            ((yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat)).map h m)).op l.1.2 +
          S.f.hom.app V' ((prod.snd : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V'
            ((yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat)).map h m)) =
        S.X₂.obj.map h (S.X₂.obj.map
            ((prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V m).op l.1.2 +
          S.f.hom.app V ((prod.snd : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app V m))
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, map_add,
        ← NatTrans.naturality_apply S.f.hom]
      congr 1
      change S.X₂.obj.map (h.unop ≫ (prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶
        _).app V m).op l.1.2 = _
      rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **Over a section on `W`, the fibre is `h_W × X₁`**: the square formed by
`fiberOverObjectTrivialization`, the first projection, the projection of the fibre and
`yoneda.map a` is cartesian. -/
public lemma isPullback_fiberOverObject [HasSheafify J AddCommGrpCat.{v}] (hS : S.ShortExact)
    {W : C} (l : (fiberOverObject S σ).obj (op W)) :
    IsPullback (fiberOverObjectTrivialization S σ l) prod.fst (fiberOverObjectToYoneda S σ)
      (yoneda.map l.1.1) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨V⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext m
    rfl
  · intro m m' ⟨h₁, h₂⟩
    have h₂' := congrArg (fun y => y.1.2) h₁
    refine prod_section_ext' h₂ ?_
    apply (shortExact_sections_left_exact S hS (op V)).1
    simp only [fiberOverObjectTrivialization] at h₂'
    change S.X₂.obj.map ((prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app
        (op V) m).op l.1.2 + _ = S.X₂.obj.map ((prod.fst : yoneda.obj W ⨯
        (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app (op V) m').op l.1.2 + _ at h₂'
    rw [show (prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app (op V) m =
      (prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app (op V) m' from h₂]
      at h₂'
    exact add_left_cancel h₂'
  · intro y b hyb
    change y.1.1 = b ≫ l.1.1 at hyb
    have hd : S.g.hom.app (op V) (y.1.2 - S.X₂.obj.map b.op l.1.2) = 0 := by
      rw [map_sub, y.2, NatTrans.naturality_apply, l.2, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← op_comp, hyb, sub_self]
    obtain ⟨f, hf⟩ := (shortExact_sections_left_exact S hS (op V)).2 _ hd
    refine ⟨prodSectionMk (A := yoneda.obj W) (B := S.X₁.obj ⋙ forget AddCommGrpCat) b f,
      ?_, fst_app_prodSectionMk _ _⟩
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change (prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app (op V)
        (prodSectionMk (A := yoneda.obj W) (B := S.X₁.obj ⋙ forget AddCommGrpCat) b f) ≫
          l.1.1 = y.1.1
      rw [fst_app_prodSectionMk, hyb]
    · change S.X₂.obj.map ((prod.fst : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app
          (op V) (prodSectionMk (A := yoneda.obj W) (B := S.X₁.obj ⋙ forget AddCommGrpCat)
            b f)).op l.1.2 +
        S.f.hom.app (op V) ((prod.snd : yoneda.obj W ⨯ (S.X₁.obj ⋙ forget AddCommGrpCat) ⟶ _).app
          (op V) (prodSectionMk (A := yoneda.obj W) (B := S.X₁.obj ⋙ forget AddCommGrpCat)
            b f)) = y.1.2
      rw [fst_app_prodSectionMk, snd_app_prodSectionMk, hf, add_sub_cancel]

end Stacks.Cohomology.Torsors

end

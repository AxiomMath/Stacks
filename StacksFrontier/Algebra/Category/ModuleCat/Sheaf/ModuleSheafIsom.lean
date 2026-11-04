module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHom
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of isomorphisms between two sheaves

Let `(C, J)` be a site and let `F`, `G` be two sheaves on it with values in a category `A`.
Stacks Tag 093T describes `Isom(F, G)` as the subsheaf of `SheafHom(F, G)` consisting of those
sections which have an inverse in `SheafHom(G, F)`. This file constructs it: a section of
`SheafHom(F, G)` over `X` is a morphism `F|_X ⟶ G|_X` on the slice site `C/X`, and having an
inverse in `SheafHom(G, F)` over `X` is exactly being an isomorphism there, so the subobject in
question is the one cut out by `CategoryTheory.IsIso`.

That this subobject is a sheaf is the statement that a morphism of sheaves which becomes
invertible after restriction along every member of a covering family is invertible. The local
inverses are compatible, because an inverse is unique, hence they glue to a section of
`SheafHom(G, F)`; the two composites restrict to the identity on the covering family, hence are
the identity because `SheafHom(F, F)` and `SheafHom(G, G)` are sheaves.

## Main definitions

* `Stacks.ConstantSheaf.sheafIsomSubfunctor`: the invertible sections of `SheafHom(F, G)`, as a
  subobject of the sheaf of types `CategoryTheory.sheafHom`.
* `Stacks.ConstantSheaf.sheafIsom`: `Isom(F, G)`, as a sheaf of sets.
* `Stacks.ConstantSheaf.moduleSheafIsom`: the same for sheaves of `Λ`-modules, i.e. the subsheaf
  of `Stacks.ConstantSheaf.moduleSheafHom` of sections invertible in the internal hom taken in
  the other order.

## Main results

* `Stacks.ConstantSheaf.isIso_of_isIso_overMapPullback_map`: a morphism of sheaves which is
  locally an isomorphism is an isomorphism.
* `Stacks.ConstantSheaf.isSheaf_sheafIsomSubfunctor`: the subobject above is a sheaf.

What this file supplies is the object that parts (2) and (4) of Tag 093T are statements about, so
`Stacks.ConstantSheaf.moduleSheafIsom` — Stacks's `Isom_{Λ̲}(F, G)` — carries the tag. The two
statements themselves, `Isom_Λ(M, N)̲ = Isom_{Λ̲}(M̲, N̲)` for finitely presented `M` and `N` and
local constancy of `Isom_{Λ̲}(F, G)` for locally constant `F` and `G` of finite presentation, are
proved in `ConstantSheafIsom.lean`.

## Implementation notes

The construction is carried out for an arbitrary coefficient category `A`, since nothing about
modules enters: `Isom` is a sheaf of sets in all cases, and the `Λ`-module version of Tag 093T is
the specialization to `A = ModuleCat Λ`. The ambient sheaf of types is Mathlib's
`CategoryTheory.sheafHom`, whose sections over `X` are by definition the morphisms
`F|_X ⟶ G|_X`; these are the same sections as those of `Stacks.ConstantSheaf.moduleSheafHom` in
the module case, which only adds the pointwise `Λ`-module structure, so the subobject described
by Stacks is literally the one built here.

The subobject is a `CategoryTheory.Subfunctor` of the underlying presheaf, and the sheaf
condition is `CategoryTheory.Subfunctor.isSheaf_iff`: a subobject of a sheaf of types is a sheaf
exactly when a section which lies in it locally lies in it. For the invertible sections that
implication is the gluing argument described above.

The local inverses are produced by `choose` rather than by `CategoryTheory.inv`, so that the
compatibility of the family is the uniqueness of a two-sided inverse
(`Stacks.ConstantSheaf.eq_of_comp_id_of_comp_id`) rather than a rewrite underneath an instance
argument.

Restriction along `CategoryTheory.Over.map` is compatible with composition only up to the
associator of the site, so the functoriality used throughout is that of the presheaf
`CategoryTheory.sheafHom` itself (`Stacks.ConstantSheaf.sheafHom_obj_map_op_comp`) rather than an
identity between restriction functors. For the same reason the steps of the gluing argument are
`congrArg` and `Eq.trans` rather than `rw`: a section of the internal hom and the local morphism
it is are only definitionally, not syntactically, the same term, which is below the transparency
at which `rw` checks its motive.

## References

* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w x u' v'

namespace Stacks.ConstantSheaf

/-- A two-sided inverse is unique: a right inverse of a morphism agrees with any left inverse
of it. -/
theorem eq_of_comp_id_of_comp_id {D : Type*} [Category D] {P Q : D} (u : P ⟶ Q) (b b' : Q ⟶ P)
    (hb : u ≫ b = 𝟙 P) (hb' : b' ≫ u = 𝟙 Q) : b = b' :=
  calc b = 𝟙 Q ≫ b := (Category.id_comp b).symm
    _ = (b' ≫ u) ≫ b := by rw [hb']
    _ = b' ≫ u ≫ b := Category.assoc _ _ _
    _ = b' ≫ 𝟙 P := by rw [hb]
    _ = b' := Category.comp_id b'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ### A morphism of sheaves which is locally an isomorphism is an isomorphism -/

section LocallyIso

variable {A : Type u'} [Category.{v'} A] {F G : Sheaf J A}

/-- The restriction maps of the internal hom are restriction of local morphisms along
`CategoryTheory.Over.map`. -/
theorem sheafHom_obj_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (γ : (sheafHom F G).obj.obj X) :
    (sheafHom F G).obj.map f γ = (J.overMapPullback A f.unop).map γ :=
  rfl

/-- Restriction along a composite, in the internal hom. This is the functoriality of the internal
hom; it is not an identity of restriction functors, since `CategoryTheory.Over.map` is only
compatible with composition up to the associator. -/
theorem sheafHom_obj_map_op_comp {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)
    (γ : (sheafHom F G).obj.obj (op X)) :
    (sheafHom F G).obj.map (g ≫ f).op γ =
      (sheafHom F G).obj.map g.op ((sheafHom F G).obj.map f.op γ) :=
  (sheafHom F G).obj.map_comp_apply f.op g.op γ

/-- Restriction along a morphism of the site preserves a right inverse. -/
theorem comp_overMapPullback_map_eq_id {X Z : C} (g : Z ⟶ X)
    (c : (J.overPullback A X).obj F ⟶ (J.overPullback A X).obj G)
    (b : (J.overPullback A X).obj G ⟶ (J.overPullback A X).obj F) (hb : c ≫ b = 𝟙 _) :
    (J.overMapPullback A g).map c ≫ (J.overMapPullback A g).map b = 𝟙 _ := by
  rw [← Functor.map_comp, hb, CategoryTheory.Functor.map_id]

/-- Restriction along a morphism of the site preserves a left inverse. -/
theorem overMapPullback_map_comp_eq_id {X Z : C} (g : Z ⟶ X)
    (c : (J.overPullback A X).obj F ⟶ (J.overPullback A X).obj G)
    (b : (J.overPullback A X).obj G ⟶ (J.overPullback A X).obj F) (hb : b ≫ c = 𝟙 _) :
    (J.overMapPullback A g).map b ≫ (J.overMapPullback A g).map c = 𝟙 _ := by
  rw [← Functor.map_comp, hb, CategoryTheory.Functor.map_id]

/-- **A morphism of sheaves which is locally an isomorphism is an isomorphism.** The inverses of
the restrictions along a covering family are compatible, because a two-sided inverse is unique, so
they glue to a morphism in the other direction; the two composites restrict to the identity on the
covering family, hence are the identity because the internal homs `SheafHom(F, F)` and
`SheafHom(G, G)` are sheaves. -/
theorem isIso_of_isIso_overMapPullback_map {X : C}
    (α : (J.overPullback A X).obj F ⟶ (J.overPullback A X).obj G)
    {S : Sieve X} (hS : S ∈ J X)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → IsIso ((J.overMapPullback A f).map α)) :
    IsIso α := by
  classical
  have hQ : Presieve.IsSheaf J (sheafHom G F).obj :=
    (isSheaf_iff_isSheaf_of_type J _).1 (sheafHom G F).property
  choose β hβ₁ hβ₂ using fun (Y : C) (f : Y ⟶ X) (hf : S f) => (h f hf).out
  have hres : ∀ {Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X),
      (sheafHom F G).obj.map (g ≫ f).op α =
        (J.overMapPullback A g).map ((J.overMapPullback A f).map α) :=
    fun g f => sheafHom_obj_map_op_comp J g f α
  let β' : Presieve.FamilyOfElements (sheafHom G F).obj S.arrows := fun _ f hf => β _ f hf
  have hβ : β'.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ e
    refine eq_of_comp_id_of_comp_id
      ((J.overMapPullback A g₁).map ((J.overMapPullback A f₁).map α)) _ _
      (comp_overMapPullback_map_eq_id J g₁ _ _ (hβ₁ _ f₁ hf₁)) ?_
    have key : (J.overMapPullback A g₁).map ((J.overMapPullback A f₁).map α) =
        (J.overMapPullback A g₂).map ((J.overMapPullback A f₂).map α) :=
      ((hres g₁ f₁).symm.trans
        (congrArg (fun t : Z ⟶ X => (sheafHom F G).obj.map t.op α) e)).trans (hres g₂ f₂)
    exact (congrArg (fun t => (J.overMapPullback A g₂).map (β _ f₂ hf₂) ≫ t) key).trans
      (overMapPullback_map_comp_eq_id J g₂ _ _ (hβ₂ _ f₂ hf₂))
  obtain ⟨γ, hγ, -⟩ := hQ S hS β' hβ
  have key : ∀ (H : Sheaf J A) (φ : (J.overPullback A X).obj H ⟶ (J.overPullback A X).obj H),
      (∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → (J.overMapPullback A f).map φ = 𝟙 _) → φ = 𝟙 _ :=
    fun H φ hφ => ((isSheaf_iff_isSheaf_of_type J _).1 (sheafHom H H).property S hS
      ).isSeparatedFor.ext fun Y f hf =>
        (hφ f hf).trans (CategoryTheory.Functor.map_id (J.overMapPullback A f) _).symm
  have h₁ : α ≫ γ = 𝟙 _ := key F _ fun Y f hf =>
    ((J.overMapPullback A f).map_comp α γ).trans
      (((congrArg (fun t => (J.overMapPullback A f).map α ≫ t) (hγ f hf)).trans
        (hβ₁ _ f hf)))
  have h₂ : γ ≫ α = 𝟙 _ := key G _ fun Y f hf =>
    ((J.overMapPullback A f).map_comp γ α).trans
      (((congrArg (fun t => t ≫ (J.overMapPullback A f).map α) (hγ f hf)).trans
        (hβ₂ _ f hf)))
  exact ⟨γ, h₁, h₂⟩

end LocallyIso

/-! ### The sheaf of isomorphisms -/

section Isom

variable (A : Type u') [Category.{v'} A]

/-- The invertible sections of the internal hom, as a subobject of `CategoryTheory.sheafHom`.
A section over `X` is a morphism `F|_X ⟶ G|_X`, and it is invertible exactly when it has an
inverse in `SheafHom(G, F)` over `X`, which is Stacks's description of `Isom(F, G)`. -/
@[sga "3 I 1.7.2" "more general"]
def sheafIsomSubfunctor (F G : Sheaf J A) : Subfunctor (sheafHom F G).obj where
  obj _ := { α | IsIso α }
  map {_ _} i := fun α hα => by
    have : IsIso α := hα
    exact Functor.map_isIso (J.overMapPullback A i.unop) α

/-- The invertible sections of the internal hom form a sheaf: a section which is locally
invertible is invertible. -/
theorem isSheaf_sheafIsomSubfunctor (F G : Sheaf J A) :
    Presheaf.IsSheaf J (sheafIsomSubfunctor J A F G).toFunctor := by
  have hP : Presieve.IsSheaf J (sheafHom F G).obj :=
    (isSheaf_iff_isSheaf_of_type J _).1 (sheafHom F G).property
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ hP]
  intro X α hα
  refine isIso_of_isIso_overMapPullback_map J α hα ?_
  intro Y f hf
  exact hf

/-- **`Isom(F, G)`.** The sheaf of sets whose sections over `X` are the isomorphisms
`F|_X ≅ G|_X` on the slice site `C/X`, realized as the subsheaf of `SheafHom(F, G)` of those
sections which have an inverse in `SheafHom(G, F)`. -/
def sheafIsom (F G : Sheaf J A) : Sheaf J (Type (max u v v')) :=
  ⟨(sheafIsomSubfunctor J A F G).toFunctor, isSheaf_sheafIsomSubfunctor J A F G⟩

/-- A section of `Isom(F, G)` over `X` is an invertible morphism `F|_X ⟶ G|_X`. -/
theorem sheafIsom_obj_obj (F G : Sheaf J A) (X : Cᵒᵖ) :
    (sheafIsom J A F G).obj.obj X =
      { α : (J.overPullback A X.unop).obj F ⟶ (J.overPullback A X.unop).obj G // IsIso α } :=
  rfl

end Isom

/-! ### The sheaf of isomorphisms of two sheaves of modules -/

section Module

variable (Λ : Type w) [CommRing Λ]

/-- **The sheaf of isomorphisms of two sheaves of `Λ`-modules**, i.e. Stacks's
`Isom_{Λ̲}(F, G)`: the subsheaf of `Stacks.ConstantSheaf.moduleSheafHom` of those sections which
have an inverse in `Stacks.ConstantSheaf.moduleSheafHom` taken in the other order. The sections
of the internal hom of sheaves of `Λ`-modules over `X` are the morphisms `F|_X ⟶ G|_X` of sheaves
of `Λ`-modules, which are also the sections of `CategoryTheory.sheafHom`, so this is the
subobject Stacks describes. -/
@[stacks 093T "the sheaf Isom"]
def moduleSheafIsom (F G : Sheaf J (ModuleCat.{max u v x} Λ)) :
    Sheaf J (Type (max u v x)) :=
  sheafIsom J (ModuleCat.{max u v x} Λ) F G

/-- A section of `Isom_{Λ̲}(F, G)` over `X` is an invertible section of the internal hom. -/
theorem moduleSheafIsom_obj_obj (F G : Sheaf J (ModuleCat.{max u v x} Λ)) (X : Cᵒᵖ) :
    (moduleSheafIsom J Λ F G).obj.obj X =
      { α : (moduleSheafHom J Λ F G).obj.obj X // IsIso α } :=
  rfl

end Module

end Stacks.ConstantSheaf

end

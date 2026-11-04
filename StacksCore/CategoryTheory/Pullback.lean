module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.TFAE
import StacksCore.Tactic.StacksAttribute

/-! # Pullbacks

This file formalizes the Stacks project section 001U and section 0021.

-/

@[expose] public section

section

add_to_stacks 001V CategoryTheory.IsPullback
add_to_stacks 001V "Uniqueness" CategoryTheory.IsPullback.isoIsPullback

add_to_stacks 08N0 CategoryTheory.IsPullback

add_to_stacks 001X "When the functor is the identity, we recover 001X"
  CategoryTheory.Functor.relativelyRepresentable

add_to_stacks 001X CategoryTheory.Limits.HasPullbacksAlong

add_to_stacks 001Z "Representable morphisms are stable under base change"
  CategoryTheory.Functor.relativelyRepresentable.isStableUnderBaseChange

add_to_stacks 001Y
  "the id functor is multiplicative, hence representable morphisms are stable under composition"
  CategoryTheory.Functor.relativelyRepresentable.isMultiplicative

open CategoryTheory CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/--
The following are equivalent:
1. `f : x ⟶ y` is representable in the sense of stacks tag 001X.
2. `f : x ⟶ y` is representable relative to the identity functor.
3. for any `g : z ⟶ y`, the pullback of `f` and `g` exists.
-/
@[stacks 001X "equivalent conditions for representable morphisms", sga "3 IV 1.4.0", sga "4 I 10.7"]
lemma CategoryTheory.Functor.id_relativelyRepresentable_iff_hasPullbacksAlong
    {x y : C} (f : x ⟶ y) :
    (𝟭 C).relativelyRepresentable f ↔ HasPullbacksAlong f := by
  constructor
  · intro h z g
    have : HasPullback f g := ⟨_, h.isPullback g |>.isLimit⟩
    exact hasPullback_symmetry ..
  · intro h z g
    obtain ⟨⟨⟨_, h⟩⟩⟩ := h g
    exact ⟨_, _, _, .flip (IsPullback.of_isLimit h)⟩

end

section

add_to_stacks 0022 "existence" CategoryTheory.Limits.functorCategoryHasLimit
add_to_stacks 0022 "pointwise formula" CategoryTheory.Limits.limitObjIsoLimitCompEvaluation

add_to_stacks 0023
  "The definition is same as saying the presheaf morphism `a : F ⟶ G` is representable relative to
  the yoneda functor"
  CategoryTheory.Functor.relativelyRepresentable

add_to_stacks 0024
  CategoryTheory.Functor.relativelyRepresentable.diag_iff

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- **Stacks 0023** (Equivalent definitions of representable presheaf morphisms).
A morphism of presheaves `a : F ⟶ G` on `𝒞` is relatively representable along the Yoneda embedding
if and only if for every object `U : 𝒞` and every section `ξ ∈ G(U)` the pullback presheaf
`h_U ×_G F` is representable. -/
@[stacks 0023 "Equivalent definitions of representable presheaf morphisms"]
lemma CategoryTheory.yoneda_relativelyRepresentable_iff_pullback_representable
  {F G : 𝒞ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
  yoneda.relativelyRepresentable a ↔
  ∀ (U : 𝒞) (ξ : G.obj (op U)), (pullback (yonedaEquiv.symm ξ) a).IsRepresentable := by
  constructor
  · intro ha U ξ
    obtain ⟨V, snd, fst, hpb⟩ := ha (yonedaEquiv.symm ξ)
    refine Functor.IsRepresentable.mk' (X := V) ?_
    simpa using (hpb.isoIsPullback _ _ (IsPullback.of_hasPullback a _) ≪≫
      pullbackSymmetry a (yonedaEquiv.symm ξ))
  · intro h A g
    have : (pullback g a).IsRepresentable := by
      simpa using h A (yonedaEquiv g)
    let i := Functor.reprW (pullback g a) ≪≫ pullbackSymmetry g a
    exact ⟨_, yoneda.preimage <| i.hom ≫ pullback.snd a g, i.hom ≫ pullback.fst a g, by
      simpa using .of_iso_pullback (.mk <| congr(i.hom ≫ $pullback.condition)) i rfl rfl⟩

/-- **Stacks 03KC**.
If `a : F ⟶ G` is a representable morphism of presheaves on `𝒞` and the target `G` is itself
representable, then so is `F`. -/
@[stacks 03KC]
lemma CategoryTheory.Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
    {F G : 𝒞ᵒᵖ ⥤ Type v} (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a)
    [hG : G.IsRepresentable] : F.IsRepresentable := by
  obtain ⟨A, snd, fst, hpb⟩ := ha G.reprW.hom
  have := hpb.isIso_fst_of_isIso
  exact isRepresentable_of_natIso (yoneda.obj A) (asIso fst)


/-- **Stacks 0024**.
For a presheaf `F` on a category `𝒞` with binary products and pullbacks, the following are
equivalent:
1. the diagonal `Δ : F ⟶ F × F` is representable along Yoneda;
2. for every `U : 𝒞` and every `ξ ∈ F(U)`, the morphism `yonedaEquiv.symm ξ : h_U ⟶ F` is
   representable along Yoneda;
3. for every pair `U, V : 𝒞` and sections `ξ ∈ F(U)`, `ξ' ∈ F(V)`, the pullback presheaf
   `h_U ×_F h_V` is representable. -/
@[stacks 0024]
lemma CategoryTheory.yoneda_relativelyRepresentable_diag_tfae
    (F : 𝒞ᵒᵖ ⥤ Type v) [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] : List.TFAE
    [
      yoneda.relativelyRepresentable (diag F),
      ∀ (U) (ξ : F.obj (op U)), yoneda.relativelyRepresentable (yonedaEquiv.symm ξ),
      ∀ (U V) (ξ : F.obj (op U)) (ξ' : F.obj (op V)),
        (pullback (yonedaEquiv.symm ξ) (yonedaEquiv.symm ξ')).IsRepresentable
    ] := by
  tfae_have 1 → 2 := fun h U ξ => Functor.relativelyRepresentable.diag_iff.1 h _
  tfae_have 2 → 3 := fun h U V ξ ξ' => yoneda_relativelyRepresentable_iff_pullback_representable _
    |>.1 (h V ξ') U ξ
  tfae_have 3 → 1 := fun h => (CategoryTheory.Functor.relativelyRepresentable.diag_iff).2
    fun U g => CategoryTheory.yoneda_relativelyRepresentable_iff_pullback_representable g |>.2
    fun V ξ' => by simpa using h V U ξ' (yonedaEquiv g)
  tfae_finish

end

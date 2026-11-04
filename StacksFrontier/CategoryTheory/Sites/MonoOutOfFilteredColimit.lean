module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Monomorphy of a morphism out of a filtered colimit of sheaves of sets

A morphism `m : colim_i F i ⟶ T` out of a filtered colimit of sheaves of sets is a monomorphism
as soon as each composite `F i ⟶ colim_i F i ⟶ T` is one.

`CategoryTheory.Sheaf.mono_colimit_ι_of_mono_transition` says that the colimit injections of such
a colimit are monomorphisms when its transition morphisms are; the statement here is the
complementary one, about a morphism *out* of the colimit, and together they give monomorphy of the
comparison morphism `colim_{n} F (ν n) ⟶ colim_{i} F i` induced by a functor `ν` into the index
category — the step that lets a fibre product over a formal algebraic space be replaced by a fibre
product over a sub-colimit of its presentation, as in the proof of Stacks 0GBB.

## Main results

* `CategoryTheory.Sheaf.mono_of_mono_colimit_ι_comp`: a morphism out of a filtered colimit of
  sheaves of sets whose composites with the colimit injections are monomorphisms is a
  monomorphism.
* `CategoryTheory.Sheaf.mono_colimit_pre_of_mono_transition`: a sub-colimit of a filtered colimit
  of sheaves of sets with monomorphic transition morphisms injects into it.

## Implementation notes

The source of `m` is a sheaf, so monomorphy is local injectivity
(`CategoryTheory.Sheaf.mono_of_isLocallyInjective`). Two sections of the colimit over an object
`W` with the same image under `m` are, locally on `W`, in the images of two colimit injections
(`Stacks.Sites.FilteredColimitSections.exists_local_section`); filteredness of the index category
pushes both local sections into a single `F k`, where they have the same image under
`F k ⟶ colim F ⟶ T`, which is a monomorphism and hence injective on sections. So the two local
sections agree there, and their images in the colimit — the restrictions of the two given
sections — agree.

No hypothesis on the transition morphisms of `F` is needed: it is monomorphy of the composites,
not of the transitions, that does the work.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₄ w₃ w₂ w₁ v u

namespace CategoryTheory.Sheaf

/-- **A morphism out of a filtered colimit of sheaves of sets is a monomorphism as soon as its
composites with the colimit injections are.**

Together with `CategoryTheory.Sheaf.mono_colimit_ι_of_mono_transition` this makes the comparison
morphism `colim_n F (ν n) ⟶ colim_i F i`, for a functor `ν` into the index category of a filtered
colimit with monomorphic transition morphisms, a monomorphism. -/
theorem mono_of_mono_colimit_ι_comp {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {I : Type w₁} [Category.{w₂} I] [IsFiltered I] [HasColimitsOfShape I (Type (max u v))]
    (F : I ⥤ Sheaf J (Type (max u v))) {T : Sheaf J (Type (max u v))} (m : colimit F ⟶ T)
    (hmono : ∀ i, Mono (colimit.ι F i ≫ m)) :
    Mono m := by
  have hinj : ∀ (i : I) (V : C), Function.Injective ((colimit.ι F i ≫ m).hom.app (op V)) :=
    fun i V ↦ (CategoryTheory.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app (colimit.ι F i ≫ m).hom).1
        ((Sheaf.Hom.mono_iff_presheaf_mono J (Type (max u v)) _).1 (hmono i)) (op V))
  have hι : ∀ (i k : I) (f : i ⟶ k) (V : C) (z : (F.obj i).obj.obj (op V)),
      (colimit.ι F k).hom.app (op V) ((F.map f).hom.app (op V) z) =
        (colimit.ι F i).hom.app (op V) z := fun i k f V z ↦ by
    rw [← NatTrans.comp_app_apply, ← ObjectProperty.FullSubcategory.comp_hom, colimit.w F f]
  have hli : Sheaf.IsLocallyInjective m := by
    constructor
    intro W x y hxy
    obtain ⟨S₁, hS₁, h₁⟩ :=
      Stacks.Sites.FilteredColimitSections.exists_local_section' F W.unop x
    obtain ⟨S₂, hS₂, h₂⟩ :=
      Stacks.Sites.FilteredColimitSections.exists_local_section' F W.unop y
    refine J.superset_covering (fun V g hg ↦ ?_) (J.intersection_covering hS₁ hS₂)
    obtain ⟨i, a, ha⟩ := h₁ g hg.1
    obtain ⟨i', b, hb⟩ := h₂ g hg.2
    have hak := (hι i _ (IsFiltered.leftToMax i i') V a).trans ha
    have hbk := (hι i' _ (IsFiltered.rightToMax i i') V b).trans hb
    have hab : (F.map (IsFiltered.leftToMax i i')).hom.app (op V) a =
        (F.map (IsFiltered.rightToMax i i')).hom.app (op V) b := by
      refine hinj (IsFiltered.max i i') V ?_
      rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app_apply,
        NatTrans.comp_app_apply, hak, hbk, m.hom.naturality_apply g.op x,
        m.hom.naturality_apply g.op y, hxy]
    show (colimit F).obj.map g.op x = (colimit F).obj.map g.op y
    rw [← hak, ← hbk, hab]
  exact Sheaf.mono_of_isLocallyInjective m

/-- **A sub-colimit of a filtered colimit of sheaves of sets with monomorphic transition
morphisms injects into it.** For a functor `ν : N ⥤ Λ` out of a filtered category, the
comparison morphism `colim_n F (ν n) ⟶ colim_i F i` is a monomorphism.

Its composite with the `n`-th colimit injection is the colimit injection of `F (ν n)`, which is
a monomorphism by `CategoryTheory.Sheaf.mono_colimit_ι_of_mono_transition`; so
`mono_of_mono_colimit_ι_comp` applies.

This is the form in which the proof of **Stacks 0GBB** replaces the base of a fibre product of
affine formal algebraic spaces by a countably indexed one: the base `V` is presented as a
directed colimit of affine thickenings, the two morphisms into it factor through countably many
stages, and the colimit `V'` of those stages maps to `V` by a monomorphism — which is what makes
`U ×_V W` and `U ×_{V'} W` agree, by
`CategoryTheory.IsPullback` cancellation along a monomorphism. -/
@[sga "4 I 8.12.1" "Forward implication"]
theorem mono_colimit_pre_of_mono_transition {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {Λ : Type w₁} [Category.{w₂} Λ] [IsFiltered Λ]
    [HasColimitsOfShape Λ (Type (max u v))] {N : Type w₃} [Category.{w₄} N] [IsFiltered N]
    [HasColimitsOfShape N (Type (max u v))] (F : Λ ⥤ Sheaf J (Type (max u v)))
    (hmono : ∀ i j (f : i ⟶ j), Mono (F.map f)) (ν : N ⥤ Λ) :
    Mono (colimit.pre F ν) :=
  mono_of_mono_colimit_ι_comp (ν ⋙ F) (colimit.pre F ν) fun n ↦ by
    rw [colimit.ι_pre]
    exact mono_colimit_ι_of_mono_transition F hmono (ν.obj n)

end CategoryTheory.Sheaf

end

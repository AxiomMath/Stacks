module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections

/-!
# Sections over a separably closed field are fibres

`Stacks.EtaleCohomology.isIso_toPresheafFiber_etaleMkId_of_isSepClosed`: over a separably closed
field `k`, sections over the final object `Spec k` of the small étale site are the fibre at any
geometric point. (Ported from the C1103b work, as an addition to `SubmersiveSections.lean`; the two
base-private facts it uses are proved inline.)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MorphismProperty
open AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- **Over a separably closed field the final object is an initial neighbourhood of every
geometric point.** For `k` separably closed and a geometric point `x` of `Spec k`, the canonical
map from the sections of a presheaf over the final object `Spec k` of the small étale site to its
fibre at `x` is an isomorphism, the coefficients being arbitrary: every étale neighbourhood of
`x` receives a unique morphism from `(Spec k, x)`, an étale `k`-scheme having a section through
each of its points. -/
public theorem isIso_toPresheafFiber_etaleMkId_of_isSepClosed (k : Type u) [Field k]
    [IsSepClosed k] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of k))
    {A : Type*} [Category* A] [HasColimitsOfSize.{u, u} A]
    (P : (Spec (.of k)).Etaleᵒᵖ ⥤ A) :
    IsIso ((pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 (Spec (.of k))))
      (Over.homMk x (by change x ≫ 𝟙 _ = x; simp)) P) := by
  -- a morphism `t` from a point into `U`, meeting a section `s` of `U`, factors through `s`
  have hfac : ∀ (U : (Spec (.of k)).Etale) {s : Spec (.of k) ⟶ U.left} {Z : Scheme.{u}}
      [Inhabited Z] [Subsingleton Z] {t : Z ⟶ U.left} {y : Z ⟶ Spec (.of k)},
      s ≫ U.hom = 𝟙 _ → t ≫ U.hom = y → s default = t default → t = y ≫ s := by
    intro U s Z _ _ t y hs ht hp
    have := Unramified.section_isOpenImmersion U.hom s hs
    have hr : Set.range t ⊆ Set.range s := by
      rintro _ ⟨z, rfl⟩
      exact ⟨default, by rw [hp, Subsingleton.elim z default]⟩
    have h := congrArg (· ≫ U.hom) (IsOpenImmersion.lift_fac s t hr)
    simp only [Category.assoc, hs, Category.comp_id] at h
    rw [← IsOpenImmersion.lift_fac s t hr, h.trans ht]
  -- an `Ω`-point of an étale `k`-scheme lying over `x` is `x` followed by a section
  have hsec : ∀ (U : (Spec (.of k)).Etale) (a : Spec (.of Ω) ⟶ U.left), a ≫ U.hom = x →
      ∃ b : Spec (.of k) ⟶ U.left, b ≫ U.hom = 𝟙 _ ∧ x ≫ b = a := by
    intro U a ha
    obtain ⟨b, hb, hy⟩ := exists_fac_of_etale_of_isSepClosed U.hom (𝟙 _)
      (a default) (Subsingleton.elim (α := Spec (.of k)) _ _)
    exact ⟨b, hb, (hfac U hb ha hy).symm⟩
  -- two sections that agree after composing with `x` are equal
  have heq : ∀ (U : (Spec (.of k)).Etale) {s t : Spec (.of k) ⟶ U.left},
      s ≫ U.hom = 𝟙 _ → t ≫ U.hom = 𝟙 _ → x ≫ s = x ≫ t → s = t := by
    intro U s t hs ht h
    refine ((hfac U hs ht ?_).trans (Category.id_comp _)).symm
    have hx : x default = (default : Spec (.of k)) := Subsingleton.elim _ _
    simpa only [Scheme.Hom.comp_apply, hx] using congrArg (· default) h
  have hinit : IsInitial (show (pointSmallEtale x).fiber.Elements from
      (pointSmallEtale x).fiber.elementsMk (Scheme.Etale.mk (𝟙 (Spec (.of k))))
        (Over.homMk x (by
          change x ≫ 𝟙 _ = x
          simp))) := by
    classical
    let sectionOf (U : (pointSmallEtale x).fiber.Elements) :=
      (hsec U.obj U.val.left (Over.w U.val)).choose
    have hsection (U : (pointSmallEtale x).fiber.Elements) :
        sectionOf U ≫ U.obj.hom = 𝟙 _ ∧ x ≫ sectionOf U = U.val.left :=
      (hsec U.obj U.val.left (Over.w U.val)).choose_spec
    refine IsInitial.ofUniqueHom
      (fun U : (pointSmallEtale x).fiber.Elements ↦ Functor.Elements.homMk
        (MorphismProperty.Over.homMk (sectionOf U) (hsection U).1)
        (Over.OverMorphism.ext (hsection U).2))
      (fun U morphism ↦ ?_)
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact heq U.obj (MorphismProperty.Over.w morphism.hom) (hsection U).1
      ((congrArg (·.left) morphism.map_val).trans (hsection U).2.symm)
  exact ((pointSmallEtale x).isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal _
    hinit.op

end Stacks.EtaleCohomology

end

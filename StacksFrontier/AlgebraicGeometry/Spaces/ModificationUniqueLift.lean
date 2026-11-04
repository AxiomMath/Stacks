module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications

/-!
# Lifting a morphism through a modification over the untouched subspace

Let `W` be a presheaf on the big fppf site of a scheme `S`, let `W₀` be a subfunctor of `W` and
let `X ⟶ W` be an algebraic space over `W` which is unchanged over `W₀`, that is, whose base
change to `W₀` is an isomorphism. Then every morphism `A ⟶ W` which factors through `W₀` lifts
through `X ⟶ W`, and the lift is unique: the base change of `X` to `W₀` being `W₀` itself, a
lift is the same datum as a factorisation through `W₀`.

This is the mechanism by which a modification is rigid away from the locus it modifies, and it
is used in two ways: a morphism into the modification is *forced* wherever its target morphism
avoids that locus, and two morphisms into a modification agree there.

## Main results

* `AlgebraicGeometry.Space.existsUnique_lift_of_isIso_pullback_snd`: a morphism to `W` factoring
  through `W₀` has exactly one lift through a morphism whose base change to `W₀` is an
  isomorphism.
* `AlgebraicGeometry.Space.lift_eq_of_isIso_pullback_snd`: two lifts of such a morphism agree.
* `AlgebraicGeometry.Space.exists_lift_of_isIso_pullback_snd`: the existence half.
* `AlgebraicGeometry.Space.eq_of_app_eq_of_mem_of_isIso_pullback_snd`: the same uniqueness read
  on sections, which is the form in which it is used to compare two descents.
* `AlgebraicGeometry.Space.exists_pullback_obj`: a section of a fibre product of presheaves may
  be assembled from two sections with the same image. This is the universal property of the
  fibre product read through `CategoryTheory.yonedaEquiv`; the converse, that a section is
  determined by its two components, is `AlgebraicGeometry.Space.pullback_obj_ext`, already in
  the development.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Sections of a fibre product of presheaves -/

/-- **A pair of sections with the same image assembles into a section of the fibre product.** -/
theorem exists_pullback_obj {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ W) (g : Y ⟶ W)
    {A : BigFppfOver B S hS} (x : X.obj (op A)) (y : Y.obj (op A))
    (h : f.app (op A) x = g.app (op A) y) :
    ∃ p : (pullback f g).obj (op A), (pullback.fst f g).app (op A) p = x ∧
      (pullback.snd f g).app (op A) p = y := by
  have hw : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm y ≫ g := by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h]
  refine ⟨yonedaEquiv (pullback.lift _ _ hw), ?_, ?_⟩
  · rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- **A morphism factoring through `W₀` lifts uniquely through a morphism which is an
isomorphism over `W₀`.** If the base change of `g : X ⟶ W` to a subfunctor `W₀` of `W` is an
isomorphism and `a : A ⟶ W` factors through `W₀`, there is exactly one `b : A ⟶ X` with
`b ≫ g = a`. -/
theorem existsUnique_lift_of_isIso_pullback_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W₀ : Subfunctor W} (g : X ⟶ W) (hg : IsIso (pullback.snd g W₀.ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ W) (a' : A ⟶ W₀.toFunctor)
    (ha' : a' ≫ W₀.ι = a) :
    ∃! b : A ⟶ X, b ≫ g = a := by
  have _ := hg
  have hfac : (a' ≫ inv (pullback.snd g W₀.ι) ≫ pullback.fst g W₀.ι) ≫ g = a := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (inv _),
      IsIso.inv_hom_id, Category.id_comp, ha']
  refine ⟨a' ≫ inv (pullback.snd g W₀.ι) ≫ pullback.fst g W₀.ι, hfac, ?_⟩
  intro b hb
  have hl : pullback.lift b a' (hb.trans ha'.symm) = a' ≫ inv (pullback.snd g W₀.ι) :=
    (IsIso.eq_comp_inv _).2 (pullback.lift_snd _ _ _)
  rw [← Category.assoc, ← hl, pullback.lift_fst]

/-- The existence half of `AlgebraicGeometry.Space.existsUnique_lift_of_isIso_pullback_snd`. -/
theorem exists_lift_of_isIso_pullback_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W₀ : Subfunctor W} (g : X ⟶ W) (hg : IsIso (pullback.snd g W₀.ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ W) (a' : A ⟶ W₀.toFunctor)
    (ha' : a' ≫ W₀.ι = a) :
    ∃ b : A ⟶ X, b ≫ g = a :=
  (existsUnique_lift_of_isIso_pullback_snd B S hS g hg a a' ha').exists

/-- **Two morphisms into a modification which agree over `W₀` agree.** Any two lifts through a
morphism which is an isomorphism over `W₀` of a morphism factoring through `W₀` are equal. -/
theorem lift_eq_of_isIso_pullback_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W₀ : Subfunctor W} (g : X ⟶ W) (hg : IsIso (pullback.snd g W₀.ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a' : A ⟶ W₀.toFunctor) (b₁ b₂ : A ⟶ X)
    (hb₁ : b₁ ≫ g = a' ≫ W₀.ι) (hb₂ : b₂ ≫ g = a' ≫ W₀.ι) :
    b₁ = b₂ :=
  (existsUnique_lift_of_isIso_pullback_snd B S hS g hg (a' ≫ W₀.ι) a' rfl).unique hb₁ hb₂

/-- **The uniqueness of the lift, read on sections.** Two sections of `X` over an object of the
site which lie over one section of `W` belonging to `W₀` are equal. -/
theorem eq_of_app_eq_of_mem_of_isIso_pullback_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W₀ : Subfunctor W} (g : X ⟶ W) (hg : IsIso (pullback.snd g W₀.ι))
    {A : BigFppfOver B S hS} (t : W.obj (op A)) (ht : t ∈ W₀.obj (op A))
    (z₁ z₂ : X.obj (op A)) (h₁ : g.app (op A) z₁ = t) (h₂ : g.app (op A) z₂ = t) :
    z₁ = z₂ := by
  have hle : Subfunctor.range (yonedaEquiv.symm t) ≤ W₀ := by
    rintro C y ⟨a, rfl⟩
    exact W₀.map a.op ht
  refine yonedaEquiv.symm.injective
    (lift_eq_of_isIso_pullback_snd B S hS g hg
      (Subfunctor.lift (yonedaEquiv.symm t) hle) _ _ ?_ ?_)
  · rw [Subfunctor.lift_ι, yonedaEquiv_symm_naturality_right, h₁]
  · rw [Subfunctor.lift_ι, yonedaEquiv_symm_naturality_right, h₂]

end AlgebraicGeometry.Space

end

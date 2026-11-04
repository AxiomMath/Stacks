module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceGeneralCase
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelocalizedSectionsFibre
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverMap

/-!
# Restriction of scalars over an object of the site is a relocalized space of sections

Let `S` be a scheme contained in a big fppf site and let `U` be an object of the big fppf site
over `S`. The restriction of scalars of Stacks 05YA is formed on the big fppf site of `S`: for
`w : W ⟶ Z_U` a morphism of algebraic spaces over `S` and `ζ : Z_U ⟶ h_U`, it is the functor
assigning to a test object `T` a morphism `T ⟶ U` together with a section of `W_T ⟶ (Z_U)_T`.
The space of sections of Stacks 05XR, `AlgebraicGeometry.Space.sectionSpace`, is instead formed
on the big fppf site of a *base scheme*. This file identifies the two, for the data that comes
from the site over the scheme `U.left.1` underlying `U`.

Concretely, let `Z₀` be an object of the big fppf site of `U.left.1` and let `w₀ : W₀ ⟶ h_{Z₀}`
be a morphism of presheaves there. Writing `Λ` for the lower-shriek relocalization along the
structural morphism of `U`, Stacks 03I5 part (2)
(`CategoryTheory.OverShriek.relocalizePresheafFunctor`), the data `Z₀`, `w₀` produces data over
`S`: the object `Z_U = j Z₀` of the site over `S`
(`AlgebraicGeometry.Space.relocalizedBase`), its structural morphism to `U`, the algebraic space
`Λ W₀` — an algebraic space by Stacks 03I4 part (3),
`AlgebraicGeometry.Space.isAlgebraicSpace_relocalizePresheaf` — and the morphism
`Λ W₀ ⟶ h_{Z_U}` obtained from `Λ w₀` and the comparison
`CategoryTheory.OverShriek.relocalizeYonedaIso` of Stacks 03I4 part (2). The theorem is that the
restriction of scalars of that data is `Λ` of the space of sections of `w₀`, compatibly with the
projection to `h_U`: the projection of the restriction of scalars becomes the structural morphism
`CategoryTheory.OverShriek.relocalizeToYoneda` of the relocalization.

## Implementation notes

A section of `Λ (sectionSpace …)` over `T` is a factorization `ψ : T.left ⟶ U.left` of the
structure morphism of `T` — that is, a morphism `τ : T ⟶ U` of the site over `S` — together with
a section of `W₀ ⟶ Z₀` over `(T.left, ψ)`. A point of the restriction of scalars over `T` is a
pair of Stacks 05Y9: a morphism `T ⟶ U` and a section of `Λ W₀ ⟶ h_{Z_U}` over `T ×_U Z_U`. The
two match up because the fibre product `V_τ = T ×_U Z_U` is at the same time the product of
`(T.left, ψ)` with `Z₀` in the site over `U.left.1`
(`AlgebraicGeometry.Space.fibreProdIso`) and the fibre product of `T` and `Z_U` over `U` in the
site over `S` (`AlgebraicGeometry.Space.isPullback_fibre`), and because a section of `Λ W₀` over
an object in the image of the relocalization carrying the tautological factorization is a section
of `W₀` (`AlgebraicGeometry.Space.fibreLiftEquiv`).

## Main definitions

* `AlgebraicGeometry.Space.relocalizedBase`, `AlgebraicGeometry.Space.relocalizedBaseHom` and
  `AlgebraicGeometry.Space.relocalizedTotalHom`: the data over `S` produced by `Z₀` and `w₀`.
* `AlgebraicGeometry.Space.fibreObj` and `AlgebraicGeometry.Space.fibreObjOver`: the fibre
  product `V_τ`, read in the two sites.
* `AlgebraicGeometry.Space.relocalizedPairOf`: the pair of Stacks 05Y9 named by a test morphism
  `τ : T ⟶ U` and a section of the space of sections over `(T, τ)`.
* `AlgebraicGeometry.Space.relocalizeSectionSpaceHom` and
  `AlgebraicGeometry.Space.relocalizeSectionSpaceIso`: the isomorphism from `Λ` of the space of
  sections of `w₀` to the restriction of scalars of the relocalized data.

## Main results

* `AlgebraicGeometry.Space.fibreSectionsEquiv` and `AlgebraicGeometry.Space.fibreLiftEquiv`: the
  two halves of the identification of sections over a single test morphism.
* `AlgebraicGeometry.Space.relocalizedPairOf_restrict`: the family of pairs is compatible with
  base change.
* `AlgebraicGeometry.Space.bijective_relocalizedPair`: the family of pairs is bijective.
* `AlgebraicGeometry.Space.relocalizeSectionSpaceHom_comp_projection`: the comparison morphism
  carries the structural morphism of the relocalization to the projection of the restriction of
  scalars.
* `AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_relocalize` and
  `AlgebraicGeometry.Space.isEtale_projection_restrictionOfScalars_relocalize`: consequently the
  restriction of scalars of the relocalized data is an algebraic space étale over `U` as soon as
  the space of sections of `w₀` is an algebraic space étale over `U.left.1`.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05Y9](https://stacks.math.columbia.edu/tag/05Y9)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Bridge

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  (Z₀ : BigFppfOver B U.left.1 U.left.2)
  (W₀ : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) (w₀ : W₀ ⟶ yoneda.obj Z₀)

/-- `Z_U`, the object of the big fppf site of `S` underlying an object `Z₀` of the big fppf site
of the scheme underlying `U`. -/
abbrev relocalizedBase : BigFppfOver B S hS := (Over.map U.hom).obj Z₀

/-- The structural morphism `Z_U ⟶ U`. -/
def relocalizedBaseHom : relocalizedBase B S hS U Z₀ ⟶ U := Over.homMk Z₀.hom rfl

/-- The underlying morphism of schemes of `Z_U ⟶ U` is the structure morphism of `Z₀`. -/
@[simp] theorem relocalizedBaseHom_left :
    (relocalizedBaseHom B S hS U Z₀).left = Z₀.hom := rfl

/-- The morphism `Λ W₀ ⟶ h_{Z_U}` obtained from `w₀ : W₀ ⟶ h_{Z₀}` by relocalizing and using
that relocalization carries representables to representables. -/
noncomputable def relocalizedTotalHom :
    (OverShriek.relocalizePresheafFunctor U.hom).obj W₀ ⟶
      yoneda.obj (relocalizedBase B S hS U Z₀) :=
  (OverShriek.relocalizePresheafFunctor U.hom).map w₀ ≫
    (OverShriek.relocalizeYonedaIso U.hom).hom.app Z₀

/-- On a section `x` of `Λ W₀`, the underlying morphism of schemes of the image of `x` in
`h_{Z_U}` is that of the image under `w₀` of the section of `W₀` carried by `x`. -/
theorem relocalizedTotalHom_app_left {T : BigFppfOver B S hS}
    (x : ((OverShriek.relocalizePresheafFunctor U.hom).obj W₀).obj (op T)) :
    ((relocalizedTotalHom B S hS U Z₀ W₀ w₀).app (op T) x).left =
      (w₀.app (op (Over.mk x.1.1)) x.1.2).left := rfl

/-! ### The fibre product of a test object with `Z_U` over `U` -/

/-- `V_τ = T ×_U Z_U`, read as an object of the big fppf site of the scheme underlying `U`. -/
noncomputable abbrev fibreObj {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    BigFppfOver B U.left.1 U.left.2 :=
  Over.mk (pullback.snd τ.left Z₀.hom ≫ Z₀.hom)

/-- `V_τ`, read as an object of the big fppf site of `S`. -/
noncomputable abbrev fibreObjOver {T : BigFppfOver B S hS} (τ : T ⟶ U) : BigFppfOver B S hS :=
  (Over.map U.hom).obj (fibreObj B S hS U Z₀ τ)

/-- The first projection `V_τ ⟶ (T, τ)` in the site over the scheme underlying `U`. -/
noncomputable def fibreFst {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    fibreObj B S hS U Z₀ τ ⟶ Over.mk τ.left :=
  Over.homMk (pullback.fst τ.left Z₀.hom) (by
    change pullback.fst τ.left Z₀.hom ≫ τ.left = pullback.snd τ.left Z₀.hom ≫ Z₀.hom
    exact pullback.condition)

/-- The second projection `V_τ ⟶ Z₀` in the site over the scheme underlying `U`. -/
noncomputable def fibreSnd {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    fibreObj B S hS U Z₀ τ ⟶ Z₀ :=
  Over.homMk (pullback.snd τ.left Z₀.hom) rfl

/-- The underlying morphism of schemes of `fibreFst` is the first pullback projection. -/
@[simp] theorem fibreFst_left {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    (fibreFst B S hS U Z₀ τ).left = pullback.fst τ.left Z₀.hom := rfl

/-- The underlying morphism of schemes of `fibreSnd` is the second pullback projection. -/
@[simp] theorem fibreSnd_left {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    (fibreSnd B S hS U Z₀ τ).left = pullback.snd τ.left Z₀.hom := rfl

/-- The first projection `V_τ ⟶ T` in the site over `S`. -/
noncomputable def fibreProj₁ {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    fibreObjOver B S hS U Z₀ τ ⟶ T :=
  Over.homMk (pullback.fst τ.left Z₀.hom) (by
    change pullback.fst τ.left Z₀.hom ≫ T.hom =
      (pullback.snd τ.left Z₀.hom ≫ Z₀.hom) ≫ U.hom
    rw [← Over.w τ, ← Category.assoc, pullback.condition])

/-- The second projection `V_τ ⟶ Z_U` in the site over `S`. -/
noncomputable def fibreProj₂ {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    fibreObjOver B S hS U Z₀ τ ⟶ relocalizedBase B S hS U Z₀ :=
  (Over.map U.hom).map (fibreSnd B S hS U Z₀ τ)

/-- The underlying morphism of schemes of `fibreProj₁` is the first pullback projection. -/
@[simp] theorem fibreProj₁_left {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    (fibreProj₁ B S hS U Z₀ τ).left = pullback.fst τ.left Z₀.hom := rfl

/-- The underlying morphism of schemes of `fibreProj₂` is the second pullback projection. -/
@[simp] theorem fibreProj₂_left {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    (fibreProj₂ B S hS U Z₀ τ).left = pullback.snd τ.left Z₀.hom := rfl

/-- **`V_τ` is the fibre product of `T` and `Z_U` over `U`**, as presheaves on the big fppf site
of `S`. -/
theorem isPullback_fibre {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    IsPullback (yoneda.map (fibreProj₁ B S hS U Z₀ τ))
      (yoneda.map (fibreProj₂ B S hS U Z₀ τ)) (yoneda.map τ)
      (yoneda.map (relocalizedBaseHom B S hS U Z₀)) := by
  have hw : fibreProj₁ B S hS U Z₀ τ ≫ τ =
      fibreProj₂ B S hS U Z₀ τ ≫ relocalizedBaseHom B S hS U Z₀ :=
    Over.OverMorphism.ext (by simpa using pullback.condition)
  have h0 : IsPullback (fibreProj₁ B S hS U Z₀ τ) (fibreProj₂ B S hS U Z₀ τ) τ
      (relocalizedBaseHom B S hS U Z₀) := by
    rw [Over.isPullback_iff_left _ _ _ _ hw]
    simpa using IsPullback.of_hasPullback τ.left Z₀.hom
  exact h0.map yoneda

/-- `h_{V_τ}` is the product of `h_{(T, τ)}` and `h_{Z₀}` in presheaves on the big fppf site of
the scheme underlying `U`. -/
noncomputable def fibreProdIso {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    yoneda.obj (fibreObj B S hS U Z₀ τ) ≅
      yoneda.obj (Over.mk τ.left) ⨯ yoneda.obj Z₀ :=
  AlgebraicGeometry.Stack.yonedaBinaryProductIso (fibreFst B S hS U Z₀ τ)
    (fibreSnd B S hS U Z₀ τ)
    (AlgebraicGeometry.Stack.overBinaryFanIsLimit Z₀.hom (Over.mk τ.left)
      (fibreObj B S hS U Z₀ τ) (fibreFst B S hS U Z₀ τ) (fibreSnd B S hS U Z₀ τ)
      (by simpa using (IsPullback.of_hasPullback τ.left Z₀.hom).flip))

/-- The first component of `fibreProdIso` is `h` of the first projection `fibreFst`. -/
@[simp] theorem fibreProdIso_hom_fst {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    (fibreProdIso B S hS U Z₀ τ).hom ≫ prod.fst = yoneda.map (fibreFst B S hS U Z₀ τ) :=
  AlgebraicGeometry.Stack.yonedaBinaryProductIso_fst _ _ _

/-- The second component of `fibreProdIso` is `h` of the second projection `fibreSnd`. -/
@[simp] theorem fibreProdIso_hom_snd {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    (fibreProdIso B S hS U Z₀ τ).hom ≫ prod.snd = yoneda.map (fibreSnd B S hS U Z₀ τ) :=
  AlgebraicGeometry.Stack.yonedaBinaryProductIso_snd _ _ _

/-! ### Sections over a test object -/

/-- The section of `W₀` over `V_τ` determined by a section of `W₀ ⟶ Z₀` over `(T, τ)`. -/
noncomputable def fibreSection {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (σ : SectionsOver B U.left.1 U.left.2 Z₀ (Over.mk τ.left) W₀ w₀) :
    W₀.obj (op (fibreObj B S hS U Z₀ τ)) :=
  yonedaEquiv ((fibreProdIso B S hS U Z₀ τ).hom ≫ σ.1)

/-- The section `fibreSection τ σ` of `W₀` lies over the second projection `V_τ ⟶ Z₀`. -/
theorem fibreSection_spec {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (σ : SectionsOver B U.left.1 U.left.2 Z₀ (Over.mk τ.left) W₀ w₀) :
    w₀.app (op (fibreObj B S hS U Z₀ τ)) (fibreSection B S hS U Z₀ W₀ w₀ τ σ) =
      fibreSnd B S hS U Z₀ τ :=
  (yonedaEquiv_comp ((fibreProdIso B S hS U Z₀ τ).hom ≫ σ.1) w₀).symm.trans (by
    rw [Category.assoc, σ.2, fibreProdIso_hom_snd, yonedaEquiv_yoneda_map])

/-- **A section of `W₀ ⟶ Z₀` over `(T, τ)` is a section of `W₀` over the fibre product `V_τ`
lying over the second projection.** -/
noncomputable def fibreSectionsEquiv {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    SectionsOver B U.left.1 U.left.2 Z₀ (Over.mk τ.left) W₀ w₀ ≃
      {t : W₀.obj (op (fibreObj B S hS U Z₀ τ)) //
        w₀.app (op (fibreObj B S hS U Z₀ τ)) t = fibreSnd B S hS U Z₀ τ} :=
  Equiv.ofBijective
    (fun σ => ⟨fibreSection B S hS U Z₀ W₀ w₀ τ σ, fibreSection_spec B S hS U Z₀ W₀ w₀ τ σ⟩)
    (by
      constructor
      · intro σ₁ σ₂ h
        have h1 : (fibreProdIso B S hS U Z₀ τ).hom ≫ σ₁.1 =
            (fibreProdIso B S hS U Z₀ τ).hom ≫ σ₂.1 :=
          yonedaEquiv.injective (congrArg Subtype.val h)
        exact Subtype.ext ((cancel_epi (fibreProdIso B S hS U Z₀ τ).hom).1 h1)
      · rintro ⟨t, ht⟩
        refine ⟨⟨(fibreProdIso B S hS U Z₀ τ).inv ≫ yonedaEquiv.symm t, ?_⟩, ?_⟩
        · refine (cancel_epi (fibreProdIso B S hS U Z₀ τ).hom).1 ?_
          rw [fibreProdIso_hom_snd, Category.assoc, Iso.hom_inv_id_assoc]
          refine yonedaEquiv.injective ?_
          rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply, ht]
        · refine Subtype.ext ?_
          change yonedaEquiv ((fibreProdIso B S hS U Z₀ τ).hom ≫
            (fibreProdIso B S hS U Z₀ τ).inv ≫ yonedaEquiv.symm t) = t
          rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply])

/-- The section of `W₀` underlying `fibreSectionsEquiv τ σ` is `fibreSection τ σ`. -/
theorem fibreSectionsEquiv_apply {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (σ : SectionsOver B U.left.1 U.left.2 Z₀ (Over.mk τ.left) W₀ w₀) :
    (fibreSectionsEquiv B S hS U Z₀ W₀ w₀ τ σ).1 = fibreSection B S hS U Z₀ W₀ w₀ τ σ := rfl

/-- The morphism `h_{V_τ} ⟶ Λ W₀` named by a section of `W₀` over `V_τ`. -/
noncomputable def fibreLift {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (t : W₀.obj (op (fibreObj B S hS U Z₀ τ))) :
    yoneda.obj (fibreObjOver B S hS U Z₀ τ) ⟶
      (OverShriek.relocalizePresheafFunctor U.hom).obj W₀ :=
  yonedaEquiv.symm (OverShriek.relocalizeMk U.hom W₀
    (W := op (fibreObjOver B S hS U Z₀ τ)) (fibreObj B S hS U Z₀ τ).hom t rfl)

/-- Under the Yoneda bijection, `fibreLift τ t` is the section of `Λ W₀` over `V_τ` given by `t`
with the tautological factorization through `U`. -/
theorem yonedaEquiv_fibreLift {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (t : W₀.obj (op (fibreObj B S hS U Z₀ τ))) :
    yonedaEquiv (fibreLift B S hS U Z₀ W₀ τ t) =
      OverShriek.relocalizeMk U.hom W₀ (W := op (fibreObjOver B S hS U Z₀ τ))
        (fibreObj B S hS U Z₀ τ).hom t rfl :=
  yonedaEquiv.apply_symm_apply _

/-- If `t` lies over the second projection `V_τ ⟶ Z₀`, then `fibreLift τ t` followed by
`Λ W₀ ⟶ h_{Z_U}` is `h` of the second projection `V_τ ⟶ Z_U`. -/
theorem fibreLift_comp {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (t : W₀.obj (op (fibreObj B S hS U Z₀ τ)))
    (ht : w₀.app (op (fibreObj B S hS U Z₀ τ)) t = fibreSnd B S hS U Z₀ τ) :
    fibreLift B S hS U Z₀ W₀ τ t ≫ relocalizedTotalHom B S hS U Z₀ W₀ w₀ =
      yoneda.map (fibreProj₂ B S hS U Z₀ τ) := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_fibreLift]
  refine Over.OverMorphism.ext ?_
  rw [relocalizedTotalHom_app_left, fibreProj₂_left]
  show (w₀.app (op (fibreObj B S hS U Z₀ τ)) t).left = _
  rw [ht, fibreSnd_left]

/-- **A section of `Λ W₀ ⟶ h_{Z_U}` over `V_τ` is a section of `W₀ ⟶ Z₀` over `V_τ`.** -/
noncomputable def fibreLiftEquiv {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    {t : W₀.obj (op (fibreObj B S hS U Z₀ τ)) //
        w₀.app (op (fibreObj B S hS U Z₀ τ)) t = fibreSnd B S hS U Z₀ τ} ≃
      {m : yoneda.obj (fibreObjOver B S hS U Z₀ τ) ⟶
          (OverShriek.relocalizePresheafFunctor U.hom).obj W₀ //
        m ≫ relocalizedTotalHom B S hS U Z₀ W₀ w₀ =
          yoneda.map (fibreProj₂ B S hS U Z₀ τ)} :=
  Equiv.ofBijective
    (fun t => ⟨fibreLift B S hS U Z₀ W₀ τ t.1, fibreLift_comp B S hS U Z₀ W₀ w₀ τ t.1 t.2⟩)
    (by
      constructor
      · intro t₁ t₂ h
        refine Subtype.ext ?_
        have h2 := congrArg yonedaEquiv (congrArg Subtype.val h)
        rw [yonedaEquiv_fibreLift, yonedaEquiv_fibreLift] at h2
        have h3 : (⟨(fibreObj B S hS U Z₀ τ).hom, t₁.1⟩ :
              Σ χ : (fibreObj B S hS U Z₀ τ).left ⟶ U.left, W₀.obj (op (Over.mk χ))) =
            ⟨(fibreObj B S hS U Z₀ τ).hom, t₂.1⟩ := Subtype.ext_iff.1 h2
        simpa using h3
      · rintro ⟨m, hm⟩
        obtain ⟨⟨⟨χ, t⟩, hχ⟩, hp⟩ :
            ∃ p : ((OverShriek.relocalizePresheafFunctor U.hom).obj W₀).obj
              (op (fibreObjOver B S hS U Z₀ τ)), yonedaEquiv m = p := ⟨_, rfl⟩
        have hx0 := congrArg yonedaEquiv hm
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, hp] at hx0
        have hx : (w₀.app (op (Over.mk χ)) t).left = pullback.snd τ.left Z₀.hom := by
          rw [← relocalizedTotalHom_app_left B S hS U Z₀ W₀ w₀ (T := fibreObjOver B S hS U Z₀ τ)
            ⟨⟨χ, t⟩, hχ⟩, hx0, fibreProj₂_left]
        have h1 : (w₀.app (op (Over.mk χ)) t).left ≫ Z₀.hom = χ := Over.w _
        obtain rfl : χ = pullback.snd τ.left Z₀.hom ≫ Z₀.hom := by rw [← h1, hx]
        refine ⟨⟨t, Over.OverMorphism.ext
          (hx.trans (fibreSnd_left B S hS U Z₀ τ).symm)⟩, ?_⟩
        refine Subtype.ext (yonedaEquiv.injective ?_)
        rw [yonedaEquiv_fibreLift, hp]
        exact Subtype.ext rfl)

/-- The morphism underlying `fibreLiftEquiv τ t` is `fibreLift τ t`. -/
theorem fibreLiftEquiv_apply {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (t : {t : W₀.obj (op (fibreObj B S hS U Z₀ τ)) //
        w₀.app (op (fibreObj B S hS U Z₀ τ)) t = fibreSnd B S hS U Z₀ τ}) :
    (fibreLiftEquiv B S hS U Z₀ W₀ w₀ τ t).1 = fibreLift B S hS U Z₀ W₀ τ t.1 := rfl

/-- Distinct sections of `W₀` over `V_τ` give distinct morphisms `h_{V_τ} ⟶ Λ W₀`. -/
theorem fibreLift_injective {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    Function.Injective (fibreLift B S hS U Z₀ W₀ τ) := by
  intro t₁ t₂ h
  have h2 := congrArg yonedaEquiv h
  rw [yonedaEquiv_fibreLift, yonedaEquiv_fibreLift] at h2
  have h3 : (⟨(fibreObj B S hS U Z₀ τ).hom, t₁⟩ :
        Σ χ : (fibreObj B S hS U Z₀ τ).left ⟶ U.left, W₀.obj (op (Over.mk χ))) =
      ⟨(fibreObj B S hS U Z₀ τ).hom, t₂⟩ := Subtype.ext_iff.1 h2
  simpa using h3

/-- Distinct sections of `W₀ ⟶ Z₀` over `(T, τ)` give distinct sections of `W₀` over `V_τ`. -/
theorem fibreSection_injective {T : BigFppfOver B S hS} (τ : T ⟶ U) :
    Function.Injective (fibreSection B S hS U Z₀ W₀ w₀ τ) := by
  intro σ₁ σ₂ h
  have h1 : (fibreProdIso B S hS U Z₀ τ).hom ≫ σ₁.1 =
      (fibreProdIso B S hS U Z₀ τ).hom ≫ σ₂.1 := yonedaEquiv.injective h
  exact Subtype.ext ((cancel_epi (fibreProdIso B S hS U Z₀ τ).hom).1 h1)

/-! ### Functoriality of the fibre product -/

/-- The morphism of fibre products over the scheme underlying `U` induced by a morphism of test
objects. -/
noncomputable def fibreMapLeft {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    pullback (k ≫ τ).left Z₀.hom ⟶ pullback τ.left Z₀.hom :=
  pullback.map (k ≫ τ).left Z₀.hom τ.left Z₀.hom k.left (𝟙 Z₀.left) (𝟙 U.left)
    (by simp) (by simp)

/-- `fibreMapLeft k τ` is compatible with the first projections, through `k`. -/
@[simp] theorem fibreMapLeft_fst {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreMapLeft B S hS U Z₀ k τ ≫ pullback.fst τ.left Z₀.hom =
      pullback.fst (k ≫ τ).left Z₀.hom ≫ k.left := by
  simp [fibreMapLeft]

/-- `fibreMapLeft k τ` commutes with the second projections to `Z₀`. -/
@[simp] theorem fibreMapLeft_snd {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreMapLeft B S hS U Z₀ k τ ≫ pullback.snd τ.left Z₀.hom =
      pullback.snd (k ≫ τ).left Z₀.hom := by
  simp [fibreMapLeft]

/-- The morphism `V_{k ≫ τ} ⟶ V_τ` of fibre products, in the site over the scheme underlying
`U`. -/
noncomputable def fibreMap {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreObj B S hS U Z₀ (k ≫ τ) ⟶ fibreObj B S hS U Z₀ τ :=
  Over.homMk (fibreMapLeft B S hS U Z₀ k τ) (by
    change fibreMapLeft B S hS U Z₀ k τ ≫ pullback.snd τ.left Z₀.hom ≫ Z₀.hom =
      pullback.snd (k ≫ τ).left Z₀.hom ≫ Z₀.hom
    rw [← Category.assoc, fibreMapLeft_snd])

/-- The underlying morphism of schemes of `fibreMap k τ` is `fibreMapLeft k τ`. -/
@[simp] theorem fibreMap_left {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    (fibreMap B S hS U Z₀ k τ).left = fibreMapLeft B S hS U Z₀ k τ := rfl

/-- The morphism `V_{k ≫ τ} ⟶ V_τ`, in the site over `S`. -/
noncomputable def fibreMapOver {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreObjOver B S hS U Z₀ (k ≫ τ) ⟶ fibreObjOver B S hS U Z₀ τ :=
  (Over.map U.hom).map (fibreMap B S hS U Z₀ k τ)

/-- The underlying morphism of schemes of `fibreMapOver k τ` is `fibreMapLeft k τ`. -/
@[simp] theorem fibreMapOver_left {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    (fibreMapOver B S hS U Z₀ k τ).left = fibreMapLeft B S hS U Z₀ k τ := rfl

/-- `fibreMap k τ` is compatible with the first projections, through the morphism
`(T', k ≫ τ) ⟶ (T, τ)` induced by `k`. -/
theorem fibreMap_comp_fibreFst {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreMap B S hS U Z₀ k τ ≫ fibreFst B S hS U Z₀ τ =
      fibreFst B S hS U Z₀ (k ≫ τ) ≫
        (Over.homMk k.left rfl : Over.mk (k ≫ τ).left ⟶ Over.mk τ.left) :=
  Over.OverMorphism.ext (by simp)

/-- `fibreMap k τ` commutes with the second projections to `Z₀`. -/
theorem fibreMap_comp_fibreSnd {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreMap B S hS U Z₀ k τ ≫ fibreSnd B S hS U Z₀ τ = fibreSnd B S hS U Z₀ (k ≫ τ) :=
  Over.OverMorphism.ext (by simp)

/-- `fibreMapOver k τ` is compatible with the first projections, through `k`. -/
theorem fibreMapOver_comp_fibreProj₁ {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreMapOver B S hS U Z₀ k τ ≫ fibreProj₁ B S hS U Z₀ τ =
      fibreProj₁ B S hS U Z₀ (k ≫ τ) ≫ k :=
  Over.OverMorphism.ext (by simp)

/-- `fibreMapOver k τ` commutes with the second projections to `Z_U`. -/
theorem fibreMapOver_comp_fibreProj₂ {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    fibreMapOver B S hS U Z₀ k τ ≫ fibreProj₂ B S hS U Z₀ τ =
      fibreProj₂ B S hS U Z₀ (k ≫ τ) :=
  Over.OverMorphism.ext (by simp)

/-- The isomorphisms `fibreProdIso` are natural in the test morphism: they intertwine `h` of
`fibreMap k τ` with the product of `h` of `(T', k ≫ τ) ⟶ (T, τ)` and the identity of `h_{Z₀}`. -/
theorem fibreProdIso_naturality {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U) :
    (fibreProdIso B S hS U Z₀ (k ≫ τ)).hom ≫
        prod.map (yoneda.map (Over.homMk k.left rfl :
            Over.mk (k ≫ τ).left ⟶ Over.mk τ.left)) (𝟙 (yoneda.obj Z₀)) =
      yoneda.map (fibreMap B S hS U Z₀ k τ) ≫ (fibreProdIso B S hS U Z₀ τ).hom := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, ← Category.assoc, fibreProdIso_hom_fst, Category.assoc,
      fibreProdIso_hom_fst, ← yoneda.map_comp, ← yoneda.map_comp, fibreMap_comp_fibreFst]
  · rw [Category.assoc, prod.map_snd, Category.comp_id, fibreProdIso_hom_snd, Category.assoc,
      fibreProdIso_hom_snd, ← yoneda.map_comp, fibreMap_comp_fibreSnd]

/-- The section of `W₀` over `V_{k ≫ τ}` attached to the restriction of `σ` along `k` is the
restriction along `fibreMap k τ` of the section over `V_τ` attached to `σ`. -/
theorem fibreSection_restrict {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U)
    (σ : SectionsOver B U.left.1 U.left.2 Z₀ (Over.mk τ.left) W₀ w₀) :
    fibreSection B S hS U Z₀ W₀ w₀ (k ≫ τ)
        (SectionsOver.restrict (Over.homMk k.left rfl :
          Over.mk (k ≫ τ).left ⟶ Over.mk τ.left) σ) =
      W₀.map (fibreMap B S hS U Z₀ k τ).op (fibreSection B S hS U Z₀ W₀ w₀ τ σ) := by
  rw [show fibreSection B S hS U Z₀ W₀ w₀ τ σ =
      yonedaEquiv ((fibreProdIso B S hS U Z₀ τ).hom ≫ σ.1) from rfl, yonedaEquiv_naturality]
  show yonedaEquiv ((fibreProdIso B S hS U Z₀ (k ≫ τ)).hom ≫
    (prod.map (yoneda.map (Over.homMk k.left rfl :
      Over.mk (k ≫ τ).left ⟶ Over.mk τ.left)) (𝟙 (yoneda.obj Z₀)) ≫ σ.1)) = _
  rw [← Category.assoc, fibreProdIso_naturality, Category.assoc]

/-! ### The restriction of scalars of the relocalized data -/

variable (hW₀ : IsAlgebraicSpace B U.left.1 U.left.2 W₀)

/-- `Z_U` as an algebraic space over `S`. -/
abbrev relocalizedBaseSpace : AlgebraicSpaces B S hS :=
  schemeSpace (relocalizedBase B S hS U Z₀)

/-- `U` as an algebraic space over `S`. -/
abbrev relocalizedTargetSpace : AlgebraicSpaces B S hS :=
  schemeSpace U

/-- `Λ W₀` as an algebraic space over `S`, by Stacks 03I4 part (3). -/
noncomputable abbrev relocalizedTotalSpace : AlgebraicSpaces B S hS :=
  ⟨(OverShriek.relocalizePresheafFunctor U.hom).obj W₀,
    isAlgebraicSpace_relocalizePresheaf B S hS U W₀ hW₀⟩

/-- `Z_U ⟶ U`, as a morphism of algebraic spaces over `S`. -/
abbrev relocalizedBaseSpaceHom :
    relocalizedBaseSpace B S hS U Z₀ ⟶ relocalizedTargetSpace B S hS U :=
  ObjectProperty.homMk (yoneda.map (relocalizedBaseHom B S hS U Z₀))

/-- `Λ W₀ ⟶ Z_U`, as a morphism of algebraic spaces over `S`. -/
noncomputable abbrev relocalizedTotalSpaceHom :
    relocalizedTotalSpace B S hS U W₀ hW₀ ⟶ relocalizedBaseSpace B S hS U Z₀ :=
  ObjectProperty.homMk (relocalizedTotalHom B S hS U Z₀ W₀ w₀)

/-- The second component of the pair determined by a test morphism and a section. -/
noncomputable def relocalizedLift {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (s : (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).obj (op (Over.mk τ.left))) :
    pullback (yoneda.map τ) (yoneda.map (relocalizedBaseHom B S hS U Z₀)) ⟶
      (OverShriek.relocalizePresheafFunctor U.hom).obj W₀ :=
  (isPullback_fibre B S hS U Z₀ τ).isoPullback.inv ≫
    fibreLift B S hS U Z₀ W₀ τ (fibreSection B S hS U Z₀ W₀ w₀ τ
      (sectionSpaceEquiv B U.left.1 U.left.2 Z₀ (Over.mk τ.left) W₀ w₀ s))

/-- `relocalizedLift τ s` lies over the second projection `T ×_U Z_U ⟶ h_{Z_U}`. -/
theorem relocalizedLift_comp {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (s : (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).obj (op (Over.mk τ.left))) :
    relocalizedLift B S hS U Z₀ W₀ w₀ τ s ≫ relocalizedTotalHom B S hS U Z₀ W₀ w₀ =
      pullback.snd (yoneda.map τ) (yoneda.map (relocalizedBaseHom B S hS U Z₀)) := by
  rw [relocalizedLift, Category.assoc, fibreLift_comp B S hS U Z₀ W₀ w₀ τ _
      (fibreSection_spec B S hS U Z₀ W₀ w₀ τ _),
    (isPullback_fibre B S hS U Z₀ τ).isoPullback_inv_snd]

/-- **The pair of Stacks 05Y9 determined by a test morphism `τ : T ⟶ U` and a section of the
space of sections of `w₀` over `(T, τ)`.** -/
noncomputable def relocalizedPairOf {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (s : (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).obj (op (Over.mk τ.left))) :
    RestrictionPair B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
      (relocalizedBaseSpaceHom B S hS U Z₀) (yoneda.obj T) :=
  ⟨yoneda.map τ, relocalizedLift B S hS U Z₀ W₀ w₀ τ s,
    relocalizedLift_comp B S hS U Z₀ W₀ w₀ τ s⟩

/-- The base of `relocalizedPairOf τ s` is `h_τ : h_T ⟶ h_U`. -/
@[simp] theorem relocalizedPairOf_base {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (s : (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).obj (op (Over.mk τ.left))) :
    (relocalizedPairOf B S hS U Z₀ W₀ w₀ hW₀ τ s).base = yoneda.map τ := rfl

/-- The lift of `relocalizedPairOf τ s` is `relocalizedLift τ s`. -/
@[simp] theorem relocalizedPairOf_lift {T : BigFppfOver B S hS} (τ : T ⟶ U)
    (s : (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).obj (op (Over.mk τ.left))) :
    (relocalizedPairOf B S hS U Z₀ W₀ w₀ hW₀ τ s).lift =
      relocalizedLift B S hS U Z₀ W₀ w₀ τ s := rfl

/-- **The family of pairs is compatible with base change.** -/
theorem relocalizedPairOf_restrict {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (τ : T ⟶ U)
    (s : (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).obj (op (Over.mk τ.left))) :
    relocalizedPairOf B S hS U Z₀ W₀ w₀ hW₀ (k ≫ τ)
        ((sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).map
          (Over.homMk k.left rfl : Over.mk (k ≫ τ).left ⟶ Over.mk τ.left).op s) =
      RestrictionPair.restrict (yoneda.map k)
        (relocalizedPairOf B S hS U Z₀ W₀ w₀ hW₀ τ s) := by
  have hbase : yoneda.map (k ≫ τ) = yoneda.map k ≫ yoneda.map τ := yoneda.map_comp k τ
  have hA : fibreLift B S hS U Z₀ W₀ (k ≫ τ)
        (fibreSection B S hS U Z₀ W₀ w₀ (k ≫ τ)
          (sectionSpaceEquiv B U.left.1 U.left.2 Z₀ (Over.mk (k ≫ τ).left) W₀ w₀
            ((sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).map
              (Over.homMk k.left rfl : Over.mk (k ≫ τ).left ⟶ Over.mk τ.left).op s))) =
      yoneda.map (fibreMapOver B S hS U Z₀ k τ) ≫
        fibreLift B S hS U Z₀ W₀ τ (fibreSection B S hS U Z₀ W₀ w₀ τ
          (sectionSpaceEquiv B U.left.1 U.left.2 Z₀ (Over.mk τ.left) W₀ w₀ s)) := by
    rw [sectionSpaceEquiv_restrict, fibreSection_restrict]
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_fibreLift, ← yonedaEquiv_naturality, yonedaEquiv_fibreLift]
    refine Subtype.ext ?_
    exact OverShriek.sigmaMk_eq W₀ _ (fibreMap B S hS U Z₀ k τ)
      (Over.homMk (fibreMapOver B S hS U Z₀ k τ).left rfl) rfl
  obtain ⟨φ, hφ⟩ : ∃ φ : pullback (yoneda.map (k ≫ τ))
        (yoneda.map (relocalizedBaseHom B S hS U Z₀)) ⟶ pullback (yoneda.map τ)
        (yoneda.map (relocalizedBaseHom B S hS U Z₀)), φ =
      (pullback.congrHom hbase (rfl : yoneda.map (relocalizedBaseHom B S hS U Z₀) =
        yoneda.map (relocalizedBaseHom B S hS U Z₀))).hom ≫
      pullback.map (yoneda.map k ≫ yoneda.map τ)
        (yoneda.map (relocalizedBaseHom B S hS U Z₀)) (yoneda.map τ)
        (yoneda.map (relocalizedBaseHom B S hS U Z₀)) (yoneda.map k) (𝟙 _) (𝟙 _)
        (by simp) (by simp) := ⟨_, rfl⟩
  have hμ : (isPullback_fibre B S hS U Z₀ (k ≫ τ)).isoPullback.hom ≫ φ ≫
        (isPullback_fibre B S hS U Z₀ τ).isoPullback.inv =
      yoneda.map (fibreMapOver B S hS U Z₀ k τ) := by
    subst hφ
    refine (isPullback_fibre B S hS U Z₀ τ).hom_ext ?_ ?_
    · simp only [Category.assoc, IsPullback.isoPullback_inv_fst, pullback.map_fst,
        pullback.congrHom_hom_fst_assoc, IsPullback.isoPullback_hom_fst_assoc,
        ← yoneda.map_comp, fibreMapOver_comp_fibreProj₁]
    · simp only [Category.assoc, IsPullback.isoPullback_inv_snd, pullback.map_snd,
        Category.comp_id, pullback.congrHom_hom_snd, IsPullback.isoPullback_hom_snd,
        ← yoneda.map_comp, fibreMapOver_comp_fibreProj₂]
  have key : relocalizedLift B S hS U Z₀ W₀ w₀ (k ≫ τ)
        ((sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀).map
          (Over.homMk k.left rfl : Over.mk (k ≫ τ).left ⟶ Over.mk τ.left).op s) =
      φ ≫ relocalizedLift B S hS U Z₀ W₀ w₀ τ s := by
    rw [relocalizedLift, relocalizedLift, Iso.inv_comp_eq, hA, ← hμ]
    simp only [Category.assoc]
  subst hφ
  exact RestrictionPair.ext_of_base_eq hbase key

/-- The family of pairs attached to the sections of the relocalized space of sections. -/
noncomputable def relocalizedPair (T : (BigFppfOver B S hS)ᵒᵖ)
    (v : ((OverShriek.relocalizePresheafFunctor U.hom).obj
      (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)).obj T) :
    RestrictionPair B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
      (relocalizedBaseSpaceHom B S hS U Z₀) (yoneda.obj T.unop) :=
  relocalizedPairOf B S hS U Z₀ W₀ w₀ hW₀ (Over.homMk v.1.1 v.2 : T.unop ⟶ U) v.1.2

/-- The family `relocalizedPair` is compatible with restriction along morphisms of test
objects. -/
theorem relocalizedPair_restrict {T T' : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ T')
    (v : ((OverShriek.relocalizePresheafFunctor U.hom).obj
      (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)).obj T) :
    relocalizedPair B S hS U Z₀ W₀ w₀ hW₀ T'
        (((OverShriek.relocalizePresheafFunctor U.hom).obj
          (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)).map f v) =
      RestrictionPair.restrict (yoneda.map f.unop)
        (relocalizedPair B S hS U Z₀ W₀ w₀ hW₀ T v) :=
  relocalizedPairOf_restrict B S hS U Z₀ W₀ w₀ hW₀ f.unop
    (Over.homMk v.1.1 v.2 : T.unop ⟶ U) v.1.2

/-- **The pairs attached to the sections of the relocalized space of sections are exactly the
pairs of Stacks 05Y9.** -/
theorem bijective_relocalizedPair (T : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Bijective (relocalizedPair B S hS U Z₀ W₀ w₀ hW₀ T) := by
  constructor
  · rintro ⟨⟨ψ₁, s₁⟩, h₁⟩ ⟨⟨ψ₂, s₂⟩, h₂⟩ h
    have hb : yoneda.map (Over.homMk ψ₁ h₁ : T.unop ⟶ U) =
        yoneda.map (Over.homMk ψ₂ h₂ : T.unop ⟶ U) := congrArg RestrictionPair.base h
    have hψ : ψ₁ = ψ₂ := congrArg Over.Hom.left (yoneda.map_injective hb)
    subst hψ
    obtain rfl : h₁ = h₂ := rfl
    have hid : (pullback.congrHom (congrArg RestrictionPair.base h)
        (rfl : (relocalizedBaseSpaceHom B S hS U Z₀).hom =
          (relocalizedBaseSpaceHom B S hS U Z₀).hom)).hom = 𝟙 _ :=
      pullback.congrHom_rfl _ _
    have hl' : (isPullback_fibre B S hS U Z₀ (Over.homMk ψ₁ h₁ : T.unop ⟶ U)).isoPullback.inv ≫
          fibreLift B S hS U Z₀ W₀ (Over.homMk ψ₁ h₁ : T.unop ⟶ U)
            (fibreSection B S hS U Z₀ W₀ w₀ (Over.homMk ψ₁ h₁ : T.unop ⟶ U)
              (sectionSpaceEquiv B U.left.1 U.left.2 Z₀ (Over.mk ψ₁) W₀ w₀ s₁)) =
        (isPullback_fibre B S hS U Z₀ (Over.homMk ψ₁ h₁ : T.unop ⟶ U)).isoPullback.inv ≫
          fibreLift B S hS U Z₀ W₀ (Over.homMk ψ₁ h₁ : T.unop ⟶ U)
            (fibreSection B S hS U Z₀ W₀ w₀ (Over.homMk ψ₁ h₁ : T.unop ⟶ U)
              (sectionSpaceEquiv B U.left.1 U.left.2 Z₀ (Over.mk ψ₁) W₀ w₀ s₂)) :=
      (RestrictionPair.lift_eq_of_eq h).trans (by rw [hid]; exact Category.id_comp _)
    exact Subtype.ext (congrArg (Sigma.mk ψ₁)
      ((sectionSpaceEquiv B U.left.1 U.left.2 Z₀ (Over.mk ψ₁) W₀ w₀).injective
        (fibreSection_injective B S hS U Z₀ W₀ w₀ _
          (fibreLift_injective B S hS U Z₀ W₀ _
            ((cancel_epi (isPullback_fibre B S hS U Z₀
              (Over.homMk ψ₁ h₁ : T.unop ⟶ U)).isoPullback.inv).1 hl')))))
  · intro p
    have hb : yoneda.map (yoneda.preimage p.base) = p.base := yoneda.map_preimage p.base
    have hover : p.lift ≫ relocalizedTotalHom B S hS U Z₀ W₀ w₀ =
        pullback.snd p.base (yoneda.map (relocalizedBaseHom B S hS U Z₀)) := p.over
    have hlr : ((pullback.congrHom hb (rfl : yoneda.map (relocalizedBaseHom B S hS U Z₀) =
            yoneda.map (relocalizedBaseHom B S hS U Z₀))).hom ≫ p.lift) ≫
          relocalizedTotalHom B S hS U Z₀ W₀ w₀ =
        pullback.snd (yoneda.map (yoneda.preimage p.base))
          (yoneda.map (relocalizedBaseHom B S hS U Z₀)) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun x => _ ≫ x) hover).trans (pullback.congrHom_hom_snd _ _))
    have hm : ((isPullback_fibre B S hS U Z₀ (yoneda.preimage p.base)).isoPullback.hom ≫
          (pullback.congrHom hb (rfl : yoneda.map (relocalizedBaseHom B S hS U Z₀) =
            yoneda.map (relocalizedBaseHom B S hS U Z₀))).hom ≫ p.lift) ≫
          relocalizedTotalHom B S hS U Z₀ W₀ w₀ =
        yoneda.map (fibreProj₂ B S hS U Z₀ (yoneda.preimage p.base)) := by
      rw [Category.assoc, hlr,
        (isPullback_fibre B S hS U Z₀ (yoneda.preimage p.base)).isoPullback_hom_snd]
    refine ⟨⟨⟨(yoneda.preimage p.base).left,
      (sectionSpaceEquiv B U.left.1 U.left.2 Z₀
          (Over.mk (yoneda.preimage p.base).left) W₀ w₀).symm
        ((fibreSectionsEquiv B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base)).symm
          ((fibreLiftEquiv B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base)).symm ⟨_, hm⟩))⟩,
      Over.w (yoneda.preimage p.base)⟩, ?_⟩
    refine RestrictionPair.ext_of_base_eq hb ?_
    show relocalizedLift B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base) _ = _
    rw [relocalizedLift, Equiv.apply_symm_apply,
      show fibreSection B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base)
            ((fibreSectionsEquiv B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base)).symm
              ((fibreLiftEquiv B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base)).symm ⟨_, hm⟩)) =
          ((fibreLiftEquiv B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base)).symm ⟨_, hm⟩).1 from
        congrArg Subtype.val
          (Equiv.apply_symm_apply (fibreSectionsEquiv B S hS U Z₀ W₀ w₀
            (yoneda.preimage p.base)) _),
      show fibreLift B S hS U Z₀ W₀ (yoneda.preimage p.base)
            ((fibreLiftEquiv B S hS U Z₀ W₀ w₀ (yoneda.preimage p.base)).symm ⟨_, hm⟩).1 =
          (isPullback_fibre B S hS U Z₀ (yoneda.preimage p.base)).isoPullback.hom ≫
            (pullback.congrHom hb (rfl : yoneda.map (relocalizedBaseHom B S hS U Z₀) =
              yoneda.map (relocalizedBaseHom B S hS U Z₀))).hom ≫ p.lift from
        congrArg Subtype.val
          (Equiv.apply_symm_apply (fibreLiftEquiv B S hS U Z₀ W₀ w₀
            (yoneda.preimage p.base)) _),
      Iso.inv_hom_id_assoc]
    rfl

/-! ### The identification -/

/-- The comparison morphism: a section of the relocalized space of sections of `w₀` names a
pair of Stacks 05Y9, hence a point of the restriction of scalars of the relocalized data. -/
noncomputable def relocalizeSectionSpaceHom :
    (OverShriek.relocalizePresheafFunctor U.hom).obj
        (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀) ⟶
      (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
        (relocalizedBaseSpaceHom B S hS U Z₀)).presheaf :=
  restrictionOfScalarsOfPairs
    (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
      (relocalizedBaseSpaceHom B S hS U Z₀))
    (relocalizedPair B S hS U Z₀ W₀ w₀ hW₀)
    (fun f v => relocalizedPair_restrict B S hS U Z₀ W₀ w₀ hW₀ f v)

/-- The pair of Stacks 05Y9 named by the image of `v` under `relocalizeSectionSpaceHom` is
`relocalizedPair T v`. -/
theorem pairEquiv_relocalizeSectionSpaceHom (T : (BigFppfOver B S hS)ᵒᵖ)
    (v : ((OverShriek.relocalizePresheafFunctor U.hom).obj
      (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)).obj T) :
    (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
          (relocalizedBaseSpaceHom B S hS U Z₀)).pairEquiv T.unop
        ((relocalizeSectionSpaceHom B S hS U Z₀ W₀ w₀ hW₀).app T v) =
      relocalizedPair B S hS U Z₀ W₀ w₀ hW₀ T v :=
  pairEquiv_restrictionOfScalarsOfPairs _ _ _ T v

/-- Each component of `relocalizeSectionSpaceHom` is a bijection. -/
instance isIso_relocalizeSectionSpaceHom_app (T : (BigFppfOver B S hS)ᵒᵖ) :
    IsIso ((relocalizeSectionSpaceHom B S hS U Z₀ W₀ w₀ hW₀).app T) :=
  (isIso_iff_bijective _).2
    (((restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
          (relocalizedBaseSpaceHom B S hS U Z₀)).pairEquiv T.unop).symm.bijective.comp
      (bijective_relocalizedPair B S hS U Z₀ W₀ w₀ hW₀ T))

/-- `relocalizeSectionSpaceHom` is an isomorphism of presheaves. -/
instance isIso_relocalizeSectionSpaceHom :
    IsIso (relocalizeSectionSpaceHom B S hS U Z₀ W₀ w₀ hW₀) :=
  NatIso.isIso_of_isIso_app _

/-- The restriction of scalars of `Λ W₀ ⟶ h_{Z_U} ⟶ h_U` is the lower-shriek
relocalization along the structural morphism of `U` of the space of sections of `w₀ : W₀ ⟶ h_{Z₀}`
formed on the big fppf site of the scheme underlying `U`. -/
noncomputable def relocalizeSectionSpaceIso :
    (OverShriek.relocalizePresheafFunctor U.hom).obj
        (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀) ≅
      (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
        (relocalizedBaseSpaceHom B S hS U Z₀)).presheaf :=
  asIso (relocalizeSectionSpaceHom B S hS U Z₀ W₀ w₀ hW₀)

/-- **`relocalizeSectionSpaceHom` is compatible with the two projections to `h_U`**, on
sections over `T`. -/
theorem projection_relocalizeSectionSpaceHom (T : BigFppfOver B S hS)
    (v : ((OverShriek.relocalizePresheafFunctor U.hom).obj
      (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)).obj (op T)) :
    (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
          (relocalizedBaseSpaceHom B S hS U Z₀)).projection.app (op T)
        ((relocalizeSectionSpaceHom B S hS U Z₀ W₀ w₀ hW₀).app (op T) v) =
      (OverShriek.relocalizeToYoneda U.hom
        (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)).app (op T) v := by
  rw [(restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
      (relocalizedBaseSpaceHom B S hS U Z₀)).projection_pairEquiv T _,
    pairEquiv_relocalizeSectionSpaceHom]
  show yonedaEquiv (yoneda.map (Over.homMk v.1.1 v.2 : T ⟶ U)) = _
  rw [yonedaEquiv_yoneda_map]
  rfl

/-- `relocalizeSectionSpaceHom` followed by the projection of the restriction of scalars to
`h_U` is the structural morphism `OverShriek.relocalizeToYoneda` of the relocalization. -/
theorem relocalizeSectionSpaceHom_comp_projection :
    relocalizeSectionSpaceHom B S hS U Z₀ W₀ w₀ hW₀ ≫
        (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
          (relocalizedBaseSpaceHom B S hS U Z₀)).projection =
      OverShriek.relocalizeToYoneda U.hom (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀) :=
  NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun v =>
    projection_relocalizeSectionSpaceHom B S hS U Z₀ W₀ w₀ hW₀ T.unop v)

/-- **Stacks 05XR for a relocalized datum, algebraicity.** If the space of sections of `w₀` is an
algebraic space over `U.left.1`, then the restriction of scalars of the relocalized data is an
algebraic space over `S`. -/
theorem isAlgebraicSpace_restrictionOfScalars_relocalize
    (hss : IsAlgebraicSpace B U.left.1 U.left.2
      (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)) :
    IsAlgebraicSpace B S hS
      (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
        (relocalizedBaseSpaceHom B S hS U Z₀)).presheaf :=
  AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
    (relocalizeSectionSpaceIso B S hS U Z₀ W₀ w₀ hW₀).symm
    (isAlgebraicSpace_relocalizePresheaf B S hS U _ hss)

/-- **Stacks 05XR for a relocalized datum, étaleness of the projection.** If the space of sections
of `w₀` is an algebraic space étale over `U.left.1`, then the projection of the restriction of
scalars of the relocalized data to `h_U` is étale. -/
theorem isEtale_projection_restrictionOfScalars_relocalize
    (hss : IsAlgebraicSpace B U.left.1 U.left.2
      (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀))
    (hsset : IsEtale B U.left.1 U.left.2
      (terminal.from (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀))) :
    IsEtale B S hS
      (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
        (relocalizedBaseSpaceHom B S hS U Z₀)).projection := by
  have h1 : IsEtale B S hS
      (OverShriek.relocalizeToYoneda U.hom (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)) :=
    isEtale_relocalizeToYoneda B U.left.1 S U.left.2 hS U.hom hss hsset
  rw [← relocalizeSectionSpaceHom_comp_projection B S hS U Z₀ W₀ w₀ hW₀] at h1
  exact IsEtale.of_iso_comp (relocalizeSectionSpaceIso B S hS U Z₀ W₀ w₀ hW₀) h1

end Bridge

end AlgebraicGeometry.Space

end

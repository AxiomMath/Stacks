module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistence

/-!
# The rings of global functions of the affine bases of an inverse system of rings

Let `(Aₙ)` be an inverse system of commutative rings, `A = lim Aₙ`, and let `Spec Aₙ`, `Spec A` be
the affine bases of the infinitesimal base changes of Situations [Stacks, Tag 0CX4] and
[Stacks, Tag 0DIK]. This file defines the inverse system `n ↦ Γ(Spec Aₙ, 𝒪)` and its cone with
vertex `Γ(Spec A, 𝒪)`, shows that the cone is a limit cone, and shows that the transition maps are
surjective with locally nilpotent kernels when those of `(Aₙ)` are. These are the hypotheses of
the results of [Stacks, Tag 0CQF] and [Stacks, Tag 0CQG] on derived limits over `A = lim Aₙ`.

## Main definitions

All names are in the namespace `AlgebraicGeometry.Space`.

* `baseSectionsSystem F`: the inverse system `n ↦ Γ(Spec Aₙ, 𝒪)`.
* `baseSectionsCone F`: its cone with vertex `Γ(Spec A, 𝒪)`, whose legs are induced by the
  projections `Spec Aₙ ⟶ Spec A`.

## Main results

* `isLimitBaseSectionsCone`: that cone is a limit cone.
* `surjective_baseSectionsSystem_map`, `isLocallyNilpotent_ker_baseSectionsSystem_map`: the
  transition maps of the system are surjective with locally nilpotent kernels when those of `(Aₙ)`
  are.
* `baseSectionsSystem_obj`, `baseSectionsSystem_map_succ`, `baseSectionsCone_pt`,
  `baseSectionsCone_π_app`: the rings and maps are those of the affine bases `baseObjectAt` and
  `limitBaseObject` of the big fppf site, and of their transitions and projections, by definition.

## References

* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
* [Stacks Project, Tag 0CQG](https://stacks.math.columbia.edu/tag/0CQG)
* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt baseProjection baseTransition)

universe u

namespace AlgebraicGeometry.Space

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})

/-- The inverse system `n ↦ Γ(Spec Aₙ, 𝒪)` of the rings of global functions of the affine
bases, with the maps induced on global functions by the transitions `Spec Aₙ ⟶ Spec Aₙ₊₁`. -/
abbrev baseSectionsSystem : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  F ⋙ Scheme.Spec.rightOp ⋙ Scheme.Γ

/-- The cone `Γ(Spec A, 𝒪) ⟶ Γ(Spec Aₙ, 𝒪)` over `baseSectionsSystem F`, with the maps induced
on global functions by the projections `Spec Aₙ ⟶ Spec A`. -/
abbrev baseSectionsCone : Cone (baseSectionsSystem F) :=
  (Scheme.Spec.rightOp ⋙ Scheme.Γ).mapCone (limit.cone F)

/-- The cone `baseSectionsCone F` is a limit cone: `Γ(Spec A, 𝒪) = lim Γ(Spec Aₙ, 𝒪)`. -/
def isLimitBaseSectionsCone : IsLimit (baseSectionsCone F) :=
  haveI : PreservesLimit F (Scheme.Spec.rightOp ⋙ Scheme.Γ) :=
    preservesLimit_of_natIso F Scheme.SpecΓIdentity.symm
  isLimitOfPreserves (Scheme.Spec.rightOp ⋙ Scheme.Γ) (limit.isLimit F)

/-- A map of `baseSectionsSystem F` is the map of `F` conjugated by the isomorphisms
`Γ(Spec R, 𝒪) ≅ R`. -/
lemma baseSectionsSystem_map_hom {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (baseSectionsSystem F).map f =
      (Scheme.ΓSpecIso (F.obj m)).hom ≫ F.map f ≫ (Scheme.ΓSpecIso (F.obj n)).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- A map of `baseSectionsSystem F`, as a function, is the map of `F` conjugated by the
isomorphisms `Γ(Spec R, 𝒪) ≅ R`. -/
lemma coe_baseSectionsSystem_map {m n : ℕᵒᵖ} (f : m ⟶ n) :
    ⇑((baseSectionsSystem F).map f).hom =
      ⇑(Scheme.ΓSpecIso (F.obj n)).inv.hom ∘ ⇑(F.map f).hom ∘
        ⇑(Scheme.ΓSpecIso (F.obj m)).hom := by
  have h := congrArg (fun g : (baseSectionsSystem F).obj m ⟶ (baseSectionsSystem F).obj n =>
    ⇑g.hom) (baseSectionsSystem_map_hom F f)
  exact h

/-- The transition maps of `baseSectionsSystem F` are surjective when those of `F` are. -/
theorem surjective_baseSectionsSystem_map {m n : ℕᵒᵖ} (f : m ⟶ n)
    (hf : Function.Surjective (F.map f).hom) :
    Function.Surjective ((baseSectionsSystem F).map f).hom := by
  rw [coe_baseSectionsSystem_map]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (F.obj n)).inv).2.comp hf).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (F.obj m)).hom).2

/-- The transition maps of `baseSectionsSystem F` have locally nilpotent kernels when those of
`F` do. -/
theorem isLocallyNilpotent_ker_baseSectionsSystem_map {m n : ℕᵒᵖ} (f : m ⟶ n)
    (hf : (RingHom.ker (F.map f).hom).IsLocallyNilpotent) :
    (RingHom.ker ((baseSectionsSystem F).map f).hom).IsLocallyNilpotent := by
  intro x hx
  have hx₁ : (Scheme.ΓSpecIso (F.obj n)).inv.hom
      ((F.map f).hom ((Scheme.ΓSpecIso (F.obj m)).hom.hom x)) = 0 := by
    have h := congrFun (coe_baseSectionsSystem_map F f) x
    rw [RingHom.mem_ker] at hx
    exact h.symm.trans hx
  have hx₂ : (F.map f).hom ((Scheme.ΓSpecIso (F.obj m)).hom.hom x) = 0 :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (F.obj n)).inv).1
      (hx₁.trans (map_zero _).symm)
  have hn := (hf _ (RingHom.mem_ker.2 hx₂)).map (Scheme.ΓSpecIso (F.obj m)).inv.hom
  have e : (Scheme.ΓSpecIso (F.obj m)).inv.hom ((Scheme.ΓSpecIso (F.obj m)).hom.hom x) = x :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (F.obj m)) x
  rw [e] at hn
  exact hn

variable (B : BigFppfSite.{u}) (hS : B.Contains (limitBase F))
  (hSn : ∀ n : ℕ, B.Contains (baseAt F n))

/-- The ring of `baseSectionsSystem F` at level `n` is the ring of global functions of the affine
base `baseObjectAt` at level `n`. -/
lemma baseSectionsSystem_obj (n : ℕ) :
    (baseSectionsSystem F).obj (op n) =
      Γ((BigFppfOver.toScheme B (limitBase F) hS).obj (baseObjectAt F B hS hSn n), ⊤) :=
  rfl

/-- The transition map of `baseSectionsSystem F` from level `n + 1` to level `n` is the map
induced on global functions by the transition `baseObjectTransition` of the affine bases. -/
lemma baseSectionsSystem_map_succ (n : ℕ) :
    (baseSectionsSystem F).map (homOfLE (Nat.le_succ n)).op =
      Scheme.Hom.appTop ((BigFppfOver.toScheme B (limitBase F) hS).map
        (baseObjectTransition F B hS hSn n)) :=
  rfl

/-- The vertex of `baseSectionsCone F` is the ring of global functions of the inverse-limit base
`limitBaseObject`. -/
lemma baseSectionsCone_pt :
    (baseSectionsCone F).pt =
      Γ((BigFppfOver.toScheme B (limitBase F) hS).obj (limitBaseObject F B hS), ⊤) :=
  rfl

/-- The leg of `baseSectionsCone F` at level `n` is the map induced on global functions by the
projection `baseObjectProjection` of the affine base at level `n` to the inverse-limit base. -/
lemma baseSectionsCone_π_app (n : ℕ) :
    (baseSectionsCone F).π.app (op n) =
      Scheme.Hom.appTop ((BigFppfOver.toScheme B (limitBase F) hS).map
        (baseObjectProjection F B hS hSn n)) :=
  rfl

end AlgebraicGeometry.Space

end

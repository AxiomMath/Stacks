module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Basic

/-!
# The derived completion functor attached to a reflector

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals. [Stacks, Tag 099F] asserts that the
inclusion `D_comp(𝒪) ⥤ D(𝒪)` of the derived-complete objects has a left adjoint. *Granting* such
a left adjoint — that is, under the instance hypothesis that the inclusion
`ObjectProperty.ι (AlgebraicGeometry.RingedSite.IsDerivedComplete X I)` is a right adjoint —
this file packages the data every consumer of that tag uses: the endofunctor `K ↦ K^∧` of
`D(𝒪)`, the map `K ⟶ K^∧`, the derived completeness of `K^∧`, and the invertibility of
`K ⟶ K^∧` on a derived-complete `K`.

Nothing here proves Tag 099F. The hypothesis is an instance argument, so a proof of Tag 099F —
or, today, one of its proved instances such as
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_zeroSubmodule` — discharges it.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedCompletionAdjunction`: the reflector adjunction
  `(-)^∧ ⊣ ι` between `D(𝒪)` and the derived-complete objects.
* `AlgebraicGeometry.RingedSite.derivedCompletion`: the derived completion functor `K ↦ K^∧` on
  `D(𝒪)`, that is the reflector followed by the inclusion.
* `AlgebraicGeometry.RingedSite.derivedCompletionUnit`: the natural map `K ⟶ K^∧`.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_derivedCompletion_obj`: `K^∧` is derived
  complete.
* `AlgebraicGeometry.RingedSite.isIso_derivedCompletionUnit_app`: `K ⟶ K^∧` is invertible when
  `K` is derived complete.
* `AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit`: the universal property in the
  form consumers need — a map out of `K^∧` into a derived-complete object is determined by its
  composite with `K ⟶ K^∧`.

## Implementation notes

The universes are those of [Stacks, Tag 0999] collapsed to a single `u`, a
`AlgebraicGeometry.RingedSite.{u, u, u}` with coefficient universe `u`. That is the shape in
which the derived direct image of this directory is available, and the shape the consumers of
this file need; the predicate itself is stated in four independent universes.

The invertibility of the unit at a derived-complete object is the general fact that the unit of
an adjunction whose right adjoint is fully faithful is invertible on the image of that right
adjoint — here `Functor.whiskerLeft`, whose components at `⟨K, hK⟩` is the unit at `K`, because
the inclusion of a full subcategory sends `⟨K, hK⟩` to `K` on the nose.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- The reflector adjunction of [Stacks, Tag 099F]: derived completion is left adjoint to the
inclusion of the derived-complete objects into `D(𝒪)`. -/
def derivedCompletionAdjunction :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).leftAdjoint ⊣
      ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I) :=
  Adjunction.ofIsRightAdjoint _

/-- The derived completion functor `K ↦ K^∧` on `D(𝒪)`: the reflector of
[Stacks, Tag 099F] followed by the inclusion of the derived-complete objects. -/
def derivedCompletion :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⥤
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).leftAdjoint ⋙
    ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)

/-- The natural map `K ⟶ K^∧` into the derived completion, that is the unit of the reflector
adjunction. -/
def derivedCompletionUnit :
    𝟭 (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ⟶
      derivedCompletion X I :=
  (derivedCompletionAdjunction X I).unit

/-- The derived completion `K^∧` of any object is derived complete: it is the image under the
inclusion of an object of the full subcategory of derived-complete objects. -/
theorem isDerivedComplete_derivedCompletion_obj
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedComplete.{u, u, u, u} X I ((derivedCompletion X I).obj K) :=
  ((ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).leftAdjoint.obj K).property

/-- The map `K ⟶ K^∧` is invertible when `K` is already derived complete: the inclusion of the
derived-complete objects is fully faithful, so the unit of the reflector adjunction is invertible
on its image. -/
theorem isIso_derivedCompletionUnit_app
    {K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hK : IsDerivedComplete.{u, u, u, u} X I K) :
    IsIso ((derivedCompletionUnit X I).app K) := by
  have h : IsIso (Functor.whiskerLeft (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I))
      (derivedCompletionAdjunction X I).unit) := inferInstance
  exact NatIso.isIso_app_of_isIso
    (Functor.whiskerLeft (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I))
      (derivedCompletionAdjunction X I).unit)
    (⟨K, hK⟩ : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I))

/-- **The universal property of the derived completion.** Two maps `K^∧ ⟶ N` into a
derived-complete object which agree after the unit `K ⟶ K^∧` are equal.

The inclusion of the derived-complete objects is full, so each of the two maps is the image of a
map into `⟨N, hN⟩` in that subcategory; and composing with the unit is the hom-equivalence of the
reflector adjunction, which is a bijection. This is the form in which a consumer identifies a map
out of `K^∧` that it has built by hand with the one the adjunction produces. -/
theorem hom_ext_derivedCompletionUnit
    {K N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hN : IsDerivedComplete.{u, u, u, u} X I N)
    {g₁ g₂ : (derivedCompletion X I).obj K ⟶ N}
    (h : (derivedCompletionUnit X I).app K ≫ g₁ =
      (derivedCompletionUnit X I).app K ≫ g₂) : g₁ = g₂ := by
  have key : ∀ g : (derivedCompletion X I).obj K ⟶ N, ∃ g' : (ObjectProperty.ι
      (IsDerivedComplete.{u, u, u, u} X I)).leftAdjoint.obj K ⟶ ⟨N, hN⟩,
      (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map g' = g :=
    fun g ↦ (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map_surjective
      (Y := (⟨N, hN⟩ : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I))) g
  obtain ⟨g₁', rfl⟩ := key g₁
  obtain ⟨g₂', rfl⟩ := key g₂
  refine congrArg _ (((derivedCompletionAdjunction X I).homEquiv K _).injective ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

/-- **Any universal arrow into the derived-complete objects *is* the derived completion.** If
`u : K ⟶ N` has derived-complete target and precomposition with it is bijective on morphisms into
every derived-complete object, then `N` is the derived completion of `K`, by a unique isomorphism
carrying the unit `K ⟶ K^∧` to `u`.

This is how a *model* for the completion is matched with the reflector of [Stacks, Tag 099F],
which is an arbitrary choice of left adjoint and carries no formula: the forward map is the
adjunct of `u`, the backward map is the preimage of the unit under the given bijection, and the
two composites are the identity by the two uniqueness statements — the universal property of the
reflector for one, the injectivity of precomposition with `u` for the other. -/
theorem exists_iso_derivedCompletion_of_bijective_precomp
    {K N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hN : IsDerivedComplete.{u, u, u, u} X I N) (u : K ⟶ N)
    (hu : ∀ M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      IsDerivedComplete.{u, u, u, u} X I M → Function.Bijective (fun g : N ⟶ M ↦ u ≫ g)) :
    ∃ θ : (derivedCompletion X I).obj K ≅ N,
      (derivedCompletionUnit X I).app K ≫ θ.hom = u := by
  obtain ⟨g, hg⟩ := ((derivedCompletionAdjunction X I).homEquiv K
    (⟨N, hN⟩ : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I))).surjective u
  rw [Adjunction.homEquiv_unit] at hg
  obtain ⟨g', hg'⟩ := (hu _ (isDerivedComplete_derivedCompletion_obj X I K)).2
    ((derivedCompletionUnit X I).app K)
  refine ⟨⟨(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map g, g', ?_, ?_⟩, hg⟩
  · refine hom_ext_derivedCompletionUnit X I (isDerivedComplete_derivedCompletion_obj X I K) ?_
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g') hg).trans hg')).trans
      (Category.comp_id _).symm
  · refine (hu N hN).1 ?_
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hg').trans hg)).trans
      (Category.comp_id _).symm

end AlgebraicGeometry.RingedSite

end

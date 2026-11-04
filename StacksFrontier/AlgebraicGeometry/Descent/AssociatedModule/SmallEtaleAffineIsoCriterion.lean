module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinalSectionsTop
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion

/-!
# A morphism of quasi-coherent modules on the small étale site of an affine scheme

Let `S` be an affine scheme. A morphism `α : 𝓖 ⟶ 𝓗` of sheaves of modules on the small étale
site of `S` which are quasi-coherent there (Stacks 03DL (6)) is an isomorphism as soon as it is
bijective on the sections over the final object `S / S`.

Both modules are associated modules: the counit `(𝓖|_{S_Zar})^a ⟶ 𝓖` of the adjunction of
Stacks 03DU (4) is an isomorphism for a quasi-coherent `𝓖`, and so is the one for `𝓗`, so `α` is
an isomorphism as soon as its restriction `α|_{S_Zar}` to the small Zariski site is. That is a
morphism of quasi-coherent `𝒪_S`-modules on an affine scheme, hence an isomorphism as soon as it
is bijective on global sections, and the global sections of a restriction are the sections over
the final object.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_of_bijective_app_final`: the criterion.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of quasi-coherent modules on the small étale site of an affine scheme which is
bijective on the sections over the final object is an isomorphism.** -/
theorem isIso_of_bijective_app_final [AlgebraicGeometry.IsAffine S]
    {P Q : SheafOfModules.{u} (structureSheaf B S hS)}
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) (α : P ⟶ Q)
    (hα : Function.Bijective (α.val.app (op (final B S hS)))) : IsIso α := by
  have key : ∀ M : SheafOfModules.{u} (structureSheaf B S hS), M.IsQuasicoherentOnSite →
      SheafOfModules.IsQuasicoherent ((restrictModule B S hS).obj M) ∧
        IsIso ((associatedModuleAdjunction B S hS).counit.app M) := fun M hM =>
    ⟨isQuasicoherent_restrictModule B S hS M hM,
      isIso_counit B S hS M hM (isQuasicoherent_restrictModule B S hS M hM)⟩
  obtain ⟨_, _⟩ := key P hP
  obtain ⟨_, _⟩ := key Q hQ
  have htop : Function.Bijective (α.val.app (op (opensObj B S hS ⊤))) := by
    let g := (finalIsoOpensObjTop B S hS).hom.op
    have hnat := ((PresheafOfModules.toPresheaf _).map α.val).naturality g
    have hbij : ∀ M : SheafOfModules.{u} (structureSheaf B S hS),
        Function.Bijective (M.val.presheaf.map g) := fun M =>
      (ConcreteCategory.isIso_iff_bijective _).1 (Functor.map_isIso _ _)
    have hcomp : ⇑(Q.val.presheaf.map g) ∘ ⇑(α.val.app (op (opensObj B S hS ⊤))) =
        ⇑(α.val.app (op (final B S hS))) ∘ ⇑(P.val.presheaf.map g) := by
      funext m
      exact (ConcreteCategory.congr_hom hnat m).symm
    exact (Function.Bijective.of_comp_iff' (hbij Q) _).1 (hcomp ▸ hα.comp (hbij P))
  have : IsIso ((restrictModule B S hS).map α) :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _
      ((ConcreteCategory.isIso_iff_bijective _).2 htop)
  have : IsIso ((associatedModuleAdjunction B S hS).counit.app P ≫ α) := by
    have := (associatedModuleAdjunction B S hS).counit.naturality α
    simp only [Functor.id_map, Functor.comp_map] at this
    rw [← this]
    infer_instance
  exact IsIso.of_isIso_comp_left ((associatedModuleAdjunction B S hS).counit.app P) α

end AlgebraicGeometry.SmallEtale

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Bijective

/-!
# Recognizing an isomorphism of sheaves of modules

Two general facts, and their application to the twist comparison
`Stacks.ProjTwistComparison.twistMap` of
`StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison`.

The comparison is defined as an adjoint transpose, so it is not given by a formula on sections;
what is given by a formula on sections is its transpose
`Stacks.ProjTwistComparison.pushforwardTwistMap`. The two facts below turn a statement about
sections into a statement about the comparison:

* a morphism of sheaves of modules which is bijective on sections over every object is an
  isomorphism; and
* composing with the comparison isomorphism of two left adjoints of the same functor does not
  change an adjoint transpose, so a morphism out of one left adjoint is an isomorphism exactly
  when the corresponding morphism out of the other is.

By the second, the inverse image along an open immersion may be replaced by restriction, whose
sections are the sections of the original sheaf over the image open.

## Main results

* `Stacks.SheafOfModulesIso.isIso_of_app_isIso`
* `Stacks.SheafOfModulesIso.homEquiv_leftAdjointUniq_hom_app_comp` and
  `Stacks.SheafOfModulesIso.isIso_homEquiv_symm_of_isIso`
* `Stacks.ProjTwistComparison.isIso_twistMap_of_bijective`: the twist comparison is an
  isomorphism as soon as it is bijective on sections over the opens of the image.
* `Stacks.ProjTwistComparison.isIso_twistMap`: for a degreewise localization away from a
  degree-zero element the twist comparison is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.SheafOfModulesIso

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}

/-- **A morphism of sheaves of modules which is an isomorphism on sections over every object is
an isomorphism.** -/
theorem isIso_of_app_isIso {M N : SheafOfModules.{v} R} (f : M ⟶ N)
    (h : ∀ X, IsIso (f.val.app X)) : IsIso f := by
  have hiso : IsIso ((SheafOfModules.forget R ⋙
      PresheafOfModules.toPresheaf R.obj).map f) := by
    have : ∀ X, IsIso (((SheafOfModules.forget R ⋙
        PresheafOfModules.toPresheaf R.obj).map f).app X) := by
      intro X
      rw [ConcreteCategory.isIso_iff_bijective]
      exact (ConcreteCategory.isIso_iff_bijective (f.val.app X)).1 (h X)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)

end

section

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- **Precomposing with the comparison of two left adjoints does not change an adjoint
transpose.** If `F` and `F'` are both left adjoint to `G`, then for `f : F'.obj x ⟶ y` the
transpose of `f` along the second adjunction is the transpose, along the first, of `f`
precomposed with `CategoryTheory.Adjunction.leftAdjointUniq`. -/
theorem homEquiv_leftAdjointUniq_hom_app_comp {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) (x : C) (y : D) (f : F'.obj x ⟶ y) :
    adj1.homEquiv x y ((Adjunction.leftAdjointUniq adj1 adj2).hom.app x ≫ f) =
      adj2.homEquiv x y f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]

/-- The two transposes of one morphism, along two adjunctions with the same right adjoint,
differ by the comparison isomorphism of the left adjoints. -/
theorem leftAdjointUniq_hom_app_comp_homEquiv_symm {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) (x : C) (y : D) (g : x ⟶ G.obj y) :
    (Adjunction.leftAdjointUniq adj1 adj2).hom.app x ≫ (adj2.homEquiv x y).symm g =
      (adj1.homEquiv x y).symm g :=
  (adj1.homEquiv x y).injective <| by
    rw [homEquiv_leftAdjointUniq_hom_app_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- A morphism out of one left adjoint is an isomorphism when the corresponding morphism out of
another left adjoint of the same functor is. -/
theorem isIso_homEquiv_symm_of_isIso {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) (y : D) (g : x ⟶ G.obj y) (h : IsIso ((adj1.homEquiv x y).symm g)) :
    IsIso ((adj2.homEquiv x y).symm g) := by
  rw [← leftAdjointUniq_hom_app_comp_homEquiv_symm adj2 adj1]
  infer_instance

end

end Stacks.SheafOfModulesIso

namespace Stacks.ProjTwistComparison

open AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ)
  [IsOpenImmersion (AlgebraicGeometry.Proj.map φ hφ)]

/-- **The twist comparison is an isomorphism as soon as it is bijective on sections over the
opens of the image.** For `r = AlgebraicGeometry.Proj.map φ` an open immersion, `θ` is an
isomorphism provided the explicit comparison on sections,
`Stacks.ProjTwistComparison.sectionsMap`, is bijective over every open of the form `r(V)`. -/
theorem isIso_twistMap_of_bijective
    (h : ∀ V : (AlgebraicGeometry.Proj ℬ).Opens,
      Function.Bijective (sectionsMap φ hφ n
        ((AlgebraicGeometry.Proj.map φ hφ).opensFunctor.obj V))) :
    IsIso (twistMap φ hφ n) := by
  have hmap : IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.Proj.map φ hφ)).map (pushforwardTwistMap φ hφ n)) := by
    refine Stacks.SheafOfModulesIso.isIso_of_app_isIso _ fun X => ?_
    obtain ⟨V⟩ := X
    rw [ConcreteCategory.isIso_iff_bijective]
    exact h V
  have hcounit : IsIso ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction
      (AlgebraicGeometry.Proj.map φ hφ)).counit.app (twistingSheaf ℬ n)) :=
    NatIso.isIso_app_of_isIso _ _
  have hrestrict : IsIso (((AlgebraicGeometry.Scheme.Modules.restrictAdjunction
      (AlgebraicGeometry.Proj.map φ hφ)).homEquiv _ _).symm (pushforwardTwistMap φ hφ n)) := by
    have hcomp : IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
          (AlgebraicGeometry.Proj.map φ hφ)).map (pushforwardTwistMap φ hφ n) ≫
        (AlgebraicGeometry.Scheme.Modules.restrictAdjunction
          (AlgebraicGeometry.Proj.map φ hφ)).counit.app (twistingSheaf ℬ n)) := inferInstance
    exact (Adjunction.homEquiv_counit
      (adj := AlgebraicGeometry.Scheme.Modules.restrictAdjunction
        (AlgebraicGeometry.Proj.map φ hφ))
      (g := pushforwardTwistMap φ hφ n)).symm ▸ hcomp
  exact Stacks.SheafOfModulesIso.isIso_homEquiv_symm_of_isIso _ _ _ _ _ hrestrict

omit [IsOpenImmersion (AlgebraicGeometry.Proj.map φ hφ)] in
/-- **The canonical twist comparison of a degreewise localization is an isomorphism.** If `φ` is,
in each degree, the localization of `𝒜` away from a degree-zero element `g`, then for every `n`
the comparison `θ : r^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)` is an isomorphism. -/
@[stacks 01NO "the twist comparison is an isomorphism, for a degreewise localization away from a \
degree-zero element; the descent to a general affine open and the compatibility with the \
multiplication maps are not covered"]
theorem isIso_twistMap {g : A} (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) : IsIso (twistMap φ hφ n) := by
  have hoi := Stacks.ProjAway.isOpenImmersion_map h hg hφ
  refine isIso_twistMap_of_bijective φ hφ n fun V =>
    bijective_sectionsMap φ h hg hφ n _ fun x => ?_
  obtain ⟨y, -, hy⟩ := x.2
  have hx : x.1 ∈ (AlgebraicGeometry.Proj.map φ hφ).opensRange := ⟨y, hy⟩
  rw [Stacks.ProjAway.opensRange_map h hg hφ] at hx
  exact (AlgebraicGeometry.Proj.mem_basicOpen 𝒜 g x.1).mp hx

end Stacks.ProjTwistComparison

end

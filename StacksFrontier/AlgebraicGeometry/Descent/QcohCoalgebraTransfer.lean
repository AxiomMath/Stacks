module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineQuasicoherentHoms
public import StacksFrontier.AlgebraicGeometry.Descent.DescentBaseChangeMate

/-!
# From quasi-coherent coalgebras to coalgebras of sheaves of modules

A morphism of Eilenberg–Moore coalgebras over the adjunction
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` on all sheaves of modules,
between the images of two quasi-coherent modules, is the same as a morphism of coalgebras over
the adjunction `Stacks.Descent.pullbackQcohAdjunction` on quasi-coherent modules, on the same
underlying morphism of sheaves of modules. Consequently, for a faithfully flat morphism of affine
schemes, pulling a morphism of quasi-coherent modules back is a bijection onto the morphisms of
the associated descent data: the one-element affine case of the full-faithfulness half of
[Stacks, Tag 023T].

## Main definitions

* `Stacks.Descent.coalgebraHomPullbackQcoh`: a morphism of Eilenberg–Moore coalgebras over
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` between the images of two
  quasi-coherent modules is a morphism of coalgebras over
  `Stacks.Descent.pullbackQcohAdjunction`, on the same underlying morphism.

## Main results

* `Stacks.Descent.bijective_comparison_map_pullbackPushforward_specMap`: for quasi-coherent
  modules on `Spec R`, the Eilenberg–Moore comparison functor of the adjunction on all sheaves
  of modules along a faithfully flat `Spec.map φ` is bijective on hom-sets.
* `Stacks.Descent.bijective_toDescentData_map_specMap_of_isPushout`: for a faithfully flat
  `φ : R ⟶ S` and a presentation of the pushout of `φ` with itself, pulling a morphism of
  quasi-coherent modules on `Spec R` back to `Spec S` is a bijection onto the morphisms of the
  associated descent data.
* `Stacks.Descent.bijective_toDescentData_map_specMap`: for a faithfully flat `φ : R ⟶ S`,
  pulling a morphism of quasi-coherent modules on `Spec R` back to `Spec S` is a bijection onto
  the morphisms of the associated descent data.

## Implementation notes

The coalgebra condition in `Stacks.Descent.coalgebraHomPullbackQcoh` is reduced to the
underlying equation by `change`, not `rw` or `simp`: rewriting re-elaborates the composite at
`implicit` transparency, where it is no longer type-correct.

In `Stacks.Descent.bijective_toDescentData_map_specMap_of_isPushout` the isomorphism is obtained
from `Stacks.AlgebraicGeometry.ModuleDescentBaseChange.isIso_descentBaseChange_specMap` at the
object spelled with `AlgebraicGeometry.modulePullbackPseudofunctor`, not from
`Stacks.AlgebraicGeometry.ModuleDescentBaseChange.mono_descentBaseChange_specMap`: a `Mono`
converted between the two definitionally equal spellings of the inverse image fails kernel
checking.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe t u

namespace Stacks.Descent

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- A morphism of Eilenberg–Moore coalgebras for the comonad of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` between the images of two
quasi-coherent modules is a morphism of coalgebras for the comonad of
`Stacks.Descent.pullbackQcohAdjunction`, on the same underlying morphism of sheaves of modules. -/
noncomputable def coalgebraHomPullbackQcoh
    {M N : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory}
    (g : (Comonad.comparison
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).obj M.obj ⟶
      (Comonad.comparison
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).obj N.obj) :
    (Comonad.comparison (pullbackQcohAdjunction φ)).obj M ⟶
      (Comonad.comparison (pullbackQcohAdjunction φ)).obj N where
  f := ObjectProperty.homMk g.f
  h := by
    apply ObjectProperty.hom_ext
    change (Scheme.Modules.pullback (Spec.map φ)).map
          ((pullbackQcohAdjunction φ).unit.app M).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map φ)).toComonad.toFunctor.map g.f =
      g.f ≫ (Scheme.Modules.pullback (Spec.map φ)).map
        ((pullbackQcohAdjunction φ).unit.app N).hom
    rw [unit_pullbackQcohAdjunction_app_hom, unit_pullbackQcohAdjunction_app_hom]
    exact g.h

/-- The underlying morphism of sheaves of modules of `coalgebraHomPullbackQcoh φ g` is `g.f`. -/
@[simp]
lemma coalgebraHomPullbackQcoh_f_hom
    {M N : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory}
    (g : (Comonad.comparison
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).obj M.obj ⟶
      (Comonad.comparison
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).obj N.obj) :
    (coalgebraHomPullbackQcoh φ g).f.hom = g.f :=
  rfl

/-- For quasi-coherent modules `M`, `N` on `Spec R` and a faithfully flat `φ`, the Eilenberg–Moore
comparison functor of `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)`
is bijective on `M ⟶ N`. -/
theorem bijective_comparison_map_pullbackPushforward_specMap (hφ : φ.hom.FaithfullyFlat)
    (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective ((Comonad.comparison
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).map : (M ⟶ N) → _) := by
  have hb := bijective_comparison_map_pullbackQcoh φ hφ
    (M := ⟨M, ‹M.IsQuasicoherent›⟩) (N := ⟨N, ‹N.IsQuasicoherent›⟩)
  refine ⟨fun α α' hα ↦ congrArg InducedCategory.Hom.hom (hb.1 (Comonad.Coalgebra.Hom.ext
    (ObjectProperty.hom_ext _ (congrArg Comonad.Coalgebra.Hom.f hα)))), fun g ↦ ?_⟩
  obtain ⟨β, hβ⟩ := hb.2 (coalgebraHomPullbackQcoh φ g)
  exact ⟨β.hom, Comonad.Coalgebra.Hom.ext
    (congrArg InducedCategory.Hom.hom (congrArg Comonad.Coalgebra.Hom.f hβ))⟩

/-- Let `φ : R ⟶ S` be faithfully flat and let `ψ₁, ψ₂ : S ⟶ P` present `P` as the pushout of `φ`
with itself, both categorically and in the sense of `MilnorPatching.IsPushoutSquare`. Then for a
one-element index type `ι`, pulling a morphism of quasi-coherent modules on `Spec R` back to
`Spec S` is a bijection onto the morphisms of the associated descent data. -/
theorem bijective_toDescentData_map_specMap_of_isPushout {P : CommRingCat.{u}} {ψ₁ ψ₂ : S ⟶ P}
    (hφ : φ.hom.FaithfullyFlat) (hpc : IsPushout φ φ ψ₁ ψ₂)
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    {ι : Type t} [Unique ι] (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective ((modulePullbackPseudofunctor.toDescentData
      (fun _ : ι ↦ Spec.map φ)).map : (M ⟶ N) → _) := by
  have hq : ((modulePullbackPseudofunctor.map
      (Spec.map φ).op.toLoc).toFunctor.obj N).IsQuasicoherent :=
    isQuasicoherent_pullback_specMap φ N
  have hiso := AlgebraicGeometry.ModuleDescentBaseChange.isIso_descentBaseChange_specMap hpc hp
    ((modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj N)
  exact Pseudofunctor.bijective_toDescentData_map_of_bijective_comparison_map
    (AlgebraicGeometry.ModuleDescentBaseChange.specChosenPullback hpc)
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (Scheme.Modules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.ModuleDescentBaseChange.specChosenPullback hpc).p₁)
    inferInstance (bijective_comparison_map_pullbackPushforward_specMap φ hφ M N)

/-- For a faithfully flat morphism `φ : R ⟶ S` of commutative rings, a one-element index type `ι`,
and quasi-coherent modules `M`, `N` on `Spec R`, pulling a morphism `M ⟶ N` back to `Spec S` is a
bijection onto the morphisms of the associated descent data. -/
theorem bijective_toDescentData_map_specMap (hφ : φ.hom.FaithfullyFlat) {ι : Type t} [Unique ι]
    (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective ((modulePullbackPseudofunctor.toDescentData
      (fun _ : ι ↦ Spec.map φ)).map : (M ⟶ N) → _) := by
  let _ : Algebra R S := φ.hom.toAlgebra
  have hpc : IsPushout φ φ
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : S →+* S ⊗[R] S))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S)) := by
    have h := (CommRingCat.isPushout_tensorProduct R S S).flip
    rwa [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] at h
  exact bijective_toDescentData_map_specMap_of_isPushout φ hφ hpc
    MilnorPatching.tensorPushout M N

end Stacks.Descent

end

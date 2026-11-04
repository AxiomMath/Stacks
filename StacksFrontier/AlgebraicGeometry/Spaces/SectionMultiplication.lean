module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionGeneratingLocusPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModuleCoherent

/-!
# Multiplication by a global section of a module

Let `X` be an algebraic space over a scheme `S` and let `𝓜` be an `𝒪_X`-module with a global
section `s`.  For every `𝒪_X`-module `𝓕` there is the map `𝓕 ⟶ 𝓕 ⊗ 𝓜`, `f ↦ f ⊗ s`: the inverse
of the right unit constraint followed by `𝓕 ⊗ φ_s`, where `φ_s : 𝒪_X ⟶ 𝓜` is `1 ↦ s`.  With
`𝓜 = 𝓛^{⊗ d}` and iterated, this is the map `s^a : 𝓕 ⟶ 𝓕 ⊗ 𝓛^{⊗ ad}` of the proof of
Stacks 0D2W.

Over the generating locus of `s` this map is an isomorphism when `𝓜` is invertible.  The étale
pullback along `g : Y ⟶ X` is restriction along the postcomposition functor of small étale sites,
which commutes with tensor products naturally in both variables
(`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality_right`), so the pullback of
`𝓕 ⊗ φ_s` is `g^*𝓕 ⊗ g^*φ_s` up to isomorphism, and `g^*φ_s` is invertible when the image of `g`
lies in the generating locus
(`AlgebraicGeometry.Space.isIso_modulePullback_map_of_range_subset_sectionGeneratingLocus`).

## Main definitions

* `AlgebraicGeometry.Space.sectionMul`: multiplication by a global section, `𝓕 ⟶ 𝓕 ⊗ 𝓜`.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorProductRightUnitor_inv_naturality`: the inverse of the
  right unit constraint is natural.
* `AlgebraicGeometry.Space.sectionMul_naturality`: multiplication by a section is natural in the
  module.

* `AlgebraicGeometry.Space.isIso_etaleModulePullback_map_tensorObjMap`: the étale pullback of
  `𝓕 ⊗ φ` is invertible once that of `φ` is.
* `AlgebraicGeometry.Space.isIso_etaleModulePullback_map_sectionMul`: multiplication by a section
  of an invertible module is invertible over the generating locus of the section.

## Implementation notes

The tensor product is the one `AlgebraicGeometry.Space.twistStep` is built from, applied at the
projections of `AlgebraicGeometry.Space.smallEtaleRingedSite` where its sheafification instances
live; the restriction comparison is applied at the topology `SmallEtale.topology`, where the
continuity and cocontinuity instances of the postcomposition functor live.  The two spellings are
definitionally equal.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The inverse of the right unit constraint is natural**: `a` followed by `N ≅ N ⊗ 𝒪` is
`M ≅ M ⊗ 𝒪` followed by `a ⊗ 𝒪`. -/
theorem tensorProductRightUnitor_inv_naturality
    {M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (a : M ⟶ N) :
    a ≫ (tensorProductRightUnitor O hO N).inv =
      (tensorProductRightUnitor O hO M).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map a).app
          _ := by
  have h := Stacks.IdealTorsion.Eta.tensorProductRightUnitor_naturality O hO a
  rw [Functor.uncurry_obj_map] at h
  dsimp only at h
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact (Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2 h.symm).trans (Category.assoc _ _ _).symm)

/-- **Multiplication by a map out of the structure sheaf is natural** in the module: for
`φ : 𝒪 ⟶ 𝓜` and `a : 𝓕 ⟶ 𝓕'`, the square formed by `𝓕 ≅ 𝓕 ⊗ 𝒪 ⟶ 𝓕 ⊗ 𝓜` and `a`, `a ⊗ 𝓜`
commutes. -/
theorem tensorProductRightUnitor_inv_comp_map_naturality
    {F F' M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (a : F ⟶ F')
    (φ : _root_.SheafOfModules.unit _ ⟶ M) :
    a ≫ (tensorProductRightUnitor O hO F').inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F').map
          φ =
      ((tensorProductRightUnitor O hO F).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F).map
          φ) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map a).app
          M :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (tensorProductRightUnitor_inv_naturality O hO a)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
            a).naturality φ).symm).trans (Category.assoc _ _ _).symm)))

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Multiplication by a global section `s` of `𝓜`: the map `𝓕 ⟶ 𝓕 ⊗ 𝓜`, `f ↦ f ⊗ s`. -/
noncomputable def sectionMul (X : AlgebraicSpaces B S hS) (F M : Modules.{u, u} B S hS X.1 X.2)
    (s : M.sections) :
    F ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
      F).obj M :=
  (@Stacks.SheafOfModules.Invertible.tensorProductRightUnitor.{u, u + 1, u}
    (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
    (structurePresheaf B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
    _ _ F).inv ≫
  ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj F).map
    (M.unitHomEquiv.symm s)

/-- **Multiplication by a section is natural in the module.** -/
theorem sectionMul_naturality (X : AlgebraicSpaces B S hS) {F F' : Modules.{u, u} B S hS X.1 X.2}
    (a : F ⟶ F') (M : Modules.{u, u} B S hS X.1 X.2) (s : M.sections) :
    a ≫ sectionMul X F' M s =
      sectionMul X F M s ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
          a).app M :=
  @Stacks.SheafOfModules.Invertible.tensorProductRightUnitor_inv_comp_map_naturality
    (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
    (structurePresheaf B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
    _ _ _ _ _ a (M.unitHomEquiv.symm s)

/-- **The étale pullback of `𝓕 ⊗ φ` is invertible once that of `φ` is.**  The étale pullback is
restriction along the postcomposition functor of small étale sites, which commutes with the
tensor product of sheaves of modules naturally in both variables
(`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality_right`). -/
theorem isIso_etaleModulePullback_map_tensorObjMap {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    {G G' : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ G')
    (hφ : IsIso ((etaleModulePullback B S hS g hg).map φ)) :
    IsIso ((etaleModulePullback B S hS g hg).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
        F).map φ)) := by
  have h := Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality_right
    (J' := SmallEtale.topology B S hS Y.1) (J := SmallEtale.topology B S hS X.1)
    (structurePresheaf B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
    (smallEtalePostcomp B S hS g hg) F φ
  have hφ' : IsIso ((Stacks.SheafOfModules.TensorPower.whiskerRestriction
      (J' := SmallEtale.topology B S hS Y.1) (J := SmallEtale.topology B S hS X.1)
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      (smallEtalePostcomp B S hS g hg)).map φ) := hφ
  have h2 := (congrArg IsIso h).mpr
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
          (@Functor.map_isIso _ _ _ _ _ _ _ _
            (@Functor.map_isIso _ _ _ _ _ _ _ _ (IsIso.id _))) _)
        (@Functor.map_isIso _ _ _ _ _ _ _ _ hφ')))
  have h3 := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) h2
  have h4 := (congrArg IsIso (CategoryTheory.Functor.map_comp _ _ _)).mp h3
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
        (@Functor.map_isIso _ _ _ _ _ _ _ _ (IsIso.id _)) _)) h4

/-- **Multiplication by a section is invertible over the generating locus.**  For an étale
morphism `g : Y ⟶ X` whose image lies in the generating locus of the global section `s` of the
invertible `𝒪_X`-module `𝓜`, the étale pullback of multiplication by `s`, `𝓕 ⟶ 𝓕 ⊗ 𝓜`, is an
isomorphism for every `𝒪_X`-module `𝓕`. -/
theorem isIso_etaleModulePullback_map_sectionMul {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (F M : Modules.{u, u} B S hS X.1 X.2)
    (hM : IsInvertibleModule X M) (s : M.sections)
    (hrange : Set.range (pointsMap B S hS Y.1 g.hom) ⊆ sectionGeneratingLocus B S hS M s) :
    IsIso ((etaleModulePullback B S hS g hg).map (sectionMul X F M s)) := by
  have h₁ := isIso_modulePullback_map_of_range_subset_sectionGeneratingLocus g hg M hM s hrange
  have h₂ : IsIso ((etaleModulePullback B S hS g hg).map (M.unitHomEquiv.symm s)) :=
    (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS g hg) _).1 h₁
  have h₃ := isIso_etaleModulePullback_map_tensorObjMap g hg F _ h₂
  exact (congrArg IsIso ((etaleModulePullback B S hS g hg).map_comp _ _)).mpr
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_inv _)) h₃)

end AlgebraicGeometry.Space

end

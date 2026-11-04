module

public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESNatTrans
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# Tensoring a bounded complex flat over the base with a pullback

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `𝒢` be a bounded complex of
`𝒪_X`-modules each of which is flat over `Y`. For an `𝒪_Y`-module `ℱ` the functor
`ℱ ↦ f^*ℱ ⊗_{𝒪_X} 𝒢^n` is exact (`Stacks.SheafOfModules.pullbackTensorFunctor_exact`), so the
functor on complexes

`K ↦ Tot(f^*K ⊗_{𝒪_X} 𝒢)`

carries acyclic complexes to acyclic complexes and quasi-isomorphisms to quasi-isomorphisms.
It therefore descends to a functor `D(𝒪_Y) ⥤ D(𝒪_X)` commuting with the shift, with no
deriving: the functor on complexes computes it on every complex.

This is the functor through which the boundary maps of [Stacks, Tag 08IF] are compared: a
short exact sequence of complexes is carried to a short exact sequence of complexes, and the
connecting morphism of the distinguished triangle it gives in `D(𝒪_X)` is the image of the
connecting morphism in `D(𝒪_Y)`, by `DerivedCategory.map_triangleOfSESδ_comp_natTrans`.

## Main definitions

* `Stacks.Cohomology.RelativeExt.pullbackTensorBifunctor`: `(ℱ, ℳ) ↦ f^*ℱ ⊗_{𝒪_X} ℳ`.
* `Stacks.Cohomology.RelativeExt.pullbackTensorComplexFunctor`: `K ↦ Tot(f^*K ⊗_{𝒪_X} 𝒢)`.
* `Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor`: its descent to the derived
  categories, for `𝒢` bounded and flat over `Y`.

## Main results

* `Stacks.Cohomology.RelativeExt.kFlat_of_isBoundedFlatOver`: a bounded complex of modules
  flat over `Y` is K-flat for the bifunctor `(ℱ, ℳ) ↦ f^*ℱ ⊗ ℳ`.
* `Stacks.Cohomology.RelativeExt.map_triangleOfSESδ_pullbackTensorDerivedFunctor`: the
  descended functor carries the connecting morphism of a short exact sequence of complexes to
  the connecting morphism of its image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The bifunctor `(ℱ, ℳ) ↦ f^*ℱ ⊗_{𝒪_X} ℳ` from `𝒪_Y`-modules and `𝒪_X`-modules to
`𝒪_X`-modules. -/
def pullbackTensorBifunctor : SheafOfModules.{u} (structureSheafRing Y) ⥤
    SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  modulePullback f ⋙ Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf

/-- Fixing the `𝒪_X`-module `ℳ`, the bifunctor is `ℱ ↦ f^*ℱ ⊗ ℳ`, which is
`Stacks.SheafOfModules.pullbackTensorFunctor`. -/
theorem pullbackTensorBifunctor_flip_obj (M : SheafOfModules.{u} (structureSheafRing X)) :
    (pullbackTensorBifunctor f).flip.obj M = Stacks.SheafOfModules.pullbackTensorFunctor f M :=
  rfl

/-- The bifunctor `(ℱ, ℳ) ↦ f^*ℱ ⊗_{𝒪_X} ℳ` is additive in `ℱ`. -/
instance pullbackTensorBifunctor_additive : (pullbackTensorBifunctor f).Additive := by
  letI := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} X.sheaf
  exact @Functor.instAdditiveComp _ _ _ _ _ _ (modulePullback f) (modulePullback_additive f) _
    _ _ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) this

/-- For a fixed `𝒪_Y`-module `ℱ`, the functor `ℳ ↦ f^*ℱ ⊗_{𝒪_X} ℳ` is additive. -/
instance pullbackTensorBifunctor_obj_additive (N : SheafOfModules.{u} (structureSheafRing Y)) :
    ((pullbackTensorBifunctor f).obj N).Additive :=
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive X.sheaf _

/-- For complexes `K₁` of `𝒪_Y`-modules and `K₂` of `𝒪_X`-modules, the total complex of
`f^*K₁ ⊗_{𝒪_X} K₂` exists. -/
instance pullbackTensorBifunctor_hasMapBifunctor
    (K₁ : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (K₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂ (pullbackTensorBifunctor f) (ComplexShape.up ℤ) := by
  haveI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  haveI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  infer_instance

variable (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- The functor `K ↦ Tot(f^*K ⊗_{𝒪_X} 𝒢)` on complexes. -/
abbrev pullbackTensorComplexFunctor :
    CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  ((pullbackTensorBifunctor f).map₂CochainComplex).flip.obj G

/-- The functor `K ↦ Tot(f^*K ⊗_{𝒪_X} 𝒢)` on complexes is additive. -/
instance pullbackTensorComplexFunctor_additive : (pullbackTensorComplexFunctor f G).Additive :=
  Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_flip_obj_additive
    (pullbackTensorBifunctor f) G

/-- A complex of `𝒪_X`-modules is **bounded and flat over `Y`** when it is strictly bounded
on both sides and each of its terms is flat over `Y`. -/
structure IsBoundedFlatOver : Prop where
  /-- The complex is bounded. -/
  bounded : ∃ a b : ℤ, G.IsStrictlyGE a ∧ G.IsStrictlyLE b
  /-- Each term is flat over `Y`. -/
  isFlatOver : ∀ i : ℤ, IsFlatOver f (G.X i)

/-- An exact functor between abelian categories carries acyclic complexes to acyclic
complexes. -/
theorem acyclic_mapHomologicalComplex_of_exact {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E]
    [PreservesFiniteColimits E] (K : CochainComplex A ℤ) (hK : K.Acyclic) :
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro i
  have h := hK i
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map E

/-- **A bounded complex of modules flat over `Y` is K-flat for `(ℱ, ℳ) ↦ f^*ℱ ⊗ ℳ`**:
`Tot(f^*K ⊗ 𝒢)` is acyclic for every acyclic complex `K` of `𝒪_Y`-modules. Each term of `𝒢`
placed in its own degree is K-flat because `ℱ ↦ f^*ℱ ⊗ 𝒢^q` is exact, and a bounded complex is
K-flat as soon as its terms are. -/
theorem kFlat_of_isBoundedFlatOver (hG : IsBoundedFlatOver f G) :
    CochainComplex.KFlatBifunctor.KFlat (pullbackTensorBifunctor f) G := by
  obtain ⟨a, b, ha, hb⟩ := hG.bounded
  refine CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_isStrictlyGE
    (pullbackTensorBifunctor f) G b a (fun q => ?_)
  refine CochainComplex.KFlatBifunctor.kFlat_single_of_exact (pullbackTensorBifunctor f)
    (G.X q) q (fun K hK => ?_)
  have hex := Stacks.SheafOfModules.pullbackTensorFunctor_exact f (G.X q) (hG.isFlatOver q)
  have : PreservesFiniteLimits (Stacks.SheafOfModules.pullbackTensorFunctor f (G.X q)) := hex.1
  have : PreservesFiniteColimits (Stacks.SheafOfModules.pullbackTensorFunctor f (G.X q)) :=
    hex.2
  exact acyclic_mapHomologicalComplex_of_exact
    (Stacks.SheafOfModules.pullbackTensorFunctor f (G.X q)) K hK

variable {f G}

/-- `K ↦ Tot(f^*K ⊗ 𝒢)` preserves quasi-isomorphisms when `𝒢` is bounded and flat over
`Y`. -/
theorem quasiIso_pullbackTensorComplexFunctor_map (hG : IsBoundedFlatOver f G)
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (φ : K ⟶ L)
    (hφ : QuasiIso φ) : QuasiIso ((pullbackTensorComplexFunctor f G).map φ) :=
  CochainComplex.KFlatBifunctor.quasiIso_of_kFlat (pullbackTensorBifunctor f) G
    (kFlat_of_isBoundedFlatOver f G hG) φ hφ

/-- The functor on complexes followed by the localization inverts quasi-isomorphisms. -/
theorem pullbackTensorComplexFunctor_comp_Q_inverts (hG : IsBoundedFlatOver f G) :
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)).IsInvertedBy
        (pullbackTensorComplexFunctor f G ⋙ DerivedCategory.Q) := fun _ _ φ hφ => by
  have := quasiIso_pullbackTensorComplexFunctor_map hG φ hφ
  exact (inferInstance : IsIso (DerivedCategory.Q.map ((pullbackTensorComplexFunctor f G).map φ)))

/-- **`ℱ ↦ f^*ℱ ⊗ 𝒢` on derived categories**, for `𝒢` bounded and flat over `Y`: the descent of
`K ↦ Tot(f^*K ⊗ 𝒢)` along the localization functors. -/
def pullbackTensorDerivedFunctor (hG : IsBoundedFlatOver f G) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  Localization.lift (pullbackTensorComplexFunctor f G ⋙ DerivedCategory.Q)
    (pullbackTensorComplexFunctor_comp_Q_inverts hG) DerivedCategory.Q

/-- The descended functor `pullbackTensorDerivedFunctor` lifts `K ↦ Tot(f^*K ⊗ 𝒢)` followed by
the localization functor along `DerivedCategory.Q`. -/
instance pullbackTensorDerivedFunctor_lifting (hG : IsBoundedFlatOver f G) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ))
      (pullbackTensorComplexFunctor f G ⋙ DerivedCategory.Q)
      (pullbackTensorDerivedFunctor hG) := by
  unfold pullbackTensorDerivedFunctor
  infer_instance

/-- The descended functor commutes with the shift. -/
instance pullbackTensorDerivedFunctor_commShift (hG : IsBoundedFlatOver f G) :
    (pullbackTensorDerivedFunctor hG).CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)) ℤ (pullbackTensorComplexFunctor f G ⋙ DerivedCategory.Q)
    (pullbackTensorDerivedFunctor hG)

/-- The descended functor is computed by `K ↦ Tot(f^*K ⊗ 𝒢)` on every complex. -/
def pullbackTensorDerivedFunctorFactors (hG : IsBoundedFlatOver f G) :
    DerivedCategory.Q ⋙ pullbackTensorDerivedFunctor hG ≅
      pullbackTensorComplexFunctor f G ⋙ DerivedCategory.Q :=
  Localization.Lifting.iso DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)) (pullbackTensorComplexFunctor f G ⋙ DerivedCategory.Q)
    (pullbackTensorDerivedFunctor hG)

/-- The identification `pullbackTensorDerivedFunctorFactors` of the descended functor with
`K ↦ Tot(f^*K ⊗ 𝒢)` commutes with the shift. -/
instance pullbackTensorDerivedFunctorFactors_commShift (hG : IsBoundedFlatOver f G) :
    NatTrans.CommShift (pullbackTensorDerivedFunctorFactors hG).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)) ℤ (pullbackTensorComplexFunctor f G ⋙ DerivedCategory.Q)
    (pullbackTensorDerivedFunctor hG)

/-! ### Connecting morphisms -/

section Connecting

variable {S : ShortComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)}

/-- The transport of cochains through `K ↦ Tot(f^*K ⊗ 𝒢)` sends the zero cochain to the zero
cochain. -/
theorem ΨcochR_zero {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ}
    {n : ℤ} :
    Stacks.SheafOfModules.Tensor.Reduction.ΨcochR (pullbackTensorBifunctor f) G
      (0 : CochainComplex.HomComplex.Cochain K L n) = 0 := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a a' h
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq2 : p + q = a := hpq
  rw [Stacks.SheafOfModules.Tensor.Reduction.ΨcochR_v (pullbackTensorBifunctor f) G
    (0 : CochainComplex.HomComplex.Cochain K L n) a a' h p q hpq2]
  simp only [CochainComplex.HomComplex.Cochain.zero_v, CategoryTheory.Functor.map_zero,
    NatTrans.app_zero, zero_comp]
  exact (Limits.comp_zero).symm

/-- `K ↦ Tot(f^*K ⊗ 𝒢)` carries the canonical map from the mapping cone of `S.f` to `S.X₃` to
the canonical map from the mapping cone of its image, through the comparison of mapping cones
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR`. -/
theorem pullbackTensorComplexFunctor_map_descShortComplex :
    (pullbackTensorComplexFunctor f G).map (CochainComplex.mappingCone.descShortComplex S) =
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR
          (pullbackTensorBifunctor f) G S.f).hom ≫
        CochainComplex.mappingCone.descShortComplex
          (S.map (pullbackTensorComplexFunctor f G)) := by
  rw [← Iso.inv_comp_eq]
  have hcomp : (Stacks.SheafOfModules.Tensor.Reduction.ΨcochR (pullbackTensorBifunctor f) G
      (CochainComplex.mappingCone.inl S.f)).comp
        (CochainComplex.HomComplex.Cochain.ofHom
          ((pullbackTensorComplexFunctor f G).map
            (CochainComplex.mappingCone.descShortComplex S))) (add_zero _) = 0 := by
    rw [← Stacks.SheafOfModules.Tensor.Reduction.ΨcochR_ofHom,
      ← Stacks.SheafOfModules.Tensor.Reduction.ΨcochR_comp,
      CochainComplex.mappingCone.descShortComplex, CochainComplex.mappingCone.inl_desc,
      ΨcochR_zero]
  have hinr : (pullbackTensorComplexFunctor f G).map (CochainComplex.mappingCone.inr S.f) ≫
      (pullbackTensorComplexFunctor f G).map (CochainComplex.mappingCone.descShortComplex S) =
        (pullbackTensorComplexFunctor f G).map S.g := by
    rw [← CategoryTheory.Functor.map_comp, CochainComplex.mappingCone.inr_descShortComplex]
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  apply CochainComplex.mappingCone.ext_from ((pullbackTensorComplexFunctor f G).map S.f)
    (n + 1) n rfl
  · rw [HomologicalComplex.comp_f]
    simp only [Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR,
      CochainComplex.mappingCone.descShortComplex,
      CochainComplex.mappingCone.inl_v_desc_f_assoc, CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.zero_v]
    have := congrArg (fun z => z.v (n + 1) n (by omega)) hcomp
    simp only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.zero_v,
      CochainComplex.mappingCone.descShortComplex] at this
    rw [this]
    exact ((CochainComplex.mappingCone.inl_v_desc_f (S.map (pullbackTensorComplexFunctor f G)).f
      _ _ _ (n + 1) n _).trans (CochainComplex.HomComplex.Cochain.zero_v _ _ _)).symm
  · rw [HomologicalComplex.comp_f]
    simp only [Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR,
      CochainComplex.mappingCone.descShortComplex,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, CochainComplex.mappingCone.inr_f_desc_f]
    rw [CochainComplex.mappingCone.descShortComplex] at hinr
    refine (congrArg (fun φ => HomologicalComplex.Hom.f φ n) hinr).trans ?_
    exact (CochainComplex.mappingCone.inr_f_desc_f (S.map (pullbackTensorComplexFunctor f G)).f
      _ _ _ n).symm

/-- `K ↦ Tot(f^*K ⊗ 𝒢)` carries the third morphism of the mapping-cone triangle of `S.f` to
the third morphism of the mapping-cone triangle of its image, through the comparison of mapping
cones. -/
theorem pullbackTensorComplexFunctor_map_mappingCone_triangle_mor₃ :
    (pullbackTensorComplexFunctor f G).map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
        ((pullbackTensorComplexFunctor f G).commShiftIso (1 : ℤ)).hom.app S.X₁ =
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR
          (pullbackTensorBifunctor f) G S.f).hom ≫
        (CochainComplex.mappingCone.triangle
          ((pullbackTensorComplexFunctor f G).map S.f)).mor₃ := by
  have h := (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMapTriangleIsoR
    (pullbackTensorBifunctor f) G S.f).hom.comm₃
  have h₁ : (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMapTriangleIsoR
      (pullbackTensorBifunctor f) G S.f).hom.hom₁ = 𝟙 _ := rfl
  have h₃ : (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMapTriangleIsoR
      (pullbackTensorBifunctor f) G S.f).hom.hom₃ =
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIsoR
          (pullbackTensorBifunctor f) G S.f).hom := rfl
  rw [h₁, h₃] at h
  exact ((Category.comp_id _).symm.trans
    (congrArg _ ((shiftFunctor (CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
      (1 : ℤ)).map_id _).symm)).trans h

variable (hG : IsBoundedFlatOver f G)

/-- **The descended functor carries connecting morphisms to connecting morphisms.** For a
short exact sequence `S` of complexes of `𝒪_Y`-modules whose image under
`K ↦ Tot(f^*K ⊗ 𝒢)` is again short exact, the image of the connecting morphism of `S` in
`D(𝒪_Y)` is, through the identification of the descended functor with the functor on
complexes, the connecting morphism of the image of `S` in `D(𝒪_X)`. -/
theorem map_triangleOfSESδ_pullbackTensorDerivedFunctor (hS : S.ShortExact)
    (hΨS : (S.map (pullbackTensorComplexFunctor f G)).ShortExact) :
    (pullbackTensorDerivedFunctor hG).map (DerivedCategory.triangleOfSESδ hS) ≫
        ((pullbackTensorDerivedFunctor hG).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj S.X₁) ≫
        ((pullbackTensorDerivedFunctorFactors hG).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (pullbackTensorDerivedFunctorFactors hG).hom.app S.X₃ ≫
        DerivedCategory.triangleOfSESδ hΨS :=
  @DerivedCategory.map_triangleOfSESδ_comp_natTrans
    (SheafOfModules.{u} (structureSheafRing Y)) _ _
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y)))
    (SheafOfModules.{u} (structureSheafRing X)) _ _
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X)))
    (pullbackTensorComplexFunctor f G) _ _
    (pullbackTensorDerivedFunctor hG) _ (pullbackTensorDerivedFunctorFactors hG).hom _ S hS hΨS
    _ (pullbackTensorComplexFunctor_map_mappingCone_triangle_mor₃ (f := f) (G := G) (S := S))
    (pullbackTensorComplexFunctor_map_descShortComplex (f := f) (G := G) (S := S))

end Connecting

end Stacks.Cohomology.RelativeExt

end

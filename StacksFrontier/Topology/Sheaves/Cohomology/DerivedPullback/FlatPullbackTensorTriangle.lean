module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatPullbackTensorComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESNatTrans
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Shift.Localization
public import StacksFrontier.Homology.DerivedTensor.KFlatDescent

/-!
# The derived functor of `M ↦ Tot(f^*M ⊗ 𝒢)` and distinguished triangles

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `𝒢` a bounded complex of
`𝒪_X`-modules with terms flat over `Y`.  The functor `Ψ : M ↦ Tot(f^*M ⊗_{𝒪_X} 𝒢)` on complexes
preserves quasi-isomorphisms
(`Stacks.Cohomology.FlatPullbackTensor.quasiIso_complexFunctor_map`), so it descends to a functor

`R : D(𝒪_Y) ⥤ D(𝒪_X)`

with `Q ⋙ R ≅ Ψ ⋙ Q`.  The descent commutes with the shift, compatibly with that isomorphism,
and this file proves that it carries the distinguished triangle of a short exact sequence of
complexes to the distinguished triangle of its image under `Ψ`, with the components of the
isomorphism `Q ⋙ R ≅ Ψ ⋙ Q` as the three components.

## Main definitions

* `Stacks.Cohomology.FlatPullbackTensor.localizerMorphism`: `Ψ` as a morphism of localizers.
* `Stacks.Cohomology.FlatPullbackTensor.derivedFunctor`: the descent `R`.
* `Stacks.Cohomology.FlatPullbackTensor.derivedFunctorFactors`: `Q ⋙ R ≅ Ψ ⋙ Q`.
* `Stacks.Cohomology.FlatPullbackTensor.mapTriangleOfSESIso`: the isomorphism of triangles
  `R(triangle of S) ≅ triangle of Ψ(S)` for a short exact sequence `S` of complexes whose image
  is short exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
  Pretriangulated

namespace Stacks.Cohomology.FlatPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (G : CochainComplex (Modules X) ℤ)

/-- The functor `M ↦ Tot(f^*M ⊗ 𝒢)` on complexes of `𝒪_Y`-modules is additive. -/
instance complexFunctor_additive : (complexFunctor f G).Additive :=
  Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_flip_obj_additive
    (bifunctor f) G

/-- **`M ↦ Tot(f^*M ⊗ 𝒢)` as a morphism of localizers**, from the quasi-isomorphisms of complexes
of `𝒪_Y`-modules to those of complexes of `𝒪_X`-modules. -/
def localizerMorphism (hflat : ∀ q : ℤ, AlgebraicGeometry.IsFlatOver f (G.X q))
    (hb : ∃ a b : ℤ, G.IsStrictlyGE a ∧ G.IsStrictlyLE b) :
    LocalizerMorphism
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso (Modules X) (ComplexShape.up ℤ)) where
  functor := complexFunctor f G
  map _ _ φ hφ := by
    obtain ⟨a, b, ha, hb⟩ := hb
    exact quasiIso_complexFunctor_map f G hflat a b φ hφ

variable (hflat : ∀ q : ℤ, AlgebraicGeometry.IsFlatOver f (G.X q))
  (hb : ∃ a b : ℤ, G.IsStrictlyGE a ∧ G.IsStrictlyLE b)

/-- The functor underlying `localizerMorphism` commutes with the shift on cochain complexes. -/
instance localizerMorphism_functor_commShift :
    (localizerMorphism f G hflat hb).functor.CommShift ℤ :=
  inferInstanceAs ((complexFunctor f G).CommShift ℤ)

/-- **The descent `R : D(𝒪_Y) ⥤ D(𝒪_X)` of `M ↦ Tot(f^*M ⊗ 𝒢)`**, Mathlib's
`CategoryTheory.LocalizerMorphism.localizedFunctor`, with its commutation with the shift. -/
def derivedFunctor :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤ DerivedCategory (Modules X) :=
  (localizerMorphism f G hflat hb).localizedFunctor DerivedCategory.Q DerivedCategory.Q

/-- `Ψ ⋙ Q ≅ Q ⋙ R`. -/
def derivedFunctorFactors :
    complexFunctor f G ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ derivedFunctor f G hflat hb :=
  CatCommSq.iso (localizerMorphism f G hflat hb).functor DerivedCategory.Q DerivedCategory.Q
    ((localizerMorphism f G hflat hb).localizedFunctor DerivedCategory.Q DerivedCategory.Q)

/-- The derived functor `R : D(𝒪_Y) ⥤ D(𝒪_X)` commutes with the shift. -/
instance derivedFunctor_commShift : (derivedFunctor f G hflat hb).CommShift ℤ :=
  (localizerMorphism f G hflat hb).commShift ℤ DerivedCategory.Q DerivedCategory.Q _
    (derivedFunctorFactors f G hflat hb)

/-- The isomorphism `Ψ ⋙ Q ≅ Q ⋙ R` is compatible with the commutations of `Ψ` and `R` with
the shift. -/
instance natTransCommShift_derivedFunctorFactors_hom :
    NatTrans.CommShift (derivedFunctorFactors f G hflat hb).hom ℤ :=
  LocalizerMorphism.natTransCommShift_hom (M := ℤ) (Φ := localizerMorphism f G hflat hb)
    (L₁ := DerivedCategory.Q) (L₂ := DerivedCategory.Q) (G := derivedFunctor f G hflat hb)
    (e := derivedFunctorFactors f G hflat hb)

section Generic

open Stacks.SheafOfModules.Tensor.Reduction
open Stacks.DerivedTensor (totRight)

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex B (ComplexShape.up ℤ)), K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (G : HomologicalComplex B (ComplexShape.up ℤ))

/-- The transport of the zero cochain is zero. -/
theorem ΨcochR_zero' {K L : CochainComplex A ℤ} {n : ℤ} :
    ΨcochR F G (0 : CochainComplex.HomComplex.Cochain K L n) = 0 := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a a' h
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [ΨcochR_v F G _ a a' h p q hpq]
  simp only [CochainComplex.HomComplex.Cochain.zero_v, Functor.map_zero, NatTrans.app_zero,
    Limits.zero_comp]
  exact Limits.comp_zero.symm

/-- The projection of a mapping cone onto the third term of a short complex kills the first
summand. -/
theorem inl_v_descShortComplex_f {C : Type*} [Category* C] [Abelian C]
    (S' : ShortComplex (CochainComplex C ℤ)) (p q : ℤ) (h : p + (-1) = q) :
    (CochainComplex.mappingCone.inl S'.f).v p q h ≫
      (CochainComplex.mappingCone.descShortComplex S').f q = 0 := by
  simp [CochainComplex.mappingCone.descShortComplex]

/-- The functor `K ↦ Tot(F(K, 𝒢))` on cochain complexes over `A` is additive. -/
instance totRight_additive : (totRight F G).Additive :=
  map₂HomologicalComplex_flip_obj_additive F G

/-- The functor `K ↦ Tot(F(K, 𝒢))` on cochain complexes over `A` preserves zero morphisms. -/
instance totRight_preservesZeroMorphisms : (totRight F G).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The cone comparison `Tot(F(cone φ, 𝒢)) ≅ cone(Tot(F(φ, 𝒢)))`, with the biproducts of the
mapping cones those of the abelian categories involved. -/
def coneIso {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (totRight F G).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone ((totRight F G).map φ) :=
  bifunctorMappingConeIsoR F G φ

/-- **The cone comparison `Tot(F(cone φ, 𝒢)) ≅ cone(Tot(F(φ, 𝒢)))` is compatible with the
projections onto the third term** of a short complex. -/
theorem map_descShortComplex_eq (S : ShortComplex (CochainComplex A ℤ)) :
    (totRight F G).map (CochainComplex.mappingCone.descShortComplex S) =
      (coneIso F G S.f).hom ≫
        CochainComplex.mappingCone.descShortComplex (S.map (totRight F G)) := by
  have hinl : (CochainComplex.mappingCone.inl S.f).comp
      (CochainComplex.HomComplex.Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S))
        (add_zero _) = 0 :=
    CochainComplex.mappingCone.inl_desc _ _ _ _
  rw [← Iso.inv_comp_eq]
  unfold coneIso
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.mappingCone.ext_from ((totRight F G).map S.f) (n + 1) n rfl
  · rw [HomologicalComplex.comp_f, ← Category.assoc]
    unfold bifunctorMappingConeIsoR
    rw [CochainComplex.mappingCone.inl_v_desc_f]
    have e1 : ((totRight F G).map (CochainComplex.mappingCone.descShortComplex S)).f n =
        (ΨcochR F G (CochainComplex.HomComplex.Cochain.ofHom
            (CochainComplex.mappingCone.descShortComplex S))).v n n (add_zero n) := by
      rw [ΨcochR_ofHom, CochainComplex.HomComplex.Cochain.ofHom_v]
    rw [e1, ← CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero (-1)) (n + 1) n n
        (by omega) (by omega), ← ΨcochR_comp, hinl, ΨcochR_zero',
      CochainComplex.HomComplex.Cochain.zero_v]
    exact (inl_v_descShortComplex_f (S.map (totRight F G)) (n + 1) n (by omega)).symm
  · rw [HomologicalComplex.comp_f, ← Category.assoc]
    unfold bifunctorMappingConeIsoR
    rw [CochainComplex.mappingCone.inr_f_desc_f, ← HomologicalComplex.comp_f,
      ← Functor.map_comp, CochainComplex.mappingCone.inr_descShortComplex,
      ← HomologicalComplex.comp_f]
    exact (congrArg (fun φ => φ.f n)
      (CochainComplex.mappingCone.inr_descShortComplex (S.map (totRight F G)))).symm

/-- **The cone comparison is compatible with the third morphisms of the cone triangles**, for
the sign-free commutation of `Tot(F(-, 𝒢))` with the shift. -/
theorem map_mappingConeTriangle_mor₃ {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (totRight F G).map (CochainComplex.mappingCone.triangle φ).mor₃ ≫
        ((totRight F G).commShiftIso (1 : ℤ)).hom.app K =
      (coneIso F G φ).hom ≫
        (CochainComplex.mappingCone.triangle ((totRight F G).map φ)).mor₃ := by
  unfold coneIso
  have h := (bifunctorMapTriangleIsoR F G φ).hom.comm₃
  have h1 : (bifunctorMapTriangleIsoR F G φ).hom.hom₁ = 𝟙 _ := rfl
  have h3 : (bifunctorMapTriangleIsoR F G φ).hom.hom₃ = (bifunctorMappingConeIsoR F G φ).hom := rfl
  rw [h1, h3] at h
  refine Eq.trans ?_ h
  exact (Category.comp_id _).symm.trans (congrArg _
    (CategoryTheory.Functor.map_id (shiftFunctor (HomologicalComplex D (ComplexShape.up ℤ)) (1 : ℤ))
      _).symm)

end Generic

end Stacks.Cohomology.FlatPullbackTensor

end

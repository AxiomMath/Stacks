module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Abelian
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Resolution

/-!
# The relative Čech complex of a sheaf of modules

This file builds the relative Čech complex of a sheaf of `𝒪_𝒳`-modules from the inverse and
direct images of modules along the projections of the relative Čech nerve, identifies its
underlying complex of abelian sheaves with the sheafified relative Čech complex of the
underlying abelian sheaf, deduces that its augmentation is a resolution (**Stacks 06XE** for
sheaves of modules), and shows that its terms are injective when the sheaf is.

## References

* [Stacks Project, Tag 06XE](https://stacks.math.columbia.edu/tag/06XE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.RelativeCech

section Modules

/-! ### The relative Čech complex of a sheaf of modules -/

section ModuleCech

open scoped Simplicial

universe u v₁ v₂ w₁ w₂ t

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type v₁} [Category.{w₁} 𝒰] {𝒳 : Type v₂} [Category.{w₂} 𝒳]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (f : 𝒰 ⥤ 𝒳)
  (τ : AlgebraicGeometry.SiteKind)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hf : p.IsFibredOneMorphism q f)

include hp hq hf in
/-- Each projection of the relative Čech nerve is continuous for the inherited topologies. -/
private lemma tupleProjection_isContinuous (n : ℕ) :
    (Tuple.projection q f n).IsContinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) :=
  (tuple_projection_continuous_cocontinuous q f (hf.comp_eq.symm ▸ hp) hq
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ) n).1

include hp hq hf in
/-- Each projection of the relative Čech nerve is cocontinuous for the inherited topologies. -/
private lemma tupleProjection_isCocontinuous (n : ℕ) :
    (Tuple.projection q f n).IsCocontinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) :=
  (tuple_projection_continuous_cocontinuous q f (hf.comp_eq.symm ▸ hp) hq
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ) n).2

include hp hf in
/-- The degree `n` term `f_{n,*} f_n^{-1}` of the relative Čech complex of a sheaf of
modules. -/
private noncomputable def cechModuleTerm (n : ℕ) :
    SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ) ⥤
      SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ) :=
  letI := tupleProjection_isContinuous B S hS p q f τ hp hq hf n
  letI := tupleProjection_isCocontinuous B S hS p q f τ hp hq hf n
  SheafOfModules.pushforward₀.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ) ⋙
    SheafOfModules.directImage.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ)

include hp hf in
/-- The map of Čech terms induced by a simplicial reindexing. -/
private noncomputable def cechModuleReindex {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf m ⟶
      cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n :=
  letI := tupleProjection_isContinuous B S hS p q f τ hp hq hf m
  letI := tupleProjection_isCocontinuous B S hS p q f τ hp hq hf m
  letI := tupleProjection_isContinuous B S hS p q f τ hp hq hf n
  letI := tupleProjection_isCocontinuous B S hS p q f τ hp hq hf n
  letI : (Tuple.reindex q f φ.toOrderHom ⋙ Tuple.projection q f m).IsContinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) :=
    tupleProjection_isContinuous B S hS p q f τ hp hq hf n
  letI : (Tuple.reindex q f φ.toOrderHom ⋙ Tuple.projection q f m).IsCocontinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) :=
    tupleProjection_isCocontinuous B S hS p q f τ hp hq hf n
  SheafOfModules.directImageReindex.{u, max v₁ v₂ w₂ t}
    (Tuple.reindex q f φ.toOrderHom) (Tuple.projection q f m)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f m ⋙ q) τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    (moduleRingSheaf B S hS q hq τ)

include hp hf in
/-- The cosimplicial object `n ↦ f_{n,*} f_n^{-1}` of endofunctors of sheaves of modules
underlying the relative Čech complex. -/
private noncomputable def cechModuleCosimplicial :
    CosimplicialObject (SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ) ⥤
      SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ)) where
  obj n := cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n.len
  map φ := cechModuleReindex.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf φ
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

include hp hf in
/-- The relative Čech complex `f_{0,*}f_0^{-1}𝓕 ⟶ f_{1,*}f_1^{-1}𝓕 ⟶ ⋯` of a sheaf of
modules, functorially in the sheaf: the alternating-coface complex of the cosimplicial object
`Stacks.RelativeCech.cechModuleCosimplicial`. -/
private noncomputable def cechModuleComplexFunctor :
    SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ) ⥤
      CochainComplex (SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ)) ℕ :=
  (cechModuleCosimplicial.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).flip ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _

include hp hf in
/-- Each Čech term is additive: it is the composite of restriction of scalars with a right
adjoint. -/
private lemma cechModuleTerm_additive (n : ℕ) :
    (cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n).Additive where
  map_add := by intros; ext; rfl

include hp hf in
/-- The relative Čech complex of sheaves of modules is an additive functor. -/
private lemma cechModuleComplexFunctor_additive :
    (cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).Additive where
  map_add := by
    intro F G φ ψ
    apply HomologicalComplex.Hom.ext
    funext n
    exact (cechModuleTerm_additive.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n).map_add

include hp hf in
/-- The augmentation of a sheaf of modules into degree `0` of its relative Čech complex: the
unit of the adjunction between the inverse and direct images along the degree-`0` projection
of the Čech nerve. -/
private noncomputable def cechModuleAugmentation :
    𝟭 (SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ)) ⟶
      cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 0 where
  app 𝓕 := ⟨(PresheafOfModules.directImageUnit.{u, max v₁ v₂ w₂ t} (Tuple.projection q f 0)
    (moduleRingSheaf B S hS q hq τ).obj).app 𝓕.val⟩
  naturality _ _ ψ := SheafOfModules.hom_ext
    ((PresheafOfModules.directImageUnit.{u, max v₁ v₂ w₂ t} (Tuple.projection q f 0)
      (moduleRingSheaf B S hS q hq τ).obj).naturality ψ.val)

/-- The differential of an alternating-coface complex is the alternating sum of the coface
maps. -/
private lemma alternatingCofaceMapComplex_obj_d {C : Type*} [Category C] [Preadditive C]
    (X : CosimplicialObject C) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]

/-- A morphism into degree `0` of a cosimplicial object which has the same composite with the
two coface maps out of degree `0` lands in the kernel of the first differential of the
alternating-coface complex. -/
private lemma comp_alternatingCofaceMapComplex_d_zero {C : Type*} [Category C] [Preadditive C]
    (X : CosimplicialObject C) {A : C} (a : A ⟶ X.obj ⦋0⦌)
    (h : a ≫ X.δ 0 = a ≫ X.δ 1) :
    a ≫ ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d 0 (0 + 1) = 0 := by
  rw [alternatingCofaceMapComplex_obj_d X 0]
  change a ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • X.δ i) = 0
  rw [Fin.sum_univ_two, Preadditive.comp_add, Preadditive.comp_zsmul,
    Preadditive.comp_zsmul, h]
  simp

include hp hf in
/-- The augmentation followed by a coface map does not depend on the coface: both send a
section to the family of its restrictions. -/
private lemma cechModuleAugmentation_comp_delta
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) (i j : Fin 2) :
    (cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).app 𝓕 ≫
        (cechModuleReindex.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf
          (SimplexCategory.δ i)).app 𝓕 =
      (cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).app 𝓕 ≫
        (cechModuleReindex.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf
          (SimplexCategory.δ j)).app 𝓕 := by
  ext; rfl

include hp hf in
/-- The augmentation lands in the kernel of the first differential, so the augmented Čech
complex is a complex. -/
private lemma cechModuleAugmentation_comp_d
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    (cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).app 𝓕 ≫
        ((cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).obj 𝓕).d
          0 1 = 0 := by
  change (cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).app 𝓕 ≫
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
        ((cechModuleCosimplicial.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf).flip.obj 𝓕)).d 0 (0 + 1) = 0
  exact comp_alternatingCofaceMapComplex_d_zero
    ((cechModuleCosimplicial.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).flip.obj 𝓕) _
    (cechModuleAugmentation_comp_delta.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0 1)

/-! ### Comparison with the relative Čech complex of abelian sheaves -/

/-- Two composites into a right Kan extension agree as soon as their factorisations through
the counit do. -/
private lemma hom_ext_of_isRightKanExtension_comp {C D H : Type*} [Category C] [Category D]
    [Category H] {L : C ⥤ D} {F : C ⥤ H} (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] {G G₁ G₂ : D ⥤ H}
    (a : G ⟶ G₁) (θ₁ : G₁ ⟶ F') (b : G ⟶ G₂) (θ₂ : G₂ ⟶ F')
    (c₁ : L ⋙ G₁ ⟶ F) (c₂ : L ⋙ G₂ ⟶ F)
    (h₁ : Functor.whiskerLeft L θ₁ ≫ α = c₁)
    (h₂ : Functor.whiskerLeft L θ₂ ≫ α = c₂)
    (h : Functor.whiskerLeft L a ≫ c₁ = Functor.whiskerLeft L b ≫ c₂) :
    a ≫ θ₁ = b ≫ θ₂ := by
  refine Functor.hom_ext_of_isRightKanExtension _ α _ _ ?_
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, Category.assoc, Category.assoc,
    h₁, h₂]
  exact h

/-- The `n`-th Čech term of a presheaf is a right Kan extension along the `n`-th projection,
with the counit of the right Kan extension. -/
private lemma isRightKanExtension_term_ranCounit
    (P : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max v₁ v₂ w₂ t}) (n : ℕ) :
    (term.{w₁, w₂, _, v₁, v₂, _, t} q f P n).IsRightKanExtension
      ((Tuple.projection q f n).op.ranCounit.app ((Tuple.projection q f n).op ⋙ P)) :=
  inferInstanceAs (((Tuple.projection q f n).op.ran.obj
    ((Tuple.projection q f n).op ⋙ P)).IsRightKanExtension _)

include hp hf in
/-- The underlying presheaf of abelian groups of the degree `n` term of the relative Čech
complex of a sheaf of modules is the degree `n` term of the relative Čech complex of abelian
presheaves: both are right Kan extensions, along the `n`-th projection of the Čech nerve, of
the restriction of the underlying presheaf of `𝓕`. -/
private noncomputable def cechModulePresheafIso
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) (n : ℕ) :
    ((cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n).obj 𝓕).val.presheaf ≅
      term.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf n :=
  PresheafOfModules.directImageRanIso.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
    (moduleRingSheaf B S hS q hq τ).obj
    ((PresheafOfModules.pushforward₀.{max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (moduleRingSheaf B S hS q hq τ).obj).obj 𝓕.val)

include hp hf in
/-- The comparison of Čech terms factors the counit of the direct image through the counit of
the right Kan extension. -/
private lemma cechModulePresheafIso_fac
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) (n : ℕ) :
    Functor.whiskerLeft (Tuple.projection q f n).op
        (cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n).hom ≫
      (Tuple.projection q f n).op.ranCounit.app
        ((Tuple.projection q f n).op ⋙ 𝓕.val.presheaf) =
      PresheafOfModules.directImageCounit.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
        (moduleRingSheaf B S hS q hq τ).obj
        ((PresheafOfModules.pushforward₀.{max v₁ v₂ w₂ t} (Tuple.projection q f n)
          (moduleRingSheaf B S hS q hq τ).obj).obj 𝓕.val) :=
  PresheafOfModules.directImageRanIso_fac.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
    (moduleRingSheaf B S hS q hq τ).obj
    ((PresheafOfModules.pushforward₀.{max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (moduleRingSheaf B S hS q hq τ).obj).obj 𝓕.val)

include hp hf in
/-- The comparison of Čech terms is compatible with the simplicial reindexing maps: both
composites are the morphism into a right Kan extension determined by the same factorisation
through its counit. -/
private lemma cechModulePresheafIso_reindex
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ))
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (PresheafOfModules.toPresheaf
          (moduleRingSheaf B S hS q hq τ).obj).map
        ((cechModuleReindex.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf φ).app 𝓕).val ≫
        (cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n).hom =
      (cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 m).hom ≫
        reindexMap.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf φ := by
  have := isRightKanExtension_term_ranCounit.{u, v₁, v₂, w₁, w₂, t} B S hS q f 𝓕.val.presheaf n
  refine hom_ext_of_isRightKanExtension_comp
    (term.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf n)
    ((Tuple.projection q f n).op.ranCounit.app
      ((Tuple.projection q f n).op ⋙ 𝓕.val.presheaf)) _ _ _ _ _ _
    (cechModulePresheafIso_fac.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n)
    (reindexMap_fac.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf φ) ?_
  exact (PresheafOfModules.directImageReindex_counit.{u, max v₁ v₂ w₂ t}
      (Tuple.reindex q f φ.toOrderHom) (Tuple.projection q f m)
      (moduleRingSheaf B S hS q hq τ).obj 𝓕.val).trans
    (congrArg (Functor.whiskerLeft (Tuple.reindex q f φ.toOrderHom).op)
      (cechModulePresheafIso_fac.{u, v₁, v₂, w₁, w₂, t}
        B S hS p q f τ hp hq hf 𝓕 m)).symm

/-- An additive functor commutes with the differential of an alternating-coface complex. -/
private lemma map_alternatingCofaceMapComplex_d {C D : Type*} [Category C] [Preadditive C]
    [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive] (X : CosimplicialObject C) (i : ℕ) :
    G.map (((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d i (i + 1)) =
      ((AlgebraicTopology.alternatingCofaceMapComplex D).obj (X ⋙ G)).d i (i + 1) := by
  rw [alternatingCofaceMapComplex_obj_d, alternatingCofaceMapComplex_obj_d]
  exact (G.map_sum (fun k : Fin (i + 2) => (-1 : ℤ) ^ (k : ℕ) • X.δ k) Finset.univ).trans
    (Finset.sum_congr rfl fun k _ => G.map_zsmul)

/-- An additive functor commutes with the alternating-coface complex of a cosimplicial
object. -/
private noncomputable def mapAlternatingCofaceMapComplexIso {C D : Type*} [Category C]
    [Preadditive C] [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : CosimplicialObject C) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex D).obj (X ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    obtain rfl : i + 1 = j := hij
    exact (Category.id_comp _).trans
      ((map_alternatingCofaceMapComplex_d G X i).symm.trans (Category.comp_id _).symm))

include hp hf in
/-- The degree `n` term of the relative Čech complex of abelian presheaves attached to the
underlying presheaf of a sheaf of modules is a sheaf. -/
private lemma isSheaf_cechTerm
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) (n : ℕ) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (term.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf n) :=
  (Presheaf.isSheaf_of_iso_iff
      (cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n)).1
    ((cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n).obj 𝓕).isSheaf

include hp hf in
/-- The degree `n` term of the relative Čech complex of abelian presheaves, as a sheaf. -/
private noncomputable def cechSheafTerm
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) (n : ℕ) :
    Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max v₁ v₂ w₂ t} :=
  ⟨term.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf n,
    isSheaf_cechTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n⟩

include hp hf in
/-- The underlying abelian sheaf of the degree `n` Čech term of a sheaf of modules is the
degree `n` Čech term of its underlying abelian sheaf. -/
private noncomputable def cechModuleSheafIso
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) (n : ℕ) :
    (SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ)).obj
        ((cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n).obj 𝓕) ≅
      cechSheafTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n where
  hom := ⟨(cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n).hom⟩
  inv := ⟨(cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n).inv⟩
  hom_inv_id := Sheaf.hom_ext
    (cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n).hom_inv_id
  inv_hom_id := Sheaf.hom_ext
    (cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n).inv_hom_id

include hp hf in
/-- The cosimplicial object of abelian sheaves whose terms are the Čech terms of the
underlying abelian sheaf of `𝓕`. -/
private noncomputable def cechSheafTermCosimplicial
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    CosimplicialObject (Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max v₁ v₂ w₂ t}) where
  obj n := cechSheafTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n.len
  map φ := ⟨reindexMap.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf φ⟩
  map_id n := Sheaf.hom_ext
    ((cosimplicial.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf).map_id n)
  map_comp φ ψ := Sheaf.hom_ext
    ((cosimplicial.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf).map_comp φ ψ)

variable
  [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max v₁ v₂ w₂ t}]
  [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
    AddCommGrpCat.{max v₁ v₂ w₂ t}]

include hp hf in
/-- The cosimplicial object of abelian sheaves underlying the relative Čech complex of a sheaf
of modules is the sheafified cosimplicial object of abelian presheaves. -/
private noncomputable def cechModuleCosimplicialSheafIso
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    (cechModuleCosimplicial.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).flip.obj 𝓕 ⋙
        SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ) ≅
      cosimplicial.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf ⋙
        presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
          AddCommGrpCat.{max v₁ v₂ w₂ t} :=
  (NatIso.ofComponents
      (fun n => cechModuleSheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 n.len)
      (fun φ => Sheaf.hom_ext
        (cechModulePresheafIso_reindex.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf 𝓕 φ)) :
      (cechModuleCosimplicial.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).flip.obj 𝓕 ⋙
          SheafOfModules.toSheaf
            (moduleRingSheaf B S hS q hq τ) ≅
        cechSheafTermCosimplicial.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕) ≪≫
    Functor.isoWhiskerLeft
      (cechSheafTermCosimplicial.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕)
      (sheafificationNatIso (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
        AddCommGrpCat.{max v₁ v₂ w₂ t})

include hp hf in
/-- The relative Čech complex of a sheaf of modules has, as underlying complex of abelian
sheaves, the relative Čech complex of the underlying abelian sheaf. -/
private noncomputable def cechModuleComplexIso
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    ((SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).obj 𝓕) ≅
      (cechSheafComplexFunctor.{u, w₁, w₂, v₁, v₂, t} B S hS q f τ).obj
        ((SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ)).obj 𝓕) :=
  mapAlternatingCofaceMapComplexIso
      (SheafOfModules.toSheaf
        (moduleRingSheaf B S hS q hq τ)) _ ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (cechModuleCosimplicialSheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕) ≪≫
    (mapAlternatingCofaceMapComplexIso
      (presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
        AddCommGrpCat.{max v₁ v₂ w₂ t})
      (cosimplicial.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf)).symm


include hp hf in
/-- The augmentation of a sheaf of modules into its relative Čech complex, as a morphism from
the complex concentrated in degree `0`, naturally in the sheaf. -/
private noncomputable def cechModuleAugmentationNatTrans :
    CochainComplex.single₀ (SheafOfModules.{max v₁ v₂ w₂ t}
        (moduleRingSheaf B S hS q hq τ)) ⟶
      cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf where
  app 𝓕 := (CochainComplex.fromSingle₀Equiv
    ((cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).obj 𝓕) 𝓕).symm
    ⟨(cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).app 𝓕,
      cechModuleAugmentation_comp_d.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕⟩
  naturality 𝓕 𝓖 ψ := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero =>
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        CochainComplex.single₀_map_f_zero]
      exact (cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
        B S hS p q f τ hp hq hf).naturality ψ
    | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 𝓕 (n + 1)
        (by omega)).eq_of_src _ _

/-! ### The augmented relative Čech complex of a sheaf of modules is a resolution -/

omit [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
    AddCommGrpCat.{max v₁ v₂ w₂ t}] in
include hp hf in
/-- In degree `0` the comparison of Čech complexes is the comparison of Čech terms followed by
the identification of a sheaf with its own sheafification. -/
private lemma cechModuleComplexIso_hom_f_zero
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    (cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕).hom.f 0 =
      (cechModuleSheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0).hom ≫
        (sheafificationIso
          (cechSheafTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0)).hom := by
  rfl

omit [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max v₁ v₂ w₂ t}]
  [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
    AddCommGrpCat.{max v₁ v₂ w₂ t}] in
include hp hf in
/-- The augmentation of a sheaf of modules into degree `0` of its relative Čech complex is,
on underlying presheaves, the unit of the right-Kan-extension adjunction. -/
private lemma cechModuleAugmentation_presheaf
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    (PresheafOfModules.toPresheaf
          (moduleRingSheaf B S hS q hq τ).obj).map
        ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf).app 𝓕).val ≫
        (cechModulePresheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0).hom =
      ((Tuple.projection q f 0).op.ranAdjunction
        AddCommGrpCat.{max v₁ v₂ w₂ t}).unit.app 𝓕.val.presheaf := by
  have := isRightKanExtension_term_ranCounit.{u, v₁, v₂, w₁, w₂, t} B S hS q f 𝓕.val.presheaf 0
  refine (hom_ext_of_isRightKanExtension_comp
    (term.{w₁, w₂, _, v₁, v₂, _, t} q f 𝓕.val.presheaf 0)
    ((Tuple.projection q f 0).op.ranCounit.app
      ((Tuple.projection q f 0).op ⋙ 𝓕.val.presheaf)) _ _ _ (𝟙 _) _
    ((Tuple.projection q f 0).op.ranCounit.app
      ((Tuple.projection q f 0).op ⋙ 𝓕.val.presheaf))
    (cechModulePresheafIso_fac.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0)
    (by simp) ?_).trans (Category.comp_id _)
  exact (PresheafOfModules.directImageUnit_directImageCounit.{u, max v₁ v₂ w₂ t}
      (Tuple.projection q f 0)
      (moduleRingSheaf B S hS q hq τ).obj 𝓕.val).trans
    (Functor.ranCounit_app_whiskerLeft_ranAdjunction_unit_app _ _).symm

omit [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
    AddCommGrpCat.{max v₁ v₂ w₂ t}] in
include hp hf in
/-- The augmentation of a sheaf of modules is, on underlying abelian sheaves, the augmentation
of the relative Čech complex of abelian sheaves. -/
private lemma toSheaf_cechModuleAugmentation
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    (SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ)).map
        ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf).app 𝓕) ≫
        (cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕).hom.f 0 =
      sheafAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS q f τ
        ((SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ)).obj 𝓕) := by
  have hsq : (SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ)).map
        ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf).app 𝓕) ≫
        (cechModuleSheafIso.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0).hom =
      (⟨((Tuple.projection q f 0).op.ranAdjunction
          AddCommGrpCat.{max v₁ v₂ w₂ t}).unit.app 𝓕.val.presheaf⟩ :
        (SheafOfModules.toSheaf
            (moduleRingSheaf B S hS q hq τ)).obj 𝓕 ⟶
          cechSheafTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0) :=
    Sheaf.hom_ext (cechModuleAugmentation_presheaf.{u, v₁, v₂, w₁, w₂, t}
      B S hS p q f τ hp hq hf 𝓕)
  have hnat := (sheafificationNatIso
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max v₁ v₂ w₂ t}).hom.naturality
    (show (SheafOfModules.toSheaf
          (moduleRingSheaf B S hS q hq τ)).obj 𝓕 ⟶
        cechSheafTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0 from
      ⟨((Tuple.projection q f 0).op.ranAdjunction
        AddCommGrpCat.{max v₁ v₂ w₂ t}).unit.app 𝓕.val.presheaf⟩)
  rw [cechModuleComplexIso_hom_f_zero.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (sheafificationIso
      (cechSheafTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕 0)).hom) hsq)).trans hnat

variable (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
  Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
    ∀ ⦃y : 𝒳⦄ (k : y ⟶ x), R k → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))

include hp hq hf hcover in
/-- **Stacks 06XE for sheaves of modules.** The augmentation of a sheaf of modules into its
relative Čech complex is a quasi-isomorphism: on underlying abelian sheaves it is the
augmentation of the relative Čech complex of abelian sheaves, which is a resolution, and
forgetting the module structure is exact and faithful. -/
private lemma quasiIso_cechModuleAugmentationNatTrans_app
    (𝓕 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ)) :
    QuasiIso ((cechModuleAugmentationNatTrans.{u, v₁, v₂, w₁, w₂, t}
      B S hS p q f τ hp hq hf).app 𝓕) := by
  have haug := toSheaf_cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
    B S hS p q f τ hp hq hf 𝓕
  have h1 : Mono ((SheafOfModules.toSheaf
      (moduleRingSheaf B S hS q hq τ)).map
        ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf).app 𝓕) ≫
      (cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t}
        B S hS p q f τ hp hq hf 𝓕).hom.f 0) := by
    rw [haug]
    exact mono_sheafAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS q f τ hcover _
  have h2 : Mono ((SheafOfModules.toSheaf
      (moduleRingSheaf B S hS q hq τ)).map
        ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf).app 𝓕)) :=
    mono_of_mono _ ((cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t}
      B S hS p q f τ hp hq hf 𝓕).hom.f 0)
  have hmono : Mono ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
      B S hS p q f τ hp hq hf).app 𝓕) := Functor.mono_of_mono_map _ h2
  refine @quasiIso_fromSingle₀_of_exact _ _ _
    ((cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).obj 𝓕) _
    ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf).app 𝓕) hmono
    (cechModuleAugmentation_comp_d.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf 𝓕) ?_ ?_
  · refine (ShortComplex.exact_map_iff_of_faithful _ (SheafOfModules.toSheaf
      (moduleRingSheaf B S hS q hq τ))).1 ?_
    have e : (ShortComplex.mk
            ((cechModuleAugmentation.{u, v₁, v₂, w₁, w₂, t}
              B S hS p q f τ hp hq hf).app 𝓕)
            (((cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, t}
              B S hS p q f τ hp hq hf).obj 𝓕).d 0 1)
            (cechModuleAugmentation_comp_d.{u, v₁, v₂, w₁, w₂, t}
              B S hS p q f τ hp hq hf 𝓕)).map
          (SheafOfModules.toSheaf
            (moduleRingSheaf B S hS q hq τ)) ≅
        ShortComplex.mk
          (sheafAugmentation.{u, v₁, v₂, w₁, w₂, t} B S hS q f τ
            ((SheafOfModules.toSheaf
              (moduleRingSheaf B S hS q hq τ)).obj 𝓕))
          ((sheafComplex.{u, v₁, v₂, w₁, w₂, t} B S hS q f τ
            ((SheafOfModules.toSheaf
              (moduleRingSheaf B S hS q hq τ)).obj 𝓕)).d 0 1)
          (sheafAugmentation_comp_d.{u, v₁, v₂, w₁, w₂, t} B S hS q f τ
            ((SheafOfModules.toSheaf
              (moduleRingSheaf B S hS q hq τ)).obj 𝓕)) :=
      ShortComplex.isoMk (Iso.refl _)
        (HomologicalComplex.Hom.isoApp (cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf 𝓕) 0)
        (HomologicalComplex.Hom.isoApp (cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf 𝓕) 1)
        ((Category.id_comp _).trans haug.symm)
        ((cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf 𝓕).hom.comm 0 1)
    exact (ShortComplex.exact_iff_of_iso e).2
      (exact_sheafAugmentation.{u, v₁, v₂, w₁, w₂, t}
        B S hS p q f τ hp hq hf hcover _)
  · intro n
    refine (ShortComplex.exact_map_iff_of_faithful _ (SheafOfModules.toSheaf
      (moduleRingSheaf B S hS q hq τ))).1 ?_
    exact (ShortComplex.exact_iff_of_iso
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) (n + 1)).mapIso
        (cechModuleComplexIso.{u, v₁, v₂, w₁, w₂, t}
          B S hS p q f τ hp hq hf 𝓕))).2
      (exactAt_sheafComplex_succ.{u, v₁, v₂, w₁, w₂, t}
        B S hS p q f τ hp hq hf hcover _ n)

/-! ### Injectivity of the Čech terms of an injective sheaf of modules -/

omit [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max v₁ v₂ w₂ t}]
  [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
    AddCommGrpCat.{max v₁ v₂ w₂ t}] in
include hp hq hf in
/-- Each term of the relative Čech nerve of a `1`-morphism of categories fibred in groupoids
is itself fibred in groupoids over the base. -/
public lemma tupleProjection_comp_isFiberedInGroupoids (n : ℕ) :
    (Tuple.projection q f n ⋙ q).IsFiberedInGroupoids :=
  tuple_isFiberedInGroupoids q f (hf.comp_eq.symm ▸ hp) hq n

omit [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max v₁ v₂ w₂ t}]
  [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
    AddCommGrpCat.{max v₁ v₂ w₂ t}] in
include hp hq hf in
/-- Direct image along the `n`-th projection of the relative Čech nerve preserves injective
sheaves of modules: this is **Stacks 06WX (2)** for that projection. -/
private lemma preservesInjectiveObjects_cechModuleDirectImage (n : ℕ) :
    letI := tupleProjection_isContinuous B S hS p q f τ hp hq hf n
    letI := tupleProjection_isCocontinuous B S hS p q f τ hp hq hf n
    (SheafOfModules.directImage.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ)).PreservesInjectiveObjects := by
  let := tupleProjection_isContinuous B S hS p q f τ hp hq hf n
  let := tupleProjection_isCocontinuous B S hS p q f τ hp hq hf n
  exact AlgebraicGeometry.Stack.preservesInjectiveObjects_of_adjunction_sheafOfModules_pushforward
    B S hS (Tuple.projection q f n ⋙ q) q (Tuple.projection q f n) (B.baseTopology τ)
    (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hq rfl
    (B.baseTopology_le_topology τ) _
    ((SheafOfModules.pushforward₀DirectImageAdjunction.{u, max v₁ v₂ w₂ t}
      (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ)).ofNatIsoLeft
        (SheafOfModules.pushforwardIdIsoPushforward₀.{u, max v₁ v₂ w₂ t}
          (Tuple.projection q f n)
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
            (Tuple.projection q f n ⋙ q) τ)
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
          (moduleRingSheaf B S hS q hq τ)).symm)

include hp hq hf in
/-- The terms of the relative Čech complex of an injective sheaf of modules are injective: the
inverse image of an injective sheaf of modules along a faithful `1`-morphism whose source has
equalizers is injective by **Stacks 06X2 (2)**, and direct image preserves injectives by
**Stacks 06WX (2)**. -/
private lemma injective_cechModuleTerm [f.Faithful] [HasEqualizers 𝒰]
    (hRightAdjoint : ∀ n : ℕ, (PresheafOfModules.pushforward.{max v₁ v₂ w₂ t}
      (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS
        (Tuple.projection q f n ⋙ q) q (Tuple.projection q f n) (B.baseTopology τ)
        (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hq rfl
        (B.baseTopology_le_topology τ)).hom).IsRightAdjoint)
    [∀ (n : ℕ) (G : (Tuple q f n)ᵒᵖ ⥤ AddCommGrpCat.{max v₁ v₂ w₂ t}),
      (Tuple.projection q f n).op.HasPointwiseLeftKanExtension G]
    (𝓘 : SheafOfModules.{max v₁ v₂ w₂ t}
      (moduleRingSheaf B S hS q hq τ))
    [Injective 𝓘] (n : ℕ) :
    Injective ((cechModuleTerm.{u, v₁, v₂, w₁, w₂, t} B S hS p q f τ hp hq hf n).obj 𝓘) := by
  let := tupleProjection_isContinuous B S hS p q f τ hp hq hf n
  let := tupleProjection_isCocontinuous B S hS p q f τ hp hq hf n
  let : (Tuple.projection q f n).Faithful := tuple_projection_faithful q f n
  let : HasEqualizers (Tuple q f n) :=
    tuple_hasEqualizers q f (hf.comp_eq.symm ▸ hp) hq n
  let := preservesInjectiveObjects_cechModuleDirectImage.{u, v₁, v₂, w₁, w₂, t}
    B S hS p q f τ hp hq hf n
  let : Injective (show SheafOfModules.{max v₁ v₂ w₂ t}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) from 𝓘) := ‹Injective 𝓘›
  have h := AlgebraicGeometry.Stack.injective_sheafOfModules_pushforward_obj
    B S hS (Tuple.projection q f n ⋙ q) q (Tuple.projection q f n) (B.baseTopology τ)
    (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hq rfl
    (B.baseTopology_le_topology τ) (hRightAdjoint n) 𝓘
  let : Injective ((SheafOfModules.pushforward₀.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ)).obj 𝓘) :=
    Injective.of_iso ((SheafOfModules.pushforwardIdIsoPushforward₀.{u, max v₁ v₂ w₂ t}
      (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ)).app 𝓘) h
  exact Functor.injective_obj_of_injective
    (SheafOfModules.directImage.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ))
    (X := (SheafOfModules.pushforward₀.{u, max v₁ v₂ w₂ t} (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ)).obj 𝓘)
    inferInstance

end ModuleCech

end Modules

end Stacks.RelativeCech

end

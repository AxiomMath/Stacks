module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Étale cohomology of quasi-coherent modules and base change

For a scheme `X` and a quasi-coherent `𝒪_X`-module `ℱ`, write `ℱᵃ` for the abelian sheaf
`T ↦ Γ(T, T^* ℱ)` on the small étale site of `X`
(`AlgebraicGeometry.smallEtaleAssociatedSheaf`), and `ℱᵉ` for the same sheaf with its
coefficients raised to `AddCommGrpCat.{u + 1}`, the coefficient universe in which the restriction
maps `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` are formed.

This file makes `ℱ ↦ ℱᵉ` functorial in `ℱ`, equips `ℱᵉ` with multiplication by global functions
of `X`, and constructs, for a morphism `g : Y ⟶ X`, the comparison `g⁻¹ ℱᵉ ⟶ (g^* ℱ)ᵉ` of abelian
sheaves on `Y_étale`, adjoint to the pullback of sections `Γ(T, T^* ℱ) ⟶ Γ(T ×_X Y, …)`. It is
natural in `ℱ` and compatible with the multiplications. Composing the restriction map of étale
cohomology with it gives the map `H^q(X_étale, ℱᵉ) ⟶ H^q(Y_étale, (g^* ℱ)ᵉ)`, which commutes with
the connecting maps of short exact sequences.

## Main definitions

* `AlgebraicGeometry.QcohEtale.etaleSheaf`: `ℱᵉ`.
* `AlgebraicGeometry.QcohEtale.etaleMap`: the morphism `ℱᵉ ⟶ 𝒢ᵉ` induced by `ℱ ⟶ 𝒢`.
* `AlgebraicGeometry.QcohEtale.etaleScalar`: multiplication by a global function on `ℱᵉ`.
* `AlgebraicGeometry.QcohEtale.comparison`: the comparison `g⁻¹ ℱᵉ ⟶ (g^* ℱ)ᵉ`.
* `AlgebraicGeometry.QcohEtale.restriction`: the induced map on étale cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.EtaleCohomology

universe w u

namespace AlgebraicGeometry.QcohEtale

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

section Sheaf

variable {X : Scheme.{u}}

/-- The morphism `ℱᵃ ⟶ 𝒢ᵃ` induced by a morphism of quasi-coherent modules. -/
def assocMap {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    smallEtaleAssociatedSheaf X F ⟶ smallEtaleAssociatedSheaf X G :=
  ⟨Functor.whiskerLeft (Scheme.Etale.forget X).op ((pullbackSectionsFunctor X).map φ)⟩

/-- Over an étale `T ⟶ X`, `assocMap φ` is the map `Γ(T, T^* ℱ) ⟶ Γ(T, T^* 𝒢)` induced by `φ`. -/
@[simp]
theorem assocMap_app {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G)
    (T : X.Etale) :
    (assocMap φ).hom.app (op T) = ((Scheme.Modules.pullback T.hom).map φ).app ⊤ := rfl

/-- `assocMap` preserves composition. -/
theorem assocMap_comp {F G H : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    [H.IsQuasicoherent] (φ : F ⟶ G) (ψ : G ⟶ H) :
    assocMap (φ ≫ ψ) = assocMap φ ≫ assocMap ψ := by
  ext T x
  change ((pullbackSectionsFunctor X).map (φ ≫ ψ)).app _ x =
    ((pullbackSectionsFunctor X).map φ ≫ (pullbackSectionsFunctor X).map ψ).app _ x
  rw [Functor.map_comp]

/-- `assocMap` sends the identity to the identity. -/
theorem assocMap_id (F : X.Modules) [F.IsQuasicoherent] : assocMap (𝟙 F) = 𝟙 _ := by
  ext T x
  change ((pullbackSectionsFunctor X).map (𝟙 F)).app _ x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- `ℱᵃ` with its coefficients raised to `AddCommGrpCat.{u + 1}`. -/
abbrev etaleSheaf (F : X.Modules) [F.IsQuasicoherent] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (smallEtaleAssociatedSheaf X F)

/-- The morphism `ℱᵉ ⟶ 𝒢ᵉ` induced by a morphism of quasi-coherent modules. -/
def etaleMap {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    etaleSheaf F ⟶ etaleSheaf G :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map (assocMap φ)

/-- Over an étale `T ⟶ X`, `etaleMap φ` applies the map `Γ(T, T^* ℱ) ⟶ Γ(T, T^* 𝒢)` induced by
`φ` to the underlying section. -/
theorem etaleMap_app {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G)
    (T : X.Etale) (x : ULift.{u + 1} Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    (etaleMap φ).hom.app (op T) x =
      ULift.up (((Scheme.Modules.pullback T.hom).map φ).app ⊤ x.down) :=
  rfl

/-- `etaleMap` preserves composition. -/
theorem etaleMap_comp {F G H : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    [H.IsQuasicoherent] (φ : F ⟶ G) (ψ : G ⟶ H) :
    etaleMap (φ ≫ ψ) = etaleMap φ ≫ etaleMap ψ := by
  rw [etaleMap, assocMap_comp, Functor.map_comp]
  rfl

/-- `etaleMap` sends the identity to the identity. -/
theorem etaleMap_id (F : X.Modules) [F.IsQuasicoherent] : etaleMap (𝟙 F) = 𝟙 _ := by
  rw [etaleMap, assocMap_id, CategoryTheory.Functor.map_id]

/-- `etaleMap` sends the zero morphism to zero. -/
theorem etaleMap_zero (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    etaleMap (0 : F ⟶ G) = 0 := by
  ext T x
  change ULift.up (((Scheme.Modules.pullback T.unop.hom).map (0 : F ⟶ G)).app ⊤ x.down) = 0
  rw [Functor.map_zero]
  rfl

end Sheaf

section Scalar

variable {X : Scheme.{u}}

/-- Multiplication by `c` on the global sections of a module, as an additive map. -/
def smulHom {T : Scheme.{u}} (M : T.Modules) (c : Γ(T, ⊤)) : Γ(M, ⊤) →+ Γ(M, ⊤) where
  toFun x := c • x
  map_zero' := smul_zero c
  map_add' := smul_add c

/-- The pullback of sections along a morphism of étale `X`-schemes is semilinear for the global
functions of `X`. -/
theorem pullbackSectionsMap_smulHom (F : X.Modules) (r : Γ(X, ⊤)) {T T' : X.Etale} (m : T' ⟶ T)
    (x : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    pullbackSectionsMap F ((Scheme.Etale.forget X).map m)
        (smulHom ((Scheme.Modules.pullback T.hom).obj F) (T.hom.appTop r) x) =
      smulHom ((Scheme.Modules.pullback T'.hom).obj F) (T'.hom.appTop r)
        (pullbackSectionsMap F ((Scheme.Etale.forget X).map m) x) := by
  have hw : m.left ≫ T.hom = T'.hom := MorphismProperty.Over.w m
  have h : T'.hom.appTop r = m.left.appTop (T.hom.appTop r) := by
    rw [← hw]
    rfl
  refine (pullbackSectionsMap_smul F ((Scheme.Etale.forget X).map m) (T.hom.appTop r) x).trans ?_
  exact congrArg (fun c => c • pullbackSectionsMap F ((Scheme.Etale.forget X).map m) x) h.symm

/-- Multiplication by a global function `r` of `X` on `ℱᵃ`: over an étale `T ⟶ X` it multiplies a
section of `T^* ℱ` by the pullback of `r` to `T`. -/
def assocScalar (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) :
    smallEtaleAssociatedSheaf X F ⟶ smallEtaleAssociatedSheaf X F :=
  ⟨{ app := fun T => AddCommGrpCat.ofHom
        (smulHom ((Scheme.Modules.pullback T.unop.hom).obj F) (T.unop.hom.appTop r))
     naturality := fun _ _ m => by
        ext x
        exact (pullbackSectionsMap_smulHom F r m.unop x).symm }⟩

/-- Over an étale `T ⟶ X`, `assocScalar F r` multiplies a section by the pullback of `r` to `T`. -/
theorem assocScalar_app (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) (T : X.Etale)
    (x : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    (assocScalar F r).hom.app (op T) x =
      smulHom ((Scheme.Modules.pullback T.hom).obj F) (T.hom.appTop r) x := rfl

/-- Multiplication by a global function on `ℱᵉ`. -/
def etaleScalar (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) :
    etaleSheaf F ⟶ etaleSheaf F :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map (assocScalar F r)

/-- Over an étale `T ⟶ X`, `etaleScalar F r` multiplies the underlying section by the pullback of
`r` to `T`. -/
theorem etaleScalar_app (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) (T : X.Etale)
    (x : ULift.{u + 1} Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    (etaleScalar F r).hom.app (op T) x =
      ULift.up (smulHom ((Scheme.Modules.pullback T.hom).obj F) (T.hom.appTop r) x.down) := rfl

/-- Multiplication by a global function commutes with morphisms of modules. -/
theorem etaleScalar_comp_etaleMap {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) (r : Γ(X, ⊤)) :
    etaleScalar F r ≫ etaleMap φ = etaleMap φ ≫ etaleScalar G r := by
  ext T x
  change ULift.up (((Scheme.Modules.pullback T.unop.hom).map φ).app ⊤
      (smulHom ((Scheme.Modules.pullback T.unop.hom).obj F) (T.unop.hom.appTop r) x.down)) =
    ULift.up (smulHom ((Scheme.Modules.pullback T.unop.hom).obj G) (T.unop.hom.appTop r)
      (((Scheme.Modules.pullback T.unop.hom).map φ).app ⊤ x.down))
  exact congrArg ULift.up (Scheme.Modules.Hom.app_smul _ _ _)

end Scalar

section Comparison

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The counit `T ×_X Y ⟶ T` of base change, as a natural transformation of functors from the
small étale site of `X` to schemes over `X`. -/
abbrev baseChangeCounit :
    smallEtaleBaseChange g ⋙ Scheme.Etale.forget Y ⋙ Over.map g ⟶ Scheme.Etale.forget X :=
  Functor.whiskerLeft (Scheme.Etale.forget X) (Over.mapPullbackAdj g).counit

/-- The base change functor followed by the forgetful functor to schemes over `Y`. -/
abbrev baseChangeOver : X.Etale ⥤ Over Y := smallEtaleBaseChange g ⋙ Scheme.Etale.forget Y

/-- The pullback of sections `Γ(T, T^* ℱ) ⟶ Γ(T ×_X Y, (T ×_X Y ⟶ Y)^* g^* ℱ)`, as a morphism of
abelian presheaves on the small étale site of `X`. -/
def unitPresheaf' (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Etale.forget X).op ⋙ quasiCoherentPresheafFunctor X F ⟶
      (baseChangeOver g).op ⋙
        quasiCoherentPresheafFunctor Y ((Scheme.Modules.pullback g).obj F) :=
  Functor.whiskerRight (NatTrans.op (baseChangeCounit g)) (quasiCoherentPresheafFunctor X F) ≫
    (Functor.associator (baseChangeOver g).op (Over.map g).op
      (quasiCoherentPresheafFunctor X F)).hom ≫
    Functor.whiskerLeft (baseChangeOver g).op
      (Stacks.Sites.quasiCoherentPresheafBaseChangeIso F (Over.mk g)).hom

/-- `unitPresheaf'` with source and target spelled as the associated sheaves. -/
def unitPresheaf (F : X.Modules) [F.IsQuasicoherent] :
    (smallEtaleAssociatedSheaf X F).obj ⟶
      (smallEtaleBaseChange g).op ⋙
        (smallEtaleAssociatedSheaf Y ((Scheme.Modules.pullback g).obj F)).obj :=
  unitPresheaf' g F

/-- The pullback of sections, as a morphism of sheaves `ℱᵃ ⟶ g_* (g^* ℱ)ᵃ`. -/
def unitSheaf (F : X.Modules) [F.IsQuasicoherent] :
    smallEtaleAssociatedSheaf X F ⟶
      ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology).obj
        (smallEtaleAssociatedSheaf Y ((Scheme.Modules.pullback g).obj F)) :=
  ⟨unitPresheaf g F⟩

/-- The pullback of sections, as a morphism of sheaves `ℱᵉ ⟶ g_* (g^* ℱ)ᵉ`. -/
def unit (F : X.Modules) [F.IsQuasicoherent] :
    etaleSheaf F ⟶
      ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology).obj
        (etaleSheaf ((Scheme.Modules.pullback g).obj F)) :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map (unitSheaf g F)

/-- **The comparison `g⁻¹ ℱᵉ ⟶ (g^* ℱ)ᵉ`**, adjoint to the pullback of sections. -/
def comparison (F : X.Modules) [F.IsQuasicoherent] :
    (etaleAbelianInverseImage.{u, u + 1} g).obj (etaleSheaf F) ⟶
      etaleSheaf ((Scheme.Modules.pullback g).obj F) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
    AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology).homEquiv _ _).symm
      (unit g F)

/-- Over an étale `T ⟶ X`, `unitPresheaf' g F` pulls a section back along `T ×_X Y ⟶ T` and
identifies the result through `Scheme.Modules.pullbackComp`. -/
theorem unitPresheaf'_app_apply (F : X.Modules) [F.IsQuasicoherent] (T : X.Etale)
    (x : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    (unitPresheaf' g F).app (op T) x =
      ((Scheme.Modules.pullbackComp ((baseChangeOver g).obj T).hom g).inv.app F).app ⊤
        (pullbackSectionsMap F ((baseChangeCounit g).app T) x) := rfl

/-- Over an étale `T ⟶ X`, `unitSheaf g F` pulls a section back along `T ×_X Y ⟶ T` and
identifies the result through `Scheme.Modules.pullbackComp`. -/
theorem unitSheaf_app_apply (F : X.Modules) [F.IsQuasicoherent] (T : X.Etale)
    (x : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    (unitSheaf g F).hom.app (op T) x =
      ((Scheme.Modules.pullbackComp ((baseChangeOver g).obj T).hom g).inv.app F).app ⊤
        (pullbackSectionsMap F ((baseChangeCounit g).app T) x) := rfl

/-- The pullback of sections is natural in the module. -/
theorem unitSheaf_naturality {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) :
    assocMap φ ≫ unitSheaf g G =
      unitSheaf g F ≫ ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology).map
          (assocMap ((Scheme.Modules.pullback g).map φ)) := by
  ext T x
  let A := (baseChangeOver g).obj T.unop
  let c := (baseChangeCounit g).app T.unop
  have h1 := ConcreteCategory.congr_hom (pullbackSectionsMap_naturality φ c) x
  have h2 := ConcreteCategory.congr_hom (congrArg (fun ψ => Scheme.Modules.Hom.app ψ ⊤)
    ((Scheme.Modules.pullbackComp A.hom g).inv.naturality φ)) (pullbackSectionsMap F c x)
  simp only [Scheme.Modules.Hom.comp_app, Functor.comp_map, ConcreteCategory.comp_apply] at h1 h2
  change ((Scheme.Modules.pullbackComp A.hom g).inv.app G).app ⊤
      (pullbackSectionsMap G c (((Scheme.Modules.pullback T.unop.hom).map φ).app ⊤ x)) =
    ((Scheme.Modules.pullback A.hom).map ((Scheme.Modules.pullback g).map φ)).app ⊤
      (((Scheme.Modules.pullbackComp A.hom g).inv.app F).app ⊤ (pullbackSectionsMap F c x))
  exact (congrArg (ConcreteCategory.hom (((Scheme.Modules.pullbackComp A.hom g).inv.app G).app ⊤))
    h1.symm).trans h2

/-- The pullback of sections `ℱᵉ ⟶ g_* (g^* ℱ)ᵉ` is natural in the module. -/
theorem unit_naturality {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) :
    etaleMap φ ≫ unit g G =
      unit g F ≫ ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology).map
          (etaleMap ((Scheme.Modules.pullback g).map φ)) := by
  have h := congrArg
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
    (unitSheaf_naturality g φ)
  simp only [Functor.map_comp] at h
  exact h

/-- The comparison intertwines `a` and `b` when `unit g` does. -/
private theorem inverseImage_map_comp_comparison {F F' : X.Modules} [F.IsQuasicoherent]
    [F'.IsQuasicoherent] (a : etaleSheaf F ⟶ etaleSheaf F')
    (b : etaleSheaf ((Scheme.Modules.pullback g).obj F) ⟶
      etaleSheaf ((Scheme.Modules.pullback g).obj F'))
    (h : a ≫ unit g F' = unit g F ≫ ((smallEtaleBaseChange g).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology).map b) :
    (etaleAbelianInverseImage.{u, u + 1} g).map a ≫ comparison g F' = comparison g F ≫ b := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange g) AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology
  have h1 := adj.homEquiv_naturality_left_symm a (unit g F')
  have h2 := adj.homEquiv_naturality_right_symm (unit g F) b
  change _ = (adj.homEquiv _ _).symm (unit g F) ≫ _
  rw [← h2, ← h, h1]
  rfl

/-- **The comparison `g⁻¹ ℱᵉ ⟶ (g^* ℱ)ᵉ` is natural in the module.** -/
theorem comparison_naturality {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) :
    (etaleAbelianInverseImage.{u, u + 1} g).map (etaleMap φ) ≫ comparison g G =
      comparison g F ≫ etaleMap ((Scheme.Modules.pullback g).map φ) :=
  inverseImage_map_comp_comparison g _ _ (unit_naturality g φ)

/-- The pullback of a global function to `T ×_X Y`, computed through `T` or through `Y`. -/
theorem baseChangeCounit_appTop (r : Γ(X, ⊤)) (T : X.Etale) :
    ((baseChangeCounit g).app T).left.appTop (T.hom.appTop r) =
      ((baseChangeOver g).obj T).hom.appTop (g.appTop r) := by
  have hw : ((baseChangeCounit g).app T).left ≫ T.hom = ((baseChangeOver g).obj T).hom ≫ g :=
    Over.w ((baseChangeCounit g).app T)
  change (((baseChangeCounit g).app T).left ≫ T.hom).appTop r =
    (((baseChangeOver g).obj T).hom ≫ g).appTop r
  rw [hw]

/-- The pullback of sections is semilinear. -/
theorem unitSheaf_scalar (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) :
    assocScalar F r ≫ unitSheaf g F =
      unitSheaf g F ≫ ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology).map
          (assocScalar ((Scheme.Modules.pullback g).obj F) (g.appTop r)) := by
  ext T x
  let A := (baseChangeOver g).obj T.unop
  let c := (baseChangeCounit g).app T.unop
  change ((Scheme.Modules.pullbackComp A.hom g).inv.app F).app ⊤
      (pullbackSectionsMap F c (smulHom _ (T.unop.hom.appTop r) x)) =
    smulHom _ (A.hom.appTop (g.appTop r))
      (((Scheme.Modules.pullbackComp A.hom g).inv.app F).app ⊤ (pullbackSectionsMap F c x))
  simp only [smulHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  refine (congrArg (ConcreteCategory.hom (((Scheme.Modules.pullbackComp A.hom g).inv.app F).app ⊤))
    (pullbackSectionsMap_smul F c (T.unop.hom.appTop r) x)).trans ?_
  refine (Scheme.Modules.Hom.app_smul _ _ _).trans ?_
  exact congrArg (· • _) (baseChangeCounit_appTop g r T.unop)

/-- The pullback of sections `ℱᵉ ⟶ g_* (g^* ℱ)ᵉ` is semilinear. -/
theorem unit_scalar (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) :
    etaleScalar F r ≫ unit g F =
      unit g F ≫ ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology).map
          (etaleScalar ((Scheme.Modules.pullback g).obj F) (g.appTop r)) := by
  have h := congrArg
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
    (unitSheaf_scalar g F r)
  simp only [Functor.map_comp] at h
  exact h

/-- **The comparison `g⁻¹ ℱᵉ ⟶ (g^* ℱ)ᵉ` is semilinear.** -/
theorem comparison_scalar (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) :
    (etaleAbelianInverseImage.{u, u + 1} g).map (etaleScalar F r) ≫ comparison g F =
      comparison g F ≫ etaleScalar ((Scheme.Modules.pullback g).obj F) (g.appTop r) :=
  inverseImage_map_comp_comparison g _ _ (unit_scalar g F r)

end Comparison

section ShortComplexes

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- A short complex of quasi-coherent modules, carried to abelian étale sheaves by `ℱ ↦ ℱᵉ`. -/
def etaleShortComplex (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (etaleMap S.f) (etaleMap S.g) (by rw [← etaleMap_comp, S.zero, etaleMap_zero])

/-- The pullback of a short complex of modules along `g`. -/
def pullbackShortComplex (S : ShortComplex X.Modules) : ShortComplex Y.Modules :=
  ShortComplex.mk ((Scheme.Modules.pullback g).map S.f) ((Scheme.Modules.pullback g).map S.g)
    (by rw [← Functor.map_comp, S.zero, Functor.map_zero])

/-- The first object of the pullback of a short complex is quasi-coherent when that of the
original is. -/
instance (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] :
    (pullbackShortComplex g S).X₁.IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pullback g).obj S.X₁).IsQuasicoherent

/-- The second object of the pullback of a short complex is quasi-coherent when that of the
original is. -/
instance (S : ShortComplex X.Modules) [S.X₂.IsQuasicoherent] :
    (pullbackShortComplex g S).X₂.IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pullback g).obj S.X₂).IsQuasicoherent

/-- The third object of the pullback of a short complex is quasi-coherent when that of the
original is. -/
instance (S : ShortComplex X.Modules) [S.X₃.IsQuasicoherent] :
    (pullbackShortComplex g S).X₃.IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pullback g).obj S.X₃).IsQuasicoherent

/-- The comparison of `g⁻¹` of `etaleShortComplex S` with `etaleShortComplex` of the pullback. -/
def comparisonShortComplex (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (etaleShortComplex S).map (etaleAbelianInverseImage.{u, u + 1} g) ⟶
      etaleShortComplex (pullbackShortComplex g S) where
  τ₁ := comparison g S.X₁
  τ₂ := comparison g S.X₂
  τ₃ := comparison g S.X₃
  comm₁₂ := (comparison_naturality g S.f).symm
  comm₂₃ := (comparison_naturality g S.g).symm

end ShortComplexes

section Restriction

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The base change map `H^q(X_étale, ℱᵉ) ⟶ H^q(Y_étale, (g^* ℱ)ᵉ)`**: restriction along `g`
followed by the comparison `g⁻¹ ℱᵉ ⟶ (g^* ℱ)ᵉ`. -/
def restriction (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    Sheaf.H.{w} (etaleSheaf F) q →+
      Sheaf.H.{w} (etaleSheaf ((Scheme.Modules.pullback g).obj F)) q :=
  ((Ext.mk₀ (comparison g F)).postcomp _ (add_zero q)).comp
    (etaleCohomologyRestrictionMap.{u, u + 1, w} g (etaleSheaf F) q)

/-- The base change map sends a class `x` to the composite of its restriction along `g` with the
comparison `g⁻¹ ℱᵉ ⟶ (g^* ℱ)ᵉ`. -/
theorem restriction_apply (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    (x : Sheaf.H.{w} (etaleSheaf F) q) :
    restriction g F q x =
      (etaleCohomologyRestrictionMap.{u, u + 1, w} g (etaleSheaf F) q x).comp
        (Ext.mk₀ (comparison g F)) (add_zero q) := rfl

/-- The base change map intertwines `a` and `b` when the comparison does. -/
private theorem restriction_comp_mk₀_of_comparison {F F' : X.Modules} [F.IsQuasicoherent]
    [F'.IsQuasicoherent] (a : etaleSheaf F ⟶ etaleSheaf F')
    (b : etaleSheaf ((Scheme.Modules.pullback g).obj F) ⟶
      etaleSheaf ((Scheme.Modules.pullback g).obj F'))
    (h : (etaleAbelianInverseImage.{u, u + 1} g).map a ≫ comparison g F' = comparison g F ≫ b)
    (q : ℕ) (x : Sheaf.H.{w} (etaleSheaf F) q) :
    restriction g F' q (x.comp (Ext.mk₀ a) (add_zero q)) =
      (restriction g F q x).comp (Ext.mk₀ b) (add_zero q) := by
  rw [restriction_apply, restriction_apply, etaleCohomologyRestrictionMap_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀, h]

/-- The base change map is natural in the module. -/
theorem restriction_comp_mk₀ {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) (q : ℕ) (x : Sheaf.H.{w} (etaleSheaf F) q) :
    restriction g G q (x.comp (Ext.mk₀ (etaleMap φ)) (add_zero q)) =
      (restriction g F q x).comp (Ext.mk₀ (etaleMap ((Scheme.Modules.pullback g).map φ)))
        (add_zero q) :=
  restriction_comp_mk₀_of_comparison g _ _ (comparison_naturality g φ) q x

/-- The base change map is semilinear. -/
theorem restriction_comp_scalar (F : X.Modules) [F.IsQuasicoherent] (r : Γ(X, ⊤)) (q : ℕ)
    (x : Sheaf.H.{w} (etaleSheaf F) q) :
    restriction g F q (x.comp (Ext.mk₀ (etaleScalar F r)) (add_zero q)) =
      (restriction g F q x).comp
        (Ext.mk₀ (etaleScalar ((Scheme.Modules.pullback g).obj F) (g.appTop r))) (add_zero q) :=
  restriction_comp_mk₀_of_comparison g _ _ (comparison_scalar g F r) q x

/-- **The base change map commutes with the connecting maps.** -/
theorem restriction_comp_extClass (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (hS : (etaleShortComplex S).ShortExact)
    (hS' : (etaleShortComplex (pullbackShortComplex g S)).ShortExact) (q r : ℕ) (hqr : q + 1 = r)
    (x : Sheaf.H.{w} (etaleSheaf S.X₃) q) :
    restriction g S.X₁ r (x.comp hS.extClass hqr) =
      (restriction g S.X₃ q x).comp hS'.extClass hqr := by
  have hS₁ := hS.map_of_exact (etaleAbelianInverseImage.{u, u + 1} g)
  have hnat := hS₁.extClass_naturality hS' (comparisonShortComplex g S)
  refine (congrArg (fun z => z.comp (Ext.mk₀ (comparison g S.X₁)) (add_zero r))
    (etaleCohomologyRestrictionMap_comp_extClass.{u, u + 1, w} g hS q r hqr x)).trans ?_
  refine (Ext.comp_assoc _ _ _ hqr (add_zero 1) (by omega)).trans ?_
  refine Eq.trans ?_ (Ext.comp_assoc _ _ _ (add_zero q) (zero_add 1) (by omega)).symm
  exact congrArg (fun z =>
    (etaleCohomologyRestrictionMap.{u, u + 1, w} g (etaleSheaf S.X₃) q x).comp z (by omega)) hnat

end Restriction

end AlgebraicGeometry.QcohEtale

end

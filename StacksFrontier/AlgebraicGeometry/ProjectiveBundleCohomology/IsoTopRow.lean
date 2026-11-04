module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoTrace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistPairing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.SpellingBridge
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPullback

/-!
# The multiplication pairing of Tag 01XX under an isomorphism of modules

Let `e : E ≅ E'` be an isomorphism of finite locally free `𝒪_S`-modules of constant rank `n + 1`
and `f : 𝐏(E') ⟶ 𝐏(E)` the induced isomorphism of projective bundles over `S`. The adjoints
`π^* Sym^k(E) ⟶ 𝒪(k)` of the homogeneous-section maps, and the multiplication pairings
`𝒪(d) ⊗ π^* Sym^k(E) ⟶ 𝒪(d + k)`, correspond under `f` and `e`.

## Main results

* `curry_dual_pullback_iso`: the curried pairing `O ⟶ L ⊗ p^*(G^∨)` of a pairing
  `O ⊗ p^* G ⟶ L` commutes with pullback along an isomorphism.
* `psiFlat_pullback`: the adjoints `π^* Sym^k(E) ⟶ 𝒪(k)` correspond under `f` and `e`.
* `twistPairing_pullback`: the multiplication pairings correspond under `f` and `e`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section DualPullback

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)

/-- A pasting of three commutative squares along two pairs of mutually inverse morphisms. -/
private theorem dualPullback_chase {C : Type*} [Category C]
    {Q₀ Q₀' Q₁ Q₂ Q₃ R R₀ R₁ R₂ : C} {c₁ : Q₀ ⟶ Q₁} {c₂ : Q₁ ⟶ Q₂} {dg : Q₂ ⟶ Q₃}
    {P₃ : Q₃ ⟶ R} {P₂ : Q₂ ⟶ R₂} {dpg : R₂ ⟶ R} {P₁ : Q₁ ⟶ R₁} {u₂ : R₂ ⟶ R₁}
    {u₂' : R₁ ⟶ R₂} {F : Q₀ ⟶ Q₀'} {PF : Q₀' ⟶ R₀} {u₁ : R₁ ⟶ R₀} {u₁' : R₀ ⟶ R₁}
    (hnat : dg ≫ P₃ = P₂ ≫ dpg) (hcongr : c₂ ≫ P₂ ≫ u₂ = P₁) (hcomp : c₁ ≫ P₁ ≫ u₁ = F ≫ PF)
    (hinv₂ : u₂ ≫ u₂' = 𝟙 _) (hinv₁ : u₁ ≫ u₁' = 𝟙 _) :
    (c₁ ≫ c₂) ≫ dg ≫ P₃ = F ≫ PF ≫ u₁' ≫ u₂' ≫ dpg := by
  rw [hnat, ← reassoc_of% hcomp, ← hcongr]
  simp only [Category.assoc, reassoc_of% hinv₁, reassoc_of% hinv₂]

/-- The dual of an isomorphism followed by the dual of its inverse is the identity. -/
public theorem dualMap_hom_inv {X : Scheme.{u}} {F G : X.Modules} (i : F ≅ G) :
    dualMap i.hom ≫ dualMap i.inv = 𝟙 _ :=
  (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_comp _ _).symm.trans
    ((congrArg dualMap i.inv_hom_id).trans (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_id _))

/-- `tensorPullbackIso` is natural in the second factor, when the first map is an identity. -/
private theorem pullback_tensorMap_id_left_tensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M L₁ L₂ : Y.Modules} {N L₁' L₂' : X.Modules} (a : (Scheme.Modules.pullback f).obj M ≅ N)
    (l : (Scheme.Modules.pullback f).obj L₁ ≅ L₁') (l' : (Scheme.Modules.pullback f).obj L₂ ≅ L₂')
    (k : L₁ ⟶ L₂) (k' : L₁' ⟶ L₂') (hk : (Scheme.Modules.pullback f).map k ≫ l'.hom = l.hom ≫ k') :
    (Scheme.Modules.pullback f).map (tensorMap (Z := Y.toRingedSpace) (𝟙 M) k) ≫
        (tensorPullbackIso f.toLRSHom.toShHom a l').hom =
      (tensorPullbackIso f.toLRSHom.toShHom a l).hom ≫
        tensorMap (Z := X.toRingedSpace) (𝟙 N) k' :=
  tensorPullbackIso_naturality₂ f.toLRSHom.toShHom a a l l' (𝟙 M) (𝟙 N) k k'
    (((congrArg (· ≫ a.hom) ((Scheme.Modules.pullback f).map_id M)).trans
      (Category.id_comp _)).trans (Category.comp_id _).symm) hk

variable {X X' T : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ T) (p' : X' ⟶ T) (hbase : f ≫ p = p')
  {G G' : T.Modules} (g : G ≅ G')

/-- **The dual base-change maps along `f`, `p` and `p' = f ≫ p` correspond**, along an
isomorphism `g : G ≅ G'`: `f^* p^*(G^∨) ≅ p'^*(G'^∨) ⟶ (p'^* G')^∨` is
`f^* p^*(G^∨) ⟶ f^*((p^* G)^∨) ⟶ (f^* p^* G)^∨ ≅ (p'^* G')^∨`. -/
public theorem pullbackDualMap_pullbackPullbackIso :
    ((Scheme.Modules.pullbackComp f p).hom.app (dualSheaf G) ≫
        (Scheme.Modules.pullbackCongr hbase).hom.app (dualSheaf G)) ≫
      (Scheme.Modules.pullback p').map (dualMap g.inv) ≫ Stacks.Chow.pullbackDualMap p' G' =
    (Scheme.Modules.pullback f).map (Stacks.Chow.pullbackDualMap p G) ≫
      Stacks.Chow.pullbackDualMap f ((Scheme.Modules.pullback p).obj G) ≫
      dualMap ((Scheme.Modules.pullbackComp f p).inv.app G) ≫
      dualMap ((Scheme.Modules.pullbackCongr hbase).inv.app G) ≫
      dualMap ((Scheme.Modules.pullback p').map g.inv) :=
  dualPullback_chase (pullbackDualMap_naturality p' g.inv)
    (Stacks.FundamentalGroup.pullbackDualMap_congr hbase G)
    (Stacks.Chow.pullbackDualMap_comp f p G)
    (dualMap_hom_inv ((Scheme.Modules.pullbackCongr hbase).app G))
    (dualMap_hom_inv ((Scheme.Modules.pullbackComp f p).app G))

/-- The inverse of `f^* p^* M ≅ p'^* M` as a composite. -/
public theorem pullbackPullbackIso_inv (M : T.Modules) :
    (pullbackPullbackIso f p p' hbase M).inv =
      (Scheme.Modules.pullbackCongr hbase).inv.app M ≫
        (Scheme.Modules.pullbackComp f p).inv.app M :=
  rfl

/-- The dual of `f^* p^* G ≅ p'^* G ≅ p'^* G'`, inverted, as a composite. -/
public theorem dualMap_pullbackPullbackIso_inv :
    dualMap (pullbackPullbackIso f p p' hbase G ≪≫ (Scheme.Modules.pullback p').mapIso g).inv =
      dualMap ((Scheme.Modules.pullbackComp f p).inv.app G) ≫
        dualMap ((Scheme.Modules.pullbackCongr hbase).inv.app G) ≫
        dualMap ((Scheme.Modules.pullback p').map g.inv) := by
  rw [Iso.trans_inv, Functor.mapIso_inv, pullbackPullbackIso_inv,
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_comp,
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_comp, Category.assoc]

variable [IsIso f]
  [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [hG' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G')]

omit [IsIso f] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G')] in
/-- **The dual base-change isomorphisms along `f`, `p` and `p' = f ≫ p` correspond**, along
`g : G ≅ G'`: `f^*(p^*(G^∨) ≅ (p^* G)^∨)` followed by the dual base change along `f` and
`f^* p^* G ≅ p'^* G'` is `f^* p^*(G^∨) ≅ p'^*(G'^∨) ≅ (p'^* G')^∨`, inverted. -/
public theorem pullbackDualSheafIso_pullbackPullbackIso' :
    (Scheme.Modules.pullback f).map (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG).inv ≫
        (pullbackPullbackIso' f p p' hbase
          ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor T).mapIso g.op).symm).hom =
      (pullbackDualIsoOf f ((Scheme.Modules.pullback p).obj G)
          (pullbackPullbackIso f p p' hbase G ≪≫ (Scheme.Modules.pullback p').mapIso g)
          inferInstance).hom ≫
        (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').inv := by
  have h : ((Scheme.Modules.pullback f).mapIso
        (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG)).hom ≫
      (pullbackDualIsoOf f ((Scheme.Modules.pullback p).obj G)
          (pullbackPullbackIso f p p' hbase G ≪≫ (Scheme.Modules.pullback p').mapIso g)
          inferInstance).hom =
      (pullbackPullbackIso' f p p' hbase
          ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor T).mapIso g.op).symm).hom ≫
        (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').hom := by
    have e₁ : ((Scheme.Modules.pullback f).mapIso
          (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG)).hom ≫
        (pullbackDualIsoOf f ((Scheme.Modules.pullback p).obj G)
            (pullbackPullbackIso f p p' hbase G ≪≫ (Scheme.Modules.pullback p').mapIso g)
            inferInstance).hom =
        (Scheme.Modules.pullback f).map (Stacks.Chow.pullbackDualMap p G) ≫
          Stacks.Chow.pullbackDualMap f ((Scheme.Modules.pullback p).obj G) ≫
          dualMap (pullbackPullbackIso f p p' hbase G ≪≫
            (Scheme.Modules.pullback p').mapIso g).inv :=
      rfl
    have e₂ : (pullbackPullbackIso' f p p' hbase
          ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor T).mapIso g.op).symm).hom ≫
          (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').hom =
        ((Scheme.Modules.pullbackComp f p).hom.app (dualSheaf G) ≫
          (Scheme.Modules.pullbackCongr hbase).hom.app (dualSheaf G)) ≫
          (Scheme.Modules.pullback p').map (dualMap g.inv) ≫ Stacks.Chow.pullbackDualMap p' G' :=
      Category.assoc _ _ _
    exact e₁.trans ((congrArg (fun x => (Scheme.Modules.pullback f).map
        (Stacks.Chow.pullbackDualMap p G) ≫
          Stacks.Chow.pullbackDualMap f ((Scheme.Modules.pullback p).obj G) ≫ x)
        (dualMap_pullbackPullbackIso_inv f p p' hbase g)).trans
      ((pullbackDualMap_pullbackPullbackIso f p p' hbase g).symm.trans e₂.symm))
  rw [← Functor.mapIso_inv]
  exact iso_square_inv _ _ _ _ h

variable (α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj G) ≅
    (Scheme.Modules.pullback p').obj G')
  (hα : α.inv = (Scheme.Modules.pullback p').map g.inv ≫ (pullbackPullbackIso f p p' hbase G).inv)
  (gd : dualSheaf G ≅ dualSheaf G') (hgd : gd.hom = dualMap g.inv)

omit [IsIso f] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G')] in
include hα hgd in
/-- **The dual base-change isomorphisms along `f`, `p` and `p'` correspond**, for any
identifications `α : f^* p^* G ≅ p'^* G'` and `G^∨ ≅ G'^∨` induced by `g : G ≅ G'`. -/
public theorem pullbackDualSheafIso_pullbackPullbackIso_of :
    (Scheme.Modules.pullback f).map (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG).inv ≫
        (pullbackPullbackIso' f p p' hbase gd).hom =
      (pullbackDualIsoOf f ((Scheme.Modules.pullback p).obj G) α inferInstance).hom ≫
        (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').inv := by
  have h := pullbackDualSheafIso_pullbackPullbackIso' f p p' hbase g
  have e₁ : ∀ β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj G) ≅
      (Scheme.Modules.pullback p').obj G',
      (pullbackDualIsoOf f ((Scheme.Modules.pullback p).obj G) β inferInstance).hom =
        (Stacks.FundamentalGroup.pullbackDualSheafIso f ((Scheme.Modules.pullback p).obj G)
          inferInstance).hom ≫ dualMap β.inv := fun _ => rfl
  have e₂ : ∀ γ : dualSheaf G ≅ dualSheaf G', (pullbackPullbackIso' f p p' hbase γ).hom =
      (pullbackPullbackIso f p p' hbase (dualSheaf G)).hom ≫
        (Scheme.Modules.pullback p').map γ.hom := fun _ => rfl
  rw [e₁, hα, e₂, hgd]
  exact h

/-- A pasting of two commutative squares and a commutative triangle in a category. -/
private theorem curryDual_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ Q R S₀ S₁ : C}
    {a : P₀ ⟶ P₁} {b : P₁ ⟶ P₂} {c : P₂ ⟶ P₃} {bc : P₁ ⟶ P₃} {δ : P₃ ⟶ Q} {ab : P₀ ⟶ P₂}
    {β : P₂ ⟶ R} {c' : R ⟶ Q} {t : P₀ ⟶ S₀} {x : S₀ ⟶ S₁} {y : S₁ ⟶ R} {y' : S₁ ⟶ Q}
    (hbc : bc = b ≫ c) (hab : a ≫ b = ab) (hT : c ≫ δ = β ≫ c') (hC : ab ≫ β = t ≫ x ≫ y)
    (hy : y ≫ c' = y') :
    a ≫ bc ≫ δ = t ≫ x ≫ y' := by
  rw [hbc, Category.assoc, hT, ← Category.assoc, hab, ← Category.assoc, hC]
  simp only [Category.assoc, hy]

variable {O L : X.Modules} {O' L' : X'.Modules}
  (θO : (Scheme.Modules.pullback f).obj O ≅ O') (θL : (Scheme.Modules.pullback f).obj L ≅ L')

omit [IsIso f] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G)] in
/-- `SheafHom(p^* G, L) ≅ L ⊗ (p^* G)^∨ ≅ L ⊗ p^*(G^∨)` under pullback, as two morphisms. -/
public theorem pullback_map_sheafHomDual :
    (Scheme.Modules.pullback f).map
        (sheafHomIsoTensorDual ((Scheme.Modules.pullback p).obj G) L ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl L)
            (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG).symm).hom =
      (Scheme.Modules.pullback f).map
          (sheafHomIsoTensorDual ((Scheme.Modules.pullback p).obj G) L).hom ≫
        (Scheme.Modules.pullback f).map (tensorMap (Z := X.toRingedSpace) (𝟙 L)
          (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG).inv) :=
  (congrArg (Scheme.Modules.pullback f).map (Iso.trans_hom _ _)).trans
    ((Scheme.Modules.pullback f).map_comp
      (sheafHomIsoTensorDual ((Scheme.Modules.pullback p).obj G) L).hom
      (tensorMap (Z := X.toRingedSpace) (𝟙 L)
        (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG).inv))

omit [IsIso f] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G')] in
include hα hgd in
/-- `1 ⊗ (p^*(G^∨) ≅ (p^* G)^∨)⁻¹` under pullback along `f`. -/
public theorem pullback_tensorSheafMap_dualSheafIso :
    (Scheme.Modules.pullback f).map (tensorMap (Z := X.toRingedSpace) (𝟙 L)
          (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG).inv) ≫
        (tensorPullbackIso f.toLRSHom.toShHom θL (pullbackPullbackIso' f p p' hbase gd)).hom =
      CategoryStruct.comp (obj := X'.Modules) (tensorPullbackIso f.toLRSHom.toShHom θL
          (pullbackDualIsoOf f ((Scheme.Modules.pullback p).obj G) α inferInstance)).hom
        (tensorMap (Z := X'.toRingedSpace) (A := L') (A' := L')
          (B := dualSheaf ((Scheme.Modules.pullback p').obj G'))
          (B' := (Scheme.Modules.pullback p').obj (dualSheaf G')) (𝟙 L')
          (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').inv) :=
  pullback_tensorMap_id_left_tensorPullbackIso f θL
    (pullbackDualIsoOf f ((Scheme.Modules.pullback p).obj G) α inferInstance)
    (pullbackPullbackIso' f p p' hbase gd) _ _
    (pullbackDualSheafIso_pullbackPullbackIso_of f p p' hbase g α hα gd hgd)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G')] in
/-- `SheafHom(p'^* G', L') ≅ L' ⊗ p'^*(G'^∨)` as a composite. -/
public theorem sheafHomDual_hom :
    CategoryStruct.comp (obj := X'.Modules)
        (sheafHomIsoTensorDual ((Scheme.Modules.pullback p').obj G') L').hom
        (tensorMap (Z := X'.toRingedSpace) (A := L') (A' := L')
          (B := dualSheaf ((Scheme.Modules.pullback p').obj G'))
          (B' := (Scheme.Modules.pullback p').obj (dualSheaf G')) (𝟙 L')
          (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').inv) =
      (sheafHomIsoTensorDual ((Scheme.Modules.pullback p').obj G') L' ≪≫
        Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl L')
          (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').symm).hom := rfl

omit [IsIso f] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf G')] in
include hα hgd in
/-- **The curried pairing `O ⟶ SheafHom(p^* G, L) ≅ L ⊗ p^*(G^∨)` commutes with pullback along
`f`**, for a pairing `O ⊗ p^* G ⟶ L` compatible with `O' ⊗ p'^* G' ⟶ L'` along `f^* O ≅ O'`,
`f^* L ≅ L'` and `α : f^* p^* G ≅ p'^* G'` induced by `g : G ≅ G'`. -/
public theorem curry_dual_pullback_iso
    (tp : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj O).obj
        ((Scheme.Modules.pullback p).obj G) ⟶ L)
    (tp' : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj O').obj
        ((Scheme.Modules.pullback p').obj G') ⟶ L')
    (htp : (Scheme.Modules.pullback f).map tp ≫ θL.hom =
      (tensorPullbackIso f.toLRSHom.toShHom θO α).hom ≫ tp') :
    (Scheme.Modules.pullback f).map (Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace O
        ((Scheme.Modules.pullback p).obj G) L tp) ≫
      (Scheme.Modules.pullback f).map
        (sheafHomIsoTensorDual ((Scheme.Modules.pullback p).obj G) L ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl L)
            (Stacks.FundamentalGroup.pullbackDualSheafIso p G hG).symm).hom ≫
      (tensorPullbackIso f.toLRSHom.toShHom θL (pullbackPullbackIso' f p p' hbase gd)).hom =
    θO.hom ≫ Stacks.SheafOfModules.tensorHomEquiv X'.toRingedSpace _ _ _ tp' ≫
      (sheafHomIsoTensorDual ((Scheme.Modules.pullback p').obj G') L' ≪≫
        Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl L')
          (Stacks.FundamentalGroup.pullbackDualSheafIso p' G' hG').symm).hom :=
  curryDual_chase (pullback_map_sheafHomDual f p (G := G) (L := L))
    ((Scheme.Modules.pullback f).map_comp (Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace O
      ((Scheme.Modules.pullback p).obj G) L tp)
      (sheafHomIsoTensorDual ((Scheme.Modules.pullback p).obj G) L).hom).symm
    (pullback_tensorSheafMap_dualSheafIso f p p' hbase g α hα gd hgd θL)
    (curry_sheafHomIsoTensorDual_pullback f θO θL α tp tp' htp)
    (sheafHomDual_hom p' (G' := G') (L' := L'))

end DualPullback

section Pairing

variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree'))

local notation "hqE" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E
local notation "hqE'" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E'

/-- `f^* π^* Sym^k(E) ≅ π'^* Sym^k(E')`, through `f ≫ π = π'` and `Sym^k(e)`. -/
public abbrev symPullbackIso (k : ℤ) :
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).obj
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
          ((bundleAlgebra E hfree).piece k)) ≅
      (Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).obj
        ((bundleAlgebra E' hfree').piece k) :=
  pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e) _ ≪≫
    (Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).mapIso
      (symIso hfree hfree' e k)

/-- The homogeneous-section maps under `e`, in the form of a transpose along `f`. -/
public theorem psi_restrict_iso (k : ℕ) :
    D.ψ k ≫ pushforwardRestrictMap (bundleMap hfree hfree' e) _ _
        (bundleMap_comp_toBase hfree hfree' e) (D.algebra.piece (k : ℤ)) ≫
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).map
          ((bundleTwistIso hfree hfree' e D D').hom.app (k : ℤ)) =
      (symHom hfree hfree' e.hom).app (k : ℤ) ≫ D'.ψ k :=
  bundleTwistIso_psi hfree hfree' e D D' k

/-- The pullback of the transpose of `Sym^k(E) ⟶ π_* 𝒪(k)` along `f`. -/
public theorem psiFlat_pullback_aux (k : ℕ) :
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (relativeProj (bundleAlgebra E hfree)).toBase).homEquiv _ _).symm (D.ψ k)) ≫
        (twistPullbackIso hfree hfree' e D D' (k : ℤ)).hom =
      (pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((bundleAlgebra E hfree).piece (k : ℤ))).hom ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (relativeProj (bundleAlgebra E' hfree')).toBase).homEquiv _ _).symm
          ((symHom hfree hfree' e.hom).app (k : ℤ) ≫ D'.ψ k) :=
  pullback_homEquiv_symm (bundleMap hfree hfree' e) _ _
    (bundleMap_comp_toBase hfree hfree' e) (twistPullbackIso hfree hfree' e D D' (k : ℤ)).hom
    (D.ψ k) ((symHom hfree hfree' e.hom).app (k : ℤ) ≫ D'.ψ k)
    (fun U s => pullbackUnit_restrict_comp (bundleMap hfree hfree' e) _ _
      (bundleMap_comp_toBase hfree hfree' e)
      ((bundleTwistIso hfree hfree' e D D').hom.app (k : ℤ)) _ _
      (psi_restrict_iso hfree hfree' e D D' k) U s)

/-- `psiFlat E D k` is the transpose of `D.ψ k` under the pullback-pushforward adjunction. -/
public theorem psiFlat_eq (k : ℕ) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    psiFlat E hqE D k = ((Scheme.Modules.pullbackPushforwardAdjunction
          (relativeProj (bundleAlgebra E hfree)).toBase).homEquiv _ _).symm (D.ψ k) :=
  rfl

/-- `Sym^k(e)` on pullbacks, as an isomorphism and as a morphism. -/
public theorem symPullback_mapIso_hom (k : ℤ) :
    ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).mapIso
        (symIso hfree hfree' e k)).hom =
      (Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).map
        ((symHom hfree hfree' e.hom).app k) := rfl

/-- `f^* π^* Sym^k E ≅ π'^* Sym^k E ≅ π'^* Sym^k E'`, as a composite. -/
public theorem symPullbackIso_trans_hom (k : ℤ) :
    ((pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((bundleAlgebra E hfree).piece k)) ≪≫
        (Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).mapIso
          (symIso hfree hfree' e k)).hom =
      (pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((bundleAlgebra E hfree).piece k)).hom ≫
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).mapIso
          (symIso hfree hfree' e k)).hom :=
  Iso.trans_hom _ _

/-- `symPullbackIso` unfolded. -/
public theorem symPullbackIso_hom_eq_trans (k : ℤ) :
    (symPullbackIso hfree hfree' e k).hom =
      ((pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((bundleAlgebra E hfree).piece k)) ≪≫
        (Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).mapIso
          (symIso hfree hfree' e k)).hom :=
  rfl

/-- `symPullbackIso` as a composite. -/
public theorem symPullbackIso_hom (k : ℤ) :
    (symPullbackIso hfree hfree' e k).hom =
      (pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((bundleAlgebra E hfree).piece k)).hom ≫
        (Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).map
          ((symHom hfree hfree' e.hom).app k) :=
  (symPullbackIso_hom_eq_trans hfree hfree' e k).trans
    ((symPullbackIso_trans_hom hfree hfree' e k).trans
      (congrArg ((pullbackPullbackIso (bundleMap hfree hfree' e) _ _
          (bundleMap_comp_toBase hfree hfree' e) ((bundleAlgebra E hfree).piece k)).hom ≫ ·)
        (symPullback_mapIso_hom hfree hfree' e k)))

/-- **The adjoints `π^* Sym^k(E) ⟶ 𝒪(k)` of the homogeneous-section maps correspond under `e`.** -/
public theorem psiFlat_pullback (k : ℕ) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map (psiFlat E hqE D k) ≫
        (twistPullbackIso hfree hfree' e D D' (k : ℤ)).hom =
      (symPullbackIso hfree hfree' e (k : ℤ)).hom ≫ psiFlat E' hqE' D' k :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  (congrArg (fun x => (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map x ≫
      (twistPullbackIso hfree hfree' e D D' (k : ℤ)).hom) (psiFlat_eq hfree D k)).trans
    ((psiFlat_pullback_aux hfree hfree' e D D' k).trans
    ((comp_homEquiv_symm_comp (p' := (relativeProj (bundleAlgebra E' hfree')).toBase)
      (pullbackPullbackIso (bundleMap hfree hfree' e) _ _
          (bundleMap_comp_toBase hfree hfree' e) _).hom ((symHom hfree hfree' e.hom).app (k : ℤ))
      (D'.ψ k)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg₂ (· ≫ ·) (symPullbackIso_hom hfree hfree' e (k : ℤ)).symm
          (psiFlat_eq hfree' D' k).symm))))

/-- The multiplication pairing as a composite. -/
public theorem twistPairing_eq (k : ℕ) (d c : ℤ) (hc : d + k = c) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    twistPairing E hqE D k d c hc =
      tensorMap (Z := (bundle E hqE).toRingedSpace) (𝟙 (D.algebra.piece d)) (psiFlat E hqE D k) ≫
        twistMul D d k ≫ eqToHom (congrArg D.algebra.piece hc) := by
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have h : tensorMap (Z := (bundle E hqE).toRingedSpace) (𝟙 (D.algebra.piece d))
      (psiFlat E hqE D k) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(bundle E hqE).toRingedSpace.presheaf, (bundle E hqE).toRingedSpace.IsSheaf⟩).obj
          (D.algebra.piece d)).map (psiFlat E hqE D k) :=
    Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(bundle E hqE).toRingedSpace.presheaf, (bundle E hqE).toRingedSpace.IsSheaf⟩)
      (D.algebra.piece d) (psiFlat E hqE D k)
  rw [h]
  rfl

/-- **The multiplication pairings `𝒪(d) ⊗ π^* Sym^k(E) ⟶ 𝒪(d + k)` correspond under `e`.** -/
public theorem twistPairing_pullback (k : ℕ) (d c : ℤ) (hc : d + k = c) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map (twistPairing E hqE D k d c hc) ≫
        (twistPullbackIso hfree hfree' e D D' c).hom =
      (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' d) (symPullbackIso hfree hfree' e (k : ℤ))).hom ≫
        twistPairing E' hqE' D' k d c hc := by
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  have h₁ : (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
        (tensorMap (Z := (bundle E hqE).toRingedSpace) (𝟙 (D.algebra.piece d))
          (psiFlat E hqE D k)) ≫
        (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' d)
          (twistPullbackIso hfree hfree' e D D' (k : ℤ))).hom =
      (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' d) (symPullbackIso hfree hfree' e (k : ℤ))).hom ≫
        tensorMap (Z := (bundle E' hqE').toRingedSpace) (𝟙 (D'.algebra.piece d))
          (psiFlat E' hqE' D' k) :=
    pullback_tensorMap_id_left_tensorPullbackIso (bundleMap hfree hfree' e)
      (twistPullbackIso hfree hfree' e D D' d) (symPullbackIso hfree hfree' e (k : ℤ))
      (twistPullbackIso hfree hfree' e D D' (k : ℤ)) _ _ (psiFlat_pullback hfree hfree' e D D' k)
  have h₂ := twistPullbackIso_twistMul' hfree hfree' e D D' d (k : ℤ)
  have h₃ :=
    twist_eqToHom_pullback (bundleMap hfree hfree' e) (twistPullbackIso hfree hfree' e D D') hc
  have h := paste_three _ _ _ _ _ _ _ _ _ _ h₁.symm h₂.symm h₃.symm
  have hm : (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
        (tensorMap (Z := (bundle E hqE).toRingedSpace) (𝟙 (D.algebra.piece d))
          (psiFlat E hqE D k) ≫ twistMul D d k ≫ eqToHom (congrArg D.algebra.piece hc)) =
      (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
          (tensorMap (Z := (bundle E hqE).toRingedSpace) (𝟙 (D.algebra.piece d))
            (psiFlat E hqE D k)) ≫
        (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map (twistMul D d k) ≫
        (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
          (eqToHom (congrArg D.algebra.piece hc)) :=
    ((Scheme.Modules.pullback (bundleMap hfree hfree' e)).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((Scheme.Modules.pullback (bundleMap hfree hfree' e)).map_comp _ _))
  refine (congrArg (fun x => (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map x ≫
    (twistPullbackIso hfree hfree' e D D' c).hom) (twistPairing_eq hfree D k d c hc)).trans ?_
  refine (congrArg (· ≫ (twistPullbackIso hfree hfree' e D D' c).hom) hm).trans ?_
  refine h.symm.trans ?_
  exact congrArg (_ ≫ ·) (twistPairing_eq hfree' D' k d c hc).symm

variable (k : ℕ)
  [hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((bundleAlgebra E hfree).piece (k : ℤ))]
  [hA' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((bundleAlgebra E' hfree').piece (k : ℤ))]
  [hdA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))]
  [hdA' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf ((bundleAlgebra E' hfree').piece (k : ℤ)))]

omit hA hA' hdA hdA' in
/-- `(Sym^k E)^∨ ≅ (Sym^k E')^∨` is the dual of `Sym^k(e⁻¹)`. -/
public theorem symDualIso_hom :
    (symDualIso hfree hfree' e k).hom =
      Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (symIso hfree hfree' e (k : ℤ)).inv :=
  rfl

end Pairing

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk

/-!
# The quasi-coherent sections equalizer condition and global sections of pullbacks

This file defines `AlgebraicGeometry.IsQuasicoherentSectionsEqualizer`, the global-section
equalizer condition for a family of morphisms of affine schemes, and collects the
global-section lemmas for pullbacks of modules used later: compatibility with units,
scalars, composition and isomorphisms, the global sections of the base change of a direct
image along an affine morphism, and the global sections of the pullback of `M~` along
`Spec S ⟶ Spec R`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

open scoped ChangeOfRings TensorProduct

/-- The global-section equalizer condition for a family of morphisms of affine schemes.
For every quasi-coherent module on the target, a compatible family of sections on the
members of the family descends uniquely to a global section on the target. -/
def IsQuasicoherentSectionsEqualizer {I : Type w} (X : AffineScheme.{u})
    (U : I → AffineScheme.{u}) (f : ∀ i, U i ⟶ X) : Prop :=
  ∀ (F : X.obj.Modules) [F.IsQuasicoherent]
    (s : ∀ i, Γ((Scheme.Modules.pullback
      (AffineScheme.forgetToScheme.map (f i))).obj F, ⊤)),
    (∀ i j,
      pullbackSectionsMap F (pairwiseFst X U f i j) (s i) =
        pullbackSectionsMap F (pairwiseSnd X U f i j) (s j)) →
      ∃! t : Γ(F, ⊤), ∀ i, pullbackGlobalSections
        (AffineScheme.forgetToScheme.map (f i)) F t = s i

namespace SectionsEqualizer

open Stacks.Ample (unitModule)

/-- Restricting a section of `M` along the equality `⊤ = f ⁻¹ᵁ ⊤` of opens of `X` is the
identity of `Γ(M, ⊤)`. -/
public theorem presheafMapTop_id {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    M.presheaf.map (eqToHom (f.preimage_top).symm).op = 𝟙 Γ(M, ⊤) := by
  rw [show (eqToHom (f.preimage_top).symm).op = CategoryTheory.CategoryStruct.id
    (Opposite.op (⊤ : X.Opens)) from rfl]
  exact M.presheaf.map_id _

/-- Restriction along the equality `⊤ = f ⁻¹ᵁ ⊤` fixes every global section of `M`. -/
public theorem presheafMapTop_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    (y : Γ(M, ⊤)) :
    M.presheaf.map (eqToHom (f.preimage_top).symm).op y = y :=
  (ConcreteCategory.congr_hom (presheafMapTop_id f M) y).trans (CategoryTheory.id_apply y)

private theorem pullbackMapTop_id {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (by simp : (⊤ : X.Opens) = f ⁻¹ᵁ ⊤)).op =
        𝟙 Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  presheafMapTop_id f ((Scheme.Modules.pullback f).obj M)

/-- A morphism of `𝒪_X`-modules commutes with restriction of sections along an inclusion of
opens `U ⟶ V`. -/
public lemma moduleHom_app_restrict {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    {U V : X.Opens} (i : U ⟶ V) (y : Γ(M, V)) :
    a.app U (M.presheaf.map i.op y) = N.presheaf.map i.op (a.app V y) :=
  ConcreteCategory.congr_hom (a.mapPresheaf.naturality i.op) y

/-- A morphism of `𝒪_X`-modules acts on the sections over `f ⁻¹ᵁ ⊤` as it does on global
sections. -/
public lemma moduleHom_app_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : X.Modules} (a : M ⟶ N) (y : Γ(M, ⊤)) :
    a.app (f ⁻¹ᵁ ⊤) y = a.app ⊤ y :=
  ((presheafMapTop_apply f N (a.app (f ⁻¹ᵁ ⊤) y)).symm.trans
    (moduleHom_app_restrict a (eqToHom (by simp : (⊤ : X.Opens) = f ⁻¹ᵁ ⊤)) y).symm).trans
      (congrArg (fun z => a.app ⊤ z) (presheafMapTop_apply f M y))

/-- On global sections, the forward map of an isomorphism of modules undoes its inverse. -/
public lemma moduleIso_hom_inv_app {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (y : Γ(G, ⊤)) : e.hom.app ⊤ (e.inv.app ⊤ y) = y :=
  (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (Iso.inv_hom_id e)) y).trans
      (CategoryTheory.id_apply y)

private lemma moduleIso_inv_hom_app {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (y : Γ(F, ⊤)) : e.inv.app ⊤ (e.hom.app ⊤ y) = y :=
  (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (Iso.hom_inv_id e)) y).trans
      (CategoryTheory.id_apply y)

/-- The pullback of a global section of `F` along `f` is its image under the unit of the
pullback–pushforward adjunction. -/
public lemma pullbackGlobalSections_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) (s : Γ(F, ⊤)) :
    pullbackGlobalSections f F s =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app ⊤ s :=
  presheafMapTop_apply f ((Scheme.Modules.pullback f).obj F)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app ⊤ s)

/-- Under the identification `Scheme.Modules.pullbackUnitIso f` of the pullback of the
structure sheaf with the structure sheaf, the pullback of a global function `s` on `Y` is
`f.appTop s`. -/
public lemma pullbackUnitIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) :
    (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
      (pullbackGlobalSections f (unitModule Y) s) = f.appTop s := by
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have h : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (unitModule Y) ≫
      (Scheme.Modules.pushforward f).map (Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      f.toRingCatSheafHom
  have he := congrArg (fun k => k.app ⊤ s) h
  change (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (unitModule Y)).app ⊤ s) = f.app ⊤ s at he
  exact (congrArg (fun z => (Scheme.Modules.pullbackUnitIso f).hom.app ⊤ z)
    (pullbackGlobalSections_unit f (unitModule Y) s)).trans he

/-- Pulling a global section back along `g` and then along `f` agrees, under
`Scheme.Modules.pullbackComp f g`, with pulling it back along `f ≫ g`. -/
public theorem pullbackGlobalSections_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules)
    (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤
      (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj F)
        (pullbackGlobalSections g F s)) =
      pullbackGlobalSections (f ≫ g) F s := by
  have h : ((Scheme.Modules.pullbackComp f g).inv.app F).app ((f ≫ g) ⁻¹ᵁ ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app F).app ⊤ s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj F)).app (g ⁻¹ᵁ ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app ⊤ s) :=
    congrArg (fun (t : F ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj F))) => t.app ⊤ s)
      (pullbackComp_unit f g F)
  have h2 : ((Scheme.Modules.pullbackComp f g).inv.app F).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app F).app ⊤ s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj F)).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app ⊤ s) :=
    (moduleHom_app_preimage_top (f ≫ g) _ _).symm.trans
      (h.trans (moduleHom_app_preimage_top g _ _))
  have hid : ∀ w : Γ((Scheme.Modules.pullback (f ≫ g)).obj F, ⊤),
      ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤
        (((Scheme.Modules.pullbackComp f g).inv.app F).app ⊤ w) = w :=
    moduleIso_hom_inv_app ((Scheme.Modules.pullbackComp f g).app F)
  calc
    _ = ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            ((Scheme.Modules.pullback g).obj F)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app ⊤ s)) := by
        refine congrArg (fun z => ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤ z) ?_
        exact (pullbackGlobalSections_unit f ((Scheme.Modules.pullback g).obj F) _).trans
          (congrArg
            (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              ((Scheme.Modules.pullback g).obj F)).app ⊤ z)
            (pullbackGlobalSections_unit g F s))
    _ = ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤
        (((Scheme.Modules.pullbackComp f g).inv.app F).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app F).app ⊤ s)) :=
        congrArg (fun z => ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤ z) h2.symm
    _ = _ := (hid _).trans (pullbackGlobalSections_unit (f ≫ g) F s).symm

private lemma pullbackSectionsMap_apply_unit {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y)
    (s : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    pullbackSectionsMap F g s =
      (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
            ((Scheme.Modules.pullback Y.hom).obj F) ≫
          (Scheme.Modules.pushforward g.left).map
            ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
              (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F)).app ⊤) s :=
  presheafMapTop_apply g.left ((Scheme.Modules.pullback X.hom).obj F) _

private lemma pullbackSectionsMap_apply {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y)
    (s : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    pullbackSectionsMap F g s =
      ((Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).app ⊤
        (((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F).app ⊤
          (pullbackGlobalSections g.left ((Scheme.Modules.pullback Y.hom).obj F) s)) := by
  let M := (Scheme.Modules.pullback Y.hom).obj F
  let a : (Scheme.Modules.pullback g.left).obj M ⟶
      (Scheme.Modules.pullback X.hom).obj F :=
    (Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F
  let u := ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app M).app ⊤
  have h1 : pullbackSectionsMap F g s = a.app (g.left ⁻¹ᵁ ⊤) (u s) :=
    pullbackSectionsMap_apply_unit F g s
  have h2 : a.app (g.left ⁻¹ᵁ ⊤) (u s) = a.app ⊤ (u s) :=
    moduleHom_app_preimage_top g.left a (u s)
  exact h1.trans (h2.trans
    (congrArg (fun z => a.app ⊤ z) (pullbackGlobalSections_unit g.left M s)).symm)

/-- For `h : f = g`, pulling back a global section along `f` agrees with pulling it back
along `g` under `Scheme.Modules.pullbackCongr h`. -/
public lemma pullbackGlobalSections_congr {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (F : Y.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app F).app ⊤
      (pullbackGlobalSections f F s) = pullbackGlobalSections g F s := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

lemma pullbackSectionsMap_global {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y) (s : Γ(F, ⊤)) :
    pullbackSectionsMap F g (pullbackGlobalSections Y.hom F s) =
      pullbackGlobalSections X.hom F s := by
  rw [pullbackSectionsMap_apply, pullbackGlobalSections_comp,
    pullbackGlobalSections_congr]

lemma moduleHom_app_smul {X : Scheme.{u}} {F G : X.Modules}
    (b : F ⟶ G) (r : Γ(X, ⊤)) (s : Γ(F, ⊤)) :
    b.app ⊤ (r • s) = r • b.app ⊤ s :=
  (b.val.app (op ⊤)).hom.map_smul r s

private lemma pushforwardHom_app_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Y.Modules} {G : X.Modules} (b : F ⟶ (Scheme.Modules.pushforward g).obj G)
    (r : Γ(Y, ⊤)) (s : Γ(F, ⊤)) :
    b.app ⊤ (r • s) = g.appTop r • (show Γ(G, ⊤) from b.app ⊤ s) :=
  moduleHom_app_smul b r s

/-- Pulling back global sections along `f` is semilinear over `f.appTop`: the pullback of
`r • s` is `f.appTop r • t`, where `t` is the pullback of `s`. -/
public lemma pullbackGlobalSections_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) (r : Γ(Y, ⊤)) (s : Γ(F, ⊤)) :
    pullbackGlobalSections f F (r • s) =
      f.appTop r • pullbackGlobalSections f F s := by
  have h := pushforwardHom_app_smul f
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) r s
  unfold pullbackGlobalSections
  rw [pullbackMapTop_id]
  exact h

private lemma pullbackGlobalSections_comp_smul {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules)
    (r : Γ(Y, ⊤)) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤
      (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj F)
        (r • pullbackGlobalSections g F s)) =
      f.appTop r • pullbackGlobalSections (f ≫ g) F s := by
  rw [pullbackGlobalSections_smul]
  rw [moduleHom_app_smul]
  exact congrArg (fun t => f.appTop r • t) (pullbackGlobalSections_comp f g F s)

lemma pullbackSectionsMap_smul {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y) (r : Γ(Y.left, ⊤))
    (s : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    pullbackSectionsMap F g (r • s) =
      g.left.appTop r • pullbackSectionsMap F g s := by
  let a := (Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
    (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F
  let b := (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
    ((Scheme.Modules.pullback Y.hom).obj F) ≫ (Scheme.Modules.pushforward g.left).map a
  exact (pullbackSectionsMap_apply_unit F g (r • s)).trans
    ((pushforwardHom_app_smul g.left b r s).trans
      (congrArg (fun z => g.left.appTop r • z)
        (pullbackSectionsMap_apply_unit F g s).symm))

private lemma moduleIso_app_injective {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) : Function.Injective (e.hom.app ⊤) :=
  ((ConcreteCategory.isIso_iff_bijective _).mp
    ((Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (inferInstance : IsIso e.hom)) ⊤)).1

/-- The unit isomorphism sends `r • (pullback of 1)` to `r`. -/
private lemma pullbackUnitIso_smul_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(X, ⊤)) :
    (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
      (r • pullbackGlobalSections f (unitModule Y) (1 : Γ(Y, ⊤))) = r :=
  (moduleHom_app_smul _ r _).trans
    ((congrArg (fun z => r • z) (pullbackUnitIso_unit f 1)).trans
      (by simp : r • f.appTop (1 : Γ(Y, ⊤)) = r))

private lemma pullbackSectionsMap_unit {S : Scheme.{u}} {X Y : Over S}
    (g : X ⟶ Y) (s : Γ((Scheme.Modules.pullback Y.hom).obj (unitModule S), ⊤)) :
    (Scheme.Modules.pullbackUnitIso X.hom).hom.app ⊤
      (pullbackSectionsMap (unitModule S) g s) =
      g.left.appTop ((Scheme.Modules.pullbackUnitIso Y.hom).hom.app ⊤ s) := by
  let F := unitModule S
  let r : Γ(Y.left, ⊤) := (Scheme.Modules.pullbackUnitIso Y.hom).hom.app ⊤ s
  have hs : s = r • pullbackGlobalSections Y.hom F (1 : Γ(S, ⊤)) :=
    moduleIso_app_injective (Scheme.Modules.pullbackUnitIso Y.hom)
      (pullbackUnitIso_smul_unit Y.hom r).symm
  calc _ = (Scheme.Modules.pullbackUnitIso X.hom).hom.app ⊤ (pullbackSectionsMap F g
        (r • pullbackGlobalSections Y.hom F (1 : Γ(S, ⊤)))) := by rw [← hs]
    _ = _ := by
      rw [pullbackSectionsMap_smul,
        pullbackSectionsMap_global F g (1 : Γ(S, ⊤))]
      exact pullbackUnitIso_smul_unit X.hom _

-- Specialising the equalizer condition at the unit module unfolds both canonical
-- pullback maps on global sections through the pullback--pushforward adjunction.
theorem ringSectionsEqualizer_of_quasicoherentSectionsEqualizer
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) (h : IsQuasicoherentSectionsEqualizer X U f)
    (x : ∀ i, Γ((U i).obj, ⊤))
    (hx : ∀ i j,
      (pairwiseFst X U f i j).left.appTop (x i) =
        (pairwiseSnd X U f i j).left.appTop (x j)) :
    ∃! a : Γ(X.obj, ⊤), ∀ i,
      (AffineScheme.forgetToScheme.map (f i)).appTop a = x i := by
  let F := unitModule X.obj
  let : F.IsQuasicoherent := inferInstance
  let s (i) :=
    (Scheme.Modules.pullbackUnitIso (AffineScheme.forgetToScheme.map (f i))).inv.app ⊤ (x i)
  have hi (i) : (Scheme.Modules.pullbackUnitIso (AffineScheme.forgetToScheme.map (f i))).hom.app ⊤
      (s i) = x i :=
    moduleIso_hom_inv_app
      (Scheme.Modules.pullbackUnitIso (AffineScheme.forgetToScheme.map (f i))) (x i)
  have hs : ∀ i j,
      pullbackSectionsMap F (pairwiseFst X U f i j) (s i) =
        pullbackSectionsMap F (pairwiseSnd X U f i j) (s j) := by
    intro i j
    apply moduleIso_app_injective (Scheme.Modules.pullbackUnitIso (pairwiseOver X U f i j).hom)
    exact ((((pullbackSectionsMap_unit (pairwiseFst X U f i j) (s i)).trans
      (congrArg (fun z => (pairwiseFst X U f i j).left.appTop z) (hi i))).trans
        (hx i j)).trans
      (congrArg (fun z => (pairwiseSnd X U f i j).left.appTop z) (hi j)).symm).trans
        (pullbackSectionsMap_unit (pairwiseSnd X U f i j) (s j)).symm
  obtain ⟨a, ha, hu⟩ := h F s hs
  refine ⟨a, ?_, ?_⟩
  · intro i
    exact (pullbackUnitIso_unit (AffineScheme.forgetToScheme.map (f i)) a).symm.trans
      ((congrArg (fun z =>
        (Scheme.Modules.pullbackUnitIso (AffineScheme.forgetToScheme.map (f i))).hom.app ⊤ z)
          (ha i)).trans (hi i))
  · intro b hb
    apply hu b
    intro i
    apply moduleIso_app_injective
      (Scheme.Modules.pullbackUnitIso (AffineScheme.forgetToScheme.map (f i)))
    exact (pullbackUnitIso_unit (AffineScheme.forgetToScheme.map (f i)) b).trans
      ((hb i).trans (hi i).symm)

private lemma pullbackGlobalSections_id {X : Scheme.{u}} (F : X.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackId X).hom.app F).app ⊤
      (pullbackGlobalSections (𝟙 X) F s) = s := by
  have h : ((Scheme.Modules.pullbackId X).hom.app F).app (𝟙 X ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F).app ⊤ s) = s :=
    congrArg (fun (t : F ⟶ (Scheme.Modules.pushforward (𝟙 X)).obj F) => t.app ⊤ s)
      (pullbackId_unit F)
  exact (congrArg (fun z => ((Scheme.Modules.pullbackId X).hom.app F).app ⊤ z)
      (pullbackGlobalSections_unit (𝟙 X) F s)).trans
    ((moduleHom_app_preimage_top (𝟙 X)
      ((Scheme.Modules.pullbackId X).hom.app F) _).symm.trans h)

/-- Pulling a global section back along an isomorphism `f` and then along `inv f` recovers it,
under the canonical identifications of the iterated pullback with `F`. -/
private lemma pullbackGlobalSections_inv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (F : Y.Modules) (t : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackId Y).hom.app F).app ⊤
      (((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).hom.app F).app ⊤
        (((Scheme.Modules.pullbackComp (inv f) f).hom.app F).app ⊤
          (pullbackGlobalSections (inv f) ((Scheme.Modules.pullback f).obj F)
            (pullbackGlobalSections f F t)))) = t := by
  rw [pullbackGlobalSections_comp, pullbackGlobalSections_congr, pullbackGlobalSections_id]

private lemma pullbackGlobalSections_injective_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (F : Y.Modules) :
    Function.Injective (pullbackGlobalSections f F) := by
  intro s t h
  have hs := pullbackGlobalSections_inv_comp f F s
  rw [h, pullbackGlobalSections_inv_comp] at hs
  exact hs.symm

lemma pullbackGlobalSections_bijective_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (F : Y.Modules) :
    Function.Bijective (pullbackGlobalSections f F) := by
  refine ⟨pullbackGlobalSections_injective_of_isIso f F, ?_⟩
  let e : (Scheme.Modules.pullback (inv f)).obj ((Scheme.Modules.pullback f).obj F) ≅ F :=
    (Scheme.Modules.pullbackComp (inv f) f).app F ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).app F ≪≫
        (Scheme.Modules.pullbackId Y).app F
  intro s
  refine ⟨e.hom.app ⊤
    (pullbackGlobalSections (inv f) ((Scheme.Modules.pullback f).obj F) s), ?_⟩
  apply pullbackGlobalSections_injective_of_isIso (inv f) ((Scheme.Modules.pullback f).obj F)
  apply moduleIso_app_injective e
  exact pullbackGlobalSections_inv_comp f F _

/-- The identity that characterises the base-change morphism as a mate: composed with the unit
of `(g')^* ⊣ (g')_*` pushed forward along `f`, the comparison of the two composite direct
images around the square is the unit of `g^* ⊣ g_*` followed by `g_*` of the base-change
morphism. -/
private lemma unit_baseChangeNatTrans {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M) ≫
      (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app
        ((Scheme.Modules.pullback g').obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.pushforward g).map
        ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app M) :=
  CategoryTheory.unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom M

/-- On sections over the whole space the comparison of the two composite direct images around a
commutative square is the identity: it is transport along an equality of opens, and over the
whole space both of those opens are the whole space. -/
private lemma pushforwardSquareIso_app_top {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) (N : X'.Modules)
    (b : N.val.obj (op (⊤ : X'.Opens))) :
    ((Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app N).val.app
      (op (⊤ : S.Opens)) b = b := by
  have E : (f' ≫ g) ⁻¹ᵁ (⊤ : S.Opens) = (g' ≫ f) ⁻¹ᵁ (⊤ : S.Opens) := by rw [w]
  have h : ((Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
        w).hom.app N).val.app (op (⊤ : S.Opens)) b =
      ConcreteCategory.hom (N.presheaf.map (eqToHom E).op) b := rfl
  have h2 : ((eqToHom E).op : op ((g' ≫ f) ⁻¹ᵁ (⊤ : S.Opens)) ⟶
      op ((f' ≫ g) ⁻¹ᵁ (⊤ : S.Opens))) = 𝟙 _ := Subsingleton.elim _ _
  have h3 : N.presheaf.map ((eqToHom E).op) = N.presheaf.map (𝟙 _) := congrArg _ h2
  rw [h, h3, N.presheaf.map_id]
  rfl

/-- The base-change morphism carries the pullback of a global section to the pullback of that
global section, for an arbitrary commutative square of schemes. -/
private lemma baseChangeNatTrans_unit_top {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) (M : X.Modules)
    (a : Γ(M, ⊤)) :
    ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app M).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pushforward f).obj M)).app ⊤ a) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M).app ⊤ a := by
  have h := congrArg (fun t : (Scheme.Modules.pushforward f).obj M ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj M)) =>
      t.val.app (op (⊤ : S.Opens)) a) (unit_baseChangeNatTrans w M)
  exact h.symm.trans (pushforwardSquareIso_app_top w ((Scheme.Modules.pullback g').obj M)
    (((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M)).val.app
        (op (⊤ : S.Opens)) a))

private lemma baseChangeNatTrans_global (d : AlgebraicGeometry.BaseChangeDiagram.{u})
    (s : Γ(d.F, ⊤)) :
    ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      d.isPullback.w).app d.F).app ⊤
      (pullbackGlobalSections d.g ((Scheme.Modules.pushforward d.f).obj d.F) s) =
      pullbackGlobalSections d.g' d.F s :=
  (congrArg (fun z => ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        d.isPullback.w).app d.F).app ⊤ z)
      (pullbackGlobalSections_unit d.g
        ((Scheme.Modules.pushforward d.f).obj d.F) s)).trans
    ((baseChangeNatTrans_unit_top d.isPullback.w d.F s).trans
      (pullbackGlobalSections_unit d.g' d.F s).symm)

/-- The canonical affine base-change isomorphism `g^* f_* F ≅ f'_* (g')^* F` attached to a
cartesian square whose right-hand morphism is affine. -/
noncomputable def affineBaseChangeIso (d : AlgebraicGeometry.BaseChangeDiagram.{u})
    [IsAffineHom d.f] :
    (Scheme.Modules.pullback d.g).obj ((Scheme.Modules.pushforward d.f).obj d.F) ≅
      (Scheme.Modules.pushforward d.f').obj d.pulledBack :=
  letI := d.isQuasicoherent
  letI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    d.isPullback d.F
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans d.isPullback.w).app d.F)

noncomputable def affineBaseChangeSectionsIso
    (d : AlgebraicGeometry.BaseChangeDiagram.{u}) [IsAffineHom d.f] :
    Γ((Scheme.Modules.pullback d.g).obj ((Scheme.Modules.pushforward d.f).obj d.F), ⊤) ≅
      Γ((Scheme.Modules.pullback d.g').obj d.F, ⊤) :=
  @asIso _ _ _ _ ((affineBaseChangeIso d).hom.app ⊤)
    ((Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (inferInstance : IsIso (affineBaseChangeIso d).hom)) ⊤)

lemma affineBaseChangeSectionsIso_global
    (d : AlgebraicGeometry.BaseChangeDiagram.{u}) [IsAffineHom d.f] (s : Γ(d.F, ⊤)) :
    (affineBaseChangeSectionsIso d).hom
      (pullbackGlobalSections d.g ((Scheme.Modules.pushforward d.f).obj d.F) s) =
      pullbackGlobalSections d.g' d.F s :=
  baseChangeNatTrans_global d s

lemma affineBaseChangeSectionsIso_smul
    (d : AlgebraicGeometry.BaseChangeDiagram.{u}) [IsAffineHom d.f]
    (r : Γ(d.S', ⊤)) (s : Γ(d.F, ⊤)) :
    (affineBaseChangeSectionsIso d).hom
      (r • pullbackGlobalSections d.g ((Scheme.Modules.pushforward d.f).obj d.F) s) =
      d.f'.appTop r • pullbackGlobalSections d.g' d.F s :=
  (pushforwardHom_app_smul d.f' ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      d.isPullback.w).app d.F) r
      (pullbackGlobalSections d.g ((Scheme.Modules.pushforward d.f).obj d.F) s)).trans
    (congrArg (fun t => d.f'.appTop r • t) (baseChangeNatTrans_global d s))

private theorem affinePullbackGlobalSections_tilde
    (R S : CommRingCat.{u}) (f : R ⟶ S) (M : ModuleCat R) (m : M) :
    (((AlgebraicGeometry.pullbackTildeIso R S f).hom.app M).val.app
      (.op (⊤ : (Spec S).Opens)))
      (pullbackGlobalSections (Spec.map f) ((tilde.functor R).obj M)
        (tilde.toOpen M ⊤ m)) =
      tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
        ((1 : S) ⊗ₜ[R, f.hom] m) := by
  unfold pullbackGlobalSections
  simp only [Scheme.Modules.Hom.app]
  rw [pullbackMapTop_id]
  exact AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen R S f M m

private theorem affineModuleSection_representative {R : CommRingCat.{u}}
    (F : (Spec R).Modules)
    (s : (modulesSpecToSheaf.obj F).presheaf.obj (op (⊤ : (Spec R).Opens))) :
    ((modulesSpecToSheaf.map F.fromTildeΓ).hom.app (op (⊤ : (Spec R).Opens))).hom
      ((tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (op ⊤)) ⊤).hom s) = s := by
  simpa using congr($(Scheme.Modules.toOpen_fromTildeΓ_app F ⊤).hom s)

private noncomputable def affineGlobalSectionsIso {R : CommRingCat.{u}}
    (F : (Spec R).Modules) [F.IsQuasicoherent] :
    moduleSpecΓFunctor.obj F ≅ ModuleCat.of R Γ(F, ⊤) := by
  letI : IsIso F.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  have hmap : IsIso (moduleSpecΓFunctor.map F.fromTildeΓ) :=
    Functor.map_isIso moduleSpecΓFunctor F.fromTildeΓ
  letI : IsIso (moduleSpecΓFunctor.map F.fromTildeΓ) := hmap
  exact tilde.isoTop (moduleSpecΓFunctor.obj F) ≪≫
    @CategoryTheory.asIso _ _ _ _ (moduleSpecΓFunctor.map F.fromTildeΓ) hmap

-- For an arbitrary quasi-coherent module on an affine scheme, identify sections
-- after pullback with extension of scalars on the associated module.  The
-- comparison is assembled from the counit of the tilde--Gamma adjunction and
-- the canonical pullback comparison proved above.
lemma affinePullbackSectionsIso_unit (R S : CommRingCat.{u})
    (f : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent]
    (m : moduleSpecΓFunctor.obj F) :
    (Stacks.Cech.affinePullbackSectionsIso R S f F).hom ((1 : S) ⊗ₜ[R, f.hom] m) =
      pullbackGlobalSections (Spec.map f) F m := by
  let M := moduleSpecΓFunctor.obj F
  let eT := (AlgebraicGeometry.pullbackTildeIso R S f).app M
  have h := affinePullbackGlobalSections_tilde R S f M m
  have h' : eT.inv.app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤ ((1 : S) ⊗ₜ[R, f.hom] m)) =
      pullbackGlobalSections (Spec.map f) ((tilde.functor R).obj M) (tilde.toOpen M ⊤ m) := by
    rw [← h]
    show (eT.hom ≫ eT.inv).app ⊤
      (pullbackGlobalSections (Spec.map f) ((tilde.functor R).obj M) (tilde.toOpen M ⊤ m)) = _
    simp
  show ((Scheme.Modules.pullback (Spec.map f)).map F.fromTildeΓ).app ⊤
    (eT.inv.app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤ ((1 : S) ⊗ₜ[R, f.hom] m))) = _
  rw [h']
  exact
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      (Spec.map f) F.fromTildeΓ (tilde.toOpen M ⊤ m)).symm.trans
      (congrArg (fun z => pullbackGlobalSections (Spec.map f) F z)
        (affineModuleSection_representative F m))

lemma affinePullbackSectionsIso_tmul (R S : CommRingCat.{u})
    (f : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent]
    (s : S) (m : moduleSpecΓFunctor.obj F) :
    (Stacks.Cech.affinePullbackSectionsIso R S f F).hom (s ⊗ₜ[R, f.hom] m) =
      s • pullbackGlobalSections (Spec.map f) F m := by
  let := f.hom.toAlgebra
  have h : (Stacks.Cech.affinePullbackSectionsIso R S f F).hom ((s * 1) ⊗ₜ[R, f.hom] m) =
      s • (Stacks.Cech.affinePullbackSectionsIso R S f F).hom ((1 : S) ⊗ₜ[R, f.hom] m) :=
    (Stacks.Cech.affinePullbackSectionsIso R S f F).hom.hom.map_smul s ((1 : S) ⊗ₜ[R] m)
  exact ((congrArg (fun z : S => (Stacks.Cech.affinePullbackSectionsIso R S f F).hom
      (z ⊗ₜ[R, f.hom] m)) (mul_one s)).symm.trans h).trans
    (congrArg (fun z => s • z) (affinePullbackSectionsIso_unit R S f F m))

private theorem affinePullbackSections_induction (R S : CommRingCat.{u})
    (f : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent]
    (P : Γ((Scheme.Modules.pullback (Spec.map f)).obj F, ⊤) → Prop)
    (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (s : S) (m : Γ(F, ⊤)), P (s • pullbackGlobalSections (Spec.map f) F m))
    (x : Γ((Scheme.Modules.pullback (Spec.map f)).obj F, ⊤)) : P x := by
  let := f.hom.toAlgebra
  obtain ⟨z, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso (Stacks.Cech.affinePullbackSectionsIso R S f F).hom)).2 x
  induction z using TensorProduct.induction_on with
  | zero =>
    exact (congrArg P (map_zero (Stacks.Cech.affinePullbackSectionsIso R S f F).hom.hom)).mpr hzero
  | tmul s m =>
    exact (congrArg P (affinePullbackSectionsIso_tmul R S f F s m)).mpr (hgen s m)
  | add a b ha hb =>
    exact (congrArg P (map_add (Stacks.Cech.affinePullbackSectionsIso R S f F).hom.hom a b)).mpr
      (hadd _ _ ha hb)

end SectionsEqualizer

end AlgebraicGeometry

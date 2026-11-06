module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeColimitSheafH
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections

/-!
# Global sections of the limit of base changes

Let `Y_a` be the base changes of `X` along a system `Z` of schemes over `T`, let `G_a` be the
level sheaves on `Y_a` of an abelian sheaf `F` on the small étale site of `X`, and let `Y` be a
limit of the `Y_a` with a map `p : Y ⟶ X`. Then `Γ(Y, p⁻¹ F)` is the colimit of the groups
`Γ(Y_a, G_a)` along the restriction maps. This is [stacks 03Q6] in degree zero: the degree-zero
case of `Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_cohomologyCocone`, transported
along the natural isomorphism `H^0(Y, G) ≅ Γ(Y, G)` given by evaluation at the canonical section of
`ℤ` over the final object.

## Main definitions

* `sheafHZeroIso`: The isomorphism `H^0(Y, G) ≅ Γ(Y, G)`.
* `gammaDiagram`: The diagram `a ↦ Γ(Y_a, G_a)` with the restriction maps `gammaTransition`.
* `gammaCocone`: The cocone with vertex `Γ(Y, p⁻¹ F)` and legs `gammaLeg`.
* `isColimitGammaCocone`: The cocone `gammaCocone` is a colimit cocone.

## Main results

* `sheafHZeroFun_naturality`: The map `H^0(Y, G) ⟶ Γ(Y, G)` commutes with restriction along
  a morphism of schemes.
* `isIso_colimitDesc_gammaCocone`: The canonical map from the colimit of `gammaDiagram` to
  `Γ(Y, p⁻¹ F)` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology.ColimitBaseChange

universe u

open Stacks.WeakSites.ExtColimit Stacks.Homology Stacks.EtaleCohomology.BaseChangeAlgebraSystem

/-- Sheafification of abelian groups at the object universe of the small étale site. -/
local instance hasSheafify_smallEtale_objectUniverse'''' (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Scheme.hasSheafify_smallEtaleTopology.{u, u + 1} Y

section Zero

variable {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology Ab.{u + 1})

/-- The final object of the small étale site. -/
abbrev etaleTop (Y : Scheme.{u}) : Y.Etale := Scheme.Etale.mk (𝟙 Y)

/-- `H^0(Y, G) ⟶ Γ(Y, G)`: the image of the canonical section of `ℤ` over the final object. -/
def sheafHZeroFun (x : Sheaf.H.{u + 1, u + 1} G 0) :
    (Sheaf.Γ Y.smallEtaleTopology Ab.{u + 1}).obj G :=
  (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1} (isTerminalEtaleMkId Y)).inv.app G
    ((Abelian.Ext.homEquiv₀ x).hom.app (op (etaleTop Y)) (constGen Y (etaleTop Y)))

/-- The map `sheafHZeroFun G` is additive. -/
theorem sheafHZeroFun_add (x y : Sheaf.H.{u + 1, u + 1} G 0) :
    sheafHZeroFun G (x + y) = sheafHZeroFun G x + sheafHZeroFun G y := by
  have h : Abelian.Ext.homEquiv₀ (x + y) = Abelian.Ext.homEquiv₀ x + Abelian.Ext.homEquiv₀ y :=
    map_add (Abelian.Ext.addEquiv₀ (X := constZ Y) (Y := G)) x y
  have h2 : (Abelian.Ext.homEquiv₀ (x + y)).hom.app (op (etaleTop Y)) (constGen Y (etaleTop Y)) =
      (Abelian.Ext.homEquiv₀ x).hom.app (op (etaleTop Y)) (constGen Y (etaleTop Y)) +
        (Abelian.Ext.homEquiv₀ y).hom.app (op (etaleTop Y)) (constGen Y (etaleTop Y)) := by
    rw [h]
    rfl
  simp only [sheafHZeroFun, h2, map_add]

/-- The map `sheafHZeroFun G : H^0(Y, G) ⟶ Γ(Y, G)` is bijective. -/
theorem bijective_sheafHZeroFun : Function.Bijective (sheafHZeroFun G) := by
  have h₁ := isCorepresentingSection_constZ Y (isTerminalEtaleMkId Y) G
  have h₂ : Function.Bijective ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
      (isTerminalEtaleMkId Y)).inv.app G) :=
    ConcreteCategory.bijective_of_isIso _
  exact h₂.comp (h₁.comp Abelian.Ext.homEquiv₀.bijective)

/-- The isomorphism `H^0(Y, G) ≅ Γ(Y, G)` given by `sheafHZeroFun`. -/
def sheafHZeroIso :
    AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} G 0) ≅
      (Sheaf.Γ Y.smallEtaleTopology Ab.{u + 1}).obj G :=
  (AddEquiv.ofBijective (AddMonoidHom.mk' (sheafHZeroFun G) (sheafHZeroFun_add G))
    (bijective_sheafHZeroFun G)).toAddCommGrpIso

/-- The forward map of `sheafHZeroIso G` is `sheafHZeroFun G`. -/
theorem sheafHZeroIso_hom_apply (x) : (sheafHZeroIso G).hom x = sheafHZeroFun G x := rfl

/-- The map `sheafHZeroFun` commutes with restriction along a morphism of schemes `f : X ⟶ Y`
followed by a morphism `e : f⁻¹ G ⟶ H`. -/
theorem sheafHZeroFun_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology Ab.{u + 1}} {H : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    (e : (smallEtalePullbackAb f).obj G ⟶ H) (x : Sheaf.H.{u + 1, u + 1} G 0) :
    sheafHZeroFun H (sheafHRestriction f e 0 x) =
      (Sheaf.Γ X.smallEtaleTopology Ab.{u + 1}).map e
        ((smallEtaleGlobalSectionsRestrictionAb f).app G (sheafHZeroFun G x)) := by
  let φ := Abelian.Ext.homEquiv₀ x
  have hT : IsTerminal (bcTop f) := isTerminal_bcTop f
  let r : etaleTop X ⟶ bcTop f := hT.from _
  let s := ((smallEtaleAdjunctionAb f).unit.app G).hom.app (op (etaleTop Y))
    (φ.hom.app (op (etaleTop Y)) (constGen Y (etaleTop Y)))
  have e1 : Abelian.Ext.homEquiv₀ (sheafHRestriction f e 0 x) =
      (constPullbackIso f).inv ≫ (smallEtalePullbackAb f).map φ ≫ e :=
    homEquiv₀_extConj_mapExactFunctor (smallEtalePullbackAb f) (constPullbackIso f).inv x e
  have e2 : (constPullbackIso f).inv.hom.app (op (etaleTop X)) (constGen X (etaleTop X)) =
      ((smallEtalePullbackAb f).obj (constZ Y)).obj.map r.op (pbGen f) := by
    rw [← constGen_restrict X r]
    have hn := ConcreteCategory.congr_hom ((constPullbackIso f).inv.hom.naturality r.op)
      (constGen X (bcTop f))
    have hk : (constPullbackIso f).inv.hom.app (op (bcTop f)) (constGen X (bcTop f)) = pbGen f := by
      rw [← constPullbackIso_hom_apply f, ← sheafHom_comp_apply, Iso.hom_inv_id]
      rfl
    exact hn.trans (congrArg (((smallEtalePullbackAb f).obj (constZ Y)).obj.map r.op) hk)
  have e3 : ((smallEtalePullbackAb f).map φ).hom.app (op (etaleTop X))
      (((smallEtalePullbackAb f).obj (constZ Y)).obj.map r.op (pbGen f)) =
      ((smallEtalePullbackAb f).obj G).obj.map r.op s := by
    have hn := ConcreteCategory.congr_hom (((smallEtalePullbackAb f).map φ).hom.naturality r.op)
      (pbGen f)
    exact hn.trans (congrArg _ (map_unit_app f φ (etaleTop Y) (constGen Y (etaleTop Y))))
  have hlift : (smallEtaleBaseChangeLift f (Scheme.Etale.mk (𝟙 Y)) f (Category.comp_id f)) = r :=
    hT.hom_ext _ _
  have e4 : (smallEtaleGlobalSectionsRestrictionAb f).app G (sheafHZeroFun G x) =
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology Ab.{u + 1} (isTerminalEtaleMkId X)).inv.app
        ((smallEtalePullbackAb f).obj G) (((smallEtalePullbackAb f).obj G).obj.map r.op s) := by
    change (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology Ab.{u + 1}
      (isTerminalEtaleMkId X)).inv.app _
        (((smallEtalePullbackAb f).obj G).obj.map
          (smallEtaleBaseChangeLift f (Scheme.Etale.mk (𝟙 Y)) f (Category.comp_id f)).op
          (((smallEtaleAdjunctionAb f).unit.app G).hom.app (op (etaleTop Y))
            ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
              (isTerminalEtaleMkId Y)).hom.app G
              ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology Ab.{u + 1}
                (isTerminalEtaleMkId Y)).inv.app G
                (φ.hom.app (op (etaleTop Y)) (constGen Y (etaleTop Y))))))) = _
    rw [hlift, Iso.inv_hom_id_app_apply]
  rw [e4]
  have hΓ := ConcreteCategory.congr_hom ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology Ab.{u + 1}
    (isTerminalEtaleMkId X)).inv.naturality e)
    (((smallEtalePullbackAb f).obj G).obj.map r.op s)
  refine Eq.trans ?_ hΓ
  change (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology Ab.{u + 1}
    (isTerminalEtaleMkId X)).inv.app H
    ((Abelian.Ext.homEquiv₀ (sheafHRestriction f e 0 x)).hom.app (op (etaleTop X))
      (constGen X (etaleTop X))) = _
  rw [e1]
  change _ = (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology Ab.{u + 1}
    (isTerminalEtaleMkId X)).inv.app H (e.hom.app (op (etaleTop X)) _)
  congr 1
  change e.hom.app _ (((smallEtalePullbackAb f).map φ).hom.app _
    ((constPullbackIso f).inv.hom.app _ (constGen X (etaleTop X)))) = _
  rw [e2, e3]

end Zero

section Gamma

variable {I : Type u} [Preorder I] (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  (F : Sheaf X.left.smallEtaleTopology Ab.{u + 1})

/-- The restriction map `gammaTransition` corresponds under `sheafHZeroFun` to the transition
map `cohomologyTransition` in degree zero. -/
theorem gammaTransition_sheafHZeroFun {i j : Iᵒᵖ} (f : i ⟶ j)
    (x : Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F j) 0) :
    gammaTransition T X Z F f (sheafHZeroFun _ x) =
      sheafHZeroFun _ (cohomologyTransition T X Z F f 0 x) :=
  (sheafHZeroFun_naturality _ _ x).symm

/-- The map `sheafHZeroFun` on the level sheaf over `Y_i` is surjective. -/
theorem surjective_sheafHZeroFun_level (i : Iᵒᵖ) :
    Function.Surjective (sheafHZeroFun (levelSheaf T X Z F i)) :=
  (bijective_sheafHZeroFun _).2

/-- The diagram `a ↦ Γ(Y_a, G_a)`, with the restriction maps `gammaTransition`. -/
def gammaDiagram : Iᵒᵖᵒᵖ ⥤ Ab.{u + 1} where
  obj a := (Sheaf.Γ ((baseChange T X Z).obj a.unop).smallEtaleTopology Ab.{u + 1}).obj
    (levelSheaf T X Z F a.unop)
  map g := gammaTransition T X Z F g.unop
  map_id a := by
    ext z
    obtain ⟨x, rfl⟩ := surjective_sheafHZeroFun_level T X Z F a.unop z
    change gammaTransition T X Z F (𝟙 a.unop) (sheafHZeroFun _ x) = sheafHZeroFun _ x
    rw [gammaTransition_sheafHZeroFun, cohomologyTransition_id]
  map_comp g g' := by
    ext z
    obtain ⟨x, rfl⟩ := surjective_sheafHZeroFun_level T X Z F _ z
    change gammaTransition T X Z F (g ≫ g').unop (sheafHZeroFun _ x) =
      gammaTransition T X Z F g'.unop (gammaTransition T X Z F g.unop (sheafHZeroFun _ x))
    rw [gammaTransition_sheafHZeroFun, gammaTransition_sheafHZeroFun, gammaTransition_sheafHZeroFun,
      cohomologyTransition_comp T X Z F g'.unop g.unop (g ≫ g').unop 0 x]

/-- The object of `gammaDiagram` at `a` is the group of global sections of the level sheaf
over `Y_a`. -/
theorem gammaDiagram_obj (a : Iᵒᵖᵒᵖ) : (gammaDiagram T X Z F).obj a =
    (Sheaf.Γ ((baseChange T X Z).obj a.unop).smallEtaleTopology Ab.{u + 1}).obj
      (levelSheaf T X Z F a.unop) := rfl

/-- The map of `gammaDiagram` along `g` is the restriction map `gammaTransition`. -/
theorem gammaDiagram_map {a b : Iᵒᵖᵒᵖ} (g : a ⟶ b) :
    (gammaDiagram T X Z F).map g = gammaTransition T X Z F g.unop := rfl

variable {T X Z} (cY : Cone (baseChange T X Z)) (p : cY.pt ⟶ X.left)
  (hp : ∀ i, p = cY.π.app i ≫ levelProj T X Z i)

/-- The restriction `gammaLeg` corresponds under `sheafHZeroFun` to the leg `cohomologyLeg` in
degree zero. -/
theorem gammaLeg_sheafHZeroFun (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F i) 0) :
    gammaLeg F cY p hp i (sheafHZeroFun _ x) = sheafHZeroFun _ (cohomologyLeg F cY p hp i 0 x) :=
  (sheafHZeroFun_naturality _ _ x).symm

variable (T X Z) in
/-- The cocone with vertex `Γ(Y, p⁻¹ F)` and legs `gammaLeg`. -/
def gammaCocone : Cocone (gammaDiagram T X Z F) where
  pt := (Sheaf.Γ cY.pt.smallEtaleTopology Ab.{u + 1}).obj ((smallEtalePullbackAb p).obj F)
  ι :=
    { app a := gammaLeg F cY p hp a.unop
      naturality a b g := by
        ext z
        obtain ⟨x, rfl⟩ := surjective_sheafHZeroFun_level T X Z F a.unop z
        change gammaLeg F cY p hp b.unop (gammaTransition T X Z F g.unop (sheafHZeroFun _ x)) =
          gammaLeg F cY p hp a.unop (sheafHZeroFun _ x)
        rw [gammaTransition_sheafHZeroFun, gammaLeg_sheafHZeroFun, gammaLeg_sheafHZeroFun,
          cohomologyLeg_transition]
        rfl }

/-- The leg of `gammaCocone` at `a` is `gammaLeg`. -/
theorem gammaCocone_ι_app (a : Iᵒᵖᵒᵖ) :
    (gammaCocone T X Z F cY p hp).ι.app a = gammaLeg F cY p hp a.unop := rfl

variable (T X Z) in
/-- [stacks 03Q6] in degree zero: if `Y` is the limit of the `Y_a`, the restriction maps on
global sections exhibit `Γ(Y, p⁻¹ F)` as the colimit of the `Γ(Y_a, G_a)`. -/
theorem isIso_colimitDesc_gammaCocone [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T]
    [∀ i, IsAffine (Z.obj i).left] [QuasiCompact X.hom] [QuasiSeparated X.hom] (hcY : IsLimit cY) :
    IsIso (colimit.desc (gammaDiagram T X Z F) (gammaCocone T X Z F cY p hp)) := by
  have h := isIso_colimitDesc_cohomologyCocone T X Z F cY p hp hcY 0
  obtain ⟨hc⟩ := (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).1 h
  let α : cohomologyDiagram T X Z F 0 ≅ gammaDiagram T X Z F :=
    NatIso.ofComponents (fun a => sheafHZeroIso (levelSheaf T X Z F a.unop)) (fun {a b} g => by
      ext x
      exact (gammaTransition_sheafHZeroFun T X Z F g.unop x).symm)
  have e : (Cocone.precompose α.hom).obj (gammaCocone T X Z F cY p hp) ≅
      cohomologyCocone T X Z F cY p hp 0 :=
    Cocone.ext (sheafHZeroIso ((smallEtalePullbackAb p).obj F)).symm (fun a => by
      ext (x : Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F a.unop) 0)
      have h1 := gammaLeg_sheafHZeroFun F cY p hp a.unop x
      exact (congrArg (sheafHZeroIso ((smallEtalePullbackAb p).obj F)).inv h1).trans
        (Iso.hom_inv_id_apply (sheafHZeroIso ((smallEtalePullbackAb p).obj F)) _))
  have h₁ : IsColimit ((Cocone.precompose α.hom).obj (gammaCocone T X Z F cY p hp)) :=
    IsColimit.ofIsoColimit hc e.symm
  exact (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).2
    ⟨(IsColimit.precomposeHomEquiv α _).1 h₁⟩

/-- If `Y` is the limit of the `Y_a`, the cocone `gammaCocone` is a colimit cocone. -/
def isColimitGammaCocone [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T]
    [∀ i, IsAffine (Z.obj i).left] [QuasiCompact X.hom] [QuasiSeparated X.hom] (hcY : IsLimit cY) :
    IsColimit (gammaCocone T X Z F cY p hp) :=
  ((Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).1
    (isIso_colimitDesc_gammaCocone T X Z F cY p hp hcY)).some

end Gamma

end Stacks.EtaleCohomology.ColimitBaseChange

end

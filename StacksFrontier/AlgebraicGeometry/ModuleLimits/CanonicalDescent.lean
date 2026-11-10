module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine

/-!
# Descent of a morphism of finitely presented modules, with the canonical identification

For a cofiltered diagram of **affine** schemes with limit `c`, a morphism between the pullbacks to
the limit of two sheaves of modules of finite presentation on a stage `i` is, after passing to a
later stage `j`, the pullback of a morphism at that stage, the pullbacks being identified through
the *canonical* isomorphisms `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`pullbackCongr`. This is [Stacks, Tag 01ZR] (2) for affine schemes.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.finitePresentation_sectionsTop`: the global sections of
  a sheaf of modules of finite presentation on an affine scheme form a finitely presented module
  over the ring of global sections.
* `Stacks.AlgebraicGeometry.ModuleLimits.xiTop_comp_map`: the comparison `xiTop` carries the
  pullback of a morphism to the base change of the corresponding map of modules.
* `Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_descend`: a morphism at an intermediate
  stage whose map of global sections is the base change of a map of modules compatible with `φ`
  pulls back to `φ` through the canonical identifications.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine`:
  **Tag 01ZR (2)** for a cofiltered diagram of affine schemes, with the canonical
  identification.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine'`: the same
  statement with the universe of the index morphisms unrestricted.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Stacks.ModuleCat Stacks.AlgebraicGeometry.SectionsBaseChange

/-! ### Global sections of a finitely presented module -/

/-- The global sections of a sheaf of modules of finite presentation on an affine scheme form a
finitely presented module over the ring of global sections. -/
theorem finitePresentation_sectionsTop {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsFinitePresentation] : Module.FinitePresentation Γ(X, ⊤) ↑Γ(F, ⊤) := by
  set β := (isAffineOpen_top X).fromSpec with hβ
  have hqF : F.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation F
  have hfp : (F.restrict β).IsFinitePresentation := isFinitePresentation_restrict β F
  have hqc : (F.restrict β).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor β F
  have hii : IsIso (Scheme.Modules.fromTildeΓ (F.restrict β)) :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ (F.restrict β) hqc
  have hiso : tilde (moduleSpecΓFunctor.obj (F.restrict β)) ≅ F.restrict β :=
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (F.restrict β)) hii
  have h0 : (tilde (moduleSpecΓFunctor.obj (F.restrict β))).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso hiso.symm hfp
  have h1 : Module.FinitePresentation Γ(X, ⊤) ↑(moduleSpecΓFunctor.obj (F.restrict β)) :=
    (tilde_isFinitePresentation_iff _).mp h0
  exact (LinearEquiv.finitePresentation_iff
    (affineSectionsLinearEquiv F (isAffineOpen_top X))).mp h1

/-! ### The comparison and the pullback of a morphism -/

section Xi

variable {W Z X : Scheme.{u}} [IsAffine W] [IsAffine Z] [IsAffine X]
  (q : W ⟶ Z) (g : Z ⟶ X) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
  [((Scheme.Modules.pullback g).obj F).IsQuasicoherent]
  [((Scheme.Modules.pullback g).obj G).IsQuasicoherent]

/-- The comparison `xiTop` carries the pullback along `q` of a morphism at the intermediate
stage to the base change along `q` of the corresponding map of modules. -/
theorem xiTop_comp_map
    (φj : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (ul : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤)) ⟶
        (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(G, ⊤)))
    (hφj : (bcTop g F).hom ≫ appTopHom φj = ul ≫ (bcTop g G).hom) :
    (xiTop q g F).hom ≫ appTopHom ((Scheme.Modules.pullback q).map φj)
      = (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map ul ≫ (xiTop q g G).hom := by
  refine extendScalars_hom_ext' _ (fun w x hx => ?_)
  obtain ⟨v, hv⟩ : ∃ v : (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).obj
        (ModuleCat.of Γ(Z, ⊤) ↑Γ((Scheme.Modules.pullback g).obj F, ⊤)),
      v = (1 : Γ(W, ⊤)) ⊗ₜ[Γ(Z, ⊤),(Scheme.Hom.appTop q).hom] ((bcTop g F).hom w) := ⟨_, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x' : (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).obj
        ((ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(G, ⊤))),
      x' = (1 : Γ(W, ⊤)) ⊗ₜ[Γ(Z, ⊤),(Scheme.Hom.appTop q).hom] (ul w) := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v' : (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).obj
        (ModuleCat.of Γ(Z, ⊤) ↑Γ((Scheme.Modules.pullback g).obj G, ⊤)),
      v' = (1 : Γ(W, ⊤)) ⊗ₜ[Γ(Z, ⊤),(Scheme.Hom.appTop q).hom] ((bcTop g G).hom (ul w)) :=
    ⟨_, rfl⟩
  have e1 : (xiTop q g F).hom x = Scheme.Modules.pullbackSection q
      ((Scheme.Modules.pullback g).obj F) ⊤ ⊤ (le_preimage_top q ⊤) ((bcTop g F).hom w) := by
    rw [xiTop_hom]
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    rw [extendScalars_map_eq _ (bcTop g F).hom w x hx v hv]
    exact extendScalars_iso_hom_eq (bcTop q ((Scheme.Modules.pullback g).obj F))
      (bcTop_hom_one_tmul q ((Scheme.Modules.pullback g).obj F) ((bcTop g F).hom w)) hv
  have e2 : (xiTop q g G).hom
      ((ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map ul x)
      = Scheme.Modules.pullbackSection q ((Scheme.Modules.pullback g).obj G) ⊤ ⊤
        (le_preimage_top q ⊤) ((bcTop g G).hom (ul w)) := by
    rw [extendScalars_map_eq _ ul w x hx x' hx', xiTop_hom]
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    rw [extendScalars_map_eq _ (bcTop g G).hom (ul w) x' hx' v' hv']
    exact extendScalars_iso_hom_eq (bcTop q ((Scheme.Modules.pullback g).obj G))
      (bcTop_hom_one_tmul q ((Scheme.Modules.pullback g).obj G) ((bcTop g G).hom (ul w))) hv'
  have h0 := congrArg (fun k => (ConcreteCategory.hom k) w) hφj
  have c1 := ConcreteCategory.comp_apply (bcTop g F).hom (appTopHom φj) w
  have c2 := ConcreteCategory.comp_apply ul (bcTop g G).hom w
  have happ := c1.symm.trans (h0.trans c2)
  have hnat := Scheme.Modules.pullbackSection_naturality q φj ⊤ ⊤ (le_preimage_top q ⊤)
    ((bcTop g F).hom w)
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
  rw [e1, e2]
  exact hnat.trans (congrArg (Scheme.Modules.pullbackSection q
    ((Scheme.Modules.pullback g).obj G) ⊤ ⊤ (le_preimage_top q ⊤)) happ)

end Xi

/-! ### The canonical equation -/

section Assemble

variable {W Z X : Scheme.{u}} [IsAffine W] [IsAffine Z] [IsAffine X]
  (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)
  (F G : X.Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
  [F.IsQuasicoherent] [G.IsQuasicoherent]
  [((Scheme.Modules.pullback g).obj F).IsQuasicoherent]
  [((Scheme.Modules.pullback g).obj G).IsQuasicoherent]

include hpi in
/-- **The canonical equation.** Let `φj` be a morphism at the intermediate stage whose map of
global sections is the base change of a map `ul` of modules (`hφj`), and suppose that the base
change of `ul` along `q` corresponds to the map of global sections of `φ` (`hu`). Then the
pullback of `φj` along `q` is `φ` under the canonical identifications `canHom`. -/
theorem canonical_eq_of_descend
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
    (φj : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (ul : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤)) ⟶
        (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(G, ⊤)))
    (hφj : (bcTop g F).hom ≫ appTopHom φj = ul ≫ (bcTop g G).hom)
    (hu : (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map ul ≫
          (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
              (Scheme.Hom.appTop pi).hom (hp_triangle q g pi hpi)
              (ModuleCat.of Γ(X, ⊤) ↑Γ(G, ⊤))).hom ≫ (bcTop pi G).hom
        = (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
              (Scheme.Hom.appTop pi).hom (hp_triangle q g pi hpi)
              (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤))).hom ≫ (bcTop pi F).hom ≫ appTopHom φ) :
    (Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi G
      = canHom q g pi hpi F ≫ φ := by
  have hfpgF : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback g F
  have hfpsrc : ((Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pullback g).obj F)).IsFinitePresentation :=
    isFinitePresentation_pullback q _
  have hqcsrc : ((Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pullback g).obj F)).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isFinitePresentation _
  have hfptgt : ((Scheme.Modules.pullback pi).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback pi G
  have hqctgt : ((Scheme.Modules.pullback pi).obj G).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isFinitePresentation _
  have key : (xiTop q g F).hom ≫
        appTopHom ((Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi G)
      = (xiTop q g F).hom ≫ appTopHom (canHom q g pi hpi F ≫ φ) := by
    rw [appTopHom_comp, appTopHom_comp,
      reassoc_of% (xiTop_comp_map q g F G φj ul hφj),
      xiTop_comp_canHom q g pi hpi G, hu,
      reassoc_of% (xiTop_comp_canHom q g pi hpi F)]
  have h2 : appTopHom ((Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi G)
      = appTopHom (canHom q g pi hpi F ≫ φ) := (cancel_epi (xiTop q g F).hom).mp key
  exact hom_ext_of_app_top (fun z => congrArg (fun k => (ConcreteCategory.hom k) z) h2)

end Assemble

/-! ### Tag 01ZR (2) for a cofiltered diagram of affine schemes -/

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]

include hc in
/-- **Stacks Project, Tag 01ZR (2)** for a cofiltered diagram of affine schemes, with the
canonical identification: a morphism between the pullbacks to the limit of two sheaves of
modules of finite presentation on a stage is, after passing to a later stage, the base change of
a morphism there, the base change being taken through
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackCongr`. -/
theorem exists_map_of_pullback_canonical_of_isAffine (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G
        = canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F ≫ φ := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hqF : F.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation F
  have hqG : G.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation G
  set E : (Over i)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget i ⋙ D).op ⋙ Scheme.Γ with hE
  set d : Cocone E := Scheme.Γ.mapCocone (c.whisker (Over.forget i)).op with hddef
  have hd : IsColimit d := by
    have hl : IsLimit (c.whisker (Over.forget i)) :=
      (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
    have : ∀ k : (Over i)ᵒᵖ, IsAffine ((Over.forget i ⋙ D).op.obj k).unop := by
      intro k; dsimp; infer_instance
    exact isColimitOfPreserves Scheme.Γ hl.op
  let _ : ∀ l : (Over i)ᵒᵖ, Algebra Γ(D.obj i, ⊤) (E.obj l) :=
    fun l => ((D.map l.unop.hom).appTop).hom.toAlgebra
  let _ : Algebra Γ(D.obj i, ⊤) d.pt := ((c.π.app i).appTop).hom.toAlgebra
  have halg : ∀ (k : (Over i)ᵒᵖ) (y : Γ(D.obj i, ⊤)),
      algebraMap Γ(D.obj i, ⊤) (E.obj k) y = (D.map k.unop.hom).appTop y := fun _ _ => rfl
  have halgR : ∀ y : Γ(D.obj i, ⊤),
      algebraMap Γ(D.obj i, ⊤) d.pt y = (c.π.app i).appTop y := fun _ => rfl
  have ha : ∀ {l m : (Over i)ᵒᵖ} (ee : l ⟶ m) (x : Γ(D.obj i, ⊤)),
      E.map ee (algebraMap Γ(D.obj i, ⊤) (E.obj l) x)
        = algebraMap Γ(D.obj i, ⊤) (E.obj m) x := by
    intro l m ee x
    rw [halg, halg]
    change (D.map ee.unop.left).appTop ((D.map l.unop.hom).appTop x)
      = (D.map m.unop.hom).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ← D.map_comp, Over.w ee.unop]
  have haR : ∀ (l : (Over i)ᵒᵖ) (x : Γ(D.obj i, ⊤)),
      d.ι.app l (algebraMap Γ(D.obj i, ⊤) (E.obj l) x)
        = algebraMap Γ(D.obj i, ⊤) d.pt x := by
    intro l x
    rw [halg, halgR]
    change (c.π.app l.unop.left).appTop ((D.map l.unop.hom).appTop x)
      = (c.π.app i).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w l.unop.hom]
  let pii : c.pt ⟶ D.obj i := c.π.app i
  have hMfp : Module.FinitePresentation Γ(D.obj i, ⊤) ↑Γ(F, ⊤) := finitePresentation_sectionsTop F
  let u : (ModuleCat.extendScalars (Scheme.Hom.appTop pii).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)) ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop pii).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤)) :=
    (bcTop pii F).hom ≫ appTopHom φ ≫ (bcTop pii G).inv
  obtain ⟨l, ul, hul⟩ := Stacks.RingFilteredColimits.exists_descend_rTensor haR ha hd
    ↑Γ(F, ⊤) ↑Γ(G, ⊤) u.hom
  let j := l.unop.left
  let e : j ⟶ i := l.unop.hom
  let g : D.obj j ⟶ D.obj i := D.map e
  let qq : c.pt ⟶ D.obj j := c.π.app j
  have hpi : qq ≫ g = pii := c.w e
  have hfpgF : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback g F
  have hfpgG : ((Scheme.Modules.pullback g).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback g G
  have hqcgF : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isFinitePresentation _
  have hqcgG : ((Scheme.Modules.pullback g).obj G).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isFinitePresentation _
  let ulM0 := ModuleCat.ofHom ul
  let ulM : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)) ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤)) := ulM0
  let vj := (bcTop g F).inv ≫ ulM ≫ (bcTop g G).hom
  obtain ⟨φj, hφj0⟩ := exists_hom_app_top_eq (X := D.obj j)
    (F := (Scheme.Modules.pullback g).obj F) (G := (Scheme.Modules.pullback g).obj G) vj.hom
  refine ⟨j, e, φj, ?_⟩
  have hφj : (bcTop g F).hom ≫ appTopHom φj = ulM ≫ (bcTop g G).hom := by
    have h1 : appTopHom φj = vj := ModuleCat.hom_ext (LinearMap.ext fun a => hφj0 a)
    rw [h1]
    change (bcTop g F).hom ≫ (bcTop g F).inv ≫ ulM ≫ (bcTop g G).hom = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hE : u ≫ (bcTop pii G).hom = (bcTop pii F).hom ≫ appTopHom φ := by
    change ((bcTop pii F).hom ≫ appTopHom φ ≫ (bcTop pii G).inv) ≫ (bcTop pii G).hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hf : ∀ β : Γ(D.obj j, ⊤), Stacks.RingFilteredColimits.legAlgHom haR l β
      = (Scheme.Hom.appTop qq).hom β := fun _ => rfl
  have hul' : ∀ y : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)),
      u (LinearMap.rTensor (↑Γ(F, ⊤))
          (Stacks.RingFilteredColimits.legAlgHom haR l).toLinearMap y)
        = LinearMap.rTensor (↑Γ(G, ⊤))
          (Stacks.RingFilteredColimits.legAlgHom haR l).toLinearMap (ulM y) := hul
  have hD := Stacks.ModuleCat.extendScalars_map_comp_cancelIsoApp
    (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop qq).hom
    (Scheme.Hom.appTop pii).hom (hp_triangle qq g pii hpi)
    (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)) (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤))
    (Stacks.RingFilteredColimits.legAlgHom haR l) hf u ulM hul'
  have hu : (ModuleCat.extendScalars (Scheme.Hom.appTop qq).hom).map ulM ≫
        (Stacks.ModuleCat.cancelIsoApp (Scheme.Hom.appTop g).hom
            (Scheme.Hom.appTop qq).hom (Scheme.Hom.appTop pii).hom
            (hp_triangle qq g pii hpi)
            (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤))).hom ≫ (bcTop pii G).hom
      = (Stacks.ModuleCat.cancelIsoApp (Scheme.Hom.appTop g).hom
            (Scheme.Hom.appTop qq).hom (Scheme.Hom.appTop pii).hom
            (hp_triangle qq g pii hpi)
            (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤))).hom ≫
          (bcTop pii F).hom ≫ appTopHom φ := by
    rw [reassoc_of% hD, hE]
  exact canonical_eq_of_descend qq g pii hpi F G φ φj ulM hφj hu

end Limit

/-! ### The index morphism universe -/

section IndexHomUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

/-- The existence of a morphism `φj` at a stage `g` pulling back to `φ` through the canonical
identifications is invariant under replacing `g` by an equal morphism `g'`. -/
theorem exists_canonical_congr {W Z X : Scheme.{u}} (q : W ⟶ Z) {g g' : Z ⟶ X}
    (h : g = g') (pi : W ⟶ X) (hpi : q ≫ g = pi) (hpi' : q ≫ g' = pi) (F G : X.Modules)
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
    (hex : ∃ φj' : (Scheme.Modules.pullback g').obj F ⟶ (Scheme.Modules.pullback g').obj G,
      (Scheme.Modules.pullback q).map φj' ≫ canHom q g' pi hpi' G
        = canHom q g' pi hpi' F ≫ φ) :
    ∃ φj : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G,
      (Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi G
        = canHom q g pi hpi F ≫ φ := by
  subst h
  exact hex

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ i, IsAffine (D.obj i)]

include c in
/-- **Stacks Project, Tag 01ZR (2)** for a cofiltered diagram of affine schemes with the index
morphism universe unrestricted, and with the canonical identification. -/
theorem exists_map_of_pullback_canonical_of_isAffine' (hc : IsLimit c) (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G
        = canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F ≫ φ := by
  obtain ⟨j, gm, hgm⟩ :=
    @exists_map_of_pullback_canonical_of_isAffine (FullImage D) _ _ (ι D) (cone D c)
      (isLimitCone D hc) (fun j => inferInstanceAs (IsAffine (D.obj j.as))) ⟨i⟩ F G ‹_› ‹_› φ
  refine ⟨j.as, hom D gm, ?_⟩
  exact exists_canonical_congr (c.π.app j.as) (map_hom D gm) (c.π.app i)
    (c.w (hom D gm)) ((cone D c).w gm) F G φ hgm

end IndexHomUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end

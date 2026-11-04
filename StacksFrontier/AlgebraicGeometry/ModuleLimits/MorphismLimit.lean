module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ExtendScalarsCancel
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescent

/-!
# Descent of morphisms of finitely presented modules through a limit of affine schemes

Let `D` be a cofiltered diagram of affine schemes with limit cone `c`, and let `F`, `G` be sheaves
of modules of finite presentation on a stage `D.obj i`. This file proves the affine case of
[Stacks Project, Tag 01ZR] (2) and (3): a morphism between the pullbacks of `F` and `G` to the
limit is, up to isomorphisms of its source and target, the pullback of a morphism at a later
stage, and two morphisms `F ⟶ G` whose pullbacks to the limit agree already have equal pullbacks
to a later stage.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_of_isAffine`: Tag 01ZR (2) for a
  cofiltered diagram of affine schemes.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine`: Tag 01ZR (3) for a
  cofiltered diagram of affine schemes.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_of_isAffine'`,
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine'`: the same two
  statements for an index category whose morphisms lie in an arbitrary universe.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules Stacks.AlgebraicGeometry.AffineTilde Stacks.ModuleCat

section Affine

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]

include hc in
/-- **Stacks Project, Tag 01ZR (3)** for a cofiltered diagram of affine schemes: two morphisms of
sheaves of modules of finite presentation on a stage whose pullbacks to the limit agree already
have equal pullbacks to a later stage. -/
theorem exists_pullback_map_eq_of_isAffine (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (ψ₁ ψ₂ : F ⟶ G)
    (h : (Scheme.Modules.pullback (c.π.app i)).map ψ₁ =
      (Scheme.Modules.pullback (c.π.app i)).map ψ₂) :
    ∃ (j : I) (e : j ⟶ i),
      (Scheme.Modules.pullback (D.map e)).map ψ₁ =
        (Scheme.Modules.pullback (D.map e)).map ψ₂ := by
  classical
  obtain ⟨M, hM, ⟨eF⟩⟩ := exists_iso_tildeOf (D.obj i) F
  obtain ⟨N, hN, ⟨eG⟩⟩ := exists_iso_tildeOf (D.obj i) G
  set T := tildeOf (D.obj i)
  set v₁ : M ⟶ N := T.preimage (eF.hom ≫ ψ₁ ≫ eG.inv)
  set v₂ : M ⟶ N := T.preimage (eF.hom ≫ ψ₂ ≫ eG.inv)
  have hTv₁ : T.map v₁ = eF.hom ≫ ψ₁ ≫ eG.inv := T.map_preimage _
  have hTv₂ : T.map v₂ = eF.hom ≫ ψ₂ ≫ eG.inv := T.map_preimage _
  have key : (Scheme.Modules.pullback (c.π.app i)).map (T.map v₁) =
      (Scheme.Modules.pullback (c.π.app i)).map (T.map v₂) := by
    rw [hTv₁, hTv₂]; simp only [Functor.map_comp, h]
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  set Θ := tildeOfPullbackIso (X := c.pt) (Y := D.obj i) (c.π.app i)
  have nat : ∀ v : M ⟶ N, (Scheme.Modules.pullback (c.π.app i)).map (T.map v) ≫ Θ.hom.app N
      = Θ.hom.app M ≫ (tildeOf c.pt).map
        ((ModuleCat.extendScalars (Scheme.Hom.appTop (c.π.app i)).hom).map v) :=
    fun v => Θ.hom.naturality v
  have key2 : (ModuleCat.extendScalars (Scheme.Hom.appTop (c.π.app i)).hom).map v₁ =
      (ModuleCat.extendScalars (Scheme.Hom.appTop (c.π.app i)).hom).map v₂ := by
    apply (tildeOf c.pt).map_injective
    rw [← cancel_epi (Θ.hom.app M), ← nat v₁, ← nat v₂, key]
  set E : (Over i)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget i ⋙ D).op ⋙ Scheme.Γ
  set d : Cocone E := Scheme.Γ.mapCocone (c.whisker (Over.forget i)).op
  have hd : IsColimit d := by
    have hl : IsLimit (c.whisker (Over.forget i)) :=
      (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
    have : ∀ j : (Over i)ᵒᵖ, IsAffine ((Over.forget i ⋙ D).op.obj j).unop := by
      intro j; dsimp; infer_instance
    exact isColimitOfPreserves Scheme.Γ hl.op
  let _ : ∀ l : (Over i)ᵒᵖ, Algebra Γ(D.obj i, ⊤) (E.obj l) :=
    fun l => ((D.map l.unop.hom).appTop).hom.toAlgebra
  let _ : Algebra Γ(D.obj i, ⊤) d.pt := ((c.π.app i).appTop).hom.toAlgebra
  have ha : ∀ {l m : (Over i)ᵒᵖ} (e : l ⟶ m) (x : Γ(D.obj i, ⊤)),
      E.map e (algebraMap Γ(D.obj i, ⊤) (E.obj l) x) = algebraMap Γ(D.obj i, ⊤) (E.obj m) x := by
    intro l m e x
    show (D.map e.unop.left).appTop ((D.map l.unop.hom).appTop x) = (D.map m.unop.hom).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ← D.map_comp, Over.w e.unop]
  have haR : ∀ (l : (Over i)ᵒᵖ) (x : Γ(D.obj i, ⊤)),
      d.ι.app l (algebraMap Γ(D.obj i, ⊤) (E.obj l) x) = algebraMap Γ(D.obj i, ⊤) d.pt x := by
    intro l x
    show (c.π.app l.unop.left).appTop ((D.map l.unop.hom).appTop x) = (c.π.app i).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w l.unop.hom]
  have hfin : Module.Finite Γ(D.obj i, ⊤) M := by have := hM; infer_instance
  have hbc : LinearMap.baseChange d.pt v₁.hom = LinearMap.baseChange d.pt v₂.hom :=
    ModuleCat.hom_ext_iff.mp key2
  obtain ⟨l, hl⟩ :=
    Stacks.RingFilteredColimits.exists_baseChange_eq haR ha hd M N v₁.hom v₂.hom hbc
  refine ⟨l.unop.left, l.unop.hom, ?_⟩
  have step : (Scheme.Modules.pullback (D.map l.unop.hom)).map (T.map v₁) =
      (Scheme.Modules.pullback (D.map l.unop.hom)).map (T.map v₂) := by
    set Θ' := tildeOfPullbackIso (X := D.obj l.unop.left) (Y := D.obj i) (D.map l.unop.hom)
    have nat' : ∀ v : M ⟶ N,
        (Scheme.Modules.pullback (D.map l.unop.hom)).map (T.map v) ≫ Θ'.hom.app N
          = Θ'.hom.app M ≫ (tildeOf (D.obj l.unop.left)).map
            ((ModuleCat.extendScalars (Scheme.Hom.appTop (D.map l.unop.hom)).hom).map v) :=
      fun v => Θ'.hom.naturality v
    rw [← cancel_mono (Θ'.hom.app N), nat' v₁, nat' v₂]
    congr 2
    exact ModuleCat.hom_ext hl
  rw [hTv₁, hTv₂] at step
  simp only [Functor.map_comp] at step
  rw [← cancel_epi ((Scheme.Modules.pullback (D.map l.unop.hom)).map eF.hom),
    ← cancel_mono ((Scheme.Modules.pullback (D.map l.unop.hom)).map eG.inv)]
  simpa using step

/-! ### Descent of a morphism -/

private theorem coreTwoComp {X Z Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (q : X ⟶ Z) (g : Z ⟶ Y) (M N : ModuleCat.{u} Γ(Y, ⊤))
    (hp : ∀ x, (Scheme.Hom.appTop (q ≫ g)).hom x =
      (Scheme.Hom.appTop q).hom ((Scheme.Hom.appTop g).hom x))
    (u : (ModuleCat.extendScalars (Scheme.Hom.appTop (q ≫ g)).hom).obj M ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop (q ≫ g)).hom).obj N)
    (ul : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj M ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj N)
    (hcompat : (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map ul ≫
          (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
            (Scheme.Hom.appTop (q ≫ g)).hom hp N).hom
        = (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
            (Scheme.Hom.appTop (q ≫ g)).hom hp M).hom ≫ u)
    (φ : (Scheme.Modules.pullback (q ≫ g)).obj ((tildeOf Y).obj M) ⟶
      (Scheme.Modules.pullback (q ≫ g)).obj ((tildeOf Y).obj N))
    (hφ : (tildeOf X).map u = (tildeOfPullbackIsoApp (q ≫ g) M).inv ≫ φ ≫
      (tildeOfPullbackIsoApp (q ≫ g) N).hom) :
    ∃ (φj : (Scheme.Modules.pullback g).obj ((tildeOf Y).obj M) ⟶
          (Scheme.Modules.pullback g).obj ((tildeOf Y).obj N))
      (α : (Scheme.Modules.pullback q).obj
            ((Scheme.Modules.pullback g).obj ((tildeOf Y).obj M)) ≅
          (Scheme.Modules.pullback (q ≫ g)).obj ((tildeOf Y).obj M))
      (β : (Scheme.Modules.pullback q).obj
            ((Scheme.Modules.pullback g).obj ((tildeOf Y).obj N)) ≅
          (Scheme.Modules.pullback (q ≫ g)).obj ((tildeOf Y).obj N)),
      (Scheme.Modules.pullback q).map φj ≫ β.hom = α.hom ≫ φ := by
  refine ⟨(tildeOfPullbackIsoApp g M).hom ≫ (tildeOf Z).map ul ≫
      (tildeOfPullbackIsoApp g N).inv,
    (Scheme.Modules.pullback q).mapIso (tildeOfPullbackIsoApp g M) ≪≫
      tildeOfPullbackIsoApp q _ ≪≫
      (tildeOf X).mapIso (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
        (Scheme.Hom.appTop (q ≫ g)).hom hp M) ≪≫ (tildeOfPullbackIsoApp (q ≫ g) M).symm,
    (Scheme.Modules.pullback q).mapIso (tildeOfPullbackIsoApp g N) ≪≫
      tildeOfPullbackIsoApp q _ ≪≫
      (tildeOf X).mapIso (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
        (Scheme.Hom.appTop (q ≫ g)).hom hp N) ≪≫ (tildeOfPullbackIsoApp (q ≫ g) N).symm, ?_⟩
  have hα : ((Scheme.Modules.pullback q).mapIso (tildeOfPullbackIsoApp g M) ≪≫
      tildeOfPullbackIsoApp q _ ≪≫
      (tildeOf X).mapIso (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
        (Scheme.Hom.appTop (q ≫ g)).hom hp M) ≪≫ (tildeOfPullbackIsoApp (q ≫ g) M).symm).hom
      = (Scheme.Modules.pullback q).map (tildeOfPullbackIsoApp g M).hom ≫
        (tildeOfPullbackIsoApp q _).hom ≫
        (tildeOf X).map (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
          (Scheme.Hom.appTop (q ≫ g)).hom hp M).hom ≫
        (tildeOfPullbackIsoApp (q ≫ g) M).inv := rfl
  have hβ : ((Scheme.Modules.pullback q).mapIso (tildeOfPullbackIsoApp g N) ≪≫
      tildeOfPullbackIsoApp q _ ≪≫
      (tildeOf X).mapIso (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
        (Scheme.Hom.appTop (q ≫ g)).hom hp N) ≪≫ (tildeOfPullbackIsoApp (q ≫ g) N).symm).hom
      = (Scheme.Modules.pullback q).map (tildeOfPullbackIsoApp g N).hom ≫
        (tildeOfPullbackIsoApp q _).hom ≫
        (tildeOf X).map (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
          (Scheme.Hom.appTop (q ≫ g)).hom hp N).hom ≫
        (tildeOfPullbackIsoApp (q ≫ g) N).inv := rfl
  rw [hα, hβ]
  have hstep : (Scheme.Modules.pullback q).map ((tildeOfPullbackIsoApp g M).hom ≫
        (tildeOf Z).map ul ≫ (tildeOfPullbackIsoApp g N).inv) ≫
        (Scheme.Modules.pullback q).map (tildeOfPullbackIsoApp g N).hom
      = (Scheme.Modules.pullback q).map (tildeOfPullbackIsoApp g M).hom ≫
        (Scheme.Modules.pullback q).map ((tildeOf Z).map ul) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp
  rw [← Category.assoc, hstep]
  have nat := tildeOfPullbackIsoApp_naturality q ul
  rw [Category.assoc, Category.assoc, ← Category.assoc ((Scheme.Modules.pullback q).map
    ((tildeOf Z).map ul)), nat]
  have hfin : (tildeOf X).map ((ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map ul) ≫
      (tildeOf X).map (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
        (Scheme.Hom.appTop (q ≫ g)).hom hp N).hom
      = (tildeOf X).map (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
          (Scheme.Hom.appTop (q ≫ g)).hom hp M).hom ≫ (tildeOf X).map u := by
    rw [← Functor.map_comp, hcompat]
    exact (tildeOf X).map_comp _ _
  simp only [Category.assoc]
  rw [reassoc_of% hfin, hφ]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `coreTwoComp` with the composite `q ≫ g` replaced by a morphism `pi` equal to it. -/
private theorem coreTwo {X Z Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (q : X ⟶ Z) (g : Z ⟶ Y) (pi : X ⟶ Y) (hpi : q ≫ g = pi) (M N : ModuleCat.{u} Γ(Y, ⊤))
    (hp : ∀ x, (Scheme.Hom.appTop pi).hom x =
      (Scheme.Hom.appTop q).hom ((Scheme.Hom.appTop g).hom x))
    (u : (ModuleCat.extendScalars (Scheme.Hom.appTop pi).hom).obj M ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop pi).hom).obj N)
    (ul : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj M ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj N)
    (hcompat : (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map ul ≫
          (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
            (Scheme.Hom.appTop pi).hom hp N).hom
        = (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
            (Scheme.Hom.appTop pi).hom hp M).hom ≫ u)
    (φ : (Scheme.Modules.pullback pi).obj ((tildeOf Y).obj M) ⟶
      (Scheme.Modules.pullback pi).obj ((tildeOf Y).obj N))
    (hφ : (tildeOf X).map u = (tildeOfPullbackIsoApp pi M).inv ≫ φ ≫
      (tildeOfPullbackIsoApp pi N).hom) :
    ∃ (φj : (Scheme.Modules.pullback g).obj ((tildeOf Y).obj M) ⟶
          (Scheme.Modules.pullback g).obj ((tildeOf Y).obj N))
      (α : (Scheme.Modules.pullback q).obj
            ((Scheme.Modules.pullback g).obj ((tildeOf Y).obj M)) ≅
          (Scheme.Modules.pullback pi).obj ((tildeOf Y).obj M))
      (β : (Scheme.Modules.pullback q).obj
            ((Scheme.Modules.pullback g).obj ((tildeOf Y).obj N)) ≅
          (Scheme.Modules.pullback pi).obj ((tildeOf Y).obj N)),
      (Scheme.Modules.pullback q).map φj ≫ β.hom = α.hom ≫ φ := by
  subst hpi
  exact coreTwoComp q g M N hp u ul hcompat φ hφ

include hc in
/-- **Stacks Project, Tag 01ZR (2)** for a cofiltered diagram of affine schemes: for sheaves of
modules of finite presentation `F`, `G` on a stage `D.obj i` and a morphism `φ` between their
pullbacks to the limit, there are a later stage `D.obj j`, a morphism `φj` between the pullbacks of
`F` and `G` to it, and isomorphisms `α`, `β` from the pullbacks to the limit of the source and
target of `φj` to the source and target of `φ`, under which the pullback of `φj` is `φ`. -/
theorem exists_map_of_pullback_of_isAffine (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G)
      (α : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj F) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj F)
      (β : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj G) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫ β.hom = α.hom ≫ φ := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  revert φ
  set pii : c.pt ⟶ D.obj i := c.π.app i with hpii
  intro φ
  obtain ⟨M, hM, ⟨eF⟩⟩ := exists_iso_tildeOf (D.obj i) F
  obtain ⟨N, hN, ⟨eG⟩⟩ := exists_iso_tildeOf (D.obj i) G
  set φ' : (Scheme.Modules.pullback pii).obj ((tildeOf (D.obj i)).obj M) ⟶
      (Scheme.Modules.pullback pii).obj ((tildeOf (D.obj i)).obj N) :=
    (Scheme.Modules.pullback pii).map eF.hom ≫ φ ≫
      (Scheme.Modules.pullback pii).map eG.inv with hφ'def
  set u : (ModuleCat.extendScalars (Scheme.Hom.appTop pii).hom).obj M ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop pii).hom).obj N :=
    (tildeOf c.pt).preimage ((tildeOfPullbackIsoApp pii M).inv ≫ φ' ≫
      (tildeOfPullbackIsoApp pii N).hom)
  have hφ : (tildeOf c.pt).map u = (tildeOfPullbackIsoApp pii M).inv ≫ φ' ≫
      (tildeOfPullbackIsoApp pii N).hom := (tildeOf c.pt).map_preimage _
  set E : (Over i)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget i ⋙ D).op ⋙ Scheme.Γ
  set d : Cocone E := Scheme.Γ.mapCocone (c.whisker (Over.forget i)).op
  have hd : IsColimit d := by
    have hl : IsLimit (c.whisker (Over.forget i)) :=
      (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
    have : ∀ k : (Over i)ᵒᵖ, IsAffine ((Over.forget i ⋙ D).op.obj k).unop := by
      intro k; dsimp; infer_instance
    exact isColimitOfPreserves Scheme.Γ hl.op
  let _ : ∀ l : (Over i)ᵒᵖ, Algebra Γ(D.obj i, ⊤) (E.obj l) :=
    fun l => ((D.map l.unop.hom).appTop).hom.toAlgebra
  let _ : Algebra Γ(D.obj i, ⊤) d.pt := (pii.appTop).hom.toAlgebra
  have ha : ∀ {l m : (Over i)ᵒᵖ} (ee : l ⟶ m) (x : Γ(D.obj i, ⊤)),
      E.map ee (algebraMap Γ(D.obj i, ⊤) (E.obj l) x)
        = algebraMap Γ(D.obj i, ⊤) (E.obj m) x := by
    intro l m ee x
    show (D.map ee.unop.left).appTop ((D.map l.unop.hom).appTop x)
      = (D.map m.unop.hom).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ← D.map_comp, Over.w ee.unop]
  have haR : ∀ (l : (Over i)ᵒᵖ) (x : Γ(D.obj i, ⊤)),
      d.ι.app l (algebraMap Γ(D.obj i, ⊤) (E.obj l) x) = algebraMap Γ(D.obj i, ⊤) d.pt x := by
    intro l x
    show (c.π.app l.unop.left).appTop ((D.map l.unop.hom).appTop x) = pii.appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hpii, c.w l.unop.hom]
  have hfp : Module.FinitePresentation Γ(D.obj i, ⊤) M := hM
  obtain ⟨l, ul, hul⟩ :=
    Stacks.RingFilteredColimits.exists_descend_rTensor haR ha hd M N u.hom
  set qj : c.pt ⟶ D.obj l.unop.left := c.π.app l.unop.left
  set g : D.obj l.unop.left ⟶ D.obj i := D.map l.unop.hom
  have hpi : qj ≫ g = pii := c.w l.unop.hom
  have hp : ∀ x, (Scheme.Hom.appTop pii).hom x =
      (Scheme.Hom.appTop qj).hom ((Scheme.Hom.appTop g).hom x) := by
    intro x; rw [← hpi]; rfl
  set ulM := ModuleCat.ofHom ul
  have hul' : ∀ y : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj M,
      u (LinearMap.rTensor (↑M)
          (Stacks.RingFilteredColimits.legAlgHom haR l).toLinearMap y)
        = LinearMap.rTensor (↑N)
          (Stacks.RingFilteredColimits.legAlgHom haR l).toLinearMap (ulM y) := hul
  have hcompat := Stacks.ModuleCat.extendScalars_map_comp_cancelIsoApp
    (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop qj).hom (Scheme.Hom.appTop pii).hom hp
    M N (Stacks.RingFilteredColimits.legAlgHom haR l) (fun _ => rfl) u ulM hul'
  obtain ⟨φjM, αM, βM, heq⟩ := coreTwo qj g pii hpi M N hp u ulM hcompat φ' hφ
  refine ⟨l.unop.left, l.unop.hom,
    (Scheme.Modules.pullback g).map eF.inv ≫ φjM ≫ (Scheme.Modules.pullback g).map eG.hom,
    ((Scheme.Modules.pullback qj).mapIso ((Scheme.Modules.pullback g).mapIso eF)).symm ≪≫
      αM ≪≫ (Scheme.Modules.pullback pii).mapIso eF,
    ((Scheme.Modules.pullback qj).mapIso ((Scheme.Modules.pullback g).mapIso eG)).symm ≪≫
      βM ≪≫ (Scheme.Modules.pullback pii).mapIso eG, ?_⟩
  have hα : (((Scheme.Modules.pullback qj).mapIso
        ((Scheme.Modules.pullback g).mapIso eF)).symm ≪≫
      αM ≪≫ (Scheme.Modules.pullback pii).mapIso eF).hom
      = (Scheme.Modules.pullback qj).map ((Scheme.Modules.pullback g).map eF.inv) ≫ αM.hom ≫
        (Scheme.Modules.pullback pii).map eF.hom := rfl
  have hβ : (((Scheme.Modules.pullback qj).mapIso
        ((Scheme.Modules.pullback g).mapIso eG)).symm ≪≫
      βM ≪≫ (Scheme.Modules.pullback pii).mapIso eG).hom
      = (Scheme.Modules.pullback qj).map ((Scheme.Modules.pullback g).map eG.inv) ≫ βM.hom ≫
        (Scheme.Modules.pullback pii).map eG.hom := rfl
  have hcancel : (Scheme.Modules.pullback qj).map ((Scheme.Modules.pullback g).map eF.inv ≫
        φjM ≫ (Scheme.Modules.pullback g).map eG.hom) ≫
        (Scheme.Modules.pullback qj).map ((Scheme.Modules.pullback g).map eG.inv)
      = (Scheme.Modules.pullback qj).map ((Scheme.Modules.pullback g).map eF.inv) ≫
        (Scheme.Modules.pullback qj).map φjM := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp
  have hcancel2 : (Scheme.Modules.pullback pii).map eG.inv ≫
      (Scheme.Modules.pullback pii).map eG.hom = 𝟙 _ := by
    rw [← Functor.map_comp]; simp
  rw [hα, hβ, ← Category.assoc, hcancel]
  simp only [Category.assoc]
  rw [reassoc_of% heq, hφ'def]
  simp only [Category.assoc, hcancel2, Category.comp_id]

end Affine

/-! ### Index categories with morphisms in an arbitrary universe -/

section IndexHomUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ i, IsAffine (D.obj i)]

include c in
/-- **Stacks Project, Tag 01ZR (2)** for a cofiltered diagram of affine schemes, with the index
morphism universe unrestricted: the statement of `exists_map_of_pullback_of_isAffine` for an index
category `[Category.{v} I]`. -/
theorem exists_map_of_pullback_of_isAffine' (hc : IsLimit c) (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G)
      (α : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj F) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj F)
      (β : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj G) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫ β.hom = α.hom ≫ φ := by
  obtain ⟨j, gm, φj, α, β, heq⟩ :=
    @exists_map_of_pullback_of_isAffine (FullImage D) _ _ (ι D) (cone D c) (isLimitCone D hc)
      (fun j => inferInstanceAs (IsAffine (D.obj j.as))) ⟨i⟩ F G ‹_› ‹_› φ
  refine ⟨j.as, hom D gm, ?_⟩
  rw [map_hom D gm]
  exact ⟨φj, α, β, heq⟩

include c in
/-- **Stacks Project, Tag 01ZR (3)** for a cofiltered diagram of affine schemes, with the index
morphism universe unrestricted: the statement of `exists_pullback_map_eq_of_isAffine` for an index
category `[Category.{v} I]`. -/
theorem exists_pullback_map_eq_of_isAffine' (hc : IsLimit c) (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (ψ₁ ψ₂ : F ⟶ G)
    (h : (Scheme.Modules.pullback (c.π.app i)).map ψ₁ =
      (Scheme.Modules.pullback (c.π.app i)).map ψ₂) :
    ∃ (j : I) (e : j ⟶ i),
      (Scheme.Modules.pullback (D.map e)).map ψ₁ =
        (Scheme.Modules.pullback (D.map e)).map ψ₂ := by
  obtain ⟨j, gm, hj⟩ :=
    @exists_pullback_map_eq_of_isAffine (FullImage D) _ _ (ι D) (cone D c) (isLimitCone D hc)
      (fun j => inferInstanceAs (IsAffine (D.obj j.as))) ⟨i⟩ F G ‹_› ‹_› ψ₁ ψ₂ h
  refine ⟨j.as, hom D gm, ?_⟩
  rw [map_hom D gm]
  exact hj

end IndexHomUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end

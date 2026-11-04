module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms

/-!
# Restricting the neighbourhood comparison to an open neighbourhood

Let `i : Y ⟶ X` be a closed immersion and let `V ⊆ X` be an open neighbourhood of `Y`. Condition
(2) of [Stacks, Tag 0EK2] is a statement about a module on `X`, condition (3) one about a module
on such a `V`; passing from the first to the second needs the comparison

`colim_W Γ(W, ℱ) ⟶ lim_n Γ(Y_n, ℱ|_{Y_n})`

for `ℱ` on `X` to carry over to `ℱ|_V` on `V`, with `W` running over the opens of `V` containing
`Y` instead of the opens of `X` containing `Y`. This file proves that. Nothing is lost in the
passage, for two reasons: the opens of `V` containing `Y` are cofinal among the opens of `X`
containing `Y`, through `W ↦ V.ι ''ᵁ W` and `U ↦ V.ι ⁻¹ᵁ U`; and the infinitesimal neighbourhoods
of `Y` are the same schemes whether read over `X` or over `V`, so the two inverse limits are
identified termwise by the canonical comparison of an iterated pullback with the pullback along
the composite.

## Main definitions

* `Stacks.Algebraization.pullbackSectionsOn` — the pullback map on sections over an open, landing
  in the sections over any open identified with its preimage. It generalizes
  `AlgebraicGeometry.pullbackSectionsAt`, which is the case of the whole space.
* `Stacks.Algebraization.imageSectionsEquiv` — the resulting bijection between the sections of a
  module over `V.ι ''ᵁ W` and the sections of its restriction to `V` over `W`.

## Main results

* `Stacks.Algebraization.pullbackSectionsOn_factor` — pulling a section back along `f ≫ b` is
  pulling it back along `b` and then along `f`.
* `Stacks.Algebraization.pullbackObjFactorIso_naturality` and
  `Stacks.Algebraization.sectionsAt_factor_transition` — the comparison of
  `Stacks.Algebraization.pullbackObjFactorIso` is compatible with a further factorization, hence
  identifies the transition maps of the two inverse systems of sections.
* `Stacks.Algebraization.pullbackSectionsMap_apply_eq` — `AlgebraicGeometry.pullbackSectionsMap`
  is the pullback of a global section followed by that comparison.
* `Stacks.Algebraization.bijective_pullbackSectionsOn_ι` — for an open contained in `V`, pulling
  sections back along the inclusion of `V` is bijective.
* `Stacks.Algebraization.isSectionsComplete_restrict` — **the comparison restricts to an open
  neighbourhood.**

## Implementation notes

The identification `Γ(f_* ℳ, U) = Γ(ℳ, f ⁻¹ᵁ U)` holds by definition but only after unfolding a
semireducible definition, so a composite of maps on sections written across it is not type-correct
at the transparency `rw` and `simp` use to build their motives, and both tactics fail on such a
goal with a message about the pattern not occurring. Two measures keep that out of the way. Every
statement below is phrased so that each map on sections is spelled with the pullback it actually
comes from — this is what `pullbackSectionsOn` and
`Stacks.Algebraization.pullbackObjFactorIso` are for — and the steps that genuinely cross the
identification are carried out in term mode, with `Eq.trans` and `congrArg` in place of a rewrite,
exactly as the neighbourhood files this one builds on do for the projection separating `Γ(ℱ, U)`
from a presheaf's sections.

For the same reason the comparison of the two inverse systems is built from
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` rather than from
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`: the latter has the better
definitional behaviour on sections but the wrong one on the iterated pullbacks along the tower,
and it is needed only once, inside `bijective_pullbackSectionsOn_ι`, where the unit of the
restriction adjunction is compared with the unit of the pullback adjunction through
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`.

The structure morphisms of the lifted tower are never unfolded; they are only ever written
`((nbhdTower i V hV).obj n).hom` and consumed through `Stacks.Algebraization.nbhdOver_hom_ι`,
since they are built from `AlgebraicGeometry.IsOpenImmersion.lift` and pulling a module back along
a second spelling of one of them exhausts the kernel's budget.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

/-- A composite of morphisms of modules on sections. -/
public theorem comp_app_apply {Z : Scheme.{u}} {M N P : Z.Modules} (φ : M ⟶ N) (ψ : N ⟶ P)
    (U : Z.Opens) (t : Γ(M, U)) : (φ ≫ ψ).app U t = ψ.app U (φ.app U t) := by
  rw [Scheme.Modules.Hom.comp_app]
  exact ConcreteCategory.comp_apply _ _ t

/-- A morphism of modules commutes with the restriction maps of the underlying presheaves. -/
public theorem app_presheafMap_apply {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N)
    {W W' : Z.Opens} (j : W ⟶ W') (x : Γ(M, W')) :
    φ.app W (M.presheaf.map j.op x) = N.presheaf.map j.op (φ.app W' x) :=
  NatTrans.naturality_apply φ.mapPresheaf j.op x

/-- The comparison of an iterated pullback with the pullback along the composite inverts the
comparison in the other direction. -/
public theorem pullbackComp_hom_inv_apply {A B C : Scheme.{u}} (f : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules) (W : A.Opens)
    (x : Γ((Scheme.Modules.pullback (f ≫ b)).obj M, W)) :
    ((Scheme.Modules.pullbackComp f b).hom.app M).app W
        (((Scheme.Modules.pullbackComp f b).inv.app M).app W x) = x := by
  have h := ConcreteCategory.congr_hom (congrArg (fun χ => Scheme.Modules.Hom.app χ W)
    ((Scheme.Modules.pullbackComp f b).inv_hom_id_app M)) x
  rw [comp_app_apply, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at h
  exact h

/-- The unit of `f^* ⊣ f_*` at a composite, read elementwise on the sections over an open of the
target: pulling a section back in two steps agrees with pulling it back along the composite. -/
public theorem pullbackComp_unit_apply {A B C : Scheme.{u}} (f : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules) (U : C.Opens) (t : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f b).hom.app M).app (f ⁻¹ᵁ (b ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            ((Scheme.Modules.pullback b).obj M)).app (b ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U t)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ b)).unit.app M).app U t := by
  have key := ConcreteCategory.congr_hom
    (congrArg (fun χ => Scheme.Modules.Hom.app χ U) (pullbackComp_unit f b M)) t
  simp only [comp_app_apply, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app] at key
  exact (congrArg (fun z => ((Scheme.Modules.pullbackComp f b).hom.app M).app
      (f ⁻¹ᵁ (b ⁻¹ᵁ U)) z) key.symm).trans
    (pullbackComp_hom_inv_apply f b M (f ⁻¹ᵁ (b ⁻¹ᵁ U)) _)

/-- Restriction along an equality between an open and itself is the identity on sections. -/
public theorem presheafMap_eqToHom_rfl_apply {Z : Scheme.{u}} (M : Z.Modules) {W : Z.Opens}
    (e : W = W) (x : Γ(M, W)) : M.presheaf.map (eqToHom e).op x = x := by
  simp

/-- The pullback map from the sections of `M` over an open `U` to the sections of `f^* M` over an
open identified with the preimage of `U`. -/
public def pullbackSectionsOn {A B : Scheme.{u}} (f : A ⟶ B) (M : B.Modules) {U : B.Opens}
    {W : A.Opens} (hW : f ⁻¹ᵁ U = W) : Γ(M, U) ⟶ Γ((Scheme.Modules.pullback f).obj M, W) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
    ((Scheme.Modules.pullback f).obj M).presheaf.map (eqToHom hW.symm).op

/-- `Stacks.Algebraization.pullbackSectionsOn` on a section. -/
public theorem pullbackSectionsOn_apply {A B : Scheme.{u}} (f : A ⟶ B) (M : B.Modules)
    {U : B.Opens} {W : A.Opens} (hW : f ⁻¹ᵁ U = W) (t : Γ(M, U)) :
    pullbackSectionsOn f M hW t =
      ((Scheme.Modules.pullback f).obj M).presheaf.map (eqToHom hW.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U t) :=
  ConcreteCategory.comp_apply _ _ t

/-- Over an open whose preimage is everything this is `AlgebraicGeometry.pullbackSectionsAt`. -/
public theorem pullbackSectionsOn_top {A B : Scheme.{u}} (f : A ⟶ B) (M : B.Modules)
    {U : B.Opens} (hU : f ⁻¹ᵁ U = ⊤) : pullbackSectionsOn f M hU = pullbackSectionsAt f M hU :=
  rfl

/-- The comparison of a trivial factorization is the comparison of iterated pullbacks. -/
public theorem pullbackObjFactorIso_rfl_hom_app_apply {A B C : Scheme.{u}} (f : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules) (W : A.Opens)
    (z : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback b).obj M), W)) :
    (pullbackObjFactorIso M f (rfl : f ≫ b = f ≫ b)).hom.app W z =
      ((Scheme.Modules.pullbackComp f b).hom.app M).app W z := by
  rw [show (pullbackObjFactorIso M f (rfl : f ≫ b = f ≫ b)).hom =
      (Scheme.Modules.pullbackComp f b).hom.app M ≫ 𝟙 _ from rfl,
    comp_app_apply, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]

/-- Over the open `U` and its own preimage, `Stacks.Algebraization.pullbackSectionsOn` is the unit
of the pullback adjunction. -/
private theorem pullbackSectionsOn_rfl_apply {A B : Scheme.{u}} (f : A ⟶ B) (M : B.Modules)
    (U : B.Opens) (t : Γ(M, U)) :
    pullbackSectionsOn f M (rfl : f ⁻¹ᵁ U = f ⁻¹ᵁ U) t =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U t :=
  (pullbackSectionsOn_apply f M rfl t).trans (presheafMap_eqToHom_rfl_apply _ _ _)

/-- **Pulling a section back along a factorization.** If `f ≫ b = k` then restricting a section of
`M` over `U` to the pullback along `b` and then to the pullback along `f` gives, under the
canonical comparison, the restriction of the section to the pullback along `k`. -/
public theorem pullbackSectionsOn_factor {A B C : Scheme.{u}} (f : A ⟶ B) (b : B ⟶ C)
    {k : A ⟶ C} (hk : f ≫ b = k) (M : C.Modules) {U : C.Opens} {W : B.Opens}
    (hW : b ⁻¹ᵁ U = W) {W' : A.Opens} (hfW : f ⁻¹ᵁ W = W') (hU : k ⁻¹ᵁ U = W')
    (t : Γ(M, U)) :
    (pullbackObjFactorIso M f hk).hom.app W'
        (pullbackSectionsOn f ((Scheme.Modules.pullback b).obj M) hfW
          (pullbackSectionsOn b M hW t)) =
      pullbackSectionsOn k M hU t := by
  subst hk
  subst hW
  subst hfW
  have step1 := (pullbackSectionsOn_rfl_apply f ((Scheme.Modules.pullback b).obj M) _ _).trans
    (congrArg (fun y => ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback b).obj M)).app (b ⁻¹ᵁ U) y) (pullbackSectionsOn_rfl_apply b M U t))
  exact (congrArg (fun z => (pullbackObjFactorIso M f (rfl : f ≫ b = f ≫ b)).hom.app
        (f ⁻¹ᵁ (b ⁻¹ᵁ U)) z) step1).trans
    ((pullbackObjFactorIso_rfl_hom_app_apply f b M (f ⁻¹ᵁ (b ⁻¹ᵁ U)) _).trans
      ((pullbackComp_unit_apply f b M U t).trans
        (pullbackSectionsOn_rfl_apply (f ≫ b) M U t).symm))

/-- Transport of the pullback along a morphism equal to itself is the identity. -/
public theorem pullbackCongr_self_hom_app {A B : Scheme.{u}} {f : A ⟶ B} (hf : f = f)
    (M : B.Modules) : (Scheme.Modules.pullbackCongr hf).hom.app M = 𝟙 _ := rfl

/-- The associativity coherence for the pullback comparison isomorphisms. -/
public theorem pullbackComp_coherence {A B C D : Scheme.{u}} (f : A ⟶ B) (q : B ⟶ C) (j : C ⟶ D)
    (p : A ⟶ C) (w : f ≫ q = p) (F : D.Modules) :
    (Scheme.Modules.pullbackComp f (q ≫ j)).hom.app F ≫
        (Scheme.Modules.pullbackCongr
          (show f ≫ q ≫ j = p ≫ j by rw [← Category.assoc, w])).hom.app F ≫
        (Scheme.Modules.pullbackComp p j).inv.app F =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp q j).inv.app F) ≫
        (Scheme.Modules.pullbackComp f q).hom.app ((Scheme.Modules.pullback j).obj F) ≫
        (Scheme.Modules.pullbackCongr w).hom.app ((Scheme.Modules.pullback j).obj F) := by
  subst w
  have hassoc := CategoryTheory.NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_associativity f q j) F
  simp only [CategoryTheory.NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.associator_hom_app,
    Category.id_comp] at hassoc
  have h2 := congrArg
    (fun t => (Scheme.Modules.pullbackComp f (q ≫ j)).hom.app F ≫ t) hassoc
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at h2
  rw [pullbackCongr_self_hom_app (f := f ≫ q), Category.comp_id,
    ← cancel_mono ((Scheme.Modules.pullbackComp (f ≫ q) j).hom.app F), h2]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- **The comparison of a factorization is natural in the factorization.** For `g ≫ fm = fn`,
`fn ≫ b = kn`, `fm ≫ b = km` and `g ≫ km = kn`, the two ways of identifying the pullback of `F`
along `kn` with the iterated pullback along `g`, `fm` and `b` agree. -/
public theorem pullbackObjFactorIso_naturality {Z V Nn Nm : Scheme.{u}} (F : Z.Modules) (b : V ⟶ Z)
    {fn : Nn ⟶ V} {fm : Nm ⟶ V} (g : Nn ⟶ Nm) (hg : g ≫ fm = fn)
    {kn : Nn ⟶ Z} {km : Nm ⟶ Z} (hkn : fn ≫ b = kn) (hkm : fm ≫ b = km) (hgk : g ≫ km = kn) :
    (Scheme.Modules.pullback g).map (pullbackObjFactorIso F fm hkm).hom ≫
        (pullbackObjFactorIso F g hgk).hom =
      (pullbackObjFactorIso ((Scheme.Modules.pullback b).obj F) g hg).hom ≫
        (pullbackObjFactorIso F fn hkn).hom := by
  subst hkm
  subst hg
  subst hkn
  have hcoh := pullbackComp_coherence g fm b (g ≫ fm) rfl F
  simp only [pullbackCongr_self_hom_app, Category.comp_id] at hcoh
  have hGhGm : (Scheme.Modules.pullback g).map
        ((Scheme.Modules.pullbackComp fm b).hom.app F) ≫
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp fm b).inv.app F) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [pullbackObjFactorIso, Iso.app_hom]
  calc (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp fm b).hom.app F) ≫
        (Scheme.Modules.pullbackComp g (fm ≫ b)).hom.app F ≫
          (Scheme.Modules.pullbackCongr hgk).hom.app F
      = (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp fm b).hom.app F) ≫
          ((Scheme.Modules.pullbackComp g (fm ≫ b)).hom.app F ≫
            (Scheme.Modules.pullbackCongr hgk).hom.app F ≫
            (Scheme.Modules.pullbackComp (g ≫ fm) b).inv.app F) ≫
          (Scheme.Modules.pullbackComp (g ≫ fm) b).hom.app F := by
        simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    _ = (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp fm b).hom.app F) ≫
          ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp fm b).inv.app F) ≫
            (Scheme.Modules.pullbackComp g fm).hom.app ((Scheme.Modules.pullback b).obj F)) ≫
          (Scheme.Modules.pullbackComp (g ≫ fm) b).hom.app F := by rw [hcoh]
    _ = (Scheme.Modules.pullbackComp g fm).hom.app ((Scheme.Modules.pullback b).obj F) ≫
          (Scheme.Modules.pullbackComp (g ≫ fm) b).hom.app F := by
        rw [← Category.assoc, ← Category.assoc, hGhGm, Category.id_comp]

/-- `AlgebraicGeometry.pullbackSectionsMap` is the pullback of a global section along the
underlying morphism, followed by the comparison `Stacks.Algebraization.pullbackObjFactorIso`. -/
public theorem pullbackSectionsMap_apply_eq {Z : Scheme.{u}} (M : Z.Modules) {A B : Over Z}
    (g : A ⟶ B) (s : Γ((Scheme.Modules.pullback B.hom).obj M, ⊤)) :
    pullbackSectionsMap M g s =
      (pullbackObjFactorIso M g.left (Over.w g)).hom.app ⊤
        (pullbackSectionsAt g.left ((Scheme.Modules.pullback B.hom).obj M)
          (Opens.map_top g.left.base) s) := by
  have h1 : pullbackSectionsAt g.left ((Scheme.Modules.pullback B.hom).obj M)
        (Opens.map_top g.left.base) s =
      ((Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback B.hom).obj M)).presheaf.map
          (eqToHom (Opens.map_top g.left.base).symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback B.hom).obj M)).app ⊤ s) :=
    ConcreteCategory.comp_apply _ _ s
  have h2 : pullbackSectionsMap M g s =
      ((Scheme.Modules.pullback A.hom).obj M).presheaf.map
          (eqToHom (Opens.map_top g.left.base).symm).op
        ((pullbackObjFactorIso M g.left (Over.w g)).hom.app (g.left ⁻¹ᵁ ⊤)
          (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
            ((Scheme.Modules.pullback B.hom).obj M)).app ⊤ s)) :=
    (ConcreteCategory.comp_apply _ _ s).trans
      (congrArg (fun y => ((Scheme.Modules.pullback A.hom).obj M).presheaf.map
        (eqToHom (Opens.map_top g.left.base).symm).op y) (comp_app_apply _ _ ⊤ s))
  exact (h2.trans (app_presheafMap_apply (pullbackObjFactorIso M g.left (Over.w g)).hom
      (eqToHom (Opens.map_top g.left.base).symm) _).symm).trans
    (congrArg (fun y => (pullbackObjFactorIso M g.left (Over.w g)).hom.app ⊤ y) h1.symm)

/-- **The two canonical transition maps on global sections agree.** The comparison
`Stacks.Algebraization.pullbackObjFactorIso` intertwines the transition map of the inverse system
of sections over the schemes `Nn ⟶ V` with that of the inverse system over `Nn ⟶ Z`. -/
public theorem sectionsAt_factor_transition {Z V Nn Nm : Scheme.{u}} (F : Z.Modules) (b : V ⟶ Z)
    {fn : Nn ⟶ V} {fm : Nm ⟶ V} (g : Nn ⟶ Nm) (hg : g ≫ fm = fn)
    {kn : Nn ⟶ Z} {km : Nm ⟶ Z} (hkn : fn ≫ b = kn) (hkm : fm ≫ b = km) (hgk : g ≫ km = kn)
    (sm : Γ((Scheme.Modules.pullback fm).obj ((Scheme.Modules.pullback b).obj F), ⊤)) :
    (pullbackObjFactorIso F g hgk).hom.app ⊤
        (pullbackSectionsAt g ((Scheme.Modules.pullback km).obj F) (Opens.map_top g.base)
          ((pullbackObjFactorIso F fm hkm).hom.app ⊤ sm)) =
      (pullbackObjFactorIso F fn hkn).hom.app ⊤
        ((pullbackObjFactorIso ((Scheme.Modules.pullback b).obj F) g hg).hom.app ⊤
          (pullbackSectionsAt g ((Scheme.Modules.pullback fm).obj
            ((Scheme.Modules.pullback b).obj F)) (Opens.map_top g.base) sm)) := by
  have hnat := pullbackSectionsAt_natural g (pullbackObjFactorIso F fm hkm).hom
    (Opens.map_top g.base) sm
  rw [hnat]
  exact (comp_app_apply ((Scheme.Modules.pullback g).map (pullbackObjFactorIso F fm hkm).hom)
      (pullbackObjFactorIso F g hgk).hom ⊤ _).symm.trans
    ((congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤
        (pullbackSectionsAt g ((Scheme.Modules.pullback fm).obj
          ((Scheme.Modules.pullback b).obj F)) (Opens.map_top g.base) sm))
      (pullbackObjFactorIso_naturality F b g hg hkn hkm hgk)).trans
      (comp_app_apply _ _ ⊤ _))

/-- Pulling sections back along a morphism commutes with shrinking the open. -/
public theorem pullbackSectionsOn_restrict {A B : Scheme.{u}} (f : A ⟶ B) (M : B.Modules)
    {U U' : B.Opens} {W W' : A.Opens} (hW : f ⁻¹ᵁ U = W) (hW' : f ⁻¹ᵁ U' = W')
    (h : U' ≤ U) (h' : W' ≤ W) (t : Γ(M, U)) :
    pullbackSectionsOn f M hW' (M.presheaf.map (homOfLE h).op t) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h').op
        (pullbackSectionsOn f M hW t) := by
  subst hW
  subst hW'
  have hsub : ((Opens.map f.base).map (homOfLE h) : (f ⁻¹ᵁ U') ⟶ (f ⁻¹ᵁ U)) = homOfLE h' :=
    Subsingleton.elim _ _
  refine ((pullbackSectionsOn_rfl_apply f M U' _).trans (((app_presheafMap_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) (homOfLE h) t)).trans ?_)).trans
    (congrArg (fun y => ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h').op y)
      (pullbackSectionsOn_rfl_apply f M U t).symm)
  exact congrArg (fun j => ((Scheme.Modules.pullback f).obj M).presheaf.map (Quiver.Hom.op j)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U t)) hsub

/-- For an open `U` of `X` recovered from its intersection with `V`, the unit of `V.ι^* ⊣ V.ι_*`
is bijective on the sections over `U`. -/
public theorem bijective_unit_app_app_of_image {X : Scheme.{u}} (V : X.Opens) (F : X.Modules)
    (U : X.Opens) (hU : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U) :
    Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app F).app U) := by
  have h1 : IsIso (((Scheme.Modules.restrictAdjunction V.ι).unit.app F).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have he : (homOfLE (V.ι.image_preimage_le U) : (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) ⟶ U) = eqToHom hU :=
      Subsingleton.elim _ _
    rw [he]
    exact isIso_presheaf_map_eqToHom F hU
  have h2 : IsIso (((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app F)).app U) := by
    show IsIso (((Scheme.Modules.toPresheaf X).map
      ((Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app F))).app (.op U))
    infer_instance
  have hunit := congrArg (fun χ => Scheme.Modules.Hom.app χ U)
    ((Scheme.Modules.restrictAdjunction V.ι).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction V.ι) F)
  have h3 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app F).app U) := by
    rw [← hunit, Scheme.Modules.Hom.comp_app]
    exact IsIso.comp_isIso
  exact (ConcreteCategory.isIso_iff_bijective _).1 h3

/-- **The sections of a module over an open contained in `V` are the sections of its restriction
to `V` over the corresponding open.** -/
public theorem bijective_pullbackSectionsOn_ι {X : Scheme.{u}} (V : X.Opens) (F : X.Modules)
    {U : X.Opens} {W : V.toScheme.Opens} (hW : V.ι ⁻¹ᵁ U = W)
    (hU : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U) :
    Function.Bijective (pullbackSectionsOn V.ι F hW) := by
  have hb1 := bijective_unit_app_app_of_image V F U hU
  have hb2 := (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pullback V.ι).obj F).presheaf.map (eqToHom hW.symm).op)).1
      (isIso_presheaf_map_eqToHom ((Scheme.Modules.pullback V.ι).obj F) hW.symm)
  have hcomp := pullbackSectionsOn_apply V.ι F hW
  refine ⟨fun x y hxy => hb1.1 (hb2.1 ((hcomp x).symm.trans (hxy.trans (hcomp y)))), fun z => ?_⟩
  obtain ⟨y, hy⟩ := hb2.2 z
  obtain ⟨x, hx⟩ := hb1.2 y
  exact ⟨x, (hcomp x).trans ((congrArg (fun w => ((Scheme.Modules.pullback V.ι).obj F).presheaf.map
    (eqToHom hW.symm).op w) hx).trans hy)⟩

/-! ### Restriction of the comparison to an open neighbourhood -/

/-- Sections of `F` over the image of an open `W` of `V` are the sections of the restriction of `F`
to `V` over `W`. -/
public def imageSectionsEquiv {X : Scheme.{u}} (V : X.Opens) (F : X.Modules)
    (W : V.toScheme.Opens) : Γ(F, V.ι ''ᵁ W) ≃ Γ((Scheme.Modules.pullback V.ι).obj F, W) :=
  Equiv.ofBijective _ (bijective_pullbackSectionsOn_ι V F (V.ι.preimage_image_eq W)
    (by rw [V.ι.preimage_image_eq]))

/-- `Stacks.Algebraization.imageSectionsEquiv` is the canonical pullback map on sections. -/
public theorem imageSectionsEquiv_apply {X : Scheme.{u}} (V : X.Opens) (F : X.Modules)
    (W : V.toScheme.Opens) (t : Γ(F, V.ι ''ᵁ W)) :
    imageSectionsEquiv V F W t = pullbackSectionsOn V.ι F (V.ι.preimage_image_eq W) t := rfl

/-- Pulling back the preimage section of `t` along the inclusion recovers `t`. -/
private theorem pullbackSectionsOn_symm_apply {X : Scheme.{u}} (V : X.Opens) (F : X.Modules)
    (W : V.toScheme.Opens) (t : Γ((Scheme.Modules.pullback V.ι).obj F, W)) :
    pullbackSectionsOn V.ι F (V.ι.preimage_image_eq W) ((imageSectionsEquiv V F W).symm t) = t :=
  ((imageSectionsEquiv_apply V F W _).symm).trans ((imageSectionsEquiv V F W).apply_symm_apply t)

variable {Y X : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- The induced immersion into an open neighbourhood composes to the original one on points. -/
public theorem ι_comp_nbhdImmersion_base (V : X.Opens) (hV : Set.range i.base ⊆ V) :
    V.ι.base ∘ (nbhdImmersion i V hV).base = i.base := by
  rw [← TopCat.coe_comp, ← Scheme.Hom.comp_base, nbhdImmersion_ι]

/-- An open of `V` containing the support of the lifted tower has an image containing the image of
the immersion. -/
public theorem range_subset_image_of_support_subset (V : X.Opens) (hV : Set.range i.base ⊆ V)
    (W : V.toScheme.Opens) (hW : (nbhdTower i V hV).support ⊆ W) :
    (infTower i).support ⊆ (V.ι ''ᵁ W : X.Opens) := by
  have himg : ((V.ι ''ᵁ W : X.Opens) : Set X) = V.ι.base '' (W : Set V.toScheme) := by simp
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  rw [himg]
  exact ⟨(nbhdImmersion i V hV).base y, hW (Set.mem_range_self y),
    congrFun (ι_comp_nbhdImmersion_base i V hV) y⟩

/-- The preimage of an open containing the image of the immersion contains the support of the
lifted tower. -/
public theorem support_subset_preimage (V : X.Opens) (hV : Set.range i.base ⊆ V)
    (U : X.Opens) (hU : (infTower i).support ⊆ U) :
    (nbhdTower i V hV).support ⊆ (V.ι ⁻¹ᵁ U : V.toScheme.Opens) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  show V.ι.base ((nbhdImmersion i V hV).base y) ∈ (U : Set X)
  exact Set.mem_of_eq_of_mem (congrFun (ι_comp_nbhdImmersion_base i V hV) y)
    (hU (Set.mem_range_self y))

/-- The structure morphism of the lifted tower composes to that of the tower over `X`. -/
public theorem nbhdTower_obj_hom_ι (V : X.Opens) (hV : Set.range i.base ⊆ V) (n : ℕ) :
    ((nbhdTower i V hV).obj n).hom ≫ V.ι = ((infTower i).obj n).hom :=
  nbhdOver_hom_ι i V hV n

/-- **Completeness restricts to an open neighbourhood.** If the colimit of the sections of a module
`F` on `X` over the open neighbourhoods of a closed subscheme is the inverse limit of its sections
on the infinitesimal neighbourhoods, then the same holds for the restriction of `F` to any open
neighbourhood `V`, computed with the tower of infinitesimal neighbourhoods read over `V`. -/
public theorem isSectionsComplete_restrict (V : X.Opens) (hV : Set.range i.base ⊆ V)
    (F : X.Modules) (h : (infTower i).IsSectionsComplete F) :
    (nbhdTower i V hV).IsSectionsComplete ((Scheme.Modules.pullback V.ι).obj F) := by
  refine InfinitesimalTower.IsSectionsComplete.ofTowerMap (infTower i) (nbhdTower i V hV) F
    ((Scheme.Modules.pullback V.ι).obj F) (fun W => V.ι ''ᵁ W)
    (fun {_ _} hle => Scheme.Hom.image_mono _ hle) (fun {W W'} hle => ?_)
    (range_subset_image_of_support_subset i V hV)
    (fun U hU => ⟨V.ι ⁻¹ᵁ U, support_subset_preimage i V hV U hU, V.ι.image_preimage_le U⟩)
    (fun W _ => (imageSectionsEquiv V F W).symm)
    (fun W _ => (imageSectionsEquiv V F W).symm.bijective) ?_
    (fun n => (pullbackObjFactorIso F ((nbhdTower i V hV).obj n).hom
      (nbhdTower_obj_hom_ι i V hV n)).hom.app ⊤)
    (fun _ => bijective_app_of_isIso _ ⊤) ?_ ?_ h
  · rw [← V.ι.preimage_image_eq W', ← V.ι.preimage_image_eq W]
    exact leOfHom ((Opens.map V.ι.base).map (homOfLE hle))
  · intro W W' hW hW' hle t
    refine (imageSectionsEquiv V F W').injective ?_
    rw [Equiv.apply_symm_apply]
    refine ((imageSectionsEquiv_apply V F W' _).trans
      ((pullbackSectionsOn_restrict V.ι F (V.ι.preimage_image_eq W) (V.ι.preimage_image_eq W')
        (Scheme.Hom.image_mono _ hle) hle ((imageSectionsEquiv V F W).symm t)).trans ?_)).symm
    exact congrArg (fun y => ((Scheme.Modules.pullback V.ι).obj F).presheaf.map
        (homOfLE hle).op y)
      (pullbackSectionsOn_symm_apply V F W t)
  · intro n m hnm x
    exact ((congrArg (fun y => (pullbackObjFactorIso F ((nbhdTower i V hV).obj n).hom
              (nbhdTower_obj_hom_ι i V hV n)).hom.app ⊤ y)
            (pullbackSectionsMap_apply_eq ((Scheme.Modules.pullback V.ι).obj F)
              ((nbhdTower i V hV).trans n m hnm) x)).trans
          (sectionsAt_factor_transition F V.ι ((nbhdTower i V hV).trans n m hnm).left
            (Over.w ((nbhdTower i V hV).trans n m hnm)) (nbhdTower_obj_hom_ι i V hV n)
            (nbhdTower_obj_hom_ι i V hV m) (Over.w ((infTower i).trans n m hnm)) x).symm).trans
      (pullbackSectionsMap_apply_eq F ((infTower i).trans n m hnm)
        ((pullbackObjFactorIso F ((nbhdTower i V hV).obj m).hom
          (nbhdTower_obj_hom_ι i V hV m)).hom.app ⊤ x)).symm
  · intro W hW n t
    exact (congrArg (fun y => (pullbackObjFactorIso F ((nbhdTower i V hV).obj n).hom
          (nbhdTower_obj_hom_ι i V hV n)).hom.app ⊤
        (pullbackSectionsOn ((nbhdTower i V hV).obj n).hom
          ((Scheme.Modules.pullback V.ι).obj F)
          ((nbhdTower i V hV).preimage_eq_top hW n) y))
        (pullbackSectionsOn_symm_apply V F W t).symm).trans
      (pullbackSectionsOn_factor ((nbhdTower i V hV).obj n).hom V.ι
        (nbhdTower_obj_hom_ι i V hV n) F (V.ι.preimage_image_eq W)
        ((nbhdTower i V hV).preimage_eq_top hW n)
        ((infTower i).preimage_eq_top (range_subset_image_of_support_subset i V hV W hW) n)
        ((imageSectionsEquiv V F W).symm t))

end Stacks.Algebraization

end

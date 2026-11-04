module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms

/-!
# The comparison maps of a tower over a base form a cone

Let `M` be a module on a scheme `S` and let `U ⊆ S` be an open. A morphism `a : A ⟶ S` whose
image lands in `U`, i.e. with `a ⁻¹ᵁ U = ⊤`, has a comparison map
`AlgebraicGeometry.pullbackSectionsAt a M : Γ(M, U) ⟶ Γ(a^* M, ⊤)`. This file proves that these
comparison maps are compatible with a factorization `g ≫ b = a`: transporting the section
obtained on `B` down to `A` along `g` gives the section obtained on `A` directly.

## Main results

* `AlgebraicGeometry.pullbackSectionsAt_factor` — the cone property for a factorization
  `g ≫ b = a` of raw morphisms of schemes, stated through
  `Stacks.Algebraization.pullbackObjFactorIso`.
* `AlgebraicGeometry.pullbackSectionsMap_apply_factor` — the transition map
  `AlgebraicGeometry.pullbackSectionsMap` of a morphism of `CategoryTheory.Over S` is the
  composite of `AlgebraicGeometry.pullbackGlobalSections` with
  `Stacks.Algebraization.pullbackObjFactorIso`.
* `AlgebraicGeometry.pullbackSectionsAt_trans` — the cone property for a morphism of
  `CategoryTheory.Over S`: restricting a section of `M` on `S` to a bigger member of a tower and
  then transitioning down equals restricting it to the smaller member directly.

## Implementation notes

The mathematical content is the computation `AlgebraicGeometry.pullbackComp_unit` of the unit of
the pullback--pushforward adjunction at a composite, read on sections over `U` instead of over the
whole space. What has to be carried past it is the transport `eqToHom hb.symm` along
`b ⁻¹ᵁ U = ⊤` which is built into `AlgebraicGeometry.pullbackSectionsAt`: on one side of the
equation the transport happens in the middle of the composite and on the other side at the end,
and the two are exchanged by naturality of a morphism of modules on sections
(`AlgebraicGeometry.SectionsEqualizer.moduleHom_app_restrict`). The two transports are then
identified by `Subsingleton.elim`, the opens of a scheme being a partial order.

The elementwise vocabulary for the unit of the adjunction on global sections —
`AlgebraicGeometry.SectionsEqualizer.presheafMapTop_apply`,
`AlgebraicGeometry.SectionsEqualizer.moduleHom_app_restrict`,
`AlgebraicGeometry.SectionsEqualizer.moduleHom_app_preimage_top` and
`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit` — is taken from the Stacks 0EUA
file rather than restated here, which is why this module imports it.

As elsewhere in this directory, `rw` cannot cross the projection separating `Γ(M, U)` from the
sections of the underlying presheaf, so the proofs are in term mode, built from `Eq.trans`,
`congrArg`, `CategoryTheory.ConcreteCategory.comp_apply` and
`CategoryTheory.ConcreteCategory.congr_hom`. Everything is phrased with the structure morphisms
written out and a factorization equation supplied, rather than with objects of
`CategoryTheory.Over S`, because deciding `(CategoryTheory.Over.mk f).hom =?= f` inside the
argument of `AlgebraicGeometry.Scheme.Modules.pullback` exhausts the elaborator.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- An isomorphism of modules is a bijection on sections over any open. -/
private theorem moduleIso_hom_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (V : X.Opens) (y : Γ(N, V)) : e.hom.app V (e.inv.app V y) = y :=
  (ConcreteCategory.congr_hom
    (congrArg (fun χ => Scheme.Modules.Hom.app χ V) (Iso.inv_hom_id e)) y).trans
      (CategoryTheory.id_apply y)

/-- The comparison map on sections, written out as the unit of the adjunction followed by a
transport along `f ⁻¹ᵁ V = ⊤`. -/
private theorem pullbackSectionsAt_apply {W Y : Scheme.{u}} (f : W ⟶ Y) (F : Y.Modules)
    {V : Y.Opens} (hV : f ⁻¹ᵁ V = ⊤) (s : Γ(F, V)) :
    pullbackSectionsAt f F hV s =
      ((Scheme.Modules.pullback f).obj F).presheaf.map (eqToHom hV.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V s) :=
  ConcreteCategory.comp_apply _ _ s

/-- `AlgebraicGeometry.pullbackComp_unit` read on sections over an open `U`. -/
private theorem unit_comp_app {S A B : Scheme.{u}} (M : S.Modules) (b : B ⟶ S) (g : A ⟶ B)
    (U : S.Opens) (t : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp g b).inv.app M).app ((g ≫ b) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app M).app U t) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback b).obj M)).app (b ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U t) :=
  congrArg (fun χ : M ⟶ (Scheme.Modules.pushforward (g ≫ b)).obj
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj M)) =>
        Scheme.Modules.Hom.app χ U t)
    (pullbackComp_unit g b M)

/-- The two transports along `b ⁻¹ᵁ U = ⊤` and `(g ≫ b) ⁻¹ᵁ U = ⊤` agree, the opens of a scheme
being a partial order. -/
private theorem pushforward_presheaf_map_eqToHom {S A B : Scheme.{u}} (b : B ⟶ S) (g : A ⟶ B)
    (P : A.Modules) {U : S.Opens} (hb : b ⁻¹ᵁ U = ⊤) (hgb : (g ≫ b) ⁻¹ᵁ U = ⊤) :
    ((Scheme.Modules.pushforward g).obj P).presheaf.map (eqToHom hb.symm).op =
      P.presheaf.map (eqToHom hgb.symm).op := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  congr 1

/-- The comparison maps on sections over `U` are compatible with a composite: the section
obtained on `B` and then pulled back to `A` is the section obtained along `g ≫ b`. -/
private theorem pullbackSectionsAt_comp {S A B : Scheme.{u}} (M : S.Modules) (b : B ⟶ S)
    (g : A ⟶ B) {U : S.Opens} (hb : b ⁻¹ᵁ U = ⊤) (hgb : (g ≫ b) ⁻¹ᵁ U = ⊤) (t : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp g b).hom.app M).app ⊤
        (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj M)
          (pullbackSectionsAt b M hb t)) =
      pullbackSectionsAt (g ≫ b) M hgb t := by
  have e₁ : pullbackGlobalSections g ((Scheme.Modules.pullback b).obj M)
        (pullbackSectionsAt b M hb t) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback b).obj M)).app ⊤
        (((Scheme.Modules.pullback b).obj M).presheaf.map (eqToHom hb.symm).op
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U t)) :=
    (SectionsEqualizer.pullbackGlobalSections_unit g ((Scheme.Modules.pullback b).obj M) _).trans
      (congrArg (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pullback b).obj M)).app ⊤ z) (pullbackSectionsAt_apply b M hb t))
  have e₂ := SectionsEqualizer.moduleHom_app_restrict
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback b).obj M)) (eqToHom hb.symm)
    (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U t)
  have e₃ := ConcreteCategory.congr_hom
    (pushforward_presheaf_map_eqToHom b g
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj M)) hb hgb)
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback b).obj M)).app (b ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U t))
  have e₄ := SectionsEqualizer.moduleHom_app_restrict ((Scheme.Modules.pullbackComp g b).hom.app M)
    (eqToHom hgb.symm)
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback b).obj M)).app (b ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U t))
  have e₅ : ((Scheme.Modules.pullbackComp g b).hom.app M).app ((g ≫ b) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback b).obj M)).app (b ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U t)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app M).app U t :=
    (congrArg (fun z => ((Scheme.Modules.pullbackComp g b).hom.app M).app ((g ≫ b) ⁻¹ᵁ U) z)
      (unit_comp_app M b g U t).symm).trans
      (moduleIso_hom_inv_app ((Scheme.Modules.pullbackComp g b).app M) ((g ≫ b) ⁻¹ᵁ U) _)
  refine Eq.trans (congrArg
    (fun z => ((Scheme.Modules.pullbackComp g b).hom.app M).app ⊤ z) (e₁.trans e₂)) ?_
  refine Eq.trans (congrArg
    (fun z => ((Scheme.Modules.pullbackComp g b).hom.app M).app ⊤ z) e₃) ?_
  exact (e₄.trans (congrArg (fun z => ((Scheme.Modules.pullback (g ≫ b)).obj M).presheaf.map
    (eqToHom hgb.symm).op z) e₅)).trans (pullbackSectionsAt_apply (g ≫ b) M hgb t).symm

/-- The comparison map on sections over `U` only depends on the morphism, through
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
private theorem pullbackSectionsAt_congr {S A : Scheme.{u}} (M : S.Modules) {a a' : A ⟶ S}
    (h : a = a') {U : S.Opens} (ha : a ⁻¹ᵁ U = ⊤) (ha' : a' ⁻¹ᵁ U = ⊤) (t : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤ (pullbackSectionsAt a M ha t) =
      pullbackSectionsAt a' M ha' t := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- **The comparison maps on sections form a cone.** For a factorization `g ≫ b = a`, the section
of `a^* M` obtained from a section of `M` over `U` by first comparing along `b` and then
transporting along `g` is the section obtained by comparing along `a` directly. -/
public theorem pullbackSectionsAt_factor {S A B : Scheme.{u}} (M : S.Modules) {a : A ⟶ S}
    {b : B ⟶ S} (g : A ⟶ B) (hg : g ≫ b = a) {U : S.Opens}
    (hb : b ⁻¹ᵁ U = ⊤) (ha : a ⁻¹ᵁ U = ⊤) (t : Γ(M, U)) :
    (Stacks.Algebraization.pullbackObjFactorIso M g hg).hom.app ⊤
        (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj M)
          (pullbackSectionsAt b M hb t)) =
      pullbackSectionsAt a M ha t := by
  have hgb : (g ≫ b) ⁻¹ᵁ U = ⊤ := by rw [hg]; exact ha
  show ((Scheme.Modules.pullbackCongr hg).hom.app M).app ⊤
      (((Scheme.Modules.pullbackComp g b).hom.app M).app ⊤
        (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj M)
          (pullbackSectionsAt b M hb t))) = pullbackSectionsAt a M ha t
  exact (congrArg (fun z => ((Scheme.Modules.pullbackCongr hg).hom.app M).app ⊤ z)
    (pullbackSectionsAt_comp M b g hb hgb t)).trans
      (pullbackSectionsAt_congr M hg hgb ha t)

/-- The transition map of a morphism of `CategoryTheory.Over S` is the comparison map on global
sections followed by the identification of the iterated pullback. -/
public theorem pullbackSectionsMap_apply_factor {S : Scheme.{u}} (M : S.Modules)
    {A B : CategoryTheory.Over S} (g : A ⟶ B)
    (s : Γ((Scheme.Modules.pullback B.hom).obj M, ⊤)) :
    pullbackSectionsMap M g s =
      (Stacks.Algebraization.pullbackObjFactorIso M g.left (CategoryTheory.Over.w g)).hom.app ⊤
        (pullbackGlobalSections g.left ((Scheme.Modules.pullback B.hom).obj M) s) := by
  have h1 : pullbackSectionsMap M g s =
      (Stacks.Algebraization.pullbackObjFactorIso M g.left (CategoryTheory.Over.w g)).hom.app
          (g.left ⁻¹ᵁ (⊤ : B.left.Opens))
        (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback B.hom).obj M)).app ⊤ s) :=
    SectionsEqualizer.presheafMapTop_apply g.left ((Scheme.Modules.pullback A.hom).obj M) _
  exact h1.trans ((SectionsEqualizer.moduleHom_app_preimage_top g.left
    (Stacks.Algebraization.pullbackObjFactorIso M g.left (CategoryTheory.Over.w g)).hom _).trans
      (congrArg (fun z => (Stacks.Algebraization.pullbackObjFactorIso M g.left
        (CategoryTheory.Over.w g)).hom.app ⊤ z)
        (SectionsEqualizer.pullbackGlobalSections_unit g.left
          ((Scheme.Modules.pullback B.hom).obj M) s).symm))

/-- **The comparison maps of a tower of schemes over `S` form a cone.** Restricting a section of a
module on `S` to a bigger member of the tower and then transitioning down equals restricting it to
the smaller member directly. -/
public theorem pullbackSectionsAt_trans {S : Scheme.{u}} (M : S.Modules)
    {A B : CategoryTheory.Over S} (g : A ⟶ B) {U : S.Opens} (hb : B.hom ⁻¹ᵁ U = ⊤)
    (ha : A.hom ⁻¹ᵁ U = ⊤) (t : Γ(M, U)) :
    pullbackSectionsMap M g (pullbackSectionsAt B.hom M hb t) =
      pullbackSectionsAt A.hom M ha t :=
  (pullbackSectionsMap_apply_factor M g _).trans
    (pullbackSectionsAt_factor M g.left (CategoryTheory.Over.w g) hb ha t)

end AlgebraicGeometry

end


module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionRelocalize

/-!
# The chapter's convention on limits, under restriction and base change

Section 70.2 of the source (tag 07SD) assumes that every ring it considers has its spectrum in
the big fppf site. For an inverse system `D` of algebraic spaces with affine transition
morphisms, the rings in question are the directed colimits of the rings of the base changes
`Z ×_{D_i} D_k`, over a stage `i`, of the stages `k` over `i` to an affine test object `Z`; the
convention says that the limits of those diagrams lie in the site. That is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

The proofs of the chapter pass from one inverse system to others built from it: the stages at
or beyond a given one, and the base changes `D_k ×_Y T` of a system over `Y` along `T ⟶ Y`. The
rings these systems give rise to are rings the original system gives rise to, so the
convention for the original system is the convention for them. This file proves that.

## Main definitions

* `CategoryTheory.overOpSubtypeGeEquivalence`: the slice over `j` of the opposite of the upper
  set of `a` is the slice over `j` of the opposite of the whole preorder.

## Main results

* `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.limitInSite_of_equivalence`: the
  convention passes along an equivalence of slices identifying the diagrams of base changes.
* `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.comp_subtypeGe`: the convention passes
  to the stages at or beyond a given one.
* `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.baseChangeOverSystem`: the convention
  passes to a base change of the system.

## Implementation notes

The convention is a property of the limits of the underlying schemes of a diagram of base
changes, `AlgebraicGeometry.BigFppfOver.LimitInSite`, and so is invariant under isomorphism of
diagrams (`AlgebraicGeometry.BigFppfOver.LimitInSite.of_iso`) and under precomposition with an
initial functor (`AlgebraicGeometry.BigFppfOver.LimitInSite.comp_initial`). Both transfers are
instances of the first main result: for the stages the slices are equivalent and the diagrams
agree, and for a base change the slices are the same and the diagrams are isomorphic, because
`D_k ×_Y T = D_k ×_{D_i} (D_i ×_Y T)`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-- **The slices of the upper set of `a` are the slices of the whole order.** For a stage `j` at
or beyond `a`, the slice over `j` of the opposite of the upper set `{i // a ≤ i}` is the slice
over `j` of the opposite of the whole preorder: every index at or beyond `j` is at or beyond
`a`. The functor is `CategoryTheory.Over.post` of the inclusion. -/
def overOpSubtypeGeEquivalence {I : Type u} [Preorder I] (a : I) (j : {i : I // a ≤ i}ᵒᵖ) :
    Over j ≌ Over (op j.unop.1) :=
  CategoryTheory.Equivalence.mk (Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op)
    { obj k := Over.mk (X := j) (Y := op ⟨k.left.unop, j.unop.2.trans (leOfHom k.hom.unop)⟩)
        (homOfLE (show j.unop ≤ ⟨k.left.unop, j.unop.2.trans (leOfHom k.hom.unop)⟩ from
          leOfHom k.hom.unop)).op
      map {k l} f := Over.homMk (homOfLE
        (show (⟨l.left.unop, j.unop.2.trans (leOfHom l.hom.unop)⟩ : {i : I // a ≤ i}) ≤
          ⟨k.left.unop, j.unop.2.trans (leOfHom k.hom.unop)⟩ from leOfHom f.left.unop)).op
      map_id _ := rfl
      map_comp _ _ := rfl }
    (NatIso.ofComponents (fun k => Over.isoMk (Iso.refl _)) (fun _ => rfl))
    (NatIso.ofComponents (fun k => Over.isoMk (Iso.refl _)) (fun _ => rfl))

/-- The functor of `overOpSubtypeGeEquivalence a j` is `Over.post` of the inclusion of the
upper set. -/
@[simp]
theorem overOpSubtypeGeEquivalence_functor {I : Type u} [Preorder I] (a : I)
    (j : {i : I // a ≤ i}ᵒᵖ) :
    (overOpSubtypeGeEquivalence a j).functor =
      Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op := rfl

end CategoryTheory

namespace AlgebraicGeometry

section LimitInSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {J K : Type u} [Category.{u} J] [Category.{u} K]

/-- The convention for one diagram of the site passes to its precomposition with an initial
functor, which has the same limits. -/
theorem BigFppfOver.LimitInSite.comp_initial (G : K ⥤ J) [G.Initial] {V : J ⥤ BigFppfOver B S hS}
    (h : BigFppfOver.LimitInSite V) : BigFppfOver.LimitInSite (G ⋙ V) := by
  intro c hc
  let a : underlyingDiagram (G ⋙ V) ≅ G ⋙ underlyingDiagram V :=
    Functor.isoWhiskerRight (Functor.associator G V (BigFppfOver.forget B S hS)) B.inclusion ≪≫
      Functor.associator G (V ⋙ BigFppfOver.forget B S hS) B.inclusion
  let c' : Cone (G ⋙ underlyingDiagram V) := (Cone.postcompose a.hom).obj c
  have hc' : IsLimit c' := (IsLimit.postcomposeHomEquiv a c).symm hc
  have hl : IsLimit ((Functor.Initial.extendCone (F := G)).obj c') :=
    (Functor.Initial.isLimitExtendConeEquiv (F := G) c').symm hc'
  have hs := h _ hl
  exact hs

end LimitInSite

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
instance hasPullbacks_presheaf_baseChangeLimits :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_baseChangeLimits
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site
/-- **The convention passes along an identification of diagrams of base changes.** If the
slice over `i` is equivalent to the slice over `i'` by `e`, and the diagram of base changes of
`D` along `g` is the diagram of base changes of `D'` along `g'` read through `e`, then every
lift of the first has its limit in the site as soon as `D'` satisfies the convention: the lift
read through the inverse of `e` is a lift of the second. -/
theorem SiteContainsBaseChangeLimits.limitInSite_of_equivalence
    {J J' : Type u} [Category.{u} J] [Category.{u} J']
    {D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {D' : J' ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : SiteContainsBaseChangeLimits B S hS D') {i : J} {i' : J'} {Z : BigAffineFppf B S hS}
    {g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i}
    {g' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D'.obj i'}
    (e : Over i ≌ Over i')
    (α : (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)) ≅
      e.functor ⋙ (Over.post (X := i') D' ⋙ Over.pullback g') ⋙
        Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)))
    (W : Over i ⥤ BigAffineFppf B S hS)
    (hW : W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
      (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) :
    BigFppfOver.LimitInSite (W ⋙ BigAffineFppf.inclusion B S hS) := by
  have hiso : (e.inverse ⋙ W) ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
      (Over.post (X := i') D' ⋙ Over.pullback g') ⋙
        Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse (hW ≪≫ α) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.counitIso _ ≪≫
      Functor.leftUnitor _
  have hL' : BigFppfOver.LimitInSite
      (e.functor ⋙ e.inverse ⋙ W ⋙ BigAffineFppf.inclusion B S hS) :=
    BigFppfOver.LimitInSite.comp_initial e.functor
      (BigFppfOver.LimitInSite.of_iso (Functor.isoWhiskerRight (Functor.isoWhiskerRight
        (Functor.associator _ _ _).symm (BigFppfOver.forget B S hS)) B.inclusion)
        (h i' Z g' (e.inverse ⋙ W) hiso))
  refine BigFppfOver.LimitInSite.of_iso (Functor.isoWhiskerRight (Functor.isoWhiskerRight
    ?_ (BigFppfOver.forget B S hS)) B.inclusion) hL'
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.unitIso _ ≪≫
    Functor.associator _ _ _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site
/-- Base changing along a point `g` of a stage `D_i ×_Y T` of the base-changed system is base
changing along the point `g ≫ pr₁` of `D_i`: the stage `D_j ×_Y T` is `D_j ×_{D_i} (D_i ×_Y T)`. -/
theorem isPullback_baseChangeOverSystem_pullback {I : Type u} [Preorder I]
    {Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) {i j : Iᵒᵖ} (φ : j ⟶ i)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ (baseChangeOverSystem B S hS Dsys t u).obj i) :
    IsPullback
      (pullback.fst ((baseChangeOverSystem B S hS Dsys t u).map φ) g ≫
        (baseChangeOverProj B S hS Dsys t u).app j)
      (pullback.snd ((baseChangeOverSystem B S hS Dsys t u).map φ) g)
      (Dsys.map φ) (g ≫ (baseChangeOverProj B S hS Dsys t u).app i) :=
  (IsPullback.of_hasPullback ((baseChangeOverSystem B S hS Dsys t u).map φ) g).paste_horiz
    (isPullback_baseChangeOverMap B S hS (t.app j) (t.app i) (Dsys.map φ) (by simp) u).flip

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site
/-- The identifications of `AlgebraicGeometry.Space.isPullback_baseChangeOverSystem_pullback`
are compatible with the transition morphisms. -/
theorem isPullback_baseChangeOverSystem_pullback_isoPullback_naturality {I : Type u}
    [Preorder I] {Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y)
    (u : T ⟶ Y) {i j k : Iᵒᵖ} (φ : j ⟶ i) (ψ : k ⟶ i) (a : j ⟶ k)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ (baseChangeOverSystem B S hS Dsys t u).obj i)
    (w : (pullback.fst ((baseChangeOverSystem B S hS Dsys t u).map φ) g ≫
        (baseChangeOverSystem B S hS Dsys t u).map a) ≫
          (baseChangeOverSystem B S hS Dsys t u).map ψ =
      pullback.snd ((baseChangeOverSystem B S hS Dsys t u).map φ) g ≫ g)
    (w' : (pullback.fst (Dsys.map φ) (g ≫ (baseChangeOverProj B S hS Dsys t u).app i) ≫
        Dsys.map a) ≫ Dsys.map ψ =
      pullback.snd (Dsys.map φ) (g ≫ (baseChangeOverProj B S hS Dsys t u).app i) ≫
        (g ≫ (baseChangeOverProj B S hS Dsys t u).app i)) :
    pullback.lift _ _ w ≫
        (isPullback_baseChangeOverSystem_pullback Dsys t u ψ g).isoPullback.hom =
      (isPullback_baseChangeOverSystem_pullback Dsys t u φ g).isoPullback.hom ≫
        pullback.lift _ _ w' := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
      pullback.lift_fst_assoc, IsPullback.isoPullback_hom_fst_assoc]
    rw [(baseChangeOverProj B S hS Dsys t u).naturality]
  · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site
/-- The diagram of base changes, along a point `g` of a stage `D_i ×_Y T` of the base-changed
system, of the stages over that one is the diagram of base changes, along the point `g ≫ pr₁`
of `D_i`, of the stages of `D` over `i`. -/
noncomputable def baseChangeOverSystemDiagramIso {I : Type u} [Preorder I]
    {Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) {i : Iᵒᵖ}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ (baseChangeOverSystem B S hS Dsys t u).obj i) :
    (Over.post (X := i) (baseChangeOverSystem B S hS Dsys t u) ⋙ Over.pullback g) ⋙
        Over.forget Z ≅
      (Over.post (X := i) Dsys ⋙
        Over.pullback (g ≫ (baseChangeOverProj B S hS Dsys t u).app i)) ⋙ Over.forget Z :=
  NatIso.ofComponents
    (fun k => (isPullback_baseChangeOverSystem_pullback Dsys t u k.hom g).isoPullback)
    (fun {k l} f => isPullback_baseChangeOverSystem_pullback_isoPullback_naturality Dsys t u
      k.hom l.hom f.left g _ _)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site
/-- **The chapter's convention passes to a base change of the system.** If every limit of the
base changes of the stages of `D` over one stage to an affine test object lies in the site,
then so does every such limit for the system `D_j ×_Y T` of base changes along `u : T ⟶ Y`:
by `AlgebraicGeometry.Space.baseChangeOverSystemDiagramIso` each of its diagrams is one of
those of `D`. -/
theorem SiteContainsBaseChangeLimits.baseChangeOverSystem {I : Type u} [Preorder I]
    {Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : SiteContainsBaseChangeLimits B S hS Dsys)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) :
    SiteContainsBaseChangeLimits B S hS (baseChangeOverSystem B S hS Dsys t u) := by
  intro i Z g W hW
  exact h.limitInSite_of_equivalence (CategoryTheory.Equivalence.refl)
    (baseChangeOverSystemDiagramIso Dsys t u g ≪≫ (Functor.leftUnitor _).symm) W hW

/-- **The chapter's convention passes to the stages at or beyond a given one.** Every diagram of
base changes of the restricted system is, through
`CategoryTheory.overOpSubtypeGeEquivalence`, one of the original system. -/
theorem SiteContainsBaseChangeLimits.comp_subtypeGe {I : Type u} [Preorder I]
    {Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : SiteContainsBaseChangeLimits B S hS Dsys) (a : I) :
    SiteContainsBaseChangeLimits B S hS ((Subtype.mono_coe fun i => a ≤ i).functor.op ⋙ Dsys) := by
  intro j Z g W hW
  exact h.limitInSite_of_equivalence (g' := g) (overOpSubtypeGeEquivalence a j) (Iso.refl _) W hW

end Space

end AlgebraicGeometry

module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.PointSimplicialFlat
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget

/-!
# Flatness of the face morphisms of the point simplicial site

For a cosimplicial commutative ring `A`, viewed as a sheaf of rings on the total site of the
constant simplicial site on the point, the morphism of ringed topoi `f_φ` induced by a simplex map
`φ` is flat as soon as the ring map `A(φ)` is flat.

## Main results

* `CategoryTheory.PointSimplicialSite.isFlat_transitionRingedToposHom`: the morphism of ringed
  topoi `f_φ` is flat when `A(φ)` is flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.PointSimplicialSite

noncomputable section

variable (A : SimplexCategory ⥤ CommRingCat.{u})

/-- The transition `f_φ⁻¹O_m ⟶ O_n` of the sheaf of rings defined by `A`, evaluated at the
point, is a flat ring map as soon as `A(φ)` is flat. -/
theorem flat_fiberTransitionCommRing_app {m n : SimplexCategory} (φ : m ⟶ n)
    (hφ : (A.map φ).hom.Flat) :
    ((situation.{u}.fiberTransitionCommRing (ringSheaf A) φ).hom.app (op pt)).hom.Flat := by
  let O := ringSheaf A
  let g := situation.{u}.fiberTransitionCommRing O φ
  let f := situation.{u}.transitionMorphism φ
  let F := commRingImageAdjunction f
  let J : GrothendieckTopology Pt.{u} := coverage.{u}.toGrothendieck
  have : (𝟭 Pt.{u}).IsContinuous J J := inferInstance
  let Om := (situation.{u}.componentRingedTopos O m).O
  let R := (situation.{u}.transitionInverseImageCommRing φ).obj Om
  let S' := (situation.{u}.componentRingedTopos O n).O
  let eR := restrictionCommRingIso J J (𝟭 Pt.{u}) R
  let eS := restrictionCommRingIso J J (𝟭 Pt.{u}) S'
  have hnat : (pushforwardCommRingFunctor f).map g ≫ eS.hom =
      eR.hom ≫ ((𝟭 Pt.{u}).sheafPushforwardContinuous CommRingCat.{u} J J).map g :=
    (restrictionCommRingNatIso J J (𝟭 Pt.{u})).hom.naturality g
  have e2 : F.homEquiv _ _ g = F.unit.app Om ≫ (pushforwardCommRingFunctor f).map g :=
    F.homEquiv_unit _ _ _
  have hu : Function.Bijective ((F.unit.app Om).hom.app (op pt)).hom := by
    have h1 := forget_map_commRingImageAdjunction_unit_app f Om
    let X := (sheafCompose (situation.{u}.componentTopology m) (forget CommRingCat.{u})).obj Om
    have h2 : IsIso (f.adj.unit.app X) := @isIso_unit_id J this _
    have h4 : IsIso ((f.adj.unit.app X).hom.app (op pt)) := by
      have := h2
      have : IsIso ((sheafToPresheaf _ (Type u)).map (f.adj.unit.app X)) := Functor.map_isIso _ _
      exact NatIso.isIso_app_of_isIso ((sheafToPresheaf _ (Type u)).map (f.adj.unit.app X)) (op pt)
    have h6 : ⇑((F.unit.app Om).hom.app (op pt)).hom = (f.adj.unit.app X).hom.app (op pt) :=
      congrArg (fun k => (k.hom.app (op pt) : _ → _)) h1
    rw [h6]
    exact (isIso_iff_bijective _).1 h4
  have hA : ∀ x, ((F.homEquiv _ _ g).hom.app (op pt)).hom x = (A.map φ).hom x := by
    intro x
    have h1 := forget_map_commRingImageAdjunction_homEquiv f Om S' g
    have h2 := congrArg (fun k => k.hom.app (op pt) x) h1
    refine h2.trans ?_
    rw [situation.{u}.fiberTransitionCommRing_forget O φ]
    exact (congrArg (fun k => k.hom.app (op pt) x) (situation.{u}.fiberTransition_adj φ
      ((sheafCompose situation.{u}.totalTopology (forget CommRingCat.{u})).obj O))).trans rfl
  have key : ∀ x, (g.hom.app (op pt)).hom ((eR.hom.hom.app (op pt)).hom
      (((F.unit.app Om).hom.app (op pt)).hom x)) = (A.map φ).hom x := by
    intro x
    have h1 := congrArg (fun k => (k.hom.app (op pt)).hom (((F.unit.app Om).hom.app (op pt)).hom x))
      hnat
    have h2 := congrArg (fun k => (k.hom.app (op pt)).hom x) e2
    exact h1.symm.trans (h2.symm.trans (hA x))
  let v : Om.obj.obj (op pt) ⟶ R.obj.obj (op pt) :=
    (F.unit.app Om).hom.app (op pt) ≫ eR.hom.hom.app (op pt)
  have hv : Function.Bijective v.hom := hu
  let e := RingEquiv.ofBijective v.hom hv
  let a : Om.obj.obj (op pt) ⟶ S'.obj.obj (op pt) := A.map φ
  have ha : a.hom.Flat := hφ
  have hg : g.hom.app (op pt) = e.toCommRingCatIso.inv ≫ a := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (key x).trans (congrArg a.hom (e.symm_apply_apply x).symm)
  rw [hg]
  exact RingHom.Flat.comp (f := e.symm.toRingHom) (RingHom.Flat.of_bijective e.symm.bijective) ha

/-- **Flatness of `f_φ` on the point.** For a cosimplicial commutative ring `A`, viewed as a sheaf
of rings on the total site of the constant simplicial site on the point, the morphism of ringed
topoi `f_φ` induced by a simplex map `φ` is flat as soon as the ring map `A(φ)` is flat. -/
theorem isFlat_transitionRingedToposHom {m n : SimplexCategory} (φ : m ⟶ n)
    (hφ : (A.map φ).hom.Flat) :
    (situation.{u}.transitionRingedToposHom (ringSheaf A) φ).IsFlat := by
  have h := isFlatMap_of_flat_app (componentTopology_eq_bot n) _
    (flat_fiberTransitionCommRing_app A φ hφ)
  rw [← SimplicialSiteSituation.transitionRingedToposHom_fSharpInverseImage] at h
  exact h

end

end CategoryTheory.PointSimplicialSite

end

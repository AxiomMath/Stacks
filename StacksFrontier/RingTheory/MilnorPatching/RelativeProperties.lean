module

public import Mathlib
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.FinitePresentation
public import StacksFrontier.RingTheory.MilnorPatching.ModuleProperties
public import StacksFrontier.RingTheory.MilnorPatching.Relative
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback

/-!
# Flatness, finiteness and finite presentation of relatively glued modules

Work in the relative situation of a fibre product `B' = B ×_A A'` together with a ring map
`B' → D'` and the base-change rings `D`, `C'`, `C`.  Gluing a compatible pair of a `D`-module and
a `C'`-module preserves each of the three properties one expects: flatness over `B'`, finiteness,
and — under a factorization hypothesis on `B' → D'` — finite presentation.  Flatness moreover goes
both ways and yields an equivalence between the flat `D'`-modules and the compatible pairs of
flat modules.

## Main results

* `MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct` is Stacks Tag 07RW: relative
  flatness of a glued pair, canonical reconstruction of a relatively flat module from its two
  scalar extensions, and the resulting equivalence of the two full subcategories.
* `MilnorPatching.finite_relativeRightAdjoint_obj_of_finite_components` is Stacks Tag 08IH: the
  glued module is finite over `D'` when its two components are finite.
* `MilnorPatching.finitePresentation_rightAdjoint_obj_of_factorization` is Stacks Tag 08KP: the
  glued module is finitely presented over `D'` when its components are finitely presented and
  relatively flat and `B' → D'` factors as a flat algebra followed by a finitely presented ring
  map.

## Implementation notes

Flatness over a smaller ring is always stated after restriction of scalars, and canonical
reconstruction is phrased as the unit of the relative adjunction being an isomorphism; the
equivalences of subcategories are required to commute up to natural isomorphism with both ambient
functors, which is what makes them the canonical ones.  The glued module appears as the value of a
right adjoint with invertible counit, and
`MilnorPatching.relativeCompatiblePairsRightAdjoint_counit_isIso` is the bridge to the source's
explicitly named fibre product `N ×_M M'`: uniqueness of right adjoints identifies any right
adjoint occurring in a statement naturally with that one.  In Tag 08KP the factorization is given
by two ring homomorphisms, flatness of the first encoded by the induced module structure and
finite presentation of the second by `RingHom.FinitePresentation`.

## References

* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
* [Stacks Project, Tag 08IH](https://stacks.math.columbia.edu/tag/08IH)
* [Stacks Project, Tag 08KP](https://stacks.math.columbia.edu/tag/08KP)
-/

section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct
open ModuleGlueing
universe u v₁ v₂ u₁ u₂
namespace MilnorPatching

private theorem adjunction_mate_unit
    {C : Type u₁} {D : Type u₂} {C' : Type*} {D' : Type*}
    [Category.{v₁} C] [Category.{v₂} D] [Category C'] [Category D']
    {E : C ⥤ D} {F : D ⥤ C} {Eb : C' ⥤ D'} {Fb : D' ⥤ C'}
    (adj : E ⊣ F) (adjb : Eb ⊣ Fb)
    (R : D ⥤ D') (S : C ⥤ C') (α : E ⋙ R ≅ S ⋙ Eb) (L : C) :
    S.map (adj.unit.app L) ≫
        (adjb.homEquiv _ _)
          (α.inv.app (F.obj (E.obj L)) ≫ R.map (adj.counit.app (E.obj L))) =
      adjb.unit.app (S.obj L) ≫ Fb.map (α.inv.app L) := by
  apply (adjb.homEquiv _ _).symm.injective
  rw [adjb.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
    adjb.homEquiv_naturality_right_symm]
  simp only [Functor.id_obj, adjb.homEquiv_symm_unit, Category.id_comp]
  rw [← Category.assoc]
  show ((S ⋙ Eb).map (adj.unit.app L) ≫ α.inv.app _) ≫ _ = _
  rw [α.inv.naturality]
  simp only [Functor.comp_map, Category.assoc, ← R.map_comp]
  have ht : E.map (adj.unit.app L) ≫ adj.counit.app (E.obj L) = 𝟙 _ :=
    adj.left_triangle_components L
  rw [ht, R.map_id]
  exact Category.comp_id _

private theorem compatiblePairs_restrictScalars_iff
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : RelativeModuleFibreProductSituation (D' := D') base)
    (X : RelativeModuleFibreProductSituation.CompatibleModules s)
    (n : X.fst) (m : X.snd) :
    let : Module B X.fst := Module.compHom X.fst s.BtoD
    let : Module A' X.snd := Module.compHom X.snd s.A'toC'
    X.iso.hom ((1 : s.C) ⊗ₜ[s.D,s.DtoC] n) =
        (1 : s.C) ⊗ₜ[s.C',s.C'toC] m ↔
      ((s.restrictCompatibleModules.obj X).iso.hom)
          ((1 : A) ⊗ₜ[B,toBase] n) =
        (1 : A) ⊗ₜ[A',surjection] m := by
  dsimp only
  let : Module B X.fst := Module.compHom X.fst s.BtoD
  let : Module A' X.snd := Module.compHom X.snd s.A'toC'
  let α := s.restrictionSndIso
  let β := s.restrictionFstIso
  have ha : (α.inv.app X.snd) ((1 : A) ⊗ₜ[A',surjection] m) =
      (1 : s.C) ⊗ₜ[s.C',s.C'toC] m := by
    simpa only [map_one] using s.restrictionSndIso_inv_tmul X.snd 1 m
  have hb : (β.inv.app X.fst) ((1 : A) ⊗ₜ[B,toBase] n) =
      (1 : s.C) ⊗ₜ[s.D,s.DtoC] n := by
    simpa only [map_one] using s.restrictionFstIso_inv_tmul X.fst 1 n
  have hinj : Function.Injective (α.inv.app X.snd : _ → _) :=
    (ConcreteCategory.bijective_of_isIso (α.inv.app X.snd)).1
  rw [← hinj.eq_iff, ha]
  show _ ↔ (α.inv.app X.snd)
    ((α.hom.app X.snd) (X.iso.hom ((β.inv.app X.fst) _))) = _
  rw [hb]
  show _ ↔ (α.hom.app X.snd ≫ α.inv.app X.snd) _ = _
  rw [α.hom_inv_id_app]
  rfl

set_option maxHeartbeats 2000000 in
-- The mate comparison elaborates several nested scalar-extension and restriction functors.
/-- **Stacks Project, Tag 07RW.** In a relative fibre-product situation, compatible pairs
whose components are flat over the original rings glue to a module flat over the original
fibre-product ring. Every relatively flat module is canonically reconstructed from its scalar
extensions, and these operations induce an equivalence of the corresponding full
subcategories.

Relative flatness, canonical reconstruction, and gluing of relatively flat modules. -/
@[stacks 07RW]
public theorem relativelyFlatModulesEquivalenceOverFibreProduct
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : RelativeModuleFibreProductSituation (D' := D') base) :
    let E := (letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A))
    let flatSource : ObjectProperty (ModuleCat.{u} D') :=
      fun L ↦ Module.Flat base.fibreProduct
        ((ModuleCat.restrictScalars.{u, u, u} s.toD').obj L)
    let flatTarget : ObjectProperty
        (RelativeModuleFibreProductSituation.CompatibleModules s) :=
      fun X ↦
        Module.Flat B ((ModuleCat.restrictScalars.{u, u, u} s.BtoD).obj X.fst) ∧
          Module.Flat A'
            ((ModuleCat.restrictScalars.{u, u, u} s.A'toC').obj X.snd)
    ∃ (F : RelativeModuleFibreProductSituation.CompatibleModules s ⥤
          ModuleCat.{u} D')
      (e : ∀ X, F.obj X ≃ₗ[D']
          compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm X)
      (adj : E ⊣ F),
      (∀ (L : ModuleCat.{u} D') (X) (h : L ⟶ F.obj X) (l : L),
          (e X (h l)).1.1 =
              ((adj.homEquiv L X).symm h).fst
                ((1 : s.D) ⊗ₜ[D',s.toD] l) ∧
            (e X (h l)).1.2 =
              ((adj.homEquiv L X).symm h).snd
                ((1 : s.C') ⊗ₜ[D',s.toC'] l)) ∧
        (∀ {X Y} (f : X ⟶ Y) (p : F.obj X),
          (e Y (F.map f p)).1.1 = f.fst (e X p).1.1 ∧
            (e Y (F.map f p)).1.2 = f.snd (e X p).1.2) ∧
        IsIso adj.counit ∧
        (∀ X, flatTarget X → flatSource (F.obj X)) ∧
        (∀ L, flatSource L → IsIso (adj.unit.app L)) ∧
        ∃ q : flatSource.FullSubcategory ≌ flatTarget.FullSubcategory,
          Nonempty (flatSource.ι ⋙ E ≅ q.functor ⋙ flatTarget.ι) ∧
            Nonempty (flatTarget.ι ⋙ F ≅ q.inverse ⋙ flatSource.ι) := by
  classical
  obtain ⟨F_r, e_r, adj_r, nat_r, form_r⟩ :=
    exists_rightAdjoint_extensionOfScalarsToPullback
      s.toD s.toC' s.DtoC s.C'toC
      s.relativeSquare_comm
  obtain ⟨F_b, e_b, adj_b, form_b, counit_b, flat_b, unit_b, _⟩ :=
    flatModulesEquivalenceOverFibreProduct toBase surjection I base
  let R := s.restrictCompatibleModules
  let S := ModuleCat.restrictScalars.{u, u, u} s.toD'
  let α := s.restrictionSquareIso
  let Eb := extensionOfScalarsToPullback
    base.pullbackCone.fst.hom base.pullbackCone.snd.hom toBase surjection
    (RingHom.pullback_comm_sq toBase surjection)
  let Er := extensionOfScalarsToPullback
    s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm
  let z (X : s.CompatibleModules) : Eb.obj (S.obj (F_r.obj X)) ⟶ R.obj X :=
    α.inv.app (F_r.obj X) ≫ R.map (adj_r.counit.app X)
  let h (X : s.CompatibleModules) : S.obj (F_r.obj X) ⟶ F_b.obj (R.obj X) :=
    (adj_b.homEquiv (S.obj (F_r.obj X)) (R.obj X)) (z X)
  have hIso (X : s.CompatibleModules) : IsIso (h X) := by
    let z := z X
    let h := h X
    have αfst_unit_inv (x : F_r.obj X) :
        (α.inv.app (F_r.obj X)).fst
            ((1 : B) ⊗ₜ[base.fibreProduct,base.pullbackCone.fst.hom]
              (show S.obj (F_r.obj X) from x)) =
          (1 : s.D) ⊗ₜ[D',s.toD] x := by
      simpa only [map_one] using s.restrictionSquareIso_inv_fst_tmul (F_r.obj X) 1 x
    have αsnd_unit_inv (x : F_r.obj X) :
        (α.inv.app (F_r.obj X)).snd
            ((1 : A') ⊗ₜ[base.fibreProduct,base.pullbackCone.snd.hom]
              (show S.obj (F_r.obj X) from x)) =
          (1 : s.C') ⊗ₜ[D',s.toC'] x := by
      simpa only [map_one] using s.restrictionSquareIso_inv_snd_tmul (F_r.obj X) 1 x
    have hcoord (x : F_r.obj X) :
        (e_b (R.obj X) (h x)).1.1 = (e_r X x).1.1 ∧
        (e_b (R.obj X) (h x)).1.2 = (e_r X x).1.2 := by
      have hb := form_b (S.obj (F_r.obj X)) (R.obj X) h x
      have hr := form_r (F_r.obj X) X (𝟙 _) x
      have hzx : (adj_b.homEquiv (S.obj (F_r.obj X)) (R.obj X)).symm h = z :=
        (adj_b.homEquiv (S.obj (F_r.obj X)) (R.obj X)).symm_apply_apply z
      rw [hzx] at hb
      rw [adj_r.homEquiv_symm_id] at hr
      constructor
      · rw [hb.1]
        show (adj_r.counit.app X).fst
          ((α.inv.app (F_r.obj X)).fst
            ((1 : B) ⊗ₜ[base.fibreProduct,base.pullbackCone.fst.hom]
              (show S.obj (F_r.obj X) from x))) = (e_r X x).1.1
        rw [αfst_unit_inv]
        have hr1 := hr.1
        change (e_r X x).1.1 = (adj_r.counit.app X).fst
          ((1 : s.D) ⊗ₜ[D',s.toD] x) at hr1
        exact hr1.symm
      · rw [hb.2]
        show (adj_r.counit.app X).snd
          ((α.inv.app (F_r.obj X)).snd
            ((1 : A') ⊗ₜ[base.fibreProduct,base.pullbackCone.snd.hom]
              (show S.obj (F_r.obj X) from x))) = (e_r X x).1.2
        rw [αsnd_unit_inv]
        have hr2 := hr.2
        change (e_r X x).1.2 = (adj_r.counit.app X).snd
          ((1 : s.C') ⊗ₜ[D',s.toC'] x) at hr2
        exact hr2.symm
    have hinj : Function.Injective (h : S.obj (F_r.obj X) → F_b.obj (R.obj X)) := by
      intro x y hxy
      apply (e_r X).injective
      apply Subtype.ext
      apply Prod.ext
      · have hz := congrArg (fun t => (e_b (R.obj X) t).1.1) hxy
        exact (hcoord x).1.symm.trans (hz.trans (hcoord y).1)
      · have hz := congrArg (fun t => (e_b (R.obj X) t).1.2) hxy
        exact (hcoord x).2.symm.trans (hz.trans (hcoord y).2)
    have hsurj : Function.Surjective
        (h : S.obj (F_r.obj X) → F_b.obj (R.obj X)) := by
      intro y
      let p := e_b (R.obj X) y
      have hp : X.iso.hom ((1 : s.C) ⊗ₜ[s.D,s.DtoC] (show X.fst from p.1.1)) =
          (1 : s.C) ⊗ₜ[s.C',s.C'toC] (show X.snd from p.1.2) :=
        (compatiblePairs_restrictScalars_iff s X p.1.1 p.1.2).mpr p.2
      let pr : CompatiblePairs s.DtoC s.C'toC X := ⟨p.1, hp⟩
      let x : F_r.obj X := (e_r X).symm pr
      refine ⟨x, ?_⟩
      apply (e_b (R.obj X)).injective
      apply Subtype.ext
      apply Prod.ext
      · exact (hcoord x).1.trans (by simp [x, pr, p])
      · exact (hcoord x).2.trans (by simp [x, pr, p])
    exact (ConcreteCategory.isIso_iff_bijective h).2 ⟨hinj, hsurj⟩
  have hz (X : s.CompatibleModules) :
      Eb.map (h X) ≫ adj_b.counit.app (R.obj X) = z X :=
    (adj_b.homEquiv (S.obj (F_r.obj X)) (R.obj X)).symm_apply_apply (z X)
  have counitIso (X : s.CompatibleModules) : IsIso (adj_r.counit.app X) := by
    have hzIso : IsIso (z X) := by
      rw [← hz X]
      let : IsIso (h X) := hIso X
      let : IsIso adj_b.counit := counit_b
      have h₁ : IsIso (Eb.map (h X)) := Eb.map_isIso (h X)
      have h₂ : IsIso (adj_b.counit.app (R.obj X)) := inferInstance
      exact IsIso.comp_isIso' h₁ h₂
    have hc : R.map (adj_r.counit.app X) = α.hom.app (F_r.obj X) ≫ z X := by
      simp [z]
    have hR : IsIso (R.map (adj_r.counit.app X)) := by
      rw [hc]
      let : IsIso (z X) := hzIso
      have hα : IsIso (α.hom.app (F_r.obj X)) := inferInstance
      exact IsIso.comp_isIso' hα hzIso
    apply (CategoricalPullback.isIso_iff (ModuleCat.extendScalars s.DtoC)
      (ModuleCat.extendScalars s.C'toC) (adj_r.counit.app X)).2
    constructor
    · have hfst : IsIso ((R.map (adj_r.counit.app X)).fst) := inferInstance
      change IsIso ((ModuleCat.restrictScalars s.BtoD).map (adj_r.counit.app X).fst) at hfst
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars s.BtoD)
    · have hsnd : IsIso ((R.map (adj_r.counit.app X)).snd) := inferInstance
      change IsIso ((ModuleCat.restrictScalars s.A'toC').map (adj_r.counit.app X).snd) at hsnd
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars s.A'toC')
  have hunit (L : ModuleCat.{u} D') :
      S.map (adj_r.unit.app L) ≫ h (Er.obj L) =
        adj_b.unit.app (S.obj L) ≫ F_b.map (α.inv.app L) :=
    adjunction_mate_unit adj_r adj_b R S α L
  have hflat (X : s.CompatibleModules)
      (hX : Module.Flat B (R.obj X).fst ∧ Module.Flat A' (R.obj X).snd) :
      Module.Flat base.fibreProduct (S.obj (F_r.obj X)) := by
    let : IsIso (h X) := hIso X
    let : Module.Flat base.fibreProduct (F_b.obj (R.obj X)) := flat_b (R.obj X) hX
    exact Module.Flat.of_linearEquiv (asIso (h X)).toLinearEquiv
  have hu (L : ModuleCat.{u} D') (hL : Module.Flat base.fibreProduct (S.obj L)) :
      IsIso (adj_r.unit.app L) := by
    let : IsIso (h (Er.obj L)) := hIso (Er.obj L)
    let : IsIso (adj_b.unit.app (S.obj L)) := unit_b (S.obj L) hL
    have : IsIso (S.map (adj_r.unit.app L) ≫ h (Er.obj L)) := by
      rw [hunit L]
      infer_instance
    have : IsIso (S.map (adj_r.unit.app L)) :=
      IsIso.of_isIso_comp_right _ (h (Er.obj L))
    exact isIso_of_reflects_iso _ S
  have hflatE (L : ModuleCat.{u} D') (hL : Module.Flat base.fibreProduct (S.obj L)) :
      Module.Flat B (R.obj (Er.obj L)).fst ∧
        Module.Flat A' (R.obj (Er.obj L)).snd := by
    let : Module.Flat base.fibreProduct (S.obj L) := hL
    constructor
    · let : Algebra base.fibreProduct B := base.pullbackCone.fst.hom.toAlgebra
      let : Module.Flat B (Eb.obj (S.obj L)).fst := by
        show Module.Flat B (B ⊗[base.fibreProduct] (S.obj L))
        infer_instance
      let e : (R.obj (Er.obj L)).fst ≃ₗ[B] (Eb.obj (S.obj L)).fst :=
        ((CategoricalPullback.π₁ _ _).mapIso (α.app L)).toLinearEquiv
      exact Module.Flat.of_linearEquiv e
    · let : Algebra base.fibreProduct A' := base.pullbackCone.snd.hom.toAlgebra
      let : Module.Flat A' (Eb.obj (S.obj L)).snd := by
        show Module.Flat A' (A' ⊗[base.fibreProduct] (S.obj L))
        infer_instance
      let e : (R.obj (Er.obj L)).snd ≃ₗ[A'] (Eb.obj (S.obj L)).snd :=
        ((CategoricalPullback.π₂ _ _).mapIso (α.app L)).toLinearEquiv
      exact Module.Flat.of_linearEquiv e
  refine ⟨F_r, e_r, adj_r, form_r, nat_r, ?_, hflat, hu, ?_⟩
  · have : ∀ X, IsIso (adj_r.counit.app X) := fun X => counitIso X
    exact NatIso.isIso_of_isIso_app _
  exact restrictedEquivalence Er F_r adj_r _ _ hflatE hflat hu
    (fun X _ => counitIso X)

end MilnorPatching
end

end

section

section
open CategoryTheory
open CategoryTheory.Limits
open Submodule LinearEquiv
open scoped ChangeOfRings

universe u

namespace MilnorPatching

/-- In the restriction of scalars along `f`, `d • 1` is `f d`. -/
private theorem restrictScalars_smul_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (d : R) :
    d • (show (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) from (1 : S)) =
      (show (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) from f d) :=
  (ModuleCat.restrictScalars.smul_def' (f := f) (M := ModuleCat.of S S) d (1 : S)).trans
    (mul_one (f d))

set_option maxHeartbeats 1000000 in
-- the proof elaborates a long chain of `let` algebra and finiteness instances
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Project, Tag 08IH.** In a relative module fibre-product situation, the
compatible-pairs module associated to a finite `D`-module and a finite `C'`-module is
finite over `D'`. -/
@[stacks 08IH]
public theorem finite_relativeRightAdjoint_obj_of_finite_components
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : RelativeModuleFibreProductSituation (D' := D') base)
    (F : RelativeModuleFibreProductSituation.CompatibleModules s ⥤
      ModuleCat.{u} D')
    (adj : (letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)) ⊣
           F)
    (hCounit : IsIso adj.counit)
    (X : RelativeModuleFibreProductSituation.CompatibleModules s) :
    Module.Finite s.D X.fst → Module.Finite s.C' X.snd →
      Module.Finite D' (F.obj X) := by
  intro hN hM
  let : IsIso adj.counit := hCounit
  obtain ⟨F₀, e, adj₀, he, hCounit₀⟩ :=
    relativeCompatiblePairsRightAdjoint_counit_isIso s
  let : IsIso adj₀.counit := hCounit₀
  let : Module.Finite s.D X.fst := hN
  let : Module.Finite s.C' X.snd := hM
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  let : Algebra base.fibreProduct B :=
    (RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct A' :=
    (RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  let : Algebra base.fibreProduct A :=
    (RelativeModuleFibreProductSituation.toA (base := base)).toAlgebra
  have he_fst (z : F₀.obj X) :
      (e X z).1.1 = (adj₀.counit.app X).fst ((1 : s.D) ⊗ₜ[D',s.toD] z) := by
    rw [← adj₀.homEquiv_symm_id X]
    exact (he (F₀.obj X) X (𝟙 _) z).1
  have he_snd (z : F₀.obj X) :
      (e X z).1.2 = (adj₀.counit.app X).snd ((1 : s.C') ⊗ₜ[D',s.toC'] z) := by
    rw [← adj₀.homEquiv_symm_id X]
    exact (he (F₀.obj X) X (𝟙 _) z).2
  let cB0 : (ModuleCat.extendScalars s.toD).obj (F₀.obj X) ≃ₗ[s.D] X.fst :=
    (asIso (adj₀.counit.app X).fst).toLinearEquiv
  let cB := cB0
  let cC0 : (ModuleCat.extendScalars s.toC').obj (F₀.obj X) ≃ₗ[s.C'] X.snd :=
    (asIso (adj₀.counit.app X).snd).toLinearEquiv
  let cC := cC0
  have cB_apply (w) : cB w = (adj₀.counit.app X).fst w := rfl
  have cC_apply (w) : cC w = (adj₀.counit.app X).snd w := rfl
  have coord_fst (w : F₀.obj X) :
      cB ((1 : s.D) ⊗ₜ[D'] w) = (e X w).1.1 :=
    (cB_apply _).trans (he_fst w).symm
  have coord_snd (w : F₀.obj X) :
      cC ((1 : s.C') ⊗ₜ[D'] w) = (e X w).1.2 :=
    (cC_apply _).trans (he_snd w).symm
  have hXfst : Module.Finite s.D ((𝟭 _).obj X).fst := hN
  have hXsnd : Module.Finite s.C' ((𝟭 _).obj X).snd := hM
  let := hXfst
  let := hXsnd
  let : Module.Finite s.D ((ModuleCat.extendScalars s.toD).obj (F₀.obj X)) :=
    Module.Finite.equiv cB.symm
  let : Module.Finite s.C' ((ModuleCat.extendScalars s.toC').obj (F₀.obj X)) :=
    Module.Finite.equiv cC.symm
  obtain ⟨r, y, hy⟩ := Module.Finite.exists_fin
    (R := s.D) (M := (ModuleCat.extendScalars s.toD).obj (F₀.obj X))
  obtain ⟨q, x, hx⟩ := Module.Finite.exists_fin
    (R := s.C') (M := (ModuleCat.extendScalars s.toC').obj (F₀.obj X))
  choose kr br pr hpr using fun i ↦ TensorProduct.exists_sum_tmul_eq (y i)
  choose kq bq pq hpq using fun i ↦ TensorProduct.exists_sum_tmul_eq (x i)
  dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.obj'] at y hy x hx br hpr bq hpq
  let P : Submodule D' (F₀.obj X) :=
    Submodule.span D' (Set.range (fun ij : Σ i, Fin (kr i) ↦ pr ij.1 ij.2))
  let Q : Submodule D' (F₀.obj X) :=
    Submodule.span D' (Set.range (fun ij : Σ i, Fin (kq i) ↦ pq ij.1 ij.2))
  have hPfin : Module.Finite D' P :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  have hQfin : Module.Finite D' Q :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  have hscalarD (d : D') : (d • (1 : s.D) : s.D) = s.toD d := by
    simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
      RelativeModuleFibreProductSituation.toD]
  have hscalarC (d : D') : (d • (1 : s.C') : s.C') = s.toC' d := by
    simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
      RelativeModuleFibreProductSituation.toC']
  -- The lifting argument in 08IG: the first projection is surjective, and
  -- the kernel on the second side is the image of the extended ideal (08KN).
  have htoB : Function.Surjective s.toD := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul d b =>
        obtain ⟨a', ha'⟩ := base.surjective_surjection (toBase b)
        let j : base.fibreProduct := ⟨(b, a'), ha'.symm⟩
        refine ⟨d * s.toD' j, ?_⟩
        show (d * algebraMap base.fibreProduct D' j) ⊗ₜ[base.fibreProduct] (1 : B) = _
        rw [mul_comm d, ← Algebra.smul_def, TensorProduct.smul_tmul]
        show d ⊗ₜ[base.fibreProduct] (b * 1) = _
        rw [mul_one]
    | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
  have hC'surj : Function.Surjective s.C'toC := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul d a =>
        obtain ⟨a', rfl⟩ := base.surjective_surjection a
        refine ⟨d ⊗ₜ[base.fibreProduct] a', ?_⟩
        simp [RelativeModuleFibreProductSituation.C'toC]
    | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
  have hker : RingHom.ker s.C'toC = I.map s.A'toC' := by
    let g : A' →ₐ[base.fibreProduct] A :=
      { surjection with commutes' := fun x => x.property.symm }
    show RingHom.ker (Algebra.TensorProduct.map (AlgHom.id base.fibreProduct D') g) = _
    rw [Algebra.TensorProduct.lTensor_ker g base.surjective_surjection]
    show (RingHom.ker surjection).map s.A'toC' = _
    rw [base.ker_surjection]
  have liftZero (t : s.C') (ht : s.C'toC t = 0) :
      ∃ d : D', s.toD d = 0 ∧ s.toC' d = t := by
    have htI : t ∈ I.map s.A'toC' := by rw [← hker]; exact ht
    rw [← SetLike.mem_coe, ← image_extendedKernel_eq_extendedIdeal s] at htI
    obtain ⟨d, hd, hdt⟩ := htI
    refine ⟨d, ?_, hdt⟩
    have hle : (RingHom.ker
        (RelativeModuleFibreProductSituation.toB (base := base))).map s.toD' ≤
        RingHom.ker s.toD := by
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      show s.toD (s.toD' j) = 0
      show (algebraMap base.fibreProduct D' j) ⊗ₜ[base.fibreProduct] (1 : B) = 0
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
      show (1 : D') ⊗ₜ[base.fibreProduct]
        (RelativeModuleFibreProductSituation.toB (base := base)) j = 0
      rw [show (RelativeModuleFibreProductSituation.toB (base := base)) j = 0
        from hj, TensorProduct.tmul_zero]
    exact hle hd
  have lift_fst (n : X.fst) : ∃ p ∈ P, (e X p).1.1 = n := by
    have hn : cB.symm n ∈ Submodule.span s.D (Set.range y) := by rw [hy]; trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun s.D).mp hn
    choose d hd using fun ij : Σ i, Fin (kr i) ↦ htoB (a ij.1 * br ij.1 ij.2)
    refine ⟨∑ i, ∑ j, d ⟨i, j⟩ • pr i j, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
        P.smul_mem (d ⟨i, j⟩) (Submodule.subset_span
          ⟨(⟨i, j⟩ : Σ i, Fin (kr i)), rfl⟩)
    · rw [he_fst]
      show cB ((1 : s.D) ⊗ₜ[D'] (∑ i, ∑ j, d ⟨i, j⟩ • pr i j)) = n
      rw [← cB.apply_symm_apply n, ← ha]
      apply congrArg cB
      simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul, hpr, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [TensorProduct.smul_tmul', restrictScalars_smul_one s.toD, hd]
      congr 1
  have lift_smul_snd (t : s.C') (ht : s.C'toC t = 0) (m : X.snd) :
      ∃ z ∈ Q, (e X z).1.1 = 0 ∧ (e X z).1.2 = t • m := by
    have hm : cC.symm m ∈ Submodule.span s.C' (Set.range x) := by rw [hx]; trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun s.C').mp hm
    choose d hd using fun ij : Σ i, Fin (kq i) ↦
      liftZero (t * a ij.1 * bq ij.1 ij.2) (by simp [ht])
    refine ⟨∑ i, ∑ j, d ⟨i, j⟩ • pq i j, ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
        Q.smul_mem (d ⟨i, j⟩) (Submodule.subset_span
          ⟨(⟨i, j⟩ : Σ i, Fin (kq i)), rfl⟩)
    · rw [he_fst]
      show cB ((1 : s.D) ⊗ₜ[D'] (∑ i, ∑ j, d ⟨i, j⟩ • pq i j)) = 0
      rw [cB.map_eq_zero_iff]
      simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [TensorProduct.smul_tmul', restrictScalars_smul_one s.toD, (hd ⟨i, j⟩).1]
      simp
    · rw [he_snd]
      show cC ((1 : s.C') ⊗ₜ[D'] (∑ i, ∑ j, d ⟨i, j⟩ • pq i j)) = t • m
      rw [← cC.apply_symm_apply m, ← cC.map_smul, ← ha]
      apply congrArg cC
      simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul, hpq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [TensorProduct.smul_tmul', restrictScalars_smul_one s.toC', (hd ⟨i, j⟩).2]
      congr 1
      simp [smul_eq_mul, mul_assoc]
  have hPQ : P ⊔ Q = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨p, hpP, hp⟩ := lift_fst (e X z).1.1
    let d := z - p
    have hd_fst : (e X d).1.1 = 0 := by
      rw [he_fst]
      show cB ((1 : s.D) ⊗ₜ[D'] (z - p)) = 0
      rw [TensorProduct.tmul_sub, map_sub]
      have hp' : cB ((1 : s.D) ⊗ₜ[D'] p) =
          cB ((1 : s.D) ⊗ₜ[D'] z) := by
        rw [coord_fst, coord_fst]
        exact hp
      rw [hp', sub_self]
    let M' := X.snd
    let θ : M' := (e X d).1.2
    have hθ : θ ∈ RingHom.ker s.C'toC • (⊤ : Submodule s.C' M') := by
      let : Algebra s.C' s.C := s.C'toC.toAlgebra
      rw [← ker_tensorProductMk_of_surjective s.C'toC hC'surj]
      show (1 : s.C) ⊗ₜ[s.C',s.C'toC] θ = 0
      have hc := (e X d).2
      rw [hd_fst, TensorProduct.tmul_zero, map_zero] at hc
      exact hc.symm
    have hθ' : θ ∈ RingHom.ker s.C'toC •
        Submodule.span s.C' (Set.range (id : M' → M')) := by
      simpa using hθ
    obtain ⟨a, haI, ha⟩ :=
      (Submodule.mem_ideal_smul_span_iff_exists_sum
        (RingHom.ker s.C'toC) (id : M' → M') θ).mp hθ'
    choose v hvQ hvfst hvsnd using fun m ↦
      lift_smul_snd (a m) (RingHom.mem_ker.mp (haI m)) m
    let vSum : F₀.obj X := ∑ m ∈ a.support, v m
    have hvSumQ : vSum ∈ Q := Submodule.sum_mem _ fun m _ ↦ hvQ m
    have hvSum_fst : (e X vSum).1.1 = 0 := by
      rw [he_fst]
      show cB ((1 : s.D) ⊗ₜ[D'] (∑ m ∈ a.support, v m)) = 0
      rw [cB.map_eq_zero_iff]
      simp_rw [TensorProduct.tmul_sum]
      apply Finset.sum_eq_zero
      intro m _
      rw [← cB.map_eq_zero_iff, coord_fst]
      exact hvfst m
    have hvSum_snd : (e X vSum).1.2 = θ := by
      rw [he_snd]
      show cC ((1 : s.C') ⊗ₜ[D'] (∑ m ∈ a.support, v m)) = θ
      simp_rw [TensorProduct.tmul_sum, map_sum, coord_snd, hvsnd]
      show (∑ m ∈ a.support, a m • (m : M')) = θ
      simpa [Finsupp.sum, id_eq] using ha
    have hd_eq : d = vSum := by
      apply (e X).injective
      apply Subtype.ext
      apply Prod.ext
      · rw [hd_fst, hvSum_fst]
      · rw [hvSum_snd]
    show z ∈ P ⊔ Q
    have : z = p + vSum := by
      dsimp [d] at hd_eq
      calc
        z = vSum + p := (sub_eq_iff_eq_add).mp hd_eq
        _ = p + vSum := add_comm _ _
    rw [this]
    exact (P ⊔ Q).add_mem (Submodule.mem_sup_left hpP) (Submodule.mem_sup_right hvSumQ)
  have hF₀ : Module.Finite D' (F₀.obj X) := by
    apply Module.Finite.of_fg_top
    rw [← hPQ]
    exact (Module.Finite.iff_fg.mp hPfin).sup (Module.Finite.iff_fg.mp hQfin)
  let : Module.Finite D' (F₀.obj X) := hF₀
  exact Module.Finite.equiv
    ((adj.rightAdjointUniq adj₀).app X).toLinearEquiv.symm

end MilnorPatching
end

end

section

section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe u v

namespace MilnorPatching
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendScalarsAlgebraMapEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M := by
  let e : ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[R] S :=
    { Equiv.refl S with
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (Algebra.smul_def r (show S from x)).symm }
  let eT := TensorProduct.congr e (LinearEquiv.refl R M)
  refine { eT.toAddEquiv with map_smul' := ?_ }
  intro s x
  change eT (s • x) = s • eT x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul t m =>
      change eT (s • t ⊗ₜ[R] m) = s • eT (t ⊗ₜ[R] m)
      simp only [smul_tmul', eT, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
      rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictScalarsAlgebraMapEquiv
    (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≃ₗ[R] M :=
  { Equiv.refl M with
    map_add' := fun _ _ => rfl
    map_smul' := fun r m => IsScalarTower.algebraMap_smul S r (show M from m) }

private theorem finitePresentation_restrictScalars_of_surjective
    (R S M : Type*) [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : Function.Surjective f)
    (hfp : f.FinitePresentation)
    (hM : Module.FinitePresentation S M) :
    @Module.FinitePresentation R M _ _ (Module.compHom M f) := by
  let : Algebra R S := f.toAlgebra
  have : Module.Finite R S :=
    Module.Finite.of_surjective (Algebra.linearMap R S) hf
  have : Algebra.FinitePresentation R S := hfp
  have : Module.FinitePresentation R S :=
    Module.FinitePresentation.of_finite_of_finitePresentation R S
  let : Module R M := Module.compHom M f
  let : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  have : Module.FinitePresentation S M := hM
  exact Module.FinitePresentation.trans R M S

/-- A semilinear equivalence over a ring isomorphism is linear after restricting scalars of the
source along the inverse isomorphism. -/
private def compHomLinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (f : LinearEquiv (σ' := (↑e.symm : S →+* R)) (↑e : R →+* S) M N) :
    letI : Module S M := Module.compHom M (↑e.symm : S →+* R)
    M ≃ₗ[S] N :=
  letI : Module S M := Module.compHom M (↑e.symm : S →+* R)
  { f.toAddEquiv with
    map_smul' := fun s m => by
      show f (e.symm s • m) = s • f m
      rw [f.map_smulₛₗ]
      show e (e.symm s) • f m = s • f m
      rw [e.apply_symm_apply] }

private theorem flat_of_semilinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (f : LinearEquiv (σ' := (↑e.symm : S →+* R)) (↑e : R →+* S) M N)
    [Module.Flat R M] : Module.Flat S N := by
  let : Algebra S R := (↑e.symm : S →+* R).toAlgebra
  let : Module S M := Module.compHom M (↑e.symm : S →+* R)
  have : IsScalarTower S R M := IsScalarTower.restrictScalars S R M
  have : Module.Flat S R :=
    Module.Flat.of_linearEquiv (Module.compHom.toLinearEquiv e.symm).symm
  have : Module.Flat S M := Module.Flat.trans S R M
  exact Module.Flat.of_linearEquiv (compHomLinearEquiv e f).symm

private def algebraSemilinearEquiv
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (h : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r)) :
    LinearEquiv (σ' := (↑eR.symm : R' →+* R)) (↑eR : R →+* R') S S' :=
  { eS.toAddEquiv with map_smul' := fun r s => by simp [Algebra.smul_def, h] }

private noncomputable def tensorRingEquiv
    {R S T R' S' T' : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing R'] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R' S'] [Algebra R' T']
    (eR : R ≃+* R') (eS : S ≃+* S') (eT : T ≃+* T')
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R' T' (eR r)) :
    S ⊗[R] T ≃+* S' ⊗[R'] T' := by
  let e := TensorProduct.congr (algebraSemilinearEquiv eR eS hS)
    (algebraSemilinearEquiv eR eT hT)
  refine { e.toAddEquiv with map_mul' := ?_ }
  intro x y
  change e (x * y) = e x * e y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [add_mul, hx, hx']
  | tmul s t =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp [mul_add, hy, hy']
    | tmul s' t' =>
      simp [e, Algebra.TensorProduct.tmul_mul_tmul, algebraSemilinearEquiv]

private theorem tensorRingEquiv_tmul
    {R S T R' S' T' : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing R'] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R' S'] [Algebra R' T']
    (eR : R ≃+* R') (eS : S ≃+* S') (eT : T ≃+* T')
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R' T' (eR r)) (s : S) (t : T) :
    tensorRingEquiv eR eS eT hS hT (s ⊗ₜ[R] t) = eS s ⊗ₜ[R'] eT t := by
  simp [tensorRingEquiv, algebraSemilinearEquiv]

private noncomputable def tensorExtensionEquiv
    {R S T M R' S' T' M' : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing R'] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R' S'] [Algebra R' T']
    [AddCommGroup M] [AddCommGroup M'] [Module S M] [Module S' M']
    (eR : R ≃+* R') (eS : S ≃+* S') (eT : T ≃+* T')
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R' T' (eR r))
    (eM : LinearEquiv (σ' := (↑eS.symm : S' →+* S)) (↑eS : S →+* S') M M') :
    LinearEquiv (σ' := (↑(tensorRingEquiv eR eS eT hS hT).symm : S' ⊗[R'] T' →+* S ⊗[R] T))
      (↑(tensorRingEquiv eR eS eT hS hT) : S ⊗[R] T →+* S' ⊗[R'] T')
      ((S ⊗[R] T) ⊗[S] M) ((S' ⊗[R'] T') ⊗[S'] M') := by
  let eST := tensorRingEquiv eR eS eT hS hT
  let eLeft : LinearEquiv (σ' := (↑eS.symm : S' →+* S)) (↑eS : S →+* S') (S ⊗[R] T) (S' ⊗[R'] T') :=
    { eST.toAddEquiv with
      map_smul' := by
        intro s x
        change eST (s • x) = eS s • eST x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp [smul_add, hx, hy]
        | tmul a b =>
          simp only [smul_tmul', smul_eq_mul, eST, tensorRingEquiv_tmul, map_mul] }
  let e := TensorProduct.congr eLeft eM
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro r x
  change e (r • x) = eST r • e x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul q m =>
    simp only [smul_tmul', smul_eq_mul, e, TensorProduct.congr_tmul]
    change eST (r * q) ⊗ₜ[S'] eM m = (eST r * eST q) ⊗ₜ[S'] eM m
    rw [map_mul]

private theorem finitePresentation_of_semilinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (f : LinearEquiv (σ' := (↑e.symm : S →+* R)) (↑e : R →+* S) M N)
    [Module.FinitePresentation R M] : Module.FinitePresentation S N := by
  have h := finitePresentation_restrictScalars_of_surjective S R M
    (e.symm : S →+* R) e.symm.surjective
    (RingHom.FinitePresentation.of_bijective e.symm.bijective) inferInstance
  let : Module S M := Module.compHom M (e.symm : S →+* R)
  have : Module.FinitePresentation S M := h
  exact .of_equiv (compHomLinearEquiv e f)

/-- Finite presentation of the scalar extension, in either of its two formulations. -/
private theorem finitePresentation_tensor_of_extendScalars
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (L : ModuleCat R)
    (h : Module.FinitePresentation S ((ModuleCat.extendScalars (algebraMap R S)).obj L)) :
    Module.FinitePresentation S (S ⊗[R] L) :=
  .of_equiv (extendScalarsAlgebraMapEquiv L)

private theorem flat_ker_of_surjective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Flat R (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ g hg
  have hP := LinearMap.lTensor_injective_of_exact_of_flat f hf (LinearMap.ker f).subtype
    (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map f) P
  have hM := Module.Flat.rTensor_preserves_injective_linearMap (M := M) g hg
  apply Function.Injective.of_comp (f := (LinearMap.ker f).subtype.lTensor Q)
  show Function.Injective (((LinearMap.ker f).subtype.lTensor Q).comp
    (g.rTensor (LinearMap.ker f)))
  rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
  exact hM.comp hP

private theorem finitePresentation_of_restrictScalars_of_surjective
    (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hf : Function.Surjective (algebraMap R S))
    [Module.FinitePresentation R M] : Module.FinitePresentation S M := by
  have : TensorProduct.CompatibleSMul R S S M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S M hf
  exact .of_equiv (TensorProduct.lidOfCompatibleSMul R S M)

private theorem finitePresentation_tensorProduct_map
    (R P S T : Type*) [CommRing R] [CommRing P] [CommRing S] [CommRing T]
    [Algebra R P] [Algebra R S] [Algebra R T]
    (f : P →ₐ[R] S) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG) :
    (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_surjective
  · exact Algebra.TensorProduct.map_surjective f (AlgHom.id R T) hf Function.surjective_id
  · show (RingHom.ker (Algebra.TensorProduct.map f (AlgHom.id R T))).FG
    rw [Algebra.TensorProduct.rTensor_ker f hf]
    exact hker.map _

section
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
variable (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
/-- Base change of `M` from `S` to `S ⊗[R] T`, read as the base change of `M` from `R` to `T`
after restricting scalars. -/
public noncomputable def tensorBaseChangeEquiv :
    ((S ⊗[R] T) ⊗[S] M) ≃ₗ[R] T ⊗[R] M :=
  (TensorProduct.comm S (S ⊗[R] T) M).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R S S M T).restrictScalars R ≪≫ₗ TensorProduct.comm R M T
/-- The base-change comparison on a tensor of a scalar, a ring element and a module element. -/
public theorem tensorBaseChangeEquiv_tmul (s : S) (t : T) (m : M) :
    tensorBaseChangeEquiv R S T M ((s ⊗ₜ[R] t) ⊗ₜ[S] m) = t ⊗ₜ[R] (s • m) := by
  simp [tensorBaseChangeEquiv]
/-- The base-change comparison is natural in the module. -/
public theorem tensorBaseChangeEquiv_natural (f : M →ₗ[S] N)
    (x : (S ⊗[R] T) ⊗[S] M) :
    tensorBaseChangeEquiv R S T N (f.baseChange (S ⊗[R] T) x) =
      (f.restrictScalars R).lTensor T (tensorBaseChangeEquiv R S T M x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul st m =>
    induction st with
    | zero => simp
    | add x y hx hy => simpa [add_tmul] using congrArg₂ (· + ·) hx hy
    | tmul s t => simp [tensorBaseChangeEquiv_tmul]
/-- Base change along `R → T` of an injection of `S`-modules with flat cokernel stays
injective. -/
public theorem baseChange_injective_of_flat_cokernel [Module.Flat R N]
    (f : M →ₗ[S] N) (hf : Function.Surjective f) :
    Function.Injective ((LinearMap.ker f).subtype.baseChange (S ⊗[R] T)) := by
  have H := LinearMap.lTensor_injective_of_exact_of_flat (f.restrictScalars R) hf
    ((LinearMap.ker f).subtype.restrictScalars R)
    (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map f) T
  intro x y h
  apply (tensorBaseChangeEquiv R S T (LinearMap.ker f)).injective
  apply H
  simpa only [← tensorBaseChangeEquiv_natural] using
    congrArg (tensorBaseChangeEquiv R S T M) h

/-- Base change along `R → T` of the kernel of a map of finite `S`-modules with flat source
is finite. -/
public theorem finite_baseChange_ker_of_flat [Module.Flat R N] [Module.Finite S M]
    [Module.FinitePresentation (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] N)]
    (f : M →ₗ[S] N) (hf : Function.Surjective f) :
    Module.Finite (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] LinearMap.ker f) := by
  let g := f.baseChange (S ⊗[R] T)
  have : Module.Finite (S ⊗[R] T) (LinearMap.ker g) :=
    Module.Finite.of_fg
      (Module.FinitePresentation.fg_ker g (LinearMap.lTensor_surjective _ hf))
  let e : ((S ⊗[R] T) ⊗[S] LinearMap.ker f) ≃ₗ[S ⊗[R] T] LinearMap.ker g :=
    LinearEquiv.ofBijective (f.tensorKer (S ⊗[R] T) (S ⊗[R] T)) (by
      constructor
      · intro x y h
        apply baseChange_injective_of_flat_cokernel R S T M N f hf
        simpa only [LinearMap.tensorKer_coe, LinearMap.baseChange_eq_ltensor] using
          congrArg Subtype.val h
      · intro x
        obtain ⟨y, hy⟩ := (lTensor_exact (S ⊗[R] T)
          (LinearMap.exact_subtype_ker_map f) hf x.val).mp x.property
        exact ⟨y, Subtype.ext (by simpa only [LinearMap.tensorKer_coe] using hy)⟩)
  exact Module.Finite.equiv e.symm
end
section
variable (R P S T M : Type*) [CommRing R] [CommRing P] [CommRing S] [CommRing T]
    [Algebra R P] [Algebra R S] [Algebra R T] [Algebra P S] [IsScalarTower R P S]
    [AddCommGroup M] [Module R M] [Module P M] [Module S M]
    [IsScalarTower R P M] [IsScalarTower R S M] [IsScalarTower P S M]

private noncomputable def tensorRestrictScalarsEquiv :
    ((P ⊗[R] T) ⊗[P] M) ≃ₗ[R] ((S ⊗[R] T) ⊗[S] M) :=
  tensorBaseChangeEquiv R P T M ≪≫ₗ (tensorBaseChangeEquiv R S T M).symm

private theorem tensorRestrictScalarsEquiv_tmul (p : P) (t : T) (m : M) :
    tensorRestrictScalarsEquiv R P S T M ((p ⊗ₜ[R] t) ⊗ₜ[P] m) =
      (1 ⊗ₜ[R] t) ⊗ₜ[S] (p • m) := by
  simp [tensorRestrictScalarsEquiv, tensorBaseChangeEquiv]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorRestrictScalarsLinearEquiv :
    ((P ⊗[R] T) ⊗[P] M) ≃ₗ[P ⊗[R] T]
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R P S) (AlgHom.id R T)).toRingHom).obj
          (ModuleCat.of (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] M)) := by
  let e := tensorRestrictScalarsEquiv R P S T M
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro r x
  change e (r • x) =
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R P S) (AlgHom.id R T) r) • e x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul q m =>
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add q q' hq hq' => simpa [add_tmul, smul_add] using congrArg₂ (· + ·) hq hq'
    | tmul q w =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add r r' hr hr' => simpa [add_smul] using congrArg₂ (· + ·) hr hr'
      | tmul p t =>
        simp only [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
          e, tensorRestrictScalarsEquiv_tmul, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, IsScalarTower.toAlgHom_apply, mul_one]
        rw [← TensorProduct.smul_tmul, smul_tmul']
        simp only [Algebra.smul_def, map_mul, mul_one]
        rw [← IsScalarTower.algebraMap_smul S q m, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_comm]

private theorem finitePresentation_tensor_restrictScalars
    (hf : Function.Surjective (algebraMap P S))
    (hker : (RingHom.ker (algebraMap P S)).FG)
    (hM : Module.FinitePresentation (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] M)) :
    Module.FinitePresentation (P ⊗[R] T) ((P ⊗[R] T) ⊗[P] M) := by
  let f := IsScalarTower.toAlgHom R P S
  let g := Algebra.TensorProduct.map f (AlgHom.id R T)
  have hg : Function.Surjective g :=
    Algebra.TensorProduct.map_surjective f (AlgHom.id R T) hf Function.surjective_id
  have hgfp : g.toRingHom.FinitePresentation :=
    finitePresentation_tensorProduct_map R P S T f hf hker
  have : Module.FinitePresentation (P ⊗[R] T)
      ((ModuleCat.restrictScalars g.toRingHom).obj
        (ModuleCat.of (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] M))) :=
    finitePresentation_restrictScalars_of_surjective _ _ _ g.toRingHom hg hgfp hM
  exact .of_equiv (tensorRestrictScalarsLinearEquiv R P S T M).symm
end

variable {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : RelativeModuleFibreProductSituation (D' := D') base)

private theorem flat_rightAdjoint_obj
    (F : s.CompatibleModules ⥤ ModuleCat.{u} D')
    (adj : (letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)) ⊣
           F) (X : s.CompatibleModules)
    (hB : Module.Flat B ((ModuleCat.restrictScalars s.BtoD).obj X.fst))
    (hA : Module.Flat A' ((ModuleCat.restrictScalars s.A'toC').obj X.snd)) :
    Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj (F.obj X)) := by
  obtain ⟨G, e, adjG, he, -, -, hflat, hunit, hrest⟩ :=
    relativelyFlatModulesEquivalenceOverFibreProduct s
  have := hflat X ⟨hB, hA⟩
  exact Module.Flat.of_linearEquiv
    ((ModuleCat.restrictScalars s.toD').mapIso ((adj.rightAdjointUniq adjG).app X)).toLinearEquiv

private theorem finite_of_flat_of_finite_components
    (L : ModuleCat.{u} D')
    (hL : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L))
    (hB : Module.Finite s.D ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
           A)).obj L).fst)
    (hA : Module.Finite s.C' ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
           A)).obj L).snd) :
    Module.Finite D' L := by
  let E := (let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    let : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    let : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    let : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
    extensionOfScalarsToTensorProductPullback (D' := D')
    ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
    ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A))
  obtain ⟨G, e, adjG, he, -, -, hflat, hunit, hrest⟩ :=
    relativelyFlatModulesEquivalenceOverFibreProduct s
  obtain ⟨F, eF, adjF, heF, hF⟩ :=
    relativeCompatiblePairsRightAdjoint_counit_isIso s
  have := hunit L hL
  have := finite_relativeRightAdjoint_obj_of_finite_components s F adjF hF
    (E.obj L) hB hA
  exact Module.Finite.equiv
    ((((adjG.rightAdjointUniq adjF).app (E.obj L)).toLinearEquiv.symm)
      ≪≫ₗ (asIso (adjG.unit.app L)).toLinearEquiv.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_of_flat_of_finitePresentation_components
    (hS : @Module.Flat base.fibreProduct D' _ _ (Module.compHom D' s.toD'))
    (L : ModuleCat.{u} D')
    (hL : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L))
    (hB : Module.FinitePresentation s.D ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
           A)).obj L).fst)
    (hA : Module.FinitePresentation s.C' ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
           A)).obj L).snd) :
    Module.FinitePresentation D' L := by
  let E := (let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    let : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    let : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    let : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
    extensionOfScalarsToTensorProductPullback (D' := D')
    ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
    ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A))
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  let : Algebra base.fibreProduct B :=
    (RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct A' :=
    (RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  let : Module base.fibreProduct L := Module.compHom L s.toD'
  let : IsScalarTower base.fibreProduct D' L :=
    IsScalarTower.restrictScalars base.fibreProduct D' L
  have : Module.Flat base.fibreProduct D' := hS
  have : Module.Flat base.fibreProduct L := hL
  have : Module.FinitePresentation s.D (E.obj L).fst := hB
  have : Module.FinitePresentation s.C' (E.obj L).snd := hA
  have : Module.Finite D' L := finite_of_flat_of_finite_components s L hL
    inferInstance inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' D' L
  have : Module.Flat base.fibreProduct (Fin n → D') :=
    Module.Flat.trans base.fibreProduct D' _
  have hK : Module.Flat base.fibreProduct (LinearMap.ker f) :=
    flat_ker_of_surjective (f.restrictScalars base.fibreProduct) hf
  have hB' := finitePresentation_tensor_of_extendScalars (S := s.D) L hB
  have hA' := finitePresentation_tensor_of_extendScalars (S := s.C') L hA
  have hKB := finite_baseChange_ker_of_flat base.fibreProduct D' B (Fin n → D') L f hf
  have hKA := finite_baseChange_ker_of_flat base.fibreProduct D' A' (Fin n → D') L f hf
  have : Module.Finite D' (LinearMap.ker f) :=
    finite_of_flat_of_finite_components s (ModuleCat.of D' (LinearMap.ker f)) hK
      (Module.Finite.equiv (extendScalarsAlgebraMapEquiv
        (R := D') (S := s.D) (ModuleCat.of D' (LinearMap.ker f))).symm)
      (Module.Finite.equiv (extendScalarsAlgebraMapEquiv
        (R := D') (S := s.C') (ModuleCat.of D' (LinearMap.ker f))).symm)
  exact Module.finitePresentation_of_free_of_surjective f hf (Module.Finite.iff_fg.mp this)

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_of_flat_of_finitePresentation_tensor
    (hS : @Module.Flat base.fibreProduct D' _ _ (Module.compHom D' s.toD'))
    (L : ModuleCat.{u} D')
    (hL : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L))
    (hB : letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
      let : Algebra base.fibreProduct B :=
        (RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
      Module.FinitePresentation s.D (s.D ⊗[D'] L))
    (hA : letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
      let : Algebra base.fibreProduct A' :=
        (RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
      Module.FinitePresentation s.C' (s.C' ⊗[D'] L)) :
    Module.FinitePresentation D' L := by
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  let : Algebra base.fibreProduct B :=
    (RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct A' :=
    (RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  have := hB
  have := hA
  apply finitePresentation_of_flat_of_finitePresentation_components s hS L hL
  · exact .of_equiv (extendScalarsAlgebraMapEquiv (R := D') (S := s.D) L).symm
  · exact .of_equiv (extendScalarsAlgebraMapEquiv (R := D') (S := s.C') L).symm

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_of_flat_of_finitePresentation_tensor_large
    {E : Type v} [CommRing E]
    (t : RelativeModuleFibreProductSituation (D' := E) base)
    (M : Type u) [AddCommGroup M] [Module E M]
    (hE : @Module.Flat base.fibreProduct E _ _ (Module.compHom E t.toD'))
    (hM : @Module.Flat base.fibreProduct M _ _ (Module.compHom M t.toD'))
    (hB : letI : Algebra base.fibreProduct E := t.toD'.toAlgebra
      let : Algebra base.fibreProduct B :=
        (RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
      Module.FinitePresentation t.D (t.D ⊗[E] M))
    (hA : letI : Algebra base.fibreProduct E := t.toD'.toAlgebra
      let : Algebra base.fibreProduct A' :=
        (RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
      Module.FinitePresentation t.C' (t.C' ⊗[E] M)) :
    Module.FinitePresentation E M := by
  let eA : ULift.{v} A ≃+* A := ULift.ringEquiv
  let eA' : ULift.{v} A' ≃+* A' := ULift.ringEquiv
  let eB : ULift.{v} B ≃+* B := ULift.ringEquiv
  let eE : ULift.{u} E ≃+* E := ULift.ringEquiv
  let f : ULift.{v} B →+* ULift.{v} A :=
    (eA.symm : A →+* ULift A).comp (toBase.comp eB.toRingHom)
  let g : ULift.{v} A' →+* ULift.{v} A :=
    (eA.symm : A →+* ULift A).comp (surjection.comp eA'.toRingHom)
  have base0 : RingFibreProduct.Situation f g (RingHom.ker g) :=
    ⟨eA.symm.surjective.comp (base.surjective_surjection.comp eA'.surjective), rfl⟩
  let eR : base0.fibreProduct ≃+* base.fibreProduct :=
    { toFun := fun x => ⟨(x.val.1.down, x.val.2.down), congrArg ULift.down x.property⟩
      invFun := fun x => ⟨(ULift.up x.val.1, ULift.up x.val.2), congrArg ULift.up x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let t0 : RelativeModuleFibreProductSituation (D' := ULift.{u} E) base0 :=
    ⟨(eE.symm : E →+* ULift E).comp (t.toD'.comp eR.toRingHom)⟩
  let : Algebra base.fibreProduct E := t.toD'.toAlgebra
  let : Algebra base.fibreProduct B :=
    (RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct A' :=
    (RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  let : Algebra base0.fibreProduct (ULift.{u} E) := t0.toD'.toAlgebra
  let : Algebra base0.fibreProduct (ULift.{v} B) :=
    (RelativeModuleFibreProductSituation.toB (base := base0)).toAlgebra
  let : Algebra base0.fibreProduct (ULift.{v} A') :=
    (RelativeModuleFibreProductSituation.toA' (base := base0)).toAlgebra
  let : Module (ULift.{u} E) (ULift.{v} M) :=
    Module.compHom (ULift.{v} M) eE.toRingHom
  let L0 := ModuleCat.of (ULift.{u} E) (ULift.{v} M)
  let em : LinearEquiv (σ' := (↑eE.symm : E →+* ULift.{u} E))
      (↑eE : ULift.{u} E →+* E) (ULift.{v} M) M :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : ∀ r, eE (algebraMap base0.fibreProduct (ULift.{u} E) r) =
      algebraMap base.fibreProduct E (eR r) := fun _ => rfl
  have hb : ∀ r, eB (algebraMap base0.fibreProduct (ULift.{v} B) r) =
      algebraMap base.fibreProduct B (eR r) := fun _ => rfl
  have ha : ∀ r, eA' (algebraMap base0.fibreProduct (ULift.{v} A') r) =
      algebraMap base.fibreProduct A' (eR r) := fun _ => rfl
  have : Module.Flat base.fibreProduct E := hE
  have hE0 : @Module.Flat base0.fibreProduct (ULift.{u} E) _ _
      (Module.compHom (ULift.{u} E) t0.toD') :=
    flat_of_semilinearEquiv eR.symm (algebraSemilinearEquiv eR eE he).symm
  let : Module base.fibreProduct M := Module.compHom M t.toD'
  have : Module.Flat base.fibreProduct M := hM
  let emR : LinearEquiv (σ' := (↑eR.symm : base.fibreProduct →+* base0.fibreProduct))
      (↑eR : base0.fibreProduct →+* base.fibreProduct)
      ((ModuleCat.restrictScalars t0.toD').obj L0) M :=
    { em.toAddEquiv with map_smul' := fun _ _ => rfl }
  have hM0 : Module.Flat base0.fibreProduct ((ModuleCat.restrictScalars t0.toD').obj L0) :=
    flat_of_semilinearEquiv eR.symm emR.symm
  have := hB
  have := hA
  have hB0 : Module.FinitePresentation t0.D (t0.D ⊗[ULift.{u} E] L0) :=
    finitePresentation_of_semilinearEquiv (tensorRingEquiv eR eE eB he hb).symm
      (tensorExtensionEquiv eR eE eB he hb em).symm
  have hA0 : Module.FinitePresentation t0.C' (t0.C' ⊗[ULift.{u} E] L0) :=
    finitePresentation_of_semilinearEquiv (tensorRingEquiv eR eE eA' he ha).symm
      (tensorExtensionEquiv eR eE eA' he ha em).symm
  have : Module.FinitePresentation (ULift.{u} E) L0 :=
    finitePresentation_of_flat_of_finitePresentation_tensor t0 hE0 L0 hM0 hB0 hA0
  exact finitePresentation_of_semilinearEquiv eE em

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_of_factorization
    {D'' : Type v} [CommRing D'']
    (L : ModuleCat.{u} D')
    (hL : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L))
    (hB : Module.FinitePresentation s.D ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
           A)).obj L).fst)
    (hA : Module.FinitePresentation s.C' ((letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct]
           A)).obj L).snd)
    (toD'' : base.fibreProduct →+* D'') (fromD'' : D'' →+* D')
    (hcomp : fromD''.comp toD'' = s.toD')
    (hflat : @Module.Flat base.fibreProduct D'' _ _ (Module.compHom D'' toD''))
    (hfp : fromD''.FinitePresentation) : Module.FinitePresentation D' L := by
  let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
  let : Algebra base.fibreProduct D'' := toD''.toAlgebra
  let : Algebra D'' D' := fromD''.toAlgebra
  have : IsScalarTower base.fibreProduct D'' D' :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : Algebra.FinitePresentation D'' D' := hfp
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := D'') (A := D')
  let P := MvPolynomial (Fin n) D''
  let t : RelativeModuleFibreProductSituation (D' := P) base :=
    ⟨MvPolynomial.C.comp toD''⟩
  let : Algebra base.fibreProduct P := t.toD'.toAlgebra
  let : Module base.fibreProduct P := Module.compHom P t.toD'
  let : Algebra P D' := f.toRingHom.toAlgebra
  have : IsScalarTower base.fibreProduct D'' P :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower base.fibreProduct P D' := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    show s.toD' r = f (MvPolynomial.C (toD'' r))
    rw [show MvPolynomial.C (toD'' r) = algebraMap D'' P (toD'' r) from rfl,
      f.commutes]
    exact (RingHom.congr_fun hcomp r).symm
  let : Module base.fibreProduct L := Module.compHom L s.toD'
  let : Module P L := Module.compHom L f.toRingHom
  have : IsScalarTower P D' L := IsScalarTower.restrictScalars P D' L
  have : IsScalarTower base.fibreProduct D' L :=
    IsScalarTower.restrictScalars base.fibreProduct D' L
  have : IsScalarTower base.fibreProduct P L :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      show (f (t.toD' r)) • m = s.toD' r • m
      exact congrArg (· • m)
        (IsScalarTower.algebraMap_apply base.fibreProduct P D' r).symm)
  let : Algebra base.fibreProduct B :=
    (RelativeModuleFibreProductSituation.toB (base := base)).toAlgebra
  let : Algebra base.fibreProduct A' :=
    (RelativeModuleFibreProductSituation.toA' (base := base)).toAlgebra
  have hpB := finitePresentation_tensor_restrictScalars base.fibreProduct P D' B L hf hker
    (finitePresentation_tensor_of_extendScalars (S := s.D) L hB)
  have hpA := finitePresentation_tensor_restrictScalars base.fibreProduct P D' A' L hf hker
    (finitePresentation_tensor_of_extendScalars (S := s.C') L hA)
  have : Module.Flat base.fibreProduct D'' := hflat
  have hP : Module.Flat base.fibreProduct P := Module.Flat.trans base.fibreProduct D'' P
  have : Module.Flat base.fibreProduct L := hL
  have hLPflat : Module.Flat base.fibreProduct
      ((ModuleCat.restrictScalars t.toD').obj (ModuleCat.of P L)) :=
    Module.Flat.of_linearEquiv (restrictScalarsAlgebraMapEquiv base.fibreProduct P L)
  have hLP : Module.FinitePresentation P L :=
    finitePresentation_of_flat_of_finitePresentation_tensor_large t L hP hLPflat hpB hpA
  exact finitePresentation_of_restrictScalars_of_surjective P D' L hf

end MilnorPatching
end
section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace MilnorPatching
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Project, Tag 08KP.** In a relative module fibre-product situation, the
compatible-pairs module is finitely presented over `D'` if its `D`-component and
`C'`-component are finitely presented and flat over `B` and `A'`, respectively, and
the map `B' → D'` factors as a flat map followed by a finitely presented map. -/
@[stacks 08KP]
public theorem finitePresentation_rightAdjoint_obj_of_factorization
    {A A' B D' : Type u} {D'' : Type v}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D'] [CommRing D'']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection I}
    (s : RelativeModuleFibreProductSituation (D' := D') base)
    (F : RelativeModuleFibreProductSituation.CompatibleModules s ⥤
      ModuleCat.{u} D')
    (adj : (letI : Algebra base.fibreProduct D' := s.toD'.toAlgebra
       letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
       letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
       letI : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
       extensionOfScalarsToTensorProductPullback (D' := D')
         ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
         ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A)) ⊣
           F)
    (_ : IsIso adj.counit)
    (X : RelativeModuleFibreProductSituation.CompatibleModules s)
    (_ : Module.FinitePresentation s.D X.fst)
    (_ : Module.Flat B ((ModuleCat.restrictScalars s.BtoD).obj X.fst))
    (_ : Module.FinitePresentation s.C' X.snd)
    (_ : Module.Flat A' ((ModuleCat.restrictScalars s.A'toC').obj X.snd))
    (toD'' : base.fibreProduct →+* D'') (fromD'' : D'' →+* D')
    (_ : fromD''.comp toD'' = s.toD')
    (_ : @Module.Flat base.fibreProduct D'' _ _ (Module.compHom D'' toD''))
    (_ : fromD''.FinitePresentation) :
    Module.FinitePresentation D' (F.obj X) := by
  rename_i hCounit hN hNflat hM hMflat hcomp hflat hfp
  let E := (let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    let : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    let : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    let : Algebra base.fibreProduct A := (toBase.comp (toBase.pullbackFst surjection)).toAlgebra
    extensionOfScalarsToTensorProductPullback (D' := D')
    ({ toBase with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
    ({ surjection with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A))
  have : IsIso adj.counit := hCounit
  have : Module.FinitePresentation s.D X.fst := hN
  have : Module.FinitePresentation s.C' X.snd := hM
  have : Module.FinitePresentation s.D ((𝟭 s.CompatibleModules).obj X).fst := hN
  have : Module.FinitePresentation s.C' ((𝟭 s.CompatibleModules).obj X).snd := hM
  have hB : Module.FinitePresentation s.D
      (E.obj (F.obj X)).fst :=
    .of_equiv (show X.fst ≃ₗ[s.D] (E.obj (F.obj X)).fst from
      (asIso (adj.counit.app X).fst).toLinearEquiv.symm)
  have hA : Module.FinitePresentation s.C'
      (E.obj (F.obj X)).snd :=
    .of_equiv (show X.snd ≃ₗ[s.C'] (E.obj (F.obj X)).snd from
      (asIso (adj.counit.app X).snd).toLinearEquiv.symm)
  exact finitePresentation_of_factorization s (F.obj X)
    (flat_rightAdjoint_obj s F adj X hNflat hMflat) hB hA
    toD'' fromD'' hcomp hflat hfp

end MilnorPatching
end

end

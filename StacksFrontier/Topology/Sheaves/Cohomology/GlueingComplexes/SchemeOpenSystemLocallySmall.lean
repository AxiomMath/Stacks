module

public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.SchemeFiniteCoverLocallySmall
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.SchemeOpenSystem

/-!
# Glueing locally given derived objects at the locally small model

`Stacks.Cohomology.GlueingComplexes.OpenSystem.exists_solution` glues a system of locally given
objects of the derived categories of the opens of a scheme at the standard model of the derived
categories. This file carries the statement to the locally small model of [Stacks, Tag 079Q], at
which the upper shriek functors live. The two models have the same objects, and derived pullbacks
and their composition isomorphisms correspond through
`StacksDraft.DerivedModel.derivedPullbackModelIso`.

## Main results

* `Stacks.Cohomology.GlueingComplexes.map_factorIso_inv_app`: the composition isomorphisms of
  the two models correspond.
* `Stacks.Cohomology.GlueingComplexes.exists_solution_locallySmall`: glueing of locally given
  objects with vanishing negative self-Ext along a finite cover, at the locally small model.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open StacksDraft.DerivedModel (derivedPullbackModelIso derivedPullbackCongr)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

namespace Stacks.Cohomology.GlueingComplexes

universe u

section RingedSpaces

variable {A B Z : RingedSpace.{u, u}}

private theorem inv_chase {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C} (gchom : X₁ ⟶ X₂)
    (gcinv : X₂ ⟶ X₁) (hg : gchom ≫ gcinv = 𝟙 _) (mk : X₂ ≅ Y₂) (clhom : Y₁ ⟶ Y₂)
    (clinv : Y₂ ⟶ Y₁) (hcl : clinv ≫ clhom = 𝟙 _) (P : Y₁ ⟶ X₁)
    (h : clhom ≫ mk.inv = P ≫ gchom) :
    gcinv = mk.hom ≫ clinv ≫ P := by
  calc gcinv = mk.hom ≫ (clinv ≫ clhom) ≫ mk.inv ≫ gcinv := by simp [hcl]
    _ = mk.hom ≫ clinv ≫ (clhom ≫ mk.inv) ≫ gcinv := by simp
    _ = mk.hom ≫ clinv ≫ P := by rw [h, Category.assoc, hg, Category.comp_id]

/-- **The composition isomorphisms of derived pullback at the two models correspond**: the
comparison `Lf^* Lg^* ≅ Lk^*` at the standard model for `f ≫ g = k`, read at the locally small
model through `derivedPullbackModelIso`, is the one of the locally small model. -/
theorem map_factorIso_inv_app (f : A ⟶ B) (g : B ⟶ Z) (k : A ⟶ Z) (e : f ≫ g = k)
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z)))) :
    (Stacks.Injectives.grothendieckModelEquiv _).functor.map
        ((Stacks.DerivedPullback.factorIso f g k e).inv.app K) =
      (derivedPullbackModelIso k).hom.app K ≫
        (derivedPullbackCompIsoCanonical f g ≪≫ derivedPullbackCongr e).inv.app
          ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K) ≫
        (derivedPullback f).map ((derivedPullbackModelIso g).inv.app K) ≫
        (derivedPullbackModelIso f).inv.app ((@derivedPullback B Z g
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          inferInstance).obj K) := by
  subst e
  refine inv_chase _ _ ?_ ((derivedPullbackModelIso (f ≫ g)).app K)
    ((derivedPullbackCompIsoCanonical f g).hom.app
      ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K)) _ ?_ _
    ((StacksDraft.DerivedModel.derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso
      f g K).trans (Category.assoc _ _ _).symm)
  · exact ((Stacks.Injectives.grothendieckModelEquiv _).functor.map_comp _ _).symm.trans
      ((congrArg (Stacks.Injectives.grothendieckModelEquiv _).functor.map
        ((@derivedPullbackCompIsoCanonical _ _ _ f g (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)).hom_inv_id_app K)).trans
        (CategoryTheory.Functor.map_id _ _))
  · change ((derivedPullbackCongr rfl).inv.app _ ≫
        (derivedPullbackCompIsoCanonical f g).inv.app _) ≫
      (derivedPullbackCompIsoCanonical f g).hom.app _ = 𝟙 _
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rfl

/-- Derived pullback at the standard model, read at the locally small model through
`derivedPullbackModelIso`. -/
theorem map_derivedPullback_map (f : A ⟶ Z)
    {K L : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z)))} (x : K ⟶ L) :
    (Stacks.Injectives.grothendieckModelEquiv _).functor.map
        ((@derivedPullback A Z f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          inferInstance).map x) =
      (derivedPullbackModelIso f).hom.app K ≫
        (derivedPullback f).map ((Stacks.Injectives.grothendieckModelEquiv _).functor.map x) ≫
        (derivedPullbackModelIso f).inv.app L := by
  have nat := (derivedPullbackModelIso f).hom.naturality x
  simp only [Functor.comp_map] at nat
  rw [← reassoc_of% nat, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

end RingedSpaces

section Scheme

variable {X : Scheme.{u}} (B : X.Opens → Prop)
  (obj : ∀ W : X.Opens, B W →
    DerivedCategory (SheafOfModules.{u} (structureSheafRing W.toScheme.toRingedSpace)))
  (iso : ∀ {W' W : X.Opens} (h : W' ≤ W) (hW : B W) (hW' : B W'),
    (derivedPullback (X.homOfLE h).toLRSHom.toShHom).obj (obj W hW) ≅ obj W' hW')

/-- The restriction isomorphisms of a system at the locally small model, read at the standard
model. -/
def isoStandard {W' W : X.Opens} (h : W' ≤ W) (hW : B W) (hW' : B W') :
    (@derivedPullback _ _ (X.homOfLE h).toLRSHom.toShHom (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) inferInstance).obj
        ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W hW)) ≅
      (Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W' hW') :=
  (Stacks.Injectives.grothendieckModelEquiv _).fullyFaithfulFunctor.preimageIso
    ((derivedPullbackModelIso (X.homOfLE h).toLRSHom.toShHom).app
      ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W hW)) ≪≫ iso h hW hW')

/-- Transported back to the locally small model, the forward map of `isoStandard` is the
component of `derivedPullbackModelIso` followed by the forward map of the given isomorphism. -/
theorem map_isoStandard_hom {W' W : X.Opens} (h : W' ≤ W) (hW : B W) (hW' : B W') :
    (Stacks.Injectives.grothendieckModelEquiv _).functor.map
        (isoStandard B obj iso h hW hW').hom =
      (derivedPullbackModelIso (X.homOfLE h).toLRSHom.toShHom).hom.app
        ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W hW)) ≫
        (iso h hW hW').hom :=
  (Stacks.Injectives.grothendieckModelEquiv _).fullyFaithfulFunctor.map_preimage _

variable (cocycle : ∀ {W'' W' W : X.Opens} (h₁ : W'' ≤ W') (h₂ : W' ≤ W) (hW : B W)
    (hW' : B W') (hW'' : B W''),
    (iso (h₁.trans h₂) hW hW'').hom =
      (derivedPullbackCompIsoCanonical (X.homOfLE h₁).toLRSHom.toShHom
          (X.homOfLE h₂).toLRSHom.toShHom ≪≫
        derivedPullbackCongr (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
          (X.homOfLE_homOfLE h₁ h₂))).inv.app (obj W hW) ≫
        (derivedPullback (X.homOfLE h₁).toLRSHom.toShHom).map (iso h₂ hW hW').hom ≫
          (iso h₁ hW' hW'').hom)

private theorem cocycle_chase {D D' : Type*} [Category D] [Category D'] (L : D' ⥤ D)
    {P Q Ps' Ps'' Z : D} {S₁ S₂ S₃ : D'}
    (m₁₂ : P ≅ Q) (cL : L.obj S₂ ≅ Q) (m₂ : S₁ ≅ S₂) (m₁a : Ps' ≅ L.obj S₁) (m₁b : Ps'' ≅ L.obj S₃)
    (i₁₂ : Q ⟶ Z) (i₂ : S₂ ⟶ S₃) (i₁ : L.obj S₃ ⟶ Z) (GF : P ⟶ Ps') (Gx : Ps' ⟶ Ps'')
    (y₂ : S₁ ⟶ S₃) (y₁ : Ps'' ⟶ Z) (y₁₂ : P ⟶ Z)
    (hF : GF = m₁₂.hom ≫ cL.inv ≫ L.map m₂.inv ≫ m₁a.inv)
    (hx : Gx = m₁a.hom ≫ L.map y₂ ≫ m₁b.inv)
    (h₂ : y₂ = m₂.hom ≫ i₂) (h₁ : y₁ = m₁b.hom ≫ i₁) (h₁₂ : y₁₂ = m₁₂.hom ≫ i₁₂)
    (hc : i₁₂ = cL.inv ≫ L.map i₂ ≫ i₁) :
    y₁₂ = GF ≫ Gx ≫ y₁ := by
  rw [hF, hx, h₂, h₁, h₁₂, hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [← L.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem compat_chase {C D D' : Type*} [Category C] [Category D] [Category D']
    (Gf : C ⥤ D) (L : D' ⥤ D) {a₀ a₁ a₂ a₃ : C} (fx : a₀ ⟶ a₁) (rx : a₁ ⟶ a₂) (ix : a₂ ⟶ a₃)
    {Q : D} {S₁ S₂ S₃ : D'} (mW' : Gf.obj a₀ ≅ Q) (cL : L.obj S₂ ≅ Q) (mW : S₁ ≅ S₂)
    (mh : Gf.obj a₁ ≅ L.obj S₁) (mh' : Gf.obj a₂ ≅ L.obj S₃) (GA : S₁ ⟶ S₃)
    (i : L.obj S₃ ⟶ Gf.obj a₃) (GA' : Gf.obj a₀ ⟶ Gf.obj a₃)
    (hF : Gf.map fx = mW'.hom ≫ cL.inv ≫ L.map mW.inv ≫ mh.inv)
    (hx : Gf.map rx = mh.hom ≫ L.map GA ≫ mh'.inv) (hi : Gf.map ix = mh'.hom ≫ i)
    (hc : GA' = Gf.map (fx ≫ rx ≫ ix)) :
    mW'.inv ≫ GA' = cL.inv ≫ L.map (mW.inv ≫ GA) ≫ i := by
  rw [hc, Functor.map_comp, Functor.map_comp, hF, hx, hi]
  simp

/-- A system of locally given objects at the locally small model, read at the standard model. -/
def openSystemStandard : OpenSystem B where
  obj W hW := (Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W hW)
  iso h hW hW' := isoStandard B obj iso h hW hW'
  cocycle {W'' W' W} h₁ h₂ hW hW' hW'' := by
    apply (Stacks.Injectives.grothendieckModelEquiv _).functor.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    exact cocycle_chase (derivedPullback (X.homOfLE h₁).toLRSHom.toShHom)
      ((derivedPullbackModelIso (X.homOfLE (h₁.trans h₂)).toLRSHom.toShHom).app
        ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W hW)))
      ((derivedPullbackCompIsoCanonical (X.homOfLE h₁).toLRSHom.toShHom
          (X.homOfLE h₂).toLRSHom.toShHom ≪≫
        derivedPullbackCongr (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
          (X.homOfLE_homOfLE h₁ h₂))).app (obj W hW))
      ((derivedPullbackModelIso (X.homOfLE h₂).toLRSHom.toShHom).app
        ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W hW)))
      ((derivedPullbackModelIso (X.homOfLE h₁).toLRSHom.toShHom).app
        ((@derivedPullback _ _ (X.homOfLE h₂).toLRSHom.toShHom (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) inferInstance).obj
          ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W hW))))
      ((derivedPullbackModelIso (X.homOfLE h₁).toLRSHom.toShHom).app
        ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj (obj W' hW')))
      (iso (h₁.trans h₂) hW hW'').hom (iso h₂ hW hW').hom (iso h₁ hW' hW'').hom _ _ _ _ _
      (map_factorIso_inv_app _ _ _ _ _) (map_derivedPullback_map _ _)
      (map_isoStandard_hom B obj iso h₂ hW hW') (map_isoStandard_hom B obj iso h₁ hW' hW'')
      (map_isoStandard_hom B obj iso (h₁.trans h₂) hW hW'') (cocycle h₁ h₂ hW hW' hW'')

include cocycle in
/-- **Locally given derived objects glue over a finite cover, at the locally small model.**
Let `B` be a property of opens of `X` stable under shrinking, `(K_W, ρ_{W'W})` a system of
locally given objects at the locally small model on the opens with `B` whose negative self-Ext
vanishes (read at the standard model, which has the same objects). If finitely many opens with
`B` cover `X`, there is an object `F` of `D(𝒪_X)` with isomorphisms `F|_W ≅ K_W` for all `W` with
`B W`, compatible with the `ρ_{W'W}`. -/
theorem exists_solution_locallySmall (hB : ∀ {W' W : X.Opens}, W' ≤ W → B W → B W')
    (hExt : ∀ W hW (g : ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj
        (obj W hW))⟦(1 : ℤ)⟧ ⟶ (Stacks.Injectives.grothendieckModelEquiv _).inverse.obj
          (obj W hW)), g = 0)
    {ι : Type*} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, B (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
      (a : ∀ (W : X.Opens) (hW : B W), (derivedPullback W.ι.toLRSHom.toShHom).obj F ≅ obj W hW),
      ∀ {W' W : X.Opens} (h : W' ≤ W) (hW : B W) (hW' : B W'),
        (a W' hW').hom =
          (derivedPullbackCompIsoCanonical (X.homOfLE h).toLRSHom.toShHom W.ι.toLRSHom.toShHom ≪≫
            derivedPullbackCongr (congrArg (fun m : W'.toScheme ⟶ X ↦ m.toLRSHom.toShHom)
              (X.homOfLE_ι h))).inv.app F ≫
            (derivedPullback (X.homOfLE h).toLRSHom.toShHom).map (a W hW).hom ≫
              (iso h hW hW').hom := by
  obtain ⟨sol⟩ := (openSystemStandard B obj iso cocycle).exists_solution hB hExt U hU hcov
  refine ⟨(Stacks.Injectives.grothendieckModelEquiv _).functor.obj sol.F,
    fun W hW => ((derivedPullbackModelIso W.ι.toLRSHom.toShHom).app sol.F).symm ≪≫
      (Stacks.Injectives.grothendieckModelEquiv _).functor.mapIso (sol.iso W le_top hW),
    fun {W' W} h hW hW' => ?_⟩
  exact compat_chase (Stacks.Injectives.grothendieckModelEquiv _).functor
    (derivedPullback (X.homOfLE h).toLRSHom.toShHom) _ _ _
    ((derivedPullbackModelIso W'.ι.toLRSHom.toShHom).app sol.F)
    ((derivedPullbackCompIsoCanonical (X.homOfLE h).toLRSHom.toShHom W.ι.toLRSHom.toShHom ≪≫
      derivedPullbackCongr (congrArg (fun m : W'.toScheme ⟶ X ↦ m.toLRSHom.toShHom)
        (X.homOfLE_ι h))).app ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj sol.F))
    ((derivedPullbackModelIso W.ι.toLRSHom.toShHom).app sol.F)
    ((derivedPullbackModelIso (X.homOfLE h).toLRSHom.toShHom).app _)
    ((derivedPullbackModelIso (X.homOfLE h).toLRSHom.toShHom).app _) _ (iso h hW hW').hom _
    (map_factorIso_inv_app _ _ _ _ _) (map_derivedPullback_map _ _)
    (map_isoStandard_hom B obj iso h hW hW')
    (congrArg (Stacks.Injectives.grothendieckModelEquiv _).functor.map
      (sol.compat h le_top hW hW'))

end Scheme

end Stacks.Cohomology.GlueingComplexes

end

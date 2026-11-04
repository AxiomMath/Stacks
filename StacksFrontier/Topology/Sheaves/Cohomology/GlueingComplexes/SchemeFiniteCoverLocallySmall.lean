module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.SchemeFiniteCover

/-!
# Glueing derived morphisms over a finite cover, at the locally small model

`Stacks.Cohomology.GlueingComplexes.existsUnique_map_eq_of_iSup_eq_top` glues morphisms of
`D(𝒪_X)` along a finite open cover at the standard model of the derived categories. This file
carries it to the locally small model of [Stacks, Tag 079Q], at which the upper shriek functors
live. The two models have the same objects; morphisms between derived pullbacks are carried
across by `StacksDraft.DerivedModel.derivedPullbackModelIso`, compatibly with the composition
isomorphisms of [Stacks, Tag 0D5S].

## Main definitions

* `Stacks.Cohomology.GlueingComplexes.pullbackHomToStandard`: a morphism
  `Lf^*K ⟶ Lf^*E` at the locally small model, read at the standard model.

## Main results

* `Stacks.Cohomology.GlueingComplexes.pullbackHomToStandard_factor`: the transport is compatible
  with restriction along a factorisation.
* `Stacks.Cohomology.GlueingComplexes.existsUnique_map_eq_of_iSup_eq_top_locallySmall`: glueing
  along a finite open cover at the locally small model.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
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

/-- A morphism between derived pullbacks at the locally small model, read at the standard model:
conjugation by the comparison `StacksDraft.DerivedModel.derivedPullbackModelIso`. -/
def pullbackHomToStandard (f : A ⟶ Z)
    (K E : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z))))
    (φ : (derivedPullback f).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K) ⟶
      (derivedPullback f).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj E)) :
    (@derivedPullback A Z f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        inferInstance).obj K ⟶
      (@derivedPullback A Z f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        inferInstance).obj E :=
  (Stacks.Injectives.grothendieckModelEquiv _).fullyFaithfulFunctor.preimage
    ((derivedPullbackModelIso f).hom.app K ≫ φ ≫ (derivedPullbackModelIso f).inv.app E)

/-- The image of `pullbackHomToStandard f K E φ` at the locally small model is the conjugate of `φ`
by `StacksDraft.DerivedModel.derivedPullbackModelIso`. -/
theorem map_pullbackHomToStandard (f : A ⟶ Z)
    (K E : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z))))
    (φ : (derivedPullback f).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K) ⟶
      (derivedPullback f).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj E)) :
    (Stacks.Injectives.grothendieckModelEquiv _).functor.map (pullbackHomToStandard f K E φ) =
      (derivedPullbackModelIso f).hom.app K ≫ φ ≫ (derivedPullbackModelIso f).inv.app E :=
  (Stacks.Injectives.grothendieckModelEquiv _).fullyFaithfulFunctor.map_preimage _

/-- The map `pullbackHomToStandard f K E` is injective. -/
theorem pullbackHomToStandard_injective (f : A ⟶ Z)
    (K E : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z)))) :
    Function.Injective (pullbackHomToStandard f K E) := by
  intro φ ψ h
  have h' := congrArg (Stacks.Injectives.grothendieckModelEquiv _).functor.map h
  rw [map_pullbackHomToStandard, map_pullbackHomToStandard] at h'
  exact (cancel_mono _).mp ((cancel_epi _).mp h')

/-- The transport of the derived pullback of a morphism is the derived pullback at the standard
model. -/
theorem pullbackHomToStandard_map (f : A ⟶ Z)
    {K E : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z)))} (ψ : K ⟶ E) :
    pullbackHomToStandard f K E
        ((derivedPullback f).map ((Stacks.Injectives.grothendieckModelEquiv _).functor.map ψ)) =
      (@derivedPullback A Z f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        inferInstance).map ψ := by
  apply (Stacks.Injectives.grothendieckModelEquiv _).functor.map_injective
  rw [map_pullbackHomToStandard]
  have nat := (derivedPullbackModelIso f).hom.naturality ψ
  simp only [Functor.comp_map] at nat
  rw [← reassoc_of% nat, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem factor_chase {C : Type*} [Category C] {x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : C}
    (P : x₁ ≅ x₂) (L : x₃ ≅ x₂) (S : x₄ ≅ x₁) (Mp : x₄ ≅ x₅) (Mq : x₅ ≅ x₃)
    (P' : y₁ ≅ y₂) (L' : y₃ ≅ y₂) (S' : y₄ ≅ y₁) (Mp' : y₄ ≅ y₅) (Mq' : y₅ ≅ y₃)
    (Φ : x₃ ⟶ y₃)
    (h : L.hom ≫ P.inv = Mq.inv ≫ Mp.inv ≫ S.hom)
    (h' : L'.hom ≫ P'.inv = Mq'.inv ≫ Mp'.inv ≫ S'.hom) :
    P.hom ≫ (L.inv ≫ Φ ≫ L'.hom) ≫ P'.inv =
      S.inv ≫ (Mp.hom ≫ (Mq.hom ≫ Φ ≫ Mq'.inv) ≫ Mp'.inv) ≫ S'.hom := by
  have e : P.hom ≫ L.inv = S.inv ≫ Mp.hom ≫ Mq.hom := by
    simpa using congrArg (fun i => i.symm.hom) (Iso.ext h : L ≪≫ P.symm = Mq.symm ≪≫ Mp.symm ≪≫ S)
  simp only [Category.assoc]
  rw [reassoc_of% e, h']

/-- **The transport is compatible with restriction along a factorisation**: for `p ≫ q = k`,
transporting the restriction along `p` of a morphism over `q` is restricting its transport. -/
theorem pullbackHomToStandard_factor (p : A ⟶ B) (q : B ⟶ Z) (k : A ⟶ Z) (e : p ≫ q = k)
    (K E : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z))))
    (φ : (derivedPullback q).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K) ⟶
      (derivedPullback q).obj ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj E)) :
    pullbackHomToStandard k K E
        ((derivedPullbackCompIsoCanonical p q ≪≫ derivedPullbackCongr e).inv.app _ ≫
          (derivedPullback p).map φ ≫
            (derivedPullbackCompIsoCanonical p q ≪≫ derivedPullbackCongr e).hom.app _) =
      Stacks.DerivedPullback.factorHom p q k e K E (pullbackHomToStandard q K E φ) := by
  subst e
  apply (Stacks.Injectives.grothendieckModelEquiv _).functor.map_injective
  rw [map_pullbackHomToStandard]
  have hG := congrArg (Stacks.Injectives.grothendieckModelEquiv _).functor.map
    (pullbackHomToStandard_map p (pullbackHomToStandard q K E φ))
  simp only [map_pullbackHomToStandard] at hG
  simp only [Stacks.DerivedPullback.factorHom, Iso.homCongr_apply, Functor.map_comp, ← hG]
  refine factor_chase ((derivedPullbackModelIso (p ≫ q)).app K)
    ((derivedPullbackCompIsoCanonical p q ≪≫ derivedPullbackCongr rfl).app _)
    ((Stacks.Injectives.grothendieckModelEquiv _).functor.mapIso
      ((Stacks.DerivedPullback.factorIso p q (p ≫ q) rfl).app K))
    ((derivedPullbackModelIso p).app ((@derivedPullback B Z q (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) inferInstance).obj K)) ((derivedPullback p).mapIso
      ((derivedPullbackModelIso q).app K))
    ((derivedPullbackModelIso (p ≫ q)).app E)
    ((derivedPullbackCompIsoCanonical p q ≪≫ derivedPullbackCongr rfl).app _)
    ((Stacks.Injectives.grothendieckModelEquiv _).functor.mapIso
      ((Stacks.DerivedPullback.factorIso p q (p ≫ q) rfl).app E))
    ((derivedPullbackModelIso p).app ((@derivedPullback B Z q (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) inferInstance).obj E)) ((derivedPullback p).mapIso
      ((derivedPullbackModelIso q).app E)) _ ?_ ?_ <;>
  · simp only [Iso.trans_hom, NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
      StacksDraft.DerivedModel.derivedPullbackCongr_hom_app, eqToHom_refl]
    exact (congrArg (· ≫ _) (Category.comp_id _)).trans
      (StacksDraft.DerivedModel.derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso p q _)

end RingedSpaces

section Schemes

variable {X : Scheme.{u}}

/-- Restriction of derived morphisms from an open `U` to an open `W ≤ U` at the locally small
model: derived pullback along `W ⟶ U`, read through the composition isomorphism of
[Stacks, Tag 0D5S] for `W ⟶ U ⟶ X`. -/
def restrictHomLocallySmall {W U : X.Opens} (h : W ≤ U)
    (K E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (φ : (derivedPullback U.ι.toLRSHom.toShHom).obj K ⟶
      (derivedPullback U.ι.toLRSHom.toShHom).obj E) :
    (derivedPullback W.ι.toLRSHom.toShHom).obj K ⟶ (derivedPullback W.ι.toLRSHom.toShHom).obj E :=
  (derivedPullbackCompIsoCanonical (X.homOfLE h).toLRSHom.toShHom U.ι.toLRSHom.toShHom ≪≫
      derivedPullbackCongr (congrArg (fun m : W.toScheme ⟶ X ↦ m.toLRSHom.toShHom)
        (X.homOfLE_ι h))).inv.app K ≫
    (derivedPullback (X.homOfLE h).toLRSHom.toShHom).map φ ≫
    (derivedPullbackCompIsoCanonical (X.homOfLE h).toLRSHom.toShHom U.ι.toLRSHom.toShHom ≪≫
      derivedPullbackCongr (congrArg (fun m : W.toScheme ⟶ X ↦ m.toLRSHom.toShHom)
        (X.homOfLE_ι h))).hom.app E

/-- **Glueing derived morphisms along a finite open cover, at the locally small model.** Let
`X = ⋃ U_i` be a finite open cover and `K`, `E` objects of `D(𝒪_X)` with `Ext^{-1}(K|_W, E|_W) = 0`
for every open `W` contained in some `U_i` (read at the standard model, which has the same
objects). A family of morphisms `a_i : K|_{U_i} ⟶ E|_{U_i}` agreeing on the overlaps is the
family of restrictions of a unique morphism `K ⟶ E`. -/
theorem existsUnique_map_eq_of_iSup_eq_top_locallySmall {ι : Type*} [Finite ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (K E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hExt : ∀ W : X.Opens, (∃ i, W ≤ U i) →
      ∀ g : ((@derivedPullback _ _ W.ι.toLRSHom.toShHom (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) inferInstance).obj
            ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj K))⟦(1 : ℤ)⟧ ⟶
        (@derivedPullback _ _ W.ι.toLRSHom.toShHom (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) inferInstance).obj
            ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj E), g = 0)
    (a : ∀ i, (derivedPullback (U i).ι.toLRSHom.toShHom).obj K ⟶
      (derivedPullback (U i).ι.toLRSHom.toShHom).obj E)
    (ha : ∀ i j, restrictHomLocallySmall (inf_le_left : U i ⊓ U j ≤ U i) K E (a i) =
      restrictHomLocallySmall (inf_le_right : U i ⊓ U j ≤ U j) K E (a j)) :
    ∃! φ : K ⟶ E, ∀ i, (derivedPullback (U i).ι.toLRSHom.toShHom).map φ = a i := by
  let G := Stacks.Injectives.grothendieckModelEquiv
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let K₀ := G.inverse.obj K
  let E₀ := G.inverse.obj E
  let b : ∀ i, OpenHom K₀ E₀ (U i) := fun i => pullbackHomToStandard _ K₀ E₀ (a i)
  have restrict_b : ∀ (i : ι) {W : X.Opens} (h : W ≤ U i), restrictHom K₀ E₀ h (b i) =
      pullbackHomToStandard _ K₀ E₀ (restrictHomLocallySmall (U := U i) h K E (a i)) :=
    fun i W h => (pullbackHomToStandard_factor (X.homOfLE h).toLRSHom.toShHom
      (U i).ι.toLRSHom.toShHom W.ι.toLRSHom.toShHom
      (congrArg (fun m : W.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h)) K₀ E₀ (a i)).symm
  have hb : ∀ i j, restrictHom K₀ E₀ (inf_le_left : U i ⊓ U j ≤ U i) (b i) =
      restrictHom K₀ E₀ (inf_le_right : U i ⊓ U j ≤ U j) (b j) := fun i j => by
    rw [restrict_b, restrict_b, ha]
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_map_eq_of_iSup_eq_top K₀ E₀ U hU hExt b hb
  have key : ∀ (ψ' : K₀ ⟶ E₀) (i : ι),
      pullbackHomToStandard _ K₀ E₀ ((derivedPullback (U i).ι.toLRSHom.toShHom).map
        (G.functor.map ψ')) =
      (@derivedPullback _ _ (U i).ι.toLRSHom.toShHom (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) inferInstance).map ψ' :=
    fun ψ' i => pullbackHomToStandard_map _ ψ'
  refine ⟨G.functor.map ψ, fun i => pullbackHomToStandard_injective _ K₀ E₀
    ((key ψ i).trans (hψ i)), fun φ' hφ' => ?_⟩
  have hφ'' := G.fullyFaithfulFunctor.map_preimage φ'
  refine hφ''.symm.trans (congrArg G.functor.map (hu _ fun i => ?_))
  exact (key _ i).symm.trans (congrArg (pullbackHomToStandard _ K₀ E₀)
    ((congrArg (derivedPullback (U i).ι.toLRSHom.toShHom).map hφ'').trans (hφ' i)))

end Schemes

end Stacks.Cohomology.GlueingComplexes

end

module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapFlatChain

/-!
# Flat base change on the `A`-side of the base-change map of Stacks 0DJ7

Let `R → A`, `R → R'` be ring maps and `A → A₁` a flat ring map. For `K ∈ D(A)` the map
`Hⁿ(K|_R ⊗ᴸ_R R') → Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')` induced by the unit `K → (K ⊗ᴸ_A A₁)|_A`
exhibits the target, with `A₁` acting through `K ⊗ᴸ_A A₁`, as `A₁ ⊗_A Hⁿ(K|_R ⊗ᴸ_R R')`.

The proof computes `(-)|_R ⊗ᴸ_R R'` by a K-flat resolution `F → R'` over `R`: on a complex `P`
of `A`-modules it is `P|_R ⊗_R F = (P ⊗_A (A ⊗_R F))|_R`, and flat base change commutes with the
cohomology of `P ⊗_A (A ⊗_R F)`.

## Main results

* `RingTheory.TorIndependence.isBaseChangeOfActions_derivedUnit`: the base-change statement above.

## References

* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CochainComplex.ExtendScalars
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

section FirstSquare

variable {R R' A A₁ : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing A₁]
  [Algebra A A₁]

instance dext_additive (φ : R →+* R') : (dext φ).Additive :=
  (totalDerivedExtensionScalarsAdjunction φ).left_adjoint_additive

/-- `Hⁿ(- ⊗ᴸ_R R')`, read over `R`. -/
abbrev baseChangeHomologyRestrict (g : R →+* R') (n : ℤ) :
    DerivedCategory (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  dext g ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n ⋙ ModuleCat.restrictScalars.{u} g

/-- The two spellings of degreewise restriction of scalars. -/
def restrictScalarsLargeIso (φ : R →+* A) :
    (ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      CochainComplex.restrictScalarsLarge.{u, u, u} φ :=
  Iso.refl _

/-- **The chain-level model of `Hⁿ((-)|_R ⊗ᴸ_R R')`.** For a K-flat resolution `F → R'` over `R`
and `E = A ⊗_R F`, on complexes of `A`-modules `Hⁿ(Q(P)|_R ⊗ᴸ_R R') ≅ Hⁿ(P ⊗_A E)|_R`. -/
def baseChangeHomologyModel (f : R →+* A) (g : R →+* R')
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : F.KFlat)
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) [QuasiIso q] (n : ℤ) :
    DerivedCategory.Q ⋙ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        baseChangeHomologyRestrict g n ≅
      tensorRight ((mapCochainComplex f).obj F) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n ⋙
          ModuleCat.restrictScalars.{u} f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
      (baseChangeHomologyRestrict g n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)) (resolutionHomologyIso g F hF q n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (restrictScalarsLargeIso f) (tensorRight F))
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n) ≪≫
    Functor.isoWhiskerRight (NatIso.ofComponents
      (fun L => asIso (projectionMap f L F)) (fun {L L'} v => projectionMap_naturality f v F))
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tensorRight ((mapCochainComplex f).obj F))
      (Functor.isoWhiskerRight (restrictScalarsLargeIso f).symm _ ≪≫
        (ModuleCat.restrictScalars.{u} f).mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n)

/-- **Flat base change on the `A`-side (the core of Stacks 0DJ8, step (c)).** For ring maps
`f : R → A`, `g : R → R'`, a flat `A`-algebra `A₁` and `K ∈ D(A)`, the map
`Hⁿ(K|_R ⊗ᴸ_R R') → Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')` induced by the unit of Stacks 0GMT is a base
change along `A → A₁`, `A` and `A₁` acting through `K` and `K ⊗ᴸ_A A₁`. -/
theorem isBaseChangeOfActions_derivedUnit [Module.Flat A A₁] (f : R →+* A) (g : R →+* R')
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    IsBaseChangeOfActions
      (functorAction (A := A) ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        baseChangeHomologyRestrict g n) K)
      (functorAction (A := A₁) (((ModuleCat.restrictScalars.{u} (algebraMap A A₁)).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategory) ⋙ baseChangeHomologyRestrict g n)
        ((dext (algebraMap A A₁)).obj K))
      ((baseChangeHomologyRestrict g n).map ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsAdjunction (algebraMap A A₁)).unit.app K))).hom.toAddMonoidHom := by
  let a := algebraMap A A₁
  obtain ⟨F, q, hF, -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
  haveI := hq
  let E := (mapCochainComplex f).obj F
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let Q₁ := DerivedCategory.Q (C := ModuleCat.{u} A₁)
  let Rf := (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
  let Ra := (ModuleCat.restrictScalars.{u} a).mapDerivedCategory
  let rac := (ModuleCat.restrictScalars.{u} a).mapHomologicalComplex (ComplexShape.up ℤ)
  let G₀ := baseChangeHomologyRestrict g n
  let HA := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n
  let Sc := tensorRight E ⋙ HA ⋙ ModuleCat.restrictScalars.{u} f
  let σ : Q ⋙ Rf ⋙ G₀ ≅ Sc := baseChangeHomologyModel f g F hF q n
  let faca := (ModuleCat.restrictScalars.{u} a).mapDerivedCategoryFactors
  let τ : Q₁ ⋙ Ra ⋙ Rf ⋙ G₀ ≅ rac ⋙ Sc :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight faca (Rf ⋙ G₀) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft rac σ
  let adj := extendRestrictScalarsComplexAdj a
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} a
  let P := Q.objPreimage K
  let e : Q.obj P ≅ K := Q.objObjPreimageIso K
  let extP := (mapCochainComplex a).obj P
  let uP : P ⟶ rac.obj extP := adj.unit.app P
  -- the chain-level statement
  have hCC := isBaseChangeOfActions_homologyMap_unit_whiskerRight (A₁ := A₁) P E n
  let θ : (Q ⋙ Rf ⋙ G₀).obj P ⟶ (Q₁ ⋙ Ra ⋙ Rf ⋙ G₀).obj extP :=
    G₀.map (Rf.map (Q.map uP ≫ faca.inv.app extP))
  have hsq : θ ≫ τ.hom.app extP = σ.hom.app P ≫ Sc.map uP := by
    have hτ : τ.hom.app extP = G₀.map (Rf.map (faca.hom.app extP)) ≫ σ.hom.app (rac.obj extP) := by
      simp [τ]
    have c : (Q.map uP ≫ faca.inv.app extP) ≫ faca.hom.app extP = Q.map uP := by
      rw [Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _
    have c' : θ ≫ G₀.map (Rf.map (faca.hom.app extP)) = G₀.map (Rf.map (Q.map uP)) := by
      simp only [θ]
      rw [← G₀.map_comp, ← Rf.map_comp, c]
    rw [hτ, ← Category.assoc, c']
    exact σ.hom.naturality uP
  have hQ : IsBaseChangeOfActions (functorAction (A := A) (Q ⋙ Rf ⋙ G₀) P)
      (functorAction (A := A₁) (Q₁ ⋙ Ra ⋙ Rf ⋙ G₀) extP) θ.hom.toAddMonoidHom :=
    (isBaseChangeOfActions_iff_of_natTrans σ.hom τ.hom θ (Sc.map uP) hsq).mpr hCC
  rw [functorAction_comp Q, functorAction_comp Q₁] at hQ
  -- transport from `Q P` to `K`
  let cmp : Q ⋙ D.functor ⟶ (ModuleCat.extendScalars.{u, u, u} a).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ Q₁ := D.comparison
  haveI : D.functor.IsLeftDerivedFunctor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  haveI : IsIso cmp := StacksDraft.DerivedHom.HomModuleBaseChange.isIso_comparison_of_flat
    inferInstance D.functor cmp
  let e' : Q₁.obj extP ≅ (dext a).obj K := (asIso (cmp.app P)).symm ≪≫ (dext a).mapIso e
  refine (isBaseChangeOfActions_iff_of_iso (Rf ⋙ G₀) ((Ra ⋙ Rf) ⋙ G₀) e e' θ _ ?_).mp hQ
  -- the unit at `Q P`
  have hη : (totalDerivedExtensionScalarsAdjunction a).unit.app (Q.obj P) ≫ Ra.map (cmp.app P) =
      Q.map uP ≫ faca.inv.app extP :=
    StacksDraft.DerivedHom.HomModuleBaseChange.unit_app_Q_comp_map_comparison D.functor cmp P
  have hn := (totalDerivedExtensionScalarsAdjunction a).unit.naturality e.hom
  have key : (Q.map uP ≫ faca.inv.app extP) ≫ Ra.map e'.hom =
      e.hom ≫ (totalDerivedExtensionScalarsAdjunction a).unit.app K := by
    rw [← hη]
    simp only [e', Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, Ra.map_comp,
      Category.assoc, ← Ra.map_comp_assoc, IsIso.hom_inv_id, Ra.map_id, Category.id_comp]
    exact hn.symm
  simp only [θ, Functor.comp_map, ← G₀.map_comp, ← Rf.map_comp]
  rw [key, Rf.map_comp, G₀.map_comp]
  rfl

end FirstSquare

end RingTheory.TorIndependence

end

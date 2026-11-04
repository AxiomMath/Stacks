module

public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic

/-!
# Degree-zero cohomology over an open is the sections functor over that open

For a ringed space `(X, 𝒪_X)` and an open `U`, the cohomology functor `H⁰(U, -)` of
`StacksFrontier/Topology/Sheaves/Cohomology/Locality/CohomologyVanishesLocally.lean` is the
zeroth right derived functor of `Γ(U, -)`, and `Γ(U, -)` is left exact
(`Stacks.SectionsExact.preservesFiniteLimits_secF`). So `H⁰(U, -) ≅ Γ(U, -)`, by
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`.

That isomorphism is natural in the sheaf by construction. What is proved here is that it is
also natural in the **open**: it carries the restriction map `H⁰(V, ℱ) ⟶ H⁰(U, ℱ)` of
`Hrestrict` to the restriction map `Γ(V, ℱ) ⟶ Γ(U, ℱ)` of the sheaf. Both restriction maps come
from one natural transformation `Γ(V, -) ⟶ Γ(U, -)`, the first through
`CategoryTheory.NatTrans.rightDerived`, so the statement is an instance of the compatibility of
`CategoryTheory.Functor.toRightDerivedZero` with `CategoryTheory.NatTrans.rightDerived`, proved
first in the generality of an arbitrary additive functor.

## Main results

* `CategoryTheory.Functor.toRightDerivedZero_naturality`: for a natural transformation `α : F ⟶ G`
  of additive functors, `F.toRightDerivedZero ≫ NatTrans.rightDerived α 0 = α ≫
  G.toRightDerivedZero`.
* `HzeroIso`: the comparison `H⁰(U, -) ≅ Γ(U, -)`.
* `bijective_Hzero`: its components are bijective.
* `Hzero_map`: the comparison is natural in the sheaf.
* `Hzero_Hrestrict`: the comparison carries `Hrestrict` to the restriction of sections.

## References

* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category Opposite TopologicalSpace

universe v u w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- **The unit of the zeroth right derived functor is natural in the functor, componentwise.**
Both sides are computed on the chosen injective resolution `P` of the object: there the unit is
`CategoryTheory.InjectiveResolution.toRightDerivedZero_eq` and the induced transformation is
`CategoryTheory.InjectiveResolution.rightDerived_app_eq`. After cancelling the comparison
isomorphisms the identity to be proved is the naturality of `α` at `P.ι.f 0`, read through the
cycles in degree zero. -/
theorem Functor.toRightDerivedZero_naturality_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (Y : C) :
    F.toRightDerivedZero.app Y ≫ (NatTrans.rightDerived α 0).app Y =
      α.app Y ≫ G.toRightDerivedZero.app Y := by
  let P : InjectiveResolution Y := injectiveResolution Y
  let φ := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex
  have hcyc : P.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap φ 0 =
      α.app Y ≫ P.toRightDerivedZero' G := by
    rw [← cancel_mono (HomologicalComplex.iCycles
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex) 0)]
    simp only [assoc, HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc,
      NatTrans.mapHomologicalComplex_app_f, φ]
    simpa using α.naturality (P.ι.f 0)
  have hmap : (CochainComplex.isoHomologyπ₀
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).hom ≫
        HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.cyclesMap φ 0 ≫ (CochainComplex.isoHomologyπ₀
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).hom := by
    rw [← cancel_mono (CochainComplex.isoHomologyπ₀
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).inv,
      assoc, assoc, CochainComplex.isoHomologyπ₀_inv_naturality, Iso.hom_inv_id, comp_id,
      Iso.hom_inv_id_assoc]
  -- the two comparison isomorphisms, named at the `homology` spelling of their target so that
  -- every composite below is written in one spelling
  let eF : (F.rightDerived 0).obj Y ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex).homology 0 :=
    P.isoRightDerivedObj F 0
  let eG : (G.rightDerived 0).obj Y ≅
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex).homology 0 :=
    P.isoRightDerivedObj G 0
  have e1 : (NatTrans.rightDerived α 0).app Y =
      eF.hom ≫ HomologicalComplex.homologyMap φ 0 ≫ eG.inv :=
    InjectiveResolution.rightDerived_app_eq α P 0
  have e2 : F.toRightDerivedZero.app Y = P.toRightDerivedZero' F ≫ (CochainComplex.isoHomologyπ₀
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).hom ≫ eF.inv :=
    P.toRightDerivedZero_eq F
  have e3 : G.toRightDerivedZero.app Y = P.toRightDerivedZero' G ≫ (CochainComplex.isoHomologyπ₀
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).hom ≫ eG.inv :=
    P.toRightDerivedZero_eq G
  clear_value eF eG
  have key : (CochainComplex.isoHomologyπ₀
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).hom ≫
        HomologicalComplex.homologyMap φ 0 ≫ eG.inv =
      HomologicalComplex.cyclesMap φ 0 ≫ (CochainComplex.isoHomologyπ₀
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).hom ≫ eG.inv := by
    rw [← assoc, hmap, assoc]
  rw [e1, e2, e3, assoc, assoc, Iso.inv_hom_id_assoc, key, ← assoc, hcyc, assoc]

/-- **The unit of the zeroth right derived functor is natural in the functor.** -/
theorem Functor.toRightDerivedZero_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) :
    F.toRightDerivedZero ≫ NatTrans.rightDerived α 0 = α ≫ G.toRightDerivedZero := by
  ext Y
  simpa using Functor.toRightDerivedZero_naturality_app α Y

end CategoryTheory

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} R)]

/-- **The comparison between degree-zero cohomology over `U` and sections over `U`.** -/
noncomputable def HzeroIso (U : Opens X) : Hfunctor R U 0 ≅ secF R U :=
  Functor.rightDerivedZeroIsoSelf (secF.{u, _, w} R U)

/-- The comparison map `H⁰(U, ℱ) ⟶ Γ(U, ℱ)` is bijective. -/
theorem bijective_Hzero (U : Opens X) (G : SheafOfModules.{w} R) :
    Function.Bijective (ConcreteCategory.hom ((HzeroIso R U).hom.app G)) :=
  ConcreteCategory.bijective_of_isIso ((HzeroIso R U).hom.app G)

/-- **The comparison map is natural in the sheaf**: it carries the map induced on degree-zero
cohomology by a morphism of sheaves to the map induced on sections. -/
theorem Hzero_map (U : Opens X) {G G' : SheafOfModules.{w} R} (φ : G ⟶ G')
    (ξ : (Hgroup R U 0 G : Type w)) :
    ConcreteCategory.hom ((HzeroIso R U).hom.app G')
        (ConcreteCategory.hom ((Hfunctor R U 0).map φ) ξ) =
      ConcreteCategory.hom ((secF R U).map φ)
        (ConcreteCategory.hom ((HzeroIso R U).hom.app G) ξ) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    (HzeroIso R U).hom.naturality φ]

/-- **The comparison is natural in the open**: it carries the restriction of cohomology classes
to the restriction of sections. -/
theorem HzeroIso_hom_HrestrictNT {U V : Opens X} (h : U ≤ V) :
    HrestrictNT R h 0 ≫ (HzeroIso R U).hom = (HzeroIso R V).hom ≫ secRestrict R h := by
  have hn : (HzeroIso R V).inv ≫ HrestrictNT R h 0 =
      secRestrict R h ≫ (HzeroIso R U).inv :=
    Functor.toRightDerivedZero_naturality (secRestrict.{u, _, w} R h)
  rw [← cancel_epi (HzeroIso R V).inv, ← assoc, hn, assoc, Iso.inv_hom_id, comp_id]
  exact (Iso.inv_hom_id_assoc (HzeroIso R V) (secRestrict R h)).symm

/-- **The comparison map is natural in the open**, read on a class. -/
theorem Hzero_Hrestrict {U V : Opens X} (h : U ≤ V) (G : SheafOfModules.{w} R)
    (ξ : (Hgroup R V 0 G : Type w)) :
    ConcreteCategory.hom ((HzeroIso R U).hom.app G)
        (ConcreteCategory.hom (Hrestrict R h 0 G) ξ) =
      ConcreteCategory.hom ((secRestrict R h).app G)
        (ConcreteCategory.hom ((HzeroIso R V).hom.app G) ξ) := by
  have happ := congrArg (fun ψ => NatTrans.app ψ G) (HzeroIso_hom_HrestrictNT R h)
  simp only [NatTrans.comp_app] at happ
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congrArg
    (fun ψ : Hgroup R V 0 G ⟶ (secF R U).obj G => ConcreteCategory.hom ψ ξ) happ

end

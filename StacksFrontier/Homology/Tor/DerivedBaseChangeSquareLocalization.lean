module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquationsUnit
public import StacksFrontier.Homology.Tor.DerivedExtensionLocalizationComp
public import StacksFrontier.Homology.Tor.Independence

/-!
# The derived base-change comparison, natural along a square of localizations

Let `R → A` and `R → R'`, `A → A'`, `R' → A'` be a commuting square of commutative rings. Tag 065Z
attaches to it a comparison `K ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A A')|_{R'}`, natural in `K ∈ D(A)`:
`RingTheory.TorIndependence.derivedBaseChangeComparison`. This file compares it with the comparison
of a square of localizations.

Let `R₂` be a localization of `R` and `A₂` one of `A`, compatibly, and let the two *target* corners
`R'` and `A'` already be algebras over `R₂` resp. `A₂`, forming a commuting square over `R₂`. There
are then two squares with the same target corners,

`(R, A, R', A')`  and  `(R₂, A₂, R', A')`,

and for a complex `N` that already lives over `A₂` the comparison of the first, evaluated at `N`
read over `A`, has the same source and target as the comparison of the second at `N`. The main
result says the two comparisons *are* the same map under those identifications.

## Main definitions

* `RingTheory.TorIndependence.mapDerivedCategoryCompNatIso`: a composition isomorphism for
  `CategoryTheory.Functor.mapDerivedCategory`.
* `RingTheory.TorIndependence.derivedRestrictScalarsSquareIso`: restriction of scalars around a
  commuting square of rings, read on derived categories.
* `RingTheory.TorIndependence.squareComparison`: the Tag 065Z comparison of a commuting square of
  rings.
* `RingTheory.TorIndependence.localizedSquareDomainIso` and
  `RingTheory.TorIndependence.localizedSquareCodomainIso`: the identifications of the sources and
  of the targets of the two comparisons.

## Main results

* `RingTheory.TorIndependence.squareComparison_localized`: the two comparisons agree.
* `RingTheory.TorIndependence.localizedSquareUnderived_compat` and
  `RingTheory.TorIndependence.localizedSquareUnderived_compat_app`: the corresponding statement for
  the two underived comparisons, degreewise: both composites send `1 ⊗ x` to `1 ⊗ x`.
* `RingTheory.TorIndependence.localizedSquareDomainIso_comparison` and
  `RingTheory.TorIndependence.localizedSquareCodomainIso_comparison`: the identifications of the
  sources and of the targets, each computed against the comparison with degreewise extension of
  scalars at a complex.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

section Bricks

variable {C D E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  [Category E] [Abelian E] [HasDerivedCategory E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- A natural isomorphism `F ⋙ G ≅ H` between exact functors between abelian categories, read on
derived categories. -/
public def mapDerivedCategoryCompNatIso (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (DerivedCategory.Q ⋙ H.mapDerivedCategory) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫ H.mapDerivedCategoryFactors.symm)

/-- The characterizing equation of `mapDerivedCategoryCompNatIso` at a complex. -/
public theorem mapDerivedCategoryCompNatIso_hom_app_Q (e : F ⋙ G ≅ H)
    (P : CochainComplex C ℤ) :
    (mapDerivedCategoryCompNatIso F G H e).hom.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app P) ≫
        H.mapDerivedCategoryFactors.inv.app P := by
  simp only [mapDerivedCategoryCompNatIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]

end Bricks

section Comparison

/-- The comparison of derived with degreewise extension of scalars, at a complex, with its source
and target spelled out through `CategoryTheory.Functor.mapHomologicalComplex` and the localization
functor. -/
public abbrev extendComparisonApp {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T)
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} T)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  (totalDerivedExtensionScalars.{u, u, u} f).comparison.app P

end Comparison

section LocalizationComp

variable {A A₂ B : Type u} [CommRing A] [CommRing A₂] [CommRing B] [Algebra A A₂]
  (S : Submonoid A) [IsLocalization S A₂] (g : A₂ →+* B)
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

include S in
/-- **The characterizing equation of derived extension of scalars through a localization.** At a
complex `P` of `A₂`-modules, the isomorphism
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` read against the comparison of
derived with degreewise extension of scalars is: the derived extension along `A → B` of the
factorization of restriction of scalars, the comparison for `A → B`, the scalar-tower isomorphism
of degreewise extension of scalars, and the degreewise underived idempotence of the
localization. -/
public theorem restrictScalarsDerivedExtendCompIso_hom_app_Q
    (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    (restrictScalarsDerivedExtendCompIso.{u, w} S g).hom.app (DerivedCategory.Q.obj P) ≫
        extendComparisonApp.{u, w} g P =
      (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A A₂))).functor.map
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app
            P) ≫
        extendComparisonApp.{u, w} (g.comp (algebraMap A A₂))
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (ModuleCat.extendScalarsComp.{u, u} (algebraMap A A₂) g).symm
                (ComplexShape.up ℤ)).inv.app
                (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
              (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P)) := by
  have hK : (restrictScalarsDerivedExtendCompIso.{u, w} S g).hom.app
        (DerivedCategory.Q.obj P) =
      (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).inv.app
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P)) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((restrictScalarsDerivedExtendIso.{u, w} S (A₂ := A₂)).hom.app
            (DerivedCategory.Q.obj P)) := by
    simp [restrictScalarsDerivedExtendCompIso]
  have hrs : (restrictScalarsDerivedExtendIso.{u, w} S (A₂ := A₂)).hom.app
        (DerivedCategory.Q.obj P) =
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.map
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app
            P) ≫
        extendComparisonApp.{u, w} (algebraMap A A₂)
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P) :=
    restrictScalarsDerivedExtendIso_hom_app_Q.{u, w} S P
  have hnat : (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          (DerivedCategory.Q.map ((restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P)) ≫
        extendComparisonApp.{u, w} g P =
      extendComparisonApp.{u, w} g
          (((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            ((restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P)) :=
    (totalDerivedExtensionScalars.{u, u, u} g).comparison.naturality
      ((restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P)
  have hcp : (totalDerivedExtensionScalars.{u, u, u} g).functor.map
            (extendComparisonApp.{u, w} (algebraMap A A₂)
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          extendComparisonApp.{u, w} g
            (((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.extendScalarsComp.{u, u} (algebraMap A A₂) g).symm
              (ComplexShape.up ℤ)).hom.app
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) =
        (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).hom.app
            (DerivedCategory.Q.obj
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          extendComparisonApp.{u, w} (g.comp (algebraMap A A₂))
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) :=
    totalDerivedExtensionScalarsComp_comparison.{u, u} (algebraMap A A₂) g
      (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
  have hcompnat : (totalDerivedExtensionScalars.{u, u, u} g).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.map
              ((ModuleCat.restrictScalars.{u}
                (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app P)) ≫
          (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).hom.app
            (DerivedCategory.Q.obj
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) =
        (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).hom.app
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A A₂))).functor.map
            ((ModuleCat.restrictScalars.{u}
              (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app P) :=
    (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).hom.naturality
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app P)
  have hcp2 : (totalDerivedExtensionScalars.{u, u, u} g).functor.map
            (extendComparisonApp.{u, w} (algebraMap A A₂)
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          extendComparisonApp.{u, w} g
            (((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) =
        ((totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).hom.app
              (DerivedCategory.Q.obj
                (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            extendComparisonApp.{u, w} (g.comp (algebraMap A A₂))
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.extendScalarsComp.{u, u} (algebraMap A A₂) g).symm
              (ComplexShape.up ℤ)).inv.app
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) := by
    rw [← hcp]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
      CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Category.assoc] at hcp2
  rw [hK, hrs]
  simp only [Functor.map_comp, Category.assoc, hnat, reassoc_of% hcp2,
    reassoc_of% hcompnat, Iso.inv_hom_id_app_assoc]

end LocalizationComp

section RestrictSquare

variable {R M N Z : Type u} [CommRing R] [CommRing M] [CommRing N] [CommRing Z]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} M)]
  [HasDerivedCategory.{w} (ModuleCat.{u} N)] [HasDerivedCategory.{w} (ModuleCat.{u} Z)]
  (p : R →+* M) (q : M →+* Z) (p' : R →+* N) (q' : N →+* Z)
  (hsq : q.comp p = q'.comp p')

/-- The two readings of a complex of `Z`-modules as a complex of `R`-modules around a commuting
square of rings agree degreewise: both restrictions are the identity on underlying groups. -/
public abbrev restrictSquareComplexIso :
    (ModuleCat.restrictScalars.{u} q).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars.{u} p).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.restrictScalars.{u} q').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars.{u} p').mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp'.{u} p q (q.comp p) rfl).symm (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp'.{u} p' q' (q.comp p) hsq).symm
      (ComplexShape.up ℤ)).symm

/-- **Restriction of scalars around a commuting square of rings, read on derived categories.** Both
composites are restriction along the common composite `R → Z`, so each is identified with
`CategoryTheory.Functor.mapDerivedCategory` of that single restriction. -/
public def derivedRestrictScalarsSquareIso :
    (ModuleCat.restrictScalars.{u} q).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} p).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u} q').mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} p').mapDerivedCategory :=
  mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} q)
      (ModuleCat.restrictScalars.{u} p) (ModuleCat.restrictScalars.{u} (q.comp p))
      (ModuleCat.restrictScalarsComp'.{u} p q (q.comp p) rfl).symm ≪≫
    (mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} q')
      (ModuleCat.restrictScalars.{u} p') (ModuleCat.restrictScalars.{u} (q.comp p))
      (ModuleCat.restrictScalarsComp'.{u} p' q' (q.comp p) hsq).symm).symm

include hsq in
/-- **The characterizing equation of `derivedRestrictScalarsSquareIso`.** At a complex it
intertwines the two factorizations of restriction of scalars through complexes: both become the
single factorization for the composite `R → Z`. -/
public theorem derivedRestrictScalarsSquareIso_hom_app_Q
    (P : CochainComplex (ModuleCat.{u} Z) ℤ) :
    (derivedRestrictScalarsSquareIso.{u, w} p q p' q' hsq).hom.app
          (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} p').mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u} q').mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u} p').mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{u} q').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp'.{u} p' q' (q.comp p) hsq).symm
              (ComplexShape.up ℤ)).hom.app P) =
      (ModuleCat.restrictScalars.{u} p).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u} q).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u} p).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{u} q).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp'.{u} p q (q.comp p) rfl).symm
              (ComplexShape.up ℤ)).hom.app P) := by
  have h1 := mapDerivedCategoryCompNatIso_hom_app_Q (ModuleCat.restrictScalars.{u} q)
    (ModuleCat.restrictScalars.{u} p) (ModuleCat.restrictScalars.{u} (q.comp p))
    (ModuleCat.restrictScalarsComp'.{u} p q (q.comp p) rfl).symm P
  have h2 := mapDerivedCategoryCompNatIso_hom_app_Q (ModuleCat.restrictScalars.{u} q')
    (ModuleCat.restrictScalars.{u} p') (ModuleCat.restrictScalars.{u} (q.comp p))
    (ModuleCat.restrictScalarsComp'.{u} p' q' (q.comp p) hsq).symm P
  have hcomp : (derivedRestrictScalarsSquareIso.{u, w} p q p' q' hsq).hom.app
        (DerivedCategory.Q.obj P) ≫
      (mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} q')
        (ModuleCat.restrictScalars.{u} p') (ModuleCat.restrictScalars.{u} (q.comp p))
        (ModuleCat.restrictScalarsComp'.{u} p' q' (q.comp p) hsq).symm).hom.app
          (DerivedCategory.Q.obj P) =
      (mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} q)
        (ModuleCat.restrictScalars.{u} p) (ModuleCat.restrictScalars.{u} (q.comp p))
        (ModuleCat.restrictScalarsComp'.{u} p q (q.comp p) rfl).symm).hom.app
          (DerivedCategory.Q.obj P) := by
    simp [derivedRestrictScalarsSquareIso]
  rw [h1, h2] at hcomp
  rw [← Iso.cancel_iso_inv_right _ _
    ((ModuleCat.restrictScalars.{u} (q.comp p)).mapDerivedCategoryFactors.app P)]
  simpa only [Category.assoc, Iso.app_inv] using hcomp

end RestrictSquare

section SquareComparison

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
  (a : R →+* A) (b : R →+* R') (c : A →+* A') (d : R' →+* A')
  (sq : c.comp a = d.comp b)

/-- The underived base-change comparison of Tag 065Z for a commuting square of rings:
`R' ⊗_R (M|_R) ⟶ (A' ⊗_A M)|_{R'}`. -/
public abbrev squareComparisonUnderived :
    ModuleCat.restrictScalars.{u} a ⋙ ModuleCat.extendScalars.{u, u, u} b ⟶
      ModuleCat.extendScalars.{u, u, u} c ⋙ ModuleCat.restrictScalars.{u} d :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w}
    R A R' A' _ _ _ _ _ _ _ _ a b c d sq
    (totalDerivedExtensionScalars.{u, u, u} b).functor
    (totalDerivedExtensionScalars.{u, u, u} c).functor
    (totalDerivedExtensionScalars.{u, u, u} b).comparison
    (totalDerivedExtensionScalars.{u, u, u} c).comparison
    (totalDerivedExtensionScalars.{u, u, u} b).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} c).isLeftDerived).1

/-- The derived base-change comparison of Tag 065Z for a commuting square of rings, as the natural
transformation `K ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A A')|_{R'}` of functors on derived categories. -/
public abbrev squareComparison :
    (ModuleCat.restrictScalars.{u} a).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} b).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} c).functor ⋙
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategory :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w}
    R A R' A' _ _ _ _ _ _ _ _ a b c d sq
    (totalDerivedExtensionScalars.{u, u, u} b).functor
    (totalDerivedExtensionScalars.{u, u, u} c).functor
    (totalDerivedExtensionScalars.{u, u, u} b).comparison
    (totalDerivedExtensionScalars.{u, u, u} c).comparison
    (totalDerivedExtensionScalars.{u, u, u} b).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} c).isLeftDerived).2.1

/-- The bundle of the comparison of Tag 065Z for a commuting square of rings and its properties. -/
private abbrev squareComparisonBundle :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w}
    R A R' A' _ _ _ _ _ _ _ _ a b c d sq
    (totalDerivedExtensionScalars.{u, u, u} b).functor
    (totalDerivedExtensionScalars.{u, u, u} c).functor
    (totalDerivedExtensionScalars.{u, u, u} b).comparison
    (totalDerivedExtensionScalars.{u, u, u} c).comparison
    (totalDerivedExtensionScalars.{u, u, u} b).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} c).isLeftDerived)

/-- The underived comparison sends a pure tensor `r' ⊗ m` to `d r' ⊗ m`. -/
public theorem squareComparisonUnderived_tmul (M : ModuleCat.{u} A) (r' : R') (m : M) :
    ((squareComparisonUnderived.{u, w} a b c d sq).app M).hom (r' ⊗ₜ[R,b] m) =
      d r' ⊗ₜ[A,c] m :=
  (squareComparisonBundle.{u, w} a b c d sq).2.2.1 M r' m

include sq in
/-- **The unit square of the Tag 065Z comparison.** The unit `K ⟶ (K ⊗ᴸ_R R')|_R` of the derived
change-of-rings adjunction along `R → R'`, taken at the restriction of `W` to `R` and followed by
the comparison of the square read over `R`, is the unit along `A → A'` read over `R`, under
`RingTheory.TorIndependence.derivedRestrictScalarsSquareIso`. -/
public theorem squareComparison_unit (W : DerivedCategory (ModuleCat.{u} A)) :
    (@derivedExtensionScalarsAdjunction.{u, u, u, w, w} R R' _ _ b _ _
            (totalDerivedExtensionScalars.{u, u, u} b).functor
            (totalDerivedExtensionScalars.{u, u, u} b).comparison
            (totalDerivedExtensionScalars.{u, u, u} b).isLeftDerived).unit.app
          ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.obj W) ≫
        (ModuleCat.restrictScalars.{u} b).mapDerivedCategory.map
          ((squareComparison.{u, w} a b c d sq).app W) =
      (ModuleCat.restrictScalars.{u} a).mapDerivedCategory.map
          ((@derivedExtensionScalarsAdjunction.{u, u, u, w, w} A A' _ _ c _ _
            (totalDerivedExtensionScalars.{u, u, u} c).functor
            (totalDerivedExtensionScalars.{u, u, u} c).comparison
            (totalDerivedExtensionScalars.{u, u, u} c).isLeftDerived).unit.app W) ≫
        (derivedRestrictScalarsSquareIso.{u, w} a c b d sq).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj W) :=
  @derivedBaseChangeComparison_snd_app_unit.{u, u, u, u, u, w, w, w, w} R A R' A'
    _ _ _ _ _ _ _ _ a b c d _ _ sq
    (totalDerivedExtensionScalars.{u, u, u} b).functor
    (totalDerivedExtensionScalars.{u, u, u} c).functor
    (totalDerivedExtensionScalars.{u, u, u} b).comparison
    (totalDerivedExtensionScalars.{u, u, u} c).comparison
    (totalDerivedExtensionScalars.{u, u, u} b).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} c).isLeftDerived
    (derivedRestrictScalarsSquareIso.{u, w} a c b d sq).hom
    (derivedRestrictScalarsSquareIso_hom_app_Q.{u, w} a c b d sq) W

/-- **The characterizing equation of the derived base-change comparison.** At the image of a
complex `P` under the localization functor the derived comparison is computed by the underived one,
up to the change-of-rings isomorphisms identifying the two composite functors on complexes. -/
public theorem squareComparison_fac_app (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (squareComparison.{u, w} a b c d sq).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
          (extendComparisonApp.{u, w} c P) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (Iso.refl (ModuleCat.extendScalars.{u, u, u} c ⋙ ModuleCat.restrictScalars.{u} d))
              (ComplexShape.up ℤ)).hom.app P) =
      (totalDerivedExtensionScalars.{u, u, u} b).functor.map
          ((ModuleCat.restrictScalars.{u} a).mapDerivedCategoryFactors.hom.app P) ≫
        extendComparisonApp.{u, w} b
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (Iso.refl (ModuleCat.restrictScalars.{u} a ⋙ ModuleCat.extendScalars.{u, u, u} b))
                (ComplexShape.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (squareComparisonUnderived.{u, w} a b c d sq)
                (ComplexShape.up ℤ)).app P) := by
  have hP := NatTrans.congr_app (squareComparisonBundle.{u, w} a b c d sq).2.2.2 P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.assoc,
    Functor.comp_obj] at hP
  exact hP

end SquareComparison

section Localized

variable {R A R₂ A₂ R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R₂] [CommRing A₂] [CommRing R'] [CommRing A']
  [Algebra R R₂] [Algebra A A₂]
  (SR : Submonoid R) [IsLocalization SR R₂]
  (SA : Submonoid A) [IsLocalization SA A₂]
  (a : R →+* A) (a₂ : R₂ →+* A₂) (b₂ : R₂ →+* R') (c₂ : A₂ →+* A') (d : R' →+* A')
  (hloc : (algebraMap A A₂).comp a = a₂.comp (algebraMap R R₂))
  (hsq : c₂.comp a₂ = d.comp b₂)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R₂)] [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat A)]
  [HasDerivedCategory (ModuleCat R₂)] [HasDerivedCategory (ModuleCat A₂)]
  [HasDerivedCategory (ModuleCat R')] [HasDerivedCategory (ModuleCat A')] in
include hloc hsq in
/-- The mixed square `(R, A, R', A')`, whose two target corners are the localized ones,
commutes. -/
public theorem localizedSquare_comm :
    (c₂.comp (algebraMap A A₂)).comp a = d.comp (b₂.comp (algebraMap R R₂)) := by
  ext r
  exact (congrArg c₂ (DFunLike.congr_fun hloc r)).trans (DFunLike.congr_fun hsq _)

include hloc in
/-- **The source of the comparison, transported.** The derived base change over `R` of an
`A₂`-complex read over `A` is its derived base change over `R₂`: restriction of scalars is
rearranged around the localization square by `derivedRestrictScalarsSquareIso`, and the resulting
`R → R₂ → R'` is contracted by the localization idempotence of
`restrictScalarsDerivedExtendCompIso`. -/
public def localizedSquareDomainIso :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory ⋙
          (totalDerivedExtensionScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).functor) ≅
      (ModuleCat.restrictScalars.{u} a₂).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} b₂).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
        (derivedRestrictScalarsSquareIso.{u, w} a (algebraMap A A₂) (algebraMap R R₂) a₂ hloc)
        (totalDerivedExtensionScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((ModuleCat.restrictScalars.{u} a₂).mapDerivedCategory)
        (restrictScalarsDerivedExtendCompIso.{u, w} SR b₂)

/-- **The target of the comparison, transported.** The derived extension of scalars of an
`A₂`-complex read over `A` along `A → A'` is its derived extension along `A₂ → A'`, by the
localization idempotence of `restrictScalarsDerivedExtendCompIso`. -/
public def localizedSquareCodomainIso :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        ((totalDerivedExtensionScalars.{u, u, u} (c₂.comp (algebraMap A A₂))).functor ⋙
          (ModuleCat.restrictScalars.{u} d).mapDerivedCategory) ≅
      (totalDerivedExtensionScalars.{u, u, u} c₂).functor ⋙
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictScalarsDerivedExtendCompIso.{u, w} SA c₂)
      ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory)

include hloc in
/-- The degreewise identification of the two readings over `R` of a complex of `A₂`-modules:
through `A` and through `R₂`. Both restrictions are the identity on underlying groups. -/
public def localizedRestrictComplexHom (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    ((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      ((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp'.{u} a (algebraMap A A₂)
        ((algebraMap A A₂).comp a) rfl).symm (ComplexShape.up ℤ)).hom.app P ≫
    (Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp'.{u} (algebraMap R R₂) a₂
        ((algebraMap A A₂).comp a) hloc).symm (ComplexShape.up ℤ)).inv.app P

include hloc in
/-- **The source identification, read against the comparison with degreewise extension of
scalars.** `RingTheory.TorIndependence.localizedSquareDomainIso` carries the comparison for
`R₂ → R'` at `P` to the comparison for `R → R'` at `P` read over `R` through `A`, up to the
degreewise identifications. -/
public theorem localizedSquareDomainIso_comparison
    (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    (localizedSquareDomainIso.{u, w} SR a a₂ b₂ hloc).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} b₂).functor.map
          ((ModuleCat.restrictScalars.{u} a₂).mapDerivedCategoryFactors.hom.app P) ≫
        extendComparisonApp.{u, w} b₂
          (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (totalDerivedExtensionScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).functor.map
          ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.map
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app
              P)) ≫
        (totalDerivedExtensionScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).functor.map
            ((ModuleCat.restrictScalars.{u} a).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          extendComparisonApp.{u, w} (b₂.comp (algebraMap R R₂))
              (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
                (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
                (((ModuleCat.extendScalars.{u, u, u}
                  (b₂.comp (algebraMap R R₂))).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map (localizedRestrictComplexHom.{u} a a₂ hloc P)) ≫
              DerivedCategory.Q.map
                  ((Functor.mapHomologicalComplexCompIso
                    (ModuleCat.extendScalarsComp.{u, u} (algebraMap R R₂) b₂).symm
                    (ComplexShape.up ℤ)).inv.app
                    (((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj
                      (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj P))) ≫
                DerivedCategory.Q.map
                  (((ModuleCat.extendScalars.{u, u, u} b₂).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map
                    ((restrictExtendScalarsComplexIso SR (A₂ := R₂)).hom.app
                      (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj P))) := by
  have hΦ : (localizedSquareDomainIso.{u, w} SR a a₂ b₂ hloc).hom.app
        (DerivedCategory.Q.obj P) =
      (totalDerivedExtensionScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).functor.map
          ((derivedRestrictScalarsSquareIso.{u, w} a (algebraMap A A₂) (algebraMap R R₂) a₂
            hloc).hom.app (DerivedCategory.Q.obj P)) ≫
        (restrictScalarsDerivedExtendCompIso.{u, w} SR b₂).hom.app
          ((ModuleCat.restrictScalars.{u} a₂).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P)) := by
    simp [localizedSquareDomainIso]
  have hKnat := (restrictScalarsDerivedExtendCompIso.{u, w} SR b₂).hom.naturality
    ((ModuleCat.restrictScalars.{u} a₂).mapDerivedCategoryFactors.hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hKnat
  have hC := restrictScalarsDerivedExtendCompIso_hom_app_Q.{u, w} SR b₂
    (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hΨ := derivedRestrictScalarsSquareIso_hom_app_Q.{u, w} a (algebraMap A A₂)
    (algebraMap R R₂) a₂ hloc P
  have hΨ' : (derivedRestrictScalarsSquareIso.{u, w} a (algebraMap A A₂) (algebraMap R R₂) a₂
          hloc).hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} (algebraMap R R₂)).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u} a₂).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u} (algebraMap R R₂)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (ModuleCat.restrictScalars.{u} a).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app
            P) ≫
        (ModuleCat.restrictScalars.{u} a).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (localizedRestrictComplexHom.{u} a a₂ hloc P) := by
    have h := congrArg (fun z => z ≫ DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp'.{u} (algebraMap R R₂) a₂
          ((algebraMap A A₂).comp a) hloc).symm (ComplexShape.up ℤ)).inv.app P)) hΨ
    simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
      CategoryTheory.Functor.map_id, Category.comp_id, localizedRestrictComplexHom] using h
  have hΨ'' := congrArg (totalDerivedExtensionScalars.{u, u, u}
    (b₂.comp (algebraMap R R₂))).functor.map hΨ'
  simp only [Functor.map_comp] at hΨ''
  have hγnat : (totalDerivedExtensionScalars.{u, u, u}
          (b₂.comp (algebraMap R R₂))).functor.map
          (DerivedCategory.Q.map (localizedRestrictComplexHom.{u} a a₂ hloc P)) ≫
        extendComparisonApp.{u, w} (b₂.comp (algebraMap R R₂))
          (((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
      extendComparisonApp.{u, w} (b₂.comp (algebraMap R R₂))
          (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, u}
            (b₂.comp (algebraMap R R₂))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (localizedRestrictComplexHom.{u} a a₂ hloc P)) :=
    (totalDerivedExtensionScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).comparison.naturality
      (localizedRestrictComplexHom.{u} a a₂ hloc P)
  rw [hΦ]
  simp only [Category.assoc]
  rw [← reassoc_of% hKnat, hC, reassoc_of% hΨ'', reassoc_of% hγnat]

/-- The degreewise identification of the two readings of the extension of scalars of an
`A₂`-complex to `A'`: through `A` and over `A₂`. -/
public def localizedExtendComplexHom (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    (((ModuleCat.extendScalars.{u, u, u} (c₂.comp (algebraMap A A₂)) ⋙
        ModuleCat.restrictScalars.{u} d).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) ⟶
      ((ModuleCat.extendScalars.{u, u, u} c₂ ⋙
        ModuleCat.restrictScalars.{u} d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
  (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.extendScalars.{u, u, u} (c₂.comp (algebraMap A A₂)) ⋙
          ModuleCat.restrictScalars.{u} d)) (ComplexShape.up ℤ)).inv.app
      (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≫
    ((ModuleCat.restrictScalars.{u} d).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
            (ModuleCat.extendScalarsComp.{u, u} (algebraMap A A₂) c₂).symm
            (ComplexShape.up ℤ)).inv.app
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          ((ModuleCat.extendScalars.{u, u, u} c₂).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            ((restrictExtendScalarsComplexIso SA (A₂ := A₂)).hom.app P)) ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.extendScalars.{u, u, u} c₂ ⋙
          ModuleCat.restrictScalars.{u} d)) (ComplexShape.up ℤ)).hom.app P

/-- **The target identification, read against the comparison with degreewise extension of
scalars.** `RingTheory.TorIndependence.localizedSquareCodomainIso` carries the comparison for
`A → A'` at `P` read over `A` to the comparison for `A₂ → A'` at `P`, up to the degreewise
identifications. -/
public theorem localizedSquareCodomainIso_comparison
    (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    (localizedSquareCodomainIso.{u, w} SA c₂ d).hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
          (extendComparisonApp.{u, w} c₂ P) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars.{u, u, u} c₂).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (Iso.refl (ModuleCat.extendScalars.{u, u, u} c₂ ⋙
                ModuleCat.restrictScalars.{u} d)) (ComplexShape.up ℤ)).hom.app P) =
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} (c₂.comp (algebraMap A A₂))).functor.map
            ((ModuleCat.restrictScalars.{u}
              (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
            (extendComparisonApp.{u, w} (c₂.comp (algebraMap A A₂))
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          (ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{u, u, u}
                (c₂.comp (algebraMap A A₂))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso
                  (Iso.refl (ModuleCat.extendScalars.{u, u, u} (c₂.comp (algebraMap A A₂)) ⋙
                    ModuleCat.restrictScalars.{u} d)) (ComplexShape.up ℤ)).hom.app
                  (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P)) ≫
              DerivedCategory.Q.map (localizedExtendComplexHom.{u} SA c₂ d P) := by
  have hX : (localizedSquareCodomainIso.{u, w} SA c₂ d).hom.app (DerivedCategory.Q.obj P) =
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
        ((restrictScalarsDerivedExtendCompIso.{u, w} SA c₂).hom.app
          (DerivedCategory.Q.obj P)) := by
    simp [localizedSquareCodomainIso]
  have hC := restrictScalarsDerivedExtendCompIso_hom_app_Q.{u, w} SA c₂ P
  have hn : ∀ {X Y : CochainComplex (ModuleCat.{u} A') ℤ} (f : X ⟶ Y),
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.hom.app Y =
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          (((ModuleCat.restrictScalars.{u} d).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    fun f => (ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.hom.naturality f
  have htail : DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.extendScalars.{u, u, u} (c₂.comp (algebraMap A A₂)) ⋙
              ModuleCat.restrictScalars.{u} d)) (ComplexShape.up ℤ)).hom.app
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.extendScalars.{u, u, u} (c₂.comp (algebraMap A A₂)) ⋙
              ModuleCat.restrictScalars.{u} d)) (ComplexShape.up ℤ)).inv.app
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) = CategoryStruct.id _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [hX, ← Category.assoc, ← Functor.map_comp, hC]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hn]
  simp only [localizedExtendComplexHom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% htail]

include hloc hsq in
/-- **The underived comparisons of the two squares agree, at a module.** The composite the
comparison of the localized square `(R₂, A₂, R', A')` contributes and the composite the comparison
of the mixed square `(R, A, R', A')` contributes agree. Both send `1 ⊗ x` to `1 ⊗ x`: the underived
comparison of Tag 065Z sends `r' ⊗ m` to `d r' ⊗ m` at either square, and each of the two
localization identifications is `1 ⊗ x ↦ 1 ⊗ (1 ⊗ x) ↦ 1 ⊗ x`. -/
public theorem localizedSquareUnderived_compat_app (N : ModuleCat.{u} A₂) :
    (ModuleCat.extendScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).map
          ((ModuleCat.restrictScalarsComp'App.{u} a (algebraMap A A₂)
              ((algebraMap A A₂).comp a) rfl N).inv ≫
            (ModuleCat.restrictScalarsComp'App.{u} (algebraMap R R₂) a₂
              ((algebraMap A A₂).comp a) hloc N).hom) ≫
        (ModuleCat.extendScalarsComp.{u, u} (algebraMap R R₂) b₂).hom.app
            ((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).obj
              ((ModuleCat.restrictScalars.{u} a₂).obj N)) ≫
          (ModuleCat.extendScalars.{u, u, u} b₂).map
              ((restrictExtendScalarsIso SR (A₂ := R₂)).hom.app
                ((ModuleCat.restrictScalars.{u} a₂).obj N)) ≫
            (squareComparisonUnderived.{u, w} a₂ b₂ c₂ d hsq).app N =
      (squareComparisonUnderived.{u, w} a (b₂.comp (algebraMap R R₂))
            (c₂.comp (algebraMap A A₂)) d
            (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)).app
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N) ≫
        (ModuleCat.restrictScalars.{u} d).map
          ((ModuleCat.extendScalarsComp.{u, u} (algebraMap A A₂) c₂).hom.app
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N) ≫
            (ModuleCat.extendScalars.{u, u, u} c₂).map
              ((restrictExtendScalarsIso SA (A₂ := A₂)).hom.app N)) := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  let mR : ((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).obj
    ((ModuleCat.restrictScalars.{u} a₂).obj N) : Type u) := m
  let mA : ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N : Type u) := m
  let mN : (N : Type u) := m
  have hR1 := ModuleCat.extendScalarsComp_hom_app_one_tmul (algebraMap R R₂) b₂
    ((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).obj
      ((ModuleCat.restrictScalars.{u} a₂).obj N)) mR
  have hR2 := restrictExtendScalarsIso_hom_app_one_tmul SR
    ((ModuleCat.restrictScalars.{u} a₂).obj N) mR
  have hLt := squareComparisonUnderived_tmul a₂ b₂ c₂ d hsq N (1 : R') mN
  have hA1 := ModuleCat.extendScalarsComp_hom_app_one_tmul (algebraMap A A₂) c₂
    ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N) mA
  have hA2 := restrictExtendScalarsIso_hom_app_one_tmul SA N mA
  have hRt := squareComparisonUnderived_tmul a (b₂.comp (algebraMap R R₂))
    (c₂.comp (algebraMap A A₂)) d (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)
    ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N) (1 : R') mA
  have hd : d (1 : R') = (1 : A') := map_one d
  refine Eq.trans (b := (1 : A') ⊗ₜ[A₂, c₂] mN) ?_ (Eq.symm ?_)
  · refine Eq.trans (congrArg (fun y =>
        (squareComparisonUnderived.{u, w} a₂ b₂ c₂ d hsq).app N
          ((ModuleCat.extendScalars.{u, u, u} b₂).map
            ((restrictExtendScalarsIso SR (A₂ := R₂)).hom.app
              ((ModuleCat.restrictScalars.{u} a₂).obj N)) y)) hR1) ?_
    refine Eq.trans (congrArg
      (fun y : ((ModuleCat.restrictScalars.{u} a₂).obj N : Type u) =>
        (squareComparisonUnderived.{u, w} a₂ b₂ c₂ d hsq).app N
          ((1 : R') ⊗ₜ[R₂, b₂] y)) hR2) ?_
    exact hLt.trans (congrArg (fun z : A' => z ⊗ₜ[A₂, c₂] mN) hd)
  · refine Eq.trans (congrArg (fun y =>
        (ModuleCat.extendScalars.{u, u, u} c₂).map
          ((restrictExtendScalarsIso SA (A₂ := A₂)).hom.app N)
          ((ModuleCat.extendScalarsComp.{u, u} (algebraMap A A₂) c₂).hom.app
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N) y)) hRt) ?_
    refine Eq.trans (congrArg (fun z : A' =>
        (ModuleCat.extendScalars.{u, u, u} c₂).map
          ((restrictExtendScalarsIso SA (A₂ := A₂)).hom.app N)
          ((ModuleCat.extendScalarsComp.{u, u} (algebraMap A A₂) c₂).hom.app
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N)
            (z ⊗ₜ[A, c₂.comp (algebraMap A A₂)] mA))) hd) ?_
    refine Eq.trans (congrArg (fun y =>
      (ModuleCat.extendScalars.{u, u, u} c₂).map
        ((restrictExtendScalarsIso SA (A₂ := A₂)).hom.app N) y) hA1) ?_
    exact congrArg (fun y : (N : Type u) => (1 : A') ⊗ₜ[A₂, c₂] y) hA2

include hloc hsq in
/-- **The underived comparisons of the two squares agree**, degreewise on a complex: the hypothesis
of `RingTheory.TorIndependence.squareComparison_localized_of_compat`. -/
public theorem localizedSquareUnderived_compat
    (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
  ((ModuleCat.extendScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (localizedRestrictComplexHom.{u} a a₂ hloc P) ≫
      (Functor.mapHomologicalComplexCompIso
          (ModuleCat.extendScalarsComp.{u, u} (algebraMap R R₂) b₂).symm
          (ComplexShape.up ℤ)).inv.app
          (((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        ((ModuleCat.extendScalars.{u, u, u} b₂).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            ((restrictExtendScalarsComplexIso SR (A₂ := R₂)).hom.app
              (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          (Functor.mapHomologicalComplexCompIso
              (Iso.refl (ModuleCat.restrictScalars.{u} a₂ ⋙
                ModuleCat.extendScalars.{u, u, u} b₂)) (ComplexShape.up ℤ)).hom.app P ≫
            (NatTrans.mapHomologicalComplex
              (squareComparisonUnderived.{u, w} a₂ b₂ c₂ d hsq)
              (ComplexShape.up ℤ)).app P =
    (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.restrictScalars.{u} a ⋙
          ModuleCat.extendScalars.{u, u, u} (b₂.comp (algebraMap R R₂))))
        (ComplexShape.up ℤ)).hom.app
        (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      (NatTrans.mapHomologicalComplex
          (squareComparisonUnderived.{u, w} a (b₂.comp (algebraMap R R₂))
            (c₂.comp (algebraMap A A₂)) d
            (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)) (ComplexShape.up ℤ)).app
          (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        localizedExtendComplexHom.{u} SA c₂ d P := by
  ext i : 1
  exact ModuleCat.ExtendScalars.hom_ext fun m =>
    ConcreteCategory.congr_hom
      (localizedSquareUnderived_compat_app SR SA a a₂ b₂ c₂ d hloc hsq (P.X i)) _

include hloc hsq in
/-- **The comparison of the mixed square is the comparison of the localized square, given the
underived compatibility `hU`.** Let `R₂` be a localization of `R` and `A₂` one of `A`, compatibly,
and let `R'` be an `R₂`-algebra and `A'` an `A₂`-algebra forming a commuting square over `R₂`. Then
the derived base-change comparison of Tag 065Z at the mixed square `(R, A, R', A')`, evaluated on a
complex that already lives over `A₂`, *is* the comparison at the fully localized square
`(R₂, A₂, R', A')`, under the two identifications
`RingTheory.TorIndependence.localizedSquareDomainIso` of the sources and
`RingTheory.TorIndependence.localizedSquareCodomainIso` of the targets. -/
public theorem squareComparison_localized_of_compat
    (hU : ∀ P : CochainComplex (ModuleCat.{u} A₂) ℤ,
      ((ModuleCat.extendScalars.{u, u, u} (b₂.comp (algebraMap R R₂))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (localizedRestrictComplexHom.{u} a a₂ hloc P) ≫
          (Functor.mapHomologicalComplexCompIso
              (ModuleCat.extendScalarsComp.{u, u} (algebraMap R R₂) b₂).symm
              (ComplexShape.up ℤ)).inv.app
              (((ModuleCat.restrictScalars.{u} (algebraMap R R₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
                (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            ((ModuleCat.extendScalars.{u, u, u} b₂).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((restrictExtendScalarsComplexIso SR (A₂ := R₂)).hom.app
                  (((ModuleCat.restrictScalars.{u} a₂).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P)) ≫
              (Functor.mapHomologicalComplexCompIso
                  (Iso.refl (ModuleCat.restrictScalars.{u} a₂ ⋙
                    ModuleCat.extendScalars.{u, u, u} b₂)) (ComplexShape.up ℤ)).hom.app P ≫
                (NatTrans.mapHomologicalComplex
                  (squareComparisonUnderived.{u, w} a₂ b₂ c₂ d hsq)
                  (ComplexShape.up ℤ)).app P =
        (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.restrictScalars.{u} a ⋙
              ModuleCat.extendScalars.{u, u, u} (b₂.comp (algebraMap R R₂))))
            (ComplexShape.up ℤ)).hom.app
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          (NatTrans.mapHomologicalComplex
              (squareComparisonUnderived.{u, w} a (b₂.comp (algebraMap R R₂))
                (c₂.comp (algebraMap A A₂)) d
                (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)) (ComplexShape.up ℤ)).app
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            localizedExtendComplexHom.{u} SA c₂ d P) :
    (localizedSquareDomainIso.{u, w} SR a a₂ b₂ hloc).hom ≫
        squareComparison.{u, w} a₂ b₂ c₂ d hsq =
      Functor.whiskerLeft
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory)
          (squareComparison.{u, w} a (b₂.comp (algebraMap R R₂)) (c₂.comp (algebraMap A A₂)) d
            (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)) ≫
        (localizedSquareCodomainIso.{u, w} SA c₂ d).hom := by
  have hLD : ((totalDerivedExtensionScalars.{u, u, u} c₂).functor ⋙
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q (totalDerivedExtensionScalars.{u, u, u} c₂).functor
            ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory)).inv ≫
        Functor.whiskerRight (totalDerivedExtensionScalars.{u, u, u} c₂).comparison
          ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A₂) (ComplexShape.up ℤ)) :=
    @CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{u, u, u}
      A₂ A' _ _ c₂ _ _ (totalDerivedExtensionScalars.{u, u, u} c₂).functor
      (totalDerivedExtensionScalars.{u, u, u} c₂).comparison
      (totalDerivedExtensionScalars.{u, u, u} c₂).isLeftDerived _ _
      ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory)
  refine Functor.leftDerived_ext
    ((totalDerivedExtensionScalars.{u, u, u} c₂).functor ⋙
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategory)
    ((Functor.associator DerivedCategory.Q (totalDerivedExtensionScalars.{u, u, u} c₂).functor
          ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory)).inv ≫
      Functor.whiskerRight (totalDerivedExtensionScalars.{u, u, u} c₂).comparison
        ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A₂) (ComplexShape.up ℤ)) _ _ _ ?_
  ext P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, Functor.comp_obj]
  change (localizedSquareDomainIso.{u, w} SR a a₂ b₂ hloc).hom.app
        (DerivedCategory.Q.obj P) ≫
      (squareComparison.{u, w} a₂ b₂ c₂ d hsq).app (DerivedCategory.Q.obj P) ≫
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
        (extendComparisonApp.{u, w} c₂ P) =
    (squareComparison.{u, w} a (b₂.comp (algebraMap R R₂)) (c₂.comp (algebraMap A A₂)) d
          (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)).app
        ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P)) ≫
      (localizedSquareCodomainIso.{u, w} SA c₂ d).hom.app (DerivedCategory.Q.obj P) ≫
      (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
        (extendComparisonApp.{u, w} c₂ P)
  rw [← Iso.cancel_iso_hom_right _ _
      ((ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.app
        (((ModuleCat.extendScalars.{u, u, u} c₂).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)),
    ← Iso.cancel_iso_hom_right _ _
      (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.extendScalars.{u, u, u} c₂ ⋙ ModuleCat.restrictScalars.{u} d))
        (ComplexShape.up ℤ)).app P))]
  simp only [Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  have hτnat : (totalDerivedExtensionScalars.{u, u, u}
            (b₂.comp (algebraMap R R₂))).functor.map
            ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.map
              ((ModuleCat.restrictScalars.{u}
                (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app P)) ≫
          (squareComparison.{u, w} a (b₂.comp (algebraMap R R₂)) (c₂.comp (algebraMap A A₂)) d
            (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)).app
            (DerivedCategory.Q.obj
              (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) =
        (squareComparison.{u, w} a (b₂.comp (algebraMap R R₂)) (c₂.comp (algebraMap A A₂)) d
              (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)).app
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)) ≫
          (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
            ((totalDerivedExtensionScalars.{u, u, u}
              (c₂.comp (algebraMap A A₂))).functor.map
              ((ModuleCat.restrictScalars.{u}
                (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app P)) :=
    (squareComparison.{u, w} a (b₂.comp (algebraMap R R₂)) (c₂.comp (algebraMap A A₂)) d
      (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)).naturality _
  have hUQ := congrArg DerivedCategory.Q.map (hU P)
  simp only [Functor.map_comp] at hUQ
  rw [squareComparison_fac_app.{u, w} a₂ b₂ c₂ d hsq P,
    reassoc_of% (localizedSquareDomainIso_comparison.{u, w} SR a a₂ b₂ hloc P),
    localizedSquareCodomainIso_comparison.{u, w} SA c₂ d P, ← reassoc_of% hτnat,
    reassoc_of% (squareComparison_fac_app.{u, w} a (b₂.comp (algebraMap R R₂))
      (c₂.comp (algebraMap A A₂)) d (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)
      (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)), hUQ]

include hloc hsq in
/-- **The comparison of Tag 065Z is natural along a square of localizations.** The comparison at
the mixed square `(R, A, R', A')`, evaluated on a complex that already lives over `A₂`, *is* the
comparison at the fully localized square `(R₂, A₂, R', A')`, under the identification
`RingTheory.TorIndependence.localizedSquareDomainIso` of the sources and
`RingTheory.TorIndependence.localizedSquareCodomainIso` of the targets. -/
public theorem squareComparison_localized :
    (localizedSquareDomainIso.{u, w} SR a a₂ b₂ hloc).hom ≫
        squareComparison.{u, w} a₂ b₂ c₂ d hsq =
      Functor.whiskerLeft
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory)
          (squareComparison.{u, w} a (b₂.comp (algebraMap R R₂)) (c₂.comp (algebraMap A A₂)) d
            (localizedSquare_comm a a₂ b₂ c₂ d hloc hsq)) ≫
        (localizedSquareCodomainIso.{u, w} SA c₂ d).hom :=
  squareComparison_localized_of_compat.{u, w} SR SA a a₂ b₂ c₂ d hloc hsq
    (localizedSquareUnderived_compat.{u, w} SR SA a a₂ b₂ c₂ d hloc hsq)

end Localized

end RingTheory.TorIndependence

end

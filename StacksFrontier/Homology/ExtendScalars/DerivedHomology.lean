module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.Homology.KFlat.ChosenResolution
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Flat derived extension of scalars and cohomology

Let `f : R →+* S` be a flat homomorphism of commutative rings, whose source and target may live
in different universes. Derived extension of scalars along `f` is then computed by termwise
extension of scalars on any complex, and termwise extension of scalars is exact, so the
cohomology of `K ⊗ᴸ_R S` is the extension of scalars of the cohomology of `K`. In particular a
module placed in degree zero is carried to its base change placed in degree zero. Without
flatness, the regular module placed in degree zero is carried to the regular module placed in
degree zero.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsHomologyIso`: flat derived
  extension of scalars commutes with the cohomology of an object of the derived category.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsSingleIso`: flat derived
  extension of scalars of a module in degree zero.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsULiftIso` and
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsRegularIso`: derived extension
  of scalars of the regular module, universe-lifted and in a common universe.

## Main results

* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsHomologyIso_eq`: the
  cohomology comparison is the component of the natural isomorphism
  `CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso`.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsHomologyIso_hom_naturality`
  and `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsHomologyIso_hom_app_Q`:
  its naturality in the derived object, and its value on the image of a complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CochainComplex.DerivedExtensionScalars

/-- For a flat ring map `f : R →+* S` and an object `X` of `D(R)`, the `i`-th cohomology of
`X ⊗ᴸ_R S` is the extension of scalars of the `i`-th cohomology of `X`. -/
def derivedExtensionScalarsHomologyIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (X : DerivedCategory (ModuleCat.{max u v w} R)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).obj
        ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.obj X) ≅
      (ModuleCat.extendScalars.{u, v, max u v w} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) i).obj X) := by
  let D := derivedExtensionScalarsGeneral.{u, max u v w, v} f
  let K := DerivedCategory.Q.objPreimage X
  let r := CochainComplex.KFlat.chosenResolution.{u, max v w} K
  have hq : IsIso (DerivedCategory.Q.map r.π) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 r.quasiIso
  let e : DerivedCategory.Q.obj r.complex ≅ X :=
    asIso (DerivedCategory.Q.map r.π) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  have hc : IsIso (D.comparison.app r.complex) :=
    D.comparison_isIso_of_kFlat r.complex r.kFlat
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).mapIso
      ((D.functor.mapIso e).symm ≪≫ asIso (D.comparison.app r.complex)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} S) i).app _ ≪≫
    ModuleCat.extendScalarsHomologyIso.{u, v, max u v w} f hf r.complex i ≪≫
    (ModuleCat.extendScalars.{u, v, max u v w} f).mapIso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} R) i).symm.app r.complex) ≪≫
    (ModuleCat.extendScalars.{u, v, max u v w} f).mapIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) i).mapIso e)

/-- On the image of a complex, the natural cohomology comparison for flat derived extension of
scalars is the comparison from derived to termwise extension of scalars, followed by the
cohomology of the termwise extension. -/
theorem homologyNatIso_hom_app_Q
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ) (i : ℤ) :
    (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, v, max u v w}
        f hf i).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
          ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).comparison.app K) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} S) i).hom.app
          (((ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (ModuleCat.extendScalarsHomologyIso.{u, v, max u v w} f hf K i).hom ≫
        (ModuleCat.extendScalars.{u, v, max u v w} f).map
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} R) i).inv.app K) := by
  simp only [CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, asIso_hom]
  rfl

/-- The natural cohomology comparison at an object presented as the image of a complex: an
isomorphism `Q K ≅ X` conjugates the comparison at `Q K` into the comparison at `X`. -/
theorem homologyNatIso_hom_app_eq_of_iso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    (X : DerivedCategory (ModuleCat.{max u v w} R))
    (e : DerivedCategory.Q.obj K ≅ X) (i : ℤ) :
    (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, v, max u v w}
        f hf i).hom.app X =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
          ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.map e.inv) ≫
        (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, v, max u v w}
          f hf i).hom.app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.extendScalars.{u, v, max u v w} f).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) i).map e.hom) := by
  refine (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
    ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.map e.hom))).1 ?_
  conv_rhs => rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, v, max u v w}
    f hf i).hom.naturality e.hom

/-- The natural cohomology comparison at an object presented as the image of a complex, written
out: the comparison from derived to termwise extension of scalars on that complex, transported
along the presenting isomorphism. -/
theorem homologyNatIso_hom_app_of_iso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    (X : DerivedCategory (ModuleCat.{max u v w} R))
    (e : DerivedCategory.Q.obj K ≅ X) (i : ℤ) :
    (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, v, max u v w}
        f hf i).hom.app X =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
          ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.map e.inv) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
          ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).comparison.app K) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} S) i).hom.app
          (((ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (ModuleCat.extendScalarsHomologyIso.{u, v, max u v w} f hf K i).hom ≫
        (ModuleCat.extendScalars.{u, v, max u v w} f).map
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} R) i).inv.app K) ≫
        (ModuleCat.extendScalars.{u, v, max u v w} f).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) i).map e.hom) := by
  refine (homologyNatIso_hom_app_eq_of_iso.{u, v, w} f hf K X e i).trans ?_
  rw [homologyNatIso_hom_app_Q.{u, v, w} f hf K i]
  rfl

/-- The cohomology comparison `derivedExtensionScalarsHomologyIso f hf X i` is the component at
`X` of the natural isomorphism between flat derived extension of scalars followed by cohomology
and cohomology followed by extension of scalars. -/
theorem derivedExtensionScalarsHomologyIso_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (X : DerivedCategory (ModuleCat.{max u v w} R)) (i : ℤ) :
    derivedExtensionScalarsHomologyIso.{u, v, w} f hf X i =
      (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, v, max u v w}
        f hf i).app X := by
  have hq : IsIso (DerivedCategory.Q.map
      (CochainComplex.KFlat.chosenResolution.{u, max v w}
        (DerivedCategory.Q.objPreimage X)).π) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (CochainComplex.KFlat.chosenResolution.{u, max v w}
        (DerivedCategory.Q.objPreimage X)).quasiIso
  apply Iso.ext
  change (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
        ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.map
            (asIso (DerivedCategory.Q.map (CochainComplex.KFlat.chosenResolution.{u, max v w}
              (DerivedCategory.Q.objPreimage X)).π) ≪≫
                DerivedCategory.Q.objObjPreimageIso X).inv ≫
          (derivedExtensionScalarsGeneral.{u, max u v w, v} f).comparison.app
            (CochainComplex.KFlat.chosenResolution.{u, max v w}
              (DerivedCategory.Q.objPreimage X)).complex) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} S) i).hom.app
          (((ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (CochainComplex.KFlat.chosenResolution.{u, max v w}
              (DerivedCategory.Q.objPreimage X)).complex) ≫
        ((ModuleCat.extendScalarsHomologyIso.{u, v, max u v w} f hf
            (CochainComplex.KFlat.chosenResolution.{u, max v w}
              (DerivedCategory.Q.objPreimage X)).complex i).hom ≫
          ((ModuleCat.extendScalars.{u, v, max u v w} f).map
              ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} R) i).inv.app
                (CochainComplex.KFlat.chosenResolution.{u, max v w}
                  (DerivedCategory.Q.objPreimage X)).complex) ≫
            (ModuleCat.extendScalars.{u, v, max u v w} f).map
              ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) i).map
                (asIso (DerivedCategory.Q.map (CochainComplex.KFlat.chosenResolution.{u, max v w}
                  (DerivedCategory.Q.objPreimage X)).π) ≪≫
                    DerivedCategory.Q.objObjPreimageIso X).hom)))) = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  exact (homologyNatIso_hom_app_of_iso.{u, v, w} f hf _ X _ i).symm

/-- For `φ : X ⟶ Y` in `D(R)`, cohomology of the derived base change of `φ` followed by the
cohomology comparison at `Y` is the comparison at `X` followed by the extension of scalars of
the cohomology of `φ`. -/
theorem derivedExtensionScalarsHomologyIso_hom_naturality
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    {X Y : DerivedCategory (ModuleCat.{max u v w} R)} (φ : X ⟶ Y) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
          ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.map φ) ≫
        (derivedExtensionScalarsHomologyIso.{u, v, w} f hf Y i).hom =
      (derivedExtensionScalarsHomologyIso.{u, v, w} f hf X i).hom ≫
        (ModuleCat.extendScalars.{u, v, max u v w} f).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) i).map φ) := by
  rw [derivedExtensionScalarsHomologyIso_eq.{u, v, w} f hf X i,
    derivedExtensionScalarsHomologyIso_eq.{u, v, w} f hf Y i]
  exact (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, v, max u v w}
    f hf i).hom.naturality φ

/-- On the image of a complex, the cohomology comparison is the comparison from derived to
termwise extension of scalars, followed by the cohomology of the termwise extension. -/
theorem derivedExtensionScalarsHomologyIso_hom_app_Q
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ) (i : ℤ) :
    (derivedExtensionScalarsHomologyIso.{u, v, w} f hf (DerivedCategory.Q.obj K) i).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) i).map
          ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).comparison.app K) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} S) i).hom.app
          (((ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (ModuleCat.extendScalarsHomologyIso.{u, v, max u v w} f hf K i).hom ≫
        (ModuleCat.extendScalars.{u, v, max u v w} f).map
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} R) i).inv.app K) :=
  (congrArg Iso.hom
      (derivedExtensionScalarsHomologyIso_eq.{u, v, w} f hf (DerivedCategory.Q.obj K) i)).trans
    (homologyNatIso_hom_app_Q.{u, v, w} f hf K i)

/-- Derived extension of scalars along any `f : R →+* S` carries the universe-lifted regular
`R`-module, placed in degree zero, to the regular `S`-module in degree zero. -/
def derivedExtensionScalarsULiftIso
    {R : Type u} {S : Type (max u v)} [CommRing R] [CommRing S] (f : R →+* S) :
    (derivedExtensionScalarsGeneral.{u, max u v, max u v} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
          (ModuleCat.of R (ULift.{max u v} R))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} S) 0).obj (ModuleCat.of S S) := by
  let C := ModuleCat.{max u v} R
  let D := derivedExtensionScalarsGeneral.{u, max u v, max u v} f
  let F := ModuleCat.extendScalars.{u, max u v, max u v} f
  let M : C := ModuleCat.of R (ULift.{max u v} R)
  let P := (CochainComplex.singleFunctor C 0).obj M
  have hstrict : P.IsStrictlyLE 0 := inferInstance
  have hproj : ∀ i : ℤ, Projective (P.X i) := by
    let : Module.Projective R (ULift.{max u v} R) :=
      Module.Projective.of_equiv' ULift.moduleEquiv.symm
    let : Projective M := ModuleCat.projective_of_categoryTheory_projective M
    intro i
    by_cases hi : i = 0
    · subst i
      exact (inferInstance : Projective M)
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi).projective
  let eP : (DerivedCategory.singleFunctor C 0).obj M ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.singleFunctorIsoCompQ C 0).app M
  let eSingle :=
    HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0 |>.app M
  let eQ := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} S) 0).app (F.obj M)
  have hcomp : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P 0
  exact ((D.functor.mapIso eP.symm).symm ≪≫ asIso (D.comparison.app P) ≪≫
    DerivedCategory.Q.mapIso eSingle ≪≫ eQ.symm ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} S) 0).mapIso
      (ModuleCat.extendScalarsULiftIso.{u, v} f))

/-- When the two rings share a universe, derived extension of scalars along `f : R →+* S`
carries the regular `R`-module in degree zero to the regular `S`-module in degree zero. -/
def derivedExtensionScalarsRegularIso {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S) :=
  (derivedExtensionScalarsGeneral.{u, u, u} f).functor.mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (ULift.moduleEquiv.{u, u, u} (R := R) (M := R)).symm.toModuleIso) ≪≫
    derivedExtensionScalarsULiftIso.{u, u} f

/-- For a flat ring map `f : R →+* S`, the object `M ⊗ᴸ_R S` of `D(S)` is the base change
`S ⊗_R M` placed in degree zero. -/
def derivedExtensionScalarsSingleIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{max u v w} R) :
    (derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v w} S) 0).obj
        ((ModuleCat.extendScalars.{u, v, max u v w} f).obj M) := by
  let C := ModuleCat.{max u v w} R
  let C' := ModuleCat.{max u v w} S
  let D := derivedExtensionScalarsGeneral.{u, max u v w, v} f
  let X := (DerivedCategory.singleFunctor C 0).obj M
  have hLE : X.IsLE 0 := inferInstance
  have hLE' : (D.functor.obj X).IsLE 0 := D.maps_t_le X 0
  have hGE' : (D.functor.obj X).IsGE 0 := by
    apply (DerivedCategory.isGE_iff _ 0).2
    intro i hi
    have hsrc : IsZero ((DerivedCategory.homologyFunctor C i).obj X) :=
      (DerivedCategory.isGE_iff X 0).1 inferInstance i hi
    exact IsZero.of_iso (Functor.map_isZero (ModuleCat.extendScalars.{u, v, max u v w} f) hsrc)
      (derivedExtensionScalarsHomologyIso.{u, v, w} f hf X i)
  let hY := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (D.functor.obj X) 0
  let Y := Classical.choose hY
  let eXY : D.functor.obj X ≅ (DerivedCategory.singleFunctor C' 0).obj Y :=
    Classical.choice (Classical.choose_spec hY)
  let eH := (DerivedCategory.homologyFunctor C' 0).mapIso eXY ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C' 0).app Y
  let eM := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M
  have eY : Y ≅ (ModuleCat.extendScalars.{u, v, max u v w} f).obj M :=
    eH.symm ≪≫ derivedExtensionScalarsHomologyIso.{u, v, w} f hf X 0 ≪≫
      (ModuleCat.extendScalars.{u, v, max u v w} f).mapIso eM
  exact eXY ≪≫ (DerivedCategory.singleFunctor C' 0).mapIso eY

end CochainComplex.DerivedExtensionScalars

end

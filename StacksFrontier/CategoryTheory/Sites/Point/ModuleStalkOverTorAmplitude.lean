module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.StalkwiseFiniteTor
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOver

/-!
# Tor amplitude of a derived stalk at a point of a localized site

Let `(C, J, O)` be a ringed site, `Φ` a point of it, `V` an object of `C` and `q ∈ Φ.fiber.obj V`,
so that `Φ.over q` is a point of the localized site `C/V` (Stacks 04H2).  The stalk at `Φ.over q`
of the restriction to `C/V` of a sheaf of `O`-modules is its stalk at `Φ`, semilinearly over the
identification of the two stalks of the structure sheaf.  Tor amplitude is insensitive to
restriction of scalars along a ring isomorphism, so the derived stalk at `Φ.over q` of the
restriction to `C/V` of a complex has Tor amplitude in `[a, b]` over the stalk of `O|_V` exactly
when the stalk of the complex at `Φ` has Tor amplitude in `[a, b]` over `O_Φ`.  This is the form in
which Stacks 0DJJ, applied on a slice, is compared with the stalks of the site itself.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_of_iso`: Tor amplitude depends only on
  the isomorphism class of an object of `D(R)`.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff`: Tor
  amplitude of a complex is unchanged by restriction of scalars along a ring isomorphism.
* `Stacks.hasTorAmplitudeCanonical_sheafModuleFiber_over_iff`: Tor amplitude of the stalk at
  `Φ.over q` of the restriction of a complex to `C/V` is Tor amplitude of its stalk at `Φ`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff`
  is the same statement for the derived stalk of the derived restriction to a slice of a ringed
  site.

## References

* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace StacksDraft.TorAmplitude

/-- Canonical Tor amplitude depends only on the isomorphism class of an object of `D(R)`. -/
theorem hasTorAmplitudeCanonical_iff_of_iso {R : Type u} [CommRing R]
    {E F : letI := HasDerivedCategory.standard (ModuleCat.{u} R); DerivedCategory (ModuleCat.{u} R)}
    (e : letI := HasDerivedCategory.standard (ModuleCat.{u} R); E ≅ F) (a b : ℤ) :
    HasTorAmplitudeCanonical R E a b ↔ HasTorAmplitudeCanonical R F a b :=
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  ⟨BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b,
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b⟩

/-- Restriction of scalars along the identity of `Λ`, read on `D(Λ)` at the image of a complex,
is isomorphic to the identity. -/
def restrictScalarsReflMapDerivedCategoryObjIso {Λ : Type u} [CommRing Λ]
    (N : CochainComplex (ModuleCat.{u} Λ) ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Λ)
    (ModuleCat.restrictScalars.{u} (RingEquiv.refl Λ).toRingHom).mapDerivedCategory.obj
      (DerivedCategory.Q.obj N) ≅ DerivedCategory.Q.obj N :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} Λ)
  (ModuleCat.restrictScalars.{u} (RingEquiv.refl Λ).toRingHom).mapDerivedCategoryFactors.app N ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun i => ModuleCat.restrictScalarsId'App (RingEquiv.refl Λ).toRingHom rfl (N.X i))
      (fun i j _ => (ModuleCat.restrictScalarsId'App_hom_naturality
        (RingEquiv.refl Λ).toRingHom rfl (N.d i j)).symm))

/-- **Tor amplitude is unchanged by restriction of scalars along a ring isomorphism.** For a
ring isomorphism `e : Λ ≃ R` and a complex `N` of `R`-modules, `N` has Tor amplitude in `[a, b]`
over `R` exactly when its restriction of scalars along `e` has Tor amplitude in `[a, b]` over
`Λ`.  Both directions are
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_restrictScalars_iso`, with the identity of
`Λ` as the second identification. -/
theorem hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff {Λ R : Type u} [CommRing Λ]
    [CommRing R] (e : Λ ≃+* R) (N : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} Λ)
    HasTorAmplitudeCanonical R (DerivedCategory.Q.obj N) a b ↔
      HasTorAmplitudeCanonical Λ (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{u} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) a b := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} Λ)
  let i := (ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategoryFactors.app N
  constructor
  · intro h
    exact hasTorAmplitudeCanonical_of_restrictScalars_iso (RingEquiv.refl Λ) e
      (restrictScalarsReflMapDerivedCategoryObjIso _ ≪≫ i.symm) a b h
  · intro h
    exact hasTorAmplitudeCanonical_of_restrictScalars_iso e (RingEquiv.refl Λ)
      (i ≪≫ (restrictScalarsReflMapDerivedCategoryObjIso _).symm) a b h

end StacksDraft.TorAmplitude

namespace Stacks

open StacksDraft.TorAmplitude

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) {V : C} (q : Φ.fiber.obj V) (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over V).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify (J.over V) AddCommGrpCat.{w}] [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 04H2 for the stalks of a complex.** The stalk at `Φ.over q` of the restriction of a
complex of `O`-modules to the localized site `C/V`, viewed over `O_Φ` through
`Stacks.ringStalkOverEquiv`, is the stalk of the complex at `Φ`. -/
def sheafModuleFiberOverComplexIso
    (M : CochainComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O)) ℤ) :
    ((ModuleCat.restrictScalars.{w} (ringStalkOverEquiv Φ q O).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((sheafModuleFiberOfCommRing (Φ.over q) (O.over V)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≅
      ((sheafModuleFiberOfCommRing Φ O).mapHomologicalComplex (ComplexShape.up ℤ)).obj M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (sheafModuleFiberOverIso Φ q O).app (M.X i))
    (fun i j _ => ((sheafModuleFiberOverIso Φ q O).hom.naturality (M.d i j)).symm)

/-- **Tor amplitude of a stalk at a point of a localized site.** The stalk at `Φ.over q` of the
restriction of a complex of `O`-modules to `C/V` has Tor amplitude in `[a, b]` over the stalk of
`O|_V` exactly when the stalk of the complex at `Φ` has Tor amplitude in `[a, b]` over `O_Φ`. -/
theorem hasTorAmplitudeCanonical_sheafModuleFiber_over_iff
    (M : CochainComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O)) ℤ) (a b : ℤ) :
    letI := HasDerivedCategory.standard
      (ModuleCat.{w} (((Φ.over q).presheafFiber (A := CommRingCat.{w})).obj (O.over V).obj))
    letI := HasDerivedCategory.standard
      (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj))
    HasTorAmplitudeCanonical (((Φ.over q).presheafFiber (A := CommRingCat.{w})).obj (O.over V).obj)
        (DerivedCategory.Q.obj
          (((sheafModuleFiberOfCommRing (Φ.over q) (O.over V)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((SheafOfModules.overFunctor (commRingSheafToRingSheaf O) V).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M))) a b ↔
      HasTorAmplitudeCanonical ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj)
        (DerivedCategory.Q.obj
          (((sheafModuleFiberOfCommRing Φ O).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
        a b := by
  let := HasDerivedCategory.standard
    (ModuleCat.{w} (((Φ.over q).presheafFiber (A := CommRingCat.{w})).obj (O.over V).obj))
  let := HasDerivedCategory.standard
    (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj))
  exact (hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff (ringStalkOverEquiv Φ q O) _ a
    b).trans
    (hasTorAmplitudeCanonical_iff_of_iso
      (DerivedCategory.Q.mapIso (sheafModuleFiberOverComplexIso Φ q O M)) a b)

end Stacks

namespace Stacks.SheafOfModules.DerivedTensorProduct

open StacksDraft.TorAmplitude

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, v, w}} [LocallySmall.{w} Z.C]
  [HasSheafify Z.J AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits sliceLocallySmall

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (Z.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

/-- **Tor amplitude of a derived stalk on a slice, read at the site.** For a complex `M` of
`O`-modules on a ringed site, a point `Φ` and `q ∈ Φ.fiber.obj V`, the derived stalk at
`Φ.over q` of the derived restriction of `M` to the slice over `V` has Tor amplitude in `[a, b]`
over the stalk of `O|_V` exactly when the stalk of `M` at `Φ` has Tor amplitude in `[a, b]` over
`O_Φ`.

Restriction to a slice and the stalk functor are exact, so the derived stalk of the derived
restriction is computed termwise, and `Stacks.hasTorAmplitudeCanonical_sheafModuleFiber_over_iff`
applies. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_over_iff (V : Z.C)
    (Φ : Z.J.Point.{w}) (q : Φ.fiber.obj V)
    (M : CochainComplex (RingedSite.Modules.{u, v, w} Z) ℤ) (a b : ℤ) :
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, max u v, w} (Z.over V).O)) :=
      hSliceDerived V
    let Ψ : (Z.over V).J.Point.{w} := Φ.over q
    letI := HasDerivedCategory.standard
      (ModuleCat.{w} ((Ψ.presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj))
    letI := HasDerivedCategory.standard
      (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj Z.O.obj))
    HasTorAmplitudeCanonical ((Ψ.presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj)
        ((Stacks.derivedModuleFiber Ψ (Z.over V).O).obj
          ((RingedSite.derivedRestriction.{u, v, w, d} Z V).obj (DerivedCategory.Q.obj M))) a b ↔
      HasTorAmplitudeCanonical ((Φ.presheafFiber (A := CommRingCat.{w})).obj Z.O.obj)
        (DerivedCategory.Q.obj
          (((Stacks.sheafModuleFiberOfCommRing Φ Z.O).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) a b := by
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, max u v, w} (Z.over V).O)) :=
    hSliceDerived V
  let Ψ : (Z.over V).J.Point.{w} := Φ.over q
  let := HasDerivedCategory.standard
    (ModuleCat.{w} ((Ψ.presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj))
  let := HasDerivedCategory.standard
    (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj Z.O.obj))
  refine (hasTorAmplitudeCanonical_iff_of_iso
    ((Stacks.derivedModuleFiber Ψ (Z.over V).O).mapIso
        ((SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} Z.O) V).mapDerivedCategoryFactors.app
            M) ≪≫
      (Stacks.sheafModuleFiberOfCommRing Ψ (Z.over V).O).mapDerivedCategoryFactors.app
        _) a b).trans ?_
  exact Stacks.hasTorAmplitudeCanonical_sheafModuleFiber_over_iff Φ q Z.O M a b

end Stacks.SheafOfModules.DerivedTensorProduct

end

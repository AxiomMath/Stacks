module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules

/-!
# Cohomological dimension under a change of rings

Let `A → B` be a homomorphism of commutative rings and `I ⊆ A` a finitely generated ideal.
Extending `I` to `IB` cannot increase the cohomological dimension, and when `A → B` is
faithfully flat the two cohomological dimensions agree.

Both statements come from base change for local cohomology (Stacks 0ALZ): the local cohomology
of `B` with support in `V(IB)` is the derived extension of scalars of the local cohomology of
`A` with support in `V(I)`. For the inequality one applies a vanishing bound for `A` to the
regular module and transports it along `A → B`; for the equality one descends a vanishing bound
for `B` back to `A`, where faithful flatness is what makes the descent reflect vanishing.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyBaseChangeSingleIso` — base change for local cohomology
  evaluated at a module placed in degree zero.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_map_le` — the cohomological dimension of `IB`
  in `B` is at most that of `I` in `A`.
* `Stacks.LocalCohomology.cohomologicalDimension_map_eq_of_faithfullyFlat` — equality for a
  faithfully flat ring map.

## Implementation notes

The source ring, the target ring and the modules are allowed three independent universes, so
the regular module of `A` enters as `ULift A` and the target ring is replaced by `ULift B`
before the two are compared; `Stacks.LocalCohomology.isLocalCohomologyBound_map_of_ringEquiv`
transports a vanishing bound back along the resulting ring isomorphism.

## References

* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

/-- A vanishing bound for the local cohomology of `A` bounds the local cohomology of every
module in every universe, so local cohomology applied to a module in degree zero is
cohomologically concentrated in degrees at most `d`. -/
theorem isLE_localCohomologyDerived_of_isLocalCohomologyBound
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hd : IsLocalCohomologyBound A I hI d) (M : ModuleCat.{max u v} A) :
    ((localCohomologyDerived A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)).IsLE d :=
  (DerivedCategory.isLE_iff _ d).2 fun i hi =>
    isZero_homology_localCohomology_of_isLocalCohomologyBound.{v, u} I hI d hd M i hi

/-- Conversely, vanishing of the local cohomology of every module above `d` is a vanishing
bound in the sense of Stacks 0DX8. -/
theorem isLocalCohomologyBound_of_forall_isZero
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (hdm : (-1 : ℤ) ≤ d)
    (hvan : ∀ (M : ModuleCat.{max u v} A) (i : ℤ), d < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((localCohomologyDerived A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))) :
    IsLocalCohomologyBound A I hI d :=
  ⟨hdm, (isZero_homology_localCohomology_forall_iff.{v, u} I hI d).2 hvan⟩

/-- The degreewise reading of `DerivedCategory.IsLE` for local cohomology. -/
theorem isZero_homology_localCohomologyDerived_of_isLE
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (M : ModuleCat.{max u v} A)
    (h : ((localCohomologyDerived A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)).IsLE d)
    (i : ℤ) (hi : d < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      ((localCohomologyDerived A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))) :=
  (DerivedCategory.isLE_iff _ d).1 h i hi

/-- **Base change for local cohomology at a module.** The derived extension of scalars of
`RΓ_{V(I)}(M)` is `RΓ_{V(IB)}` of the derived extension of scalars of `M`. This is Stacks 0ALZ
evaluated at a module placed in degree zero. -/
def localCohomologyBaseChangeSingleIso
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v w} A) :
    (derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.obj
        ((localCohomologyDerived A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj M)) ≅
      (localCohomologyDerived B (I.map f) (hI.map f)).obj
        ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj M)) := by
  simpa [Functor.comp_obj] using
    (localCohomologyBaseChangeIso.{u, v, max u v w} f I hI).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj M)

/-- A vanishing bound over `A` is a vanishing bound for the base change of a module over `B`. -/
theorem isLE_localCohomologyDerived_baseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : IsLocalCohomologyBound A I hI d)
    (M : ModuleCat.{max u v w} A) :
    ((localCohomologyDerived B (I.map f) (hI.map f)).obj
      ((derivedExtensionScalarsGeneral.{u, max u v w, v} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj M))).IsLE d := by
  have := isLE_localCohomologyDerived_of_isLocalCohomologyBound.{u, max v w} I hI d hd M
  have := (derivedExtensionScalarsGeneral.{u, max u v w, v} f).maps_t_le
    ((localCohomologyDerived A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj M)) d
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (localCohomologyBaseChangeSingleIso.{u, v, w} f I hI M) d

/-- A vanishing bound transports along a ring isomorphism. -/
theorem isLocalCohomologyBound_map_of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : IsLocalCohomologyBound A I hI d) :
    IsLocalCohomologyBound B (I.map e.toRingHom) (hI.map e.toRingHom) d := by
  have hvan : ∀ (N : ModuleCat.{max u v} B) (i : ℤ), d < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).obj
        ((localCohomologyDerived B (I.map e.toRingHom) (hI.map e.toRingHom)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj N))) := by
    intro N i hi
    let M : ModuleCat.{max u v} A :=
      (ModuleCat.restrictScalars.{max u v, u, v} e.toRingHom).obj N
    have hbase := isLE_localCohomologyDerived_baseChange.{u, v, u} e.toRingHom I hI d hd M
    let eM := ModuleCat.extendScalarsRestrictScalarsIso.{u, v, u} e N
    have hFF : e.toRingHom.FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective e.bijective
    let eDerived := derivedExtensionScalarsSingleIso.{u, v, u} e.toRingHom hFF.flat M
    let eTarget := eDerived ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).mapIso eM
    have eLC : (localCohomologyDerived B (I.map e.toRingHom) (hI.map e.toRingHom)).obj
        ((derivedExtensionScalarsGeneral.{u, max u v, v} e.toRingHom).functor.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≅
        (localCohomologyDerived B (I.map e.toRingHom) (hI.map e.toRingHom)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj N) :=
      (localCohomologyDerived.{v, max u v} B (I.map e.toRingHom)
        (hI.map e.toRingHom)).mapIso eTarget
    let : ((localCohomologyDerived B (I.map e.toRingHom) (hI.map e.toRingHom)).obj
        ((derivedExtensionScalarsGeneral.{u, max u v, v} e.toRingHom).functor.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))).IsLE d := hbase
    have hLE : ((localCohomologyDerived B (I.map e.toRingHom) (hI.map e.toRingHom)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj N)).IsLE d :=
      DerivedCategory.TStructure.t.isLE_of_iso eLC d
    exact isZero_homology_localCohomologyDerived_of_isLE.{v, u}
      (I.map e.toRingHom) (hI.map e.toRingHom) d N hLE i hi
  exact ⟨hd.1, (isZero_homology_localCohomology_forall_iff.{u, v}
    (I.map e.toRingHom) (hI.map e.toRingHom) d).2 hvan⟩

/-- **Faithfully flat descent of a vanishing bound.** If the local cohomology of `B` with
support in `V(IB)` vanishes above `d`, so does the local cohomology of `A` with support in
`V(I)`: the base change of the latter is the former, and a faithfully flat extension reflects
vanishing. -/
theorem isLocalCohomologyBound_of_faithfullyFlat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat) (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hd : IsLocalCohomologyBound B (I.map f) (hI.map f) d) :
    IsLocalCohomologyBound A I hI d := by
  refine isLocalCohomologyBound_of_forall_isZero.{u, v} I hI d hd.1 ?_
  intro M i hi
  let D := derivedExtensionScalarsGeneral.{u, max u v, v} f
  let F := ModuleCat.extendScalars.{u, v, max u v} f
  have hFlat : f.Flat := hf.flat
  have hLEtarget := isLE_localCohomologyDerived_of_isLocalCohomologyBound.{v, u}
    (I.map f) (hI.map f) d hd (F.obj M)
  let eSingle := derivedExtensionScalarsSingleIso.{u, v, u} f hFlat M
  let eLC := (localCohomologyDerived.{v, max u v} B (I.map f) (hI.map f)).mapIso eSingle
  let := hLEtarget
  have hLE_Dtarget : ((localCohomologyDerived B (I.map f) (hI.map f)).obj
      (D.functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))).IsLE d :=
    DerivedCategory.TStructure.t.isLE_of_iso eLC.symm d
  have hBC := localCohomologyBaseChangeSingleIso.{u, v, u} f I hI M
  have hExt := (DerivedCategory.isLE_iff _ d).1 hLE_Dtarget i hi
  have hHom := derivedExtensionScalarsHomologyIso.{u, v, u} f hFlat
    ((localCohomologyDerived A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) i
  have hHomBC := hHom.symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).mapIso hBC
  have hExtModule : IsZero (F.obj ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      ((localCohomologyDerived A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))) :=
    IsZero.of_iso hExt hHomBC
  exact ModuleCat.isZero_of_isZero_extendScalars.{u, v, max u v} f hf _ hExtModule

/-- **Stacks Project, Tag 0DXA.** Cohomological dimension does not increase under extension of
the ideal along a ring homomorphism. -/
@[stacks 0DXA "inequality under a ring map"]
theorem cohomologicalDimension_map_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    cohomologicalDimension B (I.map f) (hI.map f) ≤ cohomologicalDimension A I hI := by
  let d := cohomologicalDimension A I hI
  have hA : IsLocalCohomologyBound A I hI d := isLocalCohomologyBound_cohomologicalDimension A I hI
  let S := ULift.{max u v} B
  let e : S ≃+* B := ULift.ringEquiv
  let g : A →+* S := e.symm.toRingHom.comp f
  let J := I.map g
  let hJ := hI.map g
  let M : ModuleCat.{max u v} A := ModuleCat.of A (ULift.{max u v} A)
  have hbase := isLE_localCohomologyDerived_baseChange.{u, max u v, max u v} g I hI d hA M
  let eReg := derivedExtensionScalarsULiftIso.{u, v} g
  have eLC : (localCohomologyDerived S J hJ).obj
      ((derivedExtensionScalarsGeneral.{u, max u v, max u v} g).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≅
      (localCohomologyDerived S J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} S) 0).obj (ModuleCat.of S S)) :=
    (localCohomologyDerived.{max u v, max u v} S J hJ).mapIso eReg
  have hBoundS : IsLocalCohomologyBound S J hJ d :=
    ⟨hA.1, isZero_homology_localCohomologyDerived_of_isLE.{max u v, max u v}
      J hJ d (ModuleCat.of S S) (DerivedCategory.TStructure.t.isLE_of_iso eLC d)⟩
  have hBoundB := isLocalCohomologyBound_map_of_ringEquiv.{max u v, v} e J hJ d hBoundS
  have hcomp : e.toRingHom.comp (e.symm.toRingHom.comp f) = f := by
    ext x
    simp
  have hBound : IsLocalCohomologyBound B (I.map f) (hI.map f) d := by
    simpa only [Ideal.map_map, J, hJ, g, hcomp] using hBoundB
  exact cohomologicalDimension_le B (I.map f) (hI.map f) d hBound

/-- **Stacks Project, Tag 0DXA.** Faithfully flat extension preserves cohomological
dimension. -/
@[stacks 0DXA "equality under faithfully flat extension"]
theorem cohomologicalDimension_map_eq_of_faithfullyFlat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FaithfullyFlat) (I : Ideal A) (hI : I.FG) :
    cohomologicalDimension B (I.map f) (hI.map f) = cohomologicalDimension A I hI := by
  refine le_antisymm (cohomologicalDimension_map_le f I hI) ?_
  exact cohomologicalDimension_le A I hI _ (isLocalCohomologyBound_of_faithfullyFlat f hf I hI _
    (isLocalCohomologyBound_cohomologicalDimension B (I.map f) (hI.map f)))

end Stacks.LocalCohomology

end

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.Flat.FaithfullyFlatComp

/-!
# Descent of finiteness along a faithfully flat ring map

Let `R → A → B` be ring maps with `A → B` faithfully flat and of finite presentation.
Finiteness properties of the composite `R → B` then descend to `R → A`: if the composite is
of finite presentation so is `R → A`, and if the composite is of finite type so is `R → A`.

## Main results

* `RingHom.finitePresentation_of_comp_of_faithfullyFlat`: finite presentation descends
  through a faithfully flat ring map of finite presentation.
* `RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation`: finite type
  descends through a faithfully flat ring map of finite presentation.

## Implementation notes

Both statements are phrased for explicit ring homomorphisms rather than algebra structures,
so the hypothesis on `R → B` is expressed using the composite `g.comp f`. This records the
compatibility of all three maps without choosing algebra instances.

Each proof first reduces to the case where the two upper rings live in a common universe, by
transporting along `ULift.ringEquiv`, and then applies a finitely presented model of the
faithfully flat map: faithfully flat base change descent over the model gives the conclusion
over the model's source, and composition finishes the argument.

## References

* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace RingHom

@[ega "IV 11.3.16" "special case",
  ega "IV 11.3.17",
  sga "3 XIX 2.1" "special case",
  sga "4 IV 8.5.5" "special case"]
private theorem finitePresentation_of_comp_of_faithfullyFlat_sameUniverse
    {R : Type u} {A B : Type v} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hcomp : (g.comp f).FinitePresentation)
    (hff : g.FaithfullyFlat) (hfp : g.FinitePresentation) : f.FinitePresentation := by
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra A B := g.toAlgebra
  let _ : Algebra R B := (g.comp f).toAlgebra
  let _ : IsScalarTower R A B := .of_algebraMap_eq fun _ => rfl
  have : Module.FaithfullyFlat A B :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  have : Algebra.FinitePresentation A B := hfp
  obtain ⟨A₀, B₀, _, _, _, _, _, _, _, _, _, _, hA₀, hB₀ff, hB₀fp, hpush⟩ :=
    Algebra.exists_faithfullyFlat_finitePresentation_model (R := R) (A := A) (B := B)
  let _ : IsScalarTower R A₀ B := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A B,
      IsScalarTower.algebraMap_apply R A₀ A,
      IsScalarTower.algebraMap_apply A₀ A B]
  have hA₀ft : (algebraMap R A₀).FiniteType :=
    .of_finitePresentation (RingHom.finitePresentation_algebraMap.mpr hA₀)
  have hA₀B : (algebraMap A₀ B).FinitePresentation := by
    apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap R A₀) _ hA₀ft
    change (algebraMap R B).FinitePresentation at hcomp
    simpa only [← IsScalarTower.algebraMap_eq R A₀ B] using hcomp
  have hB₀ft : (algebraMap A₀ B₀).FiniteType :=
    .of_finitePresentation (RingHom.finitePresentation_algebraMap.mpr hB₀fp)
  have hB₀B : Algebra.FinitePresentation B₀ B := by
    apply RingHom.finitePresentation_algebraMap.mp
    apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap A₀ B₀) _ hB₀ft
    rwa [← IsScalarTower.algebraMap_eq A₀ B₀ B]
  let _ : Algebra.IsPushout A₀ B₀ A B := hpush.symm
  have : Algebra.FinitePresentation B₀ (B₀ ⊗[A₀] A) :=
    Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv A₀ B₀ A B).symm
  have hA : Algebra.FinitePresentation A₀ A :=
    Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat B₀
  change (algebraMap R A).FinitePresentation
  rw [IsScalarTower.algebraMap_eq R A₀ A]
  exact (RingHom.finitePresentation_algebraMap.mpr hA).comp
    (RingHom.finitePresentation_algebraMap.mpr hA₀)

/-- **Stacks Project, Tag 02KK.** If `R → B` is of finite presentation and `A → B` is
faithfully flat and of finite presentation, then `R → A` is of finite presentation. -/
@[stacks 02KK,
  ega "IV 11.3.17" "finite presentation case",
  ega "IV 11.3.16" "affine, fin. pres. case",
  sga "3 V 9.1" "affine, finite pres.", sga "3 XIX 2.1" "special case"]
theorem finitePresentation_of_comp_of_faithfullyFlat
    {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hcomp : (g.comp f).FinitePresentation)
    (hff : g.FaithfullyFlat) (hfp : g.FinitePresentation) : f.FinitePresentation := by
  let eA : ULift.{max v w} A ≃+* A := ULift.ringEquiv
  let eB : ULift.{max v w} B ≃+* B := ULift.ringEquiv
  let f' : R →+* ULift.{max v w} A := eA.symm.toRingHom.comp f
  let g' : ULift.{max v w} A →+* ULift.{max v w} B :=
    eB.symm.toRingHom.comp (g.comp eA.toRingHom)
  have hcomp' : (g'.comp f').FinitePresentation := by
    convert (show eB.symm.toRingHom.FinitePresentation from
      RingHom.FinitePresentation.of_bijective eB.symm.bijective).comp hcomp using 1
    ext x
    simp [g', f', RingHom.comp_apply]
  have hff' : g'.FaithfullyFlat :=
    RingHom.FaithfullyFlat.comp
      (RingHom.FaithfullyFlat.comp (RingHom.FaithfullyFlat.of_bijective eA.bijective) hff)
      (RingHom.FaithfullyFlat.of_bijective eB.symm.bijective)
  have hfp' : g'.FinitePresentation :=
    (RingHom.FinitePresentation.of_bijective eB.symm.bijective).comp
      (hfp.comp (RingHom.FinitePresentation.of_bijective eA.bijective))
  convert (show eA.toRingHom.FinitePresentation from
      RingHom.FinitePresentation.of_bijective eA.bijective).comp
    (finitePresentation_of_comp_of_faithfullyFlat_sameUniverse f' g' hcomp' hff' hfp') using 1
  ext x
  simp [f', RingHom.comp_apply]

@[ega "IV 11.3.16" "special case", ega "IV 11.3.17", sga "4 IV 8.5.5" "special case"]
private theorem finiteType_of_comp_of_faithfullyFlat_of_finitePresentation_sameUniverse
    {R : Type u} {A B : Type v} [CommRing R] [CommRing A] [CommRing B]
    {f : R →+* A} {g : A →+* B} (hgf : (g.comp f).FiniteType)
    (hflat : g.FaithfullyFlat) (hfp : g.FinitePresentation) : f.FiniteType := by
  algebraize [f, g, g.comp f]
  have : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hflat
  have : Algebra.FinitePresentation A B := RingHom.finitePresentation_algebraMap.mp hfp
  have : Algebra.FiniteType R B := RingHom.finiteType_algebraMap.mp hgf
  obtain ⟨A₀, B₀, _, _, _, _, _, hRA₀A, _, _, hA₀AB, hA₀B₀B,
    hA₀, hB₀, _, hpush⟩ :=
    Algebra.exists_faithfullyFlat_finitePresentation_model (R := R) (A := A) (B := B)
  let _ : Algebra.FinitePresentation R A₀ := hA₀
  let _ : Module.FaithfullyFlat A₀ B₀ := hB₀
  let _ : Algebra R B₀ := ((algebraMap A₀ B₀).comp (algebraMap R A₀)).toAlgebra
  have : IsScalarTower R A₀ B₀ := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R A₀ B := .of_algebraMap_eq fun r ↦
    (IsScalarTower.algebraMap_apply R A B r).trans <|
      (congrArg (algebraMap A B) (IsScalarTower.algebraMap_apply R A₀ A r)).trans <|
        (IsScalarTower.algebraMap_apply A₀ A B (algebraMap R A₀ r)).symm
  have : IsScalarTower R B₀ B := .of_algebraMap_eq fun r ↦
    (IsScalarTower.algebraMap_apply R A₀ B r).trans
      (IsScalarTower.algebraMap_apply A₀ B₀ B (algebraMap R A₀ r))
  have : Algebra.FiniteType B₀ B := Algebra.FiniteType.of_restrictScalars_finiteType R B₀ B
  let _ : Algebra.IsPushout A₀ B₀ A B := Algebra.IsPushout.symm hpush
  let _ : Algebra B₀ (B₀ ⊗[A₀] A) := Algebra.TensorProduct.leftAlgebra
  have : Algebra.FiniteType B₀ (B₀ ⊗[A₀] A) :=
    Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType B₀ B))
      (Algebra.IsPushout.equiv A₀ B₀ A B).symm
  have : Algebra.FiniteType A₀ A :=
    Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat B₀
  change (algebraMap R A).FiniteType
  rw [RingHom.finiteType_algebraMap]
  exact (Algebra.FiniteType.of_finitePresentation (R := R) (A := A₀)).trans inferInstance

/-- **Stacks Project, Tag 0367.** If `R → A → B` are ring maps, the
composite is of finite type, and `A → B` is faithfully flat and of finite
presentation, then `R → A` is of finite type. -/
@[stacks 0367,
  ega "IV 11.3.17" "finite type case",
  ega "IV 11.3.16" "affine, finite type case",
  sga "3 V 9.1" "affine, finite type", ega "IV 17.7.5" "affine schemes"]
theorem finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    {f : R →+* A} {g : A →+* B}
    (hgf : (g.comp f).FiniteType) (hflat : g.FaithfullyFlat)
    (hfp : g.FinitePresentation) :
    f.FiniteType := by
  let eA : ULift.{max v w} A ≃+* A := ULift.ringEquiv
  let eB : ULift.{max v w} B ≃+* B := ULift.ringEquiv
  let f' : R →+* ULift.{max v w} A := eA.symm.toRingHom.comp f
  let g' : ULift.{max v w} A →+* ULift.{max v w} B :=
    eB.symm.toRingHom.comp (g.comp eA.toRingHom)
  have hgf' : (g'.comp f').FiniteType := by
    convert (RingHom.FiniteType.of_surjective eB.symm.toRingHom eB.symm.surjective).comp hgf
      using 1
    ext
    simp [f', g', eA, eB]
  have hflat' : g'.FaithfullyFlat :=
    RingHom.FaithfullyFlat.comp
      (RingHom.FaithfullyFlat.comp (RingHom.FaithfullyFlat.of_bijective eA.bijective) hflat)
      (RingHom.FaithfullyFlat.of_bijective eB.symm.bijective)
  have hfp' : g'.FinitePresentation :=
    (RingHom.FinitePresentation.of_bijective eB.symm.bijective).comp
      (hfp.comp (RingHom.FinitePresentation.of_bijective eA.bijective))
  convert (RingHom.FiniteType.of_surjective eA.toRingHom eA.surjective).comp
    (finiteType_of_comp_of_faithfullyFlat_of_finitePresentation_sameUniverse hgf' hflat' hfp')
    using 1
  ext
  simp [f', eA]

end RingHom
